#!/usr/bin/env bash
# Build every module of the Lean port and print a per-module pass/fail summary.
#
# Usage: etc/lean-ci.sh [-g GROUPS] [-o LOG] [--mem-cap GB] [--min-avail GB] [-q]
#
#   -g GROUPS      comma-separated subset of: framework,code,genproof,proof,other
#                  (default: all).  framework = `lake build Perennial` (the
#                  closure of Perennial.lean); code = Perennial/Code/**;
#                  genproof = Perennial/GeneratedProof/**; proof = Perennial/Proof/**;
#                  other = every remaining Perennial/**/*.lean not reached from
#                  Perennial.lean (ManualProof, TrustedCode, ...).
#   -o LOG         full lake log (default: .lake/lean-ci.log)
#   --mem-cap GB   kill any single `lean` child whose RSS exceeds this (default 20)
#   --min-avail GB kill the largest `lean` child when MemAvailable drops below
#                  this (default 6)
#   -q             only print failures and the totals
#
# All targets are passed to ONE `lake build` invocation, so lake schedules the
# whole DAG in parallel (one `lean` process per ready module, bounded by the
# core count) and keeps going past failures.  Modules are given to lake as file
# paths, so module names that need «» quoting (Perennial.Proof.«unsafe») need no
# special handling.  A watchdog enforces the memory limits above (there is no
# systemd/cgroup here and `ulimit -v` breaks Lean's thread stacks).
#
# Per-module status in the summary:
#   ok       built (or replayed from an up-to-date .olean) successfully
#   FAIL     lean reported errors (or was killed by the watchdog: see KILLED)
#   SKIP     not built because an import failed
# Also writes .lake/lean-ci-status.tsv (module, group, status, seconds) which
# etc/lean-audit.py uses to decide which modules to import.
#
# Exit status: 0 iff every requested module is ok.

set -u
cd "$(dirname "$0")/.." || exit 2
ROOT=$(pwd)

GROUPS_ARG="framework,code,genproof,proof,other"
LOG=.lake/lean-ci.log
MEMCAP_GB=20
MINAVAIL_GB=6
QUIET=0
while [ $# -gt 0 ]; do
  case "$1" in
    -g) GROUPS_ARG=$2; shift 2;;
    -o) LOG=$2; shift 2;;
    --mem-cap) MEMCAP_GB=$2; shift 2;;
    --min-avail) MINAVAIL_GB=$2; shift 2;;
    -q) QUIET=1; shift;;
    -h|--help) sed -n '2,35p' "$0"; exit 0;;
    *) echo "unknown argument $1" >&2; exit 2;;
  esac
done
mkdir -p .lake
STATUS_TSV=.lake/lean-ci-status.tsv
WDLOG=.lake/lean-ci-watchdog.log
: > "$WDLOG"

want() { case ",$GROUPS_ARG," in *",$1,"*) return 0;; esac; return 1; }

# --- enumerate modules ------------------------------------------------------
# file path -> module name (path components joined by '.'; lake's own module
# names are unquoted, which is what its log prints)
modname() { local p=${1%.lean}; echo "${p//\//.}"; }

# framework closure: follow imports from Perennial.lean (textual, cheap)
declare -A FW=()
fw_visit() {
  local f=$1 m imp
  m=$(modname "$f"); [ -n "${FW[$m]+x}" ] && return; FW[$m]=1
  while read -r imp; do
    imp=${imp//«/}; imp=${imp//»/}
    case "$imp" in Perennial|Perennial.*) ;; *) continue;; esac
    local p="${imp//.//}.lean"
    [ -f "$p" ] && fw_visit "$p"
  done < <(sed -n 's/^import[[:space:]]\+\([^[:space:]]*\).*/\1/p' "$f")
}
fw_visit Perennial.lean

declare -A GROUP=()
TARGETS=()
for f in Perennial.lean $(find Perennial -name '*.lean' | sort); do
  m=$(modname "$f")
  case "$f" in
    Perennial/Code/*) g=code;;
    Perennial/GeneratedProof/*) g=genproof;;
    Perennial/Proof/*) g=proof;;
    *) if [ -n "${FW[$m]+x}" ]; then g=framework; else g=other; fi;;
  esac
  want "$g" || continue
  GROUP[$m]=$g
  [ "$g" = framework ] || TARGETS+=("$f")
done
want framework && TARGETS=(Perennial "${TARGETS[@]}")
NMOD=${#GROUP[@]}
echo "lean-ci: $NMOD modules (groups: $GROUPS_ARG), $(nproc) cores; log: $LOG"

# --- watchdog ---------------------------------------------------------------
watchdog() {
  local lakepid=$1 cap=$((MEMCAP_GB*1024*1024)) minav=$((MINAVAIL_GB*1024*1024))
  while kill -0 "$lakepid" 2>/dev/null; do
    local kids big=0 bigpid="" bigf=""
    kids=$(pgrep -P "$lakepid" -x lean 2>/dev/null)
    for pid in $kids; do
      local rss f
      rss=$(awk '/^VmRSS/{print $2}' /proc/$pid/status 2>/dev/null); rss=${rss:-0}
      f=$( { tr '\0' ' ' < /proc/$pid/cmdline; } 2>/dev/null | awk '{print $2}')
      if [ "$rss" -gt "$cap" ]; then
        echo "$(date +%T) KILLED $f rss=$((rss/1048576))GB > cap ${MEMCAP_GB}GB" >> "$WDLOG"
        kill "$pid"; continue
      fi
      if [ "$rss" -gt "$big" ]; then big=$rss; bigpid=$pid; bigf=$f; fi
    done
    local avail
    avail=$(awk '/^MemAvailable/{print $2}' /proc/meminfo)
    if [ -n "$bigpid" ] && [ "$avail" -lt "$minav" ]; then
      echo "$(date +%T) KILLED $bigf rss=$((big/1048576))GB (MemAvailable $((avail/1048576))GB < ${MINAVAIL_GB}GB)" >> "$WDLOG"
      kill "$bigpid"
    fi
    sleep 2
  done
}

# --- build ------------------------------------------------------------------
START=$(date +%s)
lake build -v "${TARGETS[@]}" > "$LOG" 2>&1 &
LAKEPID=$!
watchdog "$LAKEPID" &
WDPID=$!
wait "$LAKEPID"; RC=$?
kill "$WDPID" 2>/dev/null; wait "$WDPID" 2>/dev/null
END=$(date +%s)

# --- summarize --------------------------------------------------------------
# lake -v prints, per module job:  "ℹ [i/n] Built M (1.2s)", "... Replayed M",
# "✖ [i/n] Building M (3.4s)" on failure (also "⚠ [i/n] Built M" with warnings).
declare -A ST=() SECS=()
while IFS= read -r line; do
  case "$line" in
    *"] Built "*|*"] Replayed "*|*"] Building "*) ;;
    *) continue;;
  esac
  rest=${line#*] }; verb=${rest%% *}; rest=${rest#* }
  m=${rest%% *}
  t=""; [[ "$rest" =~ \(([0-9.]+)(m?s)\) ]] && { t=${BASH_REMATCH[1]}; [ "${BASH_REMATCH[2]}" = ms ] && t=$(awk "BEGIN{print $t/1000}"); }
  [ -n "${GROUP[$m]+x}" ] || continue
  case "$verb" in
    Built|Replayed) ST[$m]=ok;;
    Building) ST[$m]=FAIL;;
  esac
  SECS[$m]=${t:-0}
done < <(sed 's/\x1b\[[0-9;]*m//g' "$LOG")

declare -A CNT=()
: > "$STATUS_TSV"
for m in $(printf '%s\n' "${!GROUP[@]}" | sort); do
  s=${ST[$m]:-SKIP}
  # the `Perennial` root module itself is not printed by lake as a module job
  if [ "$m" = Perennial ] && [ "$s" = SKIP ] && grep -q "Build completed successfully" "$LOG"; then s=ok; fi
  g=${GROUP[$m]}
  CNT[$g.$s]=$(( ${CNT[$g.$s]:-0} + 1 ))
  printf '%s\t%s\t%s\t%s\n' "$m" "$g" "$s" "${SECS[$m]:-}" >> "$STATUS_TSV"
  if [ "$QUIET" = 0 ] || [ "$s" != ok ]; then
    printf '%-4s %-9s %-90s %s\n' "$s" "$g" "$m" "${SECS[$m]:+${SECS[$m]}s}"
  fi
done

echo
echo "== failures (first error of each) =="
for m in $(awk -F'\t' '$3=="FAIL"{print $1}' "$STATUS_TSV"); do
  f="${m//.//}.lean"
  e=$(sed 's/\x1b\[[0-9;]*m//g' "$LOG" | grep -m1 -E "^error: (\./)?$f:" | cut -c1-200)
  echo "  $m: ${e:-(no error line; see $LOG / $WDLOG)}"
done
[ -s "$WDLOG" ] && { echo "== watchdog =="; cat "$WDLOG"; }

echo
echo "== summary ==  (lake exit $RC, wall $((END-START))s)"
printf '%-10s %6s %6s %6s\n' group ok FAIL SKIP
TOK=0; TBAD=0
for g in framework code genproof proof other; do
  want "$g" || continue
  o=${CNT[$g.ok]:-0}; f=${CNT[$g.FAIL]:-0}; s=${CNT[$g.SKIP]:-0}
  TOK=$((TOK+o)); TBAD=$((TBAD+f+s))
  printf '%-10s %6s %6s %6s\n' "$g" "$o" "$f" "$s"
done
echo "total: $TOK ok, $TBAD not ok, of $NMOD modules; slowest (re)built this run:"
sort -t$'\t' -k4 -gr "$STATUS_TSV" | head -5 | awk -F'\t' '$4!=""{printf "  %8.1fs  %s\n", $4, $1}'
[ "$TBAD" = 0 ] && [ "$RC" = 0 ]
