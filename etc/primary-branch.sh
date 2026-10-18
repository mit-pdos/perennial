# Sourced by the workflow scripts (etc/land.sh, etc/githooks/*, etc/hooks/*): the
# primary branch, the one etc/primary-branch names. The rule (etc/trusted-delta.py
# reads the file with the same one): the file's content with all whitespace removed,
# or `lean` when the file is absent or that leaves nothing.
#
#   primary_branch DIR   the primary branch of the checkout at DIR
#   primary_branch_of    the same rule applied to stdin (the file's content read
#                        elsewhere, e.g. `git show <rev>:etc/primary-branch`)

primary_branch_of() {
  local b
  b=$(tr -d '[:space:]')
  printf '%s\n' "${b:-lean}"
}

primary_branch() {
  primary_branch_of 2>/dev/null < "$1/etc/primary-branch" || echo lean
}
