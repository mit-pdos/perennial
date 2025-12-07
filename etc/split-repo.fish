#!/usr/bin/env fish

# Note: this script is only to identify how to split the repo.
# Once the sets of files are determined, we will remove them
# from the repo and delete this file.

set -l tulip_srcs (find src/program_proof/{tulip,rsm} -name "*.v")
set -l grove_srcs \
    (find src/program_proof/{ctrexample,vrsm,memkv,tutorial,fencing,mvcc} -name "*.v") \
    src/program_proof/wp_auto/experiments.v \
    src/program_proof/minlease/proof.v \
    (find external/Goose/github_com/mit_pdos/gokv -name "*.v")
set -l pav_srcs \
    (find new/proof/github_com/sanjit_bhat/pav -name "*.v")

# set_subtract s1 s2 stores s1 \ s2 in s1
function set_subtract
    sort $argv[1] >/tmp/tmp1.txt
    sort --check $argv[2]
    comm -23 /tmp/tmp1.txt $argv[2] >$argv[1]
    rm /tmp/tmp1.txt
end

function header
    set_color blue
    echo $argv
    set_color normal
end

./etc/package-sources.sh old-goose | sort >old-goose.txt
# pretend that new-goose also includes its dependencies
perennial-cli deps (./etc/package-sources.sh new-goose) | sort >new-goose.txt

perennial-cli deps $tulip_srcs >tulip.txt
set_subtract tulip.txt old-goose.txt

perennial-cli deps $grove_srcs >grove.txt
set_subtract grove.txt old-goose.txt

perennial-cli deps $pav_srcs >pav.txt
set_subtract pav.txt new-goose.txt

header "created file lists:"
wc -l tulip.txt grove.txt pav.txt

comm -12 tulip.txt grove.txt >bad.txt
if [ -s bad.txt ]
    set_color red
    echo "tulip grove overlap:"
    set_color normal
    cat bad.txt
else
    rm bad.txt
end

echo
header "moving tulip would break:"
perennial-cli deps -r (cat tulip.txt) >broken.txt
set_subtract broken.txt old-goose.txt
cat broken.txt
rm broken.txt

echo
header "moving grove would break:"
perennial-cli deps -r (cat grove.txt) >broken.txt
set_subtract broken.txt old-goose.txt
cat broken.txt
rm broken.txt

echo
header "moving pav would break:"
perennial-cli deps -r (cat pav.txt) >broken.txt
set_subtract broken.txt new-goose.txt
cat broken.txt
set_color red
echo "(lots of things, need to fix new-goose package)"
set_color normal
wc -l broken.txt
rm broken.txt

rm old-goose.txt new-goose.txt
