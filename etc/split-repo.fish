#!/usr/bin/env fish

# Note: this script is only to identify how to split the repo.
# Once the sets of files are determined, we will remove them
# from the repo and delete this file.

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

perennial-cli deps $pav_srcs >pav.txt
set_subtract pav.txt new-goose.txt

header "created file lists:"
wc -l pav.txt

echo
header "moving pav would break:"
perennial-cli deps -r (cat pav.txt) >pav-broken.txt
set_subtract pav-broken.txt new-goose.txt
wc -l pav-broken.txt
set_color red
echo "(most fixes should be in new-goose package)"
set_color normal

rm old-goose.txt new-goose.txt
