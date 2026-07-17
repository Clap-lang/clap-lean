#!/usr/bin/env bash
set -euo pipefail

output="${1:-Clap.lean}"
output="${output#./}"

mkdir -p "$(dirname "$output")"
tmp="$(mktemp)"

{
    echo

    find . \
        \( -path './.lake' -o -path './.git' \) -prune \
        -o -type f -name '*.lean' ! -name 'Clap.lean' -print |
    sed 's|^\./||' |
    grep -Fxv "$output" |
    sed \
        -e 's|\.lean$||' \
        -e 's|/|.|g' \
        -e 's|^|import |' |
    LC_ALL=C sort -u
} > "$tmp"

mv "$tmp" "$output"
echo "Generated $output"
