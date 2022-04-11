#!/usr/bin/env bash

set -e

file="$(realpath "$1")"
cd "$(dirname "$0")"

{ justine/compile.sh < "$file" | justine/asc2bin.com; cat /dev/stdin; } | justine/Blc
