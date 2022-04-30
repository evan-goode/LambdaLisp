#!/usr/bin/env bash

set -e

file="$(realpath "$1")"
cd "$(dirname "$0")"

{ ./to_bytes.py < "$file" | justine/asc2bin.com; cat /dev/stdin; } | justine/lambda.com -b
