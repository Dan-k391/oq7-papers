#!/bin/sh
# Source this file after activating the pinned Lean toolchain. Lake supplies LEAN_PATH.
if ! command -v lake >/dev/null 2>&1; then
  printf '%s\n' 'Activate Lean 4.34.1 before using this release.' >&2
  return 1 2>/dev/null || exit 1
fi
oq7_lean() { lake env lean "$@"; }
oq7_checker() { lake env leanchecker "$@"; }
