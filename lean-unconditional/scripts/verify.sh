#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"
TOOLCHAIN="$(cat lean-toolchain)"
PINNED_LEAN="$ROOT/.scratch/pinned-v4.35.0/lean-4.35.0-linux/bin"

# Prefer an installed elan toolchain. The fallback is a project-local toolchain, rebuilt
# from the official release asset when this machine has no elan (as in the development VM).
if command -v elan >/dev/null 2>&1; then
  elan toolchain install "$TOOLCHAIN"
  LAKE=(elan run "$TOOLCHAIN" lake)
else
  if [ ! -x "$PINNED_LEAN/lake" ]; then
    BASE="$ROOT/.scratch/pinned-v4.35.0"
    mkdir -p "$BASE" "$ROOT/.scratch/tmp"
    curl -fL --retry 3 \
      "https://github.com/leanprover/lean4/releases/download/v4.35.0/lean-4.35.0-linux.tar.zst" \
      -o "$BASE/lean.tar.zst"
    tar --zstd -xf "$BASE/lean.tar.zst" -C "$BASE"
  fi
  export PATH="$PINNED_LEAN:$PATH"
  LAKE=(lake)
fi
unset LEAN_PATH
"${LAKE[@]}" exe cache get
"${LAKE[@]}" build
