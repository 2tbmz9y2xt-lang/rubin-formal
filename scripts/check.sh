#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

export PATH="$HOME/.elan/bin:/opt/homebrew/bin:$PATH"

echo "[check] lake build"
lake build

echo "[check] ok"
