#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."

if [[ "$(git rev-parse --abbrev-ref HEAD)" != "main" ]]; then
  echo "[push-main] expected branch 'main' (got $(git rev-parse --abbrev-ref HEAD))" >&2
  exit 1
fi

if [[ -n "$(git status --porcelain)" ]]; then
  echo "[push-main] working tree not clean" >&2
  git status --porcelain >&2
  exit 1
fi

./scripts/check.sh

echo "[push-main] pushing origin main"
git push origin main

