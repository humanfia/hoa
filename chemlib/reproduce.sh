#!/usr/bin/env bash
set -euo pipefail

script_dir="$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)"
cd "$script_dir/chemlib"

lean --version
lake exe cache get
lake build
lake env lean Chemlib.lean
lake env lean AFPS2017.lean
