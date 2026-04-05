#!/usr/bin/env bash
set -euo pipefail

./clean.sh
uv run --reinstall test.py
