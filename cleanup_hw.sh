#!/usr/bin/env bash
set -euo pipefail

# === CONFIGURE ROOT PATH ===
ROOT="/Users/bilalwaraich/Desktop/Lean4-Functional-Programming"

echo "Cleaning all HW folders inside: $ROOT"
echo

# Loop through every hw*-Bilal-Waraich directory
for dir in "$ROOT"/hw*-Bilal-Waraich; do
  [ -d "$dir" ] || continue
  echo "→ Cleaning $dir"

  # Remove any Git repositories
  find "$dir" -type d -name ".git" -exec rm -rf {} + 2>/dev/null || true

  #  Remove any GitHub Actions/workflows folders
  find "$dir" -type d -name ".github" -exec rm -rf {} + 2>/dev/null || true

  # Remove all .gitignore files
  find "$dir" -type f -name ".gitignore" -delete 2>/dev/null || true

  # Optional: remove Lake build/cache folders
  find "$dir" -type d -name "lake_output" -exec rm -rf {} + 2>/dev/null || true
  find "$dir" -type d -name ".lake" -exec rm -rf {} + 2>/dev/null || true
  find "$dir" -type d -name "build" -exec rm -rf {} + 2>/dev/null || true

  echo "Cleaned $dir"
  echo
done

echo "All homework directories cleaned successfully!"

