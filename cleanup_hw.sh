#!/usr/bin/env bash
set -euo pipefail

# === CONFIGURE ===
ROOT="/Users/bilalwaraich/Desktop/Lean4-Functional-Programming"
DRY_RUN=false  # Set to true to verify before deleting

echo "Cleaning all HW folders inside: $ROOT"
echo

# Loop through every hw*-Bilal-Waraich directory
for dir in "$ROOT"/hw*-Bilal-Waraich; do
  [ -d "$dir" ] || continue
  echo "→ Processing $dir"

  # 1. Clean Directories (.git, .github, .lake, build, lake_output)
  # We look for directories matching these names and execute rm -rf on them.
  # -prune prevents find from looking inside the folder we are about to delete.
  if [ "$DRY_RUN" = true ]; then
      echo "  [DRY RUN] Would delete directories:"
      find "$dir" -type d \( -name ".git" -o -name ".github" -o -name ".lake" -o -name "lake_output" -o -name "build" \) -print
      
      echo "  [DRY RUN] Would delete files:"
      find "$dir" -type f -name ".gitignore" -print
  else
      # Actual Deletion
      
      # Delete directories
      find "$dir" -type d \( -name ".git" -o -name ".github" -o -name ".lake" -o -name "lake_output" -o -name "build" \) -exec rm -rf {} + 2>/dev/null || true
      
      # Delete specific files
      find "$dir" -type f -name ".gitignore" -delete 2>/dev/null || true
      
      echo "  ✓ Cleaned artifacts"
  fi
  echo
done

echo "All homework directories processed!"