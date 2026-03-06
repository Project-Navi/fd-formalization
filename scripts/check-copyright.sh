#!/bin/bash
# Check that all .lean files (excluding .lake/) have the Mathlib copyright header
EXPECTED="Copyright (c) 2026 Nelson Spence. All rights reserved."
FAILED=0

for f in $(find . -name '*.lean' -not -path './.lake/*' -not -path './archive/*' -not -path './artifacts/*' -not -path './drafts/*'); do
  if ! head -5 "$f" | grep -q "$EXPECTED"; then
    echo "Missing copyright header: $f"
    FAILED=1
  fi
done

if [ "$FAILED" -eq 1 ]; then
  echo ""
  echo "Expected header (first 4 lines):"
  echo "/-"
  echo "Copyright (c) 2026 Nelson Spence. All rights reserved."
  echo "Released under Apache 2.0 license as described in the file LICENSE."
  echo "Authors: Nelson Spence"
  echo "-/"
  exit 1
fi
