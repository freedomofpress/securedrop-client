#!/bin/bash

set -e

EXCLUDE_RULES="SC1091,SC2001,SC2164"

# Omitting:
# - the `.git/` directory since its hooks won't pass # validation, and
#   we don't maintain those scripts.
# - Python, JavaScript, YAML, HTML, SASS, PNG files because they're not shell scripts.
# - Cache directories
# - test results
FILES=$(find "." \
     \( \
        -path '*.mo' \
        -o -path '*.po' \
        -o -path '*.py' \
        -o -path '*.yml' \
        -o -path '*/.mypy_cache/*' \
        -o -path './.git' \
        -o -path './build/*' \
        -o -path './target' \
     \) -prune \
     -o -type f \
     -exec file --mime {} + \
    | awk '$2 ~ /x-shellscript/ { print $1 }' \
    | sed 's/://')
# Turn the multiline find output into a single space-separated line
FILES=$(echo "$FILES" | tr '\n' ' ')

shellcheck --version
# $FILES intentionally unquoted so each file is passed as its own argument
# shellcheck disable=SC2086
shellcheck -x --exclude="$EXCLUDE_RULES" $FILES
