#!/bin/bash
input=$(cat)

# Extract session ID and CWD (stable identifiers for caching)
SESSION_ID=$(echo "$input" | python -c "import sys,json; d=json.load(sys.stdin); print(d.get('session_id',''))" 2>/dev/null)
CWD=$(echo "$input" | python -c "import sys,json; d=json.load(sys.stdin); print((d.get('workspace') or {}).get('current_dir',''))" 2>/dev/null)

# Git branch with 5-second cache keyed by session_id (avoids slow git on every render)
GIT_BRANCH=""
if [ -n "$SESSION_ID" ] && [ -n "$CWD" ]; then
  cache_file="/tmp/.claude_git_${SESSION_ID}"
  if python -c "import os,time; f='$cache_file'; exit(0 if os.path.exists(f) and time.time()-os.path.getmtime(f)<5 else 1)" 2>/dev/null; then
    GIT_BRANCH=$(cat "$cache_file" 2>/dev/null)
  else
    GIT_BRANCH=$(git -C "$CWD" --no-optional-locks rev-parse --abbrev-ref HEAD 2>/dev/null)
    printf '%s' "$GIT_BRANCH" > "$cache_file"
  fi
fi
export GIT_BRANCH

echo "$input" | python ~/.claude/statusline.py
