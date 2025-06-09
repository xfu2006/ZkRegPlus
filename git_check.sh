# list all files greater than 1MB in the git_stage area.
git diff --cached --name-only | while read file; do
  size=$(git cat-file -s :$file)
  if [ "$size" -gt 1048576 ]; then
    echo "$file ($((size / 1024)) KB)"
  fi
done

