
#!/bin/bash

if [[ "$1" != "--skip-fetch" ]]; then
  echo "GRADER: Checking for upstream chanegs."
  if ! git fetch; then
    echo "GRADER: Fetch failed, please run it manually."
    echo "GRADER: You can pass --skip-fetch to this script if you're sure your branch is not behind."
    exit 1
  fi

  if [[ $(git rev-list HEAD..@{u} --count) -gt 0 ]]; then
    echo "GRADER: Your branch is behind the remote, please git pull before running this script."
    exit 1
  fi
fi

lake_output=$(lake build)
if [[ $? -gt 0 ]]; then
  echo "GRADER: Your build has failed. If you submit this solution, you will get 0 points."
  echo "GRADER: Output from lake build:"
  echo "$lake_output"
  echo "GRADER: Your build has failed. If you submit this solution, you will get 0 points."
  echo "GRADER: Fix your build errors before submitting."
  exit 1
fi
score=0

if echo "$lake_output" | grep ex01 | grep -q unsolved; then
  echo "GRADER: exercise 01 is NOT solved."
else
  echo "GRADER: exercise 01 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex02 | grep -q unsolved; then
  echo "GRADER: exercise 02 is NOT solved."
else
  echo "GRADER: exercise 02 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex03 | grep -q unsolved; then
  echo "GRADER: exercise 03 is NOT solved."
else
  echo "GRADER: exercise 03 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex04 | grep -q unsolved; then
  echo "GRADER: exercise 04 is NOT solved."
else
  echo "GRADER: exercise 04 is solved."
  ((score += 3))
fi

if echo "$lake_output" | grep ex05 | grep -q unsolved; then
  echo "GRADER: exercise 05 is NOT solved."
else
  echo "GRADER: exercise 05 is solved."
  ((score += 3))
fi

if echo "$lake_output" | grep ex06 | grep -q unsolved; then
  echo "GRADER: exercise 06 is NOT solved."
else
  echo "GRADER: exercise 06 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex07 | grep -q unsolved; then
  echo "GRADER: exercise 07 is NOT solved."
else
  echo "GRADER: exercise 07 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex08 | grep -q unsolved; then
  echo "GRADER: exercise 08 is NOT solved."
else
  echo "GRADER: exercise 08 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex09 | grep -q unsolved; then
  echo "GRADER: exercise 09 is NOT solved."
else
  echo "GRADER: exercise 09 is solved."
  ((score += 2))
fi

if echo "$lake_output" | grep ex10 | grep -q unsolved; then
  echo "GRADER: exercise 10 is NOT solved."
else
  echo "GRADER: exercise 10 is solved."
  ((score += 2))
fi

if echo "$lake_output" | grep ex11 | grep -q unsolved; then
  echo "GRADER: exercise 11 is NOT solved."
else
  echo "GRADER: exercise 11 is solved."
  ((score += 2))
fi

if echo "$lake_output" | grep ex12 | grep -q unsolved; then
  echo "GRADER: exercise 12 is NOT solved."
else
  echo "GRADER: exercise 12 is solved."
  ((score += 4))
fi

echo "GRADER: Your score is $score / 22"
