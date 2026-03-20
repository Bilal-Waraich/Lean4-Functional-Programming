
#!/bin/bash

if [[ $1 -ne "--skip-fetch" ]]; then
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
  ((score += 1))
fi

if echo "$lake_output" | grep ex05 | grep -q unsolved; then
  echo "GRADER: exercise 05 is NOT solved."
else
  echo "GRADER: exercise 05 is solved."
  ((score += 1))
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
  ((score += 1))
fi

if echo "$lake_output" | grep ex10 | grep -q unsolved; then
  echo "GRADER: exercise 10 is NOT solved."
else
  echo "GRADER: exercise 10 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex11 | grep -q unsolved; then
  echo "GRADER: exercise 11 is NOT solved."
else
  echo "GRADER: exercise 11 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex12 | grep -q unsolved; then
  echo "GRADER: exercise 12 is NOT solved."
else
  echo "GRADER: exercise 12 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex13 | grep -q unsolved; then
  echo "GRADER: exercise 13 is NOT solved."
else
  echo "GRADER: exercise 13 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex14 | grep -q unsolved; then
  echo "GRADER: exercise 14 is NOT solved."
else
  echo "GRADER: exercise 14 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex15 | grep -q unsolved; then
  echo "GRADER: exercise 15 is NOT solved."
else
  echo "GRADER: exercise 15 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex16 | grep -q unsolved; then
  echo "GRADER: exercise 16 is NOT solved."
else
  echo "GRADER: exercise 16 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex17 | grep -q unsolved; then
  echo "GRADER: exercise 17 is NOT solved."
else
  echo "GRADER: exercise 17 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex18 | grep -q unsolved; then
  echo "GRADER: exercise 18 is NOT solved."
else
  echo "GRADER: exercise 18 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex19 | grep -q unsolved; then
  echo "GRADER: exercise 19 is NOT solved."
else
  echo "GRADER: exercise 19 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex20 | grep -q unsolved; then
  echo "GRADER: exercise 20 is NOT solved."
else
  echo "GRADER: exercise 20 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex21 | grep -q unsolved; then
  echo "GRADER: exercise 21 is NOT solved."
else
  echo "GRADER: exercise 21 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex22 | grep -q unsolved; then
  echo "GRADER: exercise 22 is NOT solved."
else
  echo "GRADER: exercise 22 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex23 | grep -q unsolved; then
  echo "GRADER: exercise 23 is NOT solved."
else
  echo "GRADER: exercise 23 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex24 | grep -q unsolved; then
  echo "GRADER: exercise 24 is NOT solved."
else
  echo "GRADER: exercise 24 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex25 | grep -q unsolved; then
  echo "GRADER: exercise 25 is NOT solved."
else
  echo "GRADER: exercise 25 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex26 | grep -q unsolved; then
  echo "GRADER: exercise 26 is NOT solved."
else
  echo "GRADER: exercise 26 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex27 | grep -q unsolved; then
  echo "GRADER: exercise 27 is NOT solved."
else
  echo "GRADER: exercise 27 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex28 | grep -q unsolved; then
  echo "GRADER: exercise 28 is NOT solved."
else
  echo "GRADER: exercise 28 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex29 | grep -q unsolved; then
  echo "GRADER: exercise 29 is NOT solved."
else
  echo "GRADER: exercise 29 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex30 | grep -q unsolved; then
  echo "GRADER: exercise 30 is NOT solved."
else
  echo "GRADER: exercise 30 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex31 | grep -q unsolved; then
  echo "GRADER: exercise 31 is NOT solved."
else
  echo "GRADER: exercise 31 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex32 | grep -q unsolved; then
  echo "GRADER: exercise 32 is NOT solved."
else
  echo "GRADER: exercise 32 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex33 | grep -q unsolved; then
  echo "GRADER: exercise 33 is NOT solved."
else
  echo "GRADER: exercise 33 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex34 | grep -q unsolved; then
  echo "GRADER: exercise 34 is NOT solved."
else
  echo "GRADER: exercise 34 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex35 | grep -q unsolved; then
  echo "GRADER: exercise 35 is NOT solved."
else
  echo "GRADER: exercise 35 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex36 | grep -q unsolved; then
  echo "GRADER: exercise 36 is NOT solved."
else
  echo "GRADER: exercise 36 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex37 | grep -q unsolved; then
  echo "GRADER: exercise 37 is NOT solved."
else
  echo "GRADER: exercise 37 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex38 | grep -q unsolved; then
  echo "GRADER: exercise 38 is NOT solved."
else
  echo "GRADER: exercise 38 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex39 | grep -q unsolved; then
  echo "GRADER: exercise 39 is NOT solved."
else
  echo "GRADER: exercise 39 is solved."
  ((score += 1))
fi

if echo "$lake_output" | grep ex40 | grep -q unsolved; then
  echo "GRADER: exercise 40 is NOT solved."
else
  echo "GRADER: exercise 40 is solved."
  ((score += 1))
fi

echo "GRADER: Your score is $score / 40"
