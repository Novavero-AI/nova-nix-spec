#!/bin/sh
# Runs a checker over the databases in a metamath-test checkout, which are read
# as data. The expected verdicts are the ones that suite publishes.
#
# Usage: run-suite.sh CHECKER SUITE_DIR

if [ "$#" -ne 2 ]; then
  echo "usage: run-suite.sh CHECKER SUITE_DIR" >&2
  exit 2
fi
checker=$1
suite=$2
failed=0

check() {
  expected=$1
  database=$2
  if (cd "$suite" && "$checker" "$database") >/dev/null 2>&1; then
    got=accept
  else
    got=refuse
  fi
  if [ "$got" = "$expected" ]; then
    echo "ok      $expected $database"
  else
    echo "FAILED  wanted $expected, got $got: $database"
    failed=$((failed + 1))
  fi
}

check accept anatomy.mm
check refuse anatomy-bad1.mm
check refuse anatomy-bad2.mm
check refuse anatomy-bad3.mm
check accept big-unifier.mm
check refuse big-unifier-bad1.mm
check refuse big-unifier-bad2.mm
check refuse big-unifier-bad3.mm
check accept demo0.mm
check refuse demo0-bad1.mm
check accept demo0-includer.mm
check accept emptyline.mm
check accept hol.mm
check accept iset.mm
check accept miu.mm
check accept nf.mm
check accept peano-fixed.mm
check accept ql.mm
check accept set.2010-08-29.mm
check accept set.mm
check refuse set-dist-bad1.mm

if [ "$failed" -ne 0 ]; then
  echo "$failed failed"
  exit 1
fi
echo "all passed"
