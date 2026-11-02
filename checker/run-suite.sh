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

# Only exit status 1 is a refusal. A crash on a bad database is not one.
check() {
  expected=$1
  database=$2
  status=0
  output=$(cd "$suite" && "$checker" "$database" 2>&1) || status=$?
  case "$status" in
    0) got=accept ;;
    1) got=refuse ;;
    *) got="crash, status $status" ;;
  esac
  if [ "$got" = "$expected" ]; then
    echo "ok      $expected $database"
  else
    echo "FAILED  wanted $expected, got $got: $database: $output"
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
