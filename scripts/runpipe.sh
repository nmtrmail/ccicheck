#!/bin/bash

# Exit on any errors
set -e
if [ -z "$1" ] || [ -z "$2" ] || [ -z "$3" ] || [ -z "$4" ]
then
  echo "Usage: ./runpipe.sh <path to tests> <list of tests> <pipeline name> <num threads>"
  exit 1
fi

# Store all of the tests in the given path into TESTS
TESTS=$(cat $2)
OUTPUTDIR=results/graphs-$3-$(date +"%m-%d-%y--%H-%M-%S-%p")

mkdir -p $OUTPUTDIR
rm -f latest
ln -s $OUTPUTDIR latest
cp ../src/ccicheck $OUTPUTDIR

# Loop over each test
date | tee $OUTPUTDIR/$3.log
parallel -j$4 --results $OUTPUTDIR time $OUTPUTDIR/ccicheck -i $1/{}.litmus -o $OUTPUTDIR/{}.gv -p $3 -f ::: $TESTS 2>&1 | egrep "BUG|Strict|WARNING" || true

echo "$0 Done!"
