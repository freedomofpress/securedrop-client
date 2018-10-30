#!/usr/bin/env bash
set -e

while [ -n "$1" ]; do
  param="$1"
  value="$2"
  case $param in
    --sdc-home)
        SDC_HOME="$value"
        shift
        ;;
    *)
    break
  esac
  shift
done

SDC_HOME=${SDC_HOME:-$(mktemp -d)}
DB_HOME=$SDC_HOME/data
LOGS_HOME=$SDC_HOME/logs

export SDC_HOME DB_HOME LOGS_HOME

mkdir -p $DB_HOME
mkdir -p $LOGS_HOME
chmod 0700 $SDC_HOME
chmod 0700 $DB_HOME
chmod 0700 $LOGS_HOME

echo "Running app with home directory: $SDC_HOME"

# create the database for local testing
./createdb.py $DB_HOME

exec python -m securedrop_client --sdc-home "$SDC_HOME" $@
