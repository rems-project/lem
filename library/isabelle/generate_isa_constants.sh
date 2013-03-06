#!/bin/bash - 

set -o nounset                              # Treat unset variables as an error

if test "x$ISABELLE_HOME" = "x" ; then  
  echo "No ISABELL_HOME set, using hardvode, default one (/usr/local/Isabelle)";
  ISABELLE_HOME='/usr/local/Isabelle'
fi

sed \
  -e 's/"\([a-zA-Z0-9._-\\]*\)"/\1/g' \
  -e '/(defconst/d' \
  -e "s/'(/  /g" \
  -e 's/))$//g' \
  -e '/(provide /d' \
  -e '/^[ \t]*$/d' \
  -e '/^;;/d' \
  -e 's/^[ \t]*//g' \
  $ISABELLE_HOME/etc/isar-keywords.el >constants
