if [[ $OSTYPE == 'darwin'* ]]; then
  # Override tempfile behavior in OS X as /var symlink conflicts with path traversal checks
  TMP_BASE=$HOME/.sdc_tmp
  [ -d $TMP_BASE ] && rm -rf $TMP_BASE
  mkdir $TMP_BASE
  export TMPDIR=$TMP_BASE
  SDC_HOME=${SDC_HOME:-$(mktemp -d $TMP_BASE/sd_client.XXXX)}
else
  SDC_HOME=${SDC_HOME:-$(mktemp -d)}
fi
export SDC_HOME
