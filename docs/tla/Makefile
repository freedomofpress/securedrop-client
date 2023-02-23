Reply: Reply.png

%.png: %.dot Makefile
	dot -Tpng $< > $@

%.dot: %.tla %.cfg
	$(TLA_BIN) $< \
		-tool \
		-modelcheck \
		-coverage 1 \
		-config $(<:.tla=.cfg) \
		-dump dot,actionable,colorize \
		$@