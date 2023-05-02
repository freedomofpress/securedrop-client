Reply: Reply.png

%.png: %.dot Makefile
	dot -Tpng $< > $@

%.dot: %.tla %.cfg TLA_BIN
	$(TLA_BIN) $< \
		-tool \
		-modelcheck \
		-coverage 1 \
		-config $(<:.tla=.cfg) \
		-dump dot,actionable,colorize \
		$@

TLA_BIN:
ifndef TLA_BIN
	$(error Missing $$TLA_BIN. Download "tla2tools.jar" from <https://github.com/tlaplus/tlaplus/releases> and set $$TLA_BIN to that path)
endif
