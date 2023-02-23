This directory contains TLA+ models for specific Client behavior. Each
`$MODEL.tla` is documented:

- in its accompanying configuration `$MODEL.cfg`;
- with a preamble, above the (e.g.) `---- MODULE Reply ----` line;
- inline; and
- with any footnotes or concluding commentary below the `====` line.

With `$TLA_BIN` set in your path, you can run `make $MODEL` to run the model and
render its state graph. (Or you can let the [TLA+ extension] for Visual Studio
Code/Codium do all this for you.)

## See also

- [Cory's TLA+ resources]

[cory's tla+ resources]: https://wiki.freedom.press/wiki/User:Cory/TLA+
[tla+ extension]: https://marketplace.visualstudio.com/items?itemName=alygin.vscode-tlaplus
