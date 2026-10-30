# This file is part of Proof General.
#
# SPDX-License-Identifier: GPL-3.0-or-later

# Tests of the Eglot backend for Coq. They need Emacs >= 29 and
# coq-lsp, set COQ_LSP to use a given server.

COQ_EGLOT_TESTS:=$(wildcard coq-eglot-test-*.el)

COQ_EGLOT_SUCCESS:=$(COQ_EGLOT_TESTS:.el=.success)

.PHONY: all
all: $(COQ_EGLOT_SUCCESS)

%.success: %.el
	emacs -batch -l ../../generic/proof-site.el -l $< \
		-f ert-run-tests-batch-and-exit \
	&& touch $@

.PHONY: clean
clean:
	rm -f *.vo *.glob *.vos *.vok .*.aux *.success
	cd compile && rm -f *.vo *.glob *.vos *.vok .*.aux
