.DEFAULT_GOAL = Everything.agdai
AGDA = agda
STACK = stack
VERBOSITY = 0

-include env.mk

EVERYTHING_DIR = tools/everything
EVERYTHING_STACK_YAML = $(EVERYTHING_DIR)/stack.yaml
EVERYTHING_STACK = $(STACK) --stack-yaml='$(EVERYTHING_STACK_YAML)'


Everything.agda: $(shell find Cats -type d)
	$(EVERYTHING_STACK) build --exec everything

Everything.agdai: Everything.agda
	$(AGDA) --verbose='$(VERBOSITY)' Everything.agda

clean:
	rm -f Everything.agda Everything.agdai
	find Cats -name '*.agdai' -delete
	$(EVERYTHING_STACK) clean --full
