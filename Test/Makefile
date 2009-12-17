TESTS_FILE = alltests.txt
LONG = $(shell awk '{ if (tolower($$2) ~ /^long$$/) print $$1 }' $(TESTS_FILE))
NORMAL = $(shell awk '{ if (tolower($$2) ~ /^use$$/) print $$1 }' $(TESTS_FILE))
TESTS = $(NORMAL)

all: $(addprefix run-, $(TESTS))
	@echo ALL OK


show:
	@echo $(TESTS)

long:
	$(MAKE) TESTS="$(NORMAL) $(LONG)" all

run-%:
	@./runtest.bat $*
