PROLOG=swipl
SCRIPT=../src/main.pl

.PHONY: check_%.test
check_%.test:
	$(PROLOG) -s $(SCRIPT) < $*.test	

check_all: $(addprefix check_,$(wildcard *.test))
