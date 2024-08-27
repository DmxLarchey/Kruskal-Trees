all: Makefile.coq
	@+$(MAKE) -f Makefile.coq all

clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq clean

mrproper: clean
	rm -f Makefile.coq Makefile.coq.conf
	find \( -name "*.aux" -o -name "*.vo*" -o -name "*.glob" \) -exec rm -f {} \;

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

force _CoqProject Makefile: ;

whitespaces: force
	find . -type f -name "*.v" -exec sed --in-place 's/[[:space:]]\+$$//' {} \+

wc: force
	coqwc `find -name "*.v"`

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

.PHONY: all clean force
