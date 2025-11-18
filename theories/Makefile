all: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq all

clean: Makefile.rocq
	@+$(MAKE) -f Makefile.rocq clean

mrproper: clean
	rm -f Makefile.rocq Makefile.rocq.conf
	find \( -name "*.aux" -o -name "*.vo*" -o -name "*.glob" \) -exec rm -f {} \;

Makefile.rocq: _CoqProject
	$(COQBIN)rocq makefile -f _CoqProject -o Makefile.rocq

force _CoqProject Makefile: ;

whitespaces: force
	find . -type f -name "*.v" -exec sed --in-place 's/[[:space:]]\+$$//' {} \+

wc: force
	coqwc `find -name "*.v"`

%: Makefile.rocq force
	@+$(MAKE) -f Makefile.rocq $@

.PHONY: all clean force

