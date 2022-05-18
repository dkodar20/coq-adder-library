all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -rf Makefile.coq clean
	rm -rf *.vo
	rm -rf *.vok
	rm -rf *.vos
	rm -rf *.glob
	rm -rf Makefile.coq
	rm -rf Makefile.coq.conf
	rm -rf .*.aux
	rm -rf .Makefile.coq.d

Makefile.coq: Make
	$(COQBIN)coq_makefile -f Make -o Makefile.coq

Make: ;

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean