all: Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -rv Makefile.coq clean
	rm -rv *.vo
	rm -rv *.vok
	rm -rv *.vos
	rm -rv *.glob
	rm -rv Makefile.coq
	rm -rv Makefile.coq.conf
	rm -rf .*.aux
	rm -rv .Makefile.coq.d

Makefile.coq: Make
	$(COQBIN)coq_makefile -f Make -o Makefile.coq

Make: ;

%: Makefile.coq
	+make -f Makefile.coq $@

.PHONY: all clean