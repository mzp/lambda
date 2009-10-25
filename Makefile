proof:
	coqc Lambda.v
	coqc TypeInv.v
clean:
	rm -f *~ *.vo *.glob