proof:
	coqc Lambda.v
	coqc TypeInv.v
	coqc TypeUniq.v
clean:
	rm -f *~ *.vo *.glob