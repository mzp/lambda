Src := Lambda.v TypeInv.v TypeUniq.v CannonicalForm.v Progress.v
Obj := $(patsubst %.v,%.vo,$(Src))

proof: $(Obj)

%.vo %.glob : %.v
	coqc $<

clean:
	rm -f *~ *.vo *.glob