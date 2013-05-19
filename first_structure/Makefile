Misc.vo: Misc.v
	coqc Misc.v

Buffer.vo: Buffer.v Misc.vo
	coqc Buffer.v

Deque.vo: Deque.v Misc.vo Level.vo
	coqc Deque.v

extract: Extractor.v Deque.vo
	coqtop -l Extractor.v -batch

all: Misc.vo Buffer.vo Deque.vo

refresh: Misc.vo Buffer.vo

clean:
	rm *.vo
	rm *.glob
	rm deque.ml
	rm deque.mli

.PHONY: refresh clean all extract
