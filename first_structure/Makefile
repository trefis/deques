Misc.vo: Misc.v
	coqc Misc.v

Level.vo: Level.v Misc.vo
	coqc Level.v

Deque.vo: Deque.v Misc.vo Level.vo
	coqc Deque.v

extract: Extractor.v Deque.vo
	coqtop -l Extractor.v -batch

all: Misc.vo Level.vo Deque.vo

refresh: Misc.vo Level.vo

clean:
	rm *.vo
	rm *.glob
	rm deque.ml
	rm deque.mli

.PHONY: refresh clean all extract
