Misc.vo: Misc.v
	coqc Misc.v

Buffer.vo: Buffer.v Misc.vo
	coqc Buffer.v

Level.vo: Level.v Misc.vo Buffer.vo
	coqc Level.v

Stack.vo: Stack.v Misc.vo Buffer.vo Level.vo
	coqc Stack.v

Deque.vo: Deque.v Misc.vo Buffer.vo Level.vo Stack.vo
	coqc Deque.v

extract: Extractor.v Deque.vo
	coqtop -l Extractor.v -batch

all: Misc.vo Buffer.vo Level.vo Stack.vo Deque.vo

refresh: Misc.vo Buffer.vo Level.vo Stack.vo

clean:
	rm *.vo
	rm *.glob
	rm *.ml
	rm *.mli

.PHONY: refresh clean all extract
