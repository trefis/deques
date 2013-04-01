Misc.vo: Misc.v
	coqc Misc.v

Level.vo: Level.v Misc.vo
	coqc Level.v

Deque.vo: Deque.v Misc.vo Level.vo
	coqc Deque.v

all: Misc.vo Level.vo Deque.vo

extract: Extractor.v Deque.vo
	coqtop -l Extractor.v -batch

refresh: Misc.vo Level.vo

clean:
	rm *.vo
	rm *.glob

.PHONY: refresh clean all
