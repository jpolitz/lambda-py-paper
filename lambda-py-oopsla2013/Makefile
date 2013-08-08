all:
	~/src/racket-edge/racket/bin/scribble --pdf paper.scrbl
	~/src/racket-edge/racket/bin/scribble --tex paper.scrbl
	latex for-bbl.tex
	bibtex for-bbl.tex
	pdftk paper.pdf multibackground ../aec/aec-badge-a.pdf output paper-badge.pdf dont_ask

