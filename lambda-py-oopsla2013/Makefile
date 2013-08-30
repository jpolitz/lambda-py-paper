all:
	~/src/racket-edge/racket/bin/scribble --pdf paper.scrbl
	~/src/racket-edge/racket/bin/scribble --latex paper.scrbl
	latex for-bbl.tex
	bibtex for-bbl
	pdftk paper.pdf multibackground ../aec/aec-badge-a.pdf output paper-badge.pdf dont_ask
	~/src/racket-edge/racket/bin/scribble --pdf appendix.scrbl

