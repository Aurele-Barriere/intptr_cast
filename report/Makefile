all: report.pdf

report.pdf: report.tex introduction.tex relatedworks.tex preliminaries.tex memupdate.tex meminj.tex mixedsim.tex capturesem.tex evaluation.tex conclusion.tex appendix.tex ../bib/intptrcast.bib
	pdflatex report.tex
	bibtex report.aux
	pdflatex report.tex
	pdflatex report.tex

clean:
	-rm *.aux
	-rm *.bbl
	-rm *.log
	-rm *.blg
	-rm *.toc
	-rm report.pdf
