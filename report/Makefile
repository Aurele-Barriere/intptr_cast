all: report.pdf

report.pdf: report.tex introduction.tex relatedworks.tex preliminaries.tex contribution.tex evaluation.tex conclusion.tex
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
