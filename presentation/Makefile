all: pres

pres: pres.pdf

pres.pdf: cmds.tex style.tex pres.tex intro.tex models.tex correctnessproof.tex contrib.tex eval.tex conclusion.tex
	pdflatex pres && pdflatex pres

clean:
	rm -rf *.aux *.bbl *.blg *.log *.nav *.out *.snm *.toc
