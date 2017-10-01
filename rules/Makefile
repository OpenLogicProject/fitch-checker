.PRECIOUS: %.tex

objects := $(patsubst texf/%.texf,%.svg,$(wildcard texf/*.texf))

all: $(objects)

%.tex: texf/%.texf texf/rule-template.tex forallxyyc.sty
	pandoc -f latex -t latex --template texf/rule-template.tex -o $@ $<

%.pdf: %.tex
	pdflatex $*

%.svg: %.pdf
	pdf2svg $< $@

clean:
	rm -f *.tex *.pdf *.aux *.out *.log
