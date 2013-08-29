markdown_targets := $(patsubst %.markdown,%.html,$(wildcard *.markdown))

markdown: $(markdown_targets)

%.html : %.markdown
	markdown $< > $@
