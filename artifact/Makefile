HTML := README.html EXPERIMENTS.html

all: $(HTML)

%.html: %.md styles.css
	pandoc --standalone --include-in-header=styles.css $< -o "$@"

clean:
	rm -f $(HTML)

.PHONY: all clean
