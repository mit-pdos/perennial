HTML := README.html EXPERIMENTS.html

all: $(HTML)

%.html: %.md styles.css
	pandoc --standalone --include-in-header=styles.css --metadata pagetitle="Armada artifact $(basename $@)" $< -o "$@"

clean:
	rm -f $(HTML)

.PHONY: all clean
