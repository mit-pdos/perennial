all: README.html EXPERIMENTS.html

%.html: %.md styles.css
	pandoc --standalone --include-in-header=styles.css $< -o "$@"
