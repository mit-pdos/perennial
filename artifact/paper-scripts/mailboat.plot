set terminal png size 600,428
set output "mailboat.png"

set auto x
set yrange [0:*]
set grid y
set xtics 1
set ylabel "requests / sec"
set format y '%.0s%c'
set xlabel "# cores"
set key top left
if (!exists("numcores")) numcores=12

set style data line

plot \
  "mailboat.data" using 1:(numcores*100000/$2) with linespoints title 'Mailboat', \
  "gomail.data" using 1:(numcores*100000/$2) with linespoints title 'GoMail', \
  "cmail.data"  using 1:(numcores*100000/$2) with linespoints title 'CMAIL',
