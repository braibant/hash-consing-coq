set term pdf
set output "pigeon.pdf"
set xlabel "P(n)"
set ylabel "Time (s)"
set logscale y
set key on inside left top
plot '../pure.p.log' using 3:4 ps 0.6 pt 5 with linespoints title "Pure", \
     '../smart.p.log' using 3:4 ps 0.6 pt 9 with linespoints title "Smart", \
     '../ref-conservative.p.log' using 3:4 ps 0.6 pt 7 with linespoints title "Reference (conservative)", \
     '../ref.p.log' using 3:4 ps 0.6 pt 3 with linespoints title "Reference"


