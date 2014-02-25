set term pdf
set output "urquhart.pdf"
set xlabel "U(n)"
set ylabel "Time (s)"
set logscale y
set key on inside left top
plot '../pure.u.log' using 3:4 ps 0.3 pt 5 with linespoints title "Pure", \
     '../smart.u.log' using 3:4 ps 0.3 pt 9 with linespoints title "Smart", \
     '../ref-conservative.u.log' using 3:4 ps 0.3 pt 7 with linespoints title "Reference (conservative)", \
     '../ref.u.log' using 3:4 ps 0.3 pt 7 with linespoints title "Reference"


