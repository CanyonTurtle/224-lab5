ls ./traces/ | sed 's/^/traces\//' | xargs -n1 ./mdriver -f | sed -n '/Perf/p' > tracesoutputs.txt
ls ./traces/ | sed -n '/\.rep/p' > tracelist.txt
paste tracesoutputs.txt tracelist.txt | column -s $'\t' -t
