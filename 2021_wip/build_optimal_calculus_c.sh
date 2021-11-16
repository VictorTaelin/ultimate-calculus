clang -O3 -c -o optimal_calculus.o optimal_calculus.c
clang -O3 -shared -Wl -o optimal_calculus.dylib optimal_calculus.o
