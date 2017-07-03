all: compcert gcco1 gcco2

compcert: test.c
	../CompCert-intptr/ccomp -stdlib ../CompCert-intptr/runtime test.c -o compcert

gcco1: test.c
	gcc -O1 test.c -o gcco1

gcco2: test.c
	gcc -O2 test.c -o gcco2
