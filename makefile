CC=gcc
CFLAGS=-W -Wall -Wextra -O3 -g -g
DEPQBFDIR=libs/depqbf




all: outer-count.c
	${CC} ${CFLAGS} outer-count.c -o outer-count \
		-L${DEPQBFDIR} -lqdpll -I${DEPQBFDIR}

clean:
	rm -f *.o

.PHONY: all clean 
