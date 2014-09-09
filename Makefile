CC	?= cc
CFLAGS	:= -std=c99 -pedantic -Wall -Wextra

mz: mz.c
	$(CC) $(CFLAGS) -o $@ mz.c

clean:
	rm -f mz
