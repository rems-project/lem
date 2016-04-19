all: zarith/zarith.cma

zarith/zarith.cma: zarith-1.3.tgz
	mkdir -p zarith
	tar -zxf zarith-1.3.tgz -C zarith --strip-components=1
	cd zarith && ./configure > /dev/null
	OCAMLOPTFLAGS=-quiet make -C zarith

clean:
	rm -rf zarith

.PHONY: all clean
