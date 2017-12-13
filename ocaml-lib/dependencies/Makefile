all: zarith

zarith: zarith-1.3.tgz
	mkdir -p zarith
	tar -zxf zarith-1.3.tgz -C zarith --strip-components=1
	cd zarith && ./configure
	OCAMLOPTFLAGS=-quiet make -C zarith

install: all
	make -C zarith install

clean:
	rm -rf zarith

.PHONY: all zarith clean install
