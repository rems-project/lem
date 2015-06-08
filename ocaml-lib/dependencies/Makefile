all: extract make-zarith

extract:
	mkdir -p zarith
	tar -zxvf zarith-1.3.tgz -C zarith --strip-components=1
	
clean:
	rm -rf zarith
	
make-zarith:
	cd zarith && ./configure
	make -C zarith
