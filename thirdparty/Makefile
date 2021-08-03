.PHONY: clean

PREFIX=/Users/martin/code/plato-2020-ocaml/thirdparty/target

clean:
	rm -rf bdwgc/ libatomic_ops/ c-rrb/

libatomic_ops/:
	git clone git://github.com/ivmai/libatomic_ops.git

bdwgc/: libatomic_ops/
	git clone git://github.com/ivmai/bdwgc.git
	ln -s libatomic_ops bdwgc/libatomic_ops

target/include/gc.h: bdwgc/
	echo $(PREFIX)
	cd bdwgc && ./autogen.sh
	cd bdwgc && ./configure --disable-dependency-tracking --disable-shared --prefix=$(PREFIX)
	cd bdwgc && make
	cd bdwgc && make check
	cd bdwgc && make install

c-rrb/:
	git clone https://github.com/hypirion/c-rrb.git

target/c-rrb/: c-rrb/ target/include/gc.h
	echo $(PREFIX)
	cd c-rrb ; autoreconf --install
	cd c-rrb ; ./configure --help=short
	cd c-rrb ; LDFLAGS="-L$(PREFIX)/lib" CFLAGS='-I$(PREFIX)/include -Ofast' ./configure --disable-shared --prefix=$(PREFIX)
	cd c-rrb ; make
	cd c-rrb ; make check
	cd c-rrb ; make install
