.PHONY: clean all

PREFIX=/Users/martin/code/plato-2020-ocaml/thirdparty/target
LD_C_FLAGS=LDFLAGS="-L$(PREFIX)/lib" CFLAGS='-I$(PREFIX)/include -Ofast'

clean:
	rm -rf bdwgc/ libatomic_ops/ c-rrb/ sds/

libatomic_ops/:
	git clone git://github.com/ivmai/libatomic_ops.git

bdwgc/: libatomic_ops/
	git clone git://github.com/ivmai/bdwgc.git
	ln -s libatomic_ops bdwgc/libatomic_ops

target/include/gc.h: bdwgc/
	echo $(PREFIX)
	cp -R bdwgc build/bdwgc
	cd build/bdwgc && ./autogen.sh
	cd build/bdwgc && ./configure --disable-dependency-tracking --disable-shared --prefix=$(PREFIX)
	cd build/bdwgc && make
	cd build/bdwgc && make check
	cd build/bdwgc && make install
	rm -rf build/bdwgc

c-rrb/:
	git clone https://github.com/hypirion/c-rrb.git

target/include/rrb.h: c-rrb/ target/include/gc.h
	echo $(PREFIX)
	cp -R c-rrb build/c-rrb
	cd build/c-rrb ; autoreconf --install
	cd build/c-rrb ; $(LD_C_FLAGS) ./configure --disable-shared --prefix=$(PREFIX)
	cd build/c-rrb ; make
	cd build/c-rrb ; make check
	cd build/c-rrb ; make install
	rm -rf build/c-rrb

sds/:
	git clone https://github.com/antirez/sds.git

target/include/sds.h: sds/
	cc -c sds/sds.c
	ar -r sds.a sds.o
	mv sds.a target/lib/libsds.a
	rm sds.o
	cp sds/sds.h target/include/sds.h

all: target/include/gc.h target/include/sds.h target/include/sds.h target/include/rrb.h
