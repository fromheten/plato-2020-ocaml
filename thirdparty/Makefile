.PHONY: clean all

PREFIX=$(PWD)/target
LDFLAGS="-L$(PREFIX)/lib"
CFLAGS='-I$(PREFIX)/include'
# LD_C_FLAGS=$(LDFLAGS) $(CFLAGS)
LD_C_FLAGS=LDFLAGS="-L$(PREFIX)/lib" CFLAGS='-I$(PREFIX)/include -Ofast'

clean:
	rm -rf target/ build/ bdwgc/ libatomic_ops/ c-rrb/ sds/ hash-array-mapped-trie/

libatomic_ops/:
	git clone git://github.com/ivmai/libatomic_ops.git

bdwgc/: libatomic_ops/
	git clone git://github.com/ivmai/bdwgc.git
	ln -s libatomic_ops bdwgc/libatomic_ops

target/include/gc.h: bdwgc/
	echo $(PREFIX)
	mkdir -p target/include target/lib build
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
	mkdir -p target/include target/lib build/
	cc -c sds/sds.c
	ar -r sds.a sds.o
	mv sds.a target/lib/libsds.a
	rm sds.o
	cp sds/sds.h target/include/sds.h

hash-array-mapped-trie-poly/:
	git clone https://github.com/fromheten/hash-array-mapped-trie-poly.git
	cd hash-array-mapped-trie-poly && git checkout 2.1 && git log -n1

target/include/hamt.h: hash-array-mapped-trie-poly/
	cp hash-array-mapped-trie-poly/hamt.h $@

all: target/include/gc.h target/include/sds.h target/include/sds.h target/include/rrb.h target/ target/include/hamt.h
