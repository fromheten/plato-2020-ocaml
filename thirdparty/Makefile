.PHONY: clean

clean:
	rm -rf bdwgc/ libatomic_ops/

libatomic_ops/:
	git clone git://github.com/ivmai/libatomic_ops.git

bdwgc/: libatomic_ops/
	git clone git://github.com/ivmai/bdwgc.git

bdwgc/cool-lib.dylib: bdwgc/
	ln -s libatomic_ops bdwgc/libatomic_ops
	cd bdwgc && ./autogen.sh
	cd bdwgc && export PREFIX=$PWD/build-aux && ./configure --disable-dependency-tracking --prefix=/Users/martin/code/plato-2020-ocaml/thirdparty/bdwgc/build-aux
	cd bdwgc && make
	cd bdwgc && make check
	cd bdwgc && make install
