CARGO := cargo --offline

.PHONY: all dev debug rel release clean

all: release

dev: debug

debug:
	$(CARGO) build --lib --bins

rel: release

release:
	$(CARGO) build --release --lib --bins

clean:
	rm -rf Cargo.lock target
