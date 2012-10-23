all: Guess
test: all
	./Guess

%: %.hs
	ghc --make -O $@
