PYTHON = python3
TESTS  = ./examples/brake-system.maude \
		 ./examples/gear-system.maude \
		 ./examples/p2p-protocol.maude \
		 ./examples/b-retrans-4.maude \
		 ./examples/b-retrans-5.maude 


all: $(TESTS)



%.maude: %.b ./parser/B2Maude.py
	$(PYTHON) ./parser/B2Maude.py --input $<  --output $@ 

clean:
		rm -vf $(TESTS)
		$(MAKE) -C ./parser clean
		
