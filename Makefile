.PHONY: all clean doc

all:
	-rm src/PipeGraph
	-$(MAKE) -C src
	cd src && ln -s . PipeGraph

clean:
	$(MAKE) -C src clean

doc:
	$(MAKE) -C src doc
