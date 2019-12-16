# Makefile to generate the Boogie scanner and parser using Coco/R.

FRAME_DIR = .

ifeq (, $(shell dotnet tool list | grep coco))
    $(error "Coco/R not available, run dotnet tool restore")
endif

all: Scanner.cs Parser.cs

Scanner.cs Parser.cs: BoogiePL.atg $(FRAME_DIR)/Scanner.frame $(FRAME_DIR)/Parser.frame $(FRAME_DIR)/Copyright.frame
	dotnet tool run coco BoogiePL.atg -namespace Microsoft.Boogie -frames $(FRAME_DIR)

clean:
	@-rm -f Scanner.cs Scanner.cs.old Parser.cs Parser.cs.old
