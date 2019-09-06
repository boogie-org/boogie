# Makefile to generate the Boogie scanner and parser using Coco/R.

# If the Coco/R binary below for some reason does not work for you, consider
# compiling the source code in ../../ThirdParty/Coco/src.
COCO_EXE = ../../ThirdParty/Coco/bin/Coco.exe
FRAME_DIR = ../../ThirdParty/Coco/frames

ifeq ($(OS),Windows_NT)
    COCO = $(COCO_EXE)
else
    COCO = mono $(COCO_EXE)
endif

all: Scanner.cs Parser.cs

Scanner.cs Parser.cs: BoogiePL.atg $(FRAME_DIR)/Scanner.frame $(FRAME_DIR)/Parser.frame $(FRAME_DIR)/Copyright.frame
	$(COCO) BoogiePL.atg -namespace Microsoft.Boogie -frames $(FRAME_DIR)

clean:
	@-rm -f Scanner.cs Scanner.cs.old Parser.cs Parser.cs.old
