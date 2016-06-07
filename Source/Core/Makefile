COCO = Coco.exe

# ###############################################################################
# The frame files are no longer in this directory. They must be downloaded
# from https://github.com/boogie-org/boogie-partners . Update the FRAME_DIR variable to
# point to whatever directory you install that into.
# ###############################################################################
FRAME_DIR = ..\..\..\boogiepartners\CocoR\Modified

# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
all: Parser.cs

Parser.cs: $(FRAME_DIR)\Scanner.frame $(FRAME_DIR)\Parser.frame BoogiePL.atg
	$(COCO) BoogiePL.atg -namespace Microsoft.Boogie -frames $(FRAME_DIR)

clean:
	if exist Scanner.cs del Scanner.cs
	if exist Parser.cs del Parser.cs
