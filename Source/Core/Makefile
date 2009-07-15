COCO = ..\..\Binaries\Coco.exe
ASML = ..\..\Binaries\asmlc.boot.exe

# "all" depends on 2 files, really (Parser.cs and Scanner.cs), but they
# are both generated in one go and I don't know a better way to tell
# nmake that.  --KRML
all: Parser.ssc 

#Graph.dll: Graph.as
#  $(ASML) /target:library Graph.as
  
Parser.ssc: Scanner.frame Parser.frame BoogiePL.atg
	$(COCO) BoogiePL.atg
	copy Parser.cs Parser.ssc
	copy Scanner.cs Scanner.ssc

clean:
	rm -f Scanner.ssc Parser.ssc
