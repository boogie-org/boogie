# Makefile for Chalice tool

SCALAC = scalac
SCALA = scala
CLASS_DIR = bin
SRC_DIR = src


all: $(CLASS_DIR)/Chalice.class

SOURCES = $(SRC_DIR)/*.scala

$(CLASS_DIR)/Chalice.class: $(SOURCES)
	IF NOT EXIST $(CLASS_DIR) MKDIR $(CLASS_DIR)
	$(SCALAC) -d $(CLASS_DIR) -unchecked $(SOURCES)

clean:
	rm -f $(CLASS_DIR)/*.class

RUN_CHALICE = $(SCALA) -cp $(CLASS_DIR) -unchecked Chalice 
RUN_BOOGIE = ..\Binaries\boogie.exe
test: $(RUN_CHALICE) examples\cell.chalice > examples\results\cell.chalice.expected

try: $(CLASS_DIR)/Chalice.class
	$(RUN_CHALICE) prog3.chalice > prog3.bpl
	$(RUN_BOOGIE) prog3.bpl /smoke
