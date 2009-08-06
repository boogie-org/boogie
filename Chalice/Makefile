# Makefile for Chalice tool

SCALAC = scalac
SCALA = scala
CLASS_DIR = bin
SRC_DIR = src

SOURCES = $(SRC_DIR)/*.scala


all: $(CLASS_DIR)/Chalice.class

$(CLASS_DIR)/Chalice.class: $(SOURCES)
	IF NOT EXIST $(CLASS_DIR) MKDIR $(CLASS_DIR)
	$(SCALAC) -d $(CLASS_DIR) -unchecked $(SOURCES)

clean:
	del $(CLASS_DIR)\*.class

RUN_CHALICE = $(SCALA) -cp $(CLASS_DIR) -unchecked Chalice 
test: $(RUN_CHALICE) examples\cell.chalice > examples\results\cell.chalice.expected
