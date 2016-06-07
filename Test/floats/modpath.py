import sys

f = open(sys.argv[1], 'r')
to_write = ""

for i in f:
	to_write += i.replace("..\\Test\\floats\\", "")
	
f.close()

f = open(sys.argv[1], 'w')

f.write(to_write)