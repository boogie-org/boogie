import os
import glob
import sys
import datetime

bindir = "bin"
    
srcspecs = ["src\\*.scala"]
srcfiles = [file for spec in srcspecs for file in glob.glob(spec)]

buildstamp = "makestamp"

lastbuild = None
if os.path.exists(buildstamp):
    lastbuild = os.path.getmtime(buildstamp)

if not os.path.exists(bindir):
    os.makedirs(bindir)

changedfiles = [file for file in srcfiles if not lastbuild or lastbuild <= os.path.getmtime(file)]

if not changedfiles:
    print "Build is up-to-date."
    sys.exit(0)

def printtime():
    print datetime.datetime.now().strftime("%H:%M:%S")

printtime()
cmd = "scalac -d bin -unchecked -deprecation " + " ".join(changedfiles) + " & if errorlevel 1 exit 1"
print cmd
result = os.system(cmd)
printtime()

if result == 0:
    open(buildstamp, "w").close()
else:
    print "Build failed."
