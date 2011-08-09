import sys
import getopt
import os

BOOGIE_PATH= "%boogie%"
BCT_PATH="%boogie_bct%"
CONTROL_EXTRACTOR_PATH="%phonecontrolextractor%"
WPLIB_PATH="%wplib%"
DOT_PATH="%dotpath%"

navigation_graph = {}

def checkEnv():
  retVal= True
  os.system("echo " + DOT_PATH + " > checkEnv")
  check= open("checkEnv", "r")
  if check.readline().strip() == DOT_PATH:
    print DOT_PATH + " not set"
    retVal= False

  os.system("echo " + WPLIB_PATH + " > checkEnv")
  check= open("checkEnv", "r")
  if check.readline().strip() == WPLIB_PATH:
    print WPLIB_PATH + " not set"
    retVal= False

  os.system("echo " + BOOGIE_PATH + " > checkEnv")
  check= open("checkEnv", "r")
  if check.readline().strip() == BOOGIE_PATH:
    print BOOGIE_PATH + " not set"
    retVal= False

  os.system("echo " + BCT_PATH + " > checkEnv")
  check= open("checkEnv", "r")
  if check.readline().strip() == BCT_PATH:
    print BCT_PATH +" not set"
    retVal= False

  os.system("echo " + CONTROL_EXTRACTOR_PATH + " > checkEnv")
  check= open("checkEnv", "r")
  if check.readline().strip() == CONTROL_EXTRACTOR_PATH:
    print CONTROL_EXTRACTOR_PATH + " not set"
    retVal= False
  
  check.close()
  os.remove("checkEnv")
  return retVal

def createAppControlsFile(appFile, outputFile, format):
  error = os.system(CONTROL_EXTRACTOR_PATH + " -p \"" + os.path.dirname(appFile) + "\" -o \"" + os.path.splitext(appFile)[0] + ".controls\" > nul")
  if error != 0 or not os.path.exists(os.path.splitext(appFile)[0] + ".controls"):
    return False
  return True

def bctAppFile(appFile, outputFile, format):
  error = os.system(BCT_PATH + " /heap:splitFields /lib:\"" + WPLIB_PATH + "\" /wpnav /phoneControls:\"" + \
                    os.path.splitext(appFile)[0] + ".controls\" \"" + appFile + "\" > nul")
  if error != 0 or not os.path.exists(os.path.splitext(appFile)[0] + ".bpl"):
    return False
  return True

def testBoogieOutput(appFile, outputFile, format):
  error = os.system(BOOGIE_PATH + " /doModSetAnalysis /noVerify \"" + os.path.splitext(appFile)[0] + ".bpl\" > testBpl")
  testBpl= open("testBpl", "r")
  output= testBpl.read()
  testBpl.close()
  os.remove("testBpl")
  if error != 0 or output.find("Error:") != -1:
    return False
  return True

def createBoogieQueries(appFile, outputFile, format):
  cmd ="\"" + os.path.dirname(appFile) + "\\createQueries.bat\" > nul"
  error = os.system(cmd)
  if error != 0:
    return False
  return True

def runBoogieQueries(appFile, outputFile, format):
  global navigation_graph
  queryFiles= [os.path.abspath(filename) for filename in os.listdir(".") if filename.find("$$") != -1 and os.path.splitext(filename)[1]==".bpl"]
  for filename in queryFiles:
    start= os.path.splitext(filename.split("$$")[1])[0]
    end= os.path.splitext(filename.split("$$")[3])[0]
    try:
      dests= navigation_graph[start]
    except KeyError:
      dests= []
      navigation_graph[start]= []
    error = os.system(BOOGIE_PATH + " /doModSetAnalysis /prover:SMTLib \"" + filename +"\" > testBpl")
    testBpl= open("testBpl", "r")
    output= testBpl.read()
    testBpl.close()
    os.remove("testBpl")
    if error != 0 or output.find("Error:") != -1:
      return False
    if output.find("might not hold") != -1:
      dests.append(end)
      navigation_graph[start]= dests
  return True

def buildNavigationGraph(appFile, outputFile, format):
  global navigation_graph
  nameToNode= {}
  dotFile= open(os.path.splitext(appFile)[0] + ".dot","w")
  graphName= os.path.basename(os.path.splitext(appFile)[0])
  dotFile.write("digraph " + graphName + "{\n")
  dotFile.write("\tnode [width=\"0\" label=\"\"] n0;\n")
  nextNode=1
  for pagename in navigation_graph.keys():
    dotFile.write("\tnode [label=\"" + pagename + "\"] n"+ str(nextNode) + ";\n")
    nameToNode[pagename]=nextNode
    nextNode= nextNode + 1

  dotFile.write("\n")
  for pagename in navigation_graph.keys():
    startNode= nameToNode[pagename]
    for dest in navigation_graph[pagename]:
      destNode = nameToNode[dest]
      dotFile.write("\tn" + str(startNode) + " -> n" + str(destNode) + ";\n")

  # Try and see if we know the start page
  controls= open(os.path.splitext(appFile)[0] + ".controls", "r")
  mainpage= os.path.splitext(controls.readline().strip().lower())[0]
  try:
    globalStart= nameToNode[mainpage]
    dotFile.write("\tn0 -> n" + str(globalStart) + ";\n")
  except KeyError:
    pass

  dotFile.write("}")
  dotFile.close()
  
  if format != "dot":
    os.system(DOT_PATH + " -T" + format + " -o \"" + outputFile + "\" \"" + os.path.splitext(appFile)[0] + ".dot\" > nul")
  else:
    os.rename("\"" + os.path.splitext(appFile)[0] + ".dot\"", "\"" + outputFile + "\"")
  return True

def showUsage():
  print "NavGraphBuilder -- builds the navigation graph from a phone app. See caveats in NavGraphBuilder.README"
  print "Usage:"
  print "\tNavGraphBuilder --app <PhoneApp.dll> --output <graph file> --format <graph format>"
  print "Options:"
  print "\t--app <PhoneApp.dll>: point to location of main application .dll. Short form: -a. Required."
  print "\t--output <graph file>: file to write graph to. Short form: -o. Optional, defaults to name of phone app and selected format."
  print "\t--format <graph format>: format to draw the graph into. Short form: -f. Optional, accepts dot output formats, defaults to pdf.\n"

def main():
  if (not checkEnv()):
    sys.exit(1)
  
  try:
    opts, args= getopt.getopt(sys.argv[1:], "a:o:f:b:", ["app=","output=","format=","build="])
  except getopt.error, msg:
    print msg
    showUsage()
    sys.exit(2)

  if len(opts) < 1:
    print "Missing options"
    showUsage()
    sys.exit(2)

  appFile=""
  outputFile=""
  format=""
  build=""
  for o, a in opts:
    if o in ["-a","--app"]:
      appFile= a
    if o in ["-o", "--output"]:
      outputFile= a
    if o in ["-f", "--format"]:
      format= a.lower()
    if o in ["-b", "--build"]:
      build= a

  if format=="":
    format= "pdf"

  appFile = os.path.abspath(appFile)
  if outputFile=="":
    outputFile= os.path.splitext(appFile)[0] + "." + format
  outputFile= os.path.abspath(outputFile)    

  if build=="" or build.find("c") != -1:
    print "Extracting control information..."
    if (not createAppControlsFile(appFile, outputFile, format)):
      print "Failed to create app controls file"
      sys.exit(1)

  if build=="" or build.find("i") != -1:
    print "Injecting and translating application binary..."
    if (not bctAppFile(appFile, outputFile, format)):
      print "Failed to translate application library"
      sys.exit(1)

  if build=="" or build.find("t") != -1:
    print "Testing boogie file..."
    if (not testBoogieOutput(appFile, outputFile, format)):
      print "ByteCode Translator produced erroneous or ambiguous boogie file"
      sys.exit(1)

  if build=="" or build.find("b") != -1:
    print "Creating boogie queries..."
    if (not createBoogieQueries(appFile, outputFile, format)):
      print "Error creating boogie queries"
      sys.exit(1)

  if build=="" or build.find("q") != -1:
    print "Running boogie queries..."
    if (not runBoogieQueries(appFile, outputFile, format)):
      print "Error running boogie queries"
      sys.exit(1)

  if build=="" or build.find("g") != -1:
    print "Building graph..."
    if (not buildNavigationGraph(appFile, outputFile, format)):
      print "Error creating navigation graph"
      sys.exit(1)

  print "Success!"
  sys.exit(0)

if __name__ == "__main__":
  main()