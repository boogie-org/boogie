import sys
import getopt
import os
import time

BOOGIE_PATH= "%boogie%"
BCT_PATH="%boogie_bct%"
CONTROL_EXTRACTOR_PATH="%phonecontrolextractor%"
WPLIB_PATH="%wplib%"
DOT_PATH="%dotpath%"

CONTROL_CREATION_TIME=0
INJECTION_TIME=0
TEST_TIME=0
QUERY_CREATION_TIME=0
QUERY_RUN_TIME=0
GRAPH_CREATION_TIME=0
BOOGIE_QUERY_COUNT=0
PAGE_COUNT=0
EDGE_COUNT=0

navigation_graph = {}

def createStatsNode(appFile):
  global CONTROL_CREATION_TIME
  global INJECTION_TIME
  global TEST_TIME
  global QUERY_CREATION_TIME
  global QUERY_RUN_TIME
  global GRAPH_CREATION_TIME
  global BOOGIE_QUERY_COUNT
  global PAGE_COUNT
  global EDGE_COUNT

  total= CONTROL_CREATION_TIME + INJECTION_TIME + TEST_TIME + QUERY_CREATION_TIME + QUERY_RUN_TIME + GRAPH_CREATION_TIME
  statsNode= "node [shape=plaintext, label=" + \
  "<<TABLE BORDER=\"0\" CELLBORDER=\"1\" CELLSPACING=\"0\">" + \
  "<TR><TD COLSPAN=\"2\" BGCOLOR=\"lightskyblue\">" + os.path.basename(appFile) + "</TD></TR>" + \
  "<TR><TD>Control extraction time</TD><TD>" + str(CONTROL_CREATION_TIME) + " s.</TD></TR>" + \
  "<TR><TD>Injection and translation time</TD><TD>" + str(INJECTION_TIME) + " s.</TD></TR>" + \
  "<TR><TD>Boogie test time</TD><TD>" + str(TEST_TIME) + " s.</TD></TR>" + \
  "<TR><TD>Query creation time</TD><TD>" + str(QUERY_CREATION_TIME) + " s.</TD></TR>" + \
  "<TR><TD>Boogie query run time (" + str(BOOGIE_QUERY_COUNT) + " queries)</TD><TD>" + str(QUERY_RUN_TIME) + " s.</TD></TR>" + \
  "<TR><TD>Graph creation time</TD><TD>" + str(GRAPH_CREATION_TIME) + " s.</TD></TR>" + \
  "<TR><TD BGCOLOR=\"olivedrab\">Graph sparseness</TD><TD BGCOLOR=\"olivedrab\">" + str(EDGE_COUNT) + " over " + str(PAGE_COUNT*PAGE_COUNT) + " possible</TD></TR>" + \
  "<TR><TD BGCOLOR=\"olivedrab\">Total time</TD><TD>" + str(total) + " s.</TD></TR>" + \
  "</TABLE>>" + \
  "] statsNode;"
  # statsNode= statsNode.replace(".","&#47;")
  return statsNode

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

def cleanupQueriesTempFiles():
  for tempFile in [os.path.abspath(filename) for filename in os.listdir(".") if filename.startswith("sed") and os.path.splitext(filename)[1]==""]:
    os.remove(tempFile)

def createBoogieQueries(appFile, outputFile, format):
  cmd ="\"" + os.path.dirname(appFile) + "\\createQueries.bat\" > nul"
  error = os.system(cmd)
  cleanupQueriesTempFiles()
  if error != 0:
    return False
  return True

def runBoogieQueries(appFile, outputFile, format):
  global navigation_graph
  global BOOGIE_QUERY_COUNT
  global EDGE_COUNT
  global PAGE_COUNT

  queryFiles= [os.path.abspath(filename) for filename in os.listdir(".") if filename.find("$$") != -1 and os.path.splitext(filename)[1]==".bpl"]
  BOOGIE_QUERY_COUNT= len(queryFiles)
  for filename in queryFiles:
    start= os.path.splitext(filename.split("$$")[1])[0]
    end= os.path.splitext(filename.split("$$")[3])[0]
    try:
      dests= navigation_graph[start]
    except KeyError:
      PAGE_COUNT=PAGE_COUNT+1
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
      EDGE_COUNT=EDGE_COUNT+1
  return True

def buildNavigationGraph(appFile, outputFile, format):
  global navigation_graph
  nameToNode= {}
  dotFile= open(os.path.splitext(appFile)[0] + ".dot","w")
  graphName= os.path.basename(os.path.splitext(appFile)[0])
  dotFile.write("digraph " + graphName + "{\n")
  dotFile.write("\tnode [style=\"invisible\", label=\"\"] n0;\n")
  nextNode=1
  for pagename in navigation_graph.keys():
    dotFile.write("\tnode [style=\"rounded\", shape=\"box\", label=\"" + pagename + "\"] n"+ str(nextNode) + ";\n")
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

  statsNode= createStatsNode(appFile)
  dotFile.write("\t" + statsNode + "\n")
  dotFile.write("}")
  dotFile.close()
  
  if format != "dot":
    os.system(DOT_PATH + " -T" + format + " -Kfdp -o \"" + outputFile + "\" \"" + os.path.splitext(appFile)[0] + ".dot\" > nul")
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
  global CONTROL_CREATION_TIME
  global INJECTION_TIME
  global TEST_TIME
  global QUERY_CREATION_TIME
  global QUERY_RUN_TIME
  global GRAPH_CREATION_TIME

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
    CONTROL_CREATION_TIME= time.clock();
    print "Extracting control information..."
    if (not createAppControlsFile(appFile, outputFile, format)):
      print "Failed to create app controls file"
      sys.exit(1)
    CONTROL_CREATION_TIME= time.clock() - CONTROL_CREATION_TIME

  if build=="" or build.find("i") != -1:
    INJECTION_TIME= time.clock()
    print "Injecting and translating application binary..."
    if (not bctAppFile(appFile, outputFile, format)):
      print "Failed to translate application library"
      sys.exit(1)
    INJECTION_TIME= time.clock() - INJECTION_TIME

  if build=="" or build.find("t") != -1:
    TEST_TIME= time.clock()
    print "Testing boogie file..."
    if (not testBoogieOutput(appFile, outputFile, format)):
      print "ByteCode Translator produced erroneous or ambiguous boogie file"
      sys.exit(1)
    TEST_TIME= time.clock() - TEST_TIME

  if build=="" or build.find("b") != -1:
    QUERY_CREATION_TIME= time.clock()
    print "Creating boogie queries..."
    if (not createBoogieQueries(appFile, outputFile, format)):
      print "Error creating boogie queries"
      sys.exit(1)
    QUERY_CREATION_TIME= time.clock() - QUERY_CREATION_TIME

  if build=="" or build.find("q") != -1:
    QUERY_RUN_TIME= time.clock()
    print "Running boogie queries..."
    if (not runBoogieQueries(appFile, outputFile, format)):
      print "Error running boogie queries"
      sys.exit(1)
    QUERY_RUN_TIME= time.clock() - QUERY_RUN_TIME

  if build=="" or build.find("g") != -1:
    GRAPH_CREATION_TIME= time.clock()
    print "Building graph..."
    if (not buildNavigationGraph(appFile, outputFile, format)):
      print "Error creating navigation graph"
      sys.exit(1)
    GRAPH_CREATION_TIME= time.clock() - GRAPH_CREATION_TIME

  print "Success!"
  sys.exit(0)

if __name__ == "__main__":
  main()