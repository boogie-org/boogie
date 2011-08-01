import sys
import getopt
import os
from xml.dom import minidom
from itertools import product
import xml.dom

CONTROL_NAMES= ["Button", "CheckBox", "RadioButton"]
CONTAINER_CONTROL_NAMES= ["Canvas", "Grid", "StackPanel"]

# TODO externalize strings, share with C# code
CONTINUEONPAGE_VAR= "__BOOGIE_ContinueOnPage__"

staticControlsMap= {}
mainPageXAML= None
mainAppClassname= None
appVarName = "__BOOGIE_APP_VAR"
currentNavigationVariable= None
originalPageVars= []
boogiePageVars= []
boogiePageClasses= []
dummyPageVar= "dummyBoogieStringPageName"

def showUsage():
  print "PhoneBoogieCodeGenerator -- create boilerplate code for Boogie verification of Phone apps"
  print "Usage:"
  print "\tPhoneBoogieCodeGenerator --controls <app_control_info_file> --output <code_output_file>\n"
  print "Options:"
  print "\t--controls <app_control_info_file>: Phone app control info. See PhoneControlsExtractor. Short form: -c"
  print "\t--output <code_output_file>: file to write with boilerplate code. Short form: -o\n"

def loadControlInfo(infoMap, controlClass, controlName, enabled, visible, clickHandler, checkedHandler, uncheckedHandler, bplName):
  newControl={}
  newControl["class"]= controlClass
  newControl["enabled"]= enabled
  newControl["visible"]= visible
  newControl["clickHandler"]= clickHandler
  newControl["checkedHandler"]= checkedHandler
  newControl["uncheckedHandler"]= uncheckedHandler
  newControl["bplName"]=bplName
  infoMap[controlName]= newControl

def outputPageVariables(file):
  global originalPageVars
  global boogiePageVars
  global boogiePageClasses

  file.write("var " + appVarName + ": Ref;\n")
  for entry in staticControlsMap.keys():
    pageVarName= "__BOOGIE_PAGE_VAR_" + entry
    originalPageVars.append(entry)
    pageInfo={}
    pageInfo["name"]=pageVarName
    pageInfo["boogieStringName"]= staticControlsMap[entry]["boogieStringName"]
    boogiePageVars.append(pageInfo)
    boogiePageClasses.append(staticControlsMap[entry]["class"])
    pageVar= "var " + pageVarName + ": Ref;\n"
    file.write(pageVar)

def outputMainProcedures(file, batFile):
  for i,j in product(range(0, len(boogiePageVars)),repeat=2):
    if i == j:
      continue
    if (boogiePageVars[i]["boogieStringName"] == dummyPageVar):
      continue
    if (boogiePageVars[j]["boogieStringName"] == dummyPageVar):
      continue

    file.write("procedure __BOOGIE_VERIFICATION_PROCEDURE_" + str(i) + "_" + str(j) + "();\n")
    file.write("implementation __BOOGIE_VERIFICATION_PROCEDURE_" + str(i) + "_" + str(j) + "() {\n")
    file.write("\tvar $doWork: bool;\n")
    file.write("\tvar $activeControl: int;\n")
    file.write("\tvar $isEnabledRef: Ref;\n")
    file.write("\tvar $isEnabled: bool;\n")
    file.write("\tvar $control: Ref;\n\n")

    file.write("\tcall " + mainAppClassname + ".#ctor(" + appVarName + ");\n")
    for k in range(0,len(boogiePageVars)):
      file.write("\tcall " + boogiePageClasses[k] + ".#ctor(" + boogiePageVars[k]["name"] + ");\n")

    file.write("\t//TODO still need to call Loaded handler on main page.\n")
    file.write("\thavoc $doWork;\n")
    file.write("\twhile ($doWork) {\n")
    file.write("\t\tcall DriveControls();\n")
    file.write("\t\thavoc $doWork;\n")
    file.write("\t}\n")

    file.write("\tassume " + currentNavigationVariable + " == " + boogiePageVars[i]["boogieStringName"] + ";\n")
    file.write("\tcall DriveControls();\n")
    file.write("\tassume " + currentNavigationVariable + " == " + boogiePageVars[j]["boogieStringName"] + ";\n")
    file.write("\tassert false;\n");
    file.write("}\n")

    batFile.write("type BOOGIE_PARTIAL.bpl > BOOGIE_PLACEHOLDER.bpl\n")
    batFile.write("type BOOGIE_BOILERPLATE.bpl >> BOOGIE_PLACEHOLDER.bpl\n")
    batFile.write("%POIROT_ROOT%\Corral\BctCleanup.exe BOOGIE_PLACEHOLDER.bpl BOOGIE_PLACEHOLDER_Clean.bpl /main:__BOOGIE_VERIFICATION_PROCEDURE_" + str(i) + "_" + str(j) +"\n");
    batFile.write("del corral_out_trace.txt\n")
    batFile.write("%POIROT_ROOT%\corral\corral.exe /k:1 /recursionBound:20 /main:__BOOGIE_VERIFICATION_PROCEDURE_" + str(i) +"_" + str(j) + " BOOGIE_PLACEHOLDER_Clean_" + str(i) + "_" + str(j) + ".bpl\n")
    batFile.write("if exist corral_out_trace.txt move corral_out_trace.txt corral_out_trace_" + str(i) + "_" + str(j) + ".txt\n")

def outputPageControlDriver(file, originalPageName, boogiePageName):
  file.write("procedure drive" + boogiePageName + "Controls();\n")
  file.write("implementation drive" + boogiePageName + "Controls() {\n")
  file.write("\tvar $activeControl: int;\n")
  file.write("\tvar $control: Ref;\n")
  file.write("\tvar $isEnabledRef: Ref;\n")
  file.write("\tvar $isEnabled: bool;\n")
  file.write("\tvar $handlerToActivate: int;\n")

  file.write("\t" + CONTINUEONPAGE_VAR +":=true;\n")
  file.write("\thavoc $activeControl;\n")
  file.write("\twhile (" + CONTINUEONPAGE_VAR + ") {\n")
  activeControl=0
  ifInitialized= False
  for entry in staticControlsMap[originalPageName]["controls"].keys():
    controlInfo= staticControlsMap[originalPageName]["controls"][entry]
    if controlInfo["bplName"] == "":
      continue
    if not ifInitialized:
      file.write("\t\tif ($activeControl == str(activeControl)) {\n")
      ifInitialized= True
    else:
      file.write("\t\telse if ($activeControl == " + str(activeControl) + ") {\n")
    
    file.write("\t\t\t$control := " + controlInfo["bplName"] + "[" + boogiePageName + "];\n")
    file.write("\t\t\tcall $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);\n")
    file.write("\t\t\t$isEnabled := Box2Bool(Ref2Box($isEnabledRef));\n")
    file.write("\t\t\tif ($isEnabled) {\n")
    file.write("\t\t\t\thavoc $handlerToActivate;\n")
    if not controlInfo["clickHandler"] == "":
      file.write("\t\t\t\tif ($handlerToActivate == 0) {\n")
      file.write("\t\t\t\t\tcall " + staticControlsMap[originalPageName]["class"] + "." + controlInfo["clickHandler"] + "$System.Object$System.Windows.RoutedEventArgs(" + controlInfo["bplName"] + "[" + boogiePageName + "],null,null);\n")
      file.write("\t\t\t\t}\n")
    if not controlInfo["checkedHandler"] == "":
      file.write("\t\t\t\tif ($handlerToActivate == 1) {\n")
      file.write("\t\t\t\t\tcall " + staticControlsMap[originalPageName]["class"] + "." + controlInfo["checkedHandler"] + "$System.Object$System.Windows.RoutedEventArgs(" + controlInfo["bplName"] + "[" + boogiePageName + "],null,null);\n")
      file.write("\t\t\t\t}\n")
    if not controlInfo["uncheckedHandler"] == "":
      file.write("\t\t\t\tif ($handlerToActivate == 2) {\n")
      file.write("\t\t\t\t\tcall " + staticControlsMap[originalPageName]["class"] + "." + controlInfo["uncheckedHandler"] + "$System.Object$System.Windows.RoutedEventArgs(" + controlInfo["bplName"] + "[" + boogiePageName + "],null,null);\n")
      file.write("\t\t\t\t}\n")

    file.write("\t\t\t}\n")
    file.write("\t\t}\n")
    activeControl= activeControl+1
  file.write("\t}\n")
  file.write("}\n")


def outputControlDrivers(file, batFile):
  for i in range(0,len(boogiePageVars)):
    outputPageControlDriver(file, originalPageVars[i],boogiePageVars[i]["name"])

  file.write("procedure DriveControls();\n")
  file.write("implementation DriveControls() {\n")
  for i in range(0,len(boogiePageVars)):
    file.write("\tvar isCurrent" + boogiePageVars[i]["name"] + ": bool;\n")
  file.write("\n")

  for i in range(0,len(boogiePageVars)):
    if boogiePageVars[i]["boogieStringName"] == dummyPageVar:
      file.write("\tisCurrent" + boogiePageVars[i]["name"] + " := false;\n")
    else:
      file.write("\tcall isCurrent" + boogiePageVars[i]["name"] + " := System.String.op_Equality$System.String$System.String(" + currentNavigationVariable + "," + boogiePageVars[i]["boogieStringName"] + ");\n")

  firstTime= True
  for i in range(0,len(boogiePageVars)):
    if firstTime:
      file.write("\tif")
      firstTime= False
    else:
      file.write("\telse if")

    file.write(" (isCurrent" + boogiePageVars[i]["name"] +  ") {\n")
    file.write("\t\t call drive" + boogiePageVars[i]["name"] + "Controls();\n\t}\n")
  file.write("}\n")

def outputURIHavocProcedure(file):
  file.write("procedure __BOOGIE_Havoc_CurrentURI__();\n")
  file.write("implementation __BOOGIE_Havoc_CurrentURI__() {\n")
  file.write("\thavoc " + currentNavigationVariable + ";\n")
  file.write("// TODO write assume statements to filter havoc'd variable to either of all pages\n")
  # file.write("\tassume )
  file.write("}\n")

#build a batch file for test running at the same time
def outputBoilerplate(outputFile, cmdFile):
  file= open(outputFile,"w")
  batFile= open(cmdFile, "w")
  batFile.write("del corral_out_trace.txt")
  outputPageVariables(file)
  outputURIHavocProcedure(file)
  outputControlDrivers(file, batFile)
  outputMainProcedures(file, batFile)
  file.close()
  batFile.close()

def buildControlInfo(controlInfoFileName):
  global mainPageXAML
  global mainAppClassname
  global currentNavigationVariable
  global staticControlsMap

  file = open(controlInfoFileName, "r")
  # Info file format is first line containing only the main page, another line with boogie's current navigation variable and then one line per
  # <pageClassName>,<page.xaml file>,<xaml boogie string representation>,<controlClassName>,<controlName (as in field name)>,<IsEnabledValue>,<VisibilityValue>,<ClickValue>,<CheckedValue>,<UncheckedValue>,<BoogieName>
  mainPageXAML= file.readline().strip()
  currentNavigationVariable= file.readline().strip()
  mainAppClassname= file.readline().strip()

  infoLine= file.readline().strip()
  while not infoLine == "":
    pageClass, pageName, pageBoogieStringName, controlClass, controlName, enabled, visible, clickHandler, checkedHandler, uncheckedHandler, bplName= infoLine.split(",")
    pageInfo={}
    pageInfo["class"]=pageClass
    try:
      pageInfo= staticControlsMap[pageName]
    except KeyError:
      staticControlsMap[pageName]=pageInfo

    pageInfo["boogieStringName"]= pageBoogieStringName
    pageControlInfo={}
    try:
      pageControlInfo= pageInfo["controls"]
    except KeyError:
      pageInfo["controls"]=pageControlInfo
    loadControlInfo(pageControlInfo, controlClass, controlName, enabled, visible, clickHandler, checkedHandler, uncheckedHandler, bplName)
    pageInfo["controls"]= pageControlInfo
    staticControlsMap[pageName]=pageInfo

    infoLine=file.readline().strip()
  file.close()

def main():
  controlFile= ""
  outputFile= ""
  try:
    opts, args= getopt.getopt(sys.argv[1:], "c:o:", ["controls=","output="])
  except geopt.error, msg:
    print msg
    showUsage()
    sys.exit(2)

  if not len(opts) == 2:
    print "Missing options"
    showUsage()
    sys.exit(2)

  for o, a in opts:
    if o in ["-c","--controls"]:
      controlFile= a
    if o in ["-o", "--output"]:
      outputFile= a

  buildControlInfo(controlFile)
  outputBoilerplate(outputFile, outputFile + ".bat")

if __name__ == "__main__":
  main()