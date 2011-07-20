import sys
import getopt
import os
from xml.dom import minidom
import xml.dom

CONTROL_NAMES= ["Button", "CheckBox", "RadioButton"]
CONTAINER_CONTROL_NAMES= ["Canvas", "Grid", "StackPanel"]

staticControlsMap= {}
mainPageXAML= None
originalPageVars= []
boogiePageVars= []
boogiePageClasses= []

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
  for entry in staticControlsMap.keys():
    pageVarName= "__BOOGIE_PAGE_VAR_" + entry
    originalPageVars.append(entry)
    boogiePageVars.append(pageVarName)
    boogiePageClasses.append(staticControlsMap[entry]["class"])
    pageVar= "var " + pageVarName + ": Ref;\n"
    file.write(pageVar)

def outputMainProcedure(file):
  file.write("procedure __BOOGIE_VERIFICATION_PROCEDURE();\n")
  file.write("implementation __BOOGIE_VERIFICATION_PROCEDURE() {\n")
  file.write("\tvar $doWork: bool;\n")
  file.write("\tvar $activeControl: int;\n")
  file.write("\tvar $isEnabledRef: Ref;\n")
  file.write("\tvar $isEnabled: bool;\n")
  file.write("\tvar $control: Ref;\n\n")

  for i in range(0,len(boogiePageVars)):
    file.write("\tcall " + boogiePageClasses[i] + ".#ctor(" + boogiePageVars[i] + ");\n")

  file.write("\t//TODO still need to call Loaded handler on main page and the App ctor.\n")
  file.write("\thavoc $doWork;\n")
  file.write("\twhile ($doWork) {\n")
  file.write("\t\tcall DriveControls();\n")
  file.write("\t\thavoc $doWork;\n")
  file.write("\t}\n")
  file.write("}\n")

def outputPageControlDriver(file, originalPageName, boogiePageName):
  file.write("procedure drive" + boogiePageName + "Controls();\n")
  file.write("implementation drive" + boogiePageName + "Controls() {\n")
  file.write("\tvar $activeControl: int;\n")
  file.write("\tvar $control: Ref;\n")
  file.write("\tvar $isEnabledRef: Ref;\n")
  file.write("\tvar $isEnabled: bool;\n")
  file.write("\tvar $handlerToActivate: int;\n")

  file.write("\tBOOGIE_continueOnPage:=true;\n")
  file.write("\thavoc $activeControl;\n")
  file.write("\twhile (BOOGIE_continueOnPage) {\n")
  activeControl=0
  for entry in staticControlsMap[originalPageName]["controls"].keys():
    controlInfo= staticControlsMap[originalPageName]["controls"][entry]
    if activeControl==0:
      file.write("\t\tif ($activeControl == 0) {\n")
    else:
      file.write("\t\telse if ($activeControl == " + str(activeControl) + ") {\n")
    
    file.write("\t\t\t//TODO assuming split fields heap representation\n")
    file.write("\t\t\t$control := " + controlInfo["bplName"] + "[" + boogiePageName + "];\n")
    file.write("\t\t\tcall $isEnabledRef := System.Windows.Controls.Control.get_IsEnabled($control);\n")
    file.write("\t\t\t$isEnabled := Box2Bool(Ref2Box($isEnabledRef));\n")
    file.write("\t\t\tif ($isEnabled) {\n")
    file.write("\t\t\t\thavoc $handlerToActivate;\n")
    if not controlInfo["clickHandler"] == "":
      file.write("\t\t\t\tif ($handlerToActivate == 0) {\n")
      file.write("\t\t\t\t\t" + staticControlsMap[originalPageName]["class"] + "." + controlInfo["clickHandler"] + "$System.Object$System.Windows.RoutedEventArgs(" + controlInfo["bplName"] + "[" + boogiePageName + "],null,null);\n")
      file.write("\t\t\t\t}\n")
    if not controlInfo["checkedHandler"] == "":
      file.write("\t\t\t\tif ($handlerToActivate == 1) {\n")
      file.write("\t\t\t\t\t" + staticControlsMap[originalPageName]["class"] + "." + controlInfo["checkedHandler"] + "$System.Object$System.Windows.RoutedEventArgs(" + controlInfo["bplName"] + "[" + boogiePageName + "],null,null);\n")
      file.write("\t\t\t\t}\n")
    if not controlInfo["uncheckedHandler"] == "":
      file.write("\t\t\t\tif ($handlerToActivate == 2) {\n")
      file.write("\t\t\t\t\t" + staticControlsMap[originalPageName]["class"] + "." + controlInfo["uncheckedHandler"] + "$System.Object$System.Windows.RoutedEventArgs(" + controlInfo["bplName"] + "[" + boogiePageName + "],null,null);\n")
      file.write("\t\t\t\t}\n")

    file.write("\t\t\t}\n")
    file.write("\t\t}\n")
    activeControl= activeControl+1
  file.write("\t}\n")
  file.write("}\n")


def outputControlDrivers(file):
  for i in range(0,len(boogiePageVars)):
    outputPageControlDriver(file, originalPageVars[i],boogiePageVars[i])

  file.write("procedure DriveControls();\n")
  file.write("implementation DriveControls() {\n")
  for i in range(0,len(boogiePageVars)):
    file.write("\tvar isCurrent" + boogiePageVars[i] + ": bool;\n")
  file.write("\n")

  for i in range(0,len(boogiePageVars)):
    file.write("\t//TODO call isCurrent" + boogiePageVars[i] + " := System.String.op_Equality$System.String$System.String(" + "BOOGIE_CURRENT_VAR" + "," + "BOOGIE_PAGE_APPROPRIATE_CONSTANT_STRING" + ");\n")

  firstTime= True
  for i in range(0,len(boogiePageVars)):
    if firstTime:
      file.write("\tif")
      firstTime= False
    else:
      file.write("\telse if")

    file.write(" (isCurrent" + boogiePageVars[i] +  ") {\n")
    file.write("\t\t call drive" + boogiePageVars[i] + "Controls();\n\t}\n")
  file.write("}\n")

def outputURIHavocProcedure(file):
  file.write("procedure __BOOGIE_HavocCall__();\n")
  file.write("implementation __BOOGIE_HavocCall__() {\n")
  # TODO change this name to a dynamically inferred one. This is just for testing right now
  file.write("\thavoc SimpleNavigationApp.App.$__BOOGIE_CurrentNavigationURI__;\n")
  # TODO write assume statement to filter havoc'd variable to either of all pages
  # file.write("\tassume )
  file.write("}\n")

def outputBoilerplate(outputFile):
  file= open(outputFile,"w")
  outputPageVariables(file)
  outputURIHavocProcedure(file)
  outputControlDrivers(file)
  outputMainProcedure(file)
  file.close()

def buildControlInfo(controlInfoFileName):
  global mainPageXAML
  global staticControlsMap

  file = open(controlInfoFileName, "r")
  # Info file format is first line containing only the main page, and then one line per
  # <pageClassName>,<page.xaml file>,<controlClassName>,<controlName (as in field name)>,<IsEnabledValue>,<VisibilityValue>,<ClickValue>,<CheckedValue>,<UncheckedValue>,<BoogieName>
  mainPageXAML= file.readline().strip()
  infoLine= file.readline().strip()
  while not infoLine == "":
    pageClass, pageName, controlClass, controlName, enabled, visible, clickHandler, checkedHandler, uncheckedHandler, bplName= infoLine.split(",")
    pageInfo={}
    pageInfo["class"]=pageClass
    try:
      pageInfo= staticControlsMap[pageName]
    except KeyError:
      staticControlsMap[pageName]=pageInfo

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
  print staticControlsMap

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
  outputBoilerplate(outputFile)

if __name__ == "__main__":
  main()