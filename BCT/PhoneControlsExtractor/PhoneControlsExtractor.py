import sys
import getopt
import os
from xml.dom import minidom
import xml.dom

CONTROL_NAMES= ["Button", "CheckBox", "RadioButton", "ApplicationBarIconButton"]

# TODO maybe a control is enabled but its parent is not, must take this into account
# TODO a possible solution is to tie the enabled value to that of the parent in the app until it is either overriden
# TODO (by directly manipulating the control's enabled value) or the parent becomes enabled

CONTAINER_CONTROL_NAMES= ["Canvas", "Grid", "StackPanel", "ApplicationBar"]
COMMA_REPLACEMENT="###"

staticControlsMap= {}
mainPageXAML= None

def showUsage():
  print "PhoneControlsExtractor -- extract control information from phone application pages"
  print "Usage:"
  print "\tPhoneControlsExtractor --pages <application_directory> --output <info_output_file>\n"
  print "Options:"
  print "\t--pages <application_directory>: point to location of .xaml files detailing pages. Short form: -p"
  print "\t--output <info_output_file>: file to write with control info. Short form: -o\n"

def isPageFile(file):
  # not the best way, find out the actual exceptions
  try:
    minidom.parse(file)
    file.seek(0)
    return True
  except Exception:
    return False

def removeBlankElements(xmlNode):
  blankNodes= []
  for child in xmlNode.childNodes:
    if child.nodeType == xml.dom.Node.TEXT_NODE and child.data.strip() == "":
      blankNodes.append(child)
    elif child.hasChildNodes():
      removeBlankElements(child)
	
  for node in blankNodes:
    node.parentNode.removeChild(node)
    node.unlink()

def getControlNodes(xmlNode):
  controlNodes= []
  if (xmlNode.nodeType == xml.dom.Node.ELEMENT_NODE and xmlNode.localName in CONTROL_NAMES):
    controlNodes.insert(0,xmlNode)

  for child in xmlNode.childNodes:
    controlNodes= controlNodes + getControlNodes(child)

  return controlNodes

def addDummyControlToMap(pageXAML, parentPage):
  pageControls=[]
  newControl={}
  try:
    pageControls= staticControlsMap[parentPage]
  except KeyError:
    pass
  
  newControl["Type"]= "DummyType"
  newControl["Name"]= "DummyName"
  newControl["IsEnabled"]= "false"
  newControl["Visibility"]= "Collapsed"
  newControl["Click"] = ""
  newControl["Checked"] = ""
  newControl["Unchecked"] = ""
  newControl["XAML"]= pageXAML
  pageControls.append(newControl)
  staticControlsMap[parentPage]= pageControls

def addControlToMap(pageXAML, parentPage, controlNode):
  pageControls=[]
  newControl={}
  try:
    pageControls= staticControlsMap[parentPage]
  except KeyError:
    pass
  
  newControl["Type"]= controlNode.localName
  newControl["Name"]= controlNode.getAttribute("Name").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)
  if (controlNode.hasAttribute("IsEnabled")):
    newControl["IsEnabled"]= controlNode.getAttribute("IsEnabled").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)
  else:
    newControl["IsEnabled"]= "true"
  
  if (controlNode.hasAttribute("Visibility")):
    newControl["Visibility"]= controlNode.getAttribute("Visibility").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)
  else:
    newControl["Visibility"]= "Visible"

  # TODO it is possible that more events are of interest, we should add as we discover them in existing applications
  newControl["Click"] = controlNode.getAttribute("Click").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)
  newControl["Checked"] = controlNode.getAttribute("Checked").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)
  newControl["Unchecked"] = controlNode.getAttribute("Unchecked").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)
  newControl["XAML"]= pageXAML
  pageControls.append(newControl)
  staticControlsMap[parentPage]= pageControls

def extractPhoneControlsFromPage(pageXAML):
  # maybe it is not a page file
  print "extracting from " + pageXAML
  pageFile= open(pageXAML, "r")
  if not isPageFile(pageFile):
    return
  pageFileXML= minidom.parse(pageFile)
  pageFile.close()
  removeBlankElements(pageFileXML)
  controls= getControlNodes(pageFileXML)
  ownerPage = getOwnerPage(pageFileXML)
  if (ownerPage != None):
    print pageXAML + " is not none"
    if (len(controls) == 0):
      # it is either a page with no controls, or controls that are dynamically created, or controls we do not track yet
      # in any case, just add a dummy control so as not to lose the page
      addDummyControlToMap(pageXAML, ownerPage)
    else:
      for control in controls:
        parent= control
        while not parent == None and ownerPage == None:
          parent= parent.parentNode
        addControlToMap(pageXAML, ownerPage, control)

def getOwnerPage(xmlNode):
  ownerPage= None
  if (xmlNode.nodeType == xml.dom.Node.ELEMENT_NODE):
    ownerPage= xmlNode.getAttribute("x:Class").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)
    if ownerPage == "":
      ownerPage= None
  else:
   for child in xmlNode.childNodes:
     ownerPage= getOwnerPage(child)
     if (ownerPage != None):
       break

  return ownerPage


def outputPhoneControls(outputFileName):
  outputFile= open(outputFileName, "w")

  # Output format is first line containing only the main page, then line containing boogie navigation variable, and then one line per
  # <pageClassName>,<page.xaml file>,<boogie string page name>,<controlClassName>,<controlName (as in field name)>,<IsEnabledValue>,<VisibilityValue>,<ClickValue>,<CheckedValue>,<UncheckedValue>
  outputFile.write(mainPageXAML + "\n")
  outputFile.write("dummyNavigationVariable_unknown\n")
  outputFile.write("dummyMainAppName_unknown\n") # I could possibly deduce it from WMAppManifest.xml, but I'm unsure. Doing it later is safe anyway
  for page in staticControlsMap.keys():
    for control in staticControlsMap[page]:
    # TODO we still cannot handle bindings, and those we identified through commas and equality signs
      isEnabled= control["IsEnabled"]
      if (isEnabled.find(COMMA_REPLACEMENT) != -1):
        isEnabled= ""
      visibility= control["Visibility"]
      if (visibility.find(COMMA_REPLACEMENT) != -1):
        visibility= ""
      click= control["Click"]
      if (click.find(COMMA_REPLACEMENT) != -1):
        click= ""
      checked= control["Checked"]
      if (checked.find(COMMA_REPLACEMENT) != -1):
        checked= ""
      unchecked= control["Unchecked"]
      if (unchecked.find(COMMA_REPLACEMENT) != -1):
        unchecked= ""
      pageXAML= control["XAML"]
      # last comma is to account for bpl translation name, that is unknown for now
      # boogie string page name is unknown for now
      outputFile.write(page + "," + os.path.basename(pageXAML) + ",dummyBoogieStringPageName," + control["Type"] + "," + control["Name"] + "," + isEnabled + "," + visibility + "," + click + "," + checked + "," + unchecked + ",\n")

  outputFile.close()

def getMainPageXAMLFromManifest(filename):
  file= open(filename, "r");
  manifest= minidom.parse(file)
  file.close()
  # interesting XPath location /App/Tasks/DefaultTask/@NavigationPage
  return manifest.getElementsByTagName("DefaultTask")[0].getAttribute("NavigationPage").replace(",",COMMA_REPLACEMENT).replace("=",COMMA_REPLACEMENT)

def extractPhoneControls(sourceDir):
  global mainPageXAML
  fileList= [os.path.join(sourceDir, fileName) for fileName in os.listdir(sourceDir) if os.path.splitext(fileName)[1] == ".xaml" or os.path.splitext(fileName)[1] == ".xml"]
  for fileName in fileList:
    if os.path.splitext(fileName)[1] == ".xml" and os.path.splitext(os.path.split(fileName)[1])[0].lower() == "wmappmanifest":
      mainPageXAML= getMainPageXAMLFromManifest(fileName)
      break

  for fileName in fileList:
    extractPhoneControlsFromPage(fileName)

def main():
  pagesDir= ""
  outputFile= ""
  try:
    opts, args= getopt.getopt(sys.argv[1:], "p:o:", ["pages=","output="])
  except getopt.error, msg:
    print msg
    showUsage()
    sys.exit(2)

  if not len(opts) == 2:
    print "Missing options"
    showUsage()
    sys.exit(2)

  for o, a in opts:
    if o in ["-p","--pages"]:
      pagesDir= a
    if o in ["-o", "--output"]:
      outputFile= a

  extractPhoneControls(pagesDir)
  outputPhoneControls(outputFile)

if __name__ == "__main__":
  main()