import sys
import getopt
import os
from xml.dom import minidom
import xml.dom

CONTROL_NAMES= ["Button", "CheckBox", "RadioButton"]

# TODO maybe a control is enabled but its parent is not, must take this into account
# TODO a possible solution is to tie the enabled value to that of the parent in the app until it is either overriden
# TODO (by directly manipulating the control's enabled value) or the parent becomes enabled

CONTAINER_CONTROL_NAMES= ["Canvas", "Grid", "StackPanel"]

staticControlsMap= {}

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

def addControlToMap(parentPage, controlNode):
  pageControls=[]
  newControl={}
  try:
    pageControls= staticControlsMap[parentPage]
  except KeyError:
    pass
  
  newControl["Type"]= controlNode.localName
  newControl["Name"]= controlNode.getAttribute("Name")
  if (controlNode.hasAttribute("IsEnabled")):
    newControl["IsEnabled"]= controlNode.getAttribute("IsEnabled")
  else:
    newControl["IsEnabled"]= "true"

  # TODO it is possible that more events are of interest, we should add as we discover them in existing applications
  newControl["Click"] = controlNode.getAttribute("Click")
  newControl["Checked"] = controlNode.getAttribute("Checked")
  newControl["Unchecked"] = controlNode.getAttribute("Unchecked")
  pageControls.append(newControl)
  staticControlsMap[parentPage]= pageControls

def extractPhoneControlsFromPage(pageFile, outputFile):
  # maybe it is not a page file
  if not isPageFile(pageFile):
    return

  pageFileXML= minidom.parse(pageFile)
  removeBlankElements(pageFileXML)
  controls= getControlNodes(pageFileXML)
  for control in controls:
    ownerPage=""
    parent= control
    while not parent == None:
      a=""
      if parent.localName == "PhoneApplicationPage":
        ownerPage= parent.getAttribute("x:Class")
      parent= parent.parentNode
    addControlToMap(ownerPage, control)

def extractPhoneControls(sourceDir, outputFile):
  fileList= [os.path.normcase(fileName) for fileName in os.listdir(sourceDir)]
  fileList= [os.path.join(sourceDir, fileName) for fileName in fileList if os.path.splitext(fileName)[1] == ".xaml"]
  for fileName in fileList:
    pageFile= open(fileName, "r")
    extractPhoneControlsFromPage(pageFile, outputFile)
    pageFile.close()

  # TODO dump controls into a config file that can be passed to BCT

def main():
  pagesDir= ""
  outputFile= ""
  try:
    opts, args= getopt.getopt(sys.argv[1:], "p:o:", ["pages=","output="])
  except geopt.error, msg:
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

  output= open(outputFile, "w")
  extractPhoneControls(pagesDir, output)
  output.close()

if __name__ == "__main__":
  main()