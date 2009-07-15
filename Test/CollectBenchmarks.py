#! /usr/bin/python

# 13 Aug 2006 Alexander Fuchs
#
# creates bpl and prover files for all test cases
# and puts these into a zip file

import sys;
import os;
import shutil;
import re;
import zipfile;


#PROVER_NAME = "smt"
PROVER_NAME = "simplify"

# constants
# prefix of temporary files created by boogie
PREFIX_TMP = "boogie_tmp"

# prefix of files put into package
PREFIX_PGK = "boogie"

# arguments to runtest so that boogie creates problem specifications
BOOGIE_ARG0 = "/prover:blank /print:" + PREFIX_TMP + ".@TIME@.bpl /proverLog:" + PREFIX_TMP + ".@TIME@.simplify"
BOOGIE_ARG1 = "/prover:smt /print:" + PREFIX_TMP + ".@TIME@.bpl /proverLog:" + PREFIX_TMP + ".@TIME@.jjsmt"

# file containing the directories with tests
TESTS_FILE = "alltests.txt"

# marker in boogie generated proover files to denote end of background axioms
START_OF_AXIOMS = "; Boogie universal background predicate"
END_OF_AXIOMS = "; Initialized all axioms."

# assumptions:
# files: problems, runtest
# calling boogie: parameters and filename only





# call runtests to create the bpl/prover specifications:
# - /print creates the boogie bpl file
# - /proverLog creates the prover verification condition
# @TIME@ is used to create a unique file name per test case
def runtests(parameters):
  boogie_arg = BOOGIE_ARG0
  if PROVER_NAME == "simplify":
     boogie_arg = BOOGIE_ARG0
  if PROVER_NAME == "smt":
     boogie_arg = BOOGIE_ARG1
  if os.name == "nt":
    command = "runtestall.bat "  + " ".join(parameters) + " " + boogie_arg
  else:
    command = "./rtestall "  + " ".join(parameters) + " " + boogie_arg
  
  print command

  os.system(command)


# evaluates a call to boogie, which is of the form:
# ; Command Line Options: -nologo /print:boogie_testcase.@TIME@.bpl /proverLog:boogie_testcase.@TIME@.'prover' SimpleAssignments0.dll /infer:i
#
# returns (file_name, parameters), where
# - file_name: the called file name (e.g. SimpleAssignments0.dll)
# - parameters: boogie parameters except for nologo, print, proverLog
def process_boogie_call(line):
  match = re.match("; Command Line Options:(?P<parameters>.*)$", line)
  parameters = match.group("parameters")
  parameters = re.split("\s", parameters)
  
  copy = []
  for parameter in parameters:
    # file names on DOS seem not to like containing ":", so replace by "_"
    parameter = re.sub(":", "_", parameter)
    # ignore these parameters
    if parameter == "":
      ()
    elif re.match("-nologo", parameter):
      ()
    elif re.match("/nologo", parameter):
      ()
    elif re.match("/print", parameter):
      ()
    elif re.match("/proverLog", parameter):
      ()
    elif re.match("-prover", parameter):
      ()
    elif re.match("/prover", parameter):
      ()

    # keep any other parameter
    elif re.match("-", parameter):
      copy.append(parameter)
    elif re.match("/", parameter):
      copy.append("-" + parameter[1:])

    # get the file name
    elif re.match("[a-zA-Z]", parameter):
      file_name = parameter

    # don't know what that is
    else:
      raise ("process_parameters: unknown argument: " + parameter)

  # couldn't find the file name???
  if not file_name:
    raise ("split_parameters: file_name not found in: " + parameters)
  
  else:
    return (file_name, copy)
  



# evaluates the file name on which boogie was called, which is of the form:
# SimpleAssignments0.dll
#
# returns (file_name, is_dll):
# - file_name: the file name, e.g. SimpleAssignments0
# - is_dll: if it was a dll or exe, and not a bpl file
def process_file_name(file_name):
  if re.match("^[a-zA-Z].*\.dll$", file_name.lower()):
    return (file_name[:-4], 1)
  elif re.match("^[a-zA-Z].*\.exe$", file_name.lower()):
    return (file_name[:-4], 1)
  elif re.match("^[a-zA-Z].*\.bpl$", file_name.lower()):
    return (file_name[:-4], 0)
  else:
    return (file_name, 1)
#  else:
#    raise ("process_file_name: neither dll nor bpl: " + file_name)



# creates the package name for a package file (without extension)
# the file name creation scheme used here is not unique,
# so a unique id is added in addition
names = {}
def create_pgk_name(suite, problem_name, condition_name, parameters, extension):
  # things like LESS, less happen, doesn't work under Windows
  name = (problem_name + condition_name + extension).lower()
  if name in names:
    names[name] = names[name] + 1
    name_id = "_" + repr(names[name])
  else:
    names[name] = 0
    name_id = ""
    
  if condition_name != "":
    condition_name = "_" + condition_name

  return os.path.join(suite, PREFIX_PGK + "_" + problem_name + condition_name + "".join(parameters) + name_id + "." + extension)



# creates the bpl package file and adds it to the manifest
def create_bpl(suite, source_name, problem_name, is_dll, parameters, manifest):
  # create unique problem file_name
  target_name = create_pgk_name(suite, problem_name, "", parameters, "bpl")
 
  # copy bpl
  if is_dll:
    # started from dll/exe, so rename converted bpl
    source_name = os.path.join(suite, source_name[:-1-len(PROVER_NAME)] + ".bpl")
    os.rename(source_name, target_name)
  else:
    # started from existing bpl, so just copy it
    source_name = os.path.join(suite, problem_name + ".bpl")
    shutil.copy(source_name, target_name)
      
  manifest.append(target_name)



def create_simplify(suite, problem_name, parameters, file, manifest):
  # get background axioms
  background = []
  next = file.readline()
  if (re.match("; -------------------------------------------------------------------------", next)):
    next = file.readline()
    if (re.match(START_OF_AXIOMS, next)):
      while(not re.match(END_OF_AXIOMS, next)):
        background.append(next)
        next = file.readline()

      next = file.readline()


  # get individual queries
  name = next
  while(name):
    query = file.readline()
    status = file.readline()

    # create simplify file for this query
    match = re.match("; (?P<name>\S+)", name)
    condition_name = match.group("name")
    query_file_name = create_pgk_name(suite, problem_name, condition_name, parameters, PROVER_NAME)

    query_file = open(query_file_name, 'w')
    query_file.writelines(background)
    query_file.write(name)
    query_file.write(query)
    query_file.write(status)
    query_file.close()

    manifest.append(query_file_name)

    name = file.readline()





#
# main
#

# create problem specifications
runtests(sys.argv[1:])

# list of created files
manifest = []
# list of generated bpl files
bpl_files = []

# go into each test directory
suites = open(TESTS_FILE)
for suite in suites.readlines():
  suite = re.split("\s", suite)[0]
  #print suite

  # find the created simplify input files
  files = os.listdir(suite)
  
  prover_files = filter(lambda file: re.search(PREFIX_TMP + ("\S+\.%s$" % PROVER_NAME) , file), files)
  prover_files.sort()
  
  new_bpl_files = filter(lambda file: re.search(PREFIX_TMP + "\S+\.bpl$" , file), files)
  bpl_files.extend(map(lambda file: os.path.join(suite, file), new_bpl_files))


  # process each prover input file
  for prover_file in prover_files:
		# parse header
    file = open(os.path.join(suite, prover_file))
    line = file.readline()
    line = file.readline()
    (file_name, parameters) = process_boogie_call(line)
    (problem_name, is_dll) = process_file_name(file_name)

    # create bpl file
    create_bpl(suite, prover_file, problem_name, is_dll, parameters, manifest)

    # keep prover file for all queries
    target_name = create_pgk_name(suite, problem_name, "", parameters, PROVER_NAME)
    manifest.append(target_name)

    # split prover file into individual queries
    if PROVER_NAME == "simplify":
       create_simplify(suite, problem_name, parameters, file, manifest)
    file.close()

    os.rename(os.path.join(suite, prover_file), target_name)

suites.close()    


    
#print "\n".join(manifest)

# create package
#print "zipping"
zipFile = zipfile.ZipFile("boogie-benchmarks.zip", 'w', zipfile.ZIP_DEFLATED)
for file_name in manifest:
  zipFile.write(file_name)
zipFile.close()

# clean up
for file_name in manifest:
  os.remove(file_name)


# some bpl files are create with /noVerify,
# and then no prover file is generated,
# so these files are just ignored and removed
for file_name in bpl_files:
  try:
    os.remove(file_name)
  except OSError:
    ()
