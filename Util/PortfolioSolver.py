#!/usr/bin/env python2.7

import atexit
import getopt
import os
import signal
import subprocess
import sys
import timeit
import threading
import multiprocessing 

""" WindowsError is not defined on UNIX systems, this works around that """
try:
   WindowsError
except NameError:
   WindowsError = None

""" Horrible hack: Patch sys.exit() so we can get the exitcode in atexit callbacks """
class ExitHook(object):
  def __init__(self):
    self.code = None

  def hook(self):
    self.realExit = sys.exit
    sys.exit = self.exit

  def exit(self, code=0):
    self.code = code
    self.realExit(code)

exitHook = ExitHook()
exitHook.hook()

""" Options for the tool """
class CommandLineOptions(object):
  sourceFiles = []
  boogieOptions = [ "/nologo",
                    "/typeEncoding:m", 
                    "/useArrayTheory", 
                    "/doNotUseLabels", 
                    "/noinfer", 
                    "/contractInfer",
                    "/outputRefuted",
                    "/proverOpt:OPTIMIZE_FOR_BV=true"
                  ]
  workers = 1
  inference = True
  debugging = False
  verbose = False
  noSourceLocInfer = False
  time = False
  timeCSVLabel = None
  boogieMemout=0
  boogieTimeout=300

def SplitFilenameExt(f):
  filename, ext = os.path.splitext(f)
  return filename, ext

class VerificationTask(multiprocessing.Process):
    """ This class is used to create a new thread and run a
    verification task on it.
    """
    def __init__(self, taskID, queue, solver, errorLimit, timeout=0, timeoutErrorCode=None):
        super(VerificationTask, self).__init__()
        self.taskID = taskID
        self.queue = queue
        self.solver = solver
        self.timeout = timeout
        self.timeoutErrorCode = timeoutErrorCode
        self.options = [ "/outputRefuted",
                         "/errorLimit:" + str(errorLimit)
                       ]
        
        if (solver == "cvc4"):
          self.options += [ "/proverOpt:SOLVER=cvc4" ]
          self.options += [ "/cvc4exe:" + os.path.dirname(__file__) + os.sep + "../Binaries/cvc4.exe" ]
        elif (solver == "Z3"):
          self.options += [ "/z3exe:" + os.path.dirname(__file__) + os.sep + "../Binaries/z3.exe" ]
          self.options += ["/z3opt:RELEVANCY=0", "/z3opt:SOLVER=true" ]
    
    def run(self):
        print "INFO:[Task-" + str(self.taskID) + "] running Boogie using the " + self.solver + " solver."
        RunTool("boogie",
            (["mono"] if os.name == "posix" else []) +
            [os.path.dirname(__file__) + os.sep + "../Binaries/Boogie.exe"] +
            CommandLineOptions.boogieOptions + self.options,
            ErrorCodes.BOOGIE_ERROR,
            self.timeout,
            self.timeoutErrorCode)
        self.queue.put(self.taskID)
    
class Timeout(Exception):
    pass

class ToolWatcher(object):
  """ This class is used by run() to implement a timeout.
  It uses threading.Timer to implement the timeout and provides
  a method for checking if the timeout occurred. It also provides a 
  method for cancelling the timeout.

  The class is reentrant
  """

  def __handleTimeOut(self):
    if self.popenObject.poll() == None :
      # Program is still running, let's kill it
      self.__killed=True
      self.popenObject.terminate()

  """ Create a ToolWatcher instance with an existing "subprocess.Popen" instance
      and timeout.
  """
  def __init__(self,popenObject,timeout):
    """ Create ToolWatcher. This will start the timeout.
    """
    self.timeout=timeout
    self.popenObject=popenObject
    self.__killed=False

    self.timer=threading.Timer(self.timeout, self.__handleTimeOut)
    self.timer.start()

  """ Returns True if the timeout occurred """
  def timeOutOccured(self):
    return self.__killed

  """ Cancel the timeout. You must call this if your program wishes
      to exit else exit() will block waiting for this class's Thread
      (threading.Timer) to finish.
  """
  def cancelTimeout(self):
    self.timer.cancel()

def run(command,timeout=0):
  """ Run a command with an optional timeout. A timeout of zero 
      implies no timeout.
  """
  popenargs={}
  if CommandLineOptions.verbose:
    print " ".join(command)
  else:
    popenargs['bufsize']=0
    popenargs['stdout']=subprocess.PIPE
    popenargs['stderr']=subprocess.PIPE

  killer=None
  def cleanupKiller():
    if killer!=None:
      killer.cancelTimeout()

  proc = subprocess.Popen(command,**popenargs)
  if timeout > 0:
    killer=ToolWatcher(proc,timeout)
  try:
    stdout, stderr = proc.communicate()
    if killer != None and killer.timeOutOccured():
      raise Timeout
  except KeyboardInterrupt:
    cleanupKiller()
    proc.wait()
    sys.exit(ErrorCodes.CTRL_C)
  finally:
    #Need to kill the timer if it exists else exit() will block until the timer finishes
    cleanupKiller()

  return stdout, stderr, proc.returncode

class ErrorCodes(object):
  SUCCESS = 0
  COMMAND_LINE_ERROR = 1
  BOOGIE_ERROR = 2
  BOOGIE_TIMEOUT = 3
  CTRL_C = 4

def RunTool(ToolName, Command, ErrorCode,timeout=0,timeoutErrorCode=None):
  """ Run a tool. 
      If the timeout is set to 0 then there will no timeout.
      If the timeout is > 0 then timeoutErrorCode MUST be set!
  """
  try:
    stdout, stderr, returnCode = run(Command, timeout)
  except Timeout:
    PortfolioSolverError(ToolName + " timed out.  Use --timeout=N with N > " + str(timeout) + " to increase timeout, or --timeout=0 to disable timeout.", timeoutErrorCode)
  except (OSError,WindowsError) as e:
    PortfolioSolverError("While invoking " + ToolName + ": " + str(e),ErrorCode)

  if returnCode != 0:
    if stdout: print >> sys.stderr, stdout
    if stderr: print >> sys.stderr, stderr
    sys.exit(ErrorCode)

def showHelpAndExit():
  print "OVERVIEW: Portfolio Solver"
  print ""
  print "USAGE: PortfolioSolver.py [options] <inputs>"
  print ""
  print "GENERAL OPTIONS:"
  print "  -h, --help              Display this message"
  print "  -p, --processes=        Number of solvers to run in parallel"
  print "  --memout=X              Give Boogie a hard memory limit of X megabytes."
  print "                          A memout of 0 disables the memout. The default is " + str(CommandLineOptions.boogieMemout) + " megabytes."
  print "  --time                  Show timing information"
  print "  --timeout=X             Allow Boogie to run for X seconds before giving up."
  print "                          A timeout of 0 disables the timeout. The default is " + str(CommandLineOptions.boogieTimeout) + " seconds."
  print "  --verbose               Show commands to run and use verbose output"
  sys.exit(0)

def PortfolioSolverError(msg, code):
  print >> sys.stderr, "PortfolioSolver: error: " + msg
  sys.exit(code)

def Verbose(msg):
  if(CommandLineOptions.verbose):
    print msg

def getSourceFiles(args):
  if len(args) == 0:
    PortfolioSolverError("no .bpl files supplied", ErrorCodes.COMMAND_LINE_ERROR)
  for a in args:
    filename, ext = SplitFilenameExt(a)
    if not ext == ".bpl":
      PortfolioSolverError("'" + a + "' has unknown file extension, supported file extensions are .bpl (Boogie PL)", ErrorCodes.COMMAND_LINE_ERROR)
    CommandLineOptions.sourceFiles.append(a)

def showHelpIfRequested(opts):
  for o, a in opts:
    if o == "--help" or o == "-h":
      showHelpAndExit()

def processOptions(opts, args):
  for o, a in opts:
    if o == "--processes" or o == "-p":
      try:
        if int(a) < 0:
          PortfolioSolverError("negative value " + a + " provided as argument to --processes", ErrorCodes.COMMAND_LINE_ERROR) 
        CommandLineOptions.workers = int(a)
      except ValueError:
        PortfolioSolverError("non integer value '" + a + "' provided as argument to --processes", ErrorCodes.COMMAND_LINE_ERROR)
    if o == "--boogie-opt":
      CommandLineOptions.boogieOptions += str(a).split(" ")
    if o == "--no-source-loc-infer":
      CommandLineOptions.noSourceLocInfer = True
    if o == "--time":
      CommandLineOptions.time = True
    if o == "--time-as-csv":
      CommandLineOptions.time = True
      CommandLineOptions.timeCSVLabel = a
    if o == "--timeout":
      try:
        CommandLineOptions.boogieTimeout = int(a)
        if CommandLineOptions.boogieTimeout < 0:
          raise ValueError
      except ValueError as e:
          PortfolioSolverError("Invalid timeout \"" + a + "\"", ErrorCodes.COMMAND_LINE_ERROR)
    if o == "--memout":
      try:
        CommandLineOptions.boogieMemout = int(a)
        if CommandLineOptions.boogieMemout < 0:
          raise ValueError
      except ValueError as e:
          PortfolioSolverError("Invalid memout \"" + a + "\"", ErrorCodes.COMMAND_LINE_ERROR)
    if o == "--verbose":
      CommandLineOptions.verbose = True

def main(argv=None):
  if argv is None:
    argv = sys.argv
  progname = argv[0]

  try:
    opts, args = getopt.gnu_getopt(argv[1:],'p:h', 
             ['help', 'processors=',
              'verbose',
              'memout=',
              'no-source-loc-infer',
              'boogie-opt=',
              'time', 'time-as-csv=',
              'timeout='
             ])
  except getopt.GetoptError as getoptError:
    PortfolioSolverError(getoptError.msg + ".  Try --help for list of options", ErrorCodes.COMMAND_LINE_ERROR)

  showHelpIfRequested(opts)
  getSourceFiles(args)
  processOptions(opts, args)
  
  if CommandLineOptions.noSourceLocInfer:
    CommandLineOptions.boogieOptions += [ "/noSourceLocInfer" ]
  if CommandLineOptions.boogieMemout > 0:
    CommandLineOptions.boogieOptions.append("/z3opt:-memory:" + str(CommandLineOptions.boogieMemout))

  timeoutArguments={}
  if CommandLineOptions.boogieTimeout > 0:
    timeoutArguments['timeout']= CommandLineOptions.boogieTimeout
    timeoutArguments['timeoutErrorCode']=ErrorCodes.BOOGIE_TIMEOUT
    
  CommandLineOptions.boogieOptions += [ CommandLineOptions.sourceFiles[0] ]
  
  toolTasks = []
  taskQueue = multiprocessing.Queue()  
  start = timeit.default_timer()
  
  for taskID in range(CommandLineOptions.workers):
    if (taskID == 0):
      task = VerificationTask(taskID + 1, taskQueue, "Z3", 8, **timeoutArguments)
    elif (taskID == 1):
      task = VerificationTask(taskID + 1, taskQueue, "Z3", 4, **timeoutArguments)
    task.start()
    toolTasks.append(task)
  
  taskResult = taskQueue.get()
  end = timeit.default_timer()
  for task in toolTasks:
    task.terminate()
  timing = end-start
  if CommandLineOptions.time:
    print "INFO:[Task-" + str(taskResult) + "] finished (%.2f secs)." % timing
  else:
    print "INFO:[Task-" + str(taskResult) + "] finished."
  os.remove("houdini.txt")

  return 0

def showTiming():
  label = CommandLineOptions.timeCSVLabel
  times.append(timing)
  row = [ '%.3f' % t for t in times ]
  if len(label) > 0: row.insert(0, label)
  if exitHook.code is ErrorCodes.SUCCESS:
    row.append('PASS')
    print ', '.join(row)
  else:
    row.append('FAIL(' + str(exitHook.code) + ')')
    print >> sys.stderr, ', '.join(row)

def killChildrenPosix():
  def handler(signal,frame):
    return
  signal.signal(signal.SIGINT, handler)
  os.killpg(0,signal.SIGINT)

def exitHandler():
  if CommandLineOptions.timeCSVLabel is not None:
    showTiming()
  sys.stderr.flush()
  sys.stdout.flush()
  if os.name == 'posix':
    killChildrenPosix()

if __name__ == '__main__':
  atexit.register(exitHandler)
  sys.exit(main())
