#!/usr/bin/env python
"""
This is a simple script to invoke nunit-console.exe
on Windows or Linux on all UnitTest libraries.
"""
import argparse
import logging
import os
import subprocess
import sys

class ReturnCode:
  SUCCESS = 0
  CONFIG_ERROR = 1
  RUN_ERROR = 2


def main(args):
  parser = argparse.ArgumentParser(description=__doc__)
  parser.add_argument('BuildType', choices=['Release', 'Debug'],
                      help='Build type of unit test libraries')
  parser.add_argument('-l','--log-level',
                      choices=['critical', 'error', 'warning', 'info', 'debug'],
                      default='info',
                      dest='log_level',
                      help='Logging level. Default %(default)s')
  parser.add_argument('--nunit-console-path', default='',
                      help='Path to nunit-console tool. If not set the script will try to guess its location',
                      dest='nunit_console_path'
                     )
  parser.add_argument('-e', '--nunit-console-extra-args', action='append',
                      help='Pass extra arguments to nunit-console. This can be used multiple times',
                      default=[],
                      dest='nunit_console_extra_args'
                     )
  parser.add_argument('--no-progress',
                      action='store_true',
                      dest='no_progress',
                      help='Suppress nunit-console progress information')


  parsedArgs = parser.parse_args(args)
  logging.basicConfig(level=getattr(logging, parsedArgs.log_level.upper()))
  buildType=parsedArgs.BuildType

  logging.info('Build type is {}'.format(buildType))

  if parsedArgs.no_progress:
    parsedArgs.nunit_console_extra_args.append('-nodots')

  logging.info('Extra arguments to nunit-console "{}"'.format(parsedArgs.nunit_console_extra_args))

  UnitTestDirRoot = os.path.dirname(os.path.abspath(__file__))

  # Find nunit-console.exe
  if parsedArgs.nunit_console_path == "":
    # Try to guess where the tool is
    nunitConsolePath = os.path.join(os.path.join(UnitTestDirRoot,'..'),
                                    "packages",
                                    "NUnit.Runners.2.6.3",
                                    "tools",
                                    "nunit-console.exe"
                                   )
    # Mono needs the path to be absolute
    nunitConsolePath = os.path.abspath(nunitConsolePath)
  else:
    nunitConsolePath = parsedArgs.nunit_console_path

  logging.info('Looking for NUnit console at "{}"'.format(nunitConsolePath))
  if not os.path.exists(nunitConsolePath):
    logging.error('Could not find NUnit console tool')
    return ReturnCode.CONFIG_ERROR

  # Find unit test libraries
  unitTestLibraries = [ ]
  logging.info('Searching for Unit test libraries in "{}"'.format(UnitTestDirRoot))
  for (dirpath, dirnames, filenames) in os.walk(UnitTestDirRoot):

    # Search current directory for dll with correct suffix
    for filename in filenames:
      if filename.endswith('Tests.dll'):
        logging.debug('Found "{}" checking build type'.format(filename))

        pathComponents = dirpath.split(os.path.sep)
        fullPath = os.path.join(dirpath, filename)
        try:
          buildTypeIndex = pathComponents.index(buildType)
          if buildTypeIndex == 0 or pathComponents[buildTypeIndex -1] != 'bin':
            continue

          logging.info('Using "{}"'.format(fullPath))
          unitTestLibraries.append(fullPath)
        except ValueError:
          pass

  # Run Unit tests
  if len(unitTestLibraries) == 0:
    logging.error('No Unit test libraries were found')
    return ReturnCode.CONFIG_ERROR

  cmd = []

  if os.name == 'posix':
    cmd.append('mono')

  cmd.extend([nunitConsolePath, '-nologo'])

  if len(parsedArgs.nunit_console_extra_args) > 0:
    cmd.extend(parsedArgs.nunit_console_extra_args)

  cmd.extend(unitTestLibraries)
  logging.info('Running "{}"'.format(cmd))
  exitCode = subprocess.call(cmd)
  if exitCode != 0:
    logging.error('FAILED!')
    return ReturnCode.RUN_ERROR
  else:
    logging.info('Succeeded')

  return ReturnCode.SUCCESS


if __name__ == '__main__':
  sys.exit(main(sys.argv[1:]))
