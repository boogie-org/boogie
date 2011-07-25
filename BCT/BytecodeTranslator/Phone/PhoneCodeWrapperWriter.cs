using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;

using TranslationPlugins;

namespace BytecodeTranslator.Phone {
  class PhoneCodeWrapperWriter {
    private static Sink sink;
    public static void createCodeWrapper(Sink sink) {
      PhoneCodeWrapperWriter.sink = sink;
      /*
       * create Main procedure
       *  - creates page instances, one per page -- this overapproximates as there may be more instances
       *  - havoc'd loop drives controls via calls to driver
       *  
       * create Driver procedure
       *  - determine current page; for each page check if it is current or not
       *  - call page driver accordingly
       *  
       * create Page drivers
       *  - one for each page
       *  - havoc-ly determine control to stimulate
       *  - check enabledness of control, stimulate by calling handler of chosen event if yes, nothing ig not
       *  - possibly many events to handle
       *  - might be slightly more efficient to nto return control until we know page navigation may have changed,
       *    but this requires a lot of knowledge (ie, will the called method call NavigationService or not)
       */
      //createMainProcedure();
    }
  }
}
