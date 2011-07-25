using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using Microsoft.Cci;

namespace BytecodeTranslator.Phone {
  class PhoneControlFeedbackCodeTraverser : BaseCodeTraverser {
  }

  class PhoneControlFeedbackMetadataTraverser : BaseMetadataTraverser {
    private MetadataReaderHost host;

    public PhoneControlFeedbackMetadataTraverser(MetadataReaderHost host) : base() {
      this.host = host;
    }

  }
}
