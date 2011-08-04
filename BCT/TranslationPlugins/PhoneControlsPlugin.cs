using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace TranslationPlugins {
  public enum Visibility { Visible, Collapsed };

  public enum Event { Click, Checked, Unchecked, SelectionChanged };

  public class HandlerSignature {
    public static string[] getParameterTypesForHandler(Event controlEvent) {
      switch (controlEvent) {
        case Event.Checked:
        case Event.Unchecked:
        case Event.Click:
        case Event.SelectionChanged:
          return new string[] { "object", "System.WindowsRoutedventArgs" };
        default:
          throw new NotImplementedException("Handlers for event: " + controlEvent + " not supported yet");
      }
    }
    // TODO it would be nice to be dynamic on handler names and parameters
    // TODO for now you just have to know the handler signature for each event at load time, and for now we only handle a handful of default control events
    public string Name;
    public string[] ParameterTypes;
  }

  public class ControlInfoStructure {
    public string Name { get; set; }
    public string ClassName { get; set; }
    public bool IsEnabled { get; set; }
    public Visibility Visible { get; set; }
    public string BplName { get; set; }

    private IDictionary<Event, IList<HandlerSignature>> handlers;

    public ControlInfoStructure() {
      handlers = new Dictionary<Event, IList<HandlerSignature>>();
    }

    public void setHandler(Event p, string handler) {
      IList<HandlerSignature> eventHandlers;
      try {
        eventHandlers = handlers[p];
      } catch (KeyNotFoundException) {
        eventHandlers= new List<HandlerSignature>();
        handlers[p] = eventHandlers;
      }

      HandlerSignature newHandler= new HandlerSignature();
      newHandler.Name= handler;
      newHandler.ParameterTypes= HandlerSignature.getParameterTypesForHandler(p);
      eventHandlers.Add(newHandler);
    }

    public IList<HandlerSignature> getHandlers(Event p) {
      try {
        return handlers[p];
      } catch (KeyNotFoundException) {
        return new List<HandlerSignature>();
      }
    }
  }

  class PageStructure {
    public PageStructure() {
      controlsInfo = new Dictionary<string, ControlInfoStructure>();
    }

    public string PageBoogieName { get; set; }
    public string PageClassName { get; set; }
    public string PageXAML { get; set; }
    public bool IsMainPage { get; set; }

    private IDictionary<string, ControlInfoStructure> controlsInfo;
    public ControlInfoStructure getControlInfo(string controlName) {
      try {
        return controlsInfo[controlName];
      } catch (KeyNotFoundException) {
        return null;
      }
    }

    public void setControlInfo(string controlName, ControlInfoStructure controlInfo) {
      controlsInfo[controlName] = controlInfo;
    }

    public IEnumerable<ControlInfoStructure> getAllControlsInfo() {
      return controlsInfo.Values.AsEnumerable();
    }
  }

  public class PhoneControlsPlugin : TranslationPlugin {
    // TODO this will probably need a complete rewrite once it is event based, and make it more push than pull
    // TODO but it doesn't make sense right now to make it BCT or CCI aware
    private static int CONFIG_LINE_FIELDS= 12;
    private static int PAGE_CLASS_FIELD= 0;
    private static int PAGE_XAML_FIELD= 1;
    private static int PAGE_BOOGIE_STRING_FIELD = 2;
    private static int CONTROL_CLASS_FIELD= 3;
    private static int CONTROL_NAME_FIELD= 4;
    private static int ENABLED_FIELD= 5;
    private static int VISIBILITY_FIELD= 6;
    private static int CLICK_HANDLER_FIELD= 7;
    private static int CHECKED_HANDLER_FIELD= 8;
    private static int UNCHECKED_HANDLER_FIELD = 9;
    private static int SELECTIONCHANGED_HANDLER_FIELD = 10;
    private static int BPL_NAME_FIELD = 11;

    private IDictionary<string, PageStructure> pageStructureInfo;

    public static string getURILastPath(string uri) {
      // I need to build an absolute URI just to call getComponents() ...
      Uri mockBaseUri = new Uri("mock://mock/", UriKind.RelativeOrAbsolute);
      Uri realUri;
      try {
        realUri = new Uri(uri, UriKind.Absolute);
      } catch (UriFormatException) {
        // uri string is relative
        realUri = new Uri(mockBaseUri, uri);
      }

      string str = realUri.GetComponents(UriComponents.Path | UriComponents.StrongAuthority | UriComponents.Scheme, UriFormat.UriEscaped);
      Uri mockStrippedUri = new Uri(str);
      return mockBaseUri.MakeRelativeUri(mockStrippedUri).ToString();
    }

    //public static string getFullyQualifiedControlClass(string controlClass) {
    //  // TODO do an actual API discovery. The problem will be differencing 7.0 apps from 7.1 apps
    //  return "System.Windows.Controls." + controlClass;
    //}
    
    public PhoneControlsPlugin(string configFile) {
      pageStructureInfo = new Dictionary<string, PageStructure>();
      StreamReader fileStream = null;
      try {
        fileStream = new StreamReader(configFile);
      } catch (Exception e) {
        if (e is DirectoryNotFoundException || e is FileNotFoundException || e is IOException) {
          // TODO log, I don't want to terminate BCT because of this
          throw;
        } else if (e is ArgumentException || e is ArgumentNullException) {
          // TODO log, I don't want to terminate BCT because of this
          throw;
        } else {
          throw;
        }
      }

      LoadControlStructure(fileStream);

      if (fileStream != null)
        fileStream.Close();
    }

    public string getMainPageXAML() {
      KeyValuePair<string, PageStructure> entry= pageStructureInfo.FirstOrDefault(keyValue => keyValue.Value.IsMainPage);
      return entry.Value.PageXAML;
    }

    private string boogieCurrentNavigationVariable;
    public string getBoogieNavigationVariable() {
      return boogieCurrentNavigationVariable;
    }

    public void setBoogieNavigationVariable(string var) {
      boogieCurrentNavigationVariable = var;
    }

    private void setPageAsMainPage(string pageXAML) {
      pageXAML = pageXAML.ToLower();
      int lastDirPos= pageXAML.LastIndexOf('/');
      if (lastDirPos != -1)
        pageXAML = pageXAML.Substring(lastDirPos+1);
      KeyValuePair<string,PageStructure> mainPageClass= pageStructureInfo.FirstOrDefault(keyValue => keyValue.Value.PageXAML.ToLower() == pageXAML.ToLower());
      if (mainPageClass.Equals(default(KeyValuePair<string, PageStructure>))) {
        // the main page doesn't exist because it has no tracked controls. While we cannot track those controls, create a page struct for it
      } else {
        mainPageClass.Value.IsMainPage = true;
      }
    }

    private string mainAppTypeName;
    public void setMainAppTypeName(string typeName) {
      mainAppTypeName= typeName;
    }

    public string getMainAppTypeName() {
      return mainAppTypeName;
    }

    public void DumpControlStructure(StreamWriter outputStream) {
      // maintain same format as input format
      string pageClass, pageXAML, pageBoogieStringName, controlClass, controlName, enabled, visibility, clickHandler,
             checkedHandler, uncheckedHandler, selectionChangedHandler, bplName;
      outputStream.WriteLine(getMainPageXAML());
      outputStream.WriteLine(getBoogieNavigationVariable());
      outputStream.WriteLine(getMainAppTypeName());

      foreach (KeyValuePair<string, PageStructure> entry in this.pageStructureInfo) {
        pageClass = entry.Key;
        pageXAML = entry.Value.PageXAML.ToLower();
        pageBoogieStringName = entry.Value.PageBoogieName;
        foreach (ControlInfoStructure controlInfo in entry.Value.getAllControlsInfo()) {
          controlClass= controlInfo.ClassName;
          controlName = controlInfo.Name;
          enabled= controlInfo.IsEnabled ? "true" : "false";
          switch (controlInfo.Visible) {
            case Visibility.Collapsed:
              visibility = "Collapsed";
              break;
            default:
              visibility = "Visible";
              break;
          }
          IEnumerable<HandlerSignature> handlers= controlInfo.getHandlers(Event.Click);
          if (handlers.Any()) {
            clickHandler = handlers.First().Name;
          } else {
            clickHandler = "";
          }

          handlers = controlInfo.getHandlers(Event.Checked);
          if (handlers.Any()) {
            checkedHandler = handlers.First().Name;
          } else {
            checkedHandler = "";
          }

          handlers = controlInfo.getHandlers(Event.Unchecked);
          if (handlers.Any()) {
            uncheckedHandler = handlers.First().Name;
          } else {
            uncheckedHandler = "";
          }

          handlers = controlInfo.getHandlers(Event.SelectionChanged);
          if (handlers.Any()) {
            selectionChangedHandler= handlers.First().Name;
          } else {
            selectionChangedHandler = "";
          }
          bplName = controlInfo.BplName;
          outputStream.WriteLine(pageClass + "," + pageXAML.ToLower() + "," + pageBoogieStringName + "," + controlClass + "," + controlName + "," + enabled + "," +
                                 visibility + "," + clickHandler + "," + checkedHandler + "," + uncheckedHandler + "," + selectionChangedHandler + "," +
                                 bplName);
        }
      }
    }

    public void setBoogieStringPageNameForPageClass(string pageClass, string boogieStringPageName) {
      pageStructureInfo[pageClass].PageBoogieName = boogieStringPageName;
    }

    private static int dummyControlNameIndex = 0;
    private void LoadControlStructure(StreamReader configStream) {
      // FEEDBACK TODO. Easy check on Feedback issue: Button and HyperLinkButton MUST have a Click handler, if not, it is obvious there is no feedback

      // TODO it would be nice to have some kind of dynamic definition of config format
      // TODO for now remember that config format is CSV
      // TODO each line is <pageClassName>,<pageXAMLPath>,<pageBoogieStringName>,<controlClassName>,<controlName>,<IsEnabledValue>,<VisibilityValue>,<ClickValue>,<CheckedValue>,<UncheckedValue>,<BPL control name>
      // TODO BPL control name will most probably be empty, but it is useful to be able to dump it
      // TODO check PhoneControlsExtractor.py and PhoneBoogieCodeCreator.py

      // TODO the page.xaml value is saved with no directory information: if two pages exist with same name but different directories it will treat them as the same
      // TODO I'm not handling this for now, and I won't be handling relative/absolute URI either for now

      string pageClass, pageXAML, pageBoogieStringName, controlClass, controlName, enabled, visibility, clickHandler, checkedHandler,
             uncheckedHandler, selectionChangedHandler, bplName;
      string configLine = configStream.ReadLine();
      string[] inputLine;
      PageStructure pageStr;
      ControlInfoStructure controlInfoStr;

      // first line just states the main page xaml
      string mainPageXAML= configLine.Trim().ToLower();
      configLine = configStream.ReadLine();

      // second line states boogie current nav variable, possibly dummy value
      setBoogieNavigationVariable(configLine.Trim());
      configLine= configStream.ReadLine();

      // third line is main phone app type, possibly dummy;
      setMainAppTypeName(configLine.Trim());
      configLine = configStream.ReadLine();

      while (configLine != null) {
        if (configLine.Trim().Equals(string.Empty)) {
          configLine = configStream.ReadLine();
          continue;
        }
        inputLine = configLine.Split(',');

        if (inputLine.Length != CONFIG_LINE_FIELDS)
          throw new ArgumentException("Config input line contains wrong number of fields: " + inputLine.Length + ", expected " + CONFIG_LINE_FIELDS);

        pageClass = inputLine[PAGE_CLASS_FIELD].Trim();
        pageXAML = inputLine[PAGE_XAML_FIELD].Trim().ToLower();
        pageBoogieStringName = inputLine[PAGE_BOOGIE_STRING_FIELD].Trim();
        controlClass = inputLine[CONTROL_CLASS_FIELD].Trim();
        controlName = inputLine[CONTROL_NAME_FIELD].Trim();
        if (string.IsNullOrEmpty(controlName))
          controlName = "__BOOGIE_DUMMY_CONTROLNAME_" + dummyControlNameIndex++;

        enabled = inputLine[ENABLED_FIELD].Trim();
        visibility = inputLine[VISIBILITY_FIELD].Trim();
        clickHandler = inputLine[CLICK_HANDLER_FIELD].Trim();
        checkedHandler = inputLine[CHECKED_HANDLER_FIELD].Trim();
        uncheckedHandler = inputLine[UNCHECKED_HANDLER_FIELD].Trim();
        selectionChangedHandler = inputLine[SELECTIONCHANGED_HANDLER_FIELD].Trim();
        bplName = inputLine[BPL_NAME_FIELD].Trim();

        try {
          pageStr = pageStructureInfo[pageClass];
        } catch (KeyNotFoundException) {
          pageStr = new PageStructure();
          pageStr.PageClassName = pageClass;
          pageStr.PageXAML = pageXAML;
          pageStr.PageBoogieName = pageBoogieStringName;
          pageStr.IsMainPage = false;
        }

        controlInfoStr= pageStr.getControlInfo(controlName);
        if (controlInfoStr == null) {
          controlInfoStr = new ControlInfoStructure();
          controlInfoStr.Name = controlName;
          controlInfoStr.ClassName = controlClass;
          controlInfoStr.BplName = bplName;
        }
        controlInfoStr.IsEnabled = Boolean.Parse(enabled);
        controlInfoStr.Visible = visibility == "Collapsed" ? Visibility.Collapsed : Visibility.Visible;
        controlInfoStr.setHandler(Event.Click, clickHandler);
        controlInfoStr.setHandler(Event.Checked, checkedHandler);
        controlInfoStr.setHandler(Event.Unchecked, uncheckedHandler);
        controlInfoStr.setHandler(Event.SelectionChanged, selectionChangedHandler);

        pageStr.setControlInfo(controlName, controlInfoStr);
        pageStructureInfo[pageClass] = pageStr;
        configLine = configStream.ReadLine();
      }

      setPageAsMainPage(mainPageXAML);
    }

    public IEnumerable<ControlInfoStructure> getControlsForPage(string pageClass) {
      try {
        return pageStructureInfo[pageClass].getAllControlsInfo();
      } catch (KeyNotFoundException) {
        return null;
      }
    }

    public string getXAMLForPage(string pageClass) {
      try {
        return pageStructureInfo[pageClass].PageXAML;
      } catch (KeyNotFoundException) {
        return null;
      }
    }

    public bool getIsEnabled(string pageClass, string controlName) {
      try {
        return pageStructureInfo[pageClass].getControlInfo(controlName).IsEnabled;
      } catch (KeyNotFoundException) {
        //TODO not really correct
        return false;
      }
    }

    public Visibility getVisibility(string pageClass, string controlName) {
      try {
        return pageStructureInfo[pageClass].getControlInfo(controlName).Visible;
      } catch (KeyNotFoundException) {
        // TODO not really correct
        return default(Visibility);
      }
    }

    public IList<HandlerSignature> getHandlers(string pageClass, string controlName, string eventName) {
      if (eventName != "Checked" && eventName != "Unchecked" && eventName != "Click")
        throw new NotImplementedException("Event " + eventName + " is not translated or defined for control " + controlName + " in page " + pageClass);

      try {
        return pageStructureInfo[pageClass].getControlInfo(controlName).getHandlers((Event) Event.Parse(typeof(Event), eventName));
      } catch (KeyNotFoundException) {
        return null;
      }
    }
  }
}
