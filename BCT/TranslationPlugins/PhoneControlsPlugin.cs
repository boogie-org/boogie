using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.IO;

namespace TranslationPlugins {
  public enum Visibility { Visible, Collapsed };

  public enum Event { Click, Checked, Unchecked };

  public class HandlerSignature {
    public static string[] getParameterTypesForHandler(Event controlEvent) {
      switch (controlEvent) {
        case Event.Checked:
        case Event.Unchecked:
        case Event.Click:
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

  class ControlInfoStructure {
    public string Name;
    public string ClassName;
    public bool IsEnabled;
    public Visibility Visible;
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

    public string PageClassName;
    public string PageXAML;

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
  }

  public class PhoneControlsPlugin : TranslationPlugin {
    // TODO this will probably need a complete rewrite once it is event based, and make it more push than pull
    // TODO but it doesn't make sense right now to make it BCT or CCI aware
    private static int CONFIG_LINE_FIELDS= 9;
    private static int PAGE_CLASS_FIELD= 0;
    private static int PAGE_XAML_FIELD= 1;
    private static int CONTROL_CLASS_FIELD= 2;
    private static int CONTROL_NAME_FIELD= 3;
    private static int ENABLED_FIELD= 4;
    private static int VISIBILITY_FIELD= 5;
    private static int CLICK_HANDLER_FIELD= 6;
    private static int CHECKED_HANDLER_FIELD= 7;
    private static int UNCHECKED_HANDLER_FIELD = 8;

    private IDictionary<string, PageStructure> pageStructureInfo;

    public static string getFullyQualifiedControlClass(string controlClass) {
      // TODO do an actual API discovery. The problem will be differencing 7.0 apps from 7.1 apps
      return "System.Windows.Controls." + controlClass;
    }
    
    public PhoneControlsPlugin(string configFile) {
      pageStructureInfo = new Dictionary<string, PageStructure>();
      StreamReader fileStream = null;
      try {
        fileStream = new StreamReader(configFile);
      } catch (Exception e) {
        if (e is DirectoryNotFoundException || e is FileNotFoundException || e is IOException) {
          // TODO log, I don't want to terminate BCT because of this
        } else if (e is ArgumentException || e is ArgumentNullException) {
          // TODO log, I don't want to terminate BCT because of this
        } else {
          throw;
        }
      }

      LoadControlStructure(fileStream);

      if (fileStream != null)
        fileStream.Close();
    }

    private void LoadControlStructure(StreamReader configStream) {
      // TODO it would be nice to have some kind of dynamic definition of config format
      // TODO for now remember that config format is CSV
      // TODO each line is <pageClassName>,<pageXAMLPath>,<controlClassName>,<controlName>,<IsEnabledValue>,<VisibilityValue>,<ClickValue>,<CheckedValue>,<UncheckedValue>
      // TODO check PhoneControlsExtractor.py

      // TODO the page.xaml value is saved with no directory information: if two pages exist with same name but different directories it will treat them as the same
      // TODO I'm not handling this for now, and I won't be handling relative/absolute URI either for now

      try {
        string pageClass, pageXAML, controlClass, controlName, enabled, visibility, clickHandler, checkedHandler, uncheckedHandler;
        string configLine = configStream.ReadLine();
        string[] inputLine;
        PageStructure pageStr;
        ControlInfoStructure controlInfoStr;

        while (configLine != null) {
          inputLine = configLine.Split(',');

          if (inputLine.Length != CONFIG_LINE_FIELDS)
            throw new ArgumentException("Config input line contains wrong number of fields: " + inputLine.Length + ", expected " + CONFIG_LINE_FIELDS);

          pageClass = inputLine[PAGE_CLASS_FIELD];
          pageXAML = inputLine[PAGE_XAML_FIELD];
          controlClass = inputLine[CONTROL_CLASS_FIELD];
          controlName = inputLine[CONTROL_NAME_FIELD];
          enabled = inputLine[ENABLED_FIELD];
          visibility = inputLine[VISIBILITY_FIELD];
          clickHandler = inputLine[CLICK_HANDLER_FIELD];
          checkedHandler = inputLine[CHECKED_HANDLER_FIELD];
          uncheckedHandler = inputLine[UNCHECKED_HANDLER_FIELD];

          try {
            pageStr = pageStructureInfo[pageClass];
          } catch (KeyNotFoundException) {
            pageStr = new PageStructure();
            pageStr.PageClassName = pageClass;
            pageStr.PageXAML = pageXAML;
          }

          controlInfoStr= pageStr.getControlInfo(controlName);
          if (controlInfoStr == null) {
            controlInfoStr = new ControlInfoStructure();
            controlInfoStr.Name = controlName;
            controlInfoStr.ClassName = controlClass;
          }
          controlInfoStr.IsEnabled = Boolean.Parse(enabled);
          controlInfoStr.Visible = visibility == "Collapsed" ? Visibility.Collapsed : Visibility.Visible;
          controlInfoStr.setHandler(Event.Click, clickHandler);
          controlInfoStr.setHandler(Event.Checked, checkedHandler);
          controlInfoStr.setHandler(Event.Unchecked, uncheckedHandler);

          pageStr.setControlInfo(controlName, controlInfoStr);
          pageStructureInfo[pageClass] = pageStr;
          configLine = configStream.ReadLine();

        }
      } catch (Exception) {
        // TODO log, I don't want to terminate BCT because of this
      }
    }

    public void getControlsForPage(string pageClass) {
    }

    public string getXAMLForPage(string pageClass) {
      return pageStructureInfo[pageClass].PageXAML;
    }

    public bool getIsEnabled(string pageClass, string controlName) {
      return pageStructureInfo[pageClass].getControlInfo(controlName).IsEnabled;
    }

    public Visibility getVisibility(string pageClass, string controlName) {
      return pageStructureInfo[pageClass].getControlInfo(controlName).Visible;
    }

    public IList<HandlerSignature> getHandlers(string pageClass, string controlName, string eventName) {
      if (eventName != "Checked" && eventName != "Unchecked" && eventName != "Click")
        throw new NotImplementedException("Event " + eventName + " is not translated or defined for control " + controlName + " in page " + pageClass);

      return pageStructureInfo[pageClass].getControlInfo(controlName).getHandlers((Event) Event.Parse(typeof(Event), eventName));
    }
  }
}
