using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class ControlFlowIdMap<T>
  {
    Dictionary<T, int> toId = new ();
    Dictionary<int, T> fromId = new ();
    private int counter = 1; // Index 0 is reserved.
    
    public int GetId(T value)
    {
      if (toId.TryGetValue(value, out var result)) {
        return result;
      }

      toId[value] = counter;
      fromId[counter] = value;

      return counter++;
    }

    public T GetValue(int id)
    {
      return fromId[id];
    }
  }
}