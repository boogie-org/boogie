using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class ControlFlowIdMap<T>
  {
    private readonly Dictionary<T, int> toId = new ();
    private readonly Dictionary<int, T> fromId = new ();
    private int counter = 1; // Index 0 is reserved because it is assigned to the fictitious control-flow location at the beginning of an error trace
    
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