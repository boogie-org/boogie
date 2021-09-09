using System.Collections.Generic;

namespace Microsoft.Boogie
{
  public class IdMap<T>
  {
    Dictionary<T, int> toId = new ();
    Dictionary<int, T> fromId = new ();
    private int counter = 10;
    
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