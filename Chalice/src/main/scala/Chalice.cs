//-----------------------------------------------------------------------------
//
// Copyright (C) Microsoft Corporation.  All Rights Reserved.
//
//-----------------------------------------------------------------------------
using System.Collections.Generic;
using System.Linq;
using System.Threading;

namespace Chalice
{
  public class ImmutableList<E>
  {
    private List<E> list;

    public ImmutableList()
    {
      list = new List<E>();
    }

    public ImmutableList(IEnumerable<E> elems)
    {
      list = new List<E>(elems);
    }

    public ImmutableList<E> Append(ImmutableList<E> other)
    {
      var res = new ImmutableList<E>();
      res.list.AddRange(list);
      res.list.AddRange(other.list);
      return res;
    }

    public E At(int index)
    {
      return list[index];
    }

    public ImmutableList<E> Take(int howMany)
    {
      var res = new ImmutableList<E>(this.list.Take(howMany));
      return res;
    }

    public ImmutableList<E> Drop(int howMany)
    {
      var res = new ImmutableList<E>(this.list.Skip(howMany));
      return res;
    }

    public int Length
    {
      get
      {
        return list.Count;
      }
    }

    public static ImmutableList<int> Range(int min, int max)
    {
      ImmutableList<int> l = new ImmutableList<int>();
      for (int i = min; i < max; i++)
      {
        l.list.Add(i);
      }
      return l;
    }
  }

  public class ChannelBuffer<E>
  {
    private Queue<E> contents = new Queue<E>();

    public void Add(E e)
    {
      lock (this)
      {
        contents.Enqueue(e);
        Monitor.Pulse(this);
      }
    }

    public E Remove()
    {
      lock (this)
      {
        while (contents.Count == 0)
        {
          Monitor.Wait(this);
        }
        E e = contents.Dequeue();
        return e;
      }
    }
  }

  public class ChalicePrint
  {
    public void Int(int x)
    {
      System.Console.WriteLine(x);
    }
    public void Bool(bool x)
    {
      System.Console.WriteLine(x);
    }
  }
}
