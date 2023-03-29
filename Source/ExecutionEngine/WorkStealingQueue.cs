using System.Collections.Generic;
using System.Threading;

namespace Microsoft.Boogie; 

/// <summary>A work-stealing queue.</summary>
/// <typeparam name="T">Specifies the type of data stored in the queue.</typeparam>
internal class WorkStealingQueue<T> where T : class
{
    private const int INITIAL_SIZE = 32;
    private T[] m_array = new T[INITIAL_SIZE];
    private int m_mask = INITIAL_SIZE - 1;
    private volatile int m_headIndex = 0;
    private volatile int m_tailIndex = 0;

    private object m_foreignLock = new object();

    internal void LocalPush(T obj)
    {
        int tail = m_tailIndex;

        // When there are at least 2 elements' worth of space, we can take the fast path.
        if (tail < m_headIndex + m_mask)
        {
            m_array[tail & m_mask] = obj;
            m_tailIndex = tail + 1;
        }
        else
        {
            // We need to contend with foreign pops, so we lock.
            lock (m_foreignLock)
            {
                int head = m_headIndex;
                int count = m_tailIndex - m_headIndex;

                // If there is still space (one left), just add the element.
                if (count >= m_mask)
                {
                    // We're full; expand the queue by doubling its size.
                    T[] newArray = new T[m_array.Length << 1];
                    for (int i = 0; i < m_array.Length; i++) {
                      newArray[i] = m_array[(i + head) & m_mask];
                    }

                    // Reset the field values, incl. the mask.
                    m_array = newArray;
                    m_headIndex = 0;
                    m_tailIndex = tail = count;
                    m_mask = (m_mask << 1) | 1;
                }

                m_array[tail & m_mask] = obj;
                m_tailIndex = tail + 1;
            }
        }
    }

    internal bool LocalPop(ref T obj)
    {
        while (true)
        {
            // Decrement the tail using a fence to ensure subsequent read doesn't come before.
            int tail = m_tailIndex;
            if (m_headIndex >= tail)
            {
                obj = null;
                return false;
            }

            tail -= 1;
#pragma warning disable 0420
            Interlocked.Exchange(ref m_tailIndex, tail);
#pragma warning restore 0420

            // If there is no interaction with a take, we can head down the fast path.
            if (m_headIndex <= tail)
            {
                int idx = tail & m_mask;
                obj = m_array[idx];

                // Check for nulls in the array.
                if (obj == null) {
                  continue;
                }

                m_array[idx] = null;
                return true;
            }
            else
            {
                // Interaction with takes: 0 or 1 elements left.
                lock (m_foreignLock)
                {
                    if (m_headIndex <= tail)
                    {
                        // Element still available. Take it.
                        int idx = tail & m_mask;
                        obj = m_array[idx];

                        // Check for nulls in the array.
                        if (obj == null) {
                          continue;
                        }

                        m_array[idx] = null;
                        return true;
                    }
                    else
                    {
                        // We lost the race, element was stolen, restore the tail.
                        m_tailIndex = tail + 1;
                        obj = null;
                        return false;
                    }
                }
            }
        }
    }

    internal bool TrySteal(ref T obj)
    {
        obj = null;

        while (true)
        {
            if (m_headIndex >= m_tailIndex) {
              return false;
            }

            lock (m_foreignLock)
            {
                // Increment head, and ensure read of tail doesn't move before it (fence).
                int head = m_headIndex;
#pragma warning disable 0420
                Interlocked.Exchange(ref m_headIndex, head + 1);
#pragma warning restore 0420

                if (head < m_tailIndex)
                {
                    int idx = head & m_mask;
                    obj = m_array[idx];

                    // Check for nulls in the array.
                    if (obj == null) {
                      continue;
                    }

                    m_array[idx] = null;
                    return true;
                }
                else
                {
                    // Failed, restore head.
                    m_headIndex = head;
                    obj = null;
                }
            }

            return false;
        }
    }

    internal bool TryFindAndPop(T obj)
    {
        // We do an O(N) search for the work item. The theory of work stealing and our
        // inlining logic is that most waits will happen on recently queued work.  And
        // since recently queued work will be close to the tail end (which is where we
        // begin our search), we will likely find it quickly.  In the worst case, we
        // will traverse the whole local queue; this is typically not going to be a
        // problem (although degenerate cases are clearly an issue) because local work
        // queues tend to be somewhat shallow in length, and because if we fail to find
        // the work item, we are about to block anyway (which is very expensive).

        for (int i = m_tailIndex - 1; i >= m_headIndex; i--)
        {
            if (m_array[i & m_mask] == obj)
            {
                // If we found the element, block out steals to avoid interference.
                lock (m_foreignLock)
                {
                    // If we lost the race, bail.
                    if (m_array[i & m_mask] == null)
                    {
                        return false;
                    }

                    // Otherwise, null out the element.
                    m_array[i & m_mask] = null;

                    // And then check to see if we can fix up the indexes (if we're at
                    // the edge).  If we can't, we just leave nulls in the array and they'll
                    // get filtered out eventually (but may lead to superflous resizing).
                    if (i == m_tailIndex) {
                      m_tailIndex -= 1;
                    } else if (i == m_headIndex) {
                      m_headIndex += 1;
                    }

                    return true;
                }
            }
        }

        return false;
    }

    internal T[] ToArray()
    {
        List<T> list = new List<T>();
        for (int i = m_tailIndex - 1; i >= m_headIndex; i--)
        {
            T obj = m_array[i & m_mask];
            if (obj != null) {
              list.Add(obj);
            }
        }
        return list.ToArray();
    }
}