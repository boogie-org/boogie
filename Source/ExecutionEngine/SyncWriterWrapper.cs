using System;
using System.IO;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

class SyncWriterWrapper : TextWriter {
  protected TextWriter target;
  protected object Lock { get; } = new();

  public override Encoding Encoding => target.Encoding;

  protected SyncWriterWrapper(TextWriter target) {
    this.target = target;
  }

  public override void Write(char value) {
    lock (Lock) {
      target.Write(value);
    }
  }

  public override void Write(char[] buffer, int index, int count) {
    lock (Lock) {
      target.Write(buffer, index, count);
    }
  }

  public override void Write(ReadOnlySpan<char> buffer) {
    lock (Lock) {
      target.Write(buffer);
    }
  }

  public override void Write(string value) {
    lock (Lock) {
      target.Write(value);
    }
  }

  public override void WriteLine(char[] buffer, int index, int count) {
    lock (Lock) {
      target.WriteLine(buffer, index, count);
    }
  }

  public override void WriteLine(ReadOnlySpan<char> buffer) {
    lock (Lock) {
      target.WriteLine(buffer);
    }
  }

  public override void WriteLine(StringBuilder value) {
    lock (Lock) {
      target.WriteLine(value);
    }
  }

  public override void Write(StringBuilder value) {
    lock (Lock) {
      target.Write(value);
    }
  }

  public override Task WriteAsync(char value) {
    lock (Lock) {
      target.Write(value);
    }
    return Task.CompletedTask;
  }

  public override Task WriteAsync(char[] buffer, int index, int count) {
    lock (Lock) {
      target.Write(buffer, index, count);
    }
    return Task.CompletedTask;
  }

  public override Task WriteAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new()) {
    if (cancellationToken.IsCancellationRequested)
    {
      return Task.FromCanceled(cancellationToken);
    }

    lock (Lock) {
      target.Write(buffer);
    }
    return Task.CompletedTask;
  }

  public override Task WriteAsync(string value) {
    lock (Lock) {
      target.Write(value);
    }
    return Task.CompletedTask;
  }

  public override Task WriteAsync(StringBuilder value, CancellationToken cancellationToken = new()) {
    if (cancellationToken.IsCancellationRequested)
    {
      return Task.FromCanceled(cancellationToken);
    }

    lock (Lock) {
      target.Write(value);
    }
    return Task.CompletedTask;
  }

  public override Task WriteLineAsync(char value) {
    lock (Lock) {
      target.WriteLine(value);
    }
    return Task.CompletedTask;
  }

  public override Task WriteLineAsync(char[] buffer, int index, int count) {
    lock (Lock) {
      target.WriteLine(buffer, index, count);
    }
    return Task.CompletedTask;
  }

  public override Task WriteLineAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new()) {
    if (cancellationToken.IsCancellationRequested)
    {
      return Task.FromCanceled(cancellationToken);
    }

    lock (Lock) {
      target.WriteLine(buffer);
    }
    return Task.CompletedTask;
  }

  public override Task WriteLineAsync(string value) {
    lock (Lock) {
      target.WriteLine(value);
    }
    return Task.CompletedTask;
  }

  public override Task WriteLineAsync(StringBuilder value, CancellationToken cancellationToken = new()) {
    if (cancellationToken.IsCancellationRequested)
    {
      return Task.FromCanceled(cancellationToken);
    }

    lock (Lock) {
      target.WriteLine(value);
    }

    return Task.CompletedTask;
  }
}