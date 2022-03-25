using System;
using System.IO;
using System.Text;
using System.Threading;
using System.Threading.Tasks;

namespace Microsoft.Boogie;

class WriterWrapper : TextWriter {
  protected TextWriter target;
  public override Encoding Encoding => target.Encoding;

  protected WriterWrapper(TextWriter target) {
    this.target = target;
  }

  public override void Write(char value) {
    target.Write(value);
  }

  public override void Write(char[] buffer, int index, int count) {
    target.Write(buffer, index, count);
  }

  public override void Write(ReadOnlySpan<char> buffer) {
    target.Write(buffer);
  }

  public override void Write(string value) {
    target.Write(value);
  }

  public override void WriteLine(char[] buffer, int index, int count) {
    target.WriteLine(buffer, index, count);
  }

  public override void WriteLine(ReadOnlySpan<char> buffer) {
    target.WriteLine(buffer);
  }

  public override void WriteLine(StringBuilder value) {
    target.WriteLine(value);
  }

  public override void Write(StringBuilder value) {
    target.Write(value);
  }

  public override Task WriteAsync(char value) {
    return target.WriteAsync(value);
  }

  public override Task WriteAsync(char[] buffer, int index, int count) {
    return target.WriteAsync(buffer, index, count);
  }

  public override Task WriteAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new()) {
    return target.WriteAsync(buffer, cancellationToken);
  }

  public override Task WriteAsync(string value) {
    return target.WriteAsync(value);
  }

  public override Task WriteAsync(StringBuilder value, CancellationToken cancellationToken = new()) {
    return target.WriteAsync(value, cancellationToken);
  }

  public override Task WriteLineAsync(char value) {
    return target.WriteLineAsync(value);
  }

  public override Task WriteLineAsync(char[] buffer, int index, int count) {
    return target.WriteLineAsync(buffer, index, count);
  }

  public override Task WriteLineAsync(ReadOnlyMemory<char> buffer, CancellationToken cancellationToken = new()) {
    return target.WriteLineAsync(buffer, cancellationToken);
  }

  public override Task WriteLineAsync(string value) {
    return target.WriteLineAsync(value);
  }

  public override Task WriteLineAsync(StringBuilder value, CancellationToken cancellationToken = new()) {
    return target.WriteLineAsync(value, cancellationToken);
  }
}