using System;

namespace Demo
{
  static class GuidList
  {
    public const string guidIronyLanguageServiceString = "0A949930-AB4A-4A00-ABD0-191E81249240";
    public const string guidIronyLanguageServicePkgString = "FC7F6CE7-49C7-40C9-8636-EB37A936D77F";
    public const string guidIronyLanguageServiceCmdSetString = "72B8E853-2250-426B-9566-6D318ADE7C2D";

    public static readonly Guid guidIronyLanguageServiceCmdSet = new Guid(guidIronyLanguageServiceCmdSetString);
  };
}