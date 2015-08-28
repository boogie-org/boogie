// RUN: %boogie -monomorphize "%s" > "%t"
// RUN: %diff success.expect "%t"
type byte, name;
function OneByteToInt(byte) returns (int);
function TwoBytesToInt(byte, byte) returns (int);
function FourBytesToInt(byte, byte, byte, byte) returns (int);
axiom(forall b0:byte, c0:byte :: {OneByteToInt(b0), OneByteToInt(c0)} OneByteToInt(b0) == OneByteToInt(c0) ==> b0 == c0);
axiom(forall b0:byte, b1: byte, c0:byte, c1:byte :: {TwoBytesToInt(b0, b1), TwoBytesToInt(c0, c1)} TwoBytesToInt(b0, b1) == TwoBytesToInt(c0, c1) ==> b0 == c0 && b1 == c1);
axiom(forall b0:byte, b1: byte, b2:byte, b3:byte, c0:byte, c1:byte, c2:byte, c3:byte :: {FourBytesToInt(b0, b1, b2, b3), FourBytesToInt(c0, c1, c2, c3)} FourBytesToInt(b0, b1, b2, b3) == FourBytesToInt(c0, c1, c2, c3) ==> b0 == c0 && b1 == c1 && b2 == c2 && b3 == c3);

// Mutable
var Mem_BYTE:[int]byte;
var alloc:[int]name;


function Field(int) returns (name);
function Base(int) returns (int);

// Constants
const unique UNALLOCATED:name;
const unique ALLOCATED: name;
const unique FREED:name;

const unique BYTE:name;

function Equal([int]bool, [int]bool) returns (bool);
function Subset([int]bool, [int]bool) returns (bool);
function Disjoint([int]bool, [int]bool) returns (bool);

function Empty() returns ([int]bool);
function SetTrue() returns ([int]bool);
function Singleton(int) returns ([int]bool);
function Reachable([int,int]bool, int) returns ([int]bool);
function Union([int]bool, [int]bool) returns ([int]bool);
function Intersection([int]bool, [int]bool) returns ([int]bool);
function Difference([int]bool, [int]bool) returns ([int]bool);
function Dereference([int]bool, [int]int) returns ([int]bool);
function Inverse(f:[int]int, x:int) returns ([int]bool);

function AtLeast(int, int) returns ([int]bool);
function Rep(int, int) returns (int);
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x)[y]} AtLeast(n,x)[y] ==> x <= y && Rep(n,x) == Rep(n,y));
axiom(forall n:int, x:int, y:int :: {AtLeast(n,x),Rep(n,x),Rep(n,y)} x <= y && Rep(n,x) == Rep(n,y) ==> AtLeast(n,x)[y]);
axiom(forall n:int, x:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);
axiom(forall n:int, x:int, z:int :: {PLUS(x,n,z)} Rep(n,x) == Rep(n,PLUS(x,n,z)));
axiom(forall n:int, x:int :: {Rep(n,x)} (exists k:int :: Rep(n,x) - x  == n*k));

/*
function AtLeast(int, int) returns ([int]bool);
function ModEqual(int, int, int) returns (bool);
axiom(forall n:int, x:int :: ModEqual(n,x,x));
axiom(forall n:int, x:int, y:int :: {ModEqual(n,x,y)} ModEqual(n,x,y) ==> ModEqual(n,y,x));
axiom(forall n:int, x:int, y:int, z:int :: {ModEqual(n,x,y), ModEqual(n,y,z)} ModEqual(n,x,y) && ModEqual(n,y,z) ==> ModEqual(n,x,z));
axiom(forall n:int, x:int, z:int :: {PLUS(x,n,z)} ModEqual(n,x,PLUS(x,n,z)));
axiom(forall n:int, x:int, y:int :: {ModEqual(n,x,y)} ModEqual(n,x,y) ==> (exists k:int :: x - y == n*k));
axiom(forall x:int, n:int, y:int :: {AtLeast(n,x)[y]}{ModEqual(n,x,y)} AtLeast(n,x)[y] <==> x <= y && ModEqual(n,x,y));
axiom(forall x:int, n:int :: {AtLeast(n,x)} AtLeast(n,x)[x]);
*/

function Array(int, int, int) returns ([int]bool);
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z <= 0 ==> Equal(Array(x,n,z), Empty()));
axiom(forall x:int, n:int, z:int :: {Array(x,n,z)} z > 0 ==> Equal(Array(x,n,z), Difference(AtLeast(n,x),AtLeast(n,PLUS(x,n,z)))));


axiom(forall x:int :: !Empty()[x]);

axiom(forall x:int :: SetTrue()[x]);

axiom(forall x:int, y:int :: {Singleton(y)[x]} Singleton(y)[x] <==> x == y);
axiom(forall y:int :: {Singleton(y)} Singleton(y)[y]);

/* this formulation of Union IS more complete than the earlier one */
/* (A U B)[e], A[d], A U B = Singleton(c), d != e */
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Union(S,T)[x]}{Union(S,T),S[x]}{Union(S,T),T[x]} Union(S,T)[x] <==> S[x] || T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Intersection(S,T)[x]}{Intersection(S,T),S[x]}{Intersection(S,T),T[x]} Intersection(S,T)[x] <==>  S[x] && T[x]);
axiom(forall x:int, S:[int]bool, T:[int]bool :: {Difference(S,T)[x]}{Difference(S,T),S[x]}{Difference(S,T),T[x]} Difference(S,T)[x] <==> S[x] && !T[x]);

axiom(forall S:[int]bool, T:[int]bool :: {Equal(S,T)} Equal(S,T) <==> Subset(S,T) && Subset(T,S));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x],Subset(S,T)}{T[x],Subset(S,T)} S[x] && Subset(S,T) ==> T[x]);
axiom(forall S:[int]bool, T:[int]bool :: {Subset(S,T)} Subset(S,T) || (exists x:int :: S[x] && !T[x]));
axiom(forall x:int, S:[int]bool, T:[int]bool :: {S[x],Disjoint(S,T)}{T[x],Disjoint(S,T)} !(S[x] && Disjoint(S,T) && T[x]));
axiom(forall S:[int]bool, T:[int]bool :: {Disjoint(S,T)} Disjoint(S,T) || (exists x:int :: S[x] && T[x]));

axiom(forall f:[int]int, x:int :: {Inverse(f,f[x])} Inverse(f,f[x])[x]);
axiom(forall f:[int]int, x:int, y:int :: {Inverse(f,y), f[x]} Inverse(f,y)[x] ==> f[x] == y);
axiom(forall f:[int]int, x:int, y:int :: {Inverse(f[x := y],y)} Equal(Inverse(f[x := y],y), Union(Inverse(f,y), Singleton(x))));
axiom(forall f:[int]int, x:int, y:int, z:int :: {Inverse(f[x := y],z)} y == z || Equal(Inverse(f[x := y],z), Difference(Inverse(f,z), Singleton(x))));


axiom(forall x:int, S:[int]bool, M:[int]int :: {Dereference(S,M)[x]} Dereference(S,M)[x] ==> (exists y:int :: x == M[y] && S[y]));
axiom(forall x:int, S:[int]bool, M:[int]int :: {M[x], S[x], Dereference(S,M)} S[x] ==> Dereference(S,M)[M[x]]);
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} !S[x] ==> Equal(Dereference(S,M[x := y]), Dereference(S,M)));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] &&  Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Difference(Dereference(S,M), Singleton(M[x])), Singleton(y))));
axiom(forall x:int, y:int, S:[int]bool, M:[int]int :: {Dereference(S,M[x := y])} 
     S[x] && !Equal(Intersection(Inverse(M,M[x]), S), Singleton(x)) ==> Equal(Dereference(S,M[x := y]), Union(Dereference(S,M), Singleton(y))));

function Unified([name][int]int) returns ([int]int);
axiom(forall M:[name][int]int, x:int :: {Unified(M)[x]} Unified(M)[x] == M[Field(x)][x]);
axiom(forall M:[name][int]int, x:int, y:int :: {Unified(M[Field(x) := M[Field(x)][x := y]])} Unified(M[Field(x) := M[Field(x)][x := y]]) == Unified(M)[x := y]);
// Memory model

var Mem: [name][int]int;

function Match(a:int, t:name) returns (bool);
function HasType(v:int, t:name, m:[name][int]int) returns (bool);
function Values(t:name, m:[name][int]int) returns ([int]bool);
function T.Ptr(t:name) returns (name);

axiom(forall v:int, t:name, m:[name][int]int :: {Values(t, m)[v]} Values(t, m)[v] ==> HasType(v, t, m));
axiom(forall v:int, t:name, m:[name][int]int :: {HasType(v, t, m), Values(t, m)} HasType(v, t, m) ==> Values(t, m)[v]);

axiom(forall a:int, t:name :: {Match(a, T.Ptr(t))} Match(a, T.Ptr(t)) <==> Field(a) == T.Ptr(t));
axiom(forall v:int, t:name, m:[name][int]int :: {HasType(v, T.Ptr(t), m)} HasType(v, T.Ptr(t), m) <==> (v == 0 || (v > 0 && Match(v, t))));

axiom(forall v:int, t:name, m1:[name][int]int, m2:[name][int]int :: {HasType(v, t, m1), HasType(v, t, m2)}
    (HasType(v, t, m1) <==> HasType(v, t, m2)));

// Field declarations

const unique T.Guid_WMIGUIDREGINFO:name;
const unique T.InstanceCount_WMIGUIDREGINFO:name;
const unique T.Flags_WMIGUIDREGINFO:name;
const unique T.OperationID__ACCESS_STATE:name;
const unique T.SecurityEvaluated__ACCESS_STATE:name;
const unique T.GenerateAudit__ACCESS_STATE:name;
const unique T.GenerateOnClose__ACCESS_STATE:name;
const unique T.PrivilegesAllocated__ACCESS_STATE:name;
const unique T.Flags__ACCESS_STATE:name;
const unique T.RemainingDesiredAccess__ACCESS_STATE:name;
const unique T.PreviouslyGrantedAccess__ACCESS_STATE:name;
const unique T.OriginalDesiredAccess__ACCESS_STATE:name;
const unique T.SubjectSecurityContext__ACCESS_STATE:name;
const unique T.SecurityDescriptor__ACCESS_STATE:name;
const unique T.AuxData__ACCESS_STATE:name;
const unique T.Privileges__ACCESS_STATE:name;
const unique T.AuditPrivileges__ACCESS_STATE:name;
const unique T.ObjectName__ACCESS_STATE:name;
const unique T.ObjectTypeName__ACCESS_STATE:name;
const unique T.InterfaceType__CM_FULL_RESOURCE_DESCRIPTOR:name;
const unique T.BusNumber__CM_FULL_RESOURCE_DESCRIPTOR:name;
const unique T.PartialResourceList__CM_FULL_RESOURCE_DESCRIPTOR:name;
const unique T.Type__CM_PARTIAL_RESOURCE_DESCRIPTOR:name;
const unique T.ShareDisposition__CM_PARTIAL_RESOURCE_DESCRIPTOR:name;
const unique T.Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR:name;
const unique T.u__CM_PARTIAL_RESOURCE_DESCRIPTOR:name;
const unique T.Version__CM_PARTIAL_RESOURCE_LIST:name;
const unique T.Revision__CM_PARTIAL_RESOURCE_LIST:name;
const unique T.Count__CM_PARTIAL_RESOURCE_LIST:name;
const unique T.PartialDescriptors__CM_PARTIAL_RESOURCE_LIST:name;
const unique T.Count__CM_RESOURCE_LIST:name;
const unique T.List__CM_RESOURCE_LIST:name;
const unique T.Size__DEVICE_CAPABILITIES:name;
const unique T.Version__DEVICE_CAPABILITIES:name;
const unique T.DeviceD1__DEVICE_CAPABILITIES:name;
const unique T.DeviceD2__DEVICE_CAPABILITIES:name;
const unique T.LockSupported__DEVICE_CAPABILITIES:name;
const unique T.EjectSupported__DEVICE_CAPABILITIES:name;
const unique T.Removable__DEVICE_CAPABILITIES:name;
const unique T.DockDevice__DEVICE_CAPABILITIES:name;
const unique T.UniqueID__DEVICE_CAPABILITIES:name;
const unique T.SilentInstall__DEVICE_CAPABILITIES:name;
const unique T.RawDeviceOK__DEVICE_CAPABILITIES:name;
const unique T.SurpriseRemovalOK__DEVICE_CAPABILITIES:name;
const unique T.WakeFromD0__DEVICE_CAPABILITIES:name;
const unique T.WakeFromD1__DEVICE_CAPABILITIES:name;
const unique T.WakeFromD2__DEVICE_CAPABILITIES:name;
const unique T.WakeFromD3__DEVICE_CAPABILITIES:name;
const unique T.HardwareDisabled__DEVICE_CAPABILITIES:name;
const unique T.NonDynamic__DEVICE_CAPABILITIES:name;
const unique T.WarmEjectSupported__DEVICE_CAPABILITIES:name;
const unique T.NoDisplayInUI__DEVICE_CAPABILITIES:name;
const unique T.Reserved__DEVICE_CAPABILITIES:name;
const unique T.Address__DEVICE_CAPABILITIES:name;
const unique T.UINumber__DEVICE_CAPABILITIES:name;
const unique T.DeviceState__DEVICE_CAPABILITIES:name;
const unique T.SystemWake__DEVICE_CAPABILITIES:name;
const unique T.DeviceWake__DEVICE_CAPABILITIES:name;
const unique T.D1Latency__DEVICE_CAPABILITIES:name;
const unique T.D2Latency__DEVICE_CAPABILITIES:name;
const unique T.D3Latency__DEVICE_CAPABILITIES:name;
const unique T.Self__DEVICE_EXTENSION:name;
const unique T.TrueClassDevice__DEVICE_EXTENSION:name;
const unique T.TopPort__DEVICE_EXTENSION:name;
const unique T.PDO__DEVICE_EXTENSION:name;
const unique T.RemoveLock__DEVICE_EXTENSION:name;
const unique T.PnP__DEVICE_EXTENSION:name;
const unique T.Started__DEVICE_EXTENSION:name;
const unique T.AllowDisable__DEVICE_EXTENSION:name;
const unique T.WaitWakeSpinLock__DEVICE_EXTENSION:name;
const unique T.TrustedSubsystemCount__DEVICE_EXTENSION:name;
const unique T.InputCount__DEVICE_EXTENSION:name;
const unique T.SymbolicLinkName__DEVICE_EXTENSION:name;
const unique T.InputData__DEVICE_EXTENSION:name;
const unique T.DataIn__DEVICE_EXTENSION:name;
const unique T.DataOut__DEVICE_EXTENSION:name;
const unique T.KeyboardAttributes__DEVICE_EXTENSION:name;
const unique T.IndicatorParameters__DEVICE_EXTENSION:name;
const unique T.SpinLock__DEVICE_EXTENSION:name;
const unique T.ReadQueue__DEVICE_EXTENSION:name;
const unique T.SequenceNumber__DEVICE_EXTENSION:name;
const unique T.DeviceState__DEVICE_EXTENSION:name;
const unique T.SystemState__DEVICE_EXTENSION:name;
const unique T.UnitId__DEVICE_EXTENSION:name;
const unique T.WmiLibInfo__DEVICE_EXTENSION:name;
const unique T.SystemToDeviceState__DEVICE_EXTENSION:name;
const unique T.MinDeviceWakeState__DEVICE_EXTENSION:name;
const unique T.MinSystemWakeState__DEVICE_EXTENSION:name;
const unique T.WaitWakeIrp__DEVICE_EXTENSION:name;
const unique T.ExtraWaitWakeIrp__DEVICE_EXTENSION:name;
const unique T.TargetNotifyHandle__DEVICE_EXTENSION:name;
const unique T.Link__DEVICE_EXTENSION:name;
const unique T.File__DEVICE_EXTENSION:name;
const unique T.Enabled__DEVICE_EXTENSION:name;
const unique T.OkayToLogOverflow__DEVICE_EXTENSION:name;
const unique T.WaitWakeEnabled__DEVICE_EXTENSION:name;
const unique T.SurpriseRemoved__DEVICE_EXTENSION:name;
const unique T.Type__DEVICE_OBJECT:name;
const unique T.Size__DEVICE_OBJECT:name;
const unique T.ReferenceCount__DEVICE_OBJECT:name;
const unique T.DriverObject__DEVICE_OBJECT:name;
const unique T.NextDevice__DEVICE_OBJECT:name;
const unique T.AttachedDevice__DEVICE_OBJECT:name;
const unique T.CurrentIrp__DEVICE_OBJECT:name;
const unique T.Timer__DEVICE_OBJECT:name;
const unique T.Flags__DEVICE_OBJECT:name;
const unique T.Characteristics__DEVICE_OBJECT:name;
const unique T.Vpb__DEVICE_OBJECT:name;
const unique T.DeviceExtension__DEVICE_OBJECT:name;
const unique T.DeviceType__DEVICE_OBJECT:name;
const unique T.StackSize__DEVICE_OBJECT:name;
const unique T.Queue__DEVICE_OBJECT:name;
const unique T.AlignmentRequirement__DEVICE_OBJECT:name;
const unique T.DeviceQueue__DEVICE_OBJECT:name;
const unique T.Dpc__DEVICE_OBJECT:name;
const unique T.ActiveThreadCount__DEVICE_OBJECT:name;
const unique T.SecurityDescriptor__DEVICE_OBJECT:name;
const unique T.DeviceLock__DEVICE_OBJECT:name;
const unique T.SectorSize__DEVICE_OBJECT:name;
const unique T.Spare1__DEVICE_OBJECT:name;
const unique T.DeviceObjectExtension__DEVICE_OBJECT:name;
const unique T.Reserved__DEVICE_OBJECT:name;
const unique T.Type__DEVOBJ_EXTENSION:name;
const unique T.Size__DEVOBJ_EXTENSION:name;
const unique T.DeviceObject__DEVOBJ_EXTENSION:name;
const unique T.__unnamed_4_a97c65a1__DISPATCHER_HEADER:name;
const unique T.SignalState__DISPATCHER_HEADER:name;
const unique T.WaitListHead__DISPATCHER_HEADER:name;
const unique T.DriverObject__DRIVER_EXTENSION:name;
const unique T.AddDevice__DRIVER_EXTENSION:name;
const unique T.Count__DRIVER_EXTENSION:name;
const unique T.ServiceKeyName__DRIVER_EXTENSION:name;
const unique T.Type__DRIVER_OBJECT:name;
const unique T.Size__DRIVER_OBJECT:name;
const unique T.DeviceObject__DRIVER_OBJECT:name;
const unique T.Flags__DRIVER_OBJECT:name;
const unique T.DriverStart__DRIVER_OBJECT:name;
const unique T.DriverSize__DRIVER_OBJECT:name;
const unique T.DriverSection__DRIVER_OBJECT:name;
const unique T.DriverExtension__DRIVER_OBJECT:name;
const unique T.DriverName__DRIVER_OBJECT:name;
const unique T.HardwareDatabase__DRIVER_OBJECT:name;
const unique T.FastIoDispatch__DRIVER_OBJECT:name;
const unique T.DriverInit__DRIVER_OBJECT:name;
const unique T.DriverStartIo__DRIVER_OBJECT:name;
const unique T.DriverUnload__DRIVER_OBJECT:name;
const unique T.MajorFunction__DRIVER_OBJECT:name;
const unique T.SystemResourcesList__ERESOURCE:name;
const unique T.OwnerTable__ERESOURCE:name;
const unique T.ActiveCount__ERESOURCE:name;
const unique T.Flag__ERESOURCE:name;
const unique T.SharedWaiters__ERESOURCE:name;
const unique T.ExclusiveWaiters__ERESOURCE:name;
const unique T.OwnerEntry__ERESOURCE:name;
const unique T.ActiveEntries__ERESOURCE:name;
const unique T.ContentionCount__ERESOURCE:name;
const unique T.NumberOfSharedWaiters__ERESOURCE:name;
const unique T.NumberOfExclusiveWaiters__ERESOURCE:name;
const unique T.__unnamed_4_52c594f7__ERESOURCE:name;
const unique T.SpinLock__ERESOURCE:name;
const unique T.SizeOfFastIoDispatch__FAST_IO_DISPATCH:name;
const unique T.FastIoCheckIfPossible__FAST_IO_DISPATCH:name;
const unique T.FastIoRead__FAST_IO_DISPATCH:name;
const unique T.FastIoWrite__FAST_IO_DISPATCH:name;
const unique T.FastIoQueryBasicInfo__FAST_IO_DISPATCH:name;
const unique T.FastIoQueryStandardInfo__FAST_IO_DISPATCH:name;
const unique T.FastIoLock__FAST_IO_DISPATCH:name;
const unique T.FastIoUnlockSingle__FAST_IO_DISPATCH:name;
const unique T.FastIoUnlockAll__FAST_IO_DISPATCH:name;
const unique T.FastIoUnlockAllByKey__FAST_IO_DISPATCH:name;
const unique T.FastIoDeviceControl__FAST_IO_DISPATCH:name;
const unique T.AcquireFileForNtCreateSection__FAST_IO_DISPATCH:name;
const unique T.ReleaseFileForNtCreateSection__FAST_IO_DISPATCH:name;
const unique T.FastIoDetachDevice__FAST_IO_DISPATCH:name;
const unique T.FastIoQueryNetworkOpenInfo__FAST_IO_DISPATCH:name;
const unique T.AcquireForModWrite__FAST_IO_DISPATCH:name;
const unique T.MdlRead__FAST_IO_DISPATCH:name;
const unique T.MdlReadComplete__FAST_IO_DISPATCH:name;
const unique T.PrepareMdlWrite__FAST_IO_DISPATCH:name;
const unique T.MdlWriteComplete__FAST_IO_DISPATCH:name;
const unique T.FastIoReadCompressed__FAST_IO_DISPATCH:name;
const unique T.FastIoWriteCompressed__FAST_IO_DISPATCH:name;
const unique T.MdlReadCompleteCompressed__FAST_IO_DISPATCH:name;
const unique T.MdlWriteCompleteCompressed__FAST_IO_DISPATCH:name;
const unique T.FastIoQueryOpen__FAST_IO_DISPATCH:name;
const unique T.ReleaseForModWrite__FAST_IO_DISPATCH:name;
const unique T.AcquireForCcFlush__FAST_IO_DISPATCH:name;
const unique T.ReleaseForCcFlush__FAST_IO_DISPATCH:name;
const unique T.Count__FAST_MUTEX:name;
const unique T.Owner__FAST_MUTEX:name;
const unique T.Contention__FAST_MUTEX:name;
const unique T.Gate__FAST_MUTEX:name;
const unique T.OldIrql__FAST_MUTEX:name;
const unique T.CreationTime__FILE_BASIC_INFORMATION:name;
const unique T.LastAccessTime__FILE_BASIC_INFORMATION:name;
const unique T.LastWriteTime__FILE_BASIC_INFORMATION:name;
const unique T.ChangeTime__FILE_BASIC_INFORMATION:name;
const unique T.FileAttributes__FILE_BASIC_INFORMATION:name;
const unique T.CreationTime__FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.LastAccessTime__FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.LastWriteTime__FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.ChangeTime__FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.AllocationSize__FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.EndOfFile__FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.FileAttributes__FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.Type__FILE_OBJECT:name;
const unique T.Size__FILE_OBJECT:name;
const unique T.DeviceObject__FILE_OBJECT:name;
const unique T.Vpb__FILE_OBJECT:name;
const unique T.FsContext__FILE_OBJECT:name;
const unique T.FsContext2__FILE_OBJECT:name;
const unique T.SectionObjectPointer__FILE_OBJECT:name;
const unique T.PrivateCacheMap__FILE_OBJECT:name;
const unique T.FinalStatus__FILE_OBJECT:name;
const unique T.RelatedFileObject__FILE_OBJECT:name;
const unique T.LockOperation__FILE_OBJECT:name;
const unique T.DeletePending__FILE_OBJECT:name;
const unique T.ReadAccess__FILE_OBJECT:name;
const unique T.WriteAccess__FILE_OBJECT:name;
const unique T.DeleteAccess__FILE_OBJECT:name;
const unique T.SharedRead__FILE_OBJECT:name;
const unique T.SharedWrite__FILE_OBJECT:name;
const unique T.SharedDelete__FILE_OBJECT:name;
const unique T.Flags__FILE_OBJECT:name;
const unique T.FileName__FILE_OBJECT:name;
const unique T.CurrentByteOffset__FILE_OBJECT:name;
const unique T.Waiters__FILE_OBJECT:name;
const unique T.Busy__FILE_OBJECT:name;
const unique T.LastLock__FILE_OBJECT:name;
const unique T.Lock__FILE_OBJECT:name;
const unique T.Event__FILE_OBJECT:name;
const unique T.CompletionContext__FILE_OBJECT:name;
const unique T.IrpListLock__FILE_OBJECT:name;
const unique T.IrpList__FILE_OBJECT:name;
const unique T.FileObjectExtension__FILE_OBJECT:name;
const unique T.AllocationSize__FILE_STANDARD_INFORMATION:name;
const unique T.EndOfFile__FILE_STANDARD_INFORMATION:name;
const unique T.NumberOfLinks__FILE_STANDARD_INFORMATION:name;
const unique T.DeletePending__FILE_STANDARD_INFORMATION:name;
const unique T.Directory__FILE_STANDARD_INFORMATION:name;
const unique T.Debug__GLOBALS:name;
const unique T.GrandMaster__GLOBALS:name;
const unique T.AssocClassList__GLOBALS:name;
const unique T.NumAssocClass__GLOBALS:name;
const unique T.Opens__GLOBALS:name;
const unique T.NumberLegacyPorts__GLOBALS:name;
const unique T.Mutex__GLOBALS:name;
const unique T.ConnectOneClassToOnePort__GLOBALS:name;
const unique T.SendOutputToAllPorts__GLOBALS:name;
const unique T.PortsServiced__GLOBALS:name;
const unique T.InitExtension__GLOBALS:name;
const unique T.RegistryPath__GLOBALS:name;
const unique T.BaseClassName__GLOBALS:name;
const unique T.BaseClassBuffer__GLOBALS:name;
const unique T.LegacyDeviceList__GLOBALS:name;
const unique T.Data1__GUID:name;
const unique T.Data2__GUID:name;
const unique T.Data3__GUID:name;
const unique T.Data4__GUID:name;
const unique T.PrivilegeCount__INITIAL_PRIVILEGE_SET:name;
const unique T.Control__INITIAL_PRIVILEGE_SET:name;
const unique T.Privilege__INITIAL_PRIVILEGE_SET:name;
const unique T.Size__INTERFACE:name;
const unique T.Version__INTERFACE:name;
const unique T.Context__INTERFACE:name;
const unique T.InterfaceReference__INTERFACE:name;
const unique T.InterfaceDereference__INTERFACE:name;
const unique T.Port__IO_COMPLETION_CONTEXT:name;
const unique T.Key__IO_COMPLETION_CONTEXT:name;
const unique T.Common__IO_REMOVE_LOCK:name;
const unique T.Dbg__IO_REMOVE_LOCK:name;
const unique T.Removed__IO_REMOVE_LOCK_COMMON_BLOCK:name;
const unique T.Reserved__IO_REMOVE_LOCK_COMMON_BLOCK:name;
const unique T.IoCount__IO_REMOVE_LOCK_COMMON_BLOCK:name;
const unique T.RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK:name;
const unique T.Signature__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.LockList__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.Spin__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.Reserved1__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.Reserved2__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.Blocks__IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T.Option__IO_RESOURCE_DESCRIPTOR:name;
const unique T.Type__IO_RESOURCE_DESCRIPTOR:name;
const unique T.ShareDisposition__IO_RESOURCE_DESCRIPTOR:name;
const unique T.Spare1__IO_RESOURCE_DESCRIPTOR:name;
const unique T.Flags__IO_RESOURCE_DESCRIPTOR:name;
const unique T.Spare2__IO_RESOURCE_DESCRIPTOR:name;
const unique T.u__IO_RESOURCE_DESCRIPTOR:name;
const unique T.Version__IO_RESOURCE_LIST:name;
const unique T.Revision__IO_RESOURCE_LIST:name;
const unique T.Count__IO_RESOURCE_LIST:name;
const unique T.Descriptors__IO_RESOURCE_LIST:name;
const unique T.ListSize__IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.InterfaceType__IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.BusNumber__IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.SlotNumber__IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.Reserved__IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.AlternativeLists__IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.List__IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.SecurityQos__IO_SECURITY_CONTEXT:name;
const unique T.AccessState__IO_SECURITY_CONTEXT:name;
const unique T.DesiredAccess__IO_SECURITY_CONTEXT:name;
const unique T.FullCreateOptions__IO_SECURITY_CONTEXT:name;
const unique T.MajorFunction__IO_STACK_LOCATION:name;
const unique T.MinorFunction__IO_STACK_LOCATION:name;
const unique T.Flags__IO_STACK_LOCATION:name;
const unique T.Control__IO_STACK_LOCATION:name;
const unique T.Parameters__IO_STACK_LOCATION:name;
const unique T.DeviceObject__IO_STACK_LOCATION:name;
const unique T.FileObject__IO_STACK_LOCATION:name;
const unique T.CompletionRoutine__IO_STACK_LOCATION:name;
const unique T.Context__IO_STACK_LOCATION:name;
const unique T.__unnamed_4_d99b6e2b__IO_STATUS_BLOCK:name;
const unique T.Information__IO_STATUS_BLOCK:name;
const unique T.Type__IRP:name;
const unique T.Size__IRP:name;
const unique T.MdlAddress__IRP:name;
const unique T.Flags__IRP:name;
const unique T.AssociatedIrp__IRP:name;
const unique T.ThreadListEntry__IRP:name;
const unique T.IoStatus__IRP:name;
const unique T.RequestorMode__IRP:name;
const unique T.PendingReturned__IRP:name;
const unique T.StackCount__IRP:name;
const unique T.CurrentLocation__IRP:name;
const unique T.Cancel__IRP:name;
const unique T.CancelIrql__IRP:name;
const unique T.ApcEnvironment__IRP:name;
const unique T.AllocationFlags__IRP:name;
const unique T.UserIosb__IRP:name;
const unique T.UserEvent__IRP:name;
const unique T.Overlay__IRP:name;
const unique T.CancelRoutine__IRP:name;
const unique T.UserBuffer__IRP:name;
const unique T.Tail__IRP:name;
const unique T.Type__KAPC:name;
const unique T.SpareByte0__KAPC:name;
const unique T.Size__KAPC:name;
const unique T.SpareByte1__KAPC:name;
const unique T.SpareLong0__KAPC:name;
const unique T.Thread__KAPC:name;
const unique T.ApcListEntry__KAPC:name;
const unique T.KernelRoutine__KAPC:name;
const unique T.RundownRoutine__KAPC:name;
const unique T.NormalRoutine__KAPC:name;
const unique T.NormalContext__KAPC:name;
const unique T.SystemArgument1__KAPC:name;
const unique T.SystemArgument2__KAPC:name;
const unique T.ApcStateIndex__KAPC:name;
const unique T.ApcMode__KAPC:name;
const unique T.Inserted__KAPC:name;
const unique T.Type__KDEVICE_QUEUE:name;
const unique T.Size__KDEVICE_QUEUE:name;
const unique T.DeviceListHead__KDEVICE_QUEUE:name;
const unique T.Lock__KDEVICE_QUEUE:name;
const unique T.Busy__KDEVICE_QUEUE:name;
const unique T.DeviceListEntry__KDEVICE_QUEUE_ENTRY:name;
const unique T.SortKey__KDEVICE_QUEUE_ENTRY:name;
const unique T.Inserted__KDEVICE_QUEUE_ENTRY:name;
const unique T.Type__KDPC:name;
const unique T.Importance__KDPC:name;
const unique T.Number__KDPC:name;
const unique T.DpcListEntry__KDPC:name;
const unique T.DeferredRoutine__KDPC:name;
const unique T.DeferredContext__KDPC:name;
const unique T.SystemArgument1__KDPC:name;
const unique T.SystemArgument2__KDPC:name;
const unique T.DpcData__KDPC:name;
const unique T.Header__KEVENT:name;
const unique T.KeyboardIdentifier__KEYBOARD_ATTRIBUTES:name;
const unique T.KeyboardMode__KEYBOARD_ATTRIBUTES:name;
const unique T.NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES:name;
const unique T.NumberOfIndicators__KEYBOARD_ATTRIBUTES:name;
const unique T.NumberOfKeysTotal__KEYBOARD_ATTRIBUTES:name;
const unique T.InputDataQueueLength__KEYBOARD_ATTRIBUTES:name;
const unique T.KeyRepeatMinimum__KEYBOARD_ATTRIBUTES:name;
const unique T.KeyRepeatMaximum__KEYBOARD_ATTRIBUTES:name;
const unique T.Type__KEYBOARD_ID:name;
const unique T.Subtype__KEYBOARD_ID:name;
const unique T.UnitId__KEYBOARD_INDICATOR_PARAMETERS:name;
const unique T.LedFlags__KEYBOARD_INDICATOR_PARAMETERS:name;
const unique T.UnitId__KEYBOARD_INPUT_DATA:name;
const unique T.MakeCode__KEYBOARD_INPUT_DATA:name;
const unique T.Flags__KEYBOARD_INPUT_DATA:name;
const unique T.Reserved__KEYBOARD_INPUT_DATA:name;
const unique T.ExtraInformation__KEYBOARD_INPUT_DATA:name;
const unique T.UnitId__KEYBOARD_TYPEMATIC_PARAMETERS:name;
const unique T.Rate__KEYBOARD_TYPEMATIC_PARAMETERS:name;
const unique T.Delay__KEYBOARD_TYPEMATIC_PARAMETERS:name;
const unique T.Header__KSEMAPHORE:name;
const unique T.Limit__KSEMAPHORE:name;
const unique T.__unnamed_8_58ee4a31__LARGE_INTEGER:name;
const unique T.u__LARGE_INTEGER:name;
const unique T.QuadPart__LARGE_INTEGER:name;
const unique T.Flink__LIST_ENTRY:name;
const unique T.Blink__LIST_ENTRY:name;
const unique T.LowPart__LUID:name;
const unique T.HighPart__LUID:name;
const unique T.Luid__LUID_AND_ATTRIBUTES:name;
const unique T.Attributes__LUID_AND_ATTRIBUTES:name;
const unique T.Next__MDL:name;
const unique T.Size__MDL:name;
const unique T.MdlFlags__MDL:name;
const unique T.Process__MDL:name;
const unique T.MappedSystemVa__MDL:name;
const unique T.StartVa__MDL:name;
const unique T.ByteCount__MDL:name;
const unique T.ByteOffset__MDL:name;
const unique T.OwnerThread__OWNER_ENTRY:name;
const unique T.__unnamed_4_6f9ac8e1__OWNER_ENTRY:name;
const unique T.File__PORT:name;
const unique T.Port__PORT:name;
const unique T.Enabled__PORT:name;
const unique T.Reserved__PORT:name;
const unique T.Free__PORT:name;
const unique T.SequenceD1__POWER_SEQUENCE:name;
const unique T.SequenceD2__POWER_SEQUENCE:name;
const unique T.SequenceD3__POWER_SEQUENCE:name;
const unique T.SystemState__POWER_STATE:name;
const unique T.DeviceState__POWER_STATE:name;
const unique T.PrivilegeCount__PRIVILEGE_SET:name;
const unique T.Control__PRIVILEGE_SET:name;
const unique T.Privilege__PRIVILEGE_SET:name;
const unique T.DataSectionObject__SECTION_OBJECT_POINTERS:name;
const unique T.SharedCacheMap__SECTION_OBJECT_POINTERS:name;
const unique T.ImageSectionObject__SECTION_OBJECT_POINTERS:name;
const unique T.Length__SECURITY_QUALITY_OF_SERVICE:name;
const unique T.ImpersonationLevel__SECURITY_QUALITY_OF_SERVICE:name;
const unique T.ContextTrackingMode__SECURITY_QUALITY_OF_SERVICE:name;
const unique T.EffectiveOnly__SECURITY_QUALITY_OF_SERVICE:name;
const unique T.ClientToken__SECURITY_SUBJECT_CONTEXT:name;
const unique T.ImpersonationLevel__SECURITY_SUBJECT_CONTEXT:name;
const unique T.PrimaryToken__SECURITY_SUBJECT_CONTEXT:name;
const unique T.ProcessAuditId__SECURITY_SUBJECT_CONTEXT:name;
const unique T.__unnamed_4_3a2fdc5e__SYSTEM_POWER_STATE_CONTEXT:name;
const unique T.Length__UNICODE_STRING:name;
const unique T.MaximumLength__UNICODE_STRING:name;
const unique T.Buffer__UNICODE_STRING:name;
const unique T.Type__VPB:name;
const unique T.Size__VPB:name;
const unique T.Flags__VPB:name;
const unique T.VolumeLabelLength__VPB:name;
const unique T.DeviceObject__VPB:name;
const unique T.RealDevice__VPB:name;
const unique T.SerialNumber__VPB:name;
const unique T.ReferenceCount__VPB:name;
const unique T.VolumeLabel__VPB:name;
const unique T.WaitQueueEntry__WAIT_CONTEXT_BLOCK:name;
const unique T.DeviceRoutine__WAIT_CONTEXT_BLOCK:name;
const unique T.DeviceContext__WAIT_CONTEXT_BLOCK:name;
const unique T.NumberOfMapRegisters__WAIT_CONTEXT_BLOCK:name;
const unique T.DeviceObject__WAIT_CONTEXT_BLOCK:name;
const unique T.CurrentIrp__WAIT_CONTEXT_BLOCK:name;
const unique T.BufferChainingDpc__WAIT_CONTEXT_BLOCK:name;
const unique T.GuidCount__WMILIB_CONTEXT:name;
const unique T.GuidList__WMILIB_CONTEXT:name;
const unique T.QueryWmiRegInfo__WMILIB_CONTEXT:name;
const unique T.QueryWmiDataBlock__WMILIB_CONTEXT:name;
const unique T.SetWmiDataBlock__WMILIB_CONTEXT:name;
const unique T.SetWmiDataItem__WMILIB_CONTEXT:name;
const unique T.ExecuteWmiMethod__WMILIB_CONTEXT:name;
const unique T.WmiFunctionControl__WMILIB_CONTEXT:name;
const unique T.Reserved___unnamed_12_0d6a30de:name;
const unique T.MessageCount___unnamed_12_0d6a30de:name;
const unique T.Vector___unnamed_12_0d6a30de:name;
const unique T.Affinity___unnamed_12_0d6a30de:name;
const unique T.Start___unnamed_12_17f5c211:name;
const unique T.Length48___unnamed_12_17f5c211:name;
const unique T.Start___unnamed_12_1fb42e39:name;
const unique T.Length___unnamed_12_1fb42e39:name;
const unique T.Reserved___unnamed_12_1fb42e39:name;
const unique T.Start___unnamed_12_2a1563c6:name;
const unique T.Length___unnamed_12_2a1563c6:name;
const unique T.DataSize___unnamed_12_31347272:name;
const unique T.Reserved1___unnamed_12_31347272:name;
const unique T.Reserved2___unnamed_12_31347272:name;
const unique T.Raw___unnamed_12_429aadc0:name;
const unique T.Translated___unnamed_12_429aadc0:name;
const unique T.Start___unnamed_12_4719de1a:name;
const unique T.Length___unnamed_12_4719de1a:name;
const unique T.Data___unnamed_12_4be56faa:name;
const unique T.Data___unnamed_12_5ce25b92:name;
const unique T.Generic___unnamed_12_7a698b72:name;
const unique T.Port___unnamed_12_7a698b72:name;
const unique T.Interrupt___unnamed_12_7a698b72:name;
const unique T.MessageInterrupt___unnamed_12_7a698b72:name;
const unique T.Memory___unnamed_12_7a698b72:name;
const unique T.Dma___unnamed_12_7a698b72:name;
const unique T.DevicePrivate___unnamed_12_7a698b72:name;
const unique T.BusNumber___unnamed_12_7a698b72:name;
const unique T.DeviceSpecificData___unnamed_12_7a698b72:name;
const unique T.Memory40___unnamed_12_7a698b72:name;
const unique T.Memory48___unnamed_12_7a698b72:name;
const unique T.Memory64___unnamed_12_7a698b72:name;
const unique T.Start___unnamed_12_87c0de8d:name;
const unique T.Length64___unnamed_12_87c0de8d:name;
const unique T.Start___unnamed_12_98bfc55a:name;
const unique T.Length40___unnamed_12_98bfc55a:name;
const unique T.Priority___unnamed_12_ab1bd9d7:name;
const unique T.Reserved1___unnamed_12_ab1bd9d7:name;
const unique T.Reserved2___unnamed_12_ab1bd9d7:name;
const unique T.Level___unnamed_12_b0429be9:name;
const unique T.Vector___unnamed_12_b0429be9:name;
const unique T.Affinity___unnamed_12_b0429be9:name;
const unique T.ListEntry___unnamed_12_b43e8de8:name;
const unique T.__unnamed_4_f19b65c1___unnamed_12_b43e8de8:name;
const unique T.Level___unnamed_12_bfdb39ee:name;
const unique T.Vector___unnamed_12_bfdb39ee:name;
const unique T.Affinity___unnamed_12_bfdb39ee:name;
const unique T.Start___unnamed_12_cd42b3c3:name;
const unique T.Length___unnamed_12_cd42b3c3:name;
const unique T.__unnamed_12_429aadc0___unnamed_12_e668effc:name;
const unique T.Channel___unnamed_12_e80d029e:name;
const unique T.Port___unnamed_12_e80d029e:name;
const unique T.Reserved1___unnamed_12_e80d029e:name;
const unique T.Length___unnamed_16_07c0bcc5:name;
const unique T.MinBusNumber___unnamed_16_07c0bcc5:name;
const unique T.MaxBusNumber___unnamed_16_07c0bcc5:name;
const unique T.Reserved___unnamed_16_07c0bcc5:name;
const unique T.InterfaceType___unnamed_16_29cb9f2f:name;
const unique T.Size___unnamed_16_29cb9f2f:name;
const unique T.Version___unnamed_16_29cb9f2f:name;
const unique T.Interface___unnamed_16_29cb9f2f:name;
const unique T.InterfaceSpecificData___unnamed_16_29cb9f2f:name;
const unique T.SecurityContext___unnamed_16_30f11dbf:name;
const unique T.Options___unnamed_16_30f11dbf:name;
const unique T.FileAttributes___unnamed_16_30f11dbf:name;
const unique T.ShareAccess___unnamed_16_30f11dbf:name;
const unique T.EaLength___unnamed_16_30f11dbf:name;
const unique T.DriverContext___unnamed_16_35034f68:name;
const unique T.Length___unnamed_16_487a9498:name;
const unique T.FileName___unnamed_16_487a9498:name;
const unique T.FileInformationClass___unnamed_16_487a9498:name;
const unique T.FileIndex___unnamed_16_487a9498:name;
const unique T.OutputBufferLength___unnamed_16_5f6a8844:name;
const unique T.InputBufferLength___unnamed_16_5f6a8844:name;
const unique T.FsControlCode___unnamed_16_5f6a8844:name;
const unique T.Type3InputBuffer___unnamed_16_5f6a8844:name;
const unique T.Length___unnamed_16_7177b9f3:name;
const unique T.FileInformationClass___unnamed_16_7177b9f3:name;
const unique T.FileObject___unnamed_16_7177b9f3:name;
const unique T.__unnamed_4_43913aa5___unnamed_16_7177b9f3:name;
const unique T.Length___unnamed_16_88e91ef6:name;
const unique T.Key___unnamed_16_88e91ef6:name;
const unique T.ByteOffset___unnamed_16_88e91ef6:name;
const unique T.Length___unnamed_16_8c506c98:name;
const unique T.Key___unnamed_16_8c506c98:name;
const unique T.ByteOffset___unnamed_16_8c506c98:name;
const unique T.WhichSpace___unnamed_16_9ac2e5f8:name;
const unique T.Buffer___unnamed_16_9ac2e5f8:name;
const unique T.Offset___unnamed_16_9ac2e5f8:name;
const unique T.Length___unnamed_16_9ac2e5f8:name;
const unique T.Create___unnamed_16_b93842ad:name;
const unique T.Read___unnamed_16_b93842ad:name;
const unique T.Write___unnamed_16_b93842ad:name;
const unique T.QueryDirectory___unnamed_16_b93842ad:name;
const unique T.NotifyDirectory___unnamed_16_b93842ad:name;
const unique T.QueryFile___unnamed_16_b93842ad:name;
const unique T.SetFile___unnamed_16_b93842ad:name;
const unique T.QueryEa___unnamed_16_b93842ad:name;
const unique T.SetEa___unnamed_16_b93842ad:name;
const unique T.QueryVolume___unnamed_16_b93842ad:name;
const unique T.SetVolume___unnamed_16_b93842ad:name;
const unique T.FileSystemControl___unnamed_16_b93842ad:name;
const unique T.LockControl___unnamed_16_b93842ad:name;
const unique T.DeviceIoControl___unnamed_16_b93842ad:name;
const unique T.QuerySecurity___unnamed_16_b93842ad:name;
const unique T.SetSecurity___unnamed_16_b93842ad:name;
const unique T.MountVolume___unnamed_16_b93842ad:name;
const unique T.VerifyVolume___unnamed_16_b93842ad:name;
const unique T.Scsi___unnamed_16_b93842ad:name;
const unique T.QueryQuota___unnamed_16_b93842ad:name;
const unique T.SetQuota___unnamed_16_b93842ad:name;
const unique T.QueryDeviceRelations___unnamed_16_b93842ad:name;
const unique T.QueryInterface___unnamed_16_b93842ad:name;
const unique T.DeviceCapabilities___unnamed_16_b93842ad:name;
const unique T.FilterResourceRequirements___unnamed_16_b93842ad:name;
const unique T.ReadWriteConfig___unnamed_16_b93842ad:name;
const unique T.SetLock___unnamed_16_b93842ad:name;
const unique T.QueryId___unnamed_16_b93842ad:name;
const unique T.QueryDeviceText___unnamed_16_b93842ad:name;
const unique T.UsageNotification___unnamed_16_b93842ad:name;
const unique T.WaitWake___unnamed_16_b93842ad:name;
const unique T.PowerSequence___unnamed_16_b93842ad:name;
const unique T.Power___unnamed_16_b93842ad:name;
const unique T.StartDevice___unnamed_16_b93842ad:name;
const unique T.WMI___unnamed_16_b93842ad:name;
const unique T.Others___unnamed_16_b93842ad:name;
const unique T.Length___unnamed_16_b9c62eab:name;
const unique T.Key___unnamed_16_b9c62eab:name;
const unique T.ByteOffset___unnamed_16_b9c62eab:name;
const unique T.__unnamed_4_7d9d0c7e___unnamed_16_bb584060:name;
const unique T.Type___unnamed_16_bb584060:name;
const unique T.State___unnamed_16_bb584060:name;
const unique T.ShutdownType___unnamed_16_bb584060:name;
const unique T.OutputBufferLength___unnamed_16_dba55c7c:name;
const unique T.InputBufferLength___unnamed_16_dba55c7c:name;
const unique T.IoControlCode___unnamed_16_dba55c7c:name;
const unique T.Type3InputBuffer___unnamed_16_dba55c7c:name;
const unique T.DeviceQueueEntry___unnamed_16_e70c268b:name;
const unique T.__unnamed_16_35034f68___unnamed_16_e70c268b:name;
const unique T.Argument1___unnamed_16_e734d694:name;
const unique T.Argument2___unnamed_16_e734d694:name;
const unique T.Argument3___unnamed_16_e734d694:name;
const unique T.Argument4___unnamed_16_e734d694:name;
const unique T.ProviderId___unnamed_16_eac6dbea:name;
const unique T.DataPath___unnamed_16_eac6dbea:name;
const unique T.BufferSize___unnamed_16_eac6dbea:name;
const unique T.Buffer___unnamed_16_eac6dbea:name;
const unique T.Length___unnamed_16_f6cae4c2:name;
const unique T.EaList___unnamed_16_f6cae4c2:name;
const unique T.EaListLength___unnamed_16_f6cae4c2:name;
const unique T.EaIndex___unnamed_16_f6cae4c2:name;
const unique T.Length___unnamed_16_fe36e4f4:name;
const unique T.StartSid___unnamed_16_fe36e4f4:name;
const unique T.SidList___unnamed_16_fe36e4f4:name;
const unique T.SidListLength___unnamed_16_fe36e4f4:name;
const unique T.Abandoned___unnamed_1_29794256:name;
const unique T.Absolute___unnamed_1_29794256:name;
const unique T.NpxIrql___unnamed_1_29794256:name;
const unique T.Signalling___unnamed_1_29794256:name;
const unique T.Inserted___unnamed_1_2dc63b48:name;
const unique T.DebugActive___unnamed_1_2dc63b48:name;
const unique T.DpcActive___unnamed_1_2dc63b48:name;
const unique T.Size___unnamed_1_2ef8da39:name;
const unique T.Hand___unnamed_1_2ef8da39:name;
const unique T.Lock___unnamed_1_faa7dc71:name;
const unique T.MinimumVector___unnamed_20_f4d2e6d8:name;
const unique T.MaximumVector___unnamed_20_f4d2e6d8:name;
const unique T.AffinityPolicy___unnamed_20_f4d2e6d8:name;
const unique T.PriorityPolicy___unnamed_20_f4d2e6d8:name;
const unique T.TargetedProcessors___unnamed_20_f4d2e6d8:name;
const unique T.Length___unnamed_24_41cbc8c0:name;
const unique T.Alignment___unnamed_24_41cbc8c0:name;
const unique T.MinimumAddress___unnamed_24_41cbc8c0:name;
const unique T.MaximumAddress___unnamed_24_41cbc8c0:name;
const unique T.Length48___unnamed_24_5419c914:name;
const unique T.Alignment48___unnamed_24_5419c914:name;
const unique T.MinimumAddress___unnamed_24_5419c914:name;
const unique T.MaximumAddress___unnamed_24_5419c914:name;
const unique T.Length___unnamed_24_67a5ff10:name;
const unique T.Alignment___unnamed_24_67a5ff10:name;
const unique T.MinimumAddress___unnamed_24_67a5ff10:name;
const unique T.MaximumAddress___unnamed_24_67a5ff10:name;
const unique T.Port___unnamed_24_72c3976e:name;
const unique T.Memory___unnamed_24_72c3976e:name;
const unique T.Interrupt___unnamed_24_72c3976e:name;
const unique T.Dma___unnamed_24_72c3976e:name;
const unique T.Generic___unnamed_24_72c3976e:name;
const unique T.DevicePrivate___unnamed_24_72c3976e:name;
const unique T.BusNumber___unnamed_24_72c3976e:name;
const unique T.ConfigData___unnamed_24_72c3976e:name;
const unique T.Memory40___unnamed_24_72c3976e:name;
const unique T.Memory48___unnamed_24_72c3976e:name;
const unique T.Memory64___unnamed_24_72c3976e:name;
const unique T.Length64___unnamed_24_a26050bb:name;
const unique T.Alignment64___unnamed_24_a26050bb:name;
const unique T.MinimumAddress___unnamed_24_a26050bb:name;
const unique T.MaximumAddress___unnamed_24_a26050bb:name;
const unique T.Length___unnamed_24_b8f476db:name;
const unique T.Alignment___unnamed_24_b8f476db:name;
const unique T.MinimumAddress___unnamed_24_b8f476db:name;
const unique T.MaximumAddress___unnamed_24_b8f476db:name;
const unique T.Length40___unnamed_24_d09044b4:name;
const unique T.Alignment40___unnamed_24_d09044b4:name;
const unique T.MinimumAddress___unnamed_24_d09044b4:name;
const unique T.MaximumAddress___unnamed_24_d09044b4:name;
const unique T.ReplaceIfExists___unnamed_2_46cc4597:name;
const unique T.AdvanceOnly___unnamed_2_46cc4597:name;
const unique T.__unnamed_16_e70c268b___unnamed_40_7218f704:name;
const unique T.Thread___unnamed_40_7218f704:name;
const unique T.AuxiliaryBuffer___unnamed_40_7218f704:name;
const unique T.__unnamed_12_b43e8de8___unnamed_40_7218f704:name;
const unique T.OriginalFileObject___unnamed_40_7218f704:name;
const unique T.ListEntry___unnamed_40_c55c9377:name;
const unique T.Wcb___unnamed_40_c55c9377:name;
const unique T.InitialPrivilegeSet___unnamed_44_5584090d:name;
const unique T.PrivilegeSet___unnamed_44_5584090d:name;
const unique T.Overlay___unnamed_48_cf99b13f:name;
const unique T.Apc___unnamed_48_cf99b13f:name;
const unique T.CompletionKey___unnamed_48_cf99b13f:name;
const unique T.PowerState___unnamed_4_069846fb:name;
const unique T.IdType___unnamed_4_224c32f4:name;
const unique T.Capabilities___unnamed_4_2de698da:name;
const unique T.__unnamed_4_c3479730___unnamed_4_3a2fdc5e:name;
const unique T.ContextAsUlong___unnamed_4_3a2fdc5e:name;
const unique T.Length___unnamed_4_3a4c1a13:name;
const unique T.__unnamed_2_46cc4597___unnamed_4_43913aa5:name;
const unique T.ClusterCount___unnamed_4_43913aa5:name;
const unique T.DeleteHandle___unnamed_4_43913aa5:name;
const unique T.UserApcRoutine___unnamed_4_4e8dd2ba:name;
const unique T.IssuingProcess___unnamed_4_4e8dd2ba:name;
const unique T.Srb___unnamed_4_52603077:name;
const unique T.Address___unnamed_4_52c594f7:name;
const unique T.CreatorBackTraceIndex___unnamed_4_52c594f7:name;
const unique T.Type___unnamed_4_5ca00198:name;
const unique T.__unnamed_1_29794256___unnamed_4_5ca00198:name;
const unique T.__unnamed_1_2ef8da39___unnamed_4_5ca00198:name;
const unique T.__unnamed_1_2dc63b48___unnamed_4_5ca00198:name;
const unique T.MasterIrp___unnamed_4_6ac6463c:name;
const unique T.IrpCount___unnamed_4_6ac6463c:name;
const unique T.SystemBuffer___unnamed_4_6ac6463c:name;
const unique T.OwnerCount___unnamed_4_6f9ac8e1:name;
const unique T.TableSize___unnamed_4_6f9ac8e1:name;
const unique T.PowerSequence___unnamed_4_7a02167b:name;
const unique T.SystemContext___unnamed_4_7d9d0c7e:name;
const unique T.SystemPowerStateContext___unnamed_4_7d9d0c7e:name;
const unique T.IoResourceRequirementList___unnamed_4_82f7a864:name;
const unique T.Length___unnamed_4_9aec220b:name;
const unique T.__unnamed_4_5ca00198___unnamed_4_a97c65a1:name;
const unique T.Lock___unnamed_4_a97c65a1:name;
const unique T.Reserved1___unnamed_4_c3479730:name;
const unique T.TargetSystemState___unnamed_4_c3479730:name;
const unique T.EffectiveSystemState___unnamed_4_c3479730:name;
const unique T.CurrentSystemState___unnamed_4_c3479730:name;
const unique T.IgnoreHibernationPath___unnamed_4_c3479730:name;
const unique T.PseudoTransition___unnamed_4_c3479730:name;
const unique T.Reserved2___unnamed_4_c3479730:name;
const unique T.Status___unnamed_4_d99b6e2b:name;
const unique T.Pointer___unnamed_4_d99b6e2b:name;
const unique T.CurrentStackLocation___unnamed_4_f19b65c1:name;
const unique T.PacketType___unnamed_4_f19b65c1:name;
const unique T.Type___unnamed_4_fa10fc16:name;
const unique T.SecurityInformation___unnamed_8_01efa60d:name;
const unique T.Length___unnamed_8_01efa60d:name;
const unique T.MinimumChannel___unnamed_8_08d4cef8:name;
const unique T.MaximumChannel___unnamed_8_08d4cef8:name;
const unique T.__unnamed_4_4e8dd2ba___unnamed_8_0a898c0c:name;
const unique T.UserApcContext___unnamed_8_0a898c0c:name;
const unique T.SecurityInformation___unnamed_8_1330f93a:name;
const unique T.SecurityDescriptor___unnamed_8_1330f93a:name;
const unique T.AsynchronousParameters___unnamed_8_181d0de9:name;
const unique T.AllocationSize___unnamed_8_181d0de9:name;
const unique T.Vpb___unnamed_8_4812764d:name;
const unique T.DeviceObject___unnamed_8_4812764d:name;
const unique T.Length___unnamed_8_559a91e6:name;
const unique T.FsInformationClass___unnamed_8_559a91e6:name;
const unique T.Length___unnamed_8_5845b309:name;
const unique T.FileInformationClass___unnamed_8_5845b309:name;
const unique T.LowPart___unnamed_8_58ee4a31:name;
const unique T.HighPart___unnamed_8_58ee4a31:name;
const unique T.AllocatedResources___unnamed_8_61acf4ce:name;
const unique T.AllocatedResourcesTranslated___unnamed_8_61acf4ce:name;
const unique T.DeviceTextType___unnamed_8_6acfee04:name;
const unique T.LocaleId___unnamed_8_6acfee04:name;
const unique T.Length___unnamed_8_7f26a9dd:name;
const unique T.CompletionFilter___unnamed_8_7f26a9dd:name;
const unique T.Vpb___unnamed_8_87add0bd:name;
const unique T.DeviceObject___unnamed_8_87add0bd:name;
const unique T.InPath___unnamed_8_b2773e4c:name;
const unique T.Reserved___unnamed_8_b2773e4c:name;
const unique T.Type___unnamed_8_b2773e4c:name;
const unique T.Length___unnamed_8_de890d4e:name;
const unique T.FsInformationClass___unnamed_8_de890d4e:name;
const unique T.LowPart___unnamed_8_ef9ba0d3:name;
const unique T.HighPart___unnamed_8_ef9ba0d3:name;

// Type declarations

const unique T.A1_CM_FULL_RESOURCE_DESCRIPTOR:name;
const unique T.A1_CM_PARTIAL_RESOURCE_DESCRIPTOR:name;
const unique T.A1_IO_RESOURCE_DESCRIPTOR:name;
const unique T.A1_IO_RESOURCE_LIST:name;
const unique T.A1_LUID_AND_ATTRIBUTES:name;
const unique T.A256UINT2:name;
const unique T.A28PFDRIVER_DISPATCH:name;
const unique T.A2UCHAR:name;
const unique T.A2UINT2:name;
const unique T.A32UINT2:name;
const unique T.A37CHAR:name;
const unique T.A3UCHAR:name;
const unique T.A3UINT4:name;
const unique T.A3_LUID_AND_ATTRIBUTES:name;
const unique T.A40CHAR:name;
const unique T.A4PVOID:name;
const unique T.A4UINT4:name;
const unique T.A5_DEVICE_POWER_STATE:name;
const unique T.A65CHAR:name;
const unique T.A75CHAR:name;
const unique T.A76CHAR:name;
const unique T.A7UINT2:name;
const unique T.A7_DEVICE_POWER_STATE:name;
const unique T.A83CHAR:name;
const unique T.A8UCHAR:name;
const unique T.A9UINT2:name;
const unique T.BUS_QUERY_ID_TYPE:name;
const unique T.CHAR:name;
const unique T.DEVICE_TEXT_TYPE:name;
const unique T.F0:name;
const unique T.F1:name;
const unique T.F10:name;
const unique T.F11:name;
const unique T.F12:name;
const unique T.F13:name;
const unique T.F14:name;
const unique T.F15:name;
const unique T.F16:name;
const unique T.F17:name;
const unique T.F18:name;
const unique T.F19:name;
const unique T.F2:name;
const unique T.F20:name;
const unique T.F21:name;
const unique T.F22:name;
const unique T.F23:name;
const unique T.F24:name;
const unique T.F25:name;
const unique T.F26:name;
const unique T.F27:name;
const unique T.F28:name;
const unique T.F29:name;
const unique T.F3:name;
const unique T.F30:name;
const unique T.F31:name;
const unique T.F32:name;
const unique T.F33:name;
const unique T.F34:name;
const unique T.F35:name;
const unique T.F36:name;
const unique T.F37:name;
const unique T.F38:name;
const unique T.F4:name;
const unique T.F5:name;
const unique T.F6:name;
const unique T.F7:name;
const unique T.F8:name;
const unique T.F9:name;
const unique T.FDRIVER_ADD_DEVICE:name;
const unique T.FDRIVER_CANCEL:name;
const unique T.FDRIVER_CONTROL:name;
const unique T.FDRIVER_DISPATCH:name;
const unique T.FDRIVER_INITIALIZE:name;
const unique T.FDRIVER_STARTIO:name;
const unique T.FDRIVER_UNLOAD:name;
const unique T.FFAST_IO_ACQUIRE_FILE:name;
const unique T.FFAST_IO_ACQUIRE_FOR_CCFLUSH:name;
const unique T.FFAST_IO_ACQUIRE_FOR_MOD_WRITE:name;
const unique T.FFAST_IO_CHECK_IF_POSSIBLE:name;
const unique T.FFAST_IO_DETACH_DEVICE:name;
const unique T.FFAST_IO_DEVICE_CONTROL:name;
const unique T.FFAST_IO_LOCK:name;
const unique T.FFAST_IO_MDL_READ:name;
const unique T.FFAST_IO_MDL_READ_COMPLETE:name;
const unique T.FFAST_IO_MDL_READ_COMPLETE_COMPRESSED:name;
const unique T.FFAST_IO_MDL_WRITE_COMPLETE:name;
const unique T.FFAST_IO_MDL_WRITE_COMPLETE_COMPRESSED:name;
const unique T.FFAST_IO_PREPARE_MDL_WRITE:name;
const unique T.FFAST_IO_QUERY_BASIC_INFO:name;
const unique T.FFAST_IO_QUERY_NETWORK_OPEN_INFO:name;
const unique T.FFAST_IO_QUERY_OPEN:name;
const unique T.FFAST_IO_QUERY_STANDARD_INFO:name;
const unique T.FFAST_IO_READ:name;
const unique T.FFAST_IO_READ_COMPRESSED:name;
const unique T.FFAST_IO_RELEASE_FILE:name;
const unique T.FFAST_IO_RELEASE_FOR_CCFLUSH:name;
const unique T.FFAST_IO_RELEASE_FOR_MOD_WRITE:name;
const unique T.FFAST_IO_UNLOCK_ALL:name;
const unique T.FFAST_IO_UNLOCK_ALL_BY_KEY:name;
const unique T.FFAST_IO_UNLOCK_SINGLE:name;
const unique T.FFAST_IO_WRITE:name;
const unique T.FFAST_IO_WRITE_COMPRESSED:name;
const unique T.FIO_COMPLETION_ROUTINE:name;
const unique T.FKDEFERRED_ROUTINE:name;
const unique T.INT2:name;
const unique T.INT4:name;
const unique T.INT8:name;
const unique T.PA2UINT2:name;
const unique T.PA37CHAR:name;
const unique T.PA40CHAR:name;
const unique T.PA4UINT4:name;
const unique T.PA65CHAR:name;
const unique T.PA75CHAR:name;
const unique T.PA76CHAR:name;
const unique T.PA7UINT2:name;
const unique T.PA83CHAR:name;
const unique T.PA9UINT2:name;
const unique T.PCHAR:name;
const unique T.PF19:name;
const unique T.PF21:name;
const unique T.PF23:name;
const unique T.PF24:name;
const unique T.PF25:name;
const unique T.PF33:name;
const unique T.PF34:name;
const unique T.PF35:name;
const unique T.PF36:name;
const unique T.PF37:name;
const unique T.PF38:name;
const unique T.PFDRIVER_ADD_DEVICE:name;
const unique T.PFDRIVER_CANCEL:name;
const unique T.PFDRIVER_CONTROL:name;
const unique T.PFDRIVER_DISPATCH:name;
const unique T.PFDRIVER_INITIALIZE:name;
const unique T.PFDRIVER_STARTIO:name;
const unique T.PFDRIVER_UNLOAD:name;
const unique T.PFFAST_IO_ACQUIRE_FILE:name;
const unique T.PFFAST_IO_ACQUIRE_FOR_CCFLUSH:name;
const unique T.PFFAST_IO_ACQUIRE_FOR_MOD_WRITE:name;
const unique T.PFFAST_IO_CHECK_IF_POSSIBLE:name;
const unique T.PFFAST_IO_DETACH_DEVICE:name;
const unique T.PFFAST_IO_DEVICE_CONTROL:name;
const unique T.PFFAST_IO_LOCK:name;
const unique T.PFFAST_IO_MDL_READ:name;
const unique T.PFFAST_IO_MDL_READ_COMPLETE:name;
const unique T.PFFAST_IO_MDL_READ_COMPLETE_COMPRESSED:name;
const unique T.PFFAST_IO_MDL_WRITE_COMPLETE:name;
const unique T.PFFAST_IO_MDL_WRITE_COMPLETE_COMPRESSED:name;
const unique T.PFFAST_IO_PREPARE_MDL_WRITE:name;
const unique T.PFFAST_IO_QUERY_BASIC_INFO:name;
const unique T.PFFAST_IO_QUERY_NETWORK_OPEN_INFO:name;
const unique T.PFFAST_IO_QUERY_OPEN:name;
const unique T.PFFAST_IO_QUERY_STANDARD_INFO:name;
const unique T.PFFAST_IO_READ:name;
const unique T.PFFAST_IO_READ_COMPRESSED:name;
const unique T.PFFAST_IO_RELEASE_FILE:name;
const unique T.PFFAST_IO_RELEASE_FOR_CCFLUSH:name;
const unique T.PFFAST_IO_RELEASE_FOR_MOD_WRITE:name;
const unique T.PFFAST_IO_UNLOCK_ALL:name;
const unique T.PFFAST_IO_UNLOCK_ALL_BY_KEY:name;
const unique T.PFFAST_IO_UNLOCK_SINGLE:name;
const unique T.PFFAST_IO_WRITE:name;
const unique T.PFFAST_IO_WRITE_COMPRESSED:name;
const unique T.PFIO_COMPLETION_ROUTINE:name;
const unique T.PFKDEFERRED_ROUTINE:name;
const unique T.PINT4:name;
const unique T.POWER_ACTION:name;
const unique T.PPCHAR:name;
const unique T.PPF24:name;
const unique T.PPPUINT2:name;
const unique T.PPP_DEVICE_OBJECT:name;
const unique T.PPUINT2:name;
const unique T.PPUINT4:name;
const unique T.PPVOID:name;
const unique T.PP_DEVICE_EXTENSION:name;
const unique T.PP_DEVICE_OBJECT:name;
const unique T.PP_DRIVER_OBJECT:name;
const unique T.PP_ERESOURCE:name;
const unique T.PP_FAST_MUTEX:name;
const unique T.PP_IO_REMOVE_LOCK:name;
const unique T.PP_LIST_ENTRY:name;
const unique T.PP_MDL:name;
const unique T.PP_UNICODE_STRING:name;
const unique T.PUCHAR:name;
const unique T.PUINT2:name;
const unique T.PUINT4:name;
const unique T.PVOID:name;
const unique T.PWMIGUIDREGINFO:name;
const unique T.P_ACCESS_STATE:name;
const unique T.P_CM_RESOURCE_LIST:name;
const unique T.P_COMPRESSED_DATA_INFO:name;
const unique T.P_DEVICE_CAPABILITIES:name;
const unique T.P_DEVICE_EXTENSION:name;
const unique T.P_DEVICE_OBJECT:name;
const unique T.P_DEVOBJ_EXTENSION:name;
const unique T.P_DRIVER_EXTENSION:name;
const unique T.P_DRIVER_OBJECT:name;
const unique T.P_EPROCESS:name;
const unique T.P_ERESOURCE:name;
const unique T.P_ETHREAD:name;
const unique T.P_FAST_IO_DISPATCH:name;
const unique T.P_FAST_MUTEX:name;
const unique T.P_FILE_BASIC_INFORMATION:name;
const unique T.P_FILE_GET_QUOTA_INFORMATION:name;
const unique T.P_FILE_NETWORK_OPEN_INFORMATION:name;
const unique T.P_FILE_OBJECT:name;
const unique T.P_FILE_STANDARD_INFORMATION:name;
const unique T.P_GLOBALS:name;
const unique T.P_GUID:name;
const unique T.P_INTERFACE:name;
const unique T.P_IO_COMPLETION_CONTEXT:name;
const unique T.P_IO_REMOVE_LOCK:name;
const unique T.P_IO_REMOVE_LOCK_TRACKING_BLOCK:name;
const unique T.P_IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T.P_IO_SECURITY_CONTEXT:name;
const unique T.P_IO_STACK_LOCATION:name;
const unique T.P_IO_STATUS_BLOCK:name;
const unique T.P_IO_TIMER:name;
const unique T.P_IRP:name;
const unique T.P_KAPC:name;
const unique T.P_KDPC:name;
const unique T.P_KEVENT:name;
const unique T.P_KEYBOARD_INPUT_DATA:name;
const unique T.P_KSEMAPHORE:name;
const unique T.P_KTHREAD:name;
const unique T.P_LARGE_INTEGER:name;
const unique T.P_LIST_ENTRY:name;
const unique T.P_MDL:name;
const unique T.P_OWNER_ENTRY:name;
const unique T.P_POOL_TYPE:name;
const unique T.P_PORT:name;
const unique T.P_POWER_SEQUENCE:name;
const unique T.P_SCSI_REQUEST_BLOCK:name;
const unique T.P_SECTION_OBJECT_POINTERS:name;
const unique T.P_SECURITY_QUALITY_OF_SERVICE:name;
const unique T.P_UNICODE_STRING:name;
const unique T.P_VPB:name;
const unique T.UCHAR:name;
const unique T.UINT2:name;
const unique T.UINT4:name;
const unique T.VOID:name;
const unique T.WMIENABLEDISABLECONTROL:name;
const unique T.WMIGUIDREGINFO:name;
const unique T._ACCESS_STATE:name;
const unique T._CM_FULL_RESOURCE_DESCRIPTOR:name;
const unique T._CM_PARTIAL_RESOURCE_DESCRIPTOR:name;
const unique T._CM_PARTIAL_RESOURCE_LIST:name;
const unique T._CM_RESOURCE_LIST:name;
const unique T._COMPRESSED_DATA_INFO:name;
const unique T._DEVICE_CAPABILITIES:name;
const unique T._DEVICE_EXTENSION:name;
const unique T._DEVICE_OBJECT:name;
const unique T._DEVICE_POWER_STATE:name;
const unique T._DEVICE_RELATION_TYPE:name;
const unique T._DEVICE_USAGE_NOTIFICATION_TYPE:name;
const unique T._DEVOBJ_EXTENSION:name;
const unique T._DISPATCHER_HEADER:name;
const unique T._DRIVER_EXTENSION:name;
const unique T._DRIVER_OBJECT:name;
const unique T._EPROCESS:name;
const unique T._ERESOURCE:name;
const unique T._ETHREAD:name;
const unique T._FAST_IO_DISPATCH:name;
const unique T._FAST_MUTEX:name;
const unique T._FILE_BASIC_INFORMATION:name;
const unique T._FILE_GET_QUOTA_INFORMATION:name;
const unique T._FILE_INFORMATION_CLASS:name;
const unique T._FILE_NETWORK_OPEN_INFORMATION:name;
const unique T._FILE_OBJECT:name;
const unique T._FILE_STANDARD_INFORMATION:name;
const unique T._FSINFOCLASS:name;
const unique T._GLOBALS:name;
const unique T._GUID:name;
const unique T._INITIAL_PRIVILEGE_SET:name;
const unique T._INTERFACE:name;
const unique T._INTERFACE_TYPE:name;
const unique T._IO_ALLOCATION_ACTION:name;
const unique T._IO_COMPLETION_CONTEXT:name;
const unique T._IO_REMOVE_LOCK:name;
const unique T._IO_REMOVE_LOCK_COMMON_BLOCK:name;
const unique T._IO_REMOVE_LOCK_DBG_BLOCK:name;
const unique T._IO_REMOVE_LOCK_TRACKING_BLOCK:name;
const unique T._IO_RESOURCE_DESCRIPTOR:name;
const unique T._IO_RESOURCE_LIST:name;
const unique T._IO_RESOURCE_REQUIREMENTS_LIST:name;
const unique T._IO_SECURITY_CONTEXT:name;
const unique T._IO_STACK_LOCATION:name;
const unique T._IO_STATUS_BLOCK:name;
const unique T._IO_TIMER:name;
const unique T._IRP:name;
const unique T._IRQ_DEVICE_POLICY:name;
const unique T._IRQ_PRIORITY:name;
const unique T._KAPC:name;
const unique T._KDEVICE_QUEUE:name;
const unique T._KDEVICE_QUEUE_ENTRY:name;
const unique T._KDPC:name;
const unique T._KEVENT:name;
const unique T._KEYBOARD_ATTRIBUTES:name;
const unique T._KEYBOARD_ID:name;
const unique T._KEYBOARD_INDICATOR_PARAMETERS:name;
const unique T._KEYBOARD_INPUT_DATA:name;
const unique T._KEYBOARD_TYPEMATIC_PARAMETERS:name;
const unique T._KSEMAPHORE:name;
const unique T._KTHREAD:name;
const unique T._LARGE_INTEGER:name;
const unique T._LIST_ENTRY:name;
const unique T._LUID:name;
const unique T._LUID_AND_ATTRIBUTES:name;
const unique T._MDL:name;
const unique T._OWNER_ENTRY:name;
const unique T._POOL_TYPE:name;
const unique T._PORT:name;
const unique T._POWER_SEQUENCE:name;
const unique T._POWER_STATE:name;
const unique T._POWER_STATE_TYPE:name;
const unique T._PRIVILEGE_SET:name;
const unique T._SCSI_REQUEST_BLOCK:name;
const unique T._SECTION_OBJECT_POINTERS:name;
const unique T._SECURITY_IMPERSONATION_LEVEL:name;
const unique T._SECURITY_QUALITY_OF_SERVICE:name;
const unique T._SECURITY_SUBJECT_CONTEXT:name;
const unique T._SYSTEM_POWER_STATE:name;
const unique T._SYSTEM_POWER_STATE_CONTEXT:name;
const unique T._UNICODE_STRING:name;
const unique T._VPB:name;
const unique T._WAIT_CONTEXT_BLOCK:name;
const unique T._WMILIB_CONTEXT:name;
const unique T.__unnamed_12_0d6a30de:name;
const unique T.__unnamed_12_17f5c211:name;
const unique T.__unnamed_12_1fb42e39:name;
const unique T.__unnamed_12_2a1563c6:name;
const unique T.__unnamed_12_31347272:name;
const unique T.__unnamed_12_429aadc0:name;
const unique T.__unnamed_12_4719de1a:name;
const unique T.__unnamed_12_4be56faa:name;
const unique T.__unnamed_12_5ce25b92:name;
const unique T.__unnamed_12_7a698b72:name;
const unique T.__unnamed_12_87c0de8d:name;
const unique T.__unnamed_12_98bfc55a:name;
const unique T.__unnamed_12_ab1bd9d7:name;
const unique T.__unnamed_12_b0429be9:name;
const unique T.__unnamed_12_b43e8de8:name;
const unique T.__unnamed_12_bfdb39ee:name;
const unique T.__unnamed_12_cd42b3c3:name;
const unique T.__unnamed_12_e668effc:name;
const unique T.__unnamed_12_e80d029e:name;
const unique T.__unnamed_16_07c0bcc5:name;
const unique T.__unnamed_16_29cb9f2f:name;
const unique T.__unnamed_16_30f11dbf:name;
const unique T.__unnamed_16_35034f68:name;
const unique T.__unnamed_16_487a9498:name;
const unique T.__unnamed_16_5f6a8844:name;
const unique T.__unnamed_16_7177b9f3:name;
const unique T.__unnamed_16_88e91ef6:name;
const unique T.__unnamed_16_8c506c98:name;
const unique T.__unnamed_16_9ac2e5f8:name;
const unique T.__unnamed_16_b93842ad:name;
const unique T.__unnamed_16_b9c62eab:name;
const unique T.__unnamed_16_bb584060:name;
const unique T.__unnamed_16_dba55c7c:name;
const unique T.__unnamed_16_e70c268b:name;
const unique T.__unnamed_16_e734d694:name;
const unique T.__unnamed_16_eac6dbea:name;
const unique T.__unnamed_16_f6cae4c2:name;
const unique T.__unnamed_16_fe36e4f4:name;
const unique T.__unnamed_1_29794256:name;
const unique T.__unnamed_1_2dc63b48:name;
const unique T.__unnamed_1_2ef8da39:name;
const unique T.__unnamed_1_faa7dc71:name;
const unique T.__unnamed_20_f4d2e6d8:name;
const unique T.__unnamed_24_41cbc8c0:name;
const unique T.__unnamed_24_5419c914:name;
const unique T.__unnamed_24_67a5ff10:name;
const unique T.__unnamed_24_72c3976e:name;
const unique T.__unnamed_24_a26050bb:name;
const unique T.__unnamed_24_b8f476db:name;
const unique T.__unnamed_24_d09044b4:name;
const unique T.__unnamed_2_46cc4597:name;
const unique T.__unnamed_40_7218f704:name;
const unique T.__unnamed_40_c55c9377:name;
const unique T.__unnamed_44_5584090d:name;
const unique T.__unnamed_48_cf99b13f:name;
const unique T.__unnamed_4_069846fb:name;
const unique T.__unnamed_4_224c32f4:name;
const unique T.__unnamed_4_2de698da:name;
const unique T.__unnamed_4_3a2fdc5e:name;
const unique T.__unnamed_4_3a4c1a13:name;
const unique T.__unnamed_4_43913aa5:name;
const unique T.__unnamed_4_4e8dd2ba:name;
const unique T.__unnamed_4_52603077:name;
const unique T.__unnamed_4_52c594f7:name;
const unique T.__unnamed_4_5ca00198:name;
const unique T.__unnamed_4_6ac6463c:name;
const unique T.__unnamed_4_6f9ac8e1:name;
const unique T.__unnamed_4_7a02167b:name;
const unique T.__unnamed_4_7d9d0c7e:name;
const unique T.__unnamed_4_82f7a864:name;
const unique T.__unnamed_4_9aec220b:name;
const unique T.__unnamed_4_a97c65a1:name;
const unique T.__unnamed_4_c3479730:name;
const unique T.__unnamed_4_d99b6e2b:name;
const unique T.__unnamed_4_f19b65c1:name;
const unique T.__unnamed_4_fa10fc16:name;
const unique T.__unnamed_8_01efa60d:name;
const unique T.__unnamed_8_08d4cef8:name;
const unique T.__unnamed_8_0a898c0c:name;
const unique T.__unnamed_8_1330f93a:name;
const unique T.__unnamed_8_181d0de9:name;
const unique T.__unnamed_8_4812764d:name;
const unique T.__unnamed_8_559a91e6:name;
const unique T.__unnamed_8_5845b309:name;
const unique T.__unnamed_8_58ee4a31:name;
const unique T.__unnamed_8_61acf4ce:name;
const unique T.__unnamed_8_6acfee04:name;
const unique T.__unnamed_8_7f26a9dd:name;
const unique T.__unnamed_8_87add0bd:name;
const unique T.__unnamed_8_b2773e4c:name;
const unique T.__unnamed_8_de890d4e:name;
const unique T.__unnamed_8_ef9ba0d3:name;

function Abandoned___unnamed_1_29794256(int) returns (int);
function Abandoned___unnamed_1_29794256Inv(int) returns (int);
function _S_Abandoned___unnamed_1_29794256([int]bool) returns ([int]bool);
function _S_Abandoned___unnamed_1_29794256Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Abandoned___unnamed_1_29794256Inv(Abandoned___unnamed_1_29794256(x))} Abandoned___unnamed_1_29794256Inv(Abandoned___unnamed_1_29794256(x)) == x);
axiom (forall x:int :: {Abandoned___unnamed_1_29794256Inv(x)} Abandoned___unnamed_1_29794256(Abandoned___unnamed_1_29794256Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Abandoned___unnamed_1_29794256(S)[x]} _S_Abandoned___unnamed_1_29794256(S)[x] <==> S[Abandoned___unnamed_1_29794256Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Abandoned___unnamed_1_29794256Inv(S)[x]} _S_Abandoned___unnamed_1_29794256Inv(S)[x] <==> S[Abandoned___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Abandoned___unnamed_1_29794256(S)} S[x] ==> _S_Abandoned___unnamed_1_29794256(S)[Abandoned___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Abandoned___unnamed_1_29794256Inv(S)} S[x] ==> _S_Abandoned___unnamed_1_29794256Inv(S)[Abandoned___unnamed_1_29794256Inv(x)]);
        
axiom (forall x:int :: {Abandoned___unnamed_1_29794256(x)} Abandoned___unnamed_1_29794256(x) == x + 0);
axiom (forall x:int :: {Abandoned___unnamed_1_29794256Inv(x)} Abandoned___unnamed_1_29794256Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Abandoned___unnamed_1_29794256Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Abandoned___unnamed_1_29794256Inv(x));
function Absolute___unnamed_1_29794256(int) returns (int);
function Absolute___unnamed_1_29794256Inv(int) returns (int);
function _S_Absolute___unnamed_1_29794256([int]bool) returns ([int]bool);
function _S_Absolute___unnamed_1_29794256Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Absolute___unnamed_1_29794256Inv(Absolute___unnamed_1_29794256(x))} Absolute___unnamed_1_29794256Inv(Absolute___unnamed_1_29794256(x)) == x);
axiom (forall x:int :: {Absolute___unnamed_1_29794256Inv(x)} Absolute___unnamed_1_29794256(Absolute___unnamed_1_29794256Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Absolute___unnamed_1_29794256(S)[x]} _S_Absolute___unnamed_1_29794256(S)[x] <==> S[Absolute___unnamed_1_29794256Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Absolute___unnamed_1_29794256Inv(S)[x]} _S_Absolute___unnamed_1_29794256Inv(S)[x] <==> S[Absolute___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Absolute___unnamed_1_29794256(S)} S[x] ==> _S_Absolute___unnamed_1_29794256(S)[Absolute___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Absolute___unnamed_1_29794256Inv(S)} S[x] ==> _S_Absolute___unnamed_1_29794256Inv(S)[Absolute___unnamed_1_29794256Inv(x)]);
        
axiom (forall x:int :: {Absolute___unnamed_1_29794256(x)} Absolute___unnamed_1_29794256(x) == x + 0);
axiom (forall x:int :: {Absolute___unnamed_1_29794256Inv(x)} Absolute___unnamed_1_29794256Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Absolute___unnamed_1_29794256Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Absolute___unnamed_1_29794256Inv(x));
function AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(x))} AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(S)[AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(x)} AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 16);
axiom (forall x:int :: {AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 16);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1) == AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 16)} MINUS_LEFT_PTR(x, 1, 16) == AllocateTag__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function AllowDisable__DEVICE_EXTENSION(int) returns (int);
function AllowDisable__DEVICE_EXTENSIONInv(int) returns (int);
function _S_AllowDisable__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_AllowDisable__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {AllowDisable__DEVICE_EXTENSIONInv(AllowDisable__DEVICE_EXTENSION(x))} AllowDisable__DEVICE_EXTENSIONInv(AllowDisable__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {AllowDisable__DEVICE_EXTENSIONInv(x)} AllowDisable__DEVICE_EXTENSION(AllowDisable__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_AllowDisable__DEVICE_EXTENSION(S)[x]} _S_AllowDisable__DEVICE_EXTENSION(S)[x] <==> S[AllowDisable__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_AllowDisable__DEVICE_EXTENSIONInv(S)[x]} _S_AllowDisable__DEVICE_EXTENSIONInv(S)[x] <==> S[AllowDisable__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_AllowDisable__DEVICE_EXTENSION(S)} S[x] ==> _S_AllowDisable__DEVICE_EXTENSION(S)[AllowDisable__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_AllowDisable__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_AllowDisable__DEVICE_EXTENSIONInv(S)[AllowDisable__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {AllowDisable__DEVICE_EXTENSION(x)} AllowDisable__DEVICE_EXTENSION(x) == x + 106);
axiom (forall x:int :: {AllowDisable__DEVICE_EXTENSIONInv(x)} AllowDisable__DEVICE_EXTENSIONInv(x) == x - 106);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 106, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 106, 1) == AllowDisable__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 106)} MINUS_LEFT_PTR(x, 1, 106) == AllowDisable__DEVICE_EXTENSIONInv(x));
function BaseClassName__GLOBALS(int) returns (int);
function BaseClassName__GLOBALSInv(int) returns (int);
function _S_BaseClassName__GLOBALS([int]bool) returns ([int]bool);
function _S_BaseClassName__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {BaseClassName__GLOBALSInv(BaseClassName__GLOBALS(x))} BaseClassName__GLOBALSInv(BaseClassName__GLOBALS(x)) == x);
axiom (forall x:int :: {BaseClassName__GLOBALSInv(x)} BaseClassName__GLOBALS(BaseClassName__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_BaseClassName__GLOBALS(S)[x]} _S_BaseClassName__GLOBALS(S)[x] <==> S[BaseClassName__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_BaseClassName__GLOBALSInv(S)[x]} _S_BaseClassName__GLOBALSInv(S)[x] <==> S[BaseClassName__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_BaseClassName__GLOBALS(S)} S[x] ==> _S_BaseClassName__GLOBALS(S)[BaseClassName__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_BaseClassName__GLOBALSInv(S)} S[x] ==> _S_BaseClassName__GLOBALSInv(S)[BaseClassName__GLOBALSInv(x)]);
        
axiom (forall x:int :: {BaseClassName__GLOBALS(x)} BaseClassName__GLOBALS(x) == x + 368);
axiom (forall x:int :: {BaseClassName__GLOBALSInv(x)} BaseClassName__GLOBALSInv(x) == x - 368);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 368, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 368, 1) == BaseClassName__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 368)} MINUS_LEFT_PTR(x, 1, 368) == BaseClassName__GLOBALSInv(x));
function Blink__LIST_ENTRY(int) returns (int);
function Blink__LIST_ENTRYInv(int) returns (int);
function _S_Blink__LIST_ENTRY([int]bool) returns ([int]bool);
function _S_Blink__LIST_ENTRYInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Blink__LIST_ENTRYInv(Blink__LIST_ENTRY(x))} Blink__LIST_ENTRYInv(Blink__LIST_ENTRY(x)) == x);
axiom (forall x:int :: {Blink__LIST_ENTRYInv(x)} Blink__LIST_ENTRY(Blink__LIST_ENTRYInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Blink__LIST_ENTRY(S)[x]} _S_Blink__LIST_ENTRY(S)[x] <==> S[Blink__LIST_ENTRYInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Blink__LIST_ENTRYInv(S)[x]} _S_Blink__LIST_ENTRYInv(S)[x] <==> S[Blink__LIST_ENTRY(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Blink__LIST_ENTRY(S)} S[x] ==> _S_Blink__LIST_ENTRY(S)[Blink__LIST_ENTRY(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Blink__LIST_ENTRYInv(S)} S[x] ==> _S_Blink__LIST_ENTRYInv(S)[Blink__LIST_ENTRYInv(x)]);
        
axiom (forall x:int :: {Blink__LIST_ENTRY(x)} Blink__LIST_ENTRY(x) == x + 4);
axiom (forall x:int :: {Blink__LIST_ENTRYInv(x)} Blink__LIST_ENTRYInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == Blink__LIST_ENTRYInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == Blink__LIST_ENTRYInv(x));
function Blocks__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(Blocks__IO_REMOVE_LOCK_DBG_BLOCK(x))} Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(Blocks__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Blocks__IO_REMOVE_LOCK_DBG_BLOCK(Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Blocks__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[Blocks__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCK(S)[Blocks__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {Blocks__IO_REMOVE_LOCK_DBG_BLOCK(x)} Blocks__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 56);
axiom (forall x:int :: {Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 56);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 56, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 56, 1) == Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 56)} MINUS_LEFT_PTR(x, 1, 56) == Blocks__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function Buffer__UNICODE_STRING(int) returns (int);
function Buffer__UNICODE_STRINGInv(int) returns (int);
function _S_Buffer__UNICODE_STRING([int]bool) returns ([int]bool);
function _S_Buffer__UNICODE_STRINGInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Buffer__UNICODE_STRINGInv(Buffer__UNICODE_STRING(x))} Buffer__UNICODE_STRINGInv(Buffer__UNICODE_STRING(x)) == x);
axiom (forall x:int :: {Buffer__UNICODE_STRINGInv(x)} Buffer__UNICODE_STRING(Buffer__UNICODE_STRINGInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Buffer__UNICODE_STRING(S)[x]} _S_Buffer__UNICODE_STRING(S)[x] <==> S[Buffer__UNICODE_STRINGInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Buffer__UNICODE_STRINGInv(S)[x]} _S_Buffer__UNICODE_STRINGInv(S)[x] <==> S[Buffer__UNICODE_STRING(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Buffer__UNICODE_STRING(S)} S[x] ==> _S_Buffer__UNICODE_STRING(S)[Buffer__UNICODE_STRING(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Buffer__UNICODE_STRINGInv(S)} S[x] ==> _S_Buffer__UNICODE_STRINGInv(S)[Buffer__UNICODE_STRINGInv(x)]);
        
axiom (forall x:int :: {Buffer__UNICODE_STRING(x)} Buffer__UNICODE_STRING(x) == x + 4);
axiom (forall x:int :: {Buffer__UNICODE_STRINGInv(x)} Buffer__UNICODE_STRINGInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == Buffer__UNICODE_STRINGInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == Buffer__UNICODE_STRINGInv(x));
function Common__IO_REMOVE_LOCK(int) returns (int);
function Common__IO_REMOVE_LOCKInv(int) returns (int);
function _S_Common__IO_REMOVE_LOCK([int]bool) returns ([int]bool);
function _S_Common__IO_REMOVE_LOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Common__IO_REMOVE_LOCKInv(Common__IO_REMOVE_LOCK(x))} Common__IO_REMOVE_LOCKInv(Common__IO_REMOVE_LOCK(x)) == x);
axiom (forall x:int :: {Common__IO_REMOVE_LOCKInv(x)} Common__IO_REMOVE_LOCK(Common__IO_REMOVE_LOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Common__IO_REMOVE_LOCK(S)[x]} _S_Common__IO_REMOVE_LOCK(S)[x] <==> S[Common__IO_REMOVE_LOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Common__IO_REMOVE_LOCKInv(S)[x]} _S_Common__IO_REMOVE_LOCKInv(S)[x] <==> S[Common__IO_REMOVE_LOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Common__IO_REMOVE_LOCK(S)} S[x] ==> _S_Common__IO_REMOVE_LOCK(S)[Common__IO_REMOVE_LOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Common__IO_REMOVE_LOCKInv(S)} S[x] ==> _S_Common__IO_REMOVE_LOCKInv(S)[Common__IO_REMOVE_LOCKInv(x)]);
        
axiom (forall x:int :: {Common__IO_REMOVE_LOCK(x)} Common__IO_REMOVE_LOCK(x) == x + 0);
axiom (forall x:int :: {Common__IO_REMOVE_LOCKInv(x)} Common__IO_REMOVE_LOCKInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Common__IO_REMOVE_LOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Common__IO_REMOVE_LOCKInv(x));
function ConnectOneClassToOnePort__GLOBALS(int) returns (int);
function ConnectOneClassToOnePort__GLOBALSInv(int) returns (int);
function _S_ConnectOneClassToOnePort__GLOBALS([int]bool) returns ([int]bool);
function _S_ConnectOneClassToOnePort__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {ConnectOneClassToOnePort__GLOBALSInv(ConnectOneClassToOnePort__GLOBALS(x))} ConnectOneClassToOnePort__GLOBALSInv(ConnectOneClassToOnePort__GLOBALS(x)) == x);
axiom (forall x:int :: {ConnectOneClassToOnePort__GLOBALSInv(x)} ConnectOneClassToOnePort__GLOBALS(ConnectOneClassToOnePort__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_ConnectOneClassToOnePort__GLOBALS(S)[x]} _S_ConnectOneClassToOnePort__GLOBALS(S)[x] <==> S[ConnectOneClassToOnePort__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_ConnectOneClassToOnePort__GLOBALSInv(S)[x]} _S_ConnectOneClassToOnePort__GLOBALSInv(S)[x] <==> S[ConnectOneClassToOnePort__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ConnectOneClassToOnePort__GLOBALS(S)} S[x] ==> _S_ConnectOneClassToOnePort__GLOBALS(S)[ConnectOneClassToOnePort__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ConnectOneClassToOnePort__GLOBALSInv(S)} S[x] ==> _S_ConnectOneClassToOnePort__GLOBALSInv(S)[ConnectOneClassToOnePort__GLOBALSInv(x)]);
        
axiom (forall x:int :: {ConnectOneClassToOnePort__GLOBALS(x)} ConnectOneClassToOnePort__GLOBALS(x) == x + 56);
axiom (forall x:int :: {ConnectOneClassToOnePort__GLOBALSInv(x)} ConnectOneClassToOnePort__GLOBALSInv(x) == x - 56);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 56, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 56, 1) == ConnectOneClassToOnePort__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 56)} MINUS_LEFT_PTR(x, 1, 56) == ConnectOneClassToOnePort__GLOBALSInv(x));
function DataIn__DEVICE_EXTENSION(int) returns (int);
function DataIn__DEVICE_EXTENSIONInv(int) returns (int);
function _S_DataIn__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_DataIn__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {DataIn__DEVICE_EXTENSIONInv(DataIn__DEVICE_EXTENSION(x))} DataIn__DEVICE_EXTENSIONInv(DataIn__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {DataIn__DEVICE_EXTENSIONInv(x)} DataIn__DEVICE_EXTENSION(DataIn__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_DataIn__DEVICE_EXTENSION(S)[x]} _S_DataIn__DEVICE_EXTENSION(S)[x] <==> S[DataIn__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_DataIn__DEVICE_EXTENSIONInv(S)[x]} _S_DataIn__DEVICE_EXTENSIONInv(S)[x] <==> S[DataIn__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DataIn__DEVICE_EXTENSION(S)} S[x] ==> _S_DataIn__DEVICE_EXTENSION(S)[DataIn__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DataIn__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_DataIn__DEVICE_EXTENSIONInv(S)[DataIn__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {DataIn__DEVICE_EXTENSION(x)} DataIn__DEVICE_EXTENSION(x) == x + 132);
axiom (forall x:int :: {DataIn__DEVICE_EXTENSIONInv(x)} DataIn__DEVICE_EXTENSIONInv(x) == x - 132);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 132, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 132, 1) == DataIn__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 132)} MINUS_LEFT_PTR(x, 1, 132) == DataIn__DEVICE_EXTENSIONInv(x));
function DataOut__DEVICE_EXTENSION(int) returns (int);
function DataOut__DEVICE_EXTENSIONInv(int) returns (int);
function _S_DataOut__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_DataOut__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {DataOut__DEVICE_EXTENSIONInv(DataOut__DEVICE_EXTENSION(x))} DataOut__DEVICE_EXTENSIONInv(DataOut__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {DataOut__DEVICE_EXTENSIONInv(x)} DataOut__DEVICE_EXTENSION(DataOut__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_DataOut__DEVICE_EXTENSION(S)[x]} _S_DataOut__DEVICE_EXTENSION(S)[x] <==> S[DataOut__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_DataOut__DEVICE_EXTENSIONInv(S)[x]} _S_DataOut__DEVICE_EXTENSIONInv(S)[x] <==> S[DataOut__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DataOut__DEVICE_EXTENSION(S)} S[x] ==> _S_DataOut__DEVICE_EXTENSION(S)[DataOut__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DataOut__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_DataOut__DEVICE_EXTENSIONInv(S)[DataOut__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {DataOut__DEVICE_EXTENSION(x)} DataOut__DEVICE_EXTENSION(x) == x + 136);
axiom (forall x:int :: {DataOut__DEVICE_EXTENSIONInv(x)} DataOut__DEVICE_EXTENSIONInv(x) == x - 136);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 136, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 136, 1) == DataOut__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 136)} MINUS_LEFT_PTR(x, 1, 136) == DataOut__DEVICE_EXTENSIONInv(x));
function Dbg__IO_REMOVE_LOCK(int) returns (int);
function Dbg__IO_REMOVE_LOCKInv(int) returns (int);
function _S_Dbg__IO_REMOVE_LOCK([int]bool) returns ([int]bool);
function _S_Dbg__IO_REMOVE_LOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Dbg__IO_REMOVE_LOCKInv(Dbg__IO_REMOVE_LOCK(x))} Dbg__IO_REMOVE_LOCKInv(Dbg__IO_REMOVE_LOCK(x)) == x);
axiom (forall x:int :: {Dbg__IO_REMOVE_LOCKInv(x)} Dbg__IO_REMOVE_LOCK(Dbg__IO_REMOVE_LOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Dbg__IO_REMOVE_LOCK(S)[x]} _S_Dbg__IO_REMOVE_LOCK(S)[x] <==> S[Dbg__IO_REMOVE_LOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Dbg__IO_REMOVE_LOCKInv(S)[x]} _S_Dbg__IO_REMOVE_LOCKInv(S)[x] <==> S[Dbg__IO_REMOVE_LOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Dbg__IO_REMOVE_LOCK(S)} S[x] ==> _S_Dbg__IO_REMOVE_LOCK(S)[Dbg__IO_REMOVE_LOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Dbg__IO_REMOVE_LOCKInv(S)} S[x] ==> _S_Dbg__IO_REMOVE_LOCKInv(S)[Dbg__IO_REMOVE_LOCKInv(x)]);
        
axiom (forall x:int :: {Dbg__IO_REMOVE_LOCK(x)} Dbg__IO_REMOVE_LOCK(x) == x + 24);
axiom (forall x:int :: {Dbg__IO_REMOVE_LOCKInv(x)} Dbg__IO_REMOVE_LOCKInv(x) == x - 24);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 24, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 24, 1) == Dbg__IO_REMOVE_LOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 24)} MINUS_LEFT_PTR(x, 1, 24) == Dbg__IO_REMOVE_LOCKInv(x));
function DebugActive___unnamed_1_2dc63b48(int) returns (int);
function DebugActive___unnamed_1_2dc63b48Inv(int) returns (int);
function _S_DebugActive___unnamed_1_2dc63b48([int]bool) returns ([int]bool);
function _S_DebugActive___unnamed_1_2dc63b48Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {DebugActive___unnamed_1_2dc63b48Inv(DebugActive___unnamed_1_2dc63b48(x))} DebugActive___unnamed_1_2dc63b48Inv(DebugActive___unnamed_1_2dc63b48(x)) == x);
axiom (forall x:int :: {DebugActive___unnamed_1_2dc63b48Inv(x)} DebugActive___unnamed_1_2dc63b48(DebugActive___unnamed_1_2dc63b48Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_DebugActive___unnamed_1_2dc63b48(S)[x]} _S_DebugActive___unnamed_1_2dc63b48(S)[x] <==> S[DebugActive___unnamed_1_2dc63b48Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_DebugActive___unnamed_1_2dc63b48Inv(S)[x]} _S_DebugActive___unnamed_1_2dc63b48Inv(S)[x] <==> S[DebugActive___unnamed_1_2dc63b48(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DebugActive___unnamed_1_2dc63b48(S)} S[x] ==> _S_DebugActive___unnamed_1_2dc63b48(S)[DebugActive___unnamed_1_2dc63b48(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DebugActive___unnamed_1_2dc63b48Inv(S)} S[x] ==> _S_DebugActive___unnamed_1_2dc63b48Inv(S)[DebugActive___unnamed_1_2dc63b48Inv(x)]);
        
axiom (forall x:int :: {DebugActive___unnamed_1_2dc63b48(x)} DebugActive___unnamed_1_2dc63b48(x) == x + 0);
axiom (forall x:int :: {DebugActive___unnamed_1_2dc63b48Inv(x)} DebugActive___unnamed_1_2dc63b48Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == DebugActive___unnamed_1_2dc63b48Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == DebugActive___unnamed_1_2dc63b48Inv(x));
function Delay__KEYBOARD_TYPEMATIC_PARAMETERS(int) returns (int);
function Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(int) returns (int);
function _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERS([int]bool) returns ([int]bool);
function _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(Delay__KEYBOARD_TYPEMATIC_PARAMETERS(x))} Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(Delay__KEYBOARD_TYPEMATIC_PARAMETERS(x)) == x);
axiom (forall x:int :: {Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)} Delay__KEYBOARD_TYPEMATIC_PARAMETERS(Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Delay__KEYBOARD_TYPEMATIC_PARAMETERS(S)[x]} _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERS(S)[x] <==> S[Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[x]} _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[x] <==> S[Delay__KEYBOARD_TYPEMATIC_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERS(S)} S[x] ==> _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERS(S)[Delay__KEYBOARD_TYPEMATIC_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)} S[x] ==> _S_Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)]);
        
axiom (forall x:int :: {Delay__KEYBOARD_TYPEMATIC_PARAMETERS(x)} Delay__KEYBOARD_TYPEMATIC_PARAMETERS(x) == x + 4);
axiom (forall x:int :: {Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)} Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == Delay__KEYBOARD_TYPEMATIC_PARAMETERSInv(x));
function DeviceExtension__DEVICE_OBJECT(int) returns (int);
function DeviceExtension__DEVICE_OBJECTInv(int) returns (int);
function _S_DeviceExtension__DEVICE_OBJECT([int]bool) returns ([int]bool);
function _S_DeviceExtension__DEVICE_OBJECTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {DeviceExtension__DEVICE_OBJECTInv(DeviceExtension__DEVICE_OBJECT(x))} DeviceExtension__DEVICE_OBJECTInv(DeviceExtension__DEVICE_OBJECT(x)) == x);
axiom (forall x:int :: {DeviceExtension__DEVICE_OBJECTInv(x)} DeviceExtension__DEVICE_OBJECT(DeviceExtension__DEVICE_OBJECTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_DeviceExtension__DEVICE_OBJECT(S)[x]} _S_DeviceExtension__DEVICE_OBJECT(S)[x] <==> S[DeviceExtension__DEVICE_OBJECTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_DeviceExtension__DEVICE_OBJECTInv(S)[x]} _S_DeviceExtension__DEVICE_OBJECTInv(S)[x] <==> S[DeviceExtension__DEVICE_OBJECT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DeviceExtension__DEVICE_OBJECT(S)} S[x] ==> _S_DeviceExtension__DEVICE_OBJECT(S)[DeviceExtension__DEVICE_OBJECT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DeviceExtension__DEVICE_OBJECTInv(S)} S[x] ==> _S_DeviceExtension__DEVICE_OBJECTInv(S)[DeviceExtension__DEVICE_OBJECTInv(x)]);
        
axiom (forall x:int :: {DeviceExtension__DEVICE_OBJECT(x)} DeviceExtension__DEVICE_OBJECT(x) == x + 40);
axiom (forall x:int :: {DeviceExtension__DEVICE_OBJECTInv(x)} DeviceExtension__DEVICE_OBJECTInv(x) == x - 40);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 40, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 40, 1) == DeviceExtension__DEVICE_OBJECTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 40)} MINUS_LEFT_PTR(x, 1, 40) == DeviceExtension__DEVICE_OBJECTInv(x));
function DeviceState__DEVICE_EXTENSION(int) returns (int);
function DeviceState__DEVICE_EXTENSIONInv(int) returns (int);
function _S_DeviceState__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_DeviceState__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {DeviceState__DEVICE_EXTENSIONInv(DeviceState__DEVICE_EXTENSION(x))} DeviceState__DEVICE_EXTENSIONInv(DeviceState__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {DeviceState__DEVICE_EXTENSIONInv(x)} DeviceState__DEVICE_EXTENSION(DeviceState__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_DeviceState__DEVICE_EXTENSION(S)[x]} _S_DeviceState__DEVICE_EXTENSION(S)[x] <==> S[DeviceState__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_DeviceState__DEVICE_EXTENSIONInv(S)[x]} _S_DeviceState__DEVICE_EXTENSIONInv(S)[x] <==> S[DeviceState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DeviceState__DEVICE_EXTENSION(S)} S[x] ==> _S_DeviceState__DEVICE_EXTENSION(S)[DeviceState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DeviceState__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_DeviceState__DEVICE_EXTENSIONInv(S)[DeviceState__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {DeviceState__DEVICE_EXTENSION(x)} DeviceState__DEVICE_EXTENSION(x) == x + 188);
axiom (forall x:int :: {DeviceState__DEVICE_EXTENSIONInv(x)} DeviceState__DEVICE_EXTENSIONInv(x) == x - 188);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 188, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 188, 1) == DeviceState__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 188)} MINUS_LEFT_PTR(x, 1, 188) == DeviceState__DEVICE_EXTENSIONInv(x));
function DpcActive___unnamed_1_2dc63b48(int) returns (int);
function DpcActive___unnamed_1_2dc63b48Inv(int) returns (int);
function _S_DpcActive___unnamed_1_2dc63b48([int]bool) returns ([int]bool);
function _S_DpcActive___unnamed_1_2dc63b48Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {DpcActive___unnamed_1_2dc63b48Inv(DpcActive___unnamed_1_2dc63b48(x))} DpcActive___unnamed_1_2dc63b48Inv(DpcActive___unnamed_1_2dc63b48(x)) == x);
axiom (forall x:int :: {DpcActive___unnamed_1_2dc63b48Inv(x)} DpcActive___unnamed_1_2dc63b48(DpcActive___unnamed_1_2dc63b48Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_DpcActive___unnamed_1_2dc63b48(S)[x]} _S_DpcActive___unnamed_1_2dc63b48(S)[x] <==> S[DpcActive___unnamed_1_2dc63b48Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_DpcActive___unnamed_1_2dc63b48Inv(S)[x]} _S_DpcActive___unnamed_1_2dc63b48Inv(S)[x] <==> S[DpcActive___unnamed_1_2dc63b48(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DpcActive___unnamed_1_2dc63b48(S)} S[x] ==> _S_DpcActive___unnamed_1_2dc63b48(S)[DpcActive___unnamed_1_2dc63b48(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_DpcActive___unnamed_1_2dc63b48Inv(S)} S[x] ==> _S_DpcActive___unnamed_1_2dc63b48Inv(S)[DpcActive___unnamed_1_2dc63b48Inv(x)]);
        
axiom (forall x:int :: {DpcActive___unnamed_1_2dc63b48(x)} DpcActive___unnamed_1_2dc63b48(x) == x + 0);
axiom (forall x:int :: {DpcActive___unnamed_1_2dc63b48Inv(x)} DpcActive___unnamed_1_2dc63b48Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == DpcActive___unnamed_1_2dc63b48Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == DpcActive___unnamed_1_2dc63b48Inv(x));
function Enabled__DEVICE_EXTENSION(int) returns (int);
function Enabled__DEVICE_EXTENSIONInv(int) returns (int);
function _S_Enabled__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_Enabled__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Enabled__DEVICE_EXTENSIONInv(Enabled__DEVICE_EXTENSION(x))} Enabled__DEVICE_EXTENSIONInv(Enabled__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {Enabled__DEVICE_EXTENSIONInv(x)} Enabled__DEVICE_EXTENSION(Enabled__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Enabled__DEVICE_EXTENSION(S)[x]} _S_Enabled__DEVICE_EXTENSION(S)[x] <==> S[Enabled__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Enabled__DEVICE_EXTENSIONInv(S)[x]} _S_Enabled__DEVICE_EXTENSIONInv(S)[x] <==> S[Enabled__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Enabled__DEVICE_EXTENSION(S)} S[x] ==> _S_Enabled__DEVICE_EXTENSION(S)[Enabled__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Enabled__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_Enabled__DEVICE_EXTENSIONInv(S)[Enabled__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {Enabled__DEVICE_EXTENSION(x)} Enabled__DEVICE_EXTENSION(x) == x + 284);
axiom (forall x:int :: {Enabled__DEVICE_EXTENSIONInv(x)} Enabled__DEVICE_EXTENSIONInv(x) == x - 284);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 284, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 284, 1) == Enabled__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 284)} MINUS_LEFT_PTR(x, 1, 284) == Enabled__DEVICE_EXTENSIONInv(x));
function ExecuteWmiMethod__WMILIB_CONTEXT(int) returns (int);
function ExecuteWmiMethod__WMILIB_CONTEXTInv(int) returns (int);
function _S_ExecuteWmiMethod__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_ExecuteWmiMethod__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {ExecuteWmiMethod__WMILIB_CONTEXTInv(ExecuteWmiMethod__WMILIB_CONTEXT(x))} ExecuteWmiMethod__WMILIB_CONTEXTInv(ExecuteWmiMethod__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {ExecuteWmiMethod__WMILIB_CONTEXTInv(x)} ExecuteWmiMethod__WMILIB_CONTEXT(ExecuteWmiMethod__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_ExecuteWmiMethod__WMILIB_CONTEXT(S)[x]} _S_ExecuteWmiMethod__WMILIB_CONTEXT(S)[x] <==> S[ExecuteWmiMethod__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_ExecuteWmiMethod__WMILIB_CONTEXTInv(S)[x]} _S_ExecuteWmiMethod__WMILIB_CONTEXTInv(S)[x] <==> S[ExecuteWmiMethod__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ExecuteWmiMethod__WMILIB_CONTEXT(S)} S[x] ==> _S_ExecuteWmiMethod__WMILIB_CONTEXT(S)[ExecuteWmiMethod__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ExecuteWmiMethod__WMILIB_CONTEXTInv(S)} S[x] ==> _S_ExecuteWmiMethod__WMILIB_CONTEXTInv(S)[ExecuteWmiMethod__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {ExecuteWmiMethod__WMILIB_CONTEXT(x)} ExecuteWmiMethod__WMILIB_CONTEXT(x) == x + 24);
axiom (forall x:int :: {ExecuteWmiMethod__WMILIB_CONTEXTInv(x)} ExecuteWmiMethod__WMILIB_CONTEXTInv(x) == x - 24);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 24, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 24, 1) == ExecuteWmiMethod__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 24)} MINUS_LEFT_PTR(x, 1, 24) == ExecuteWmiMethod__WMILIB_CONTEXTInv(x));
function ExtraWaitWakeIrp__DEVICE_EXTENSION(int) returns (int);
function ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(int) returns (int);
function _S_ExtraWaitWakeIrp__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_ExtraWaitWakeIrp__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(ExtraWaitWakeIrp__DEVICE_EXTENSION(x))} ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(ExtraWaitWakeIrp__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x)} ExtraWaitWakeIrp__DEVICE_EXTENSION(ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_ExtraWaitWakeIrp__DEVICE_EXTENSION(S)[x]} _S_ExtraWaitWakeIrp__DEVICE_EXTENSION(S)[x] <==> S[ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(S)[x]} _S_ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(S)[x] <==> S[ExtraWaitWakeIrp__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ExtraWaitWakeIrp__DEVICE_EXTENSION(S)} S[x] ==> _S_ExtraWaitWakeIrp__DEVICE_EXTENSION(S)[ExtraWaitWakeIrp__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(S)[ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {ExtraWaitWakeIrp__DEVICE_EXTENSION(x)} ExtraWaitWakeIrp__DEVICE_EXTENSION(x) == x + 264);
axiom (forall x:int :: {ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x)} ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x) == x - 264);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 264, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 264, 1) == ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 264)} MINUS_LEFT_PTR(x, 1, 264) == ExtraWaitWakeIrp__DEVICE_EXTENSIONInv(x));
function File__DEVICE_EXTENSION(int) returns (int);
function File__DEVICE_EXTENSIONInv(int) returns (int);
function _S_File__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_File__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {File__DEVICE_EXTENSIONInv(File__DEVICE_EXTENSION(x))} File__DEVICE_EXTENSIONInv(File__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {File__DEVICE_EXTENSIONInv(x)} File__DEVICE_EXTENSION(File__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_File__DEVICE_EXTENSION(S)[x]} _S_File__DEVICE_EXTENSION(S)[x] <==> S[File__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_File__DEVICE_EXTENSIONInv(S)[x]} _S_File__DEVICE_EXTENSIONInv(S)[x] <==> S[File__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_File__DEVICE_EXTENSION(S)} S[x] ==> _S_File__DEVICE_EXTENSION(S)[File__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_File__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_File__DEVICE_EXTENSIONInv(S)[File__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {File__DEVICE_EXTENSION(x)} File__DEVICE_EXTENSION(x) == x + 280);
axiom (forall x:int :: {File__DEVICE_EXTENSIONInv(x)} File__DEVICE_EXTENSIONInv(x) == x - 280);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 280, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 280, 1) == File__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 280)} MINUS_LEFT_PTR(x, 1, 280) == File__DEVICE_EXTENSIONInv(x));
function Flags__DEVICE_OBJECT(int) returns (int);
function Flags__DEVICE_OBJECTInv(int) returns (int);
function _S_Flags__DEVICE_OBJECT([int]bool) returns ([int]bool);
function _S_Flags__DEVICE_OBJECTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Flags__DEVICE_OBJECTInv(Flags__DEVICE_OBJECT(x))} Flags__DEVICE_OBJECTInv(Flags__DEVICE_OBJECT(x)) == x);
axiom (forall x:int :: {Flags__DEVICE_OBJECTInv(x)} Flags__DEVICE_OBJECT(Flags__DEVICE_OBJECTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Flags__DEVICE_OBJECT(S)[x]} _S_Flags__DEVICE_OBJECT(S)[x] <==> S[Flags__DEVICE_OBJECTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Flags__DEVICE_OBJECTInv(S)[x]} _S_Flags__DEVICE_OBJECTInv(S)[x] <==> S[Flags__DEVICE_OBJECT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Flags__DEVICE_OBJECT(S)} S[x] ==> _S_Flags__DEVICE_OBJECT(S)[Flags__DEVICE_OBJECT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Flags__DEVICE_OBJECTInv(S)} S[x] ==> _S_Flags__DEVICE_OBJECTInv(S)[Flags__DEVICE_OBJECTInv(x)]);
        
axiom (forall x:int :: {Flags__DEVICE_OBJECT(x)} Flags__DEVICE_OBJECT(x) == x + 28);
axiom (forall x:int :: {Flags__DEVICE_OBJECTInv(x)} Flags__DEVICE_OBJECTInv(x) == x - 28);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 28, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 28, 1) == Flags__DEVICE_OBJECTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 28)} MINUS_LEFT_PTR(x, 1, 28) == Flags__DEVICE_OBJECTInv(x));
function Flink__LIST_ENTRY(int) returns (int);
function Flink__LIST_ENTRYInv(int) returns (int);
function _S_Flink__LIST_ENTRY([int]bool) returns ([int]bool);
function _S_Flink__LIST_ENTRYInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Flink__LIST_ENTRYInv(Flink__LIST_ENTRY(x))} Flink__LIST_ENTRYInv(Flink__LIST_ENTRY(x)) == x);
axiom (forall x:int :: {Flink__LIST_ENTRYInv(x)} Flink__LIST_ENTRY(Flink__LIST_ENTRYInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Flink__LIST_ENTRY(S)[x]} _S_Flink__LIST_ENTRY(S)[x] <==> S[Flink__LIST_ENTRYInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Flink__LIST_ENTRYInv(S)[x]} _S_Flink__LIST_ENTRYInv(S)[x] <==> S[Flink__LIST_ENTRY(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Flink__LIST_ENTRY(S)} S[x] ==> _S_Flink__LIST_ENTRY(S)[Flink__LIST_ENTRY(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Flink__LIST_ENTRYInv(S)} S[x] ==> _S_Flink__LIST_ENTRYInv(S)[Flink__LIST_ENTRYInv(x)]);
        
axiom (forall x:int :: {Flink__LIST_ENTRY(x)} Flink__LIST_ENTRY(x) == x + 0);
axiom (forall x:int :: {Flink__LIST_ENTRYInv(x)} Flink__LIST_ENTRYInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Flink__LIST_ENTRYInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Flink__LIST_ENTRYInv(x));
function GrandMaster__GLOBALS(int) returns (int);
function GrandMaster__GLOBALSInv(int) returns (int);
function _S_GrandMaster__GLOBALS([int]bool) returns ([int]bool);
function _S_GrandMaster__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {GrandMaster__GLOBALSInv(GrandMaster__GLOBALS(x))} GrandMaster__GLOBALSInv(GrandMaster__GLOBALS(x)) == x);
axiom (forall x:int :: {GrandMaster__GLOBALSInv(x)} GrandMaster__GLOBALS(GrandMaster__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_GrandMaster__GLOBALS(S)[x]} _S_GrandMaster__GLOBALS(S)[x] <==> S[GrandMaster__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_GrandMaster__GLOBALSInv(S)[x]} _S_GrandMaster__GLOBALSInv(S)[x] <==> S[GrandMaster__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_GrandMaster__GLOBALS(S)} S[x] ==> _S_GrandMaster__GLOBALS(S)[GrandMaster__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_GrandMaster__GLOBALSInv(S)} S[x] ==> _S_GrandMaster__GLOBALSInv(S)[GrandMaster__GLOBALSInv(x)]);
        
axiom (forall x:int :: {GrandMaster__GLOBALS(x)} GrandMaster__GLOBALS(x) == x + 4);
axiom (forall x:int :: {GrandMaster__GLOBALSInv(x)} GrandMaster__GLOBALSInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == GrandMaster__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == GrandMaster__GLOBALSInv(x));
function GuidCount__WMILIB_CONTEXT(int) returns (int);
function GuidCount__WMILIB_CONTEXTInv(int) returns (int);
function _S_GuidCount__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_GuidCount__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {GuidCount__WMILIB_CONTEXTInv(GuidCount__WMILIB_CONTEXT(x))} GuidCount__WMILIB_CONTEXTInv(GuidCount__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {GuidCount__WMILIB_CONTEXTInv(x)} GuidCount__WMILIB_CONTEXT(GuidCount__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_GuidCount__WMILIB_CONTEXT(S)[x]} _S_GuidCount__WMILIB_CONTEXT(S)[x] <==> S[GuidCount__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_GuidCount__WMILIB_CONTEXTInv(S)[x]} _S_GuidCount__WMILIB_CONTEXTInv(S)[x] <==> S[GuidCount__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_GuidCount__WMILIB_CONTEXT(S)} S[x] ==> _S_GuidCount__WMILIB_CONTEXT(S)[GuidCount__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_GuidCount__WMILIB_CONTEXTInv(S)} S[x] ==> _S_GuidCount__WMILIB_CONTEXTInv(S)[GuidCount__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {GuidCount__WMILIB_CONTEXT(x)} GuidCount__WMILIB_CONTEXT(x) == x + 0);
axiom (forall x:int :: {GuidCount__WMILIB_CONTEXTInv(x)} GuidCount__WMILIB_CONTEXTInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == GuidCount__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == GuidCount__WMILIB_CONTEXTInv(x));
function GuidList__WMILIB_CONTEXT(int) returns (int);
function GuidList__WMILIB_CONTEXTInv(int) returns (int);
function _S_GuidList__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_GuidList__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {GuidList__WMILIB_CONTEXTInv(GuidList__WMILIB_CONTEXT(x))} GuidList__WMILIB_CONTEXTInv(GuidList__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {GuidList__WMILIB_CONTEXTInv(x)} GuidList__WMILIB_CONTEXT(GuidList__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_GuidList__WMILIB_CONTEXT(S)[x]} _S_GuidList__WMILIB_CONTEXT(S)[x] <==> S[GuidList__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_GuidList__WMILIB_CONTEXTInv(S)[x]} _S_GuidList__WMILIB_CONTEXTInv(S)[x] <==> S[GuidList__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_GuidList__WMILIB_CONTEXT(S)} S[x] ==> _S_GuidList__WMILIB_CONTEXT(S)[GuidList__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_GuidList__WMILIB_CONTEXTInv(S)} S[x] ==> _S_GuidList__WMILIB_CONTEXTInv(S)[GuidList__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {GuidList__WMILIB_CONTEXT(x)} GuidList__WMILIB_CONTEXT(x) == x + 4);
axiom (forall x:int :: {GuidList__WMILIB_CONTEXTInv(x)} GuidList__WMILIB_CONTEXTInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == GuidList__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == GuidList__WMILIB_CONTEXTInv(x));
function Hand___unnamed_1_2ef8da39(int) returns (int);
function Hand___unnamed_1_2ef8da39Inv(int) returns (int);
function _S_Hand___unnamed_1_2ef8da39([int]bool) returns ([int]bool);
function _S_Hand___unnamed_1_2ef8da39Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Hand___unnamed_1_2ef8da39Inv(Hand___unnamed_1_2ef8da39(x))} Hand___unnamed_1_2ef8da39Inv(Hand___unnamed_1_2ef8da39(x)) == x);
axiom (forall x:int :: {Hand___unnamed_1_2ef8da39Inv(x)} Hand___unnamed_1_2ef8da39(Hand___unnamed_1_2ef8da39Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Hand___unnamed_1_2ef8da39(S)[x]} _S_Hand___unnamed_1_2ef8da39(S)[x] <==> S[Hand___unnamed_1_2ef8da39Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Hand___unnamed_1_2ef8da39Inv(S)[x]} _S_Hand___unnamed_1_2ef8da39Inv(S)[x] <==> S[Hand___unnamed_1_2ef8da39(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Hand___unnamed_1_2ef8da39(S)} S[x] ==> _S_Hand___unnamed_1_2ef8da39(S)[Hand___unnamed_1_2ef8da39(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Hand___unnamed_1_2ef8da39Inv(S)} S[x] ==> _S_Hand___unnamed_1_2ef8da39Inv(S)[Hand___unnamed_1_2ef8da39Inv(x)]);
        
axiom (forall x:int :: {Hand___unnamed_1_2ef8da39(x)} Hand___unnamed_1_2ef8da39(x) == x + 0);
axiom (forall x:int :: {Hand___unnamed_1_2ef8da39Inv(x)} Hand___unnamed_1_2ef8da39Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Hand___unnamed_1_2ef8da39Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Hand___unnamed_1_2ef8da39Inv(x));
function Header__KEVENT(int) returns (int);
function Header__KEVENTInv(int) returns (int);
function _S_Header__KEVENT([int]bool) returns ([int]bool);
function _S_Header__KEVENTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Header__KEVENTInv(Header__KEVENT(x))} Header__KEVENTInv(Header__KEVENT(x)) == x);
axiom (forall x:int :: {Header__KEVENTInv(x)} Header__KEVENT(Header__KEVENTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Header__KEVENT(S)[x]} _S_Header__KEVENT(S)[x] <==> S[Header__KEVENTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Header__KEVENTInv(S)[x]} _S_Header__KEVENTInv(S)[x] <==> S[Header__KEVENT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Header__KEVENT(S)} S[x] ==> _S_Header__KEVENT(S)[Header__KEVENT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Header__KEVENTInv(S)} S[x] ==> _S_Header__KEVENTInv(S)[Header__KEVENTInv(x)]);
        
axiom (forall x:int :: {Header__KEVENT(x)} Header__KEVENT(x) == x + 0);
axiom (forall x:int :: {Header__KEVENTInv(x)} Header__KEVENTInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Header__KEVENTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Header__KEVENTInv(x));
function HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(x))} HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(S)[HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(x)} HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 4);
axiom (forall x:int :: {HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == HighWatermark__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function IndicatorParameters__DEVICE_EXTENSION(int) returns (int);
function IndicatorParameters__DEVICE_EXTENSIONInv(int) returns (int);
function _S_IndicatorParameters__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_IndicatorParameters__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {IndicatorParameters__DEVICE_EXTENSIONInv(IndicatorParameters__DEVICE_EXTENSION(x))} IndicatorParameters__DEVICE_EXTENSIONInv(IndicatorParameters__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {IndicatorParameters__DEVICE_EXTENSIONInv(x)} IndicatorParameters__DEVICE_EXTENSION(IndicatorParameters__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_IndicatorParameters__DEVICE_EXTENSION(S)[x]} _S_IndicatorParameters__DEVICE_EXTENSION(S)[x] <==> S[IndicatorParameters__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_IndicatorParameters__DEVICE_EXTENSIONInv(S)[x]} _S_IndicatorParameters__DEVICE_EXTENSIONInv(S)[x] <==> S[IndicatorParameters__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_IndicatorParameters__DEVICE_EXTENSION(S)} S[x] ==> _S_IndicatorParameters__DEVICE_EXTENSION(S)[IndicatorParameters__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_IndicatorParameters__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_IndicatorParameters__DEVICE_EXTENSIONInv(S)[IndicatorParameters__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {IndicatorParameters__DEVICE_EXTENSION(x)} IndicatorParameters__DEVICE_EXTENSION(x) == x + 168);
axiom (forall x:int :: {IndicatorParameters__DEVICE_EXTENSIONInv(x)} IndicatorParameters__DEVICE_EXTENSIONInv(x) == x - 168);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 168, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 168, 1) == IndicatorParameters__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 168)} MINUS_LEFT_PTR(x, 1, 168) == IndicatorParameters__DEVICE_EXTENSIONInv(x));
function InputCount__DEVICE_EXTENSION(int) returns (int);
function InputCount__DEVICE_EXTENSIONInv(int) returns (int);
function _S_InputCount__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_InputCount__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {InputCount__DEVICE_EXTENSIONInv(InputCount__DEVICE_EXTENSION(x))} InputCount__DEVICE_EXTENSIONInv(InputCount__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {InputCount__DEVICE_EXTENSIONInv(x)} InputCount__DEVICE_EXTENSION(InputCount__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_InputCount__DEVICE_EXTENSION(S)[x]} _S_InputCount__DEVICE_EXTENSION(S)[x] <==> S[InputCount__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_InputCount__DEVICE_EXTENSIONInv(S)[x]} _S_InputCount__DEVICE_EXTENSIONInv(S)[x] <==> S[InputCount__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InputCount__DEVICE_EXTENSION(S)} S[x] ==> _S_InputCount__DEVICE_EXTENSION(S)[InputCount__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InputCount__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_InputCount__DEVICE_EXTENSIONInv(S)[InputCount__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {InputCount__DEVICE_EXTENSION(x)} InputCount__DEVICE_EXTENSION(x) == x + 116);
axiom (forall x:int :: {InputCount__DEVICE_EXTENSIONInv(x)} InputCount__DEVICE_EXTENSIONInv(x) == x - 116);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 116, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 116, 1) == InputCount__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 116)} MINUS_LEFT_PTR(x, 1, 116) == InputCount__DEVICE_EXTENSIONInv(x));
function InputDataQueueLength__KEYBOARD_ATTRIBUTES(int) returns (int);
function InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_InputDataQueueLength__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_InputDataQueueLength__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(InputDataQueueLength__KEYBOARD_ATTRIBUTES(x))} InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(InputDataQueueLength__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x)} InputDataQueueLength__KEYBOARD_ATTRIBUTES(InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_InputDataQueueLength__KEYBOARD_ATTRIBUTES(S)[x]} _S_InputDataQueueLength__KEYBOARD_ATTRIBUTES(S)[x] <==> S[InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[InputDataQueueLength__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InputDataQueueLength__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_InputDataQueueLength__KEYBOARD_ATTRIBUTES(S)[InputDataQueueLength__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(S)[InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {InputDataQueueLength__KEYBOARD_ATTRIBUTES(x)} InputDataQueueLength__KEYBOARD_ATTRIBUTES(x) == x + 12);
axiom (forall x:int :: {InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x)} InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x) == x - 12);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 12, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 12, 1) == InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 12)} MINUS_LEFT_PTR(x, 1, 12) == InputDataQueueLength__KEYBOARD_ATTRIBUTESInv(x));
function InputData__DEVICE_EXTENSION(int) returns (int);
function InputData__DEVICE_EXTENSIONInv(int) returns (int);
function _S_InputData__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_InputData__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {InputData__DEVICE_EXTENSIONInv(InputData__DEVICE_EXTENSION(x))} InputData__DEVICE_EXTENSIONInv(InputData__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {InputData__DEVICE_EXTENSIONInv(x)} InputData__DEVICE_EXTENSION(InputData__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_InputData__DEVICE_EXTENSION(S)[x]} _S_InputData__DEVICE_EXTENSION(S)[x] <==> S[InputData__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_InputData__DEVICE_EXTENSIONInv(S)[x]} _S_InputData__DEVICE_EXTENSIONInv(S)[x] <==> S[InputData__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InputData__DEVICE_EXTENSION(S)} S[x] ==> _S_InputData__DEVICE_EXTENSION(S)[InputData__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InputData__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_InputData__DEVICE_EXTENSIONInv(S)[InputData__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {InputData__DEVICE_EXTENSION(x)} InputData__DEVICE_EXTENSION(x) == x + 128);
axiom (forall x:int :: {InputData__DEVICE_EXTENSIONInv(x)} InputData__DEVICE_EXTENSIONInv(x) == x - 128);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 128, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 128, 1) == InputData__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 128)} MINUS_LEFT_PTR(x, 1, 128) == InputData__DEVICE_EXTENSIONInv(x));
function Inserted___unnamed_1_2dc63b48(int) returns (int);
function Inserted___unnamed_1_2dc63b48Inv(int) returns (int);
function _S_Inserted___unnamed_1_2dc63b48([int]bool) returns ([int]bool);
function _S_Inserted___unnamed_1_2dc63b48Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Inserted___unnamed_1_2dc63b48Inv(Inserted___unnamed_1_2dc63b48(x))} Inserted___unnamed_1_2dc63b48Inv(Inserted___unnamed_1_2dc63b48(x)) == x);
axiom (forall x:int :: {Inserted___unnamed_1_2dc63b48Inv(x)} Inserted___unnamed_1_2dc63b48(Inserted___unnamed_1_2dc63b48Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Inserted___unnamed_1_2dc63b48(S)[x]} _S_Inserted___unnamed_1_2dc63b48(S)[x] <==> S[Inserted___unnamed_1_2dc63b48Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Inserted___unnamed_1_2dc63b48Inv(S)[x]} _S_Inserted___unnamed_1_2dc63b48Inv(S)[x] <==> S[Inserted___unnamed_1_2dc63b48(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Inserted___unnamed_1_2dc63b48(S)} S[x] ==> _S_Inserted___unnamed_1_2dc63b48(S)[Inserted___unnamed_1_2dc63b48(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Inserted___unnamed_1_2dc63b48Inv(S)} S[x] ==> _S_Inserted___unnamed_1_2dc63b48Inv(S)[Inserted___unnamed_1_2dc63b48Inv(x)]);
        
axiom (forall x:int :: {Inserted___unnamed_1_2dc63b48(x)} Inserted___unnamed_1_2dc63b48(x) == x + 0);
axiom (forall x:int :: {Inserted___unnamed_1_2dc63b48Inv(x)} Inserted___unnamed_1_2dc63b48Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Inserted___unnamed_1_2dc63b48Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Inserted___unnamed_1_2dc63b48Inv(x));
function IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(int) returns (int);
function IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(int) returns (int);
function _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCK([int]bool) returns ([int]bool);
function _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(x))} IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(x)) == x);
axiom (forall x:int :: {IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x]} _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x] <==> S[IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x]} _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x] <==> S[IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(S)} S[x] ==> _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(S)[IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)} S[x] ==> _S_IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
        
axiom (forall x:int :: {IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(x)} IoCount__IO_REMOVE_LOCK_COMMON_BLOCK(x) == x + 4);
axiom (forall x:int :: {IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == IoCount__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
function KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(int) returns (int);
function KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(x))} KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x)} KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(S)[x]} _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(S)[x] <==> S[KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(S)[KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(S)[KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(x)} KeyRepeatMaximum__KEYBOARD_ATTRIBUTES(x) == x + 22);
axiom (forall x:int :: {KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x)} KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x) == x - 22);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 22, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 22, 1) == KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 22)} MINUS_LEFT_PTR(x, 1, 22) == KeyRepeatMaximum__KEYBOARD_ATTRIBUTESInv(x));
function KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(int) returns (int);
function KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(x))} KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x)} KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(S)[x]} _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(S)[x] <==> S[KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(S)[KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(S)[KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(x)} KeyRepeatMinimum__KEYBOARD_ATTRIBUTES(x) == x + 16);
axiom (forall x:int :: {KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x)} KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x) == x - 16);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1) == KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 16)} MINUS_LEFT_PTR(x, 1, 16) == KeyRepeatMinimum__KEYBOARD_ATTRIBUTESInv(x));
function KeyboardAttributes__DEVICE_EXTENSION(int) returns (int);
function KeyboardAttributes__DEVICE_EXTENSIONInv(int) returns (int);
function _S_KeyboardAttributes__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_KeyboardAttributes__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {KeyboardAttributes__DEVICE_EXTENSIONInv(KeyboardAttributes__DEVICE_EXTENSION(x))} KeyboardAttributes__DEVICE_EXTENSIONInv(KeyboardAttributes__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {KeyboardAttributes__DEVICE_EXTENSIONInv(x)} KeyboardAttributes__DEVICE_EXTENSION(KeyboardAttributes__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_KeyboardAttributes__DEVICE_EXTENSION(S)[x]} _S_KeyboardAttributes__DEVICE_EXTENSION(S)[x] <==> S[KeyboardAttributes__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_KeyboardAttributes__DEVICE_EXTENSIONInv(S)[x]} _S_KeyboardAttributes__DEVICE_EXTENSIONInv(S)[x] <==> S[KeyboardAttributes__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyboardAttributes__DEVICE_EXTENSION(S)} S[x] ==> _S_KeyboardAttributes__DEVICE_EXTENSION(S)[KeyboardAttributes__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyboardAttributes__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_KeyboardAttributes__DEVICE_EXTENSIONInv(S)[KeyboardAttributes__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {KeyboardAttributes__DEVICE_EXTENSION(x)} KeyboardAttributes__DEVICE_EXTENSION(x) == x + 140);
axiom (forall x:int :: {KeyboardAttributes__DEVICE_EXTENSIONInv(x)} KeyboardAttributes__DEVICE_EXTENSIONInv(x) == x - 140);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 140, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 140, 1) == KeyboardAttributes__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 140)} MINUS_LEFT_PTR(x, 1, 140) == KeyboardAttributes__DEVICE_EXTENSIONInv(x));
function KeyboardIdentifier__KEYBOARD_ATTRIBUTES(int) returns (int);
function KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(KeyboardIdentifier__KEYBOARD_ATTRIBUTES(x))} KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(KeyboardIdentifier__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x)} KeyboardIdentifier__KEYBOARD_ATTRIBUTES(KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_KeyboardIdentifier__KEYBOARD_ATTRIBUTES(S)[x]} _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTES(S)[x] <==> S[KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[KeyboardIdentifier__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTES(S)[KeyboardIdentifier__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(S)[KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {KeyboardIdentifier__KEYBOARD_ATTRIBUTES(x)} KeyboardIdentifier__KEYBOARD_ATTRIBUTES(x) == x + 0);
axiom (forall x:int :: {KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x)} KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == KeyboardIdentifier__KEYBOARD_ATTRIBUTESInv(x));
function KeyboardMode__KEYBOARD_ATTRIBUTES(int) returns (int);
function KeyboardMode__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_KeyboardMode__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_KeyboardMode__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {KeyboardMode__KEYBOARD_ATTRIBUTESInv(KeyboardMode__KEYBOARD_ATTRIBUTES(x))} KeyboardMode__KEYBOARD_ATTRIBUTESInv(KeyboardMode__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {KeyboardMode__KEYBOARD_ATTRIBUTESInv(x)} KeyboardMode__KEYBOARD_ATTRIBUTES(KeyboardMode__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_KeyboardMode__KEYBOARD_ATTRIBUTES(S)[x]} _S_KeyboardMode__KEYBOARD_ATTRIBUTES(S)[x] <==> S[KeyboardMode__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_KeyboardMode__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_KeyboardMode__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[KeyboardMode__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyboardMode__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_KeyboardMode__KEYBOARD_ATTRIBUTES(S)[KeyboardMode__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_KeyboardMode__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_KeyboardMode__KEYBOARD_ATTRIBUTESInv(S)[KeyboardMode__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {KeyboardMode__KEYBOARD_ATTRIBUTES(x)} KeyboardMode__KEYBOARD_ATTRIBUTES(x) == x + 2);
axiom (forall x:int :: {KeyboardMode__KEYBOARD_ATTRIBUTESInv(x)} KeyboardMode__KEYBOARD_ATTRIBUTESInv(x) == x - 2);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1) == KeyboardMode__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 2)} MINUS_LEFT_PTR(x, 1, 2) == KeyboardMode__KEYBOARD_ATTRIBUTESInv(x));
function LedFlags__KEYBOARD_INDICATOR_PARAMETERS(int) returns (int);
function LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(int) returns (int);
function _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERS([int]bool) returns ([int]bool);
function _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(LedFlags__KEYBOARD_INDICATOR_PARAMETERS(x))} LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(LedFlags__KEYBOARD_INDICATOR_PARAMETERS(x)) == x);
axiom (forall x:int :: {LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x)} LedFlags__KEYBOARD_INDICATOR_PARAMETERS(LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_LedFlags__KEYBOARD_INDICATOR_PARAMETERS(S)[x]} _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERS(S)[x] <==> S[LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(S)[x]} _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(S)[x] <==> S[LedFlags__KEYBOARD_INDICATOR_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERS(S)} S[x] ==> _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERS(S)[LedFlags__KEYBOARD_INDICATOR_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(S)} S[x] ==> _S_LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(S)[LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x)]);
        
axiom (forall x:int :: {LedFlags__KEYBOARD_INDICATOR_PARAMETERS(x)} LedFlags__KEYBOARD_INDICATOR_PARAMETERS(x) == x + 2);
axiom (forall x:int :: {LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x)} LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x) == x - 2);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1) == LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 2)} MINUS_LEFT_PTR(x, 1, 2) == LedFlags__KEYBOARD_INDICATOR_PARAMETERSInv(x));
function LegacyDeviceList__GLOBALS(int) returns (int);
function LegacyDeviceList__GLOBALSInv(int) returns (int);
function _S_LegacyDeviceList__GLOBALS([int]bool) returns ([int]bool);
function _S_LegacyDeviceList__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {LegacyDeviceList__GLOBALSInv(LegacyDeviceList__GLOBALS(x))} LegacyDeviceList__GLOBALSInv(LegacyDeviceList__GLOBALS(x)) == x);
axiom (forall x:int :: {LegacyDeviceList__GLOBALSInv(x)} LegacyDeviceList__GLOBALS(LegacyDeviceList__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_LegacyDeviceList__GLOBALS(S)[x]} _S_LegacyDeviceList__GLOBALS(S)[x] <==> S[LegacyDeviceList__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_LegacyDeviceList__GLOBALSInv(S)[x]} _S_LegacyDeviceList__GLOBALSInv(S)[x] <==> S[LegacyDeviceList__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LegacyDeviceList__GLOBALS(S)} S[x] ==> _S_LegacyDeviceList__GLOBALS(S)[LegacyDeviceList__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LegacyDeviceList__GLOBALSInv(S)} S[x] ==> _S_LegacyDeviceList__GLOBALSInv(S)[LegacyDeviceList__GLOBALSInv(x)]);
        
axiom (forall x:int :: {LegacyDeviceList__GLOBALS(x)} LegacyDeviceList__GLOBALS(x) == x + 888);
axiom (forall x:int :: {LegacyDeviceList__GLOBALSInv(x)} LegacyDeviceList__GLOBALSInv(x) == x - 888);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 888, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 888, 1) == LegacyDeviceList__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 888)} MINUS_LEFT_PTR(x, 1, 888) == LegacyDeviceList__GLOBALSInv(x));
function Length__UNICODE_STRING(int) returns (int);
function Length__UNICODE_STRINGInv(int) returns (int);
function _S_Length__UNICODE_STRING([int]bool) returns ([int]bool);
function _S_Length__UNICODE_STRINGInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Length__UNICODE_STRINGInv(Length__UNICODE_STRING(x))} Length__UNICODE_STRINGInv(Length__UNICODE_STRING(x)) == x);
axiom (forall x:int :: {Length__UNICODE_STRINGInv(x)} Length__UNICODE_STRING(Length__UNICODE_STRINGInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Length__UNICODE_STRING(S)[x]} _S_Length__UNICODE_STRING(S)[x] <==> S[Length__UNICODE_STRINGInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Length__UNICODE_STRINGInv(S)[x]} _S_Length__UNICODE_STRINGInv(S)[x] <==> S[Length__UNICODE_STRING(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Length__UNICODE_STRING(S)} S[x] ==> _S_Length__UNICODE_STRING(S)[Length__UNICODE_STRING(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Length__UNICODE_STRINGInv(S)} S[x] ==> _S_Length__UNICODE_STRINGInv(S)[Length__UNICODE_STRINGInv(x)]);
        
axiom (forall x:int :: {Length__UNICODE_STRING(x)} Length__UNICODE_STRING(x) == x + 0);
axiom (forall x:int :: {Length__UNICODE_STRINGInv(x)} Length__UNICODE_STRINGInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Length__UNICODE_STRINGInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Length__UNICODE_STRINGInv(x));
function Link__DEVICE_EXTENSION(int) returns (int);
function Link__DEVICE_EXTENSIONInv(int) returns (int);
function _S_Link__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_Link__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Link__DEVICE_EXTENSIONInv(Link__DEVICE_EXTENSION(x))} Link__DEVICE_EXTENSIONInv(Link__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {Link__DEVICE_EXTENSIONInv(x)} Link__DEVICE_EXTENSION(Link__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Link__DEVICE_EXTENSION(S)[x]} _S_Link__DEVICE_EXTENSION(S)[x] <==> S[Link__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Link__DEVICE_EXTENSIONInv(S)[x]} _S_Link__DEVICE_EXTENSIONInv(S)[x] <==> S[Link__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Link__DEVICE_EXTENSION(S)} S[x] ==> _S_Link__DEVICE_EXTENSION(S)[Link__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Link__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_Link__DEVICE_EXTENSIONInv(S)[Link__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {Link__DEVICE_EXTENSION(x)} Link__DEVICE_EXTENSION(x) == x + 272);
axiom (forall x:int :: {Link__DEVICE_EXTENSIONInv(x)} Link__DEVICE_EXTENSIONInv(x) == x - 272);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 272, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 272, 1) == Link__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 272)} MINUS_LEFT_PTR(x, 1, 272) == Link__DEVICE_EXTENSIONInv(x));
function LockList__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_LockList__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_LockList__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(LockList__IO_REMOVE_LOCK_DBG_BLOCK(x))} LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(LockList__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} LockList__IO_REMOVE_LOCK_DBG_BLOCK(LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_LockList__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_LockList__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[LockList__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LockList__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_LockList__IO_REMOVE_LOCK_DBG_BLOCK(S)[LockList__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {LockList__IO_REMOVE_LOCK_DBG_BLOCK(x)} LockList__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 20);
axiom (forall x:int :: {LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 20);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 20, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 20, 1) == LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 20)} MINUS_LEFT_PTR(x, 1, 20) == LockList__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function Lock___unnamed_4_a97c65a1(int) returns (int);
function Lock___unnamed_4_a97c65a1Inv(int) returns (int);
function _S_Lock___unnamed_4_a97c65a1([int]bool) returns ([int]bool);
function _S_Lock___unnamed_4_a97c65a1Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Lock___unnamed_4_a97c65a1Inv(Lock___unnamed_4_a97c65a1(x))} Lock___unnamed_4_a97c65a1Inv(Lock___unnamed_4_a97c65a1(x)) == x);
axiom (forall x:int :: {Lock___unnamed_4_a97c65a1Inv(x)} Lock___unnamed_4_a97c65a1(Lock___unnamed_4_a97c65a1Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Lock___unnamed_4_a97c65a1(S)[x]} _S_Lock___unnamed_4_a97c65a1(S)[x] <==> S[Lock___unnamed_4_a97c65a1Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Lock___unnamed_4_a97c65a1Inv(S)[x]} _S_Lock___unnamed_4_a97c65a1Inv(S)[x] <==> S[Lock___unnamed_4_a97c65a1(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Lock___unnamed_4_a97c65a1(S)} S[x] ==> _S_Lock___unnamed_4_a97c65a1(S)[Lock___unnamed_4_a97c65a1(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Lock___unnamed_4_a97c65a1Inv(S)} S[x] ==> _S_Lock___unnamed_4_a97c65a1Inv(S)[Lock___unnamed_4_a97c65a1Inv(x)]);
        
axiom (forall x:int :: {Lock___unnamed_4_a97c65a1(x)} Lock___unnamed_4_a97c65a1(x) == x + 0);
axiom (forall x:int :: {Lock___unnamed_4_a97c65a1Inv(x)} Lock___unnamed_4_a97c65a1Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Lock___unnamed_4_a97c65a1Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Lock___unnamed_4_a97c65a1Inv(x));
function LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(x))} LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(S)[LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(x)} LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 32);
axiom (forall x:int :: {LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 32);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 32, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 32, 1) == LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 32)} MINUS_LEFT_PTR(x, 1, 32) == LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(x))} MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(S)[MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(x)} MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 8);
axiom (forall x:int :: {MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 8);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1) == MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 8)} MINUS_LEFT_PTR(x, 1, 8) == MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function MaximumLength__UNICODE_STRING(int) returns (int);
function MaximumLength__UNICODE_STRINGInv(int) returns (int);
function _S_MaximumLength__UNICODE_STRING([int]bool) returns ([int]bool);
function _S_MaximumLength__UNICODE_STRINGInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {MaximumLength__UNICODE_STRINGInv(MaximumLength__UNICODE_STRING(x))} MaximumLength__UNICODE_STRINGInv(MaximumLength__UNICODE_STRING(x)) == x);
axiom (forall x:int :: {MaximumLength__UNICODE_STRINGInv(x)} MaximumLength__UNICODE_STRING(MaximumLength__UNICODE_STRINGInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_MaximumLength__UNICODE_STRING(S)[x]} _S_MaximumLength__UNICODE_STRING(S)[x] <==> S[MaximumLength__UNICODE_STRINGInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_MaximumLength__UNICODE_STRINGInv(S)[x]} _S_MaximumLength__UNICODE_STRINGInv(S)[x] <==> S[MaximumLength__UNICODE_STRING(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MaximumLength__UNICODE_STRING(S)} S[x] ==> _S_MaximumLength__UNICODE_STRING(S)[MaximumLength__UNICODE_STRING(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MaximumLength__UNICODE_STRINGInv(S)} S[x] ==> _S_MaximumLength__UNICODE_STRINGInv(S)[MaximumLength__UNICODE_STRINGInv(x)]);
        
axiom (forall x:int :: {MaximumLength__UNICODE_STRING(x)} MaximumLength__UNICODE_STRING(x) == x + 2);
axiom (forall x:int :: {MaximumLength__UNICODE_STRINGInv(x)} MaximumLength__UNICODE_STRINGInv(x) == x - 2);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1) == MaximumLength__UNICODE_STRINGInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 2)} MINUS_LEFT_PTR(x, 1, 2) == MaximumLength__UNICODE_STRINGInv(x));
function MinDeviceWakeState__DEVICE_EXTENSION(int) returns (int);
function MinDeviceWakeState__DEVICE_EXTENSIONInv(int) returns (int);
function _S_MinDeviceWakeState__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_MinDeviceWakeState__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {MinDeviceWakeState__DEVICE_EXTENSIONInv(MinDeviceWakeState__DEVICE_EXTENSION(x))} MinDeviceWakeState__DEVICE_EXTENSIONInv(MinDeviceWakeState__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {MinDeviceWakeState__DEVICE_EXTENSIONInv(x)} MinDeviceWakeState__DEVICE_EXTENSION(MinDeviceWakeState__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_MinDeviceWakeState__DEVICE_EXTENSION(S)[x]} _S_MinDeviceWakeState__DEVICE_EXTENSION(S)[x] <==> S[MinDeviceWakeState__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_MinDeviceWakeState__DEVICE_EXTENSIONInv(S)[x]} _S_MinDeviceWakeState__DEVICE_EXTENSIONInv(S)[x] <==> S[MinDeviceWakeState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MinDeviceWakeState__DEVICE_EXTENSION(S)} S[x] ==> _S_MinDeviceWakeState__DEVICE_EXTENSION(S)[MinDeviceWakeState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MinDeviceWakeState__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_MinDeviceWakeState__DEVICE_EXTENSIONInv(S)[MinDeviceWakeState__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {MinDeviceWakeState__DEVICE_EXTENSION(x)} MinDeviceWakeState__DEVICE_EXTENSION(x) == x + 252);
axiom (forall x:int :: {MinDeviceWakeState__DEVICE_EXTENSIONInv(x)} MinDeviceWakeState__DEVICE_EXTENSIONInv(x) == x - 252);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 252, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 252, 1) == MinDeviceWakeState__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 252)} MINUS_LEFT_PTR(x, 1, 252) == MinDeviceWakeState__DEVICE_EXTENSIONInv(x));
function MinSystemWakeState__DEVICE_EXTENSION(int) returns (int);
function MinSystemWakeState__DEVICE_EXTENSIONInv(int) returns (int);
function _S_MinSystemWakeState__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_MinSystemWakeState__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {MinSystemWakeState__DEVICE_EXTENSIONInv(MinSystemWakeState__DEVICE_EXTENSION(x))} MinSystemWakeState__DEVICE_EXTENSIONInv(MinSystemWakeState__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {MinSystemWakeState__DEVICE_EXTENSIONInv(x)} MinSystemWakeState__DEVICE_EXTENSION(MinSystemWakeState__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_MinSystemWakeState__DEVICE_EXTENSION(S)[x]} _S_MinSystemWakeState__DEVICE_EXTENSION(S)[x] <==> S[MinSystemWakeState__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_MinSystemWakeState__DEVICE_EXTENSIONInv(S)[x]} _S_MinSystemWakeState__DEVICE_EXTENSIONInv(S)[x] <==> S[MinSystemWakeState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MinSystemWakeState__DEVICE_EXTENSION(S)} S[x] ==> _S_MinSystemWakeState__DEVICE_EXTENSION(S)[MinSystemWakeState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_MinSystemWakeState__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_MinSystemWakeState__DEVICE_EXTENSIONInv(S)[MinSystemWakeState__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {MinSystemWakeState__DEVICE_EXTENSION(x)} MinSystemWakeState__DEVICE_EXTENSION(x) == x + 256);
axiom (forall x:int :: {MinSystemWakeState__DEVICE_EXTENSIONInv(x)} MinSystemWakeState__DEVICE_EXTENSIONInv(x) == x - 256);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 256, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 256, 1) == MinSystemWakeState__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 256)} MINUS_LEFT_PTR(x, 1, 256) == MinSystemWakeState__DEVICE_EXTENSIONInv(x));
function Mutex__GLOBALS(int) returns (int);
function Mutex__GLOBALSInv(int) returns (int);
function _S_Mutex__GLOBALS([int]bool) returns ([int]bool);
function _S_Mutex__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Mutex__GLOBALSInv(Mutex__GLOBALS(x))} Mutex__GLOBALSInv(Mutex__GLOBALS(x)) == x);
axiom (forall x:int :: {Mutex__GLOBALSInv(x)} Mutex__GLOBALS(Mutex__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Mutex__GLOBALS(S)[x]} _S_Mutex__GLOBALS(S)[x] <==> S[Mutex__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Mutex__GLOBALSInv(S)[x]} _S_Mutex__GLOBALSInv(S)[x] <==> S[Mutex__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Mutex__GLOBALS(S)} S[x] ==> _S_Mutex__GLOBALS(S)[Mutex__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Mutex__GLOBALSInv(S)} S[x] ==> _S_Mutex__GLOBALSInv(S)[Mutex__GLOBALSInv(x)]);
        
axiom (forall x:int :: {Mutex__GLOBALS(x)} Mutex__GLOBALS(x) == x + 24);
axiom (forall x:int :: {Mutex__GLOBALSInv(x)} Mutex__GLOBALSInv(x) == x - 24);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 24, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 24, 1) == Mutex__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 24)} MINUS_LEFT_PTR(x, 1, 24) == Mutex__GLOBALSInv(x));
function NpxIrql___unnamed_1_29794256(int) returns (int);
function NpxIrql___unnamed_1_29794256Inv(int) returns (int);
function _S_NpxIrql___unnamed_1_29794256([int]bool) returns ([int]bool);
function _S_NpxIrql___unnamed_1_29794256Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {NpxIrql___unnamed_1_29794256Inv(NpxIrql___unnamed_1_29794256(x))} NpxIrql___unnamed_1_29794256Inv(NpxIrql___unnamed_1_29794256(x)) == x);
axiom (forall x:int :: {NpxIrql___unnamed_1_29794256Inv(x)} NpxIrql___unnamed_1_29794256(NpxIrql___unnamed_1_29794256Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_NpxIrql___unnamed_1_29794256(S)[x]} _S_NpxIrql___unnamed_1_29794256(S)[x] <==> S[NpxIrql___unnamed_1_29794256Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_NpxIrql___unnamed_1_29794256Inv(S)[x]} _S_NpxIrql___unnamed_1_29794256Inv(S)[x] <==> S[NpxIrql___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NpxIrql___unnamed_1_29794256(S)} S[x] ==> _S_NpxIrql___unnamed_1_29794256(S)[NpxIrql___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NpxIrql___unnamed_1_29794256Inv(S)} S[x] ==> _S_NpxIrql___unnamed_1_29794256Inv(S)[NpxIrql___unnamed_1_29794256Inv(x)]);
        
axiom (forall x:int :: {NpxIrql___unnamed_1_29794256(x)} NpxIrql___unnamed_1_29794256(x) == x + 0);
axiom (forall x:int :: {NpxIrql___unnamed_1_29794256Inv(x)} NpxIrql___unnamed_1_29794256Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == NpxIrql___unnamed_1_29794256Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == NpxIrql___unnamed_1_29794256Inv(x));
function NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(int) returns (int);
function NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(x))} NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x)} NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(S)[x]} _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(S)[x] <==> S[NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(S)[NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(S)[NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(x)} NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES(x) == x + 4);
axiom (forall x:int :: {NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x)} NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == NumberOfFunctionKeys__KEYBOARD_ATTRIBUTESInv(x));
function NumberOfIndicators__KEYBOARD_ATTRIBUTES(int) returns (int);
function NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_NumberOfIndicators__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_NumberOfIndicators__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(NumberOfIndicators__KEYBOARD_ATTRIBUTES(x))} NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(NumberOfIndicators__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x)} NumberOfIndicators__KEYBOARD_ATTRIBUTES(NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_NumberOfIndicators__KEYBOARD_ATTRIBUTES(S)[x]} _S_NumberOfIndicators__KEYBOARD_ATTRIBUTES(S)[x] <==> S[NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[NumberOfIndicators__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberOfIndicators__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_NumberOfIndicators__KEYBOARD_ATTRIBUTES(S)[NumberOfIndicators__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(S)[NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {NumberOfIndicators__KEYBOARD_ATTRIBUTES(x)} NumberOfIndicators__KEYBOARD_ATTRIBUTES(x) == x + 6);
axiom (forall x:int :: {NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x)} NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x) == x - 6);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 6, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 6, 1) == NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 6)} MINUS_LEFT_PTR(x, 1, 6) == NumberOfIndicators__KEYBOARD_ATTRIBUTESInv(x));
function NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(int) returns (int);
function NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(int) returns (int);
function _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTES([int]bool) returns ([int]bool);
function _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(x))} NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(x)) == x);
axiom (forall x:int :: {NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x)} NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(S)[x]} _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(S)[x] <==> S[NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(S)[x]} _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(S)[x] <==> S[NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(S)} S[x] ==> _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(S)[NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(S)} S[x] ==> _S_NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(S)[NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x)]);
        
axiom (forall x:int :: {NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(x)} NumberOfKeysTotal__KEYBOARD_ATTRIBUTES(x) == x + 8);
axiom (forall x:int :: {NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x)} NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x) == x - 8);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1) == NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 8)} MINUS_LEFT_PTR(x, 1, 8) == NumberOfKeysTotal__KEYBOARD_ATTRIBUTESInv(x));
function OkayToLogOverflow__DEVICE_EXTENSION(int) returns (int);
function OkayToLogOverflow__DEVICE_EXTENSIONInv(int) returns (int);
function _S_OkayToLogOverflow__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_OkayToLogOverflow__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {OkayToLogOverflow__DEVICE_EXTENSIONInv(OkayToLogOverflow__DEVICE_EXTENSION(x))} OkayToLogOverflow__DEVICE_EXTENSIONInv(OkayToLogOverflow__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {OkayToLogOverflow__DEVICE_EXTENSIONInv(x)} OkayToLogOverflow__DEVICE_EXTENSION(OkayToLogOverflow__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_OkayToLogOverflow__DEVICE_EXTENSION(S)[x]} _S_OkayToLogOverflow__DEVICE_EXTENSION(S)[x] <==> S[OkayToLogOverflow__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_OkayToLogOverflow__DEVICE_EXTENSIONInv(S)[x]} _S_OkayToLogOverflow__DEVICE_EXTENSIONInv(S)[x] <==> S[OkayToLogOverflow__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_OkayToLogOverflow__DEVICE_EXTENSION(S)} S[x] ==> _S_OkayToLogOverflow__DEVICE_EXTENSION(S)[OkayToLogOverflow__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_OkayToLogOverflow__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_OkayToLogOverflow__DEVICE_EXTENSIONInv(S)[OkayToLogOverflow__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {OkayToLogOverflow__DEVICE_EXTENSION(x)} OkayToLogOverflow__DEVICE_EXTENSION(x) == x + 285);
axiom (forall x:int :: {OkayToLogOverflow__DEVICE_EXTENSIONInv(x)} OkayToLogOverflow__DEVICE_EXTENSIONInv(x) == x - 285);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 285, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 285, 1) == OkayToLogOverflow__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 285)} MINUS_LEFT_PTR(x, 1, 285) == OkayToLogOverflow__DEVICE_EXTENSIONInv(x));
function PDO__DEVICE_EXTENSION(int) returns (int);
function PDO__DEVICE_EXTENSIONInv(int) returns (int);
function _S_PDO__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_PDO__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {PDO__DEVICE_EXTENSIONInv(PDO__DEVICE_EXTENSION(x))} PDO__DEVICE_EXTENSIONInv(PDO__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {PDO__DEVICE_EXTENSIONInv(x)} PDO__DEVICE_EXTENSION(PDO__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_PDO__DEVICE_EXTENSION(S)[x]} _S_PDO__DEVICE_EXTENSION(S)[x] <==> S[PDO__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_PDO__DEVICE_EXTENSIONInv(S)[x]} _S_PDO__DEVICE_EXTENSIONInv(S)[x] <==> S[PDO__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_PDO__DEVICE_EXTENSION(S)} S[x] ==> _S_PDO__DEVICE_EXTENSION(S)[PDO__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_PDO__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_PDO__DEVICE_EXTENSIONInv(S)[PDO__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {PDO__DEVICE_EXTENSION(x)} PDO__DEVICE_EXTENSION(x) == x + 12);
axiom (forall x:int :: {PDO__DEVICE_EXTENSIONInv(x)} PDO__DEVICE_EXTENSIONInv(x) == x - 12);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 12, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 12, 1) == PDO__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 12)} MINUS_LEFT_PTR(x, 1, 12) == PDO__DEVICE_EXTENSIONInv(x));
function PnP__DEVICE_EXTENSION(int) returns (int);
function PnP__DEVICE_EXTENSIONInv(int) returns (int);
function _S_PnP__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_PnP__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {PnP__DEVICE_EXTENSIONInv(PnP__DEVICE_EXTENSION(x))} PnP__DEVICE_EXTENSIONInv(PnP__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {PnP__DEVICE_EXTENSIONInv(x)} PnP__DEVICE_EXTENSION(PnP__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_PnP__DEVICE_EXTENSION(S)[x]} _S_PnP__DEVICE_EXTENSION(S)[x] <==> S[PnP__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_PnP__DEVICE_EXTENSIONInv(S)[x]} _S_PnP__DEVICE_EXTENSIONInv(S)[x] <==> S[PnP__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_PnP__DEVICE_EXTENSION(S)} S[x] ==> _S_PnP__DEVICE_EXTENSION(S)[PnP__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_PnP__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_PnP__DEVICE_EXTENSIONInv(S)[PnP__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {PnP__DEVICE_EXTENSION(x)} PnP__DEVICE_EXTENSION(x) == x + 104);
axiom (forall x:int :: {PnP__DEVICE_EXTENSIONInv(x)} PnP__DEVICE_EXTENSIONInv(x) == x - 104);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 104, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 104, 1) == PnP__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 104)} MINUS_LEFT_PTR(x, 1, 104) == PnP__DEVICE_EXTENSIONInv(x));
function QueryWmiDataBlock__WMILIB_CONTEXT(int) returns (int);
function QueryWmiDataBlock__WMILIB_CONTEXTInv(int) returns (int);
function _S_QueryWmiDataBlock__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_QueryWmiDataBlock__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {QueryWmiDataBlock__WMILIB_CONTEXTInv(QueryWmiDataBlock__WMILIB_CONTEXT(x))} QueryWmiDataBlock__WMILIB_CONTEXTInv(QueryWmiDataBlock__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {QueryWmiDataBlock__WMILIB_CONTEXTInv(x)} QueryWmiDataBlock__WMILIB_CONTEXT(QueryWmiDataBlock__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_QueryWmiDataBlock__WMILIB_CONTEXT(S)[x]} _S_QueryWmiDataBlock__WMILIB_CONTEXT(S)[x] <==> S[QueryWmiDataBlock__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_QueryWmiDataBlock__WMILIB_CONTEXTInv(S)[x]} _S_QueryWmiDataBlock__WMILIB_CONTEXTInv(S)[x] <==> S[QueryWmiDataBlock__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_QueryWmiDataBlock__WMILIB_CONTEXT(S)} S[x] ==> _S_QueryWmiDataBlock__WMILIB_CONTEXT(S)[QueryWmiDataBlock__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_QueryWmiDataBlock__WMILIB_CONTEXTInv(S)} S[x] ==> _S_QueryWmiDataBlock__WMILIB_CONTEXTInv(S)[QueryWmiDataBlock__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {QueryWmiDataBlock__WMILIB_CONTEXT(x)} QueryWmiDataBlock__WMILIB_CONTEXT(x) == x + 12);
axiom (forall x:int :: {QueryWmiDataBlock__WMILIB_CONTEXTInv(x)} QueryWmiDataBlock__WMILIB_CONTEXTInv(x) == x - 12);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 12, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 12, 1) == QueryWmiDataBlock__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 12)} MINUS_LEFT_PTR(x, 1, 12) == QueryWmiDataBlock__WMILIB_CONTEXTInv(x));
function QueryWmiRegInfo__WMILIB_CONTEXT(int) returns (int);
function QueryWmiRegInfo__WMILIB_CONTEXTInv(int) returns (int);
function _S_QueryWmiRegInfo__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_QueryWmiRegInfo__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {QueryWmiRegInfo__WMILIB_CONTEXTInv(QueryWmiRegInfo__WMILIB_CONTEXT(x))} QueryWmiRegInfo__WMILIB_CONTEXTInv(QueryWmiRegInfo__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {QueryWmiRegInfo__WMILIB_CONTEXTInv(x)} QueryWmiRegInfo__WMILIB_CONTEXT(QueryWmiRegInfo__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_QueryWmiRegInfo__WMILIB_CONTEXT(S)[x]} _S_QueryWmiRegInfo__WMILIB_CONTEXT(S)[x] <==> S[QueryWmiRegInfo__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_QueryWmiRegInfo__WMILIB_CONTEXTInv(S)[x]} _S_QueryWmiRegInfo__WMILIB_CONTEXTInv(S)[x] <==> S[QueryWmiRegInfo__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_QueryWmiRegInfo__WMILIB_CONTEXT(S)} S[x] ==> _S_QueryWmiRegInfo__WMILIB_CONTEXT(S)[QueryWmiRegInfo__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_QueryWmiRegInfo__WMILIB_CONTEXTInv(S)} S[x] ==> _S_QueryWmiRegInfo__WMILIB_CONTEXTInv(S)[QueryWmiRegInfo__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {QueryWmiRegInfo__WMILIB_CONTEXT(x)} QueryWmiRegInfo__WMILIB_CONTEXT(x) == x + 8);
axiom (forall x:int :: {QueryWmiRegInfo__WMILIB_CONTEXTInv(x)} QueryWmiRegInfo__WMILIB_CONTEXTInv(x) == x - 8);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1) == QueryWmiRegInfo__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 8)} MINUS_LEFT_PTR(x, 1, 8) == QueryWmiRegInfo__WMILIB_CONTEXTInv(x));
function Rate__KEYBOARD_TYPEMATIC_PARAMETERS(int) returns (int);
function Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(int) returns (int);
function _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERS([int]bool) returns ([int]bool);
function _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(Rate__KEYBOARD_TYPEMATIC_PARAMETERS(x))} Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(Rate__KEYBOARD_TYPEMATIC_PARAMETERS(x)) == x);
axiom (forall x:int :: {Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)} Rate__KEYBOARD_TYPEMATIC_PARAMETERS(Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Rate__KEYBOARD_TYPEMATIC_PARAMETERS(S)[x]} _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERS(S)[x] <==> S[Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[x]} _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[x] <==> S[Rate__KEYBOARD_TYPEMATIC_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERS(S)} S[x] ==> _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERS(S)[Rate__KEYBOARD_TYPEMATIC_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)} S[x] ==> _S_Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)]);
        
axiom (forall x:int :: {Rate__KEYBOARD_TYPEMATIC_PARAMETERS(x)} Rate__KEYBOARD_TYPEMATIC_PARAMETERS(x) == x + 2);
axiom (forall x:int :: {Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)} Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x) == x - 2);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1) == Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 2)} MINUS_LEFT_PTR(x, 1, 2) == Rate__KEYBOARD_TYPEMATIC_PARAMETERSInv(x));
function ReadQueue__DEVICE_EXTENSION(int) returns (int);
function ReadQueue__DEVICE_EXTENSIONInv(int) returns (int);
function _S_ReadQueue__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_ReadQueue__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {ReadQueue__DEVICE_EXTENSIONInv(ReadQueue__DEVICE_EXTENSION(x))} ReadQueue__DEVICE_EXTENSIONInv(ReadQueue__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {ReadQueue__DEVICE_EXTENSIONInv(x)} ReadQueue__DEVICE_EXTENSION(ReadQueue__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_ReadQueue__DEVICE_EXTENSION(S)[x]} _S_ReadQueue__DEVICE_EXTENSION(S)[x] <==> S[ReadQueue__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_ReadQueue__DEVICE_EXTENSIONInv(S)[x]} _S_ReadQueue__DEVICE_EXTENSIONInv(S)[x] <==> S[ReadQueue__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ReadQueue__DEVICE_EXTENSION(S)} S[x] ==> _S_ReadQueue__DEVICE_EXTENSION(S)[ReadQueue__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_ReadQueue__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_ReadQueue__DEVICE_EXTENSIONInv(S)[ReadQueue__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {ReadQueue__DEVICE_EXTENSION(x)} ReadQueue__DEVICE_EXTENSION(x) == x + 176);
axiom (forall x:int :: {ReadQueue__DEVICE_EXTENSIONInv(x)} ReadQueue__DEVICE_EXTENSIONInv(x) == x - 176);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 176, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 176, 1) == ReadQueue__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 176)} MINUS_LEFT_PTR(x, 1, 176) == ReadQueue__DEVICE_EXTENSIONInv(x));
function RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(int) returns (int);
function RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(int) returns (int);
function _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK([int]bool) returns ([int]bool);
function _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(x))} RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(x)) == x);
axiom (forall x:int :: {RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x]} _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x] <==> S[RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x]} _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x] <==> S[RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(S)} S[x] ==> _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(S)[RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)} S[x] ==> _S_RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
        
axiom (forall x:int :: {RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(x)} RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCK(x) == x + 8);
axiom (forall x:int :: {RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x) == x - 8);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1) == RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 8)} MINUS_LEFT_PTR(x, 1, 8) == RemoveEvent__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
function RemoveLock__DEVICE_EXTENSION(int) returns (int);
function RemoveLock__DEVICE_EXTENSIONInv(int) returns (int);
function _S_RemoveLock__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_RemoveLock__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {RemoveLock__DEVICE_EXTENSIONInv(RemoveLock__DEVICE_EXTENSION(x))} RemoveLock__DEVICE_EXTENSIONInv(RemoveLock__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {RemoveLock__DEVICE_EXTENSIONInv(x)} RemoveLock__DEVICE_EXTENSION(RemoveLock__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_RemoveLock__DEVICE_EXTENSION(S)[x]} _S_RemoveLock__DEVICE_EXTENSION(S)[x] <==> S[RemoveLock__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_RemoveLock__DEVICE_EXTENSIONInv(S)[x]} _S_RemoveLock__DEVICE_EXTENSIONInv(S)[x] <==> S[RemoveLock__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_RemoveLock__DEVICE_EXTENSION(S)} S[x] ==> _S_RemoveLock__DEVICE_EXTENSION(S)[RemoveLock__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_RemoveLock__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_RemoveLock__DEVICE_EXTENSIONInv(S)[RemoveLock__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {RemoveLock__DEVICE_EXTENSION(x)} RemoveLock__DEVICE_EXTENSION(x) == x + 16);
axiom (forall x:int :: {RemoveLock__DEVICE_EXTENSIONInv(x)} RemoveLock__DEVICE_EXTENSIONInv(x) == x - 16);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1) == RemoveLock__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 16)} MINUS_LEFT_PTR(x, 1, 16) == RemoveLock__DEVICE_EXTENSIONInv(x));
function Removed__IO_REMOVE_LOCK_COMMON_BLOCK(int) returns (int);
function Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(int) returns (int);
function _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCK([int]bool) returns ([int]bool);
function _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(Removed__IO_REMOVE_LOCK_COMMON_BLOCK(x))} Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(Removed__IO_REMOVE_LOCK_COMMON_BLOCK(x)) == x);
axiom (forall x:int :: {Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} Removed__IO_REMOVE_LOCK_COMMON_BLOCK(Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Removed__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x]} _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x] <==> S[Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x]} _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x] <==> S[Removed__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCK(S)} S[x] ==> _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCK(S)[Removed__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)} S[x] ==> _S_Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
        
axiom (forall x:int :: {Removed__IO_REMOVE_LOCK_COMMON_BLOCK(x)} Removed__IO_REMOVE_LOCK_COMMON_BLOCK(x) == x + 0);
axiom (forall x:int :: {Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Removed__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
function Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(x))} Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(S)[Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(x)} Reserved1__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 36);
axiom (forall x:int :: {Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 36);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 36, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 36, 1) == Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 36)} MINUS_LEFT_PTR(x, 1, 36) == Reserved1__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(x))} Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(S)[Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(x)} Reserved2__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 52);
axiom (forall x:int :: {Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 52);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 52, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 52, 1) == Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 52)} MINUS_LEFT_PTR(x, 1, 52) == Reserved2__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(int) returns (int);
function Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(int) returns (int);
function _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCK([int]bool) returns ([int]bool);
function _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(x))} Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(x)) == x);
axiom (forall x:int :: {Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x]} _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(S)[x] <==> S[Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x]} _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[x] <==> S[Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(S)} S[x] ==> _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(S)[Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)} S[x] ==> _S_Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(S)[Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)]);
        
axiom (forall x:int :: {Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(x)} Reserved__IO_REMOVE_LOCK_COMMON_BLOCK(x) == x + 1);
axiom (forall x:int :: {Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x)} Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x) == x - 1);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 1, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 1, 1) == Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 1)} MINUS_LEFT_PTR(x, 1, 1) == Reserved__IO_REMOVE_LOCK_COMMON_BLOCKInv(x));
function Self__DEVICE_EXTENSION(int) returns (int);
function Self__DEVICE_EXTENSIONInv(int) returns (int);
function _S_Self__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_Self__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Self__DEVICE_EXTENSIONInv(Self__DEVICE_EXTENSION(x))} Self__DEVICE_EXTENSIONInv(Self__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {Self__DEVICE_EXTENSIONInv(x)} Self__DEVICE_EXTENSION(Self__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Self__DEVICE_EXTENSION(S)[x]} _S_Self__DEVICE_EXTENSION(S)[x] <==> S[Self__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Self__DEVICE_EXTENSIONInv(S)[x]} _S_Self__DEVICE_EXTENSIONInv(S)[x] <==> S[Self__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Self__DEVICE_EXTENSION(S)} S[x] ==> _S_Self__DEVICE_EXTENSION(S)[Self__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Self__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_Self__DEVICE_EXTENSIONInv(S)[Self__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {Self__DEVICE_EXTENSION(x)} Self__DEVICE_EXTENSION(x) == x + 0);
axiom (forall x:int :: {Self__DEVICE_EXTENSIONInv(x)} Self__DEVICE_EXTENSIONInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Self__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Self__DEVICE_EXTENSIONInv(x));
function SequenceNumber__DEVICE_EXTENSION(int) returns (int);
function SequenceNumber__DEVICE_EXTENSIONInv(int) returns (int);
function _S_SequenceNumber__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_SequenceNumber__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SequenceNumber__DEVICE_EXTENSIONInv(SequenceNumber__DEVICE_EXTENSION(x))} SequenceNumber__DEVICE_EXTENSIONInv(SequenceNumber__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {SequenceNumber__DEVICE_EXTENSIONInv(x)} SequenceNumber__DEVICE_EXTENSION(SequenceNumber__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SequenceNumber__DEVICE_EXTENSION(S)[x]} _S_SequenceNumber__DEVICE_EXTENSION(S)[x] <==> S[SequenceNumber__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SequenceNumber__DEVICE_EXTENSIONInv(S)[x]} _S_SequenceNumber__DEVICE_EXTENSIONInv(S)[x] <==> S[SequenceNumber__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SequenceNumber__DEVICE_EXTENSION(S)} S[x] ==> _S_SequenceNumber__DEVICE_EXTENSION(S)[SequenceNumber__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SequenceNumber__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_SequenceNumber__DEVICE_EXTENSIONInv(S)[SequenceNumber__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {SequenceNumber__DEVICE_EXTENSION(x)} SequenceNumber__DEVICE_EXTENSION(x) == x + 184);
axiom (forall x:int :: {SequenceNumber__DEVICE_EXTENSIONInv(x)} SequenceNumber__DEVICE_EXTENSIONInv(x) == x - 184);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 184, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 184, 1) == SequenceNumber__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 184)} MINUS_LEFT_PTR(x, 1, 184) == SequenceNumber__DEVICE_EXTENSIONInv(x));
function SetWmiDataBlock__WMILIB_CONTEXT(int) returns (int);
function SetWmiDataBlock__WMILIB_CONTEXTInv(int) returns (int);
function _S_SetWmiDataBlock__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_SetWmiDataBlock__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SetWmiDataBlock__WMILIB_CONTEXTInv(SetWmiDataBlock__WMILIB_CONTEXT(x))} SetWmiDataBlock__WMILIB_CONTEXTInv(SetWmiDataBlock__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {SetWmiDataBlock__WMILIB_CONTEXTInv(x)} SetWmiDataBlock__WMILIB_CONTEXT(SetWmiDataBlock__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SetWmiDataBlock__WMILIB_CONTEXT(S)[x]} _S_SetWmiDataBlock__WMILIB_CONTEXT(S)[x] <==> S[SetWmiDataBlock__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SetWmiDataBlock__WMILIB_CONTEXTInv(S)[x]} _S_SetWmiDataBlock__WMILIB_CONTEXTInv(S)[x] <==> S[SetWmiDataBlock__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SetWmiDataBlock__WMILIB_CONTEXT(S)} S[x] ==> _S_SetWmiDataBlock__WMILIB_CONTEXT(S)[SetWmiDataBlock__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SetWmiDataBlock__WMILIB_CONTEXTInv(S)} S[x] ==> _S_SetWmiDataBlock__WMILIB_CONTEXTInv(S)[SetWmiDataBlock__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {SetWmiDataBlock__WMILIB_CONTEXT(x)} SetWmiDataBlock__WMILIB_CONTEXT(x) == x + 16);
axiom (forall x:int :: {SetWmiDataBlock__WMILIB_CONTEXTInv(x)} SetWmiDataBlock__WMILIB_CONTEXTInv(x) == x - 16);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 16, 1) == SetWmiDataBlock__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 16)} MINUS_LEFT_PTR(x, 1, 16) == SetWmiDataBlock__WMILIB_CONTEXTInv(x));
function SetWmiDataItem__WMILIB_CONTEXT(int) returns (int);
function SetWmiDataItem__WMILIB_CONTEXTInv(int) returns (int);
function _S_SetWmiDataItem__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_SetWmiDataItem__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SetWmiDataItem__WMILIB_CONTEXTInv(SetWmiDataItem__WMILIB_CONTEXT(x))} SetWmiDataItem__WMILIB_CONTEXTInv(SetWmiDataItem__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {SetWmiDataItem__WMILIB_CONTEXTInv(x)} SetWmiDataItem__WMILIB_CONTEXT(SetWmiDataItem__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SetWmiDataItem__WMILIB_CONTEXT(S)[x]} _S_SetWmiDataItem__WMILIB_CONTEXT(S)[x] <==> S[SetWmiDataItem__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SetWmiDataItem__WMILIB_CONTEXTInv(S)[x]} _S_SetWmiDataItem__WMILIB_CONTEXTInv(S)[x] <==> S[SetWmiDataItem__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SetWmiDataItem__WMILIB_CONTEXT(S)} S[x] ==> _S_SetWmiDataItem__WMILIB_CONTEXT(S)[SetWmiDataItem__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SetWmiDataItem__WMILIB_CONTEXTInv(S)} S[x] ==> _S_SetWmiDataItem__WMILIB_CONTEXTInv(S)[SetWmiDataItem__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {SetWmiDataItem__WMILIB_CONTEXT(x)} SetWmiDataItem__WMILIB_CONTEXT(x) == x + 20);
axiom (forall x:int :: {SetWmiDataItem__WMILIB_CONTEXTInv(x)} SetWmiDataItem__WMILIB_CONTEXTInv(x) == x - 20);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 20, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 20, 1) == SetWmiDataItem__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 20)} MINUS_LEFT_PTR(x, 1, 20) == SetWmiDataItem__WMILIB_CONTEXTInv(x));
function SignalState__DISPATCHER_HEADER(int) returns (int);
function SignalState__DISPATCHER_HEADERInv(int) returns (int);
function _S_SignalState__DISPATCHER_HEADER([int]bool) returns ([int]bool);
function _S_SignalState__DISPATCHER_HEADERInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SignalState__DISPATCHER_HEADERInv(SignalState__DISPATCHER_HEADER(x))} SignalState__DISPATCHER_HEADERInv(SignalState__DISPATCHER_HEADER(x)) == x);
axiom (forall x:int :: {SignalState__DISPATCHER_HEADERInv(x)} SignalState__DISPATCHER_HEADER(SignalState__DISPATCHER_HEADERInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SignalState__DISPATCHER_HEADER(S)[x]} _S_SignalState__DISPATCHER_HEADER(S)[x] <==> S[SignalState__DISPATCHER_HEADERInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SignalState__DISPATCHER_HEADERInv(S)[x]} _S_SignalState__DISPATCHER_HEADERInv(S)[x] <==> S[SignalState__DISPATCHER_HEADER(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SignalState__DISPATCHER_HEADER(S)} S[x] ==> _S_SignalState__DISPATCHER_HEADER(S)[SignalState__DISPATCHER_HEADER(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SignalState__DISPATCHER_HEADERInv(S)} S[x] ==> _S_SignalState__DISPATCHER_HEADERInv(S)[SignalState__DISPATCHER_HEADERInv(x)]);
        
axiom (forall x:int :: {SignalState__DISPATCHER_HEADER(x)} SignalState__DISPATCHER_HEADER(x) == x + 4);
axiom (forall x:int :: {SignalState__DISPATCHER_HEADERInv(x)} SignalState__DISPATCHER_HEADERInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == SignalState__DISPATCHER_HEADERInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == SignalState__DISPATCHER_HEADERInv(x));
function Signalling___unnamed_1_29794256(int) returns (int);
function Signalling___unnamed_1_29794256Inv(int) returns (int);
function _S_Signalling___unnamed_1_29794256([int]bool) returns ([int]bool);
function _S_Signalling___unnamed_1_29794256Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Signalling___unnamed_1_29794256Inv(Signalling___unnamed_1_29794256(x))} Signalling___unnamed_1_29794256Inv(Signalling___unnamed_1_29794256(x)) == x);
axiom (forall x:int :: {Signalling___unnamed_1_29794256Inv(x)} Signalling___unnamed_1_29794256(Signalling___unnamed_1_29794256Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Signalling___unnamed_1_29794256(S)[x]} _S_Signalling___unnamed_1_29794256(S)[x] <==> S[Signalling___unnamed_1_29794256Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Signalling___unnamed_1_29794256Inv(S)[x]} _S_Signalling___unnamed_1_29794256Inv(S)[x] <==> S[Signalling___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Signalling___unnamed_1_29794256(S)} S[x] ==> _S_Signalling___unnamed_1_29794256(S)[Signalling___unnamed_1_29794256(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Signalling___unnamed_1_29794256Inv(S)} S[x] ==> _S_Signalling___unnamed_1_29794256Inv(S)[Signalling___unnamed_1_29794256Inv(x)]);
        
axiom (forall x:int :: {Signalling___unnamed_1_29794256(x)} Signalling___unnamed_1_29794256(x) == x + 0);
axiom (forall x:int :: {Signalling___unnamed_1_29794256Inv(x)} Signalling___unnamed_1_29794256Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Signalling___unnamed_1_29794256Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Signalling___unnamed_1_29794256Inv(x));
function Signature__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_Signature__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_Signature__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(Signature__IO_REMOVE_LOCK_DBG_BLOCK(x))} Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(Signature__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Signature__IO_REMOVE_LOCK_DBG_BLOCK(Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Signature__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_Signature__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[Signature__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Signature__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_Signature__IO_REMOVE_LOCK_DBG_BLOCK(S)[Signature__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {Signature__IO_REMOVE_LOCK_DBG_BLOCK(x)} Signature__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 0);
axiom (forall x:int :: {Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Signature__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function Size___unnamed_1_2ef8da39(int) returns (int);
function Size___unnamed_1_2ef8da39Inv(int) returns (int);
function _S_Size___unnamed_1_2ef8da39([int]bool) returns ([int]bool);
function _S_Size___unnamed_1_2ef8da39Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Size___unnamed_1_2ef8da39Inv(Size___unnamed_1_2ef8da39(x))} Size___unnamed_1_2ef8da39Inv(Size___unnamed_1_2ef8da39(x)) == x);
axiom (forall x:int :: {Size___unnamed_1_2ef8da39Inv(x)} Size___unnamed_1_2ef8da39(Size___unnamed_1_2ef8da39Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Size___unnamed_1_2ef8da39(S)[x]} _S_Size___unnamed_1_2ef8da39(S)[x] <==> S[Size___unnamed_1_2ef8da39Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Size___unnamed_1_2ef8da39Inv(S)[x]} _S_Size___unnamed_1_2ef8da39Inv(S)[x] <==> S[Size___unnamed_1_2ef8da39(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Size___unnamed_1_2ef8da39(S)} S[x] ==> _S_Size___unnamed_1_2ef8da39(S)[Size___unnamed_1_2ef8da39(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Size___unnamed_1_2ef8da39Inv(S)} S[x] ==> _S_Size___unnamed_1_2ef8da39Inv(S)[Size___unnamed_1_2ef8da39Inv(x)]);
        
axiom (forall x:int :: {Size___unnamed_1_2ef8da39(x)} Size___unnamed_1_2ef8da39(x) == x + 0);
axiom (forall x:int :: {Size___unnamed_1_2ef8da39Inv(x)} Size___unnamed_1_2ef8da39Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Size___unnamed_1_2ef8da39Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Size___unnamed_1_2ef8da39Inv(x));
function SpinLock__DEVICE_EXTENSION(int) returns (int);
function SpinLock__DEVICE_EXTENSIONInv(int) returns (int);
function _S_SpinLock__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_SpinLock__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SpinLock__DEVICE_EXTENSIONInv(SpinLock__DEVICE_EXTENSION(x))} SpinLock__DEVICE_EXTENSIONInv(SpinLock__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {SpinLock__DEVICE_EXTENSIONInv(x)} SpinLock__DEVICE_EXTENSION(SpinLock__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SpinLock__DEVICE_EXTENSION(S)[x]} _S_SpinLock__DEVICE_EXTENSION(S)[x] <==> S[SpinLock__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SpinLock__DEVICE_EXTENSIONInv(S)[x]} _S_SpinLock__DEVICE_EXTENSIONInv(S)[x] <==> S[SpinLock__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SpinLock__DEVICE_EXTENSION(S)} S[x] ==> _S_SpinLock__DEVICE_EXTENSION(S)[SpinLock__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SpinLock__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_SpinLock__DEVICE_EXTENSIONInv(S)[SpinLock__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {SpinLock__DEVICE_EXTENSION(x)} SpinLock__DEVICE_EXTENSION(x) == x + 172);
axiom (forall x:int :: {SpinLock__DEVICE_EXTENSIONInv(x)} SpinLock__DEVICE_EXTENSIONInv(x) == x - 172);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 172, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 172, 1) == SpinLock__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 172)} MINUS_LEFT_PTR(x, 1, 172) == SpinLock__DEVICE_EXTENSIONInv(x));
function Spin__IO_REMOVE_LOCK_DBG_BLOCK(int) returns (int);
function Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(int) returns (int);
function _S_Spin__IO_REMOVE_LOCK_DBG_BLOCK([int]bool) returns ([int]bool);
function _S_Spin__IO_REMOVE_LOCK_DBG_BLOCKInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(Spin__IO_REMOVE_LOCK_DBG_BLOCK(x))} Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(Spin__IO_REMOVE_LOCK_DBG_BLOCK(x)) == x);
axiom (forall x:int :: {Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Spin__IO_REMOVE_LOCK_DBG_BLOCK(Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Spin__IO_REMOVE_LOCK_DBG_BLOCK(S)[x]} _S_Spin__IO_REMOVE_LOCK_DBG_BLOCK(S)[x] <==> S[Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x]} _S_Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[x] <==> S[Spin__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Spin__IO_REMOVE_LOCK_DBG_BLOCK(S)} S[x] ==> _S_Spin__IO_REMOVE_LOCK_DBG_BLOCK(S)[Spin__IO_REMOVE_LOCK_DBG_BLOCK(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(S)} S[x] ==> _S_Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(S)[Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x)]);
        
axiom (forall x:int :: {Spin__IO_REMOVE_LOCK_DBG_BLOCK(x)} Spin__IO_REMOVE_LOCK_DBG_BLOCK(x) == x + 28);
axiom (forall x:int :: {Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x)} Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x) == x - 28);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 28, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 28, 1) == Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 28)} MINUS_LEFT_PTR(x, 1, 28) == Spin__IO_REMOVE_LOCK_DBG_BLOCKInv(x));
function Started__DEVICE_EXTENSION(int) returns (int);
function Started__DEVICE_EXTENSIONInv(int) returns (int);
function _S_Started__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_Started__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Started__DEVICE_EXTENSIONInv(Started__DEVICE_EXTENSION(x))} Started__DEVICE_EXTENSIONInv(Started__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {Started__DEVICE_EXTENSIONInv(x)} Started__DEVICE_EXTENSION(Started__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Started__DEVICE_EXTENSION(S)[x]} _S_Started__DEVICE_EXTENSION(S)[x] <==> S[Started__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Started__DEVICE_EXTENSIONInv(S)[x]} _S_Started__DEVICE_EXTENSIONInv(S)[x] <==> S[Started__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Started__DEVICE_EXTENSION(S)} S[x] ==> _S_Started__DEVICE_EXTENSION(S)[Started__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Started__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_Started__DEVICE_EXTENSIONInv(S)[Started__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {Started__DEVICE_EXTENSION(x)} Started__DEVICE_EXTENSION(x) == x + 105);
axiom (forall x:int :: {Started__DEVICE_EXTENSIONInv(x)} Started__DEVICE_EXTENSIONInv(x) == x - 105);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 105, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 105, 1) == Started__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 105)} MINUS_LEFT_PTR(x, 1, 105) == Started__DEVICE_EXTENSIONInv(x));
function Subtype__KEYBOARD_ID(int) returns (int);
function Subtype__KEYBOARD_IDInv(int) returns (int);
function _S_Subtype__KEYBOARD_ID([int]bool) returns ([int]bool);
function _S_Subtype__KEYBOARD_IDInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Subtype__KEYBOARD_IDInv(Subtype__KEYBOARD_ID(x))} Subtype__KEYBOARD_IDInv(Subtype__KEYBOARD_ID(x)) == x);
axiom (forall x:int :: {Subtype__KEYBOARD_IDInv(x)} Subtype__KEYBOARD_ID(Subtype__KEYBOARD_IDInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Subtype__KEYBOARD_ID(S)[x]} _S_Subtype__KEYBOARD_ID(S)[x] <==> S[Subtype__KEYBOARD_IDInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Subtype__KEYBOARD_IDInv(S)[x]} _S_Subtype__KEYBOARD_IDInv(S)[x] <==> S[Subtype__KEYBOARD_ID(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Subtype__KEYBOARD_ID(S)} S[x] ==> _S_Subtype__KEYBOARD_ID(S)[Subtype__KEYBOARD_ID(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Subtype__KEYBOARD_IDInv(S)} S[x] ==> _S_Subtype__KEYBOARD_IDInv(S)[Subtype__KEYBOARD_IDInv(x)]);
        
axiom (forall x:int :: {Subtype__KEYBOARD_ID(x)} Subtype__KEYBOARD_ID(x) == x + 1);
axiom (forall x:int :: {Subtype__KEYBOARD_IDInv(x)} Subtype__KEYBOARD_IDInv(x) == x - 1);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 1, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 1, 1) == Subtype__KEYBOARD_IDInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 1)} MINUS_LEFT_PTR(x, 1, 1) == Subtype__KEYBOARD_IDInv(x));
function SurpriseRemoved__DEVICE_EXTENSION(int) returns (int);
function SurpriseRemoved__DEVICE_EXTENSIONInv(int) returns (int);
function _S_SurpriseRemoved__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_SurpriseRemoved__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SurpriseRemoved__DEVICE_EXTENSIONInv(SurpriseRemoved__DEVICE_EXTENSION(x))} SurpriseRemoved__DEVICE_EXTENSIONInv(SurpriseRemoved__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {SurpriseRemoved__DEVICE_EXTENSIONInv(x)} SurpriseRemoved__DEVICE_EXTENSION(SurpriseRemoved__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SurpriseRemoved__DEVICE_EXTENSION(S)[x]} _S_SurpriseRemoved__DEVICE_EXTENSION(S)[x] <==> S[SurpriseRemoved__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SurpriseRemoved__DEVICE_EXTENSIONInv(S)[x]} _S_SurpriseRemoved__DEVICE_EXTENSIONInv(S)[x] <==> S[SurpriseRemoved__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SurpriseRemoved__DEVICE_EXTENSION(S)} S[x] ==> _S_SurpriseRemoved__DEVICE_EXTENSION(S)[SurpriseRemoved__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SurpriseRemoved__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_SurpriseRemoved__DEVICE_EXTENSIONInv(S)[SurpriseRemoved__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {SurpriseRemoved__DEVICE_EXTENSION(x)} SurpriseRemoved__DEVICE_EXTENSION(x) == x + 287);
axiom (forall x:int :: {SurpriseRemoved__DEVICE_EXTENSIONInv(x)} SurpriseRemoved__DEVICE_EXTENSIONInv(x) == x - 287);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 287, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 287, 1) == SurpriseRemoved__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 287)} MINUS_LEFT_PTR(x, 1, 287) == SurpriseRemoved__DEVICE_EXTENSIONInv(x));
function SymbolicLinkName__DEVICE_EXTENSION(int) returns (int);
function SymbolicLinkName__DEVICE_EXTENSIONInv(int) returns (int);
function _S_SymbolicLinkName__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_SymbolicLinkName__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SymbolicLinkName__DEVICE_EXTENSIONInv(SymbolicLinkName__DEVICE_EXTENSION(x))} SymbolicLinkName__DEVICE_EXTENSIONInv(SymbolicLinkName__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {SymbolicLinkName__DEVICE_EXTENSIONInv(x)} SymbolicLinkName__DEVICE_EXTENSION(SymbolicLinkName__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SymbolicLinkName__DEVICE_EXTENSION(S)[x]} _S_SymbolicLinkName__DEVICE_EXTENSION(S)[x] <==> S[SymbolicLinkName__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SymbolicLinkName__DEVICE_EXTENSIONInv(S)[x]} _S_SymbolicLinkName__DEVICE_EXTENSIONInv(S)[x] <==> S[SymbolicLinkName__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SymbolicLinkName__DEVICE_EXTENSION(S)} S[x] ==> _S_SymbolicLinkName__DEVICE_EXTENSION(S)[SymbolicLinkName__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SymbolicLinkName__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_SymbolicLinkName__DEVICE_EXTENSIONInv(S)[SymbolicLinkName__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {SymbolicLinkName__DEVICE_EXTENSION(x)} SymbolicLinkName__DEVICE_EXTENSION(x) == x + 120);
axiom (forall x:int :: {SymbolicLinkName__DEVICE_EXTENSIONInv(x)} SymbolicLinkName__DEVICE_EXTENSIONInv(x) == x - 120);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 120, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 120, 1) == SymbolicLinkName__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 120)} MINUS_LEFT_PTR(x, 1, 120) == SymbolicLinkName__DEVICE_EXTENSIONInv(x));
function SystemState__DEVICE_EXTENSION(int) returns (int);
function SystemState__DEVICE_EXTENSIONInv(int) returns (int);
function _S_SystemState__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_SystemState__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SystemState__DEVICE_EXTENSIONInv(SystemState__DEVICE_EXTENSION(x))} SystemState__DEVICE_EXTENSIONInv(SystemState__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {SystemState__DEVICE_EXTENSIONInv(x)} SystemState__DEVICE_EXTENSION(SystemState__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SystemState__DEVICE_EXTENSION(S)[x]} _S_SystemState__DEVICE_EXTENSION(S)[x] <==> S[SystemState__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SystemState__DEVICE_EXTENSIONInv(S)[x]} _S_SystemState__DEVICE_EXTENSIONInv(S)[x] <==> S[SystemState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SystemState__DEVICE_EXTENSION(S)} S[x] ==> _S_SystemState__DEVICE_EXTENSION(S)[SystemState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SystemState__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_SystemState__DEVICE_EXTENSIONInv(S)[SystemState__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {SystemState__DEVICE_EXTENSION(x)} SystemState__DEVICE_EXTENSION(x) == x + 192);
axiom (forall x:int :: {SystemState__DEVICE_EXTENSIONInv(x)} SystemState__DEVICE_EXTENSIONInv(x) == x - 192);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 192, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 192, 1) == SystemState__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 192)} MINUS_LEFT_PTR(x, 1, 192) == SystemState__DEVICE_EXTENSIONInv(x));
function SystemToDeviceState__DEVICE_EXTENSION(int) returns (int);
function SystemToDeviceState__DEVICE_EXTENSIONInv(int) returns (int);
function _S_SystemToDeviceState__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_SystemToDeviceState__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {SystemToDeviceState__DEVICE_EXTENSIONInv(SystemToDeviceState__DEVICE_EXTENSION(x))} SystemToDeviceState__DEVICE_EXTENSIONInv(SystemToDeviceState__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {SystemToDeviceState__DEVICE_EXTENSIONInv(x)} SystemToDeviceState__DEVICE_EXTENSION(SystemToDeviceState__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_SystemToDeviceState__DEVICE_EXTENSION(S)[x]} _S_SystemToDeviceState__DEVICE_EXTENSION(S)[x] <==> S[SystemToDeviceState__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_SystemToDeviceState__DEVICE_EXTENSIONInv(S)[x]} _S_SystemToDeviceState__DEVICE_EXTENSIONInv(S)[x] <==> S[SystemToDeviceState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SystemToDeviceState__DEVICE_EXTENSION(S)} S[x] ==> _S_SystemToDeviceState__DEVICE_EXTENSION(S)[SystemToDeviceState__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_SystemToDeviceState__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_SystemToDeviceState__DEVICE_EXTENSIONInv(S)[SystemToDeviceState__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {SystemToDeviceState__DEVICE_EXTENSION(x)} SystemToDeviceState__DEVICE_EXTENSION(x) == x + 232);
axiom (forall x:int :: {SystemToDeviceState__DEVICE_EXTENSIONInv(x)} SystemToDeviceState__DEVICE_EXTENSIONInv(x) == x - 232);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 232, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 232, 1) == SystemToDeviceState__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 232)} MINUS_LEFT_PTR(x, 1, 232) == SystemToDeviceState__DEVICE_EXTENSIONInv(x));
function TargetNotifyHandle__DEVICE_EXTENSION(int) returns (int);
function TargetNotifyHandle__DEVICE_EXTENSIONInv(int) returns (int);
function _S_TargetNotifyHandle__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_TargetNotifyHandle__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {TargetNotifyHandle__DEVICE_EXTENSIONInv(TargetNotifyHandle__DEVICE_EXTENSION(x))} TargetNotifyHandle__DEVICE_EXTENSIONInv(TargetNotifyHandle__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {TargetNotifyHandle__DEVICE_EXTENSIONInv(x)} TargetNotifyHandle__DEVICE_EXTENSION(TargetNotifyHandle__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_TargetNotifyHandle__DEVICE_EXTENSION(S)[x]} _S_TargetNotifyHandle__DEVICE_EXTENSION(S)[x] <==> S[TargetNotifyHandle__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_TargetNotifyHandle__DEVICE_EXTENSIONInv(S)[x]} _S_TargetNotifyHandle__DEVICE_EXTENSIONInv(S)[x] <==> S[TargetNotifyHandle__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TargetNotifyHandle__DEVICE_EXTENSION(S)} S[x] ==> _S_TargetNotifyHandle__DEVICE_EXTENSION(S)[TargetNotifyHandle__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TargetNotifyHandle__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_TargetNotifyHandle__DEVICE_EXTENSIONInv(S)[TargetNotifyHandle__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {TargetNotifyHandle__DEVICE_EXTENSION(x)} TargetNotifyHandle__DEVICE_EXTENSION(x) == x + 268);
axiom (forall x:int :: {TargetNotifyHandle__DEVICE_EXTENSIONInv(x)} TargetNotifyHandle__DEVICE_EXTENSIONInv(x) == x - 268);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 268, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 268, 1) == TargetNotifyHandle__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 268)} MINUS_LEFT_PTR(x, 1, 268) == TargetNotifyHandle__DEVICE_EXTENSIONInv(x));
function TopPort__DEVICE_EXTENSION(int) returns (int);
function TopPort__DEVICE_EXTENSIONInv(int) returns (int);
function _S_TopPort__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_TopPort__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {TopPort__DEVICE_EXTENSIONInv(TopPort__DEVICE_EXTENSION(x))} TopPort__DEVICE_EXTENSIONInv(TopPort__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {TopPort__DEVICE_EXTENSIONInv(x)} TopPort__DEVICE_EXTENSION(TopPort__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_TopPort__DEVICE_EXTENSION(S)[x]} _S_TopPort__DEVICE_EXTENSION(S)[x] <==> S[TopPort__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_TopPort__DEVICE_EXTENSIONInv(S)[x]} _S_TopPort__DEVICE_EXTENSIONInv(S)[x] <==> S[TopPort__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TopPort__DEVICE_EXTENSION(S)} S[x] ==> _S_TopPort__DEVICE_EXTENSION(S)[TopPort__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TopPort__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_TopPort__DEVICE_EXTENSIONInv(S)[TopPort__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {TopPort__DEVICE_EXTENSION(x)} TopPort__DEVICE_EXTENSION(x) == x + 8);
axiom (forall x:int :: {TopPort__DEVICE_EXTENSIONInv(x)} TopPort__DEVICE_EXTENSIONInv(x) == x - 8);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1) == TopPort__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 8)} MINUS_LEFT_PTR(x, 1, 8) == TopPort__DEVICE_EXTENSIONInv(x));
function TrueClassDevice__DEVICE_EXTENSION(int) returns (int);
function TrueClassDevice__DEVICE_EXTENSIONInv(int) returns (int);
function _S_TrueClassDevice__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_TrueClassDevice__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {TrueClassDevice__DEVICE_EXTENSIONInv(TrueClassDevice__DEVICE_EXTENSION(x))} TrueClassDevice__DEVICE_EXTENSIONInv(TrueClassDevice__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {TrueClassDevice__DEVICE_EXTENSIONInv(x)} TrueClassDevice__DEVICE_EXTENSION(TrueClassDevice__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_TrueClassDevice__DEVICE_EXTENSION(S)[x]} _S_TrueClassDevice__DEVICE_EXTENSION(S)[x] <==> S[TrueClassDevice__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_TrueClassDevice__DEVICE_EXTENSIONInv(S)[x]} _S_TrueClassDevice__DEVICE_EXTENSIONInv(S)[x] <==> S[TrueClassDevice__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TrueClassDevice__DEVICE_EXTENSION(S)} S[x] ==> _S_TrueClassDevice__DEVICE_EXTENSION(S)[TrueClassDevice__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TrueClassDevice__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_TrueClassDevice__DEVICE_EXTENSIONInv(S)[TrueClassDevice__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {TrueClassDevice__DEVICE_EXTENSION(x)} TrueClassDevice__DEVICE_EXTENSION(x) == x + 4);
axiom (forall x:int :: {TrueClassDevice__DEVICE_EXTENSIONInv(x)} TrueClassDevice__DEVICE_EXTENSIONInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == TrueClassDevice__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == TrueClassDevice__DEVICE_EXTENSIONInv(x));
function TrustedSubsystemCount__DEVICE_EXTENSION(int) returns (int);
function TrustedSubsystemCount__DEVICE_EXTENSIONInv(int) returns (int);
function _S_TrustedSubsystemCount__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_TrustedSubsystemCount__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {TrustedSubsystemCount__DEVICE_EXTENSIONInv(TrustedSubsystemCount__DEVICE_EXTENSION(x))} TrustedSubsystemCount__DEVICE_EXTENSIONInv(TrustedSubsystemCount__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {TrustedSubsystemCount__DEVICE_EXTENSIONInv(x)} TrustedSubsystemCount__DEVICE_EXTENSION(TrustedSubsystemCount__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_TrustedSubsystemCount__DEVICE_EXTENSION(S)[x]} _S_TrustedSubsystemCount__DEVICE_EXTENSION(S)[x] <==> S[TrustedSubsystemCount__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_TrustedSubsystemCount__DEVICE_EXTENSIONInv(S)[x]} _S_TrustedSubsystemCount__DEVICE_EXTENSIONInv(S)[x] <==> S[TrustedSubsystemCount__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TrustedSubsystemCount__DEVICE_EXTENSION(S)} S[x] ==> _S_TrustedSubsystemCount__DEVICE_EXTENSION(S)[TrustedSubsystemCount__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_TrustedSubsystemCount__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_TrustedSubsystemCount__DEVICE_EXTENSIONInv(S)[TrustedSubsystemCount__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {TrustedSubsystemCount__DEVICE_EXTENSION(x)} TrustedSubsystemCount__DEVICE_EXTENSION(x) == x + 112);
axiom (forall x:int :: {TrustedSubsystemCount__DEVICE_EXTENSIONInv(x)} TrustedSubsystemCount__DEVICE_EXTENSIONInv(x) == x - 112);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 112, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 112, 1) == TrustedSubsystemCount__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 112)} MINUS_LEFT_PTR(x, 1, 112) == TrustedSubsystemCount__DEVICE_EXTENSIONInv(x));
function Type__KEYBOARD_ID(int) returns (int);
function Type__KEYBOARD_IDInv(int) returns (int);
function _S_Type__KEYBOARD_ID([int]bool) returns ([int]bool);
function _S_Type__KEYBOARD_IDInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Type__KEYBOARD_IDInv(Type__KEYBOARD_ID(x))} Type__KEYBOARD_IDInv(Type__KEYBOARD_ID(x)) == x);
axiom (forall x:int :: {Type__KEYBOARD_IDInv(x)} Type__KEYBOARD_ID(Type__KEYBOARD_IDInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Type__KEYBOARD_ID(S)[x]} _S_Type__KEYBOARD_ID(S)[x] <==> S[Type__KEYBOARD_IDInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Type__KEYBOARD_IDInv(S)[x]} _S_Type__KEYBOARD_IDInv(S)[x] <==> S[Type__KEYBOARD_ID(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Type__KEYBOARD_ID(S)} S[x] ==> _S_Type__KEYBOARD_ID(S)[Type__KEYBOARD_ID(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Type__KEYBOARD_IDInv(S)} S[x] ==> _S_Type__KEYBOARD_IDInv(S)[Type__KEYBOARD_IDInv(x)]);
        
axiom (forall x:int :: {Type__KEYBOARD_ID(x)} Type__KEYBOARD_ID(x) == x + 0);
axiom (forall x:int :: {Type__KEYBOARD_IDInv(x)} Type__KEYBOARD_IDInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Type__KEYBOARD_IDInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Type__KEYBOARD_IDInv(x));
function Type___unnamed_4_5ca00198(int) returns (int);
function Type___unnamed_4_5ca00198Inv(int) returns (int);
function _S_Type___unnamed_4_5ca00198([int]bool) returns ([int]bool);
function _S_Type___unnamed_4_5ca00198Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Type___unnamed_4_5ca00198Inv(Type___unnamed_4_5ca00198(x))} Type___unnamed_4_5ca00198Inv(Type___unnamed_4_5ca00198(x)) == x);
axiom (forall x:int :: {Type___unnamed_4_5ca00198Inv(x)} Type___unnamed_4_5ca00198(Type___unnamed_4_5ca00198Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Type___unnamed_4_5ca00198(S)[x]} _S_Type___unnamed_4_5ca00198(S)[x] <==> S[Type___unnamed_4_5ca00198Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Type___unnamed_4_5ca00198Inv(S)[x]} _S_Type___unnamed_4_5ca00198Inv(S)[x] <==> S[Type___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Type___unnamed_4_5ca00198(S)} S[x] ==> _S_Type___unnamed_4_5ca00198(S)[Type___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Type___unnamed_4_5ca00198Inv(S)} S[x] ==> _S_Type___unnamed_4_5ca00198Inv(S)[Type___unnamed_4_5ca00198Inv(x)]);
        
axiom (forall x:int :: {Type___unnamed_4_5ca00198(x)} Type___unnamed_4_5ca00198(x) == x + 0);
axiom (forall x:int :: {Type___unnamed_4_5ca00198Inv(x)} Type___unnamed_4_5ca00198Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == Type___unnamed_4_5ca00198Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == Type___unnamed_4_5ca00198Inv(x));
function UnitId__DEVICE_EXTENSION(int) returns (int);
function UnitId__DEVICE_EXTENSIONInv(int) returns (int);
function _S_UnitId__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_UnitId__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {UnitId__DEVICE_EXTENSIONInv(UnitId__DEVICE_EXTENSION(x))} UnitId__DEVICE_EXTENSIONInv(UnitId__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {UnitId__DEVICE_EXTENSIONInv(x)} UnitId__DEVICE_EXTENSION(UnitId__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_UnitId__DEVICE_EXTENSION(S)[x]} _S_UnitId__DEVICE_EXTENSION(S)[x] <==> S[UnitId__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_UnitId__DEVICE_EXTENSIONInv(S)[x]} _S_UnitId__DEVICE_EXTENSIONInv(S)[x] <==> S[UnitId__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_UnitId__DEVICE_EXTENSION(S)} S[x] ==> _S_UnitId__DEVICE_EXTENSION(S)[UnitId__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_UnitId__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_UnitId__DEVICE_EXTENSIONInv(S)[UnitId__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {UnitId__DEVICE_EXTENSION(x)} UnitId__DEVICE_EXTENSION(x) == x + 196);
axiom (forall x:int :: {UnitId__DEVICE_EXTENSIONInv(x)} UnitId__DEVICE_EXTENSIONInv(x) == x - 196);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 196, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 196, 1) == UnitId__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 196)} MINUS_LEFT_PTR(x, 1, 196) == UnitId__DEVICE_EXTENSIONInv(x));
function UnitId__KEYBOARD_INDICATOR_PARAMETERS(int) returns (int);
function UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(int) returns (int);
function _S_UnitId__KEYBOARD_INDICATOR_PARAMETERS([int]bool) returns ([int]bool);
function _S_UnitId__KEYBOARD_INDICATOR_PARAMETERSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(UnitId__KEYBOARD_INDICATOR_PARAMETERS(x))} UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(UnitId__KEYBOARD_INDICATOR_PARAMETERS(x)) == x);
axiom (forall x:int :: {UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x)} UnitId__KEYBOARD_INDICATOR_PARAMETERS(UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_UnitId__KEYBOARD_INDICATOR_PARAMETERS(S)[x]} _S_UnitId__KEYBOARD_INDICATOR_PARAMETERS(S)[x] <==> S[UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(S)[x]} _S_UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(S)[x] <==> S[UnitId__KEYBOARD_INDICATOR_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_UnitId__KEYBOARD_INDICATOR_PARAMETERS(S)} S[x] ==> _S_UnitId__KEYBOARD_INDICATOR_PARAMETERS(S)[UnitId__KEYBOARD_INDICATOR_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(S)} S[x] ==> _S_UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(S)[UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x)]);
        
axiom (forall x:int :: {UnitId__KEYBOARD_INDICATOR_PARAMETERS(x)} UnitId__KEYBOARD_INDICATOR_PARAMETERS(x) == x + 0);
axiom (forall x:int :: {UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x)} UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == UnitId__KEYBOARD_INDICATOR_PARAMETERSInv(x));
function UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(int) returns (int);
function UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(int) returns (int);
function _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERS([int]bool) returns ([int]bool);
function _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(x))} UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(x)) == x);
axiom (forall x:int :: {UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)} UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(S)[x]} _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(S)[x] <==> S[UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[x]} _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[x] <==> S[UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(S)} S[x] ==> _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(S)[UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)} S[x] ==> _S_UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(S)[UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)]);
        
axiom (forall x:int :: {UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(x)} UnitId__KEYBOARD_TYPEMATIC_PARAMETERS(x) == x + 0);
axiom (forall x:int :: {UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x)} UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == UnitId__KEYBOARD_TYPEMATIC_PARAMETERSInv(x));
function WaitListHead__DISPATCHER_HEADER(int) returns (int);
function WaitListHead__DISPATCHER_HEADERInv(int) returns (int);
function _S_WaitListHead__DISPATCHER_HEADER([int]bool) returns ([int]bool);
function _S_WaitListHead__DISPATCHER_HEADERInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {WaitListHead__DISPATCHER_HEADERInv(WaitListHead__DISPATCHER_HEADER(x))} WaitListHead__DISPATCHER_HEADERInv(WaitListHead__DISPATCHER_HEADER(x)) == x);
axiom (forall x:int :: {WaitListHead__DISPATCHER_HEADERInv(x)} WaitListHead__DISPATCHER_HEADER(WaitListHead__DISPATCHER_HEADERInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_WaitListHead__DISPATCHER_HEADER(S)[x]} _S_WaitListHead__DISPATCHER_HEADER(S)[x] <==> S[WaitListHead__DISPATCHER_HEADERInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_WaitListHead__DISPATCHER_HEADERInv(S)[x]} _S_WaitListHead__DISPATCHER_HEADERInv(S)[x] <==> S[WaitListHead__DISPATCHER_HEADER(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitListHead__DISPATCHER_HEADER(S)} S[x] ==> _S_WaitListHead__DISPATCHER_HEADER(S)[WaitListHead__DISPATCHER_HEADER(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitListHead__DISPATCHER_HEADERInv(S)} S[x] ==> _S_WaitListHead__DISPATCHER_HEADERInv(S)[WaitListHead__DISPATCHER_HEADERInv(x)]);
        
axiom (forall x:int :: {WaitListHead__DISPATCHER_HEADER(x)} WaitListHead__DISPATCHER_HEADER(x) == x + 8);
axiom (forall x:int :: {WaitListHead__DISPATCHER_HEADERInv(x)} WaitListHead__DISPATCHER_HEADERInv(x) == x - 8);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1) == WaitListHead__DISPATCHER_HEADERInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 8)} MINUS_LEFT_PTR(x, 1, 8) == WaitListHead__DISPATCHER_HEADERInv(x));
function WaitWakeEnabled__DEVICE_EXTENSION(int) returns (int);
function WaitWakeEnabled__DEVICE_EXTENSIONInv(int) returns (int);
function _S_WaitWakeEnabled__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_WaitWakeEnabled__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {WaitWakeEnabled__DEVICE_EXTENSIONInv(WaitWakeEnabled__DEVICE_EXTENSION(x))} WaitWakeEnabled__DEVICE_EXTENSIONInv(WaitWakeEnabled__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {WaitWakeEnabled__DEVICE_EXTENSIONInv(x)} WaitWakeEnabled__DEVICE_EXTENSION(WaitWakeEnabled__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_WaitWakeEnabled__DEVICE_EXTENSION(S)[x]} _S_WaitWakeEnabled__DEVICE_EXTENSION(S)[x] <==> S[WaitWakeEnabled__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_WaitWakeEnabled__DEVICE_EXTENSIONInv(S)[x]} _S_WaitWakeEnabled__DEVICE_EXTENSIONInv(S)[x] <==> S[WaitWakeEnabled__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitWakeEnabled__DEVICE_EXTENSION(S)} S[x] ==> _S_WaitWakeEnabled__DEVICE_EXTENSION(S)[WaitWakeEnabled__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitWakeEnabled__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_WaitWakeEnabled__DEVICE_EXTENSIONInv(S)[WaitWakeEnabled__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {WaitWakeEnabled__DEVICE_EXTENSION(x)} WaitWakeEnabled__DEVICE_EXTENSION(x) == x + 286);
axiom (forall x:int :: {WaitWakeEnabled__DEVICE_EXTENSIONInv(x)} WaitWakeEnabled__DEVICE_EXTENSIONInv(x) == x - 286);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 286, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 286, 1) == WaitWakeEnabled__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 286)} MINUS_LEFT_PTR(x, 1, 286) == WaitWakeEnabled__DEVICE_EXTENSIONInv(x));
function WaitWakeIrp__DEVICE_EXTENSION(int) returns (int);
function WaitWakeIrp__DEVICE_EXTENSIONInv(int) returns (int);
function _S_WaitWakeIrp__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_WaitWakeIrp__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {WaitWakeIrp__DEVICE_EXTENSIONInv(WaitWakeIrp__DEVICE_EXTENSION(x))} WaitWakeIrp__DEVICE_EXTENSIONInv(WaitWakeIrp__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {WaitWakeIrp__DEVICE_EXTENSIONInv(x)} WaitWakeIrp__DEVICE_EXTENSION(WaitWakeIrp__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_WaitWakeIrp__DEVICE_EXTENSION(S)[x]} _S_WaitWakeIrp__DEVICE_EXTENSION(S)[x] <==> S[WaitWakeIrp__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_WaitWakeIrp__DEVICE_EXTENSIONInv(S)[x]} _S_WaitWakeIrp__DEVICE_EXTENSIONInv(S)[x] <==> S[WaitWakeIrp__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitWakeIrp__DEVICE_EXTENSION(S)} S[x] ==> _S_WaitWakeIrp__DEVICE_EXTENSION(S)[WaitWakeIrp__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitWakeIrp__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_WaitWakeIrp__DEVICE_EXTENSIONInv(S)[WaitWakeIrp__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {WaitWakeIrp__DEVICE_EXTENSION(x)} WaitWakeIrp__DEVICE_EXTENSION(x) == x + 260);
axiom (forall x:int :: {WaitWakeIrp__DEVICE_EXTENSIONInv(x)} WaitWakeIrp__DEVICE_EXTENSIONInv(x) == x - 260);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 260, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 260, 1) == WaitWakeIrp__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 260)} MINUS_LEFT_PTR(x, 1, 260) == WaitWakeIrp__DEVICE_EXTENSIONInv(x));
function WaitWakeSpinLock__DEVICE_EXTENSION(int) returns (int);
function WaitWakeSpinLock__DEVICE_EXTENSIONInv(int) returns (int);
function _S_WaitWakeSpinLock__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_WaitWakeSpinLock__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {WaitWakeSpinLock__DEVICE_EXTENSIONInv(WaitWakeSpinLock__DEVICE_EXTENSION(x))} WaitWakeSpinLock__DEVICE_EXTENSIONInv(WaitWakeSpinLock__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {WaitWakeSpinLock__DEVICE_EXTENSIONInv(x)} WaitWakeSpinLock__DEVICE_EXTENSION(WaitWakeSpinLock__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_WaitWakeSpinLock__DEVICE_EXTENSION(S)[x]} _S_WaitWakeSpinLock__DEVICE_EXTENSION(S)[x] <==> S[WaitWakeSpinLock__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_WaitWakeSpinLock__DEVICE_EXTENSIONInv(S)[x]} _S_WaitWakeSpinLock__DEVICE_EXTENSIONInv(S)[x] <==> S[WaitWakeSpinLock__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitWakeSpinLock__DEVICE_EXTENSION(S)} S[x] ==> _S_WaitWakeSpinLock__DEVICE_EXTENSION(S)[WaitWakeSpinLock__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WaitWakeSpinLock__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_WaitWakeSpinLock__DEVICE_EXTENSIONInv(S)[WaitWakeSpinLock__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {WaitWakeSpinLock__DEVICE_EXTENSION(x)} WaitWakeSpinLock__DEVICE_EXTENSION(x) == x + 108);
axiom (forall x:int :: {WaitWakeSpinLock__DEVICE_EXTENSIONInv(x)} WaitWakeSpinLock__DEVICE_EXTENSIONInv(x) == x - 108);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 108, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 108, 1) == WaitWakeSpinLock__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 108)} MINUS_LEFT_PTR(x, 1, 108) == WaitWakeSpinLock__DEVICE_EXTENSIONInv(x));
function WmiFunctionControl__WMILIB_CONTEXT(int) returns (int);
function WmiFunctionControl__WMILIB_CONTEXTInv(int) returns (int);
function _S_WmiFunctionControl__WMILIB_CONTEXT([int]bool) returns ([int]bool);
function _S_WmiFunctionControl__WMILIB_CONTEXTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {WmiFunctionControl__WMILIB_CONTEXTInv(WmiFunctionControl__WMILIB_CONTEXT(x))} WmiFunctionControl__WMILIB_CONTEXTInv(WmiFunctionControl__WMILIB_CONTEXT(x)) == x);
axiom (forall x:int :: {WmiFunctionControl__WMILIB_CONTEXTInv(x)} WmiFunctionControl__WMILIB_CONTEXT(WmiFunctionControl__WMILIB_CONTEXTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_WmiFunctionControl__WMILIB_CONTEXT(S)[x]} _S_WmiFunctionControl__WMILIB_CONTEXT(S)[x] <==> S[WmiFunctionControl__WMILIB_CONTEXTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_WmiFunctionControl__WMILIB_CONTEXTInv(S)[x]} _S_WmiFunctionControl__WMILIB_CONTEXTInv(S)[x] <==> S[WmiFunctionControl__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WmiFunctionControl__WMILIB_CONTEXT(S)} S[x] ==> _S_WmiFunctionControl__WMILIB_CONTEXT(S)[WmiFunctionControl__WMILIB_CONTEXT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WmiFunctionControl__WMILIB_CONTEXTInv(S)} S[x] ==> _S_WmiFunctionControl__WMILIB_CONTEXTInv(S)[WmiFunctionControl__WMILIB_CONTEXTInv(x)]);
        
axiom (forall x:int :: {WmiFunctionControl__WMILIB_CONTEXT(x)} WmiFunctionControl__WMILIB_CONTEXT(x) == x + 28);
axiom (forall x:int :: {WmiFunctionControl__WMILIB_CONTEXTInv(x)} WmiFunctionControl__WMILIB_CONTEXTInv(x) == x - 28);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 28, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 28, 1) == WmiFunctionControl__WMILIB_CONTEXTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 28)} MINUS_LEFT_PTR(x, 1, 28) == WmiFunctionControl__WMILIB_CONTEXTInv(x));
function WmiLibInfo__DEVICE_EXTENSION(int) returns (int);
function WmiLibInfo__DEVICE_EXTENSIONInv(int) returns (int);
function _S_WmiLibInfo__DEVICE_EXTENSION([int]bool) returns ([int]bool);
function _S_WmiLibInfo__DEVICE_EXTENSIONInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {WmiLibInfo__DEVICE_EXTENSIONInv(WmiLibInfo__DEVICE_EXTENSION(x))} WmiLibInfo__DEVICE_EXTENSIONInv(WmiLibInfo__DEVICE_EXTENSION(x)) == x);
axiom (forall x:int :: {WmiLibInfo__DEVICE_EXTENSIONInv(x)} WmiLibInfo__DEVICE_EXTENSION(WmiLibInfo__DEVICE_EXTENSIONInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_WmiLibInfo__DEVICE_EXTENSION(S)[x]} _S_WmiLibInfo__DEVICE_EXTENSION(S)[x] <==> S[WmiLibInfo__DEVICE_EXTENSIONInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_WmiLibInfo__DEVICE_EXTENSIONInv(S)[x]} _S_WmiLibInfo__DEVICE_EXTENSIONInv(S)[x] <==> S[WmiLibInfo__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WmiLibInfo__DEVICE_EXTENSION(S)} S[x] ==> _S_WmiLibInfo__DEVICE_EXTENSION(S)[WmiLibInfo__DEVICE_EXTENSION(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_WmiLibInfo__DEVICE_EXTENSIONInv(S)} S[x] ==> _S_WmiLibInfo__DEVICE_EXTENSIONInv(S)[WmiLibInfo__DEVICE_EXTENSIONInv(x)]);
        
axiom (forall x:int :: {WmiLibInfo__DEVICE_EXTENSION(x)} WmiLibInfo__DEVICE_EXTENSION(x) == x + 200);
axiom (forall x:int :: {WmiLibInfo__DEVICE_EXTENSIONInv(x)} WmiLibInfo__DEVICE_EXTENSIONInv(x) == x - 200);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 200, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 200, 1) == WmiLibInfo__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 200)} MINUS_LEFT_PTR(x, 1, 200) == WmiLibInfo__DEVICE_EXTENSIONInv(x));
function __unnamed_1_29794256___unnamed_4_5ca00198(int) returns (int);
function __unnamed_1_29794256___unnamed_4_5ca00198Inv(int) returns (int);
function _S___unnamed_1_29794256___unnamed_4_5ca00198([int]bool) returns ([int]bool);
function _S___unnamed_1_29794256___unnamed_4_5ca00198Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {__unnamed_1_29794256___unnamed_4_5ca00198Inv(__unnamed_1_29794256___unnamed_4_5ca00198(x))} __unnamed_1_29794256___unnamed_4_5ca00198Inv(__unnamed_1_29794256___unnamed_4_5ca00198(x)) == x);
axiom (forall x:int :: {__unnamed_1_29794256___unnamed_4_5ca00198Inv(x)} __unnamed_1_29794256___unnamed_4_5ca00198(__unnamed_1_29794256___unnamed_4_5ca00198Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S___unnamed_1_29794256___unnamed_4_5ca00198(S)[x]} _S___unnamed_1_29794256___unnamed_4_5ca00198(S)[x] <==> S[__unnamed_1_29794256___unnamed_4_5ca00198Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S___unnamed_1_29794256___unnamed_4_5ca00198Inv(S)[x]} _S___unnamed_1_29794256___unnamed_4_5ca00198Inv(S)[x] <==> S[__unnamed_1_29794256___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_1_29794256___unnamed_4_5ca00198(S)} S[x] ==> _S___unnamed_1_29794256___unnamed_4_5ca00198(S)[__unnamed_1_29794256___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_1_29794256___unnamed_4_5ca00198Inv(S)} S[x] ==> _S___unnamed_1_29794256___unnamed_4_5ca00198Inv(S)[__unnamed_1_29794256___unnamed_4_5ca00198Inv(x)]);
        
axiom (forall x:int :: {__unnamed_1_29794256___unnamed_4_5ca00198(x)} __unnamed_1_29794256___unnamed_4_5ca00198(x) == x + 1);
axiom (forall x:int :: {__unnamed_1_29794256___unnamed_4_5ca00198Inv(x)} __unnamed_1_29794256___unnamed_4_5ca00198Inv(x) == x - 1);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 1, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 1, 1) == __unnamed_1_29794256___unnamed_4_5ca00198Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 1)} MINUS_LEFT_PTR(x, 1, 1) == __unnamed_1_29794256___unnamed_4_5ca00198Inv(x));
function __unnamed_1_2dc63b48___unnamed_4_5ca00198(int) returns (int);
function __unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(int) returns (int);
function _S___unnamed_1_2dc63b48___unnamed_4_5ca00198([int]bool) returns ([int]bool);
function _S___unnamed_1_2dc63b48___unnamed_4_5ca00198Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {__unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(__unnamed_1_2dc63b48___unnamed_4_5ca00198(x))} __unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(__unnamed_1_2dc63b48___unnamed_4_5ca00198(x)) == x);
axiom (forall x:int :: {__unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x)} __unnamed_1_2dc63b48___unnamed_4_5ca00198(__unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S___unnamed_1_2dc63b48___unnamed_4_5ca00198(S)[x]} _S___unnamed_1_2dc63b48___unnamed_4_5ca00198(S)[x] <==> S[__unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S___unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(S)[x]} _S___unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(S)[x] <==> S[__unnamed_1_2dc63b48___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_1_2dc63b48___unnamed_4_5ca00198(S)} S[x] ==> _S___unnamed_1_2dc63b48___unnamed_4_5ca00198(S)[__unnamed_1_2dc63b48___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(S)} S[x] ==> _S___unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(S)[__unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x)]);
        
axiom (forall x:int :: {__unnamed_1_2dc63b48___unnamed_4_5ca00198(x)} __unnamed_1_2dc63b48___unnamed_4_5ca00198(x) == x + 3);
axiom (forall x:int :: {__unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x)} __unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x) == x - 3);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 3, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 3, 1) == __unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 3)} MINUS_LEFT_PTR(x, 1, 3) == __unnamed_1_2dc63b48___unnamed_4_5ca00198Inv(x));
function __unnamed_1_2ef8da39___unnamed_4_5ca00198(int) returns (int);
function __unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(int) returns (int);
function _S___unnamed_1_2ef8da39___unnamed_4_5ca00198([int]bool) returns ([int]bool);
function _S___unnamed_1_2ef8da39___unnamed_4_5ca00198Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {__unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(__unnamed_1_2ef8da39___unnamed_4_5ca00198(x))} __unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(__unnamed_1_2ef8da39___unnamed_4_5ca00198(x)) == x);
axiom (forall x:int :: {__unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x)} __unnamed_1_2ef8da39___unnamed_4_5ca00198(__unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S___unnamed_1_2ef8da39___unnamed_4_5ca00198(S)[x]} _S___unnamed_1_2ef8da39___unnamed_4_5ca00198(S)[x] <==> S[__unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S___unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(S)[x]} _S___unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(S)[x] <==> S[__unnamed_1_2ef8da39___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_1_2ef8da39___unnamed_4_5ca00198(S)} S[x] ==> _S___unnamed_1_2ef8da39___unnamed_4_5ca00198(S)[__unnamed_1_2ef8da39___unnamed_4_5ca00198(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(S)} S[x] ==> _S___unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(S)[__unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x)]);
        
axiom (forall x:int :: {__unnamed_1_2ef8da39___unnamed_4_5ca00198(x)} __unnamed_1_2ef8da39___unnamed_4_5ca00198(x) == x + 2);
axiom (forall x:int :: {__unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x)} __unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x) == x - 2);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 2, 1) == __unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 2)} MINUS_LEFT_PTR(x, 1, 2) == __unnamed_1_2ef8da39___unnamed_4_5ca00198Inv(x));
function __unnamed_4_5ca00198___unnamed_4_a97c65a1(int) returns (int);
function __unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(int) returns (int);
function _S___unnamed_4_5ca00198___unnamed_4_a97c65a1([int]bool) returns ([int]bool);
function _S___unnamed_4_5ca00198___unnamed_4_a97c65a1Inv([int]bool) returns ([int]bool);

axiom (forall x:int :: {__unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(__unnamed_4_5ca00198___unnamed_4_a97c65a1(x))} __unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(__unnamed_4_5ca00198___unnamed_4_a97c65a1(x)) == x);
axiom (forall x:int :: {__unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x)} __unnamed_4_5ca00198___unnamed_4_a97c65a1(__unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S___unnamed_4_5ca00198___unnamed_4_a97c65a1(S)[x]} _S___unnamed_4_5ca00198___unnamed_4_a97c65a1(S)[x] <==> S[__unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x)]);
axiom (forall x:int, S:[int]bool :: {_S___unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(S)[x]} _S___unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(S)[x] <==> S[__unnamed_4_5ca00198___unnamed_4_a97c65a1(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_4_5ca00198___unnamed_4_a97c65a1(S)} S[x] ==> _S___unnamed_4_5ca00198___unnamed_4_a97c65a1(S)[__unnamed_4_5ca00198___unnamed_4_a97c65a1(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(S)} S[x] ==> _S___unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(S)[__unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x)]);
        
axiom (forall x:int :: {__unnamed_4_5ca00198___unnamed_4_a97c65a1(x)} __unnamed_4_5ca00198___unnamed_4_a97c65a1(x) == x + 0);
axiom (forall x:int :: {__unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x)} __unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == __unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == __unnamed_4_5ca00198___unnamed_4_a97c65a1Inv(x));
function __unnamed_4_a97c65a1__DISPATCHER_HEADER(int) returns (int);
function __unnamed_4_a97c65a1__DISPATCHER_HEADERInv(int) returns (int);
function _S___unnamed_4_a97c65a1__DISPATCHER_HEADER([int]bool) returns ([int]bool);
function _S___unnamed_4_a97c65a1__DISPATCHER_HEADERInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {__unnamed_4_a97c65a1__DISPATCHER_HEADERInv(__unnamed_4_a97c65a1__DISPATCHER_HEADER(x))} __unnamed_4_a97c65a1__DISPATCHER_HEADERInv(__unnamed_4_a97c65a1__DISPATCHER_HEADER(x)) == x);
axiom (forall x:int :: {__unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x)} __unnamed_4_a97c65a1__DISPATCHER_HEADER(__unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S___unnamed_4_a97c65a1__DISPATCHER_HEADER(S)[x]} _S___unnamed_4_a97c65a1__DISPATCHER_HEADER(S)[x] <==> S[__unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S___unnamed_4_a97c65a1__DISPATCHER_HEADERInv(S)[x]} _S___unnamed_4_a97c65a1__DISPATCHER_HEADERInv(S)[x] <==> S[__unnamed_4_a97c65a1__DISPATCHER_HEADER(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_4_a97c65a1__DISPATCHER_HEADER(S)} S[x] ==> _S___unnamed_4_a97c65a1__DISPATCHER_HEADER(S)[__unnamed_4_a97c65a1__DISPATCHER_HEADER(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S___unnamed_4_a97c65a1__DISPATCHER_HEADERInv(S)} S[x] ==> _S___unnamed_4_a97c65a1__DISPATCHER_HEADERInv(S)[__unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x)]);
        
axiom (forall x:int :: {__unnamed_4_a97c65a1__DISPATCHER_HEADER(x)} __unnamed_4_a97c65a1__DISPATCHER_HEADER(x) == x + 0);
axiom (forall x:int :: {__unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x)} __unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == __unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == __unnamed_4_a97c65a1__DISPATCHER_HEADERInv(x));
function MINUS_BOTH_PTR_OR_BOTH_INT(a:int, b:int, size:int) returns (int); 
axiom  (forall a:int, b:int, size:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)} 
size * MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size) <= a - b && a - b < size * (MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size) + 1));

function MINUS_LEFT_PTR(a:int, a_size:int, b:int) returns (int);
axiom(forall a:int, a_size:int, b:int :: {MINUS_LEFT_PTR(a,a_size,b)} MINUS_LEFT_PTR(a,a_size,b) == a - a_size * b);

function PLUS(a:int, a_size:int, b:int) returns (int);
axiom (forall a:int, a_size:int, b:int :: {PLUS(a,a_size,b)} PLUS(a,a_size,b) == a + a_size * b);

function MULT(a:int, b:int) returns (int); // a*b
axiom(forall a:int, b:int :: {MULT(a,b)} MULT(a,b) == a * b);

function DIV(a:int, b:int) returns (int); // a/b	
	      
axiom(forall a:int, b:int :: {DIV(a,b)}
a >= 0 && b > 0 ==> b * DIV(a,b) <= a && a < b * (DIV(a,b) + 1)
); 

axiom(forall a:int, b:int :: {DIV(a,b)}
a >= 0 && b < 0 ==> b * DIV(a,b) <= a && a < b * (DIV(a,b) - 1)
); 

axiom(forall a:int, b:int :: {DIV(a,b)}
a < 0 && b > 0 ==> b * DIV(a,b) >= a && a > b * (DIV(a,b) - 1)
); 

axiom(forall a:int, b:int :: {DIV(a,b)}
a < 0 && b < 0 ==> b * DIV(a,b) >= a && a > b * (DIV(a,b) + 1)
); 

function BINARY_BOTH_INT(a:int, b:int) returns (int);

function POW2(a:int) returns (bool);
axiom POW2(1);
axiom POW2(2);
axiom POW2(4);
axiom POW2(8);
axiom POW2(16);
axiom POW2(32);
axiom POW2(64);
axiom POW2(128);
axiom POW2(256);
axiom POW2(512);
axiom POW2(1024);
axiom POW2(2048);
axiom POW2(4096);
axiom POW2(8192);
axiom POW2(16384);
axiom POW2(32768);
axiom POW2(65536);
axiom POW2(131072);
axiom POW2(262144);
axiom POW2(524288);
axiom POW2(1048576);
axiom POW2(2097152);
axiom POW2(4194304);
axiom POW2(8388608);
axiom POW2(16777216);
axiom POW2(33554432);

function choose(a:bool, b:int, c:int) returns (x:int);
axiom(forall a:bool, b:int, c:int :: {choose(a,b,c)} a ==> choose(a,b,c) == b);
axiom(forall a:bool, b:int, c:int :: {choose(a,b,c)} !a ==> choose(a,b,c) == c);

function BIT_BAND(a:int, b:int) returns (x:int);
axiom(forall a:int, b:int :: {BIT_BAND(a,b)} a == b ==> BIT_BAND(a,b) == a);
axiom(forall a:int, b:int :: {BIT_BAND(a,b)} POW2(a) && POW2(b) && a != b ==> BIT_BAND(a,b) == 0);
axiom(forall a:int, b:int :: {BIT_BAND(a,b)} a == 0 || b == 0 ==> BIT_BAND(a,b) == 0);

function BIT_BOR(a:int, b:int) returns (x:int);

function BIT_BXOR(a:int, b:int) returns (x:int);

function BIT_BNOT(a:int) returns (int);

function LIFT(a:bool) returns (int);
axiom(forall a:bool :: {LIFT(a)} a <==> LIFT(a) != 0);

function NOT(a:int) returns (int);
axiom(forall a:int :: {NOT(a)} a == 0 ==> NOT(a) != 0);
axiom(forall a:int :: {NOT(a)} a != 0 ==> NOT(a) == 0);

function NULL_CHECK(a:int) returns (int);
axiom(forall a:int :: {NULL_CHECK(a)} a == 0 ==> NULL_CHECK(a) != 0);
axiom(forall a:int :: {NULL_CHECK(a)} a != 0 ==> NULL_CHECK(a) == 0);




procedure havoc_assert(i:int);
requires (i != 0);

procedure havoc_assume(i:int);
ensures (i != 0);

procedure __HAVOC_free(a:int);
modifies alloc;
ensures (forall x:int :: {alloc[x]} x == a || old(alloc)[x] == alloc[x]);
ensures (alloc[a] == FREED);
// Additional checks guarded by tranlator flags
// requires alloc[a] == ALLOCATED;
// requires Base(a) == a;

procedure __HAVOC_malloc(obj_size:int) returns (new:int);
requires obj_size >= 0;
modifies alloc;
ensures (new > 0);
ensures (forall x:int :: {Base(x)} new <= x && x < new+obj_size ==> Base(x) == new);
ensures (forall x:int :: {alloc[x]} x == new || old(alloc)[x] == alloc[x]);
ensures old(alloc)[new] == UNALLOCATED && alloc[new] == ALLOCATED;

procedure nondet_choice() returns (x:int);

procedure _strdup(str:int) returns (new:int);

procedure _xstrcasecmp(a0:int, a1:int) returns (ret:int);

procedure _xstrcmp(a0:int, a1:int) returns (ret:int);

var Res_DEVICE_STACK:[int]int;
var Res_DEV_EXTN:[int]int;
var Res_DEV_OBJ_INIT:[int]int;
var Res_SPIN_LOCK:[int]int;



////////////////////
// Between predicate
//////////////////// 
function ReachBetween(f: [int]int, x: int, y: int, z: int) returns (bool);
function ReachAvoiding(f: [int]int, x: int, y: int, z: int) returns (bool);


//////////////////////////
// Between set constructor
//////////////////////////
function ReachBetweenSet(f: [int]int, x: int, z: int) returns ([int]bool);

////////////////////////////////////////////////////
// axioms relating ReachBetween and ReachBetweenSet
////////////////////////////////////////////////////
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetweenSet(f, x, z)[y]} ReachBetweenSet(f, x, z)[y] <==> ReachBetween(f, x, y, z));
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, z), ReachBetweenSet(f, x, z)} ReachBetween(f, x, y, z) ==> ReachBetweenSet(f, x, z)[y]);
axiom(forall f: [int]int, x: int, z: int :: {ReachBetweenSet(f, x, z)} ReachBetween(f, x, x, x));


//////////////////////////
// Axioms for ReachBetween
//////////////////////////

// reflexive
axiom(forall f: [int]int, x: int :: ReachBetween(f, x, x, x));

// step
//axiom(forall f: [int]int, x: int :: {f[x]} ReachBetween(f, x, f[x], f[x])); 
axiom(forall f: [int]int, x: int, y: int, z: int, w:int :: {ReachBetween(f, y, z, w), f[x]} ReachBetween(f, x, f[x], f[x])); 

// reach
axiom(forall f: [int]int, x: int, y: int :: {f[x], ReachBetween(f, x, y, y)} ReachBetween(f, x, y, y) ==> x == y || ReachBetween(f, x, f[x], y));

// cycle
axiom(forall f: [int]int, x: int, y:int :: {f[x], ReachBetween(f, x, y, y)} f[x] == x && ReachBetween(f, x, y, y) ==> x == y);

// sandwich
axiom(forall f: [int]int, x: int, y: int :: {ReachBetween(f, x, y, x)} ReachBetween(f, x, y, x) ==> x == y);

// order1
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, y), ReachBetween(f, x, z, z)} ReachBetween(f, x, y, y) && ReachBetween(f, x, z, z) ==> ReachBetween(f, x, y, z) || ReachBetween(f, x, z, y));

// order2
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, z)} ReachBetween(f, x, y, z) ==> ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z));

// transitive1
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachBetween(f, x, y, y), ReachBetween(f, y, z, z)} ReachBetween(f, x, y, y) && ReachBetween(f, y, z, z) ==> ReachBetween(f, x, z, z));

// transitive2
axiom(forall f: [int]int, x: int, y: int, z: int, w: int :: {ReachBetween(f, x, y, z), ReachBetween(f, y, w, z)} ReachBetween(f, x, y, z) && ReachBetween(f, y, w, z) ==> ReachBetween(f, x, y, w) && ReachBetween(f, x, w, z));

// transitive3
axiom(forall f: [int]int, x: int, y: int, z: int, w: int :: {ReachBetween(f, x, y, z), ReachBetween(f, x, w, y)} ReachBetween(f, x, y, z) && ReachBetween(f, x, w, y) ==> ReachBetween(f, x, w, z) && ReachBetween(f, w, y, z));

// This axiom is required to deal with the incompleteness of the trigger for the reflexive axiom.  
// It cannot be proved using the rest of the axioms.
axiom(forall f: [int]int, u:int, x: int :: {ReachBetween(f, u, x, x)} ReachBetween(f, u, x, x) ==> ReachBetween(f, u, u, x));

// relation between ReachAvoiding and ReachBetween
axiom(forall f: [int]int, x: int, y: int, z: int :: {ReachAvoiding(f, x, y, z)}{ReachBetween(f, x, y, z)} ReachAvoiding(f, x, y, z) <==> (ReachBetween(f, x, y, z) || (ReachBetween(f, x, y, y) && !ReachBetween(f, x, z, z))));

// update
axiom(forall f: [int]int, u: int, v: int, x: int, p: int, q: int :: {ReachAvoiding(f[p := q], u, v, x)} ReachAvoiding(f[p := q], u, v, x) <==> ((ReachAvoiding(f, u, v, p) && ReachAvoiding(f, u, v, x)) || (ReachAvoiding(f, u, p, x) && p != x && ReachAvoiding(f, q, v, p) && ReachAvoiding(f, q, v, x))));
 ///////////////////////////////
 // Shifts for linking fields   
 ///////////////////////////////
function Shift_Flink__LIST_ENTRY(f: [int]int) returns ([int]int);
axiom( forall f: [int]int, __x:int :: {f[Flink__LIST_ENTRY(__x)],Shift_Flink__LIST_ENTRY(f)} {Shift_Flink__LIST_ENTRY(f)[__x]} Shift_Flink__LIST_ENTRY(f)[__x] == f[Flink__LIST_ENTRY(__x)]);
axiom(forall f: [int]int, __x:int, __v:int :: {Shift_Flink__LIST_ENTRY(f[Flink__LIST_ENTRY(__x) := __v])} Shift_Flink__LIST_ENTRY(f[Flink__LIST_ENTRY(__x) := __v]) == Shift_Flink__LIST_ENTRY(f)[__x := __v]);

const unique Globals : int;
axiom(Globals != 0);
// the set of constants for 64 bit integers that Boogie doesn't parse
const unique BOOGIE_LARGE_INT_4294967273:int;



procedure ExAcquireFastMutex($FastMutex$1$15000.16$ExAcquireFastMutex$41:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure ExAllocatePoolWithTag($PoolType$1$14789.57$ExAllocatePoolWithTag$121:int, $NumberOfBytes$2$14790.16$ExAllocatePoolWithTag$121:int, $Tag$3$14791.15$ExAllocatePoolWithTag$121:int) returns ($result.ExAllocatePoolWithTag$14788.0$1$:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure ExFreePoolWithTag($P$1$14901.35$ExFreePoolWithTag$81:int, $Tag$2$14902.15$ExFreePoolWithTag$81:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure ExReleaseFastMutex($FastMutex$1$15013.16$ExReleaseFastMutex$41:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure InitializeListHead_IRP($ListHead$1$12.44$InitializeListHead_IRP$41:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure IoCreateDevice($DriverObject$1$21226.25$IoCreateDevice$281:int, $DeviceExtensionSize$2$21227.16$IoCreateDevice$281:int, $DeviceName$3$21228.29$IoCreateDevice$281:int, $DeviceType$4$21229.22$IoCreateDevice$281:int, $DeviceCharacteristics$5$21230.16$IoCreateDevice$281:int, $Exclusive$6$21231.18$IoCreateDevice$281:int, $DeviceObject$7$21237.20$IoCreateDevice$281:int) returns ($result.IoCreateDevice$21225.0$1$:int);

//TAG: ensures (LONG)__return >= 0 ==> *DeviceObject != (void *)0
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> (Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281] != 0));
//TAG: ensures (LONG)__return >= 0 ==> (*DeviceObject)->DeviceExtension != (void *)0
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])] != 0));
//TAG: ensures (LONG)__return >= 0 ==> __resource("DEV_EXTN", (*DeviceObject)->DeviceExtension) == 1
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])]] == 1));
//TAG: ensures (LONG)__return >= 0 ==> __resource("DEV_OBJ_INIT", *DeviceObject) == 1 && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*DeviceObject))->DeviceExtension)) == 1
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> ((Res_DEV_OBJ_INIT[Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281]] == 1) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])]] == 1)));
//TAG: ensures (LONG)__return >= 0 ==> __old_resource("DEV_OBJ_INIT", *DeviceObject) == 0 && __old_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*DeviceObject))->DeviceExtension)) == 0
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> ((old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281]] == 0) && (old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])]] == 0)));
//TAG: ensures (LONG)__return >= 0 ==> __updates_resource("DEV_OBJ_INIT", *DeviceObject, 1) && __updates_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*DeviceObject))->DeviceExtension), 1)
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281] := 1]) && (Res_DEV_EXTN == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])] := 1])));
//TAG: ensures !((LONG)__return >= 0) ==> __resource("DEV_OBJ_INIT", *DeviceObject) == __old_resource("DEV_OBJ_INIT", *DeviceObject) && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*DeviceObject))->DeviceExtension)) == __old_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*DeviceObject))->DeviceExtension))
ensures((!($result.IoCreateDevice$21225.0$1$ >= 0)) ==> ((Res_DEV_OBJ_INIT[Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281]] == old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281]]) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])]] == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])]])));
//TAG: ensures !((LONG)__return >= 0) ==> __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
free ensures((!($result.IoCreateDevice$21225.0$1$ >= 0)) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN))));
//TAG: ensures (LONG)__return >= 0 ==> !(__resource("DEV_OBJ_INIT", ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*DeviceObject))->DeviceExtension))->Self) == 1)
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> (!(Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])])]] == 1)));
//TAG: ensures !((LONG)__return >= 0) ==> *DeviceObject == __old(*DeviceObject)
ensures((!($result.IoCreateDevice$21225.0$1$ >= 0)) ==> (Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281] == old(Mem)[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281]));
//TAG: ensures __preserves_field_map(__offset((*((struct _LIST_ENTRY *)0)).Flink))
ensures(Mem[T.Flink__LIST_ENTRY] == old(Mem)[T.Flink__LIST_ENTRY]);
//TAG: ensures (LONG)__return >= 0 ==> __return == 0
ensures(($result.IoCreateDevice$21225.0$1$ >= 0) ==> ($result.IoCreateDevice$21225.0$1$ == 0));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*DeviceObject))->DeviceExtension)
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])]))) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281])] == r) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty, *DeviceObject
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton(Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281]))) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || (Mem[T.P_DEVICE_OBJECT][$DeviceObject$7$21237.20$IoCreateDevice$281] == r) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty, DeviceObject
ensures   (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton($DeviceObject$7$21237.20$IoCreateDevice$281))) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || (_m == $DeviceObject$7$21237.20$IoCreateDevice$281) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure IoDeleteDevice($DeviceObject$1$21328.67$IoDeleteDevice$41:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: requires 1 ==> __resource("DEV_OBJ_INIT", DeviceObject) == 1 && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)DeviceObject)->DeviceExtension)) == 1
requires((true) ==> ((Res_DEV_OBJ_INIT[$DeviceObject$1$21328.67$IoDeleteDevice$41] == 1) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT($DeviceObject$1$21328.67$IoDeleteDevice$41)]] == 1)));
//TAG: ensures 1 ==> __resource("DEV_OBJ_INIT", DeviceObject) == 0 && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)DeviceObject)->DeviceExtension)) == 0
ensures((true) ==> ((Res_DEV_OBJ_INIT[$DeviceObject$1$21328.67$IoDeleteDevice$41] == 0) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT($DeviceObject$1$21328.67$IoDeleteDevice$41)]] == 0)));
//TAG: ensures 1 ==> __updates_resource("DEV_OBJ_INIT", DeviceObject, 0) && __updates_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)DeviceObject)->DeviceExtension), 0)
ensures((true) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)[$DeviceObject$1$21328.67$IoDeleteDevice$41 := 0]) && (Res_DEV_EXTN == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT($DeviceObject$1$21328.67$IoDeleteDevice$41)] := 0])));
//TAG: ensures !1 ==> __resource("DEV_OBJ_INIT", DeviceObject) == __old_resource("DEV_OBJ_INIT", DeviceObject) && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)DeviceObject)->DeviceExtension)) == __old_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)DeviceObject)->DeviceExtension))
ensures((!(true)) ==> ((Res_DEV_OBJ_INIT[$DeviceObject$1$21328.67$IoDeleteDevice$41] == old(Res_DEV_OBJ_INIT)[$DeviceObject$1$21328.67$IoDeleteDevice$41]) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT($DeviceObject$1$21328.67$IoDeleteDevice$41)]] == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT($DeviceObject$1$21328.67$IoDeleteDevice$41)]])));
//TAG: ensures !1 ==> __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
free ensures((!(true)) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN))));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)DeviceObject)->DeviceExtension)
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT($DeviceObject$1$21328.67$IoDeleteDevice$41)]))) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT($DeviceObject$1$21328.67$IoDeleteDevice$41)] == r) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty, DeviceObject
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton($DeviceObject$1$21328.67$IoDeleteDevice$41))) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || ($DeviceObject$1$21328.67$IoDeleteDevice$41 == r) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure IoInitializeRemoveLockEx($Lock$1$22135.25$IoInitializeRemoveLockEx$201:int, $AllocateTag$2$22136.16$IoInitializeRemoveLockEx$201:int, $MaxLockedMinutes$3$22137.16$IoInitializeRemoveLockEx$201:int, $HighWatermark$4$22138.16$IoInitializeRemoveLockEx$201:int, $RemlockSize$5$22139.16$IoInitializeRemoveLockEx$201:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure KbdInitializeDataQueue($Context$1$557.13$KbdInitializeDataQueue$41:int);

//TAG: requires __resource("DEV_EXTN", Context) == 1
requires(Res_DEV_EXTN[$Context$1$557.13$KbdInitializeDataQueue$41] == 1);
//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
requires((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires __forall(_H_z, __inv_resource("DEV_EXTN", 1), 1)
requires((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> (true))));
//TAG: requires 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
requires((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: requires 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
requires((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: requires 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
requires((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: requires 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
requires((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __resource("DEV_EXTN", Context) == 1
ensures(Res_DEV_EXTN[$Context$1$557.13$KbdInitializeDataQueue$41] == 1);
//TAG: ensures __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
ensures((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: ensures __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
ensures((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: ensures __forall(_H_z, __inv_resource("DEV_EXTN", 1), 1)
ensures((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> (true))));
//TAG: ensures 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
ensures((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: ensures 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
ensures((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: ensures 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
ensures((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: ensures 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
ensures((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __preserves_field_map(__offset((*((struct _LIST_ENTRY *)0)).Flink))
ensures(Mem[T.Flink__LIST_ENTRY] == old(Mem)[T.Flink__LIST_ENTRY]);
//TAG: ensures __preserves_resource("DEV_OBJ_INIT")
ensures(Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT));
//TAG: ensures __preserves_resource("DEV_EXTN")
ensures(Res_DEV_EXTN == old(Res_DEV_EXTN));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure KeInitializeSpinLock($SpinLock$1$13860.22$KeInitializeSpinLock$41:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure KeyboardClassLogError($Object$1$580.10$KeyboardClassLogError$281:int, $ErrorCode$2$581.10$KeyboardClassLogError$281:int, $UniqueErrorValue$3$582.10$KeyboardClassLogError$281:int, $FinalStatus$4$583.13$KeyboardClassLogError$281:int, $DumpCount$5$584.10$KeyboardClassLogError$281:int, $DumpData$6$585.11$KeyboardClassLogError$281:int, $MajorFunction$7$586.10$KeyboardClassLogError$281:int);

//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
requires((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires __forall(_H_z, __inv_resource("DEV_EXTN", 1), 1)
requires((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> (true))));
//TAG: requires 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
requires((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: requires 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
requires((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: requires 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
requires((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: requires 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
requires((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
ensures((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: ensures __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
ensures((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: ensures __forall(_H_z, __inv_resource("DEV_EXTN", 1), 1)
ensures((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> (true))));
//TAG: ensures 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
ensures((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: ensures 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
ensures((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: ensures 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
ensures((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: ensures 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
ensures((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __preserves_field_map(__offset((*((struct _LIST_ENTRY *)0)).Flink))
ensures(Mem[T.Flink__LIST_ENTRY] == old(Mem)[T.Flink__LIST_ENTRY]);
//TAG: ensures __preserves_resource("DEV_OBJ_INIT")
ensures(Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT));
//TAG: ensures __preserves_resource("DEV_EXTN")
ensures(Res_DEV_EXTN == old(Res_DEV_EXTN));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure RtlAppendUnicodeToString($Destination$1$7421.28$RtlAppendUnicodeToString$81:int, $Source$2$7422.20$RtlAppendUnicodeToString$81:int) returns ($result.RtlAppendUnicodeToString$7420.0$1$:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure RtlFreeUnicodeString($UnicodeString$1$7452.28$RtlFreeUnicodeString$41:int);

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure __PREfastPagedCode();

//TAG: ensures __preserves_mem
ensures(Mem == old(Mem));
//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure  KbdCreateClassObject($DriverObject$1$3354.28$KbdCreateClassObject$201:int, $TmpDeviceExtension$2$3355.28$KbdCreateClassObject$201:int, $ClassDeviceObject$3$3356.28$KbdCreateClassObject$201:int, $FullDeviceName$4$3357.35$KbdCreateClassObject$201:int, $Legacy$5$3358.28$KbdCreateClassObject$201:int) returns ($result.KbdCreateClassObject$3353.0$1$:int)

//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
requires((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires __forall(_H_z, __inv_resource("DEV_EXTN", 1), 1)
requires((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> (true))));
//TAG: requires 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
requires((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: requires 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
requires((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: requires 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
requires((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: requires 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
requires((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
ensures((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: ensures __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
ensures((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: ensures __forall(_H_z, __inv_resource("DEV_EXTN", 1), 1)
ensures((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> (true))));
//TAG: ensures 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
ensures((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: ensures 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
ensures((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: ensures 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
ensures((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: ensures 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
ensures((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __preserves_field_map(__offset((*((struct _LIST_ENTRY *)0)).Flink))
ensures(Mem[T.Flink__LIST_ENTRY] == old(Mem)[T.Flink__LIST_ENTRY]);
//TAG: ensures (LONG)__return >= 0 ==> *ClassDeviceObject != (void *)0
ensures(($result.KbdCreateClassObject$3353.0$1$ >= 0) ==> (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201] != 0));
//TAG: ensures (LONG)__return >= 0 ==> (*ClassDeviceObject)->DeviceExtension != (void *)0
ensures(($result.KbdCreateClassObject$3353.0$1$ >= 0) ==> (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])] != 0));
//TAG: ensures (LONG)__return >= 0 ==> __resource("DEV_EXTN", (*ClassDeviceObject)->DeviceExtension) == 1
ensures(($result.KbdCreateClassObject$3353.0$1$ >= 0) ==> (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])]] == 1));
//TAG: ensures (LONG)__return >= 0 ==> __resource("DEV_OBJ_INIT", *ClassDeviceObject) == 1 && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)) == 1
ensures(($result.KbdCreateClassObject$3353.0$1$ >= 0) ==> ((Res_DEV_OBJ_INIT[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201]] == 1) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])]] == 1)));
//TAG: ensures (LONG)__return >= 0 ==> __old_resource("DEV_OBJ_INIT", *ClassDeviceObject) == 0 && __old_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)) == 0
ensures(($result.KbdCreateClassObject$3353.0$1$ >= 0) ==> ((old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201]] == 0) && (old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])]] == 0)));
//TAG: ensures (LONG)__return >= 0 ==> __updates_resource("DEV_OBJ_INIT", *ClassDeviceObject, 1) && __updates_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension), 1)
ensures(($result.KbdCreateClassObject$3353.0$1$ >= 0) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201] := 1]) && (Res_DEV_EXTN == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])] := 1])));
//TAG: ensures !((LONG)__return >= 0) ==> __resource("DEV_OBJ_INIT", *ClassDeviceObject) == __old_resource("DEV_OBJ_INIT", *ClassDeviceObject) && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)) == __old_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension))
ensures((!($result.KbdCreateClassObject$3353.0$1$ >= 0)) ==> ((Res_DEV_OBJ_INIT[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201]] == old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201]]) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])]] == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])]])));
//TAG: ensures !((LONG)__return >= 0) ==> __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
free ensures((!($result.KbdCreateClassObject$3353.0$1$ >= 0)) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN))));
modifies alloc;
free ensures(forall f:int :: {alloc[Base(f)]} old(alloc)[Base(f)] == UNALLOCATED || old(alloc)[Base(f)] == alloc[Base(f)]);

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])]))) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201])] == r) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty, *ClassDeviceObject
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201]))) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201] == r) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_true
ensures   (Subset(Empty(), Union(Empty(), SetTrue())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (SetTrue()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty, ClassDeviceObject
ensures   (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton($ClassDeviceObject$3$3356.28$KbdCreateClassObject$201))) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || (_m == $ClassDeviceObject$3$3356.28$KbdCreateClassObject$201) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;
{
var havoc_stringTemp:int;
var condVal:int;
var $ClassDeviceObject$3$3356.28$KbdCreateClassObject$20 : int;
var $DriverObject$1$3354.28$KbdCreateClassObject$20 : int;
var $ExAllocatePoolWithTag.arg.2$4$ : int;
var $FullDeviceName$4$3357.35$KbdCreateClassObject$20 : int;
var $KbdDebugPrint.arg.2$15$ : int;
var $KbdDebugPrint.arg.2$18$ : int;
var $KbdDebugPrint.arg.2$2$ : int;
var $KbdDebugPrint.arg.2$20$ : int;
var $KbdDebugPrint.arg.2$22$ : int;
var $KbdDebugPrint.arg.2$5$ : int;
var $Legacy$5$3358.28$KbdCreateClassObject$20 : int;
var $RtlAppendUnicodeToString.arg.2$12$ : int;
var $RtlAppendUnicodeToString.arg.2$14$ : int;
var $RtlAppendUnicodeToString.arg.2$9$ : int;
var $TmpDeviceExtension$2$3355.28$KbdCreateClassObject$20 : int;
var $deviceExtension$8$3388.24$KbdCreateClassObject$20 : int;
var $dumpCount$11$3391.24$KbdCreateClassObject$20 : int;
var $dumpData$12$3392.24$KbdCreateClassObject$20 : int;
var $errorCode$9$3389.24$KbdCreateClassObject$20 : int;
var $fullClassName$10$3390.24$KbdCreateClassObject$20 : int;
var $i$13$3393.24$KbdCreateClassObject$20 : int;
var $memset.arg.3$7$ : int;
var $nameIndex$14$3394.24$KbdCreateClassObject$20 : int;
var $result.ExAllocatePoolWithTag$3441.0$3$ : int;
var $result.ExAllocatePoolWithTag$3557.0$19$ : int;
var $result.IoCreateDevice$3485.35$16$ : int;
var $result.IoCreateDevice$3499.31$17$ : int;
var $result.RtlAppendUnicodeToString$3460.32$8$ : int;
var $result.RtlAppendUnicodeToString$3461.32$10$ : int;
var $result.RtlAppendUnicodeToString$3464.36$11$ : int;
var $result.RtlAppendUnicodeToString$3467.32$13$ : int;
var $result.memset$3459.8$6$ : int;
var $result.question.21$ : int;
var $status$6$3386.24$KbdCreateClassObject$20 : int;
var $uniqueErrorValue$7$3387.24$KbdCreateClassObject$20 : int;
var tempBoogie0:int;
var tempBoogie1:int;
var tempBoogie2:int;
var tempBoogie3:int;
var tempBoogie4:int;
var tempBoogie5:int;
var tempBoogie6:int;
var tempBoogie7:int;
var tempBoogie8:int;
var tempBoogie9:int;
var tempBoogie10:int;
var tempBoogie11:int;
var tempBoogie12:int;
var tempBoogie13:int;
var tempBoogie14:int;
var tempBoogie15:int;
var tempBoogie16:int;
var tempBoogie17:int;
var tempBoogie18:int;
var tempBoogie19:int;
var LOOP_78_alloc:[int]name;
var LOOP_78_Mem:[name][int]int;
var LOOP_78_Res_DEVICE_STACK:[int]int;
var LOOP_78_Res_DEV_EXTN:[int]int;
var LOOP_78_Res_DEV_OBJ_INIT:[int]int;
var LOOP_78_Res_SPIN_LOCK:[int]int;


start:

assume (alloc[$DriverObject$1$3354.28$KbdCreateClassObject$201] != UNALLOCATED);
assume (alloc[$TmpDeviceExtension$2$3355.28$KbdCreateClassObject$201] != UNALLOCATED);
assume (alloc[$ClassDeviceObject$3$3356.28$KbdCreateClassObject$201] != UNALLOCATED);
assume (alloc[$FullDeviceName$4$3357.35$KbdCreateClassObject$201] != UNALLOCATED);
call $dumpData$12$3392.24$KbdCreateClassObject$20 := __HAVOC_malloc(16);
call $fullClassName$10$3390.24$KbdCreateClassObject$20 := __HAVOC_malloc(8);
$DriverObject$1$3354.28$KbdCreateClassObject$20 := $DriverObject$1$3354.28$KbdCreateClassObject$201;
$TmpDeviceExtension$2$3355.28$KbdCreateClassObject$20 := $TmpDeviceExtension$2$3355.28$KbdCreateClassObject$201;
$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20 := $ClassDeviceObject$3$3356.28$KbdCreateClassObject$201;
$FullDeviceName$4$3357.35$KbdCreateClassObject$20 := $FullDeviceName$4$3357.35$KbdCreateClassObject$201;
$Legacy$5$3358.28$KbdCreateClassObject$20 := $Legacy$5$3358.28$KbdCreateClassObject$201;
goto label_3;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3627)
label_1:
call __HAVOC_free($dumpData$12$3392.24$KbdCreateClassObject$20);
call __HAVOC_free($fullClassName$10$3390.24$KbdCreateClassObject$20);
assume (forall m:int:: {Res_DEVICE_STACK[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_DEVICE_STACK[m] == old(Res_DEVICE_STACK)[m]);
assume (forall m:int:: {Res_DEV_EXTN[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_DEV_EXTN[m] == old(Res_DEV_EXTN)[m]);
assume (forall m:int:: {Res_DEV_OBJ_INIT[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_DEV_OBJ_INIT[m] == old(Res_DEV_OBJ_INIT)[m]);
assume (forall m:int:: {Res_SPIN_LOCK[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_SPIN_LOCK[m] == old(Res_SPIN_LOCK)[m]);
assume (forall m:int :: {Mem[T.A2UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A2UINT2][m] == old(Mem[T.A2UINT2])[m]);
assume (forall m:int :: {Mem[T.A37CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A37CHAR][m] == old(Mem[T.A37CHAR])[m]);
assume (forall m:int :: {Mem[T.A40CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A40CHAR][m] == old(Mem[T.A40CHAR])[m]);
assume (forall m:int :: {Mem[T.A4UINT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A4UINT4][m] == old(Mem[T.A4UINT4])[m]);
assume (forall m:int :: {Mem[T.A65CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A65CHAR][m] == old(Mem[T.A65CHAR])[m]);
assume (forall m:int :: {Mem[T.A75CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A75CHAR][m] == old(Mem[T.A75CHAR])[m]);
assume (forall m:int :: {Mem[T.A76CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A76CHAR][m] == old(Mem[T.A76CHAR])[m]);
assume (forall m:int :: {Mem[T.A7UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A7UINT2][m] == old(Mem[T.A7UINT2])[m]);
assume (forall m:int :: {Mem[T.A83CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A83CHAR][m] == old(Mem[T.A83CHAR])[m]);
assume (forall m:int :: {Mem[T.A9UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A9UINT2][m] == old(Mem[T.A9UINT2])[m]);
assume (forall m:int :: {Mem[T.Abandoned___unnamed_1_29794256][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Abandoned___unnamed_1_29794256][m] == old(Mem[T.Abandoned___unnamed_1_29794256])[m]);
assume (forall m:int :: {Mem[T.Absolute___unnamed_1_29794256][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Absolute___unnamed_1_29794256][m] == old(Mem[T.Absolute___unnamed_1_29794256])[m]);
assume (forall m:int :: {Mem[T.AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.AllocateTag__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.AllowDisable__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.AllowDisable__DEVICE_EXTENSION][m] == old(Mem[T.AllowDisable__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.BaseClassName__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.BaseClassName__GLOBALS][m] == old(Mem[T.BaseClassName__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.Blink__LIST_ENTRY][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Blink__LIST_ENTRY][m] == old(Mem[T.Blink__LIST_ENTRY])[m]);
assume (forall m:int :: {Mem[T.Blocks__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Blocks__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.Blocks__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.Buffer__UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Buffer__UNICODE_STRING][m] == old(Mem[T.Buffer__UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.ConnectOneClassToOnePort__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.ConnectOneClassToOnePort__GLOBALS][m] == old(Mem[T.ConnectOneClassToOnePort__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][m] == old(Mem[T.CurrentStackLocation___unnamed_4_f19b65c1])[m]);
assume (forall m:int :: {Mem[T.DataIn__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DataIn__DEVICE_EXTENSION][m] == old(Mem[T.DataIn__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.DataOut__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DataOut__DEVICE_EXTENSION][m] == old(Mem[T.DataOut__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.DebugActive___unnamed_1_2dc63b48][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DebugActive___unnamed_1_2dc63b48][m] == old(Mem[T.DebugActive___unnamed_1_2dc63b48])[m]);
assume (forall m:int :: {Mem[T.Delay__KEYBOARD_TYPEMATIC_PARAMETERS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Delay__KEYBOARD_TYPEMATIC_PARAMETERS][m] == old(Mem[T.Delay__KEYBOARD_TYPEMATIC_PARAMETERS])[m]);
assume (forall m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DeviceExtension__DEVICE_OBJECT][m] == old(Mem[T.DeviceExtension__DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.DeviceState__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DeviceState__DEVICE_EXTENSION][m] == old(Mem[T.DeviceState__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.DpcActive___unnamed_1_2dc63b48][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DpcActive___unnamed_1_2dc63b48][m] == old(Mem[T.DpcActive___unnamed_1_2dc63b48])[m]);
assume (forall m:int :: {Mem[T.Enabled__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Enabled__DEVICE_EXTENSION][m] == old(Mem[T.Enabled__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.ExecuteWmiMethod__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.ExecuteWmiMethod__WMILIB_CONTEXT][m] == old(Mem[T.ExecuteWmiMethod__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T.ExtraWaitWakeIrp__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.ExtraWaitWakeIrp__DEVICE_EXTENSION][m] == old(Mem[T.ExtraWaitWakeIrp__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.File__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.File__DEVICE_EXTENSION][m] == old(Mem[T.File__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Flags__DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Flags__DEVICE_OBJECT][m] == old(Mem[T.Flags__DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.Flink__LIST_ENTRY][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Flink__LIST_ENTRY][m] == old(Mem[T.Flink__LIST_ENTRY])[m]);
assume (forall m:int :: {Mem[T.GrandMaster__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.GrandMaster__GLOBALS][m] == old(Mem[T.GrandMaster__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.GuidCount__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.GuidCount__WMILIB_CONTEXT][m] == old(Mem[T.GuidCount__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T.GuidList__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.GuidList__WMILIB_CONTEXT][m] == old(Mem[T.GuidList__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T.Hand___unnamed_1_2ef8da39][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Hand___unnamed_1_2ef8da39][m] == old(Mem[T.Hand___unnamed_1_2ef8da39])[m]);
assume (forall m:int :: {Mem[T.HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.HighWatermark__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.INT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.INT4][m] == old(Mem[T.INT4])[m]);
assume (forall m:int :: {Mem[T.InputCount__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.InputCount__DEVICE_EXTENSION][m] == old(Mem[T.InputCount__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.InputDataQueueLength__KEYBOARD_ATTRIBUTES][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.InputDataQueueLength__KEYBOARD_ATTRIBUTES][m] == old(Mem[T.InputDataQueueLength__KEYBOARD_ATTRIBUTES])[m]);
assume (forall m:int :: {Mem[T.InputData__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.InputData__DEVICE_EXTENSION][m] == old(Mem[T.InputData__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Inserted___unnamed_1_2dc63b48][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Inserted___unnamed_1_2dc63b48][m] == old(Mem[T.Inserted___unnamed_1_2dc63b48])[m]);
assume (forall m:int :: {Mem[T.IoCount__IO_REMOVE_LOCK_COMMON_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.IoCount__IO_REMOVE_LOCK_COMMON_BLOCK][m] == old(Mem[T.IoCount__IO_REMOVE_LOCK_COMMON_BLOCK])[m]);
assume (forall m:int :: {Mem[T.KeyboardAttributes__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.KeyboardAttributes__DEVICE_EXTENSION][m] == old(Mem[T.KeyboardAttributes__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.KeyboardMode__KEYBOARD_ATTRIBUTES][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.KeyboardMode__KEYBOARD_ATTRIBUTES][m] == old(Mem[T.KeyboardMode__KEYBOARD_ATTRIBUTES])[m]);
assume (forall m:int :: {Mem[T.LedFlags__KEYBOARD_INDICATOR_PARAMETERS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.LedFlags__KEYBOARD_INDICATOR_PARAMETERS][m] == old(Mem[T.LedFlags__KEYBOARD_INDICATOR_PARAMETERS])[m]);
assume (forall m:int :: {Mem[T.LegacyDeviceList__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.LegacyDeviceList__GLOBALS][m] == old(Mem[T.LegacyDeviceList__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.Length__UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Length__UNICODE_STRING][m] == old(Mem[T.Length__UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.Link__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Link__DEVICE_EXTENSION][m] == old(Mem[T.Link__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Lock___unnamed_4_a97c65a1][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Lock___unnamed_4_a97c65a1][m] == old(Mem[T.Lock___unnamed_4_a97c65a1])[m]);
assume (forall m:int :: {Mem[T.LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.LowMemoryCount__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.MaxLockedTicks__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.MaximumLength__UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.MaximumLength__UNICODE_STRING][m] == old(Mem[T.MaximumLength__UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.MinDeviceWakeState__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.MinDeviceWakeState__DEVICE_EXTENSION][m] == old(Mem[T.MinDeviceWakeState__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.MinSystemWakeState__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.MinSystemWakeState__DEVICE_EXTENSION][m] == old(Mem[T.MinSystemWakeState__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.MinorFunction__IO_STACK_LOCATION][m] == old(Mem[T.MinorFunction__IO_STACK_LOCATION])[m]);
assume (forall m:int :: {Mem[T.Mutex__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Mutex__GLOBALS][m] == old(Mem[T.Mutex__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.NpxIrql___unnamed_1_29794256][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.NpxIrql___unnamed_1_29794256][m] == old(Mem[T.NpxIrql___unnamed_1_29794256])[m]);
assume (forall m:int :: {Mem[T.NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES][m] == old(Mem[T.NumberOfFunctionKeys__KEYBOARD_ATTRIBUTES])[m]);
assume (forall m:int :: {Mem[T.NumberOfIndicators__KEYBOARD_ATTRIBUTES][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.NumberOfIndicators__KEYBOARD_ATTRIBUTES][m] == old(Mem[T.NumberOfIndicators__KEYBOARD_ATTRIBUTES])[m]);
assume (forall m:int :: {Mem[T.NumberOfKeysTotal__KEYBOARD_ATTRIBUTES][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.NumberOfKeysTotal__KEYBOARD_ATTRIBUTES][m] == old(Mem[T.NumberOfKeysTotal__KEYBOARD_ATTRIBUTES])[m]);
assume (forall m:int :: {Mem[T.OkayToLogOverflow__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.OkayToLogOverflow__DEVICE_EXTENSION][m] == old(Mem[T.OkayToLogOverflow__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.PCHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PCHAR][m] == old(Mem[T.PCHAR])[m]);
assume (forall m:int :: {Mem[T.PDO__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PDO__DEVICE_EXTENSION][m] == old(Mem[T.PDO__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.PUINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PUINT2][m] == old(Mem[T.PUINT2])[m]);
assume (forall m:int :: {Mem[T.PUINT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PUINT4][m] == old(Mem[T.PUINT4])[m]);
assume (forall m:int :: {Mem[T.PVOID][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PVOID][m] == old(Mem[T.PVOID])[m]);
assume (forall m:int :: {Mem[T.P_DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_DEVICE_EXTENSION][m] == old(Mem[T.P_DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.P_DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_DEVICE_OBJECT][m] == old(Mem[T.P_DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.P_DRIVER_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_DRIVER_OBJECT][m] == old(Mem[T.P_DRIVER_OBJECT])[m]);
assume (forall m:int :: {Mem[T.P_FAST_MUTEX][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_FAST_MUTEX][m] == old(Mem[T.P_FAST_MUTEX])[m]);
assume (forall m:int :: {Mem[T.P_IO_REMOVE_LOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_IO_REMOVE_LOCK][m] == old(Mem[T.P_IO_REMOVE_LOCK])[m]);
assume (forall m:int :: {Mem[T.P_KEYBOARD_INPUT_DATA][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_KEYBOARD_INPUT_DATA][m] == old(Mem[T.P_KEYBOARD_INPUT_DATA])[m]);
assume (forall m:int :: {Mem[T.P_LIST_ENTRY][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_LIST_ENTRY][m] == old(Mem[T.P_LIST_ENTRY])[m]);
assume (forall m:int :: {Mem[T.P_UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_UNICODE_STRING][m] == old(Mem[T.P_UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.PnP__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PnP__DEVICE_EXTENSION][m] == old(Mem[T.PnP__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.QueryWmiDataBlock__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.QueryWmiDataBlock__WMILIB_CONTEXT][m] == old(Mem[T.QueryWmiDataBlock__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T.QueryWmiRegInfo__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.QueryWmiRegInfo__WMILIB_CONTEXT][m] == old(Mem[T.QueryWmiRegInfo__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T.Rate__KEYBOARD_TYPEMATIC_PARAMETERS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Rate__KEYBOARD_TYPEMATIC_PARAMETERS][m] == old(Mem[T.Rate__KEYBOARD_TYPEMATIC_PARAMETERS])[m]);
assume (forall m:int :: {Mem[T.ReadQueue__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.ReadQueue__DEVICE_EXTENSION][m] == old(Mem[T.ReadQueue__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.RemoveLock__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.RemoveLock__DEVICE_EXTENSION][m] == old(Mem[T.RemoveLock__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Removed__IO_REMOVE_LOCK_COMMON_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Removed__IO_REMOVE_LOCK_COMMON_BLOCK][m] == old(Mem[T.Removed__IO_REMOVE_LOCK_COMMON_BLOCK])[m]);
assume (forall m:int :: {Mem[T.Reserved1__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Reserved1__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.Reserved1__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.Reserved2__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Reserved2__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.Reserved2__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.Reserved__IO_REMOVE_LOCK_COMMON_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Reserved__IO_REMOVE_LOCK_COMMON_BLOCK][m] == old(Mem[T.Reserved__IO_REMOVE_LOCK_COMMON_BLOCK])[m]);
assume (forall m:int :: {Mem[T.Self__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Self__DEVICE_EXTENSION][m] == old(Mem[T.Self__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.SequenceNumber__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SequenceNumber__DEVICE_EXTENSION][m] == old(Mem[T.SequenceNumber__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.SetWmiDataBlock__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SetWmiDataBlock__WMILIB_CONTEXT][m] == old(Mem[T.SetWmiDataBlock__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T.SetWmiDataItem__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SetWmiDataItem__WMILIB_CONTEXT][m] == old(Mem[T.SetWmiDataItem__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T.SignalState__DISPATCHER_HEADER][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SignalState__DISPATCHER_HEADER][m] == old(Mem[T.SignalState__DISPATCHER_HEADER])[m]);
assume (forall m:int :: {Mem[T.Signalling___unnamed_1_29794256][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Signalling___unnamed_1_29794256][m] == old(Mem[T.Signalling___unnamed_1_29794256])[m]);
assume (forall m:int :: {Mem[T.Signature__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Signature__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.Signature__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.Size___unnamed_1_2ef8da39][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Size___unnamed_1_2ef8da39][m] == old(Mem[T.Size___unnamed_1_2ef8da39])[m]);
assume (forall m:int :: {Mem[T.SpinLock__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SpinLock__DEVICE_EXTENSION][m] == old(Mem[T.SpinLock__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Spin__IO_REMOVE_LOCK_DBG_BLOCK][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Spin__IO_REMOVE_LOCK_DBG_BLOCK][m] == old(Mem[T.Spin__IO_REMOVE_LOCK_DBG_BLOCK])[m]);
assume (forall m:int :: {Mem[T.Started__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Started__DEVICE_EXTENSION][m] == old(Mem[T.Started__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Subtype__KEYBOARD_ID][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Subtype__KEYBOARD_ID][m] == old(Mem[T.Subtype__KEYBOARD_ID])[m]);
assume (forall m:int :: {Mem[T.SurpriseRemoved__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SurpriseRemoved__DEVICE_EXTENSION][m] == old(Mem[T.SurpriseRemoved__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.SystemState__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SystemState__DEVICE_EXTENSION][m] == old(Mem[T.SystemState__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.SystemToDeviceState__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SystemToDeviceState__DEVICE_EXTENSION][m] == old(Mem[T.SystemToDeviceState__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.TargetNotifyHandle__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.TargetNotifyHandle__DEVICE_EXTENSION][m] == old(Mem[T.TargetNotifyHandle__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.TopPort__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.TopPort__DEVICE_EXTENSION][m] == old(Mem[T.TopPort__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.TrueClassDevice__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.TrueClassDevice__DEVICE_EXTENSION][m] == old(Mem[T.TrueClassDevice__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.TrustedSubsystemCount__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.TrustedSubsystemCount__DEVICE_EXTENSION][m] == old(Mem[T.TrustedSubsystemCount__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Type__KEYBOARD_ID][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Type__KEYBOARD_ID][m] == old(Mem[T.Type__KEYBOARD_ID])[m]);
assume (forall m:int :: {Mem[T.Type___unnamed_4_5ca00198][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Type___unnamed_4_5ca00198][m] == old(Mem[T.Type___unnamed_4_5ca00198])[m]);
assume (forall m:int :: {Mem[T.UCHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UCHAR][m] == old(Mem[T.UCHAR])[m]);
assume (forall m:int :: {Mem[T.UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UINT2][m] == old(Mem[T.UINT2])[m]);
assume (forall m:int :: {Mem[T.UINT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UINT4][m] == old(Mem[T.UINT4])[m]);
assume (forall m:int :: {Mem[T.UnitId__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UnitId__DEVICE_EXTENSION][m] == old(Mem[T.UnitId__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.UnitId__KEYBOARD_INDICATOR_PARAMETERS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UnitId__KEYBOARD_INDICATOR_PARAMETERS][m] == old(Mem[T.UnitId__KEYBOARD_INDICATOR_PARAMETERS])[m]);
assume (forall m:int :: {Mem[T.UnitId__KEYBOARD_TYPEMATIC_PARAMETERS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UnitId__KEYBOARD_TYPEMATIC_PARAMETERS][m] == old(Mem[T.UnitId__KEYBOARD_TYPEMATIC_PARAMETERS])[m]);
assume (forall m:int :: {Mem[T.WaitWakeEnabled__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.WaitWakeEnabled__DEVICE_EXTENSION][m] == old(Mem[T.WaitWakeEnabled__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.WaitWakeIrp__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.WaitWakeIrp__DEVICE_EXTENSION][m] == old(Mem[T.WaitWakeIrp__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.WaitWakeSpinLock__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.WaitWakeSpinLock__DEVICE_EXTENSION][m] == old(Mem[T.WaitWakeSpinLock__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.WmiFunctionControl__WMILIB_CONTEXT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.WmiFunctionControl__WMILIB_CONTEXT][m] == old(Mem[T.WmiFunctionControl__WMILIB_CONTEXT])[m]);
assume (forall m:int :: {Mem[T._POOL_TYPE][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T._POOL_TYPE][m] == old(Mem[T._POOL_TYPE])[m]);
return;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3627)
label_2:
assume false;
return;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3386)
label_3:
goto label_4;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3387)
label_4:
goto label_5;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3388)
label_5:
goto label_6;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3388)
label_6:
$deviceExtension$8$3388.24$KbdCreateClassObject$20 := 0 ;
goto label_7;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3389)
label_7:
goto label_8;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3389)
label_8:
$errorCode$9$3389.24$KbdCreateClassObject$20 := 0 ;
goto label_9;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3390)
label_9:
goto label_10;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3390)
label_10:
// Skipping Structure assignment due to the flag SkipStructAssignments
goto label_11;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3391)
label_11:
goto label_12;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3391)
label_12:
$dumpCount$11$3391.24$KbdCreateClassObject$20 := 0 ;
goto label_13;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3392)
label_13:
goto label_14;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3393)
label_14:
goto label_15;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3394)
label_15:
goto label_16;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3396)
label_16:
call __PREfastPagedCode ();
goto label_22;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3398)
label_19:
// skip KbdDebugPrint
goto label_23;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3398)
label_22:
call havoc_stringTemp := __HAVOC_malloc(1);
$KbdDebugPrint.arg.2$2$ := havoc_stringTemp ;
goto label_19;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3404)
label_23:
call ExAcquireFastMutex (Mutex__GLOBALS(Globals));
goto label_26;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3409)
label_26:
Mem[T.P_DEVICE_OBJECT] := Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20 := 0];
goto label_27;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3411)
label_27:
goto label_27_true , label_27_false ;


label_27_true :
assume (Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0);
goto label_89;


label_27_false :
assume (Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] == 0);
goto label_28;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3415)
label_28:
call ExReleaseFastMutex (Mutex__GLOBALS(Globals));
goto label_31;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3421)
label_31:
goto label_31_true , label_31_false ;


label_31_true :
assume (BOOGIE_LARGE_INT_4294967273 < Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING(BaseClassName__GLOBALS(Globals))]);
goto label_32;


label_31_false :
assume !(BOOGIE_LARGE_INT_4294967273 < Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING(BaseClassName__GLOBALS(Globals))]);
goto label_37;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3422)
label_32:
$status$6$3386.24$KbdCreateClassObject$20 := -1073741823 ;
goto label_33;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3423)
label_33:
$errorCode$9$3389.24$KbdCreateClassObject$20 := -1073414143 ;
goto label_34;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3424)
label_34:
$uniqueErrorValue$7$3387.24$KbdCreateClassObject$20 := 10006 ;
goto label_35;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3425)
label_35:
Mem[T.UINT4] := Mem[T.UINT4][PLUS($dumpData$12$3392.24$KbdCreateClassObject$20, 4, 0) := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)]];
goto label_36;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3426)
label_36:
$dumpCount$11$3391.24$KbdCreateClassObject$20 := 1 ;
goto label_136;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3433)
label_37:
Mem[T.MaximumLength__UNICODE_STRING] := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20) := PLUS(PLUS(18, 1, Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING(BaseClassName__GLOBALS(Globals))]), 1, 4)];
goto label_38;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3437)
label_38:
goto label_38_true , label_38_false ;


label_38_true :
assume (Mem[T.ConnectOneClassToOnePort__GLOBALS][ConnectOneClassToOnePort__GLOBALS(Globals)] != 0);
goto label_39;


label_38_false :
assume (Mem[T.ConnectOneClassToOnePort__GLOBALS][ConnectOneClassToOnePort__GLOBALS(Globals)] == 0);
goto label_44;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3437)
label_39:
goto label_39_true , label_39_false ;


label_39_true :
assume ($Legacy$5$3358.28$KbdCreateClassObject$20 != 0);
goto label_40;


label_39_false :
assume ($Legacy$5$3358.28$KbdCreateClassObject$20 == 0);
goto label_44;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3438)
label_40:
tempBoogie0 := PLUS(Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)], 1, 14) ;
Mem[T.MaximumLength__UNICODE_STRING] := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20) := tempBoogie0];
goto label_44;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3441)
label_41:
call $result.ExAllocatePoolWithTag$3441.0$3$ := ExAllocatePoolWithTag (1, $ExAllocatePoolWithTag.arg.2$4$, 1130652235);
goto label_45;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3441)
label_44:
$ExAllocatePoolWithTag.arg.2$4$ := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)] ;
goto label_41;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3441)
label_45:
Mem[T.Buffer__UNICODE_STRING] := Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20) := $result.ExAllocatePoolWithTag$3441.0$3$];
goto label_46;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3444)
label_46:
goto label_46_true , label_46_false ;


label_46_true :
assume (Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)] != 0);
goto label_59;


label_46_false :
assume (Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)] == 0);
goto label_50;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3446)
label_47:
// skip KbdDebugPrint
goto label_51;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3446)
label_50:
call havoc_stringTemp := __HAVOC_malloc(1);
$KbdDebugPrint.arg.2$5$ := havoc_stringTemp ;
goto label_47;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3451)
label_51:
$status$6$3386.24$KbdCreateClassObject$20 := -1073741823 ;
goto label_52;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3452)
label_52:
$errorCode$9$3389.24$KbdCreateClassObject$20 := -1073414143 ;
goto label_53;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3453)
label_53:
$uniqueErrorValue$7$3387.24$KbdCreateClassObject$20 := 10006 ;
goto label_54;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3454)
label_54:
Mem[T.UINT4] := Mem[T.UINT4][PLUS($dumpData$12$3392.24$KbdCreateClassObject$20, 4, 0) := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)]];
goto label_55;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3455)
label_55:
$dumpCount$11$3391.24$KbdCreateClassObject$20 := 1 ;
goto label_136;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3459)
label_56:
// ignoring intrinsic intrinsic.memset
havoc $result.memset$3459.8$6$;
goto label_63;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3459)
label_59:
$memset.arg.3$7$ := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)] ;
goto label_56;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3460)
label_60:
call $result.RtlAppendUnicodeToString$3460.32$8$ := RtlAppendUnicodeToString ($fullClassName$10$3390.24$KbdCreateClassObject$20, $RtlAppendUnicodeToString.arg.2$9$);
goto label_64;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3460)
label_63:
call havoc_stringTemp := __HAVOC_malloc(1);
$RtlAppendUnicodeToString.arg.2$9$ := havoc_stringTemp ;
goto label_60;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3461)
label_64:
call $result.RtlAppendUnicodeToString$3461.32$10$ := RtlAppendUnicodeToString ($fullClassName$10$3390.24$KbdCreateClassObject$20, Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING(BaseClassName__GLOBALS(Globals))]);
goto label_67;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3463)
label_67:
goto label_67_true , label_67_false ;


label_67_true :
assume (Mem[T.ConnectOneClassToOnePort__GLOBALS][ConnectOneClassToOnePort__GLOBALS(Globals)] != 0);
goto label_68;


label_67_false :
assume (Mem[T.ConnectOneClassToOnePort__GLOBALS][ConnectOneClassToOnePort__GLOBALS(Globals)] == 0);
goto label_76;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3463)
label_68:
goto label_68_true , label_68_false ;


label_68_true :
assume ($Legacy$5$3358.28$KbdCreateClassObject$20 != 0);
goto label_72;


label_68_false :
assume ($Legacy$5$3358.28$KbdCreateClassObject$20 == 0);
goto label_76;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3464)
label_69:
call $result.RtlAppendUnicodeToString$3464.36$11$ := RtlAppendUnicodeToString ($fullClassName$10$3390.24$KbdCreateClassObject$20, $RtlAppendUnicodeToString.arg.2$12$);
goto label_76;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3464)
label_72:
call havoc_stringTemp := __HAVOC_malloc(1);
$RtlAppendUnicodeToString.arg.2$12$ := havoc_stringTemp ;
goto label_69;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3467)
label_73:
call $result.RtlAppendUnicodeToString$3467.32$13$ := RtlAppendUnicodeToString ($fullClassName$10$3390.24$KbdCreateClassObject$20, $RtlAppendUnicodeToString.arg.2$14$);
goto label_77;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3467)
label_76:
call havoc_stringTemp := __HAVOC_malloc(1);
$RtlAppendUnicodeToString.arg.2$14$ := havoc_stringTemp ;
goto label_73;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3473)
label_77:
$nameIndex$14$3394.24$KbdCreateClassObject$20 := 0 ;
goto label_78;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3477)
label_78:
// loop entry initialization...
LOOP_78_alloc := alloc;
LOOP_78_Mem := Mem;
LOOP_78_Res_DEVICE_STACK := Res_DEVICE_STACK;
LOOP_78_Res_DEV_EXTN := Res_DEV_EXTN;
LOOP_78_Res_DEV_OBJ_INIT := Res_DEV_OBJ_INIT;
LOOP_78_Res_SPIN_LOCK := Res_SPIN_LOCK;
goto label_78_head;


label_78_head:
// loop head assertions...
//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
assert((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
assert((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires __forall(_H_z, __inv_resource("DEV_EXTN", 1), 1)
assert((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> (true))));
//TAG: requires 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
assert((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: requires 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
assert((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: requires 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
assert((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: requires 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
assert((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: requires __preserves_resource("DEV_OBJ_INIT")
assert(Res_DEV_OBJ_INIT == LOOP_78_Res_DEV_OBJ_INIT);
//TAG: requires __preserves_resource("DEV_EXTN")
assert(Res_DEV_EXTN == LOOP_78_Res_DEV_EXTN);
//TAG: requires __preserves_field_map(__offset((*((struct _LIST_ENTRY *)0)).Flink))
assert(Mem[T.Flink__LIST_ENTRY] == LOOP_78_Mem[T.Flink__LIST_ENTRY]);
assume(forall f:int :: {alloc[Base(f)]} LOOP_78_alloc[Base(f)] == UNALLOCATED || LOOP_78_alloc[Base(f)] == alloc[Base(f)]);


//TAG: net change in resource DEVICE_STACK only for: __set_empty
assert  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || LOOP_78_Res_DEVICE_STACK[r] == Res_DEVICE_STACK[r]));

//TAG: net change in resource DEV_EXTN only for: __set_empty
assert  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || LOOP_78_Res_DEV_EXTN[r] == Res_DEV_EXTN[r]));

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty
assert  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || LOOP_78_Res_DEV_OBJ_INIT[r] == Res_DEV_OBJ_INIT[r]));

//TAG: net change in resource SPIN_LOCK only for: __set_empty
assert  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (Empty()[r]) || LOOP_78_Res_SPIN_LOCK[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == LOOP_78_Mem[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_f19b65c1] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m] == LOOP_78_Mem[T.CurrentStackLocation___unnamed_4_f19b65c1][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == LOOP_78_Mem[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_true, __set_empty
assert   (Subset(Empty(), Union(Union(Empty(), SetTrue()), Empty())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (SetTrue()[_m]) || (Empty()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == LOOP_78_Mem[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == LOOP_78_Mem[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == LOOP_78_Mem[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == LOOP_78_Mem[T.P_DEVICE_OBJECT][_m]));

// end loop head assertions

Mem[T.UINT2] := Mem[T.UINT2][PLUS(Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)], 2, MINUS_BOTH_PTR_OR_BOTH_INT( BINARY_BOTH_INT(Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)], 2), 1, 1)) := PLUS(48, 1, $nameIndex$14$3394.24$KbdCreateClassObject$20)];
$nameIndex$14$3394.24$KbdCreateClassObject$20 := PLUS($nameIndex$14$3394.24$KbdCreateClassObject$20, 1, 1) ;
goto label_82;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3479)
label_79:
// skip KbdDebugPrint
goto label_83;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3479)
label_82:
call havoc_stringTemp := __HAVOC_malloc(1);
$KbdDebugPrint.arg.2$15$ := havoc_stringTemp ;
goto label_79;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3485)
label_83:
call $result.IoCreateDevice$3485.35$16$ := IoCreateDevice ($DriverObject$1$3354.28$KbdCreateClassObject$20, 288, $fullClassName$10$3390.24$KbdCreateClassObject$20, 11, 0, 0, $ClassDeviceObject$3$3356.28$KbdCreateClassObject$20);
goto label_86;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3485)
label_86:
$status$6$3386.24$KbdCreateClassObject$20 := $result.IoCreateDevice$3485.35$16$ ;
goto label_87;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3493)
label_87:
goto label_87_true , label_87_false ;


label_87_true :
assume (-1073741771 == $status$6$3386.24$KbdCreateClassObject$20);
goto label_78_head;


label_87_false :
assume !(-1073741771 == $status$6$3386.24$KbdCreateClassObject$20);
goto label_88;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3495)
label_88:
Mem[T.PUINT2] := Mem[T.PUINT2][$FullDeviceName$4$3357.35$KbdCreateClassObject$20 := Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)]];
goto label_97;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3498)
label_89:
call ExReleaseFastMutex (Mutex__GLOBALS(Globals));
goto label_92;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3499)
label_92:
call $result.IoCreateDevice$3499.31$17$ := IoCreateDevice ($DriverObject$1$3354.28$KbdCreateClassObject$20, 288, 0, 11, 0, 0, $ClassDeviceObject$3$3356.28$KbdCreateClassObject$20);
goto label_95;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3499)
label_95:
$status$6$3386.24$KbdCreateClassObject$20 := $result.IoCreateDevice$3499.31$17$ ;
goto label_96;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3506)
label_96:
Mem[T.PUINT2] := Mem[T.PUINT2][$FullDeviceName$4$3357.35$KbdCreateClassObject$20 := 0];
goto label_97;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3509)
label_97:
goto label_97_true , label_97_false ;


label_97_true :
assume (0 <= $status$6$3386.24$KbdCreateClassObject$20);
goto label_98;


label_97_false :
assume !(0 <= $status$6$3386.24$KbdCreateClassObject$20);
goto label_102;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3509)
label_98:
goto label_98_true , label_98_false ;


label_98_true :
assume (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20] != 0);
goto label_107;


label_98_false :
assume (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20] == 0);
goto label_102;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3510)
label_99:
// skip KbdDebugPrint
goto label_103;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3510)
label_102:
call havoc_stringTemp := __HAVOC_malloc(1);
$KbdDebugPrint.arg.2$18$ := havoc_stringTemp ;
goto label_99;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3516)
label_103:
$errorCode$9$3389.24$KbdCreateClassObject$20 := -1073414131 ;
goto label_104;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3517)
label_104:
$uniqueErrorValue$7$3387.24$KbdCreateClassObject$20 := 10006 ;
goto label_105;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3518)
label_105:
Mem[T.UINT4] := Mem[T.UINT4][PLUS($dumpData$12$3392.24$KbdCreateClassObject$20, 4, 0) := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullClassName$10$3390.24$KbdCreateClassObject$20)]];
goto label_106;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3519)
label_106:
$dumpCount$11$3391.24$KbdCreateClassObject$20 := 1 ;
goto label_136;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3528)
label_107:
assume (forall r:int :: {BIT_BAND(BIT_BOR(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20])], 4),r)} BIT_BAND(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20])],r)!= 0 || BIT_BAND(4,r)!= 0 <==> BIT_BAND(BIT_BOR(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20])], 4),r)!= 0);
tempBoogie0 := BIT_BOR(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20])], 4) ;
Mem[T.Flags__DEVICE_OBJECT] := Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20]) := tempBoogie0];
goto label_108;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3529)
label_108:
$deviceExtension$8$3388.24$KbdCreateClassObject$20 := Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20])] ;
goto label_109;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3531)
label_109:
// Skipping Structure assignment due to the flag SkipStructAssignments
goto label_110;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3533)
label_110:
Mem[T.Self__DEVICE_EXTENSION] := Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20) := Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20]];
goto label_111;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3534)
label_111:
call IoInitializeRemoveLockEx (RemoveLock__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20), 1130652235, 0, 0, 88);
goto label_114;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3539)
label_114:
assume (Mem[T.SpinLock__DEVICE_EXTENSION][SpinLock__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)] == Mem[T.UINT4][SpinLock__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)]);
call KeInitializeSpinLock (SpinLock__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20));
Mem[T.SpinLock__DEVICE_EXTENSION] := Mem[T.SpinLock__DEVICE_EXTENSION][SpinLock__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20) := Mem[T.UINT4][SpinLock__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)]];
goto label_117;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3544)
label_117:
call InitializeListHead_IRP (ReadQueue__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20));
goto label_120;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3550)
label_120:
Mem[T.TrustedSubsystemCount__DEVICE_EXTENSION] := Mem[T.TrustedSubsystemCount__DEVICE_EXTENSION][TrustedSubsystemCount__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20) := 0];
goto label_121;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3557)
label_121:
call $result.ExAllocatePoolWithTag$3557.0$19$ := ExAllocatePoolWithTag (0, Mem[T.InputDataQueueLength__KEYBOARD_ATTRIBUTES][InputDataQueueLength__KEYBOARD_ATTRIBUTES(KeyboardAttributes__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20))], 1130652235);
goto label_124;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3556)
label_124:
Mem[T.InputData__DEVICE_EXTENSION] := Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20) := $result.ExAllocatePoolWithTag$3557.0$19$];
goto label_125;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3562)
label_125:
goto label_125_true , label_125_false ;


label_125_true :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)] != 0);
goto label_133;


label_125_false :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)] == 0);
goto label_129;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3568)
label_126:
// skip KbdDebugPrint
goto label_130;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3568)
label_129:
call havoc_stringTemp := __HAVOC_malloc(1);
$KbdDebugPrint.arg.2$20$ := havoc_stringTemp ;
goto label_126;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3574)
label_130:
$status$6$3386.24$KbdCreateClassObject$20 := -1073741670 ;
goto label_131;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3580)
label_131:
$errorCode$9$3389.24$KbdCreateClassObject$20 := -1073414142 ;
goto label_132;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3581)
label_132:
$uniqueErrorValue$7$3387.24$KbdCreateClassObject$20 := 10020 ;
goto label_136;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3589)
label_133:
call KbdInitializeDataQueue ($deviceExtension$8$3388.24$KbdCreateClassObject$20);
goto label_136;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3593)
label_136:
goto label_136_true , label_136_false ;


label_136_true :
assume ($status$6$3386.24$KbdCreateClassObject$20 != 0);
goto label_137;


label_136_false :
assume ($status$6$3386.24$KbdCreateClassObject$20 == 0);
goto label_162;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3599)
label_137:
call RtlFreeUnicodeString ($fullClassName$10$3390.24$KbdCreateClassObject$20);
goto label_140;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3600)
label_140:
Mem[T.PUINT2] := Mem[T.PUINT2][$FullDeviceName$4$3357.35$KbdCreateClassObject$20 := 0];
goto label_141;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3602)
label_141:
goto label_141_true , label_141_false ;


label_141_true :
assume ($errorCode$9$3389.24$KbdCreateClassObject$20 != 0);
goto label_145;


label_141_false :
assume ($errorCode$9$3389.24$KbdCreateClassObject$20 == 0);
goto label_148;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3603)
label_142:
call KeyboardClassLogError ($result.question.21$, $errorCode$9$3389.24$KbdCreateClassObject$20, $uniqueErrorValue$7$3387.24$KbdCreateClassObject$20, $status$6$3386.24$KbdCreateClassObject$20, $dumpCount$11$3391.24$KbdCreateClassObject$20, $dumpData$12$3392.24$KbdCreateClassObject$20, 0);
goto label_148;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3604)
label_145:
goto label_145_true , label_145_false ;


label_145_true :
assume (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20] != 0);
goto label_147;


label_145_false :
assume (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20] == 0);
goto label_146;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3604)
label_146:
$result.question.21$ := $DriverObject$1$3354.28$KbdCreateClassObject$20 ;
goto label_142;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3604)
label_147:
$result.question.21$ := Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20] ;
goto label_142;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3614)
label_148:
goto label_148_true , label_148_false ;


label_148_true :
assume ($deviceExtension$8$3388.24$KbdCreateClassObject$20 != 0);
goto label_149;


label_148_false :
assume ($deviceExtension$8$3388.24$KbdCreateClassObject$20 == 0);
goto label_154;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3614)
label_149:
goto label_149_true , label_149_false ;


label_149_true :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)] != 0);
goto label_150;


label_149_false :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)] == 0);
goto label_154;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3615)
label_150:
call ExFreePoolWithTag (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20)], 0);
goto label_153;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3616)
label_153:
Mem[T.InputData__DEVICE_EXTENSION] := Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$8$3388.24$KbdCreateClassObject$20) := 0];
goto label_154;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3618)
label_154:
goto label_154_true , label_154_false ;


label_154_true :
assume (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20] != 0);
goto label_155;


label_154_false :
assume (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20] == 0);
goto label_162;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3619)
label_155:
call IoDeleteDevice (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20]);
goto label_158;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3620)
label_158:
Mem[T.P_DEVICE_OBJECT] := Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3356.28$KbdCreateClassObject$20 := 0];
goto label_162;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3624)
label_159:
// skip KbdDebugPrint
goto label_163;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3624)
label_162:
call havoc_stringTemp := __HAVOC_malloc(1);
$KbdDebugPrint.arg.2$22$ := havoc_stringTemp ;
goto label_159;


// e:\esp1\esp\tests\hvdrivers\houdini\kbdclass_fbl_fbs_dev2_ntfs\kbdclass.c(3626)
label_163:
$result.KbdCreateClassObject$3353.0$1$ := $status$6$3386.24$KbdCreateClassObject$20 ;
goto label_1;

}

