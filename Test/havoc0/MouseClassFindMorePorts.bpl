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
const unique T.OkayToLogOverflow__DEVICE_EXTENSION:name;
const unique T.WaitWakeSpinLock__DEVICE_EXTENSION:name;
const unique T.TrustedSubsystemCount__DEVICE_EXTENSION:name;
const unique T.InputCount__DEVICE_EXTENSION:name;
const unique T.SymbolicLinkName__DEVICE_EXTENSION:name;
const unique T.InputData__DEVICE_EXTENSION:name;
const unique T.DataIn__DEVICE_EXTENSION:name;
const unique T.DataOut__DEVICE_EXTENSION:name;
const unique T.MouseAttributes__DEVICE_EXTENSION:name;
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
const unique T.__unnamed_4_c9b2e921__DISPATCHER_HEADER:name;
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
const unique T.__unnamed_4_46b62f69__ERESOURCE:name;
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
const unique T.__unnamed_4_16aff58e__IO_STATUS_BLOCK:name;
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
const unique T.Header__KSEMAPHORE:name;
const unique T.Limit__KSEMAPHORE:name;
const unique T.__unnamed_8_8684a3e7__LARGE_INTEGER:name;
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
const unique T.MouseIdentifier__MOUSE_ATTRIBUTES:name;
const unique T.NumberOfButtons__MOUSE_ATTRIBUTES:name;
const unique T.SampleRate__MOUSE_ATTRIBUTES:name;
const unique T.InputDataQueueLength__MOUSE_ATTRIBUTES:name;
const unique T.UnitId__MOUSE_INPUT_DATA:name;
const unique T.Flags__MOUSE_INPUT_DATA:name;
const unique T.__unnamed_4_9c11ed91__MOUSE_INPUT_DATA:name;
const unique T.RawButtons__MOUSE_INPUT_DATA:name;
const unique T.LastX__MOUSE_INPUT_DATA:name;
const unique T.LastY__MOUSE_INPUT_DATA:name;
const unique T.ExtraInformation__MOUSE_INPUT_DATA:name;
const unique T.OwnerThread__OWNER_ENTRY:name;
const unique T.__unnamed_4_c1e23b02__OWNER_ENTRY:name;
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
const unique T.__unnamed_4_b4f5a780__SYSTEM_POWER_STATE_CONTEXT:name;
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
const unique T.Start___unnamed_12_06b9ee6e:name;
const unique T.Length48___unnamed_12_06b9ee6e:name;
const unique T.Start___unnamed_12_0882bd02:name;
const unique T.Length64___unnamed_12_0882bd02:name;
const unique T.__unnamed_12_2e80217b___unnamed_12_264d0dab:name;
const unique T.Raw___unnamed_12_2e80217b:name;
const unique T.Translated___unnamed_12_2e80217b:name;
const unique T.Data___unnamed_12_5cc7ace2:name;
const unique T.Channel___unnamed_12_6374506e:name;
const unique T.Port___unnamed_12_6374506e:name;
const unique T.Reserved1___unnamed_12_6374506e:name;
const unique T.Priority___unnamed_12_68a4278e:name;
const unique T.Reserved1___unnamed_12_68a4278e:name;
const unique T.Reserved2___unnamed_12_68a4278e:name;
const unique T.Generic___unnamed_12_79ed2653:name;
const unique T.Port___unnamed_12_79ed2653:name;
const unique T.Interrupt___unnamed_12_79ed2653:name;
const unique T.MessageInterrupt___unnamed_12_79ed2653:name;
const unique T.Memory___unnamed_12_79ed2653:name;
const unique T.Dma___unnamed_12_79ed2653:name;
const unique T.DevicePrivate___unnamed_12_79ed2653:name;
const unique T.BusNumber___unnamed_12_79ed2653:name;
const unique T.DeviceSpecificData___unnamed_12_79ed2653:name;
const unique T.Memory40___unnamed_12_79ed2653:name;
const unique T.Memory48___unnamed_12_79ed2653:name;
const unique T.Memory64___unnamed_12_79ed2653:name;
const unique T.Start___unnamed_12_7da594c0:name;
const unique T.Length40___unnamed_12_7da594c0:name;
const unique T.Start___unnamed_12_9873e05d:name;
const unique T.Length___unnamed_12_9873e05d:name;
const unique T.DataSize___unnamed_12_9cc8cebc:name;
const unique T.Reserved1___unnamed_12_9cc8cebc:name;
const unique T.Reserved2___unnamed_12_9cc8cebc:name;
const unique T.Start___unnamed_12_b98da82e:name;
const unique T.Length___unnamed_12_b98da82e:name;
const unique T.Level___unnamed_12_c2880e88:name;
const unique T.Vector___unnamed_12_c2880e88:name;
const unique T.Affinity___unnamed_12_c2880e88:name;
const unique T.Start___unnamed_12_c49ab31a:name;
const unique T.Length___unnamed_12_c49ab31a:name;
const unique T.ListEntry___unnamed_12_c6ed93f3:name;
const unique T.__unnamed_4_a7aa989c___unnamed_12_c6ed93f3:name;
const unique T.Data___unnamed_12_ced61554:name;
const unique T.Reserved___unnamed_12_d9c44df5:name;
const unique T.MessageCount___unnamed_12_d9c44df5:name;
const unique T.Vector___unnamed_12_d9c44df5:name;
const unique T.Affinity___unnamed_12_d9c44df5:name;
const unique T.Start___unnamed_12_db3dcbfc:name;
const unique T.Length___unnamed_12_db3dcbfc:name;
const unique T.Reserved___unnamed_12_db3dcbfc:name;
const unique T.Level___unnamed_12_fb26b3fc:name;
const unique T.Vector___unnamed_12_fb26b3fc:name;
const unique T.Affinity___unnamed_12_fb26b3fc:name;
const unique T.OutputBufferLength___unnamed_16_22e4d054:name;
const unique T.InputBufferLength___unnamed_16_22e4d054:name;
const unique T.IoControlCode___unnamed_16_22e4d054:name;
const unique T.Type3InputBuffer___unnamed_16_22e4d054:name;
const unique T.Create___unnamed_16_39b626ad:name;
const unique T.Read___unnamed_16_39b626ad:name;
const unique T.Write___unnamed_16_39b626ad:name;
const unique T.QueryDirectory___unnamed_16_39b626ad:name;
const unique T.NotifyDirectory___unnamed_16_39b626ad:name;
const unique T.QueryFile___unnamed_16_39b626ad:name;
const unique T.SetFile___unnamed_16_39b626ad:name;
const unique T.QueryEa___unnamed_16_39b626ad:name;
const unique T.SetEa___unnamed_16_39b626ad:name;
const unique T.QueryVolume___unnamed_16_39b626ad:name;
const unique T.SetVolume___unnamed_16_39b626ad:name;
const unique T.FileSystemControl___unnamed_16_39b626ad:name;
const unique T.LockControl___unnamed_16_39b626ad:name;
const unique T.DeviceIoControl___unnamed_16_39b626ad:name;
const unique T.QuerySecurity___unnamed_16_39b626ad:name;
const unique T.SetSecurity___unnamed_16_39b626ad:name;
const unique T.MountVolume___unnamed_16_39b626ad:name;
const unique T.VerifyVolume___unnamed_16_39b626ad:name;
const unique T.Scsi___unnamed_16_39b626ad:name;
const unique T.QueryQuota___unnamed_16_39b626ad:name;
const unique T.SetQuota___unnamed_16_39b626ad:name;
const unique T.QueryDeviceRelations___unnamed_16_39b626ad:name;
const unique T.QueryInterface___unnamed_16_39b626ad:name;
const unique T.DeviceCapabilities___unnamed_16_39b626ad:name;
const unique T.FilterResourceRequirements___unnamed_16_39b626ad:name;
const unique T.ReadWriteConfig___unnamed_16_39b626ad:name;
const unique T.SetLock___unnamed_16_39b626ad:name;
const unique T.QueryId___unnamed_16_39b626ad:name;
const unique T.QueryDeviceText___unnamed_16_39b626ad:name;
const unique T.UsageNotification___unnamed_16_39b626ad:name;
const unique T.WaitWake___unnamed_16_39b626ad:name;
const unique T.PowerSequence___unnamed_16_39b626ad:name;
const unique T.Power___unnamed_16_39b626ad:name;
const unique T.StartDevice___unnamed_16_39b626ad:name;
const unique T.WMI___unnamed_16_39b626ad:name;
const unique T.Others___unnamed_16_39b626ad:name;
const unique T.WhichSpace___unnamed_16_56c011d7:name;
const unique T.Buffer___unnamed_16_56c011d7:name;
const unique T.Offset___unnamed_16_56c011d7:name;
const unique T.Length___unnamed_16_56c011d7:name;
const unique T.DeviceQueueEntry___unnamed_16_5fed8f23:name;
const unique T.__unnamed_16_ae643f17___unnamed_16_5fed8f23:name;
const unique T.Length___unnamed_16_6be9abe0:name;
const unique T.FileName___unnamed_16_6be9abe0:name;
const unique T.FileInformationClass___unnamed_16_6be9abe0:name;
const unique T.FileIndex___unnamed_16_6be9abe0:name;
const unique T.InterfaceType___unnamed_16_78879a38:name;
const unique T.Size___unnamed_16_78879a38:name;
const unique T.Version___unnamed_16_78879a38:name;
const unique T.Interface___unnamed_16_78879a38:name;
const unique T.InterfaceSpecificData___unnamed_16_78879a38:name;
const unique T.Length___unnamed_16_804a2f24:name;
const unique T.StartSid___unnamed_16_804a2f24:name;
const unique T.SidList___unnamed_16_804a2f24:name;
const unique T.SidListLength___unnamed_16_804a2f24:name;
const unique T.Argument1___unnamed_16_8586693f:name;
const unique T.Argument2___unnamed_16_8586693f:name;
const unique T.Argument3___unnamed_16_8586693f:name;
const unique T.Argument4___unnamed_16_8586693f:name;
const unique T.Length___unnamed_16_8831e65f:name;
const unique T.Key___unnamed_16_8831e65f:name;
const unique T.ByteOffset___unnamed_16_8831e65f:name;
const unique T.SecurityContext___unnamed_16_8c2d663a:name;
const unique T.Options___unnamed_16_8c2d663a:name;
const unique T.FileAttributes___unnamed_16_8c2d663a:name;
const unique T.ShareAccess___unnamed_16_8c2d663a:name;
const unique T.EaLength___unnamed_16_8c2d663a:name;
const unique T.Length___unnamed_16_913b9a7a:name;
const unique T.Key___unnamed_16_913b9a7a:name;
const unique T.ByteOffset___unnamed_16_913b9a7a:name;
const unique T.OutputBufferLength___unnamed_16_94d1d1c7:name;
const unique T.InputBufferLength___unnamed_16_94d1d1c7:name;
const unique T.FsControlCode___unnamed_16_94d1d1c7:name;
const unique T.Type3InputBuffer___unnamed_16_94d1d1c7:name;
const unique T.Length___unnamed_16_a2fab4da:name;
const unique T.FileInformationClass___unnamed_16_a2fab4da:name;
const unique T.FileObject___unnamed_16_a2fab4da:name;
const unique T.__unnamed_4_a7d0864c___unnamed_16_a2fab4da:name;
const unique T.DriverContext___unnamed_16_ae643f17:name;
const unique T.Length___unnamed_16_c1b29316:name;
const unique T.Key___unnamed_16_c1b29316:name;
const unique T.ByteOffset___unnamed_16_c1b29316:name;
const unique T.ProviderId___unnamed_16_cbd53ed4:name;
const unique T.DataPath___unnamed_16_cbd53ed4:name;
const unique T.BufferSize___unnamed_16_cbd53ed4:name;
const unique T.Buffer___unnamed_16_cbd53ed4:name;
const unique T.Length___unnamed_16_db70db6e:name;
const unique T.MinBusNumber___unnamed_16_db70db6e:name;
const unique T.MaxBusNumber___unnamed_16_db70db6e:name;
const unique T.Reserved___unnamed_16_db70db6e:name;
const unique T.Length___unnamed_16_ef4b6307:name;
const unique T.EaList___unnamed_16_ef4b6307:name;
const unique T.EaListLength___unnamed_16_ef4b6307:name;
const unique T.EaIndex___unnamed_16_ef4b6307:name;
const unique T.__unnamed_4_b060dea6___unnamed_16_fdda1f62:name;
const unique T.Type___unnamed_16_fdda1f62:name;
const unique T.State___unnamed_16_fdda1f62:name;
const unique T.ShutdownType___unnamed_16_fdda1f62:name;
const unique T.Lock___unnamed_1_1394de4b:name;
const unique T.Abandoned___unnamed_1_2bb39c56:name;
const unique T.Absolute___unnamed_1_2bb39c56:name;
const unique T.NpxIrql___unnamed_1_2bb39c56:name;
const unique T.Signalling___unnamed_1_2bb39c56:name;
const unique T.Inserted___unnamed_1_9fa0583a:name;
const unique T.DebugActive___unnamed_1_9fa0583a:name;
const unique T.DpcActive___unnamed_1_9fa0583a:name;
const unique T.Size___unnamed_1_e30779f5:name;
const unique T.Hand___unnamed_1_e30779f5:name;
const unique T.MinimumVector___unnamed_20_83d468e4:name;
const unique T.MaximumVector___unnamed_20_83d468e4:name;
const unique T.AffinityPolicy___unnamed_20_83d468e4:name;
const unique T.PriorityPolicy___unnamed_20_83d468e4:name;
const unique T.TargetedProcessors___unnamed_20_83d468e4:name;
const unique T.Length40___unnamed_24_035931da:name;
const unique T.Alignment40___unnamed_24_035931da:name;
const unique T.MinimumAddress___unnamed_24_035931da:name;
const unique T.MaximumAddress___unnamed_24_035931da:name;
const unique T.Length___unnamed_24_38e128db:name;
const unique T.Alignment___unnamed_24_38e128db:name;
const unique T.MinimumAddress___unnamed_24_38e128db:name;
const unique T.MaximumAddress___unnamed_24_38e128db:name;
const unique T.Length___unnamed_24_9500ea34:name;
const unique T.Alignment___unnamed_24_9500ea34:name;
const unique T.MinimumAddress___unnamed_24_9500ea34:name;
const unique T.MaximumAddress___unnamed_24_9500ea34:name;
const unique T.Length___unnamed_24_9734802c:name;
const unique T.Alignment___unnamed_24_9734802c:name;
const unique T.MinimumAddress___unnamed_24_9734802c:name;
const unique T.MaximumAddress___unnamed_24_9734802c:name;
const unique T.Length64___unnamed_24_af62813f:name;
const unique T.Alignment64___unnamed_24_af62813f:name;
const unique T.MinimumAddress___unnamed_24_af62813f:name;
const unique T.MaximumAddress___unnamed_24_af62813f:name;
const unique T.Length48___unnamed_24_c0555099:name;
const unique T.Alignment48___unnamed_24_c0555099:name;
const unique T.MinimumAddress___unnamed_24_c0555099:name;
const unique T.MaximumAddress___unnamed_24_c0555099:name;
const unique T.Port___unnamed_24_d7c4ec3a:name;
const unique T.Memory___unnamed_24_d7c4ec3a:name;
const unique T.Interrupt___unnamed_24_d7c4ec3a:name;
const unique T.Dma___unnamed_24_d7c4ec3a:name;
const unique T.Generic___unnamed_24_d7c4ec3a:name;
const unique T.DevicePrivate___unnamed_24_d7c4ec3a:name;
const unique T.BusNumber___unnamed_24_d7c4ec3a:name;
const unique T.ConfigData___unnamed_24_d7c4ec3a:name;
const unique T.Memory40___unnamed_24_d7c4ec3a:name;
const unique T.Memory48___unnamed_24_d7c4ec3a:name;
const unique T.Memory64___unnamed_24_d7c4ec3a:name;
const unique T.ReplaceIfExists___unnamed_2_196a7f56:name;
const unique T.AdvanceOnly___unnamed_2_196a7f56:name;
const unique T.__unnamed_16_5fed8f23___unnamed_40_a0414182:name;
const unique T.Thread___unnamed_40_a0414182:name;
const unique T.AuxiliaryBuffer___unnamed_40_a0414182:name;
const unique T.__unnamed_12_c6ed93f3___unnamed_40_a0414182:name;
const unique T.OriginalFileObject___unnamed_40_a0414182:name;
const unique T.ListEntry___unnamed_40_d90496f4:name;
const unique T.Wcb___unnamed_40_d90496f4:name;
const unique T.InitialPrivilegeSet___unnamed_44_a7026dca:name;
const unique T.PrivilegeSet___unnamed_44_a7026dca:name;
const unique T.Overlay___unnamed_48_c1da9fa5:name;
const unique T.Apc___unnamed_48_c1da9fa5:name;
const unique T.CompletionKey___unnamed_48_c1da9fa5:name;
const unique T.PowerSequence___unnamed_4_0510b147:name;
const unique T.Length___unnamed_4_0a569078:name;
const unique T.Status___unnamed_4_16aff58e:name;
const unique T.Pointer___unnamed_4_16aff58e:name;
const unique T.IdType___unnamed_4_40bf8e34:name;
const unique T.Address___unnamed_4_46b62f69:name;
const unique T.CreatorBackTraceIndex___unnamed_4_46b62f69:name;
const unique T.Capabilities___unnamed_4_73d46255:name;
const unique T.Srb___unnamed_4_765e3037:name;
const unique T.Type___unnamed_4_846adf3f:name;
const unique T.__unnamed_1_2bb39c56___unnamed_4_846adf3f:name;
const unique T.__unnamed_1_e30779f5___unnamed_4_846adf3f:name;
const unique T.__unnamed_1_9fa0583a___unnamed_4_846adf3f:name;
const unique T.PowerState___unnamed_4_8dd73d30:name;
const unique T.Type___unnamed_4_957e0d74:name;
const unique T.Buttons___unnamed_4_9c11ed91:name;
const unique T.__unnamed_4_b5247f10___unnamed_4_9c11ed91:name;
const unique T.IoResourceRequirementList___unnamed_4_a58d40c8:name;
const unique T.CurrentStackLocation___unnamed_4_a7aa989c:name;
const unique T.PacketType___unnamed_4_a7aa989c:name;
const unique T.__unnamed_2_196a7f56___unnamed_4_a7d0864c:name;
const unique T.ClusterCount___unnamed_4_a7d0864c:name;
const unique T.DeleteHandle___unnamed_4_a7d0864c:name;
const unique T.Length___unnamed_4_aa20b426:name;
const unique T.UserApcRoutine___unnamed_4_ab87ddfd:name;
const unique T.IssuingProcess___unnamed_4_ab87ddfd:name;
const unique T.Reserved1___unnamed_4_b016b1e1:name;
const unique T.TargetSystemState___unnamed_4_b016b1e1:name;
const unique T.EffectiveSystemState___unnamed_4_b016b1e1:name;
const unique T.CurrentSystemState___unnamed_4_b016b1e1:name;
const unique T.IgnoreHibernationPath___unnamed_4_b016b1e1:name;
const unique T.PseudoTransition___unnamed_4_b016b1e1:name;
const unique T.Reserved2___unnamed_4_b016b1e1:name;
const unique T.SystemContext___unnamed_4_b060dea6:name;
const unique T.SystemPowerStateContext___unnamed_4_b060dea6:name;
const unique T.__unnamed_4_b016b1e1___unnamed_4_b4f5a780:name;
const unique T.ContextAsUlong___unnamed_4_b4f5a780:name;
const unique T.ButtonFlags___unnamed_4_b5247f10:name;
const unique T.ButtonData___unnamed_4_b5247f10:name;
const unique T.OwnerCount___unnamed_4_c1e23b02:name;
const unique T.TableSize___unnamed_4_c1e23b02:name;
const unique T.__unnamed_4_846adf3f___unnamed_4_c9b2e921:name;
const unique T.Lock___unnamed_4_c9b2e921:name;
const unique T.MasterIrp___unnamed_4_fa7b96a7:name;
const unique T.IrpCount___unnamed_4_fa7b96a7:name;
const unique T.SystemBuffer___unnamed_4_fa7b96a7:name;
const unique T.Vpb___unnamed_8_09ad2712:name;
const unique T.DeviceObject___unnamed_8_09ad2712:name;
const unique T.Length___unnamed_8_21ac1dba:name;
const unique T.CompletionFilter___unnamed_8_21ac1dba:name;
const unique T.Length___unnamed_8_27d3ab76:name;
const unique T.FsInformationClass___unnamed_8_27d3ab76:name;
const unique T.Vpb___unnamed_8_4289df81:name;
const unique T.DeviceObject___unnamed_8_4289df81:name;
const unique T.Length___unnamed_8_47b72724:name;
const unique T.FileInformationClass___unnamed_8_47b72724:name;
const unique T.DeviceTextType___unnamed_8_4b3e3ba3:name;
const unique T.LocaleId___unnamed_8_4b3e3ba3:name;
const unique T.__unnamed_4_ab87ddfd___unnamed_8_4f695993:name;
const unique T.UserApcContext___unnamed_8_4f695993:name;
const unique T.AllocatedResources___unnamed_8_5cfb6ca4:name;
const unique T.AllocatedResourcesTranslated___unnamed_8_5cfb6ca4:name;
const unique T.SecurityInformation___unnamed_8_606438c5:name;
const unique T.Length___unnamed_8_606438c5:name;
const unique T.MinimumChannel___unnamed_8_6ad774c0:name;
const unique T.MaximumChannel___unnamed_8_6ad774c0:name;
const unique T.Length___unnamed_8_805045cb:name;
const unique T.FsInformationClass___unnamed_8_805045cb:name;
const unique T.LowPart___unnamed_8_8684a3e7:name;
const unique T.HighPart___unnamed_8_8684a3e7:name;
const unique T.SecurityInformation___unnamed_8_8cc410da:name;
const unique T.SecurityDescriptor___unnamed_8_8cc410da:name;
const unique T.InPath___unnamed_8_a47253e0:name;
const unique T.Reserved___unnamed_8_a47253e0:name;
const unique T.Type___unnamed_8_a47253e0:name;
const unique T.AsynchronousParameters___unnamed_8_bbd07f6c:name;
const unique T.AllocationSize___unnamed_8_bbd07f6c:name;
const unique T.LowPart___unnamed_8_c9ca8234:name;
const unique T.HighPart___unnamed_8_c9ca8234:name;

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
const unique T.A3UCHAR:name;
const unique T.A3UINT4:name;
const unique T.A3_LUID_AND_ATTRIBUTES:name;
const unique T.A4PVOID:name;
const unique T.A4UINT4:name;
const unique T.A5UINT2:name;
const unique T.A5_DEVICE_POWER_STATE:name;
const unique T.A7_DEVICE_POWER_STATE:name;
const unique T.A85CHAR:name;
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
const unique T.PA256UINT2:name;
const unique T.PA2UINT2:name;
const unique T.PA4UINT4:name;
const unique T.PA5UINT2:name;
const unique T.PA85CHAR:name;
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
const unique T.PPP_FILE_OBJECT:name;
const unique T.PPUINT2:name;
const unique T.PPUINT4:name;
const unique T.PPVOID:name;
const unique T.PP_DEVICE_EXTENSION:name;
const unique T.PP_DEVICE_OBJECT:name;
const unique T.PP_DRIVER_OBJECT:name;
const unique T.PP_ERESOURCE:name;
const unique T.PP_FAST_MUTEX:name;
const unique T.PP_FILE_OBJECT:name;
const unique T.PP_LIST_ENTRY:name;
const unique T.PP_MDL:name;
const unique T.PP_PORT:name;
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
const unique T.P_KSEMAPHORE:name;
const unique T.P_KTHREAD:name;
const unique T.P_LARGE_INTEGER:name;
const unique T.P_LIST_ENTRY:name;
const unique T.P_MDL:name;
const unique T.P_MOUSE_INPUT_DATA:name;
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
const unique T._KSEMAPHORE:name;
const unique T._KTHREAD:name;
const unique T._LARGE_INTEGER:name;
const unique T._LIST_ENTRY:name;
const unique T._LUID:name;
const unique T._LUID_AND_ATTRIBUTES:name;
const unique T._MDL:name;
const unique T._MOUSE_ATTRIBUTES:name;
const unique T._MOUSE_INPUT_DATA:name;
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
const unique T.__unnamed_12_06b9ee6e:name;
const unique T.__unnamed_12_0882bd02:name;
const unique T.__unnamed_12_264d0dab:name;
const unique T.__unnamed_12_2e80217b:name;
const unique T.__unnamed_12_5cc7ace2:name;
const unique T.__unnamed_12_6374506e:name;
const unique T.__unnamed_12_68a4278e:name;
const unique T.__unnamed_12_79ed2653:name;
const unique T.__unnamed_12_7da594c0:name;
const unique T.__unnamed_12_9873e05d:name;
const unique T.__unnamed_12_9cc8cebc:name;
const unique T.__unnamed_12_b98da82e:name;
const unique T.__unnamed_12_c2880e88:name;
const unique T.__unnamed_12_c49ab31a:name;
const unique T.__unnamed_12_c6ed93f3:name;
const unique T.__unnamed_12_ced61554:name;
const unique T.__unnamed_12_d9c44df5:name;
const unique T.__unnamed_12_db3dcbfc:name;
const unique T.__unnamed_12_fb26b3fc:name;
const unique T.__unnamed_16_22e4d054:name;
const unique T.__unnamed_16_39b626ad:name;
const unique T.__unnamed_16_56c011d7:name;
const unique T.__unnamed_16_5fed8f23:name;
const unique T.__unnamed_16_6be9abe0:name;
const unique T.__unnamed_16_78879a38:name;
const unique T.__unnamed_16_804a2f24:name;
const unique T.__unnamed_16_8586693f:name;
const unique T.__unnamed_16_8831e65f:name;
const unique T.__unnamed_16_8c2d663a:name;
const unique T.__unnamed_16_913b9a7a:name;
const unique T.__unnamed_16_94d1d1c7:name;
const unique T.__unnamed_16_a2fab4da:name;
const unique T.__unnamed_16_ae643f17:name;
const unique T.__unnamed_16_c1b29316:name;
const unique T.__unnamed_16_cbd53ed4:name;
const unique T.__unnamed_16_db70db6e:name;
const unique T.__unnamed_16_ef4b6307:name;
const unique T.__unnamed_16_fdda1f62:name;
const unique T.__unnamed_1_1394de4b:name;
const unique T.__unnamed_1_2bb39c56:name;
const unique T.__unnamed_1_9fa0583a:name;
const unique T.__unnamed_1_e30779f5:name;
const unique T.__unnamed_20_83d468e4:name;
const unique T.__unnamed_24_035931da:name;
const unique T.__unnamed_24_38e128db:name;
const unique T.__unnamed_24_9500ea34:name;
const unique T.__unnamed_24_9734802c:name;
const unique T.__unnamed_24_af62813f:name;
const unique T.__unnamed_24_c0555099:name;
const unique T.__unnamed_24_d7c4ec3a:name;
const unique T.__unnamed_2_196a7f56:name;
const unique T.__unnamed_40_a0414182:name;
const unique T.__unnamed_40_d90496f4:name;
const unique T.__unnamed_44_a7026dca:name;
const unique T.__unnamed_48_c1da9fa5:name;
const unique T.__unnamed_4_0510b147:name;
const unique T.__unnamed_4_0a569078:name;
const unique T.__unnamed_4_16aff58e:name;
const unique T.__unnamed_4_40bf8e34:name;
const unique T.__unnamed_4_46b62f69:name;
const unique T.__unnamed_4_73d46255:name;
const unique T.__unnamed_4_765e3037:name;
const unique T.__unnamed_4_846adf3f:name;
const unique T.__unnamed_4_8dd73d30:name;
const unique T.__unnamed_4_957e0d74:name;
const unique T.__unnamed_4_9c11ed91:name;
const unique T.__unnamed_4_a58d40c8:name;
const unique T.__unnamed_4_a7aa989c:name;
const unique T.__unnamed_4_a7d0864c:name;
const unique T.__unnamed_4_aa20b426:name;
const unique T.__unnamed_4_ab87ddfd:name;
const unique T.__unnamed_4_b016b1e1:name;
const unique T.__unnamed_4_b060dea6:name;
const unique T.__unnamed_4_b4f5a780:name;
const unique T.__unnamed_4_b5247f10:name;
const unique T.__unnamed_4_c1e23b02:name;
const unique T.__unnamed_4_c9b2e921:name;
const unique T.__unnamed_4_fa7b96a7:name;
const unique T.__unnamed_8_09ad2712:name;
const unique T.__unnamed_8_21ac1dba:name;
const unique T.__unnamed_8_27d3ab76:name;
const unique T.__unnamed_8_4289df81:name;
const unique T.__unnamed_8_47b72724:name;
const unique T.__unnamed_8_4b3e3ba3:name;
const unique T.__unnamed_8_4f695993:name;
const unique T.__unnamed_8_5cfb6ca4:name;
const unique T.__unnamed_8_606438c5:name;
const unique T.__unnamed_8_6ad774c0:name;
const unique T.__unnamed_8_805045cb:name;
const unique T.__unnamed_8_8684a3e7:name;
const unique T.__unnamed_8_8cc410da:name;
const unique T.__unnamed_8_a47253e0:name;
const unique T.__unnamed_8_bbd07f6c:name;
const unique T.__unnamed_8_c9ca8234:name;

function AssocClassList__GLOBALS(int) returns (int);
function AssocClassList__GLOBALSInv(int) returns (int);
function _S_AssocClassList__GLOBALS([int]bool) returns ([int]bool);
function _S_AssocClassList__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {AssocClassList__GLOBALSInv(AssocClassList__GLOBALS(x))} AssocClassList__GLOBALSInv(AssocClassList__GLOBALS(x)) == x);
axiom (forall x:int :: {AssocClassList__GLOBALSInv(x)} AssocClassList__GLOBALS(AssocClassList__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_AssocClassList__GLOBALS(S)[x]} _S_AssocClassList__GLOBALS(S)[x] <==> S[AssocClassList__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_AssocClassList__GLOBALSInv(S)[x]} _S_AssocClassList__GLOBALSInv(S)[x] <==> S[AssocClassList__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_AssocClassList__GLOBALS(S)} S[x] ==> _S_AssocClassList__GLOBALS(S)[AssocClassList__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_AssocClassList__GLOBALSInv(S)} S[x] ==> _S_AssocClassList__GLOBALSInv(S)[AssocClassList__GLOBALSInv(x)]);
        
axiom (forall x:int :: {AssocClassList__GLOBALS(x)} AssocClassList__GLOBALS(x) == x + 8);
axiom (forall x:int :: {AssocClassList__GLOBALSInv(x)} AssocClassList__GLOBALSInv(x) == x - 8);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 8, 1) == AssocClassList__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 8)} MINUS_LEFT_PTR(x, 1, 8) == AssocClassList__GLOBALSInv(x));
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
        
axiom (forall x:int :: {BaseClassName__GLOBALS(x)} BaseClassName__GLOBALS(x) == x + 344);
axiom (forall x:int :: {BaseClassName__GLOBALSInv(x)} BaseClassName__GLOBALSInv(x) == x - 344);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 344, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 344, 1) == BaseClassName__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 344)} MINUS_LEFT_PTR(x, 1, 344) == BaseClassName__GLOBALSInv(x));
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
        
axiom (forall x:int :: {File__DEVICE_EXTENSION(x)} File__DEVICE_EXTENSION(x) == x + 260);
axiom (forall x:int :: {File__DEVICE_EXTENSIONInv(x)} File__DEVICE_EXTENSIONInv(x) == x - 260);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 260, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 260, 1) == File__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 260)} MINUS_LEFT_PTR(x, 1, 260) == File__DEVICE_EXTENSIONInv(x));
function File__PORT(int) returns (int);
function File__PORTInv(int) returns (int);
function _S_File__PORT([int]bool) returns ([int]bool);
function _S_File__PORTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {File__PORTInv(File__PORT(x))} File__PORTInv(File__PORT(x)) == x);
axiom (forall x:int :: {File__PORTInv(x)} File__PORT(File__PORTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_File__PORT(S)[x]} _S_File__PORT(S)[x] <==> S[File__PORTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_File__PORTInv(S)[x]} _S_File__PORTInv(S)[x] <==> S[File__PORT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_File__PORT(S)} S[x] ==> _S_File__PORT(S)[File__PORT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_File__PORTInv(S)} S[x] ==> _S_File__PORTInv(S)[File__PORTInv(x)]);
        
axiom (forall x:int :: {File__PORT(x)} File__PORT(x) == x + 0);
axiom (forall x:int :: {File__PORTInv(x)} File__PORTInv(x) == x - 0);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 0, 1) == File__PORTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 0)} MINUS_LEFT_PTR(x, 1, 0) == File__PORTInv(x));
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
function Free__PORT(int) returns (int);
function Free__PORTInv(int) returns (int);
function _S_Free__PORT([int]bool) returns ([int]bool);
function _S_Free__PORTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Free__PORTInv(Free__PORT(x))} Free__PORTInv(Free__PORT(x)) == x);
axiom (forall x:int :: {Free__PORTInv(x)} Free__PORT(Free__PORTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Free__PORT(S)[x]} _S_Free__PORT(S)[x] <==> S[Free__PORTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Free__PORTInv(S)[x]} _S_Free__PORTInv(S)[x] <==> S[Free__PORT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Free__PORT(S)} S[x] ==> _S_Free__PORT(S)[Free__PORT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Free__PORTInv(S)} S[x] ==> _S_Free__PORTInv(S)[Free__PORTInv(x)]);
        
axiom (forall x:int :: {Free__PORT(x)} Free__PORT(x) == x + 11);
axiom (forall x:int :: {Free__PORTInv(x)} Free__PORTInv(x) == x - 11);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 11, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 11, 1) == Free__PORTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 11)} MINUS_LEFT_PTR(x, 1, 11) == Free__PORTInv(x));
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
function InitExtension__GLOBALS(int) returns (int);
function InitExtension__GLOBALSInv(int) returns (int);
function _S_InitExtension__GLOBALS([int]bool) returns ([int]bool);
function _S_InitExtension__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {InitExtension__GLOBALSInv(InitExtension__GLOBALS(x))} InitExtension__GLOBALSInv(InitExtension__GLOBALS(x)) == x);
axiom (forall x:int :: {InitExtension__GLOBALSInv(x)} InitExtension__GLOBALS(InitExtension__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_InitExtension__GLOBALS(S)[x]} _S_InitExtension__GLOBALS(S)[x] <==> S[InitExtension__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_InitExtension__GLOBALSInv(S)[x]} _S_InitExtension__GLOBALSInv(S)[x] <==> S[InitExtension__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InitExtension__GLOBALS(S)} S[x] ==> _S_InitExtension__GLOBALS(S)[InitExtension__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_InitExtension__GLOBALSInv(S)} S[x] ==> _S_InitExtension__GLOBALSInv(S)[InitExtension__GLOBALSInv(x)]);
        
axiom (forall x:int :: {InitExtension__GLOBALS(x)} InitExtension__GLOBALS(x) == x + 64);
axiom (forall x:int :: {InitExtension__GLOBALSInv(x)} InitExtension__GLOBALSInv(x) == x - 64);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 64, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 64, 1) == InitExtension__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 64)} MINUS_LEFT_PTR(x, 1, 64) == InitExtension__GLOBALSInv(x));
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
        
axiom (forall x:int :: {LegacyDeviceList__GLOBALS(x)} LegacyDeviceList__GLOBALS(x) == x + 864);
axiom (forall x:int :: {LegacyDeviceList__GLOBALSInv(x)} LegacyDeviceList__GLOBALSInv(x) == x - 864);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 864, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 864, 1) == LegacyDeviceList__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 864)} MINUS_LEFT_PTR(x, 1, 864) == LegacyDeviceList__GLOBALSInv(x));
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
        
axiom (forall x:int :: {Link__DEVICE_EXTENSION(x)} Link__DEVICE_EXTENSION(x) == x + 252);
axiom (forall x:int :: {Link__DEVICE_EXTENSIONInv(x)} Link__DEVICE_EXTENSIONInv(x) == x - 252);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 252, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 252, 1) == Link__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 252)} MINUS_LEFT_PTR(x, 1, 252) == Link__DEVICE_EXTENSIONInv(x));
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
function NumberLegacyPorts__GLOBALS(int) returns (int);
function NumberLegacyPorts__GLOBALSInv(int) returns (int);
function _S_NumberLegacyPorts__GLOBALS([int]bool) returns ([int]bool);
function _S_NumberLegacyPorts__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {NumberLegacyPorts__GLOBALSInv(NumberLegacyPorts__GLOBALS(x))} NumberLegacyPorts__GLOBALSInv(NumberLegacyPorts__GLOBALS(x)) == x);
axiom (forall x:int :: {NumberLegacyPorts__GLOBALSInv(x)} NumberLegacyPorts__GLOBALS(NumberLegacyPorts__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_NumberLegacyPorts__GLOBALS(S)[x]} _S_NumberLegacyPorts__GLOBALS(S)[x] <==> S[NumberLegacyPorts__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_NumberLegacyPorts__GLOBALSInv(S)[x]} _S_NumberLegacyPorts__GLOBALSInv(S)[x] <==> S[NumberLegacyPorts__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberLegacyPorts__GLOBALS(S)} S[x] ==> _S_NumberLegacyPorts__GLOBALS(S)[NumberLegacyPorts__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_NumberLegacyPorts__GLOBALSInv(S)} S[x] ==> _S_NumberLegacyPorts__GLOBALSInv(S)[NumberLegacyPorts__GLOBALSInv(x)]);
        
axiom (forall x:int :: {NumberLegacyPorts__GLOBALS(x)} NumberLegacyPorts__GLOBALS(x) == x + 20);
axiom (forall x:int :: {NumberLegacyPorts__GLOBALSInv(x)} NumberLegacyPorts__GLOBALSInv(x) == x - 20);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 20, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 20, 1) == NumberLegacyPorts__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 20)} MINUS_LEFT_PTR(x, 1, 20) == NumberLegacyPorts__GLOBALSInv(x));
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
function Port__PORT(int) returns (int);
function Port__PORTInv(int) returns (int);
function _S_Port__PORT([int]bool) returns ([int]bool);
function _S_Port__PORTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {Port__PORTInv(Port__PORT(x))} Port__PORTInv(Port__PORT(x)) == x);
axiom (forall x:int :: {Port__PORTInv(x)} Port__PORT(Port__PORTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_Port__PORT(S)[x]} _S_Port__PORT(S)[x] <==> S[Port__PORTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_Port__PORTInv(S)[x]} _S_Port__PORTInv(S)[x] <==> S[Port__PORT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Port__PORT(S)} S[x] ==> _S_Port__PORT(S)[Port__PORT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_Port__PORTInv(S)} S[x] ==> _S_Port__PORTInv(S)[Port__PORTInv(x)]);
        
axiom (forall x:int :: {Port__PORT(x)} Port__PORT(x) == x + 4);
axiom (forall x:int :: {Port__PORTInv(x)} Port__PORTInv(x) == x - 4);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 4, 1) == Port__PORTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 4)} MINUS_LEFT_PTR(x, 1, 4) == Port__PORTInv(x));
function PortsServiced__GLOBALS(int) returns (int);
function PortsServiced__GLOBALSInv(int) returns (int);
function _S_PortsServiced__GLOBALS([int]bool) returns ([int]bool);
function _S_PortsServiced__GLOBALSInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {PortsServiced__GLOBALSInv(PortsServiced__GLOBALS(x))} PortsServiced__GLOBALSInv(PortsServiced__GLOBALS(x)) == x);
axiom (forall x:int :: {PortsServiced__GLOBALSInv(x)} PortsServiced__GLOBALS(PortsServiced__GLOBALSInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_PortsServiced__GLOBALS(S)[x]} _S_PortsServiced__GLOBALS(S)[x] <==> S[PortsServiced__GLOBALSInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_PortsServiced__GLOBALSInv(S)[x]} _S_PortsServiced__GLOBALSInv(S)[x] <==> S[PortsServiced__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_PortsServiced__GLOBALS(S)} S[x] ==> _S_PortsServiced__GLOBALS(S)[PortsServiced__GLOBALS(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_PortsServiced__GLOBALSInv(S)} S[x] ==> _S_PortsServiced__GLOBALSInv(S)[PortsServiced__GLOBALSInv(x)]);
        
axiom (forall x:int :: {PortsServiced__GLOBALS(x)} PortsServiced__GLOBALS(x) == x + 60);
axiom (forall x:int :: {PortsServiced__GLOBALSInv(x)} PortsServiced__GLOBALSInv(x) == x - 60);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 60, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 60, 1) == PortsServiced__GLOBALSInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 60)} MINUS_LEFT_PTR(x, 1, 60) == PortsServiced__GLOBALSInv(x));
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
        
axiom (forall x:int :: {SpinLock__DEVICE_EXTENSION(x)} SpinLock__DEVICE_EXTENSION(x) == x + 152);
axiom (forall x:int :: {SpinLock__DEVICE_EXTENSIONInv(x)} SpinLock__DEVICE_EXTENSIONInv(x) == x - 152);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 152, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 152, 1) == SpinLock__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 152)} MINUS_LEFT_PTR(x, 1, 152) == SpinLock__DEVICE_EXTENSIONInv(x));
function StackSize__DEVICE_OBJECT(int) returns (int);
function StackSize__DEVICE_OBJECTInv(int) returns (int);
function _S_StackSize__DEVICE_OBJECT([int]bool) returns ([int]bool);
function _S_StackSize__DEVICE_OBJECTInv([int]bool) returns ([int]bool);

axiom (forall x:int :: {StackSize__DEVICE_OBJECTInv(StackSize__DEVICE_OBJECT(x))} StackSize__DEVICE_OBJECTInv(StackSize__DEVICE_OBJECT(x)) == x);
axiom (forall x:int :: {StackSize__DEVICE_OBJECTInv(x)} StackSize__DEVICE_OBJECT(StackSize__DEVICE_OBJECTInv(x)) == x);
        
axiom (forall x:int, S:[int]bool :: {_S_StackSize__DEVICE_OBJECT(S)[x]} _S_StackSize__DEVICE_OBJECT(S)[x] <==> S[StackSize__DEVICE_OBJECTInv(x)]);
axiom (forall x:int, S:[int]bool :: {_S_StackSize__DEVICE_OBJECTInv(S)[x]} _S_StackSize__DEVICE_OBJECTInv(S)[x] <==> S[StackSize__DEVICE_OBJECT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_StackSize__DEVICE_OBJECT(S)} S[x] ==> _S_StackSize__DEVICE_OBJECT(S)[StackSize__DEVICE_OBJECT(x)]);
axiom (forall x:int, S:[int]bool :: {S[x], _S_StackSize__DEVICE_OBJECTInv(S)} S[x] ==> _S_StackSize__DEVICE_OBJECTInv(S)[StackSize__DEVICE_OBJECTInv(x)]);
        
axiom (forall x:int :: {StackSize__DEVICE_OBJECT(x)} StackSize__DEVICE_OBJECT(x) == x + 48);
axiom (forall x:int :: {StackSize__DEVICE_OBJECTInv(x)} StackSize__DEVICE_OBJECTInv(x) == x - 48);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 48, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 48, 1) == StackSize__DEVICE_OBJECTInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 48)} MINUS_LEFT_PTR(x, 1, 48) == StackSize__DEVICE_OBJECTInv(x));
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
        
axiom (forall x:int :: {UnitId__DEVICE_EXTENSION(x)} UnitId__DEVICE_EXTENSION(x) == x + 176);
axiom (forall x:int :: {UnitId__DEVICE_EXTENSIONInv(x)} UnitId__DEVICE_EXTENSIONInv(x) == x - 176);
axiom (forall x:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(x, 176, 1)} MINUS_BOTH_PTR_OR_BOTH_INT(x, 176, 1) == UnitId__DEVICE_EXTENSIONInv(x));
axiom (forall x:int :: {MINUS_LEFT_PTR(x, 1, 176)} MINUS_LEFT_PTR(x, 1, 176) == UnitId__DEVICE_EXTENSIONInv(x));
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
const unique BOOGIE_LARGE_INT_3221553153:int;



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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure InsertTailList($ListHead$1$6980.24$InsertTailList$81:int, $Entry$2$6981.41$InsertTailList$81:int);

//TAG: ensures __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
ensures((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN)));
//TAG: ensures __seteq(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), ListHead->Flink, ListHead), __setunion(__old(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), ListHead->Flink, ListHead)), __set(Entry)))
ensures((Subset(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY($ListHead$1$6980.24$InsertTailList$81)], $ListHead$1$6980.24$InsertTailList$81), Union(ReachBetweenSet(Shift_Flink__LIST_ENTRY(old(Mem)[T.Flink__LIST_ENTRY]), old(Mem)[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY($ListHead$1$6980.24$InsertTailList$81)], $ListHead$1$6980.24$InsertTailList$81), Singleton($Entry$2$6981.41$InsertTailList$81))) && Subset(Union(ReachBetweenSet(Shift_Flink__LIST_ENTRY(old(Mem)[T.Flink__LIST_ENTRY]), old(Mem)[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY($ListHead$1$6980.24$InsertTailList$81)], $ListHead$1$6980.24$InsertTailList$81), Singleton($Entry$2$6981.41$InsertTailList$81)), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY($ListHead$1$6980.24$InsertTailList$81)], $ListHead$1$6980.24$InsertTailList$81))));

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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure IoGetDeviceObjectPointer($ObjectName$1$21492.26$IoGetDeviceObjectPointer$161:int, $DesiredAccess$2$21493.22$IoGetDeviceObjectPointer$161:int, $FileObject$3$21494.24$IoGetDeviceObjectPointer$161:int, $DeviceObject$4$21495.26$IoGetDeviceObjectPointer$161:int) returns ($result.IoGetDeviceObjectPointer$21491.0$1$:int);

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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure MouCreateClassObject($DriverObject$1$3165.28$MouCreateClassObject$201:int, $TmpDeviceExtension$2$3166.28$MouCreateClassObject$201:int, $ClassDeviceObject$3$3167.28$MouCreateClassObject$201:int, $FullDeviceName$4$3168.35$MouCreateClassObject$201:int, $Legacy$5$3169.28$MouCreateClassObject$201:int) returns ($result.MouCreateClassObject$3164.0$1$:int);

//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
requires((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires __forall(_H_z, __inv_resource("DEV_EXTN", 1), __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
requires((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0)))));
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
ensures(($result.MouCreateClassObject$3164.0$1$ >= 0) ==> (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201] != 0));
//TAG: ensures (LONG)__return >= 0 ==> (*ClassDeviceObject)->DeviceExtension != (void *)0
ensures(($result.MouCreateClassObject$3164.0$1$ >= 0) ==> (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])] != 0));
//TAG: ensures (LONG)__return >= 0 ==> __resource("DEV_EXTN", (*ClassDeviceObject)->DeviceExtension) == 1
ensures(($result.MouCreateClassObject$3164.0$1$ >= 0) ==> (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])]] == 1));
//TAG: ensures (LONG)__return >= 0 ==> __resource("DEV_OBJ_INIT", *ClassDeviceObject) == 1 && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)) == 1
ensures(($result.MouCreateClassObject$3164.0$1$ >= 0) ==> ((Res_DEV_OBJ_INIT[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201]] == 1) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])]] == 1)));
//TAG: ensures (LONG)__return >= 0 ==> __old_resource("DEV_OBJ_INIT", *ClassDeviceObject) == 0 && __old_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)) == 0
ensures(($result.MouCreateClassObject$3164.0$1$ >= 0) ==> ((old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201]] == 0) && (old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])]] == 0)));
//TAG: ensures (LONG)__return >= 0 ==> __updates_resource("DEV_OBJ_INIT", *ClassDeviceObject, 1) && __updates_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension), 1)
ensures(($result.MouCreateClassObject$3164.0$1$ >= 0) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201] := 1]) && (Res_DEV_EXTN == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])] := 1])));
//TAG: ensures !((LONG)__return >= 0) ==> __resource("DEV_OBJ_INIT", *ClassDeviceObject) == __old_resource("DEV_OBJ_INIT", *ClassDeviceObject) && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)) == __old_resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension))
ensures((!($result.MouCreateClassObject$3164.0$1$ >= 0)) ==> ((Res_DEV_OBJ_INIT[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201]] == old(Res_DEV_OBJ_INIT)[Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201]]) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])]] == old(Res_DEV_EXTN)[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])]])));
//TAG: ensures !((LONG)__return >= 0) ==> __preserves_resource("DEV_OBJ_INIT") && __preserves_resource("DEV_EXTN")
free ensures((!($result.MouCreateClassObject$3164.0$1$ >= 0)) ==> ((Res_DEV_OBJ_INIT == old(Res_DEV_OBJ_INIT)) && (Res_DEV_EXTN == old(Res_DEV_EXTN))));
//TAG: ensures __forall(_H_z, __inv_resource("DEV_EXTN", 1), __setin(_H_z, __set((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension))) || __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
ensures((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Singleton(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])])[_H_z]) || ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0))))));
//TAG: ensures !((LONG)__return >= 0) ==> __forall(_H_z, __inv_resource("DEV_EXTN", 1), __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
ensures((!($result.MouCreateClassObject$3164.0$1$ >= 0)) ==> ((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0))))));
//TAG: ensures (LONG)__return >= 0 ==> __resource("SPIN_LOCK", &((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension))->SpinLock) == 0
ensures(($result.MouCreateClassObject$3164.0$1$ >= 0) ==> (Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])])] == 0));

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: __set_empty
ensures  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || old(Res_DEVICE_STACK)[r] == Res_DEVICE_STACK[r]));
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: __set_empty, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(*ClassDeviceObject))->DeviceExtension)
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])]))) && (forall r:int :: {Res_DEV_EXTN[r]} (Empty()[r]) || (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201])] == r) || old(Res_DEV_EXTN)[r] == Res_DEV_EXTN[r]));
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: __set_empty, *ClassDeviceObject
ensures  (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton(Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201]))) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (Empty()[r]) || (Mem[T.P_DEVICE_OBJECT][$ClassDeviceObject$3$3167.28$MouCreateClassObject$201] == r) || old(Res_DEV_OBJ_INIT)[r] == Res_DEV_OBJ_INIT[r]));
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: &TmpDeviceExtension->WaitWakeSpinLock, &((struct _DEVICE_EXTENSION *)TmpDeviceExtension)->SpinLock, __set_true
ensures  (Subset(Empty(), Union(Union(Union(Empty(), Singleton(WaitWakeSpinLock__DEVICE_EXTENSION($TmpDeviceExtension$2$3166.28$MouCreateClassObject$201))), Singleton(SpinLock__DEVICE_EXTENSION($TmpDeviceExtension$2$3166.28$MouCreateClassObject$201))), SetTrue())) && (forall r:int :: {Res_SPIN_LOCK[r]} (WaitWakeSpinLock__DEVICE_EXTENSION($TmpDeviceExtension$2$3166.28$MouCreateClassObject$201) == r) || (SpinLock__DEVICE_EXTENSION($TmpDeviceExtension$2$3166.28$MouCreateClassObject$201) == r) || (SetTrue()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == old(Mem)[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_true
ensures   (Subset(Empty(), Union(Empty(), SetTrue())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (SetTrue()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == old(Mem)[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == old(Mem)[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == old(Mem)[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_empty, ClassDeviceObject
ensures   (Subset(Empty(), Union(Union(Empty(), Empty()), Singleton($ClassDeviceObject$3$3167.28$MouCreateClassObject$201))) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (Empty()[_m]) || (_m == $ClassDeviceObject$3$3167.28$MouCreateClassObject$201) || Mem[T.P_DEVICE_OBJECT][_m] == old(Mem)[T.P_DEVICE_OBJECT][_m]));

//TAG: havoc memory locations by default
modifies Mem;


procedure MouDeterminePortsServiced($BasePortName$1$3491.23$MouDeterminePortsServiced$81:int, $NumberPortsServiced$2$3492.18$MouDeterminePortsServiced$81:int) returns ($result.MouDeterminePortsServiced$3490.0$1$:int);

//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
requires((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires __forall(_H_z, __inv_resource("DEV_EXTN", 1), __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
requires((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0)))));
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
//TAG: ensures __forall(_H_z, __inv_resource("DEV_EXTN", 1), __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
ensures((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0)))));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure MouseAddDeviceEx($ClassData$1$792.28$MouseAddDeviceEx$121:int, $FullClassName$2$793.29$MouseAddDeviceEx$121:int, $File$3$794.28$MouseAddDeviceEx$121:int) returns ($result.MouseAddDeviceEx$791.0$1$:int);

//TAG: requires __resource("DEV_EXTN", ClassData) == 1
requires(Res_DEV_EXTN[$ClassData$1$792.28$MouseAddDeviceEx$121] == 1);
//TAG: requires __resource("SPIN_LOCK", &((struct _DEVICE_EXTENSION *)ClassData)->SpinLock) == 0
requires(Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION($ClassData$1$792.28$MouseAddDeviceEx$121)] == 0);
//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
requires((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
requires((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: requires 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
requires((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: requires 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
requires((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: requires 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
requires((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __resource("DEV_EXTN", ClassData) == 1
ensures(Res_DEV_EXTN[$ClassData$1$792.28$MouseAddDeviceEx$121] == 1);
//TAG: ensures __resource("SPIN_LOCK", &((struct _DEVICE_EXTENSION *)ClassData)->WaitWakeSpinLock) == 0
ensures(Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION($ClassData$1$792.28$MouseAddDeviceEx$121)] == 0);
//TAG: ensures __resource("SPIN_LOCK", &((struct _DEVICE_EXTENSION *)ClassData)->SpinLock) == 0
ensures(Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION($ClassData$1$792.28$MouseAddDeviceEx$121)] == 0);
//TAG: ensures __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
ensures((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: ensures __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
ensures((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
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

//TAG: net change in resource SPIN_LOCK only for: &ClassData->WaitWakeSpinLock, __set_empty
ensures  (Subset(Empty(), Union(Union(Empty(), Singleton(WaitWakeSpinLock__DEVICE_EXTENSION($ClassData$1$792.28$MouseAddDeviceEx$121))), Empty())) && (forall r:int :: {Res_SPIN_LOCK[r]} (WaitWakeSpinLock__DEVICE_EXTENSION($ClassData$1$792.28$MouseAddDeviceEx$121) == r) || (Empty()[r]) || old(Res_SPIN_LOCK)[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == old(Mem)[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure MouseClassLogError($Object$1$4550.10$MouseClassLogError$281:int, $ErrorCode$2$4551.10$MouseClassLogError$281:int, $UniqueErrorValue$3$4552.10$MouseClassLogError$281:int, $FinalStatus$4$4553.13$MouseClassLogError$281:int, $DumpCount$5$4554.10$MouseClassLogError$281:int, $DumpData$6$4555.11$MouseClassLogError$281:int, $MajorFunction$7$4556.10$MouseClassLogError$281:int);

//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
requires((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure ObfDereferenceObject($Object$1$24931.15$ObfDereferenceObject$41:int) returns ($result.ObfDereferenceObject$24930.0$1$:int);

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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure RtlCopyUnicodeString($DestinationString$1$7401.28$RtlCopyUnicodeString$81:int, $SourceString$2$7402.30$RtlCopyUnicodeString$81:int);

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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure RtlInitUnicodeString($DestinationString$1$7281.26$RtlInitUnicodeString$81:int, $SourceString$2$7282.37$RtlInitUnicodeString$81:int);

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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
ensures   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == old(Mem)[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
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


procedure  MouseClassFindMorePorts($DriverObject$1$4588.20$MouseClassFindMorePorts$121:int, $Context$2$4589.20$MouseClassFindMorePorts$121:int, $Count$3$4590.20$MouseClassFindMorePorts$121:int)

//TAG: requires 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
requires((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: requires 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
requires((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: requires 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
requires((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: requires 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
requires((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
requires((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z) && __forall(_H_z, __inv_resource("DEV_EXTN", 1), __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
requires(((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z)))) && ((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0))))));
//TAG: ensures 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
ensures((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: ensures 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
ensures((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: ensures 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
ensures((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: ensures 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
ensures((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
//TAG: ensures __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
ensures((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: ensures __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z) && __forall(_H_z, __inv_resource("DEV_EXTN", 1), __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
ensures(((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z)))) && ((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0))))));
modifies alloc;
free ensures(forall f:int :: {alloc[Base(f)]} old(alloc)[Base(f)] == UNALLOCATED || old(alloc)[Base(f)] == alloc[Base(f)]);

modifies Res_DEVICE_STACK;

//TAG: net change in resource DEVICE_STACK only for: 
modifies Res_DEV_EXTN;

//TAG: net change in resource DEV_EXTN only for: 
modifies Res_DEV_OBJ_INIT;

//TAG: net change in resource DEV_OBJ_INIT only for: 
modifies Res_SPIN_LOCK;

//TAG: net change in resource SPIN_LOCK only for: 

//TAG: havoc memory locations by default
modifies Mem;
{
var havoc_stringTemp:int;
var condVal:int;
var $Context$2$4589.20$MouseClassFindMorePorts$12 : int;
var $Count$3$4590.20$MouseClassFindMorePorts$12 : int;
var $DriverObject$1$4588.20$MouseClassFindMorePorts$12 : int;
var $ExAllocatePoolWithTag.arg.2$5$ : int;
var $MouDebugPrint.arg.2$6$ : int;
var $RtlAppendUnicodeToString.arg.2$10$ : int;
var $RtlAppendUnicodeToString.arg.2$13$ : int;
var $RtlAppendUnicodeToString.arg.2$3$ : int;
var $basePortBuffer$13$4622.28$MouseClassFindMorePorts$12 : int;
var $basePortName$11$4620.28$MouseClassFindMorePorts$12 : int;
var $classDeviceObject$6$4615.28$MouseClassFindMorePorts$12 : int;
var $deviceExtension$5$4614.28$MouseClassFindMorePorts$12 : int;
var $dumpData$7$4616.28$MouseClassFindMorePorts$12 : int;
var $file$15$4624.28$MouseClassFindMorePorts$12 : int;
var $fullClassName$14$4623.28$MouseClassFindMorePorts$12 : int;
var $fullPortName$12$4621.28$MouseClassFindMorePorts$12 : int;
var $i$8$4617.28$MouseClassFindMorePorts$12 : int;
var $memset.arg.3$8$ : int;
var $numPorts$9$4618.28$MouseClassFindMorePorts$12 : int;
var $port$16$4759.22$MouseClassFindMorePorts$12 : int;
var $result.ExAllocatePoolWithTag$4653.0$4$ : int;
var $result.IoGetDeviceObjectPointer$4731.42$16$ : int;
var $result.MouCreateClassObject$4708.37$15$ : int;
var $result.MouDeterminePortsServiced$4680.29$14$ : int;
var $result.MouseAddDeviceEx$4743.34$17$ : int;
var $result.ObfDereferenceObject$4772.16$18$ : int;
var $result.RtlAppendUnicodeToString$4642.28$2$ : int;
var $result.RtlAppendUnicodeToString$4676.28$9$ : int;
var $result.RtlAppendUnicodeToString$4677.28$11$ : int;
var $result.RtlAppendUnicodeToString$4678.28$12$ : int;
var $result.memset$4630.4$1$ : int;
var $result.memset$4675.4$7$ : int;
var $status$4$4613.28$MouseClassFindMorePorts$12 : int;
var $successfulCreates$10$4619.28$MouseClassFindMorePorts$12 : int;
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
var LOOP_74_alloc:[int]name;
var LOOP_74_Mem:[name][int]int;
var LOOP_74_Res_DEVICE_STACK:[int]int;
var LOOP_74_Res_DEV_EXTN:[int]int;
var LOOP_74_Res_DEV_OBJ_INIT:[int]int;
var LOOP_74_Res_SPIN_LOCK:[int]int;


start:

assume (alloc[$DriverObject$1$4588.20$MouseClassFindMorePorts$121] != UNALLOCATED);
assume (alloc[$Context$2$4589.20$MouseClassFindMorePorts$121] != UNALLOCATED);
call $basePortBuffer$13$4622.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(512);
call $basePortName$11$4620.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(8);
call $classDeviceObject$6$4615.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(4);
call $dumpData$7$4616.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(16);
call $file$15$4624.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(4);
call $fullClassName$14$4623.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(4);
call $fullPortName$12$4621.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(8);
call $numPorts$9$4618.28$MouseClassFindMorePorts$12 := __HAVOC_malloc(4);
$DriverObject$1$4588.20$MouseClassFindMorePorts$12 := $DriverObject$1$4588.20$MouseClassFindMorePorts$121;
$Context$2$4589.20$MouseClassFindMorePorts$12 := $Context$2$4589.20$MouseClassFindMorePorts$121;
$Count$3$4590.20$MouseClassFindMorePorts$12 := $Count$3$4590.20$MouseClassFindMorePorts$121;
goto label_3;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4799)
label_1:
call __HAVOC_free($basePortBuffer$13$4622.28$MouseClassFindMorePorts$12);
call __HAVOC_free($basePortName$11$4620.28$MouseClassFindMorePorts$12);
call __HAVOC_free($classDeviceObject$6$4615.28$MouseClassFindMorePorts$12);
call __HAVOC_free($dumpData$7$4616.28$MouseClassFindMorePorts$12);
call __HAVOC_free($file$15$4624.28$MouseClassFindMorePorts$12);
call __HAVOC_free($fullClassName$14$4623.28$MouseClassFindMorePorts$12);
call __HAVOC_free($fullPortName$12$4621.28$MouseClassFindMorePorts$12);
call __HAVOC_free($numPorts$9$4618.28$MouseClassFindMorePorts$12);
assume (forall m:int:: {Res_DEVICE_STACK[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_DEVICE_STACK[m] == old(Res_DEVICE_STACK)[m]);
assume (forall m:int:: {Res_DEV_EXTN[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_DEV_EXTN[m] == old(Res_DEV_EXTN)[m]);
assume (forall m:int:: {Res_DEV_OBJ_INIT[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_DEV_OBJ_INIT[m] == old(Res_DEV_OBJ_INIT)[m]);
assume (forall m:int:: {Res_SPIN_LOCK[m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Res_SPIN_LOCK[m] == old(Res_SPIN_LOCK)[m]);
assume (forall m:int :: {Mem[T.A256UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A256UINT2][m] == old(Mem[T.A256UINT2])[m]);
assume (forall m:int :: {Mem[T.A2UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A2UINT2][m] == old(Mem[T.A2UINT2])[m]);
assume (forall m:int :: {Mem[T.A4UINT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A4UINT4][m] == old(Mem[T.A4UINT4])[m]);
assume (forall m:int :: {Mem[T.A5UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A5UINT2][m] == old(Mem[T.A5UINT2])[m]);
assume (forall m:int :: {Mem[T.A85CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A85CHAR][m] == old(Mem[T.A85CHAR])[m]);
assume (forall m:int :: {Mem[T.A9UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.A9UINT2][m] == old(Mem[T.A9UINT2])[m]);
assume (forall m:int :: {Mem[T.AssocClassList__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.AssocClassList__GLOBALS][m] == old(Mem[T.AssocClassList__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.BaseClassName__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.BaseClassName__GLOBALS][m] == old(Mem[T.BaseClassName__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.Buffer__UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Buffer__UNICODE_STRING][m] == old(Mem[T.Buffer__UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.CHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.CHAR][m] == old(Mem[T.CHAR])[m]);
assume (forall m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][m] == old(Mem[T.CurrentStackLocation___unnamed_4_a7aa989c])[m]);
assume (forall m:int :: {Mem[T.DataIn__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DataIn__DEVICE_EXTENSION][m] == old(Mem[T.DataIn__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.DataOut__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DataOut__DEVICE_EXTENSION][m] == old(Mem[T.DataOut__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.DeviceExtension__DEVICE_OBJECT][m] == old(Mem[T.DeviceExtension__DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.File__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.File__DEVICE_EXTENSION][m] == old(Mem[T.File__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.File__PORT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.File__PORT][m] == old(Mem[T.File__PORT])[m]);
assume (forall m:int :: {Mem[T.Flags__DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Flags__DEVICE_OBJECT][m] == old(Mem[T.Flags__DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.Flink__LIST_ENTRY][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Flink__LIST_ENTRY][m] == old(Mem[T.Flink__LIST_ENTRY])[m]);
assume (forall m:int :: {Mem[T.Free__PORT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Free__PORT][m] == old(Mem[T.Free__PORT])[m]);
assume (forall m:int :: {Mem[T.GrandMaster__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.GrandMaster__GLOBALS][m] == old(Mem[T.GrandMaster__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.INT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.INT4][m] == old(Mem[T.INT4])[m]);
assume (forall m:int :: {Mem[T.InitExtension__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.InitExtension__GLOBALS][m] == old(Mem[T.InitExtension__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.InputData__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.InputData__DEVICE_EXTENSION][m] == old(Mem[T.InputData__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.LegacyDeviceList__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.LegacyDeviceList__GLOBALS][m] == old(Mem[T.LegacyDeviceList__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.Length__UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Length__UNICODE_STRING][m] == old(Mem[T.Length__UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.Link__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Link__DEVICE_EXTENSION][m] == old(Mem[T.Link__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.MaximumLength__UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.MaximumLength__UNICODE_STRING][m] == old(Mem[T.MaximumLength__UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.MinorFunction__IO_STACK_LOCATION][m] == old(Mem[T.MinorFunction__IO_STACK_LOCATION])[m]);
assume (forall m:int :: {Mem[T.Mutex__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Mutex__GLOBALS][m] == old(Mem[T.Mutex__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.NumberLegacyPorts__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.NumberLegacyPorts__GLOBALS][m] == old(Mem[T.NumberLegacyPorts__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.PCHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PCHAR][m] == old(Mem[T.PCHAR])[m]);
assume (forall m:int :: {Mem[T.PPUINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PPUINT2][m] == old(Mem[T.PPUINT2])[m]);
assume (forall m:int :: {Mem[T.PP_DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PP_DEVICE_OBJECT][m] == old(Mem[T.PP_DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.PP_FILE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PP_FILE_OBJECT][m] == old(Mem[T.PP_FILE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.PUINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PUINT2][m] == old(Mem[T.PUINT2])[m]);
assume (forall m:int :: {Mem[T.PUINT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PUINT4][m] == old(Mem[T.PUINT4])[m]);
assume (forall m:int :: {Mem[T.PVOID][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PVOID][m] == old(Mem[T.PVOID])[m]);
assume (forall m:int :: {Mem[T.P_DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_DEVICE_EXTENSION][m] == old(Mem[T.P_DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.P_DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_DEVICE_OBJECT][m] == old(Mem[T.P_DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.P_DRIVER_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_DRIVER_OBJECT][m] == old(Mem[T.P_DRIVER_OBJECT])[m]);
assume (forall m:int :: {Mem[T.P_FAST_MUTEX][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_FAST_MUTEX][m] == old(Mem[T.P_FAST_MUTEX])[m]);
assume (forall m:int :: {Mem[T.P_FILE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_FILE_OBJECT][m] == old(Mem[T.P_FILE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.P_LIST_ENTRY][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_LIST_ENTRY][m] == old(Mem[T.P_LIST_ENTRY])[m]);
assume (forall m:int :: {Mem[T.P_MOUSE_INPUT_DATA][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_MOUSE_INPUT_DATA][m] == old(Mem[T.P_MOUSE_INPUT_DATA])[m]);
assume (forall m:int :: {Mem[T.P_UNICODE_STRING][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.P_UNICODE_STRING][m] == old(Mem[T.P_UNICODE_STRING])[m]);
assume (forall m:int :: {Mem[T.PnP__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PnP__DEVICE_EXTENSION][m] == old(Mem[T.PnP__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.Port__PORT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Port__PORT][m] == old(Mem[T.Port__PORT])[m]);
assume (forall m:int :: {Mem[T.PortsServiced__GLOBALS][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.PortsServiced__GLOBALS][m] == old(Mem[T.PortsServiced__GLOBALS])[m]);
assume (forall m:int :: {Mem[T.Self__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Self__DEVICE_EXTENSION][m] == old(Mem[T.Self__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.SpinLock__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.SpinLock__DEVICE_EXTENSION][m] == old(Mem[T.SpinLock__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.StackSize__DEVICE_OBJECT][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.StackSize__DEVICE_OBJECT][m] == old(Mem[T.StackSize__DEVICE_OBJECT])[m]);
assume (forall m:int :: {Mem[T.Started__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.Started__DEVICE_EXTENSION][m] == old(Mem[T.Started__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.TopPort__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.TopPort__DEVICE_EXTENSION][m] == old(Mem[T.TopPort__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.UCHAR][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UCHAR][m] == old(Mem[T.UCHAR])[m]);
assume (forall m:int :: {Mem[T.UINT2][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UINT2][m] == old(Mem[T.UINT2])[m]);
assume (forall m:int :: {Mem[T.UINT4][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UINT4][m] == old(Mem[T.UINT4])[m]);
assume (forall m:int :: {Mem[T.UnitId__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.UnitId__DEVICE_EXTENSION][m] == old(Mem[T.UnitId__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T.WaitWakeSpinLock__DEVICE_EXTENSION][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T.WaitWakeSpinLock__DEVICE_EXTENSION][m] == old(Mem[T.WaitWakeSpinLock__DEVICE_EXTENSION])[m]);
assume (forall m:int :: {Mem[T._POOL_TYPE][m]} alloc[Base(m)] != ALLOCATED  && old(alloc)[Base(m)] != ALLOCATED  ==> Mem[T._POOL_TYPE][m] == old(Mem[T._POOL_TYPE])[m]);
return;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4799)
label_2:
assume false;
return;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4613)
label_3:
goto label_4;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4614)
label_4:
goto label_5;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4614)
label_5:
$deviceExtension$5$4614.28$MouseClassFindMorePorts$12 := 0 ;
goto label_6;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4615)
label_6:
goto label_7;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4615)
label_7:
Mem[T.P_DEVICE_OBJECT] := Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12 := 0];
goto label_8;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4616)
label_8:
goto label_9;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4617)
label_9:
goto label_10;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4618)
label_10:
goto label_11;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4619)
label_11:
goto label_12;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4620)
label_12:
goto label_13;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4621)
label_13:
goto label_14;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4622)
label_14:
goto label_15;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4623)
label_15:
goto label_16;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4623)
label_16:
Mem[T.PUINT2] := Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12 := 0];
goto label_17;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4624)
label_17:
goto label_18;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4626)
label_18:
call __PREfastPagedCode ();
goto label_21;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4628)
label_21:
Mem[T.MaximumLength__UNICODE_STRING] := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12) := 0];
goto label_22;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4630)
label_22:
// ignoring intrinsic intrinsic.memset
havoc $result.memset$4630.4$1$;
goto label_25;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4631)
label_25:
Mem[T.Buffer__UNICODE_STRING] := Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($basePortName$11$4620.28$MouseClassFindMorePorts$12) := $basePortBuffer$13$4622.28$MouseClassFindMorePorts$12];
goto label_26;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4632)
label_26:
Mem[T.Length__UNICODE_STRING] := Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING($basePortName$11$4620.28$MouseClassFindMorePorts$12) := 0];
goto label_27;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4633)
label_27:
Mem[T.MaximumLength__UNICODE_STRING] := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($basePortName$11$4620.28$MouseClassFindMorePorts$12) := 512];
goto label_28;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4640)
label_28:
call RtlCopyUnicodeString ($basePortName$11$4620.28$MouseClassFindMorePorts$12, BaseClassName__GLOBALS(Globals));
goto label_31;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4641)
label_31:
tempBoogie0 := MINUS_BOTH_PTR_OR_BOTH_INT( Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING($basePortName$11$4620.28$MouseClassFindMorePorts$12)], 10, 1) ;
Mem[T.Length__UNICODE_STRING] := Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING($basePortName$11$4620.28$MouseClassFindMorePorts$12) := tempBoogie0];
goto label_35;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4642)
label_32:
call $result.RtlAppendUnicodeToString$4642.28$2$ := RtlAppendUnicodeToString ($basePortName$11$4620.28$MouseClassFindMorePorts$12, $RtlAppendUnicodeToString.arg.2$3$);
goto label_36;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4642)
label_35:
call havoc_stringTemp := __HAVOC_malloc(1);
$RtlAppendUnicodeToString.arg.2$3$ := havoc_stringTemp ;
goto label_32;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4647)
label_36:
call RtlInitUnicodeString ($fullPortName$12$4621.28$MouseClassFindMorePorts$12, 0);
goto label_39;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4649)
label_39:
Mem[T.MaximumLength__UNICODE_STRING] := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12) := PLUS(PLUS(18, 1, Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING($basePortName$11$4620.28$MouseClassFindMorePorts$12)]), 1, 2)];
goto label_43;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4653)
label_40:
call $result.ExAllocatePoolWithTag$4653.0$4$ := ExAllocatePoolWithTag (1, $ExAllocatePoolWithTag.arg.2$5$, 1131377997);
goto label_44;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4653)
label_43:
$ExAllocatePoolWithTag.arg.2$5$ := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)] ;
goto label_40;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4653)
label_44:
Mem[T.Buffer__UNICODE_STRING] := Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12) := $result.ExAllocatePoolWithTag$4653.0$4$];
goto label_45;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4656)
label_45:
goto label_45_true , label_45_false ;


label_45_true :
assume (Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)] != 0);
goto label_57;


label_45_false :
assume (Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)] == 0);
goto label_49;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4658)
label_46:
// skip MouDebugPrint
goto label_50;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4658)
label_49:
call havoc_stringTemp := __HAVOC_malloc(1);
$MouDebugPrint.arg.2$6$ := havoc_stringTemp ;
goto label_46;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4663)
label_50:
Mem[T.UINT4] := Mem[T.UINT4][PLUS($dumpData$7$4616.28$MouseClassFindMorePorts$12, 4, 0) := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)]];
goto label_51;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4664)
label_51:
call MouseClassLogError ($DriverObject$1$4588.20$MouseClassFindMorePorts$12, BOOGIE_LARGE_INT_3221553153, 20008, -1073741823, 1, $dumpData$7$4616.28$MouseClassFindMorePorts$12, 0);
goto label_156;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4675)
label_54:
// ignoring intrinsic intrinsic.memset
havoc $result.memset$4675.4$7$;
goto label_61;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4675)
label_57:
$memset.arg.3$8$ := Mem[T.MaximumLength__UNICODE_STRING][MaximumLength__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)] ;
goto label_54;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4676)
label_58:
call $result.RtlAppendUnicodeToString$4676.28$9$ := RtlAppendUnicodeToString ($fullPortName$12$4621.28$MouseClassFindMorePorts$12, $RtlAppendUnicodeToString.arg.2$10$);
goto label_62;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4676)
label_61:
call havoc_stringTemp := __HAVOC_malloc(1);
$RtlAppendUnicodeToString.arg.2$10$ := havoc_stringTemp ;
goto label_58;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4677)
label_62:
call $result.RtlAppendUnicodeToString$4677.28$11$ := RtlAppendUnicodeToString ($fullPortName$12$4621.28$MouseClassFindMorePorts$12, Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($basePortName$11$4620.28$MouseClassFindMorePorts$12)]);
goto label_68;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4678)
label_65:
call $result.RtlAppendUnicodeToString$4678.28$12$ := RtlAppendUnicodeToString ($fullPortName$12$4621.28$MouseClassFindMorePorts$12, $RtlAppendUnicodeToString.arg.2$13$);
goto label_69;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4678)
label_68:
call havoc_stringTemp := __HAVOC_malloc(1);
$RtlAppendUnicodeToString.arg.2$13$ := havoc_stringTemp ;
goto label_65;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4680)
label_69:
call $result.MouDeterminePortsServiced$4680.29$14$ := MouDeterminePortsServiced ($basePortName$11$4620.28$MouseClassFindMorePorts$12, $numPorts$9$4618.28$MouseClassFindMorePorts$12);
goto label_72;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4687)
label_72:
$i$8$4617.28$MouseClassFindMorePorts$12 := Mem[T.NumberLegacyPorts__GLOBALS][NumberLegacyPorts__GLOBALS(Globals)] ;
goto label_73;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4687)
label_73:
$successfulCreates$10$4619.28$MouseClassFindMorePorts$12 := 0 ;
goto label_74;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4688)
label_74:
// loop entry initialization...
LOOP_74_alloc := alloc;
LOOP_74_Mem := Mem;
LOOP_74_Res_DEVICE_STACK := Res_DEVICE_STACK;
LOOP_74_Res_DEV_EXTN := Res_DEV_EXTN;
LOOP_74_Res_DEV_OBJ_INIT := Res_DEV_OBJ_INIT;
LOOP_74_Res_SPIN_LOCK := Res_SPIN_LOCK;
goto label_74_head;


label_74_head:
// loop head assertions...
//TAG: requires __pforall(_H_x, (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension), __inv_resource("DEV_OBJ_INIT", 1), ((struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension))->Self == _H_x && __resource("DEV_EXTN", (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)_H_x)->DeviceExtension)) == 1)
assert((forall _H_x:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]} Inverse(Res_DEV_OBJ_INIT,1)[_H_x] ==> ((Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)])] == _H_x) && (Res_DEV_EXTN[Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(_H_x)]] == 1))));
//TAG: requires __pforall(_H_z, _H_z->Self, __inv_resource("DEV_EXTN", 1), __resource("DEV_OBJ_INIT", _H_z->Self) == 1 && (struct _DEVICE_EXTENSION *)(((struct _DEVICE_OBJECT *)(_H_z->Self))->DeviceExtension) == _H_z)
assert((forall _H_z:int :: {Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]} Inverse(Res_DEV_EXTN,1)[_H_z] ==> ((Res_DEV_OBJ_INIT[Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)]] == 1) && (Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION(_H_z)])] == _H_z))));
//TAG: requires __forall(_H_z, __inv_resource("DEV_EXTN", 1), __resource("SPIN_LOCK", &_H_z->SpinLock) == 0 && __resource("SPIN_LOCK", &_H_z->WaitWakeSpinLock) == 0)
assert((Subset(Empty(), Inverse(Res_DEV_EXTN,1)) && (forall _H_z : int :: {Inverse(Res_DEV_EXTN,1)[_H_z]} (Inverse(Res_DEV_EXTN,1)[_H_z]) ==> ((Res_SPIN_LOCK[SpinLock__DEVICE_EXTENSION(_H_z)] == 0) && (Res_SPIN_LOCK[WaitWakeSpinLock__DEVICE_EXTENSION(_H_z)] == 0)))));
//TAG: requires 1 ==> (Globals.GrandMaster != (void *)0 ==> __resource("DEV_EXTN", Globals.GrandMaster) == 1)
assert((true) ==> ((Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0) ==> (Res_DEV_EXTN[Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)]] == 1)));
//TAG: requires 1 ==> __setin(&Globals.LegacyDeviceList, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList))
assert((true) ==> (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[LegacyDeviceList__GLOBALS(Globals)]));
//TAG: requires 1 ==> __forall(_H_y, __btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), _H_y == &Globals.LegacyDeviceList || __resource("DEV_EXTN", CONTAINING_RECORD(_H_y, struct _DEVICE_EXTENSION , Link)) == 1)
assert((true) ==> ((Subset(Empty(), ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))) && (forall _H_y : int :: {ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]} (ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals))[_H_y]) ==> ((_H_y == LegacyDeviceList__GLOBALS(Globals)) || (Res_DEV_EXTN[MINUS_LEFT_PTR(_H_y, 1, Link__DEVICE_EXTENSION(0))] == 1))))));
//TAG: requires 1 ==> !__setin(&Globals.GrandMaster->Link, __setminus(__btwn(__offset((*((struct _LIST_ENTRY *)0)).Flink), (&Globals.LegacyDeviceList)->Flink, &Globals.LegacyDeviceList), __set(&Globals.LegacyDeviceList)))
assert((true) ==> (!(Difference(ReachBetweenSet(Shift_Flink__LIST_ENTRY(Mem[T.Flink__LIST_ENTRY]), Mem[T.Flink__LIST_ENTRY][Flink__LIST_ENTRY(LegacyDeviceList__GLOBALS(Globals))], LegacyDeviceList__GLOBALS(Globals)), Singleton(LegacyDeviceList__GLOBALS(Globals)))[Link__DEVICE_EXTENSION(Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)])])));
assume(forall f:int :: {alloc[Base(f)]} LOOP_74_alloc[Base(f)] == UNALLOCATED || LOOP_74_alloc[Base(f)] == alloc[Base(f)]);


//TAG: net change in resource DEVICE_STACK only for: __set_empty
assert  (Subset(Empty(), Union(Empty(), Empty())) && (forall r:int :: {Res_DEVICE_STACK[r]} (Empty()[r]) || LOOP_74_Res_DEVICE_STACK[r] == Res_DEVICE_STACK[r]));

//TAG: net change in resource DEV_EXTN only for: __set_true
assert  (Subset(Empty(), Union(Empty(), SetTrue())) && (forall r:int :: {Res_DEV_EXTN[r]} (SetTrue()[r]) || LOOP_74_Res_DEV_EXTN[r] == Res_DEV_EXTN[r]));

//TAG: net change in resource DEV_OBJ_INIT only for: __set_true
assert  (Subset(Empty(), Union(Empty(), SetTrue())) && (forall r:int :: {Res_DEV_OBJ_INIT[r]} (SetTrue()[r]) || LOOP_74_Res_DEV_OBJ_INIT[r] == Res_DEV_OBJ_INIT[r]));

//TAG: net change in resource SPIN_LOCK only for: __set_true
assert  (Subset(Empty(), Union(Empty(), SetTrue())) && (forall r:int :: {Res_SPIN_LOCK[r]} (SetTrue()[r]) || LOOP_74_Res_SPIN_LOCK[r] == Res_SPIN_LOCK[r]));
//TAG: updated memory locations at Mem[T.MinorFunction__IO_STACK_LOCATION] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.MinorFunction__IO_STACK_LOCATION][_m]} (Empty()[_m]) || Mem[T.MinorFunction__IO_STACK_LOCATION][_m] == LOOP_74_Mem[T.MinorFunction__IO_STACK_LOCATION][_m]));
//TAG: updated memory locations at Mem[T.CurrentStackLocation___unnamed_4_a7aa989c] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]} (Empty()[_m]) || Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m] == LOOP_74_Mem[T.CurrentStackLocation___unnamed_4_a7aa989c][_m]));
//TAG: updated memory locations at Mem[T.DeviceExtension__DEVICE_OBJECT] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.DeviceExtension__DEVICE_OBJECT][_m]} (Empty()[_m]) || Mem[T.DeviceExtension__DEVICE_OBJECT][_m] == LOOP_74_Mem[T.DeviceExtension__DEVICE_OBJECT][_m]));
//TAG: updated memory locations at Mem[T.Self__DEVICE_EXTENSION] only for: __set_true
assert   (Subset(Empty(), Union(Empty(), SetTrue())) && (forall _m:int :: {Mem[T.Self__DEVICE_EXTENSION][_m]} (SetTrue()[_m]) || Mem[T.Self__DEVICE_EXTENSION][_m] == LOOP_74_Mem[T.Self__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.Started__DEVICE_EXTENSION] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.Started__DEVICE_EXTENSION][_m]} (Empty()[_m]) || Mem[T.Started__DEVICE_EXTENSION][_m] == LOOP_74_Mem[T.Started__DEVICE_EXTENSION][_m]));
//TAG: updated memory locations at Mem[T.GrandMaster__GLOBALS] only for: __set_empty
assert   (Subset(Empty(), Union(Empty(), Empty())) && (forall _m:int :: {Mem[T.GrandMaster__GLOBALS][_m]} (Empty()[_m]) || Mem[T.GrandMaster__GLOBALS][_m] == LOOP_74_Mem[T.GrandMaster__GLOBALS][_m]));
//TAG: updated memory locations at Mem[T.P_DEVICE_OBJECT] only for: __set_true
assert   (Subset(Empty(), Union(Empty(), SetTrue())) && (forall _m:int :: {Mem[T.P_DEVICE_OBJECT][_m]} (SetTrue()[_m]) || Mem[T.P_DEVICE_OBJECT][_m] == LOOP_74_Mem[T.P_DEVICE_OBJECT][_m]));

// end loop head assertions

goto label_74_true , label_74_false ;


label_74_true :
assume ($i$8$4617.28$MouseClassFindMorePorts$12 < Mem[T.PortsServiced__GLOBALS][PortsServiced__GLOBALS(Globals)]);
goto label_75;


label_74_false :
assume !($i$8$4617.28$MouseClassFindMorePorts$12 < Mem[T.PortsServiced__GLOBALS][PortsServiced__GLOBALS(Globals)]);
goto label_155;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4688)
label_75:
goto label_75_true , label_75_false ;


label_75_true :
assume ($i$8$4617.28$MouseClassFindMorePorts$12 < Mem[T.UINT4][$numPorts$9$4618.28$MouseClassFindMorePorts$12]);
goto label_76;


label_75_false :
assume !($i$8$4617.28$MouseClassFindMorePorts$12 < Mem[T.UINT4][$numPorts$9$4618.28$MouseClassFindMorePorts$12]);
goto label_155;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4698)
label_76:
Mem[T.UINT2] := Mem[T.UINT2][PLUS(Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)], 2, MINUS_BOTH_PTR_OR_BOTH_INT( BINARY_BOTH_INT(Mem[T.Length__UNICODE_STRING][Length__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)], 2), 1, 1)) := PLUS(48, 1, $i$8$4617.28$MouseClassFindMorePorts$12)];
goto label_77;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4700)
label_77:
goto label_77_true , label_77_false ;


label_77_true :
assume (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12] != 0);
goto label_78;


label_77_false :
assume (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12] == 0);
goto label_82;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4701)
label_78:
call ExFreePoolWithTag (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12], 0);
goto label_81;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4702)
label_81:
Mem[T.PUINT2] := Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12 := 0];
goto label_82;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4708)
label_82:
call $result.MouCreateClassObject$4708.37$15$ := MouCreateClassObject ($DriverObject$1$4588.20$MouseClassFindMorePorts$12, InitExtension__GLOBALS(Globals), $classDeviceObject$6$4615.28$MouseClassFindMorePorts$12, $fullClassName$14$4623.28$MouseClassFindMorePorts$12, 1);
goto label_85;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4708)
label_85:
$status$4$4613.28$MouseClassFindMorePorts$12 := $result.MouCreateClassObject$4708.37$15$ ;
goto label_86;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4714)
label_86:
goto label_86_true , label_86_false ;


label_86_true :
assume (0 <= $status$4$4613.28$MouseClassFindMorePorts$12);
goto label_90;


label_86_false :
assume !(0 <= $status$4$4613.28$MouseClassFindMorePorts$12);
goto label_87;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4715)
label_87:
call MouseClassLogError ($DriverObject$1$4588.20$MouseClassFindMorePorts$12, BOOGIE_LARGE_INT_3221553153, 20008, $status$4$4613.28$MouseClassFindMorePorts$12, 0, 0, 0);
goto label_154;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4725)
label_90:
$deviceExtension$5$4614.28$MouseClassFindMorePorts$12 := Mem[T.DeviceExtension__DEVICE_OBJECT][DeviceExtension__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12])] ;
goto label_91;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4726)
label_91:
Mem[T.PnP__DEVICE_EXTENSION] := Mem[T.PnP__DEVICE_EXTENSION][PnP__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := 0];
goto label_92;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4731)
label_92:
assume (Mem[T.TopPort__DEVICE_EXTENSION][TopPort__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)] == Mem[T.P_DEVICE_OBJECT][TopPort__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]);
call $result.IoGetDeviceObjectPointer$4731.42$16$ := IoGetDeviceObjectPointer ($fullPortName$12$4621.28$MouseClassFindMorePorts$12, 128, $file$15$4624.28$MouseClassFindMorePorts$12, TopPort__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12));
Mem[T.TopPort__DEVICE_EXTENSION] := Mem[T.TopPort__DEVICE_EXTENSION][TopPort__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := Mem[T.P_DEVICE_OBJECT][TopPort__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]];
goto label_95;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4731)
label_95:
$status$4$4613.28$MouseClassFindMorePorts$12 := $result.IoGetDeviceObjectPointer$4731.42$16$ ;
goto label_96;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4736)
label_96:
goto label_96_true , label_96_false ;


label_96_true :
assume ($status$4$4613.28$MouseClassFindMorePorts$12 != 0);
goto label_97;


label_96_false :
assume ($status$4$4613.28$MouseClassFindMorePorts$12 == 0);
goto label_108;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4738)
label_97:
goto label_97_true , label_97_false ;


label_97_true :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)] != 0);
goto label_98;


label_97_false :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)] == 0);
goto label_104;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4738)
label_98:
call ExFreePoolWithTag (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)], 0);
goto label_101;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4738)
label_101:
Mem[T.DataOut__DEVICE_EXTENSION] := Mem[T.DataOut__DEVICE_EXTENSION][DataOut__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := 0];
goto label_102;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4738)
label_102:
Mem[T.DataIn__DEVICE_EXTENSION] := Mem[T.DataIn__DEVICE_EXTENSION][DataIn__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := Mem[T.DataOut__DEVICE_EXTENSION][DataOut__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]];
goto label_103;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4738)
label_103:
Mem[T.InputData__DEVICE_EXTENSION] := Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := Mem[T.DataIn__DEVICE_EXTENSION][DataIn__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]];
goto label_104;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4738)
label_104:
call IoDeleteDevice (Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]);
goto label_107;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4738)
label_107:
$deviceExtension$5$4614.28$MouseClassFindMorePorts$12 := 0 ;
goto label_154;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4742)
label_108:
Mem[T.StackSize__DEVICE_OBJECT] := Mem[T.StackSize__DEVICE_OBJECT][StackSize__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12]) := PLUS(1, 1, Mem[T.StackSize__DEVICE_OBJECT][StackSize__DEVICE_OBJECT(Mem[T.TopPort__DEVICE_EXTENSION][TopPort__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)])])];
goto label_109;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4743)
label_109:
call $result.MouseAddDeviceEx$4743.34$17$ := MouseAddDeviceEx ($deviceExtension$5$4614.28$MouseClassFindMorePorts$12, Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12], Mem[T.P_FILE_OBJECT][$file$15$4624.28$MouseClassFindMorePorts$12]);
goto label_112;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4743)
label_112:
$status$4$4613.28$MouseClassFindMorePorts$12 := $result.MouseAddDeviceEx$4743.34$17$ ;
goto label_113;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4744)
label_113:
assume (forall r:int :: {BIT_BAND(BIT_BAND(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12])], BIT_BNOT(128)),r)} (POW2(r) && POW2(128) && r != 128) ==> (BIT_BAND(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12])],r)!= 0 <==> BIT_BAND(BIT_BAND(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12])], BIT_BNOT(128)),r)!= 0));
assume (BIT_BAND(BIT_BAND(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12])], BIT_BNOT(128)),128) == 0);
tempBoogie0 := BIT_BAND(Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12])], BIT_BNOT(128)) ;
Mem[T.Flags__DEVICE_OBJECT] := Mem[T.Flags__DEVICE_OBJECT][Flags__DEVICE_OBJECT(Mem[T.P_DEVICE_OBJECT][$classDeviceObject$6$4615.28$MouseClassFindMorePorts$12]) := tempBoogie0];
goto label_114;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4746)
label_114:
goto label_114_true , label_114_false ;


label_114_true :
assume (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12] != 0);
goto label_115;


label_114_false :
assume (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12] == 0);
goto label_119;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4747)
label_115:
call ExFreePoolWithTag (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12], 0);
goto label_118;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4748)
label_118:
Mem[T.PUINT2] := Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12 := 0];
goto label_119;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4751)
label_119:
goto label_119_true , label_119_false ;


label_119_true :
assume (0 <= $status$4$4613.28$MouseClassFindMorePorts$12);
goto label_150;


label_119_false :
assume !(0 <= $status$4$4613.28$MouseClassFindMorePorts$12);
goto label_120;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4752)
label_120:
goto label_120_true , label_120_false ;


label_120_true :
assume (Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] != 0);
goto label_124;


label_120_false :
assume (Mem[T.GrandMaster__GLOBALS][GrandMaster__GLOBALS(Globals)] == 0);
goto label_121;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4753)
label_121:
goto label_121_true , label_121_false ;


label_121_true :
assume (Mem[T.File__DEVICE_EXTENSION][File__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)] != 0);
goto label_122;


label_121_false :
assume (Mem[T.File__DEVICE_EXTENSION][File__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)] == 0);
goto label_135;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4754)
label_122:
Mem[T.P_FILE_OBJECT] := Mem[T.P_FILE_OBJECT][$file$15$4624.28$MouseClassFindMorePorts$12 := Mem[T.File__DEVICE_EXTENSION][File__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]];
goto label_123;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4755)
label_123:
Mem[T.File__DEVICE_EXTENSION] := Mem[T.File__DEVICE_EXTENSION][File__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := 0];
goto label_135;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4759)
label_124:
goto label_125;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4761)
label_125:
call ExAcquireFastMutex (Mutex__GLOBALS(Globals));
goto label_128;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4763)
label_128:
Mem[T.P_FILE_OBJECT] := Mem[T.P_FILE_OBJECT][$file$15$4624.28$MouseClassFindMorePorts$12 := Mem[T.File__PORT][File__PORT(PLUS(Mem[T.AssocClassList__GLOBALS][AssocClassList__GLOBALS(Globals)], 12, Mem[T.UnitId__DEVICE_EXTENSION][UnitId__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]))]];
goto label_129;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4764)
label_129:
Mem[T.File__PORT] := Mem[T.File__PORT][File__PORT(PLUS(Mem[T.AssocClassList__GLOBALS][AssocClassList__GLOBALS(Globals)], 12, Mem[T.UnitId__DEVICE_EXTENSION][UnitId__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)])) := 0];
goto label_130;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4765)
label_130:
Mem[T.Free__PORT] := Mem[T.Free__PORT][Free__PORT(PLUS(Mem[T.AssocClassList__GLOBALS][AssocClassList__GLOBALS(Globals)], 12, Mem[T.UnitId__DEVICE_EXTENSION][UnitId__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)])) := 1];
goto label_131;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4766)
label_131:
Mem[T.Port__PORT] := Mem[T.Port__PORT][Port__PORT(PLUS(Mem[T.AssocClassList__GLOBALS][AssocClassList__GLOBALS(Globals)], 12, Mem[T.UnitId__DEVICE_EXTENSION][UnitId__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)])) := 0];
goto label_132;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4768)
label_132:
call ExReleaseFastMutex (Mutex__GLOBALS(Globals));
goto label_135;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4771)
label_135:
goto label_135_true , label_135_false ;


label_135_true :
assume (Mem[T.P_FILE_OBJECT][$file$15$4624.28$MouseClassFindMorePorts$12] != 0);
goto label_136;


label_135_false :
assume (Mem[T.P_FILE_OBJECT][$file$15$4624.28$MouseClassFindMorePorts$12] == 0);
goto label_139;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4772)
label_136:
call $result.ObfDereferenceObject$4772.16$18$ := ObfDereferenceObject (Mem[T.P_FILE_OBJECT][$file$15$4624.28$MouseClassFindMorePorts$12]);
goto label_139;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4775)
label_139:
goto label_139_true , label_139_false ;


label_139_true :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)] != 0);
goto label_140;


label_139_false :
assume (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)] == 0);
goto label_146;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4775)
label_140:
call ExFreePoolWithTag (Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)], 0);
goto label_143;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4775)
label_143:
Mem[T.DataOut__DEVICE_EXTENSION] := Mem[T.DataOut__DEVICE_EXTENSION][DataOut__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := 0];
goto label_144;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4775)
label_144:
Mem[T.DataIn__DEVICE_EXTENSION] := Mem[T.DataIn__DEVICE_EXTENSION][DataIn__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := Mem[T.DataOut__DEVICE_EXTENSION][DataOut__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]];
goto label_145;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4775)
label_145:
Mem[T.InputData__DEVICE_EXTENSION] := Mem[T.InputData__DEVICE_EXTENSION][InputData__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12) := Mem[T.DataIn__DEVICE_EXTENSION][DataIn__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]];
goto label_146;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4775)
label_146:
call IoDeleteDevice (Mem[T.Self__DEVICE_EXTENSION][Self__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12)]);
goto label_149;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4775)
label_149:
$deviceExtension$5$4614.28$MouseClassFindMorePorts$12 := 0 ;
goto label_154;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4782)
label_150:
call InsertTailList (LegacyDeviceList__GLOBALS(Globals), Link__DEVICE_EXTENSION($deviceExtension$5$4614.28$MouseClassFindMorePorts$12));
goto label_153;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4783)
label_153:
$successfulCreates$10$4619.28$MouseClassFindMorePorts$12 := PLUS($successfulCreates$10$4619.28$MouseClassFindMorePorts$12, 1, 1) ;
goto label_154;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4689)
label_154:
$i$8$4617.28$MouseClassFindMorePorts$12 := PLUS($i$8$4617.28$MouseClassFindMorePorts$12, 1, 1) ;
goto label_74_head;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4786)
label_155:
tempBoogie0 := PLUS(Mem[T.NumberLegacyPorts__GLOBALS][NumberLegacyPorts__GLOBALS(Globals)], 1, $successfulCreates$10$4619.28$MouseClassFindMorePorts$12) ;
Mem[T.NumberLegacyPorts__GLOBALS] := Mem[T.NumberLegacyPorts__GLOBALS][NumberLegacyPorts__GLOBALS(Globals) := tempBoogie0];
goto label_156;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4792)
label_156:
goto label_156_true , label_156_false ;


label_156_true :
assume (Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)] != 0);
goto label_157;


label_156_false :
assume (Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)] == 0);
goto label_160;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4793)
label_157:
call ExFreePoolWithTag (Mem[T.Buffer__UNICODE_STRING][Buffer__UNICODE_STRING($fullPortName$12$4621.28$MouseClassFindMorePorts$12)], 0);
goto label_160;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4796)
label_160:
goto label_160_true , label_160_false ;


label_160_true :
assume (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12] != 0);
goto label_161;


label_160_false :
assume (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12] == 0);
goto label_1;


// e:\esp1\esp\tests\hvdrivers\houdini\mouclass_fbl_fbs_dev2_ntfs\mouclass.c(4797)
label_161:
call ExFreePoolWithTag (Mem[T.PUINT2][$fullClassName$14$4623.28$MouseClassFindMorePorts$12], 0);
goto label_1;

}

