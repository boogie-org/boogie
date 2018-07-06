// RUN: %boogie -noinfer -useArrayTheory -errorTrace:0 "%s" > "%t"
// RUN: %diff "%s.expect" "%t"
var __storm_thread_done_0 : bool;
var __storm_thread_done_1 : bool;
var __storm_thread_done_2 : bool;
var __storm_thread_done_3 : bool;

var raiseException : bool;
var errorReached : bool;
var k : int;
var __storm_atomic : bool;
var __storm_init : bool;
var tid : int;
var tidCount : int;

procedure /* dummy comment */ {:inline 1} storm_getThreadID() returns (tidRet:int)
{
  tidRet := tid;
  return;
}


procedure storm_context_0();
procedure storm_context_1();

procedure contextSwitch();
modifies k;
ensures __storm_atomic ==> old(k) == k;
ensures(old(k) <= k);
ensures(k < 2);



// Memory model

// Mutable
var alloc:int;

// Immutable

var Mem_0_T.CancelRoutine__IRP : [int]int;
var Mem_1_T.CancelRoutine__IRP : [int]int;
var Mem_s_1_T.CancelRoutine__IRP : [int]int;
var Mem_0_T.Cancel__IRP : [int]int;
var Mem_1_T.Cancel__IRP : [int]int;
var Mem_s_1_T.Cancel__IRP : [int]int;
var Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23 : [int]int;
var Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23 : [int]int;
var Mem_s_1_T.CurrentStackLocation___unnamed_4_3c640f23 : [int]int;
var Mem_0_T.DeviceExtension__DEVICE_OBJECT : [int]int;
var Mem_1_T.DeviceExtension__DEVICE_OBJECT : [int]int;
var Mem_s_1_T.DeviceExtension__DEVICE_OBJECT : [int]int;
var Mem_0_T.DeviceObject__IO_STACK_LOCATION : [int]int;
var Mem_1_T.DeviceObject__IO_STACK_LOCATION : [int]int;
var Mem_s_1_T.DeviceObject__IO_STACK_LOCATION : [int]int;


// Field declarations


// Type declarations


// Field offset definitions

function AssociatedIrp__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {AssociatedIrp__IRP(x)} AssociatedIrp__IRP(x) == x + 12);
axiom (forall x:int :: {AssociatedIrp__IRP(x)} AssociatedIrp__IRP(x) == INT_ADD(x, 12));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function COMMON_DATA__PORT_KEYBOARD_EXTENSION(int) returns (int);
        
        
//axiom (forall x:int :: {COMMON_DATA__PORT_KEYBOARD_EXTENSION(x)} COMMON_DATA__PORT_KEYBOARD_EXTENSION(x) == x + 0);
axiom (forall x:int :: {COMMON_DATA__PORT_KEYBOARD_EXTENSION(x)} COMMON_DATA__PORT_KEYBOARD_EXTENSION(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function CancelIrql__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {CancelIrql__IRP(x)} CancelIrql__IRP(x) == x + 37);
axiom (forall x:int :: {CancelIrql__IRP(x)} CancelIrql__IRP(x) == INT_ADD(x, 37));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function CancelRoutine__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {CancelRoutine__IRP(x)} CancelRoutine__IRP(x) == x + 56);
axiom (forall x:int :: {CancelRoutine__IRP(x)} CancelRoutine__IRP(x) == INT_ADD(x, 56));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Cancel__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {Cancel__IRP(x)} Cancel__IRP(x) == x + 36);
axiom (forall x:int :: {Cancel__IRP(x)} Cancel__IRP(x) == INT_ADD(x, 36));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function CompletionRoutine__IO_STACK_LOCATION(int) returns (int);
        
        
//axiom (forall x:int :: {CompletionRoutine__IO_STACK_LOCATION(x)} CompletionRoutine__IO_STACK_LOCATION(x) == x + 28);
axiom (forall x:int :: {CompletionRoutine__IO_STACK_LOCATION(x)} CompletionRoutine__IO_STACK_LOCATION(x) == INT_ADD(x, 28));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Context__IO_STACK_LOCATION(int) returns (int);
        
        
//axiom (forall x:int :: {Context__IO_STACK_LOCATION(x)} Context__IO_STACK_LOCATION(x) == x + 32);
axiom (forall x:int :: {Context__IO_STACK_LOCATION(x)} Context__IO_STACK_LOCATION(x) == INT_ADD(x, 32));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Control__IO_STACK_LOCATION(int) returns (int);
        
        
//axiom (forall x:int :: {Control__IO_STACK_LOCATION(x)} Control__IO_STACK_LOCATION(x) == x + 3);
axiom (forall x:int :: {Control__IO_STACK_LOCATION(x)} Control__IO_STACK_LOCATION(x) == INT_ADD(x, 3));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function ControllerData__GLOBALS(int) returns (int);
        
        
//axiom (forall x:int :: {ControllerData__GLOBALS(x)} ControllerData__GLOBALS(x) == x + 0);
axiom (forall x:int :: {ControllerData__GLOBALS(x)} ControllerData__GLOBALS(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function CurrentLocation__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {CurrentLocation__IRP(x)} CurrentLocation__IRP(x) == x + 35);
axiom (forall x:int :: {CurrentLocation__IRP(x)} CurrentLocation__IRP(x) == INT_ADD(x, 35));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function CurrentStackLocation___unnamed_4_3c640f23(int) returns (int);
        
        
//axiom (forall x:int :: {CurrentStackLocation___unnamed_4_3c640f23(x)} CurrentStackLocation___unnamed_4_3c640f23(x) == x + 0);
axiom (forall x:int :: {CurrentStackLocation___unnamed_4_3c640f23(x)} CurrentStackLocation___unnamed_4_3c640f23(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function DeviceExtension__DEVICE_OBJECT(int) returns (int);
        
        
//axiom (forall x:int :: {DeviceExtension__DEVICE_OBJECT(x)} DeviceExtension__DEVICE_OBJECT(x) == x + 40);
axiom (forall x:int :: {DeviceExtension__DEVICE_OBJECT(x)} DeviceExtension__DEVICE_OBJECT(x) == INT_ADD(x, 40));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function DeviceIoControl___unnamed_16_afe81cff(int) returns (int);
        
        
//axiom (forall x:int :: {DeviceIoControl___unnamed_16_afe81cff(x)} DeviceIoControl___unnamed_16_afe81cff(x) == x + 0);
axiom (forall x:int :: {DeviceIoControl___unnamed_16_afe81cff(x)} DeviceIoControl___unnamed_16_afe81cff(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function DeviceObject__IO_STACK_LOCATION(int) returns (int);
        
        
//axiom (forall x:int :: {DeviceObject__IO_STACK_LOCATION(x)} DeviceObject__IO_STACK_LOCATION(x) == x + 20);
axiom (forall x:int :: {DeviceObject__IO_STACK_LOCATION(x)} DeviceObject__IO_STACK_LOCATION(x) == INT_ADD(x, 20));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function DeviceState__POWER_STATE(int) returns (int);
        
        
//axiom (forall x:int :: {DeviceState__POWER_STATE(x)} DeviceState__POWER_STATE(x) == x + 0);
axiom (forall x:int :: {DeviceState__POWER_STATE(x)} DeviceState__POWER_STATE(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR(int) returns (int);
        
        
//axiom (forall x:int :: {Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR(x)} Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR(x) == x + 2);
axiom (forall x:int :: {Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR(x)} Flags__CM_PARTIAL_RESOURCE_DESCRIPTOR(x) == INT_ADD(x, 2));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Information__IO_STATUS_BLOCK(int) returns (int);
        
        
//axiom (forall x:int :: {Information__IO_STATUS_BLOCK(x)} Information__IO_STATUS_BLOCK(x) == x + 4);
axiom (forall x:int :: {Information__IO_STATUS_BLOCK(x)} Information__IO_STATUS_BLOCK(x) == INT_ADD(x, 4));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Initialized_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {Initialized_COMMON_DATA(x)} Initialized_COMMON_DATA(x) == x + 323);
axiom (forall x:int :: {Initialized_COMMON_DATA(x)} Initialized_COMMON_DATA(x) == INT_ADD(x, 323));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function InterruptDescriptor_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {InterruptDescriptor_COMMON_DATA(x)} InterruptDescriptor_COMMON_DATA(x) == x + 300);
axiom (forall x:int :: {InterruptDescriptor_COMMON_DATA(x)} InterruptDescriptor_COMMON_DATA(x) == INT_ADD(x, 300));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function InterruptObject_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {InterruptObject_COMMON_DATA(x)} InterruptObject_COMMON_DATA(x) == x + 4);
axiom (forall x:int :: {InterruptObject_COMMON_DATA(x)} InterruptObject_COMMON_DATA(x) == INT_ADD(x, 4));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function IoControlCode___unnamed_16_ae81ad04(int) returns (int);
        
        
//axiom (forall x:int :: {IoControlCode___unnamed_16_ae81ad04(x)} IoControlCode___unnamed_16_ae81ad04(x) == x + 8);
axiom (forall x:int :: {IoControlCode___unnamed_16_ae81ad04(x)} IoControlCode___unnamed_16_ae81ad04(x) == INT_ADD(x, 8));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function IoStatus__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {IoStatus__IRP(x)} IoStatus__IRP(x) == x + 24);
axiom (forall x:int :: {IoStatus__IRP(x)} IoStatus__IRP(x) == INT_ADD(x, 24));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Irp__I8X_KEYBOARD_WORK_ITEM(int) returns (int);
        
        
//axiom (forall x:int :: {Irp__I8X_KEYBOARD_WORK_ITEM(x)} Irp__I8X_KEYBOARD_WORK_ITEM(x) == x + 8);
axiom (forall x:int :: {Irp__I8X_KEYBOARD_WORK_ITEM(x)} Irp__I8X_KEYBOARD_WORK_ITEM(x) == INT_ADD(x, 8));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function IsKeyboard_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {IsKeyboard_COMMON_DATA(x)} IsKeyboard_COMMON_DATA(x) == x + 325);
axiom (forall x:int :: {IsKeyboard_COMMON_DATA(x)} IsKeyboard_COMMON_DATA(x) == INT_ADD(x, 325));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Item__I8X_KEYBOARD_WORK_ITEM(int) returns (int);
        
        
//axiom (forall x:int :: {Item__I8X_KEYBOARD_WORK_ITEM(x)} Item__I8X_KEYBOARD_WORK_ITEM(x) == x + 0);
axiom (forall x:int :: {Item__I8X_KEYBOARD_WORK_ITEM(x)} Item__I8X_KEYBOARD_WORK_ITEM(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Item__POWER_UP_WORK_ITEM(int) returns (int);
        
        
//axiom (forall x:int :: {Item__POWER_UP_WORK_ITEM(x)} Item__POWER_UP_WORK_ITEM(x) == x + 0);
axiom (forall x:int :: {Item__POWER_UP_WORK_ITEM(x)} Item__POWER_UP_WORK_ITEM(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function KeyboardExtension__GLOBALS(int) returns (int);
        
        
//axiom (forall x:int :: {KeyboardExtension__GLOBALS(x)} KeyboardExtension__GLOBALS(x) == x + 8);
axiom (forall x:int :: {KeyboardExtension__GLOBALS(x)} KeyboardExtension__GLOBALS(x) == INT_ADD(x, 8));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function KeyboardPowerIrp__POWER_UP_WORK_ITEM(int) returns (int);
        
        
//axiom (forall x:int :: {KeyboardPowerIrp__POWER_UP_WORK_ITEM(x)} KeyboardPowerIrp__POWER_UP_WORK_ITEM(x) == x + 8);
axiom (forall x:int :: {KeyboardPowerIrp__POWER_UP_WORK_ITEM(x)} KeyboardPowerIrp__POWER_UP_WORK_ITEM(x) == INT_ADD(x, 8));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function MajorFunction__IO_STACK_LOCATION(int) returns (int);
        
        
//axiom (forall x:int :: {MajorFunction__IO_STACK_LOCATION(x)} MajorFunction__IO_STACK_LOCATION(x) == x + 0);
axiom (forall x:int :: {MajorFunction__IO_STACK_LOCATION(x)} MajorFunction__IO_STACK_LOCATION(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function MakeCode__I8X_KEYBOARD_WORK_ITEM(int) returns (int);
        
        
//axiom (forall x:int :: {MakeCode__I8X_KEYBOARD_WORK_ITEM(x)} MakeCode__I8X_KEYBOARD_WORK_ITEM(x) == x + 4);
axiom (forall x:int :: {MakeCode__I8X_KEYBOARD_WORK_ITEM(x)} MakeCode__I8X_KEYBOARD_WORK_ITEM(x) == INT_ADD(x, 4));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function MinorFunction__IO_STACK_LOCATION(int) returns (int);
        
        
//axiom (forall x:int :: {MinorFunction__IO_STACK_LOCATION(x)} MinorFunction__IO_STACK_LOCATION(x) == x + 1);
axiom (forall x:int :: {MinorFunction__IO_STACK_LOCATION(x)} MinorFunction__IO_STACK_LOCATION(x) == INT_ADD(x, 1));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function MouseExtension__GLOBALS(int) returns (int);
        
        
//axiom (forall x:int :: {MouseExtension__GLOBALS(x)} MouseExtension__GLOBALS(x) == x + 4);
axiom (forall x:int :: {MouseExtension__GLOBALS(x)} MouseExtension__GLOBALS(x) == INT_ADD(x, 4));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function MousePowerIrp__POWER_UP_WORK_ITEM(int) returns (int);
        
        
//axiom (forall x:int :: {MousePowerIrp__POWER_UP_WORK_ITEM(x)} MousePowerIrp__POWER_UP_WORK_ITEM(x) == x + 4);
axiom (forall x:int :: {MousePowerIrp__POWER_UP_WORK_ITEM(x)} MousePowerIrp__POWER_UP_WORK_ITEM(x) == INT_ADD(x, 4));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function OutputBufferLength___unnamed_16_ae81ad04(int) returns (int);
        
        
//axiom (forall x:int :: {OutputBufferLength___unnamed_16_ae81ad04(x)} OutputBufferLength___unnamed_16_ae81ad04(x) == x + 0);
axiom (forall x:int :: {OutputBufferLength___unnamed_16_ae81ad04(x)} OutputBufferLength___unnamed_16_ae81ad04(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function OutstandingPowerIrp_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {OutstandingPowerIrp_COMMON_DATA(x)} OutstandingPowerIrp_COMMON_DATA(x) == x + 44);
axiom (forall x:int :: {OutstandingPowerIrp_COMMON_DATA(x)} OutstandingPowerIrp_COMMON_DATA(x) == INT_ADD(x, 44));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Overlay___unnamed_48_e2bbfb0b(int) returns (int);
        
        
//axiom (forall x:int :: {Overlay___unnamed_48_e2bbfb0b(x)} Overlay___unnamed_48_e2bbfb0b(x) == x + 0);
axiom (forall x:int :: {Overlay___unnamed_48_e2bbfb0b(x)} Overlay___unnamed_48_e2bbfb0b(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Parameters__IO_STACK_LOCATION(int) returns (int);
        
        
//axiom (forall x:int :: {Parameters__IO_STACK_LOCATION(x)} Parameters__IO_STACK_LOCATION(x) == x + 4);
axiom (forall x:int :: {Parameters__IO_STACK_LOCATION(x)} Parameters__IO_STACK_LOCATION(x) == INT_ADD(x, 4));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function PendingReturned__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {PendingReturned__IRP(x)} PendingReturned__IRP(x) == x + 33);
axiom (forall x:int :: {PendingReturned__IRP(x)} PendingReturned__IRP(x) == INT_ADD(x, 33));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function PnpDeviceState_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {PnpDeviceState_COMMON_DATA(x)} PnpDeviceState_COMMON_DATA(x) == x + 316);
axiom (forall x:int :: {PnpDeviceState_COMMON_DATA(x)} PnpDeviceState_COMMON_DATA(x) == INT_ADD(x, 316));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function PowerCaps__PORT_KEYBOARD_EXTENSION(int) returns (int);
        
        
//axiom (forall x:int :: {PowerCaps__PORT_KEYBOARD_EXTENSION(x)} PowerCaps__PORT_KEYBOARD_EXTENSION(x) == x + 328);
axiom (forall x:int :: {PowerCaps__PORT_KEYBOARD_EXTENSION(x)} PowerCaps__PORT_KEYBOARD_EXTENSION(x) == INT_ADD(x, 328));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function PowerEvent__PORT_KEYBOARD_EXTENSION(int) returns (int);
        
        
//axiom (forall x:int :: {PowerEvent__PORT_KEYBOARD_EXTENSION(x)} PowerEvent__PORT_KEYBOARD_EXTENSION(x) == x + 329);
axiom (forall x:int :: {PowerEvent__PORT_KEYBOARD_EXTENSION(x)} PowerEvent__PORT_KEYBOARD_EXTENSION(x) == INT_ADD(x, 329));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function PowerFlags__GLOBALS(int) returns (int);
        
        
//axiom (forall x:int :: {PowerFlags__GLOBALS(x)} PowerFlags__GLOBALS(x) == x + 40);
axiom (forall x:int :: {PowerFlags__GLOBALS(x)} PowerFlags__GLOBALS(x) == INT_ADD(x, 40));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function PowerSpinLock__CONTROLLER_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {PowerSpinLock__CONTROLLER_DATA(x)} PowerSpinLock__CONTROLLER_DATA(x) == x + 116);
axiom (forall x:int :: {PowerSpinLock__CONTROLLER_DATA(x)} PowerSpinLock__CONTROLLER_DATA(x) == INT_ADD(x, 116));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function PowerState_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {PowerState_COMMON_DATA(x)} PowerState_COMMON_DATA(x) == x + 48);
axiom (forall x:int :: {PowerState_COMMON_DATA(x)} PowerState_COMMON_DATA(x) == INT_ADD(x, 48));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Power___unnamed_16_afe81cff(int) returns (int);
        
        
//axiom (forall x:int :: {Power___unnamed_16_afe81cff(x)} Power___unnamed_16_afe81cff(x) == x + 0);
axiom (forall x:int :: {Power___unnamed_16_afe81cff(x)} Power___unnamed_16_afe81cff(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function RemoveLock_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {RemoveLock_COMMON_DATA(x)} RemoveLock_COMMON_DATA(x) == x + 20);
axiom (forall x:int :: {RemoveLock_COMMON_DATA(x)} RemoveLock_COMMON_DATA(x) == INT_ADD(x, 20));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Self_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {Self_COMMON_DATA(x)} Self_COMMON_DATA(x) == x + 0);
axiom (forall x:int :: {Self_COMMON_DATA(x)} Self_COMMON_DATA(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function ShutdownType_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {ShutdownType_COMMON_DATA(x)} ShutdownType_COMMON_DATA(x) == x + 56);
axiom (forall x:int :: {ShutdownType_COMMON_DATA(x)} ShutdownType_COMMON_DATA(x) == INT_ADD(x, 56));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function ShutdownType___unnamed_16_57972375(int) returns (int);
        
        
//axiom (forall x:int :: {ShutdownType___unnamed_16_57972375(x)} ShutdownType___unnamed_16_57972375(x) == x + 12);
axiom (forall x:int :: {ShutdownType___unnamed_16_57972375(x)} ShutdownType___unnamed_16_57972375(x) == INT_ADD(x, 12));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Started_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {Started_COMMON_DATA(x)} Started_COMMON_DATA(x) == x + 326);
axiom (forall x:int :: {Started_COMMON_DATA(x)} Started_COMMON_DATA(x) == INT_ADD(x, 326));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function State___unnamed_16_57972375(int) returns (int);
        
        
//axiom (forall x:int :: {State___unnamed_16_57972375(x)} State___unnamed_16_57972375(x) == x + 8);
axiom (forall x:int :: {State___unnamed_16_57972375(x)} State___unnamed_16_57972375(x) == INT_ADD(x, 8));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Status___unnamed_4_d4b13373(int) returns (int);
        
        
//axiom (forall x:int :: {Status___unnamed_4_d4b13373(x)} Status___unnamed_4_d4b13373(x) == x + 0);
axiom (forall x:int :: {Status___unnamed_4_d4b13373(x)} Status___unnamed_4_d4b13373(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function SysButtonEventIrp__PORT_KEYBOARD_EXTENSION(int) returns (int);
        
        
//axiom (forall x:int :: {SysButtonEventIrp__PORT_KEYBOARD_EXTENSION(x)} SysButtonEventIrp__PORT_KEYBOARD_EXTENSION(x) == x + 332);
axiom (forall x:int :: {SysButtonEventIrp__PORT_KEYBOARD_EXTENSION(x)} SysButtonEventIrp__PORT_KEYBOARD_EXTENSION(x) == INT_ADD(x, 332));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(int) returns (int);
        
        
//axiom (forall x:int :: {SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(x)} SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(x) == x + 368);
axiom (forall x:int :: {SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(x)} SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(x) == INT_ADD(x, 368));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function SystemBuffer___unnamed_4_99f86ad5(int) returns (int);
        
        
//axiom (forall x:int :: {SystemBuffer___unnamed_4_99f86ad5(x)} SystemBuffer___unnamed_4_99f86ad5(x) == x + 0);
axiom (forall x:int :: {SystemBuffer___unnamed_4_99f86ad5(x)} SystemBuffer___unnamed_4_99f86ad5(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function SystemState_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {SystemState_COMMON_DATA(x)} SystemState_COMMON_DATA(x) == x + 52);
axiom (forall x:int :: {SystemState_COMMON_DATA(x)} SystemState_COMMON_DATA(x) == INT_ADD(x, 52));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function SystemState__POWER_STATE(int) returns (int);
        
        
//axiom (forall x:int :: {SystemState__POWER_STATE(x)} SystemState__POWER_STATE(x) == x + 0);
axiom (forall x:int :: {SystemState__POWER_STATE(x)} SystemState__POWER_STATE(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Tail__IRP(int) returns (int);
        
        
//axiom (forall x:int :: {Tail__IRP(x)} Tail__IRP(x) == x + 64);
axiom (forall x:int :: {Tail__IRP(x)} Tail__IRP(x) == INT_ADD(x, 64));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function TopOfStack_COMMON_DATA(int) returns (int);
        
        
//axiom (forall x:int :: {TopOfStack_COMMON_DATA(x)} TopOfStack_COMMON_DATA(x) == x + 12);
axiom (forall x:int :: {TopOfStack_COMMON_DATA(x)} TopOfStack_COMMON_DATA(x) == INT_ADD(x, 12));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function Type___unnamed_16_57972375(int) returns (int);
        
        
//axiom (forall x:int :: {Type___unnamed_16_57972375(x)} Type___unnamed_16_57972375(x) == x + 4);
axiom (forall x:int :: {Type___unnamed_16_57972375(x)} Type___unnamed_16_57972375(x) == INT_ADD(x, 4));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function __unnamed_12_41c62b26___unnamed_40_32307de2(int) returns (int);
        
        
//axiom (forall x:int :: {__unnamed_12_41c62b26___unnamed_40_32307de2(x)} __unnamed_12_41c62b26___unnamed_40_32307de2(x) == x + 24);
axiom (forall x:int :: {__unnamed_12_41c62b26___unnamed_40_32307de2(x)} __unnamed_12_41c62b26___unnamed_40_32307de2(x) == INT_ADD(x, 24));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function __unnamed_4_3c640f23___unnamed_12_41c62b26(int) returns (int);
        
        
//axiom (forall x:int :: {__unnamed_4_3c640f23___unnamed_12_41c62b26(x)} __unnamed_4_3c640f23___unnamed_12_41c62b26(x) == x + 8);
axiom (forall x:int :: {__unnamed_4_3c640f23___unnamed_12_41c62b26(x)} __unnamed_4_3c640f23___unnamed_12_41c62b26(x) == INT_ADD(x, 8));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS

function __unnamed_4_d4b13373__IO_STATUS_BLOCK(int) returns (int);
        
        
//axiom (forall x:int :: {__unnamed_4_d4b13373__IO_STATUS_BLOCK(x)} __unnamed_4_d4b13373__IO_STATUS_BLOCK(x) == x + 0);
axiom (forall x:int :: {__unnamed_4_d4b13373__IO_STATUS_BLOCK(x)} __unnamed_4_d4b13373__IO_STATUS_BLOCK(x) == INT_ADD(x, 0));
//adding this additional axiom since to show Array(x, 1, n)[f(x)], we need f(x) to be a PLUS


///////////////////////////////////
// will be replaced by:
// "//" when using bv mode
// ""   when using int mode
// main reason is to avoid using bv for constants
// or avoid translating lines that are complex or unsound
//////////////////////////////////

////////////////////////////////////////////
/////// functions for int type /////////////
// Theorem prover does not see INT_ADD etc.
////////////////////////////////////////////
function {:inline true} INT_EQ(x:int, y:int)  returns  (bool)   {x == y}
function {:inline true} INT_NEQ(x:int, y:int)  returns  (bool)   {x != y}

function {:inline true} INT_ADD(x:int, y:int)  returns  (int)   {x + y}
function {:inline true} INT_SUB(x:int, y:int)  returns  (int)   {x - y}
function {:inline true} INT_MULT(x:int, y:int) returns  (int)   {x * y}
function {:inline true} INT_DIV(x:int, y:int)  returns  (int)   {x div y}
function {:inline true} INT_LT(x:int, y:int)   returns  (bool)  {x < y}
function {:inline true} INT_ULT(x:int, y:int)   returns  (bool)  {x < y}
function {:inline true} INT_LEQ(x:int, y:int)  returns  (bool)  {x <= y}
function {:inline true} INT_ULEQ(x:int, y:int)  returns  (bool)  {x <= y}
function {:inline true} INT_GT(x:int, y:int)   returns  (bool)  {x > y}
function {:inline true} INT_UGT(x:int, y:int)   returns  (bool)  {x > y}
function {:inline true} INT_GEQ(x:int, y:int)  returns  (bool)  {x >= y}
function {:inline true} INT_UGEQ(x:int, y:int)  returns  (bool)  {x >= y}


////////////////////////////////////////////
/////// functions for bv32 type /////////////
// Theorem prover does not see INT_ADD etc.
// we are treating unsigned ops now
////////////////////////////////////////////
function {:inline true} BV32_EQ(x:bv32, y:bv32)  returns  (bool)   {x == y}
function {:inline true} BV32_NEQ(x:bv32, y:bv32)  returns  (bool)  {x != y}

function {:bvbuiltin "bvadd"}  BV32_ADD(x:bv32, y:bv32)  returns  (bv32);
function {:bvbuiltin "bvsub"}  BV32_SUB(x:bv32, y:bv32)  returns  (bv32);
function {:bvbuiltin "bvmul"}  BV32_MULT(x:bv32, y:bv32) returns  (bv32);
function {:bvbuiltin "bvudiv"} BV32_DIV(x:bv32, y:bv32)  returns  (bv32);
function {:bvbuiltin "bvult"}  BV32_ULT(x:bv32, y:bv32)   returns  (bool);
function {:bvbuiltin "bvslt"}  BV32_LT(x:bv32, y:bv32)   returns  (bool);
function {:bvbuiltin "bvule"}  BV32_ULEQ(x:bv32, y:bv32)  returns  (bool);
function {:bvbuiltin "bvsle"}  BV32_LEQ(x:bv32, y:bv32)  returns  (bool);
function {:bvbuiltin "bvugt"}  BV32_UGT(x:bv32, y:bv32)   returns  (bool);
function {:bvbuiltin "bvsgt"}  BV32_GT(x:bv32, y:bv32)   returns  (bool);
function {:bvbuiltin "bvuge"}  BV32_UGEQ(x:bv32, y:bv32)  returns  (bool);
function {:bvbuiltin "bvsge"}  BV32_GEQ(x:bv32, y:bv32)  returns  (bool);

//what about bitwise ops {BIT_AND, BIT_OR, BIT_NOT, ..}
//only enabled with bv theory
// function {:bvbuiltin "bvand"} BIT_BAND(a:int, b:int) returns (x:int);
// function {:bvbuiltin "bvor"}  BIT_BOR(a:int, b:int) returns (x:int);
// function {:bvbuiltin "bvxor"} BIT_BXOR(a:int, b:int) returns (x:int);
// function {:bvbuiltin "bvnot"} BIT_BNOT(a:int) returns (x:int);

//////////////////////////////////
// Generic C Arithmetic operations
/////////////////////////////////

//Is this sound for bv32?
function MINUS_BOTH_PTR_OR_BOTH_INT(a:int, b:int, size:int) returns (int); 
 axiom  (forall a:int, b:int, size:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)} 
//size * MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size) <= a - b && a - b < size * (MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size) + 1));
 INT_LEQ( INT_MULT(size, MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)),  INT_SUB(a, b)) && INT_LT( INT_SUB(a, b),  INT_MULT(size, (INT_ADD(MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size), 1)))));

//we just keep this axiom for size = 1
axiom  (forall a:int, b:int, size:int :: {MINUS_BOTH_PTR_OR_BOTH_INT(a,b,size)}  MINUS_BOTH_PTR_OR_BOTH_INT(a,b,1) == INT_SUB(a,b));


function MINUS_LEFT_PTR(a:int, a_size:int, b:int) returns (int);
//axiom(forall a:int, a_size:int, b:int :: {MINUS_LEFT_PTR(a,a_size,b)} MINUS_LEFT_PTR(a,a_size,b) == a - a_size * b);
axiom(forall a:int, a_size:int, b:int :: {MINUS_LEFT_PTR(a,a_size,b)} MINUS_LEFT_PTR(a,a_size,b) == INT_SUB(a, INT_MULT(a_size, b)));


function PLUS(a:int, a_size:int, b:int) returns (int);
//axiom (forall a:int, a_size:int, b:int :: {PLUS(a,a_size,b)} PLUS(a,a_size,b) == a + a_size * b);
axiom (forall a:int, a_size:int, b:int :: {PLUS(a,a_size,b)} PLUS(a,a_size,b) == INT_ADD(a, INT_MULT(a_size, b)));
 
function MULT(a:int, b:int) returns (int); // a*b
//axiom(forall a:int, b:int :: {MULT(a,b)} MULT(a,b) == a * b);
axiom(forall a:int, b:int :: {MULT(a,b)} MULT(a,b) == INT_MULT(a, b));
 
function DIV(a:int, b:int) returns (int); // a/b	

// Not sure if these axioms hold for BV too, just commet them for BV 	      
  
 

//uninterpreted binary op
function BINARY_BOTH_INT(a:int, b:int) returns (int);


//////////////////////////////////////////
//// Bitwise ops (uninterpreted, used with int)
//////////////////////////////////////////


 function BIT_BAND(a:int, b:int) returns (x:int);
 

 function BIT_BOR(a:int, b:int) returns (x:int);
 function BIT_BXOR(a:int, b:int) returns (x:int);
 function BIT_BNOT(a:int) returns (int);




function LIFT(a:bool) returns (int);
axiom(forall a:bool :: {LIFT(a)} a <==> LIFT(a) != 0);

function PTR_NOT(a:int) returns (int);
axiom(forall a:int :: {PTR_NOT(a)} a == 0 ==> PTR_NOT(a) != 0);
axiom(forall a:int :: {PTR_NOT(a)} a != 0 ==> PTR_NOT(a) == 0);

function NULL_CHECK(a:int) returns (int);
axiom(forall a:int :: {NULL_CHECK(a)} a == 0 ==> NULL_CHECK(a) != 0);
axiom(forall a:int :: {NULL_CHECK(a)} a != 0 ==> NULL_CHECK(a) == 0);

procedure havoc_assert(i:int);
requires (i != 0);

procedure havoc_assume(i:int);
ensures (i != 0);

procedure __HAVOC_free(a:int);

function NewAlloc(x:int, y:int) returns (z:int);

//Comments below make HAVOC_malloc deterministic

procedure __HAVOC_malloc(obj_size:int) returns (new:int);
//requires obj_size >= 0;
free requires INT_GEQ(obj_size, 0);
modifies alloc;
ensures new == old(alloc);
//ensures alloc > new + obj_size;
ensures INT_GT(alloc, INT_ADD(new, obj_size));
//ensures alloc == NewAlloc(old(alloc), obj_size);




procedure _strdup(str:int) returns (new:int);

procedure _xstrcasecmp(a0:int, a1:int) returns (ret:int);

procedure _xstrcmp(a0:int, a1:int) returns (ret:int);


/*
//bv functions
function bv8ToInt(bv8)   returns (int);
function bv16ToInt(bv16) returns (int);
function bv32ToInt(bv32) returns (int);
function bv64ToInt(bv64) returns (int);

function intToBv8(int)    returns (bv8);
function intToBv16(int)   returns (bv16);
function intToBv32(int)   returns (bv32);
function intToBv64(int)   returns (bv64);

axiom(forall a:int ::  {intToBv8(a)} bv8ToInt(intToBv8(a)) == a);
axiom(forall a:int ::  {intToBv16(a)} bv16ToInt(intToBv16(a)) == a);
axiom(forall a:int ::  {intToBv32(a)} bv32ToInt(intToBv32(a)) == a);
axiom(forall a:int ::  {intToBv64(a)} bv64ToInt(intToBv64(a)) == a);

axiom(forall b:bv8 ::  {bv8ToInt(b)} intToBv8(bv8ToInt(b)) == b);
axiom(forall b:bv16 ::  {bv16ToInt(b)} intToBv16(bv16ToInt(b)) == b);
axiom(forall b:bv32 ::  {bv32ToInt(b)} intToBv32(bv32ToInt(b)) == b);
axiom(forall b:bv64 ::  {bv64ToInt(b)} intToBv64(bv64ToInt(b)) == b);
*/



var Res_0_COMPLETED : [int]int;
var Res_1_COMPLETED : [int]int;
var Res_s_1_COMPLETED : [int]int;
var Res_KERNEL_SOURCE:[int]int;
var Res_0_LOCK : [int]int;
var Res_1_LOCK : [int]int;
var Res_s_1_LOCK : [int]int;
var Res_PROBED:[int]int;

//Pointer constants

//Function pointer constants


const unique Globals : int;
axiom(Globals != 0);
const unique I8xCompleteSysButtonEventWorker : int;
axiom(I8xCompleteSysButtonEventWorker != 0);
const unique I8xPowerUpToD0Complete : int;
axiom(I8xPowerUpToD0Complete != 0);
const unique I8xReinitializeHardware : int;
axiom(I8xReinitializeHardware != 0);
const unique I8xSysButtonCancelRoutine : int;
axiom(I8xSysButtonCancelRoutine != 0);
var cancelLockStatus_0 : int;
var cancelLockStatus_1 : int;
var cancelLockStatus_s_1 : int;

const unique hdevobj : int;
axiom(hdevobj != 0);
// the set of constants for 64 bit integers that Boogie doesn't parse
const unique BOOGIE_LARGE_INT_2147483648:int;



procedure DRIVER_CANCEL(a0:int, a1:int);



procedure ExFreePoolWithTag(a0:int, a1:int);



procedure IO_COMPLETION_ROUTINE(a0:int, a1:int, a2:int) returns (ret:int);



procedure IoAcquireRemoveLockEx(a0:int, a1:int, a2:int, a3:int, a4:int) returns (ret:int);



procedure IoAllocateWorkItem(a0:int) returns (ret:int);



procedure IoDisconnectInterrupt(a0:int);



procedure IoFreeWorkItem(a0:int);



procedure IoQueueWorkItem(a0:int, a1:int, a2:int, a3:int);



procedure IoReleaseRemoveLockEx(a0:int, a1:int, a2:int);



procedure PoSetPowerState(a0:int, a1:int, a2:int) returns (ret:int);



procedure PoStartNextPowerIrp(a0:int);



procedure __PREfastPagedCode();



procedure __storm_assert_dummy();



procedure __storm_atomic_begin_dummy();



procedure __storm_atomic_end_dummy();



procedure memcpy(a0:int, a1:int, a2:int) returns (ret:int);



procedure memset(a0:int, a1:int, a2:int) returns (ret:int);






procedure storm_nondet() returns (ret:int);



procedure storm_main();
  free requires 0 < alloc;
  free requires 0 < tid;
  free requires tid < tidCount;
  requires INT_LT(PLUS(hdevobj, 1, 184), alloc);
  modifies tidCount, alloc, raiseException, cancelLockStatus_s_1, __storm_init, __storm_atomic, errorReached, cancelLockStatus_0, cancelLockStatus_1, __storm_thread_done_3, __storm_thread_done_2, __storm_thread_done_1, __storm_thread_done_0, tid, k, Res_0_COMPLETED, Res_1_COMPLETED, Res_KERNEL_SOURCE, Res_0_LOCK, Res_1_LOCK, Res_PROBED, Mem_0_T.CancelRoutine__IRP, Mem_1_T.CancelRoutine__IRP, Mem_0_T.Cancel__IRP, Mem_1_T.Cancel__IRP, Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23, Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23, Mem_0_T.DeviceExtension__DEVICE_OBJECT, Mem_1_T.DeviceExtension__DEVICE_OBJECT, Mem_0_T.DeviceObject__IO_STACK_LOCATION, Mem_1_T.DeviceObject__IO_STACK_LOCATION;



implementation storm_main()
{
  var inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock_.1: int, inline$storm_IoMarkIrpPending$2$$pirp$1$376.14$storm_IoMarkIrpPending_.1: int, $irpSp$2$92.21$storm_main: int, inline$storm_IoCancelIrp$0$myNondetVar_0: int, inline$storm_IoCancelIrp$0$myNondetVar_1: int, inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl_.1: int, inline$storm_IoSetCancelRoutine$0$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine: int, inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp: int, inline$storm_getThreadID$5$tidRet: int, inline$storm_KeAcquireSpinLock$0$$lockStatus$4$129.6$storm_KeAcquireSpinLock: int, inline$storm_IoCancelIrp$0$$result.storm_nondet$365.4$2$: int, inline$storm_IoMarkIrpPending$0$$result.storm_nondet$379.2$1$: int, inline$storm_KeAcquireSpinLock$1$$tid$3$128.6$storm_KeAcquireSpinLock: int, inline$storm_IoSetCancelRoutine$1$$result.storm_nondet$391.2$2$: int, inline$I8xKeyboardGetSysButtonCaps$0$$Irp$2$70.9$I8xKeyboardGetSysButtonCaps: int, inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine: int, inline$IoSetNextIrpStackLocation$0$tempBoogie0: int, inline$storm_IoAcquireCancelSpinLock$0$$result.storm_getThreadID$185.29$1$: int, inline$storm_IoSetCancelRoutine$1$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine_.1: int, inline$IoGetCurrentIrpStackLocation$5$myVar_0: int, inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest_.1: int, inline$storm_IoMarkIrpPending$0$$pirp$1$376.14$storm_IoMarkIrpPending: int, inline$IoGetCurrentIrpStackLocation$0$myVar_0: int, inline$I8xKeyboardGetSysButtonEvent$0$$KeyboardExtension$1$148.29$I8xKeyboardGetSysButtonEvent_.1: int, inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_1: int, inline$storm_IoCompleteRequest$4$$result.storm_nondet$343.2$1$: int, inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp: int, inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock: int, $result.IoGetCurrentIrpStackLocation$99.38$2$: int, inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0: int, inline$storm_IoAllocateIrp$0$$result.storm_IoAllocateIrp$275.0$1$: int, inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock: int, inline$storm_IoMarkIrpPending$2$$pirp$1$376.14$storm_IoMarkIrpPending: int, inline$I8xKeyboardGetSysButtonEvent$0$$KeyboardExtension$1$148.29$I8xKeyboardGetSysButtonEvent: int, inline$I8xDeviceControl$0$$DeviceObject$1$464.22$I8xDeviceControl: int, inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest: int, inline$dispatch$0$$Irp$1$8.19$dispatch_.1: int, inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation: int, inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest_.1: int, inline$I8xDeviceControl$0$$kbExtension$3$468.32$I8xDeviceControl: int, inline$storm_IoMarkIrpPending$1$$pirp$1$376.14$storm_IoMarkIrpPending: int, inline$storm_getThreadID$0$tidRet: int, inline$myInitDriver$0$$kbExtension$2$5.27$myInitDriver: int, inline$I8xKeyboardGetSysButtonEvent$0$$irql$8$156.24$I8xKeyboardGetSysButtonEvent: int, inline$storm_IoSetCancelRoutine$0$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine_.1: int, inline$IoGetCurrentIrpStackLocation$0$$result.IoGetCurrentIrpStackLocation$23297.0$1$: int, inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_nondet$257.41$7$: int, inline$I8xKeyboardGetSysButtonCaps$0$tempBoogie0: int, inline$storm_getThreadID$1$tidRet: int, inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_ExAllocatePoolWithTag$177.12$3$: int, inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock: int, inline$cancel$0$$Irp$1$64.17$cancel: int, inline$storm_IoAllocateIrp$0$$malloc.arg.1$5$: int, inline$storm_IoCompleteRequest$0$$result.storm_nondet$343.2$1$: int, inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine: int, inline$IoGetCurrentIrpStackLocation$5$$result.IoGetCurrentIrpStackLocation$23297.0$1$: int, inline$cancel$0$$Irp$1$64.17$cancel_.1: int, $irp$1$91.7$storm_main: int, inline$myInitDriver$0$myNondetVar_0: int, inline$myInitDriver$0$myNondetVar_1: int, inline$storm_getThreadID$4$tidRet: int, inline$storm_IoMarkIrpPending$1$$result.storm_nondet$379.2$1$: int, inline$storm_IoCancelIrp$0$$result.IoGetCurrentIrpStackLocation$366.40$3$: int, inline$IoSetNextIrpStackLocation$0$myNondetVar_0: int, inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_IoSetCancelRoutine$237.37$6$: int, inline$storm_KeAcquireSpinLock$1$$result.storm_getThreadID$128.29$1$: int, inline$I8xKeyboardGetSysButtonEvent$0$$result.IoAllocateWorkItem$180.43$4$: int, inline$I8xSysButtonCancelRoutine$0$myVar_0: int, inline$IoGetNextIrpStackLocation$0$myVar_0: int, inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest: int, k_old_2: int, inline$storm_IoCancelIrp$0$$irpSp$3$364.23$storm_IoCancelIrp: int, inline$storm_IoAllocateIrp$0$$result.storm_nondet$282.22$2$: int, inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine_.1: int, inline$I8xSysButtonCancelRoutine$0$$Irp$2$374.12$I8xSysButtonCancelRoutine_.1: int, inline$I8xSysButtonCancelRoutine$0$$Irp$2$374.12$I8xSysButtonCancelRoutine: int, inline$storm_IoMarkIrpPending$2$$result.storm_nondet$379.2$1$: int, inline$storm_IoReleaseCancelSpinLock$0$$result.storm_getThreadID$198.0$1$: int, inline$IoGetNextIrpStackLocation$0$$result.IoGetNextIrpStackLocation$23462.0$1$: int, inline$I8xCompleteSysButtonIrp$0$$Irp$1$50.9$I8xCompleteSysButtonIrp: int, inline$storm_IoAllocateIrp$0$$result.malloc$284.0$3$: int, inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp_.1: int, k_old_1: int, k_old_0: int, inline$I8xKeyboardGetSysButtonEvent$0$$item$9$172.32$I8xKeyboardGetSysButtonEvent: int, inline$storm_IoCancelIrp$0$myVar_0: int, inline$I8xKeyboardGetSysButtonEvent$0$myVar_0: int, inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest: int, inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps: int, inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine_.1: int, inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest_.1: int, inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl: int, inline$storm_KeInitializeSpinLock$0$$SpinLock$1$116.17$storm_KeInitializeSpinLock_.1: int, inline$storm_IoSetCancelRoutine$0$$result.storm_nondet$391.2$2$: int, inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock: int, inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock_.1: int, inline$I8xSysButtonCancelRoutine$0$$irql$5$379.10$I8xSysButtonCancelRoutine: int, inline$storm_ExAllocatePoolWithTag$0$$result.storm_ExAllocatePoolWithTag$509.0$1$: int, inline$IoGetNextIrpStackLocation$0$$Irp$1$23463.14$IoGetNextIrpStackLocation_.1: int, inline$storm_IoAllocateIrp$0$$result.malloc$284.0$4$: int, inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest: int, inline$storm_KeReleaseSpinLock$0$$result.storm_getThreadID$145.0$1$: int, inline$I8xSysButtonCancelRoutine$0$myNondetVar_1: int, inline$I8xSysButtonCancelRoutine$0$myNondetVar_0: int, inline$I8xCompleteSysButtonIrp$0$$Irp$1$50.9$I8xCompleteSysButtonIrp_.1: int, inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest_.1: int, inline$storm_IoSetCancelRoutine$1$$result.storm_IoSetCancelRoutine$385.0$1$: int, inline$storm_KeReleaseSpinLock$1$$result.storm_getThreadID$145.0$1$: int, inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0: int, inline$I8xSysButtonCancelRoutine$0$$kbExtension$3$377.29$I8xSysButtonCancelRoutine: int, inline$I8xDeviceControl$0$myVar_0: int, inline$IoGetCurrentIrpStackLocation$0$$Irp$1$23298.14$IoGetCurrentIrpStackLocation_.1: int, inline$storm_IoSetCancelRoutine$1$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine: int, inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock_.1: int, inline$IoGetCurrentIrpStackLocation$0$$Irp$1$23298.14$IoGetCurrentIrpStackLocation: int, inline$storm_IoSetCancelRoutine$1$myVar_0: int, inline$I8xDeviceControl$0$$DeviceObject$1$464.22$I8xDeviceControl_.1: int, inline$storm_KeAcquireSpinLock$1$$lockStatus$4$129.6$storm_KeAcquireSpinLock: int, inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest_.1: int, inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation_.1: int, inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock: int, inline$storm_getThreadID$3$tidRet: int, inline$IoGetCurrentIrpStackLocation$5$$Irp$1$23298.14$IoGetCurrentIrpStackLocation_.1: int, inline$storm_ExAllocatePoolWithTag$0$$result.malloc$515.15$2$: int, inline$storm_IoCompleteRequest$1$$result.storm_nondet$343.2$1$: int, inline$storm_ExAllocatePoolWithTag$0$$NumberOfBytes$2$511.12$storm_ExAllocatePoolWithTag: int, inline$IoSetNextIrpStackLocation$0$myVar_0: int, inline$storm_IoAllocateIrp$0$$irpSp$4$281.21$storm_IoAllocateIrp: int, inline$storm_KeInitializeSpinLock$0$$SpinLock$1$116.17$storm_KeInitializeSpinLock: int, inline$storm_IoAllocateIrp$0$$result.IoGetNextIrpStackLocation$284.0$6$: int, inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent: int, inline$storm_getThreadID$2$tidRet: int, inline$I8xDeviceControl$0$myNondetVar_0: int, inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp: int, inline$IoGetNextIrpStackLocation$0$$Irp$1$23463.14$IoGetNextIrpStackLocation: int, inline$storm_KeAcquireSpinLock$0$$tid$3$128.6$storm_KeAcquireSpinLock: int, inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent: int, inline$dispatch$0$$Irp$1$8.19$dispatch: int, inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock_.1: int, inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest: int, inline$I8xSysButtonCancelRoutine$0$$DeviceObject$1$373.22$I8xSysButtonCancelRoutine: int, inline$I8xKeyboardGetSysButtonCaps$0$$Irp$2$70.9$I8xKeyboardGetSysButtonCaps_.1: int, inline$storm_IoCancelIrp$0$$oldCancelRoutine$2$352.17$storm_IoCancelIrp: int, $result.storm_IoAllocateIrp$96.21$1$: int, tidCount_old: int, inline$storm_IoSetCancelRoutine$1$$oldCancelRoutine$3$390.17$storm_IoSetCancelRoutine: int, inline$I8xSysButtonCancelRoutine$0$$DeviceObject$1$373.22$I8xSysButtonCancelRoutine_.1: int, inline$storm_IoMarkIrpPending$1$$pirp$1$376.14$storm_IoMarkIrpPending_.1: int, inline$storm_KeReleaseSpinLock$1$$lockStatus$3$144.6$storm_KeReleaseSpinLock: int, inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent_.1: int, inline$IoGetCurrentIrpStackLocation$5$$Irp$1$23298.14$IoGetCurrentIrpStackLocation: int, inline$storm_ExAllocatePoolWithTag$0$$NumberOfBytes$2$511.12$storm_ExAllocatePoolWithTag_.1: int, inline$storm_KeReleaseSpinLock$0$$lockStatus$3$144.6$storm_KeReleaseSpinLock: int, inline$I8xCompleteSysButtonIrp$0$myNondetVar_0: int, inline$myInitDriver$0$myVar_0: int, tid_old_1: int, tid_old_0: int, tid_old_2: int, inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp_.1: int, inline$storm_IoCompleteRequest$3$$result.storm_nondet$343.2$1$: int, inline$storm_KeAcquireSpinLock$0$$result.storm_getThreadID$128.29$1$: int, inline$storm_IoMarkIrpPending$0$$pirp$1$376.14$storm_IoMarkIrpPending_.1: int, inline$storm_IoCompleteRequest$2$$result.storm_nondet$343.2$1$: int;

  start#2:
    assume Res_1_COMPLETED == Res_s_1_COMPLETED;
    assume Res_1_LOCK == Res_s_1_LOCK;
    assume Mem_1_T.CancelRoutine__IRP == Mem_s_1_T.CancelRoutine__IRP;
    assume Mem_1_T.Cancel__IRP == Mem_s_1_T.Cancel__IRP;
    assume Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23 == Mem_s_1_T.CurrentStackLocation___unnamed_4_3c640f23;
    assume Mem_1_T.DeviceExtension__DEVICE_OBJECT == Mem_s_1_T.DeviceExtension__DEVICE_OBJECT;
    assume Mem_1_T.DeviceObject__IO_STACK_LOCATION == Mem_s_1_T.DeviceObject__IO_STACK_LOCATION;
    assume cancelLockStatus_1 == cancelLockStatus_s_1;
    __storm_thread_done_0 := false;
    __storm_thread_done_1 := false;
    __storm_thread_done_2 := false;
    __storm_thread_done_3 := false;
    k := 0;
    errorReached := false;
    __storm_atomic := false;
    __storm_init := false;
    goto label_3#2;

  label_3#2:
    goto label_4#2;

  label_4#2:
    goto label_5#2;

  label_5#2:
    goto anon22_Then#2, anon22_Else#2;

  anon22_Else#2:
    assume k != 0;
    goto anon23_Then#2, anon23_Else#2;

  anon23_Else#2:
    assume k != 1;
    goto anon2#2;

  anon23_Then#2:
    assume k == 1;
    cancelLockStatus_1 := 0;
    goto anon2#2;

  anon22_Then#2:
    assume k == 0;
    cancelLockStatus_0 := 0;
    goto anon2#2;

  anon2#2:
    call contextSwitch();
    goto label_6#2;

  label_6#2:
    goto inline$storm_IoAllocateIrp$0$Entry#2;

  inline$storm_IoAllocateIrp$0$Entry#2:
    inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp_.1 := 2;
    goto inline$storm_IoAllocateIrp$0$start#2;

  inline$storm_IoAllocateIrp$0$start#2:
    inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp := inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp_.1;
    goto inline$storm_IoAllocateIrp$0$label_3#2;

  inline$storm_IoAllocateIrp$0$label_3#2:
    goto inline$storm_IoAllocateIrp$0$label_4#2;

  inline$storm_IoAllocateIrp$0$label_4#2:
    goto inline$storm_IoAllocateIrp$0$label_5#2;

  inline$storm_IoAllocateIrp$0$label_5#2:
    call inline$storm_IoAllocateIrp$0$$result.storm_nondet$282.22$2$ := storm_nondet();
    goto inline$storm_IoAllocateIrp$0$label_8#2;

  inline$storm_IoAllocateIrp$0$label_8#2:
    goto inline$storm_IoAllocateIrp$0$label_8_case_0#2, inline$storm_IoAllocateIrp$0$label_8_case_1#2;

  inline$storm_IoAllocateIrp$0$label_8_case_1#2:
    assume inline$storm_IoAllocateIrp$0$$result.storm_nondet$282.22$2$ == 0;
    goto inline$storm_IoAllocateIrp$0$label_10#2;

  inline$storm_IoAllocateIrp$0$label_10#2:
    __storm_atomic := true;
    goto inline$storm_IoAllocateIrp$0$label_13#2;

  inline$storm_IoAllocateIrp$0$label_13#2:
    call inline$storm_IoAllocateIrp$0$$result.malloc$284.0$3$ := __HAVOC_malloc(112);
    goto inline$storm_IoAllocateIrp$0$label_16#2;

  inline$storm_IoAllocateIrp$0$label_16#2:
    inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp := inline$storm_IoAllocateIrp$0$$result.malloc$284.0$3$;
    goto inline$storm_IoAllocateIrp$0$label_17#2;

  inline$storm_IoAllocateIrp$0$label_17#2:
    goto inline$storm_IoAllocateIrp$0$anon18_Then#2, inline$storm_IoAllocateIrp$0$anon18_Else#2;

  inline$storm_IoAllocateIrp$0$anon18_Else#2:
    assume k != 0;
    goto inline$storm_IoAllocateIrp$0$anon19_Then#2, inline$storm_IoAllocateIrp$0$anon19_Else#2;

  inline$storm_IoAllocateIrp$0$anon19_Else#2:
    assume k != 1;
    goto inline$storm_IoAllocateIrp$0$anon2#2;

  inline$storm_IoAllocateIrp$0$anon19_Then#2:
    assume k == 1;
    Mem_1_T.Cancel__IRP := Mem_1_T.Cancel__IRP[Cancel__IRP(inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp) := 0];
    goto inline$storm_IoAllocateIrp$0$anon2#2;

  inline$storm_IoAllocateIrp$0$anon18_Then#2:
    assume k == 0;
    Mem_0_T.Cancel__IRP := Mem_0_T.Cancel__IRP[Cancel__IRP(inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp) := 0];
    goto inline$storm_IoAllocateIrp$0$anon2#2;

  inline$storm_IoAllocateIrp$0$anon2#2:
    call contextSwitch();
    goto inline$storm_IoAllocateIrp$0$label_18#2;

  inline$storm_IoAllocateIrp$0$label_18#2:
    goto inline$storm_IoAllocateIrp$0$anon20_Then#2, inline$storm_IoAllocateIrp$0$anon20_Else#2;

  inline$storm_IoAllocateIrp$0$anon20_Else#2:
    assume k != 0;
    goto inline$storm_IoAllocateIrp$0$anon21_Then#2, inline$storm_IoAllocateIrp$0$anon21_Else#2;

  inline$storm_IoAllocateIrp$0$anon21_Else#2:
    assume k != 1;
    goto inline$storm_IoAllocateIrp$0$anon5#2;

  inline$storm_IoAllocateIrp$0$anon21_Then#2:
    assume k == 1;
    Mem_1_T.CancelRoutine__IRP := Mem_1_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp) := 0];
    goto inline$storm_IoAllocateIrp$0$anon5#2;

  inline$storm_IoAllocateIrp$0$anon20_Then#2:
    assume k == 0;
    Mem_0_T.CancelRoutine__IRP := Mem_0_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp) := 0];
    goto inline$storm_IoAllocateIrp$0$anon5#2;

  inline$storm_IoAllocateIrp$0$anon5#2:
    call contextSwitch();
    goto inline$storm_IoAllocateIrp$0$label_19#2;

  inline$storm_IoAllocateIrp$0$label_19#2:
    goto inline$storm_IoAllocateIrp$0$anon22_Then#2, inline$storm_IoAllocateIrp$0$anon22_Else#2;

  inline$storm_IoAllocateIrp$0$anon22_Else#2:
    assume k != 0;
    goto inline$storm_IoAllocateIrp$0$anon23_Then#2, inline$storm_IoAllocateIrp$0$anon23_Else#2;

  inline$storm_IoAllocateIrp$0$anon23_Else#2:
    assume k != 1;
    goto inline$storm_IoAllocateIrp$0$anon8#2;

  inline$storm_IoAllocateIrp$0$anon23_Then#2:
    assume k == 1;
    Res_1_COMPLETED := Res_1_COMPLETED[inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp := 0];
    goto inline$storm_IoAllocateIrp$0$anon8#2;

  inline$storm_IoAllocateIrp$0$anon22_Then#2:
    assume k == 0;
    Res_0_COMPLETED := Res_0_COMPLETED[inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp := 0];
    goto inline$storm_IoAllocateIrp$0$anon8#2;

  inline$storm_IoAllocateIrp$0$anon8#2:
    call contextSwitch();
    goto inline$storm_IoAllocateIrp$0$label_20#2;

  inline$storm_IoAllocateIrp$0$label_20#2:
    havoc raiseException;
    goto inline$storm_IoAllocateIrp$0$anon24_Then#2, inline$storm_IoAllocateIrp$0$anon24_Else#2;

  inline$storm_IoAllocateIrp$0$anon24_Else#2:
    assume !raiseException;
    goto inline$storm_IoAllocateIrp$0$anon10#2;

  inline$storm_IoAllocateIrp$0$anon10#2:
    assume INT_LT(0, inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp);
    goto inline$storm_IoAllocateIrp$0$label_21#2;

  inline$storm_IoAllocateIrp$0$label_21#2:
    inline$storm_IoAllocateIrp$0$$malloc.arg.1$5$ := MULT(inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp, 36);
    goto inline$storm_IoAllocateIrp$0$label_22#2;

  inline$storm_IoAllocateIrp$0$label_22#2:
    call inline$storm_IoAllocateIrp$0$$result.malloc$284.0$4$ := __HAVOC_malloc(inline$storm_IoAllocateIrp$0$$malloc.arg.1$5$);
    goto inline$storm_IoAllocateIrp$0$label_25#2;

  inline$storm_IoAllocateIrp$0$label_25#2:
    inline$storm_IoAllocateIrp$0$$irpSp$4$281.21$storm_IoAllocateIrp := inline$storm_IoAllocateIrp$0$$result.malloc$284.0$4$;
    goto inline$storm_IoAllocateIrp$0$label_26#2;

  inline$storm_IoAllocateIrp$0$label_26#2:
    goto inline$storm_IoAllocateIrp$0$anon25_Then#2, inline$storm_IoAllocateIrp$0$anon25_Else#2;

  inline$storm_IoAllocateIrp$0$anon25_Else#2:
    assume k != 0;
    goto inline$storm_IoAllocateIrp$0$anon26_Then#2, inline$storm_IoAllocateIrp$0$anon26_Else#2;

  inline$storm_IoAllocateIrp$0$anon26_Else#2:
    assume k != 1;
    goto inline$storm_IoAllocateIrp$0$anon13#2;

  inline$storm_IoAllocateIrp$0$anon26_Then#2:
    assume k == 1;
    Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23 := Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp))))) := PLUS(inline$storm_IoAllocateIrp$0$$irpSp$4$281.21$storm_IoAllocateIrp, 36, inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp)];
    goto inline$storm_IoAllocateIrp$0$anon13#2;

  inline$storm_IoAllocateIrp$0$anon25_Then#2:
    assume k == 0;
    Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23 := Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp))))) := PLUS(inline$storm_IoAllocateIrp$0$$irpSp$4$281.21$storm_IoAllocateIrp, 36, inline$storm_IoAllocateIrp$0$$StackSize$1$276.11$storm_IoAllocateIrp)];
    goto inline$storm_IoAllocateIrp$0$anon13#2;

  inline$storm_IoAllocateIrp$0$anon13#2:
    call contextSwitch();
    goto inline$storm_IoAllocateIrp$0$label_27#2;

  inline$storm_IoAllocateIrp$0$label_27#2:
    goto inline$IoGetNextIrpStackLocation$0$Entry#2;

  inline$IoGetNextIrpStackLocation$0$Entry#2:
    inline$IoGetNextIrpStackLocation$0$$Irp$1$23463.14$IoGetNextIrpStackLocation_.1 := inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp;
    goto inline$IoGetNextIrpStackLocation$0$start#2;

  inline$IoGetNextIrpStackLocation$0$start#2:
    inline$IoGetNextIrpStackLocation$0$$Irp$1$23463.14$IoGetNextIrpStackLocation := inline$IoGetNextIrpStackLocation$0$$Irp$1$23463.14$IoGetNextIrpStackLocation_.1;
    goto inline$IoGetNextIrpStackLocation$0$label_3#2;

  inline$IoGetNextIrpStackLocation$0$label_3#2:
    goto inline$IoGetNextIrpStackLocation$0$anon3_Then#2, inline$IoGetNextIrpStackLocation$0$anon3_Else#2;

  inline$IoGetNextIrpStackLocation$0$anon3_Else#2:
    assume k != 0;
    goto inline$IoGetNextIrpStackLocation$0$anon4_Then#2, inline$IoGetNextIrpStackLocation$0$anon4_Else#2;

  inline$IoGetNextIrpStackLocation$0$anon4_Else#2:
    assume k != 1;
    goto inline$IoGetNextIrpStackLocation$0$anon2#2;

  inline$IoGetNextIrpStackLocation$0$anon4_Then#2:
    assume k == 1;
    inline$IoGetNextIrpStackLocation$0$myVar_0 := Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoGetNextIrpStackLocation$0$$Irp$1$23463.14$IoGetNextIrpStackLocation)))))];
    goto inline$IoGetNextIrpStackLocation$0$anon2#2;

  inline$IoGetNextIrpStackLocation$0$anon3_Then#2:
    assume k == 0;
    inline$IoGetNextIrpStackLocation$0$myVar_0 := Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoGetNextIrpStackLocation$0$$Irp$1$23463.14$IoGetNextIrpStackLocation)))))];
    goto inline$IoGetNextIrpStackLocation$0$anon2#2;

  inline$IoGetNextIrpStackLocation$0$anon2#2:
    call contextSwitch();
    inline$IoGetNextIrpStackLocation$0$$result.IoGetNextIrpStackLocation$23462.0$1$ := MINUS_LEFT_PTR(inline$IoGetNextIrpStackLocation$0$myVar_0, 36, 1);
    goto inline$IoGetNextIrpStackLocation$0$label_1#2;

  inline$IoGetNextIrpStackLocation$0$label_1#2:
    goto inline$IoGetNextIrpStackLocation$0$Return#2;

  inline$IoGetNextIrpStackLocation$0$Return#2:
    inline$storm_IoAllocateIrp$0$$result.IoGetNextIrpStackLocation$284.0$6$ := inline$IoGetNextIrpStackLocation$0$$result.IoGetNextIrpStackLocation$23462.0$1$;
    goto inline$storm_IoAllocateIrp$0$label_27$1#2;

  inline$storm_IoAllocateIrp$0$label_27$1#2:
    goto inline$storm_IoAllocateIrp$0$anon27_Then#2, inline$storm_IoAllocateIrp$0$anon27_Else#2;

  inline$storm_IoAllocateIrp$0$anon27_Else#2:
    assume !raiseException;
    goto inline$storm_IoAllocateIrp$0$anon15#2;

  inline$storm_IoAllocateIrp$0$anon15#2:
    goto inline$storm_IoAllocateIrp$0$label_30#2;

  inline$storm_IoAllocateIrp$0$label_30#2:
    inline$storm_IoAllocateIrp$0$$irpSp$4$281.21$storm_IoAllocateIrp := inline$storm_IoAllocateIrp$0$$result.IoGetNextIrpStackLocation$284.0$6$;
    goto inline$storm_IoAllocateIrp$0$label_31#2;

  inline$storm_IoAllocateIrp$0$label_31#2:
    goto inline$storm_IoAllocateIrp$0$label_32#2;

  inline$storm_IoAllocateIrp$0$label_32#2:
    goto inline$storm_IoAllocateIrp$0$label_33#2;

  inline$storm_IoAllocateIrp$0$label_33#2:
    goto inline$storm_IoAllocateIrp$0$anon28_Then#2, inline$storm_IoAllocateIrp$0$anon28_Else#2;

  inline$storm_IoAllocateIrp$0$anon28_Else#2:
    assume __storm_init;
    goto inline$storm_IoAllocateIrp$0$anon17#2;

  inline$storm_IoAllocateIrp$0$anon28_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_IoAllocateIrp$0$anon17#2;

  inline$storm_IoAllocateIrp$0$anon17#2:
    call contextSwitch();
    goto inline$storm_IoAllocateIrp$0$label_36#2;

  inline$storm_IoAllocateIrp$0$anon27_Then#2:
    assume raiseException;
    goto inline$storm_IoAllocateIrp$0$Return#2;

  inline$storm_IoAllocateIrp$0$anon24_Then#2:
    assume raiseException;
    goto inline$storm_IoAllocateIrp$0$Return#2;

  inline$storm_IoAllocateIrp$0$label_8_case_0#2:
    assume inline$storm_IoAllocateIrp$0$$result.storm_nondet$282.22$2$ != 0;
    goto inline$storm_IoAllocateIrp$0$label_9#2;

  inline$storm_IoAllocateIrp$0$label_9#2:
    inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp := 0;
    goto inline$storm_IoAllocateIrp$0$label_36#2;

  inline$storm_IoAllocateIrp$0$label_36#2:
    inline$storm_IoAllocateIrp$0$$result.storm_IoAllocateIrp$275.0$1$ := inline$storm_IoAllocateIrp$0$$createdIrp$3$280.7$storm_IoAllocateIrp;
    goto inline$storm_IoAllocateIrp$0$label_1#2;

  inline$storm_IoAllocateIrp$0$label_1#2:
    goto inline$storm_IoAllocateIrp$0$Return#2;

  inline$storm_IoAllocateIrp$0$Return#2:
    $result.storm_IoAllocateIrp$96.21$1$ := inline$storm_IoAllocateIrp$0$$result.storm_IoAllocateIrp$275.0$1$;
    goto label_6$1#2;

  label_6$1#2:
    goto anon24_Then#2, anon24_Else#2;

  anon24_Else#2:
    assume !raiseException;
    goto anon4#2;

  anon4#2:
    goto label_9#2;

  label_9#2:
    $irp$1$91.7$storm_main := $result.storm_IoAllocateIrp$96.21$1$;
    goto label_10#2;

  label_10#2:
    havoc raiseException;
    goto anon25_Then#2, anon25_Else#2;

  anon25_Else#2:
    assume !raiseException;
    goto anon6#2;

  anon6#2:
    assume INT_NEQ($irp$1$91.7$storm_main, 0);
    goto label_11#2;

  label_11#2:
    goto inline$IoSetNextIrpStackLocation$0$Entry#2;

  inline$IoSetNextIrpStackLocation$0$Entry#2:
    inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation_.1 := $irp$1$91.7$storm_main;
    goto inline$IoSetNextIrpStackLocation$0$start#2;

  inline$IoSetNextIrpStackLocation$0$start#2:
    inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation := inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation_.1;
    goto inline$IoSetNextIrpStackLocation$0$label_3#2;

  inline$IoSetNextIrpStackLocation$0$label_3#2:
    havoc inline$IoSetNextIrpStackLocation$0$myNondetVar_0;
    inline$IoSetNextIrpStackLocation$0$tempBoogie0 := MINUS_BOTH_PTR_OR_BOTH_INT(inline$IoSetNextIrpStackLocation$0$myNondetVar_0, 1, 1);
    goto inline$IoSetNextIrpStackLocation$0$label_4#2;

  inline$IoSetNextIrpStackLocation$0$label_4#2:
    goto inline$IoSetNextIrpStackLocation$0$anon6_Then#2, inline$IoSetNextIrpStackLocation$0$anon6_Else#2;

  inline$IoSetNextIrpStackLocation$0$anon6_Else#2:
    assume k != 0;
    goto inline$IoSetNextIrpStackLocation$0$anon7_Then#2, inline$IoSetNextIrpStackLocation$0$anon7_Else#2;

  inline$IoSetNextIrpStackLocation$0$anon7_Else#2:
    assume k != 1;
    goto inline$IoSetNextIrpStackLocation$0$anon2#2;

  inline$IoSetNextIrpStackLocation$0$anon7_Then#2:
    assume k == 1;
    inline$IoSetNextIrpStackLocation$0$myVar_0 := Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation)))))];
    goto inline$IoSetNextIrpStackLocation$0$anon2#2;

  inline$IoSetNextIrpStackLocation$0$anon6_Then#2:
    assume k == 0;
    inline$IoSetNextIrpStackLocation$0$myVar_0 := Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation)))))];
    goto inline$IoSetNextIrpStackLocation$0$anon2#2;

  inline$IoSetNextIrpStackLocation$0$anon2#2:
    call contextSwitch();
    inline$IoSetNextIrpStackLocation$0$tempBoogie0 := MINUS_LEFT_PTR(inline$IoSetNextIrpStackLocation$0$myVar_0, 36, 1);
    goto inline$IoSetNextIrpStackLocation$0$anon8_Then#2, inline$IoSetNextIrpStackLocation$0$anon8_Else#2;

  inline$IoSetNextIrpStackLocation$0$anon8_Else#2:
    assume k != 0;
    goto inline$IoSetNextIrpStackLocation$0$anon9_Then#2, inline$IoSetNextIrpStackLocation$0$anon9_Else#2;

  inline$IoSetNextIrpStackLocation$0$anon9_Else#2:
    assume k != 1;
    goto inline$IoSetNextIrpStackLocation$0$anon5#2;

  inline$IoSetNextIrpStackLocation$0$anon9_Then#2:
    assume k == 1;
    Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23 := Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation))))) := inline$IoSetNextIrpStackLocation$0$tempBoogie0];
    goto inline$IoSetNextIrpStackLocation$0$anon5#2;

  inline$IoSetNextIrpStackLocation$0$anon8_Then#2:
    assume k == 0;
    Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23 := Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoSetNextIrpStackLocation$0$$Irp$1$23862.16$IoSetNextIrpStackLocation))))) := inline$IoSetNextIrpStackLocation$0$tempBoogie0];
    goto inline$IoSetNextIrpStackLocation$0$anon5#2;

  inline$IoSetNextIrpStackLocation$0$anon5#2:
    call contextSwitch();
    goto inline$IoSetNextIrpStackLocation$0$label_1#2;

  inline$IoSetNextIrpStackLocation$0$label_1#2:
    goto inline$IoSetNextIrpStackLocation$0$Return#2;

  inline$IoSetNextIrpStackLocation$0$Return#2:
    goto label_11$1#2;

  label_11$1#2:
    goto anon26_Then#2, anon26_Else#2;

  anon26_Else#2:
    assume !raiseException;
    goto anon8#2;

  anon8#2:
    goto label_14#2;

  label_14#2:
    goto inline$IoGetCurrentIrpStackLocation$0$Entry#2;

  inline$IoGetCurrentIrpStackLocation$0$Entry#2:
    inline$IoGetCurrentIrpStackLocation$0$$Irp$1$23298.14$IoGetCurrentIrpStackLocation_.1 := $irp$1$91.7$storm_main;
    goto inline$IoGetCurrentIrpStackLocation$0$start#2;

  inline$IoGetCurrentIrpStackLocation$0$start#2:
    inline$IoGetCurrentIrpStackLocation$0$$Irp$1$23298.14$IoGetCurrentIrpStackLocation := inline$IoGetCurrentIrpStackLocation$0$$Irp$1$23298.14$IoGetCurrentIrpStackLocation_.1;
    goto inline$IoGetCurrentIrpStackLocation$0$label_3#2;

  inline$IoGetCurrentIrpStackLocation$0$label_3#2:
    goto inline$IoGetCurrentIrpStackLocation$0$anon3_Then#2, inline$IoGetCurrentIrpStackLocation$0$anon3_Else#2;

  inline$IoGetCurrentIrpStackLocation$0$anon3_Else#2:
    assume k != 0;
    goto inline$IoGetCurrentIrpStackLocation$0$anon4_Then#2, inline$IoGetCurrentIrpStackLocation$0$anon4_Else#2;

  inline$IoGetCurrentIrpStackLocation$0$anon4_Else#2:
    assume k != 1;
    goto inline$IoGetCurrentIrpStackLocation$0$anon2#2;

  inline$IoGetCurrentIrpStackLocation$0$anon4_Then#2:
    assume k == 1;
    inline$IoGetCurrentIrpStackLocation$0$myVar_0 := Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoGetCurrentIrpStackLocation$0$$Irp$1$23298.14$IoGetCurrentIrpStackLocation)))))];
    goto inline$IoGetCurrentIrpStackLocation$0$anon2#2;

  inline$IoGetCurrentIrpStackLocation$0$anon3_Then#2:
    assume k == 0;
    inline$IoGetCurrentIrpStackLocation$0$myVar_0 := Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoGetCurrentIrpStackLocation$0$$Irp$1$23298.14$IoGetCurrentIrpStackLocation)))))];
    goto inline$IoGetCurrentIrpStackLocation$0$anon2#2;

  inline$IoGetCurrentIrpStackLocation$0$anon2#2:
    call contextSwitch();
    inline$IoGetCurrentIrpStackLocation$0$$result.IoGetCurrentIrpStackLocation$23297.0$1$ := inline$IoGetCurrentIrpStackLocation$0$myVar_0;
    goto inline$IoGetCurrentIrpStackLocation$0$label_1#2;

  inline$IoGetCurrentIrpStackLocation$0$label_1#2:
    goto inline$IoGetCurrentIrpStackLocation$0$Return#2;

  inline$IoGetCurrentIrpStackLocation$0$Return#2:
    $result.IoGetCurrentIrpStackLocation$99.38$2$ := inline$IoGetCurrentIrpStackLocation$0$$result.IoGetCurrentIrpStackLocation$23297.0$1$;
    goto label_14$1#2;

  label_14$1#2:
    goto anon27_Then#2, anon27_Else#2;

  anon27_Else#2:
    assume !raiseException;
    goto anon10#2;

  anon10#2:
    goto label_17#2;

  label_17#2:
    $irpSp$2$92.21$storm_main := $result.IoGetCurrentIrpStackLocation$99.38$2$;
    goto label_18#2;

  label_18#2:
    goto anon28_Then#2, anon28_Else#2;

  anon28_Else#2:
    assume k != 0;
    goto anon29_Then#2, anon29_Else#2;

  anon29_Else#2:
    assume k != 1;
    goto anon13#2;

  anon29_Then#2:
    assume k == 1;
    Mem_1_T.DeviceObject__IO_STACK_LOCATION := Mem_1_T.DeviceObject__IO_STACK_LOCATION[DeviceObject__IO_STACK_LOCATION($irpSp$2$92.21$storm_main) := hdevobj];
    goto anon13#2;

  anon28_Then#2:
    assume k == 0;
    Mem_0_T.DeviceObject__IO_STACK_LOCATION := Mem_0_T.DeviceObject__IO_STACK_LOCATION[DeviceObject__IO_STACK_LOCATION($irpSp$2$92.21$storm_main) := hdevobj];
    goto anon13#2;

  anon13#2:
    call contextSwitch();
    goto label_19#2;

  label_19#2:
    goto inline$myInitDriver$0$Entry#2;

  inline$myInitDriver$0$Entry#2:
    goto inline$myInitDriver$0$start#2;

  inline$myInitDriver$0$start#2:
    goto inline$myInitDriver$0$label_3#2;

  inline$myInitDriver$0$label_3#2:
    goto inline$myInitDriver$0$label_4#2;

  inline$myInitDriver$0$label_4#2:
    goto inline$myInitDriver$0$anon5_Then#2, inline$myInitDriver$0$anon5_Else#2;

  inline$myInitDriver$0$anon5_Else#2:
    assume k != 0;
    goto inline$myInitDriver$0$anon6_Then#2, inline$myInitDriver$0$anon6_Else#2;

  inline$myInitDriver$0$anon6_Else#2:
    assume k != 1;
    goto inline$myInitDriver$0$anon2#2;

  inline$myInitDriver$0$anon6_Then#2:
    assume k == 1;
    inline$myInitDriver$0$myVar_0 := Mem_1_T.DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(hdevobj)];
    goto inline$myInitDriver$0$anon2#2;

  inline$myInitDriver$0$anon5_Then#2:
    assume k == 0;
    inline$myInitDriver$0$myVar_0 := Mem_0_T.DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(hdevobj)];
    goto inline$myInitDriver$0$anon2#2;

  inline$myInitDriver$0$anon2#2:
    call contextSwitch();
    inline$myInitDriver$0$$kbExtension$2$5.27$myInitDriver := inline$myInitDriver$0$myVar_0;
    goto inline$myInitDriver$0$label_5#2;

  inline$myInitDriver$0$label_5#2:
    havoc inline$myInitDriver$0$myNondetVar_0;
    havoc inline$myInitDriver$0$myNondetVar_1;
    assume inline$myInitDriver$0$myNondetVar_0 == inline$myInitDriver$0$myNondetVar_1;
    goto inline$storm_KeInitializeSpinLock$0$Entry#2;

  inline$storm_KeInitializeSpinLock$0$Entry#2:
    inline$storm_KeInitializeSpinLock$0$$SpinLock$1$116.17$storm_KeInitializeSpinLock_.1 := SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(inline$myInitDriver$0$$kbExtension$2$5.27$myInitDriver);
    goto inline$storm_KeInitializeSpinLock$0$start#2;

  inline$storm_KeInitializeSpinLock$0$start#2:
    inline$storm_KeInitializeSpinLock$0$$SpinLock$1$116.17$storm_KeInitializeSpinLock := inline$storm_KeInitializeSpinLock$0$$SpinLock$1$116.17$storm_KeInitializeSpinLock_.1;
    goto inline$storm_KeInitializeSpinLock$0$label_3#2;

  inline$storm_KeInitializeSpinLock$0$label_3#2:
    goto inline$storm_KeInitializeSpinLock$0$anon3_Then#2, inline$storm_KeInitializeSpinLock$0$anon3_Else#2;

  inline$storm_KeInitializeSpinLock$0$anon3_Else#2:
    assume k != 0;
    goto inline$storm_KeInitializeSpinLock$0$anon4_Then#2, inline$storm_KeInitializeSpinLock$0$anon4_Else#2;

  inline$storm_KeInitializeSpinLock$0$anon4_Else#2:
    assume k != 1;
    goto inline$storm_KeInitializeSpinLock$0$anon2#2;

  inline$storm_KeInitializeSpinLock$0$anon4_Then#2:
    assume k == 1;
    Res_1_LOCK := Res_1_LOCK[inline$storm_KeInitializeSpinLock$0$$SpinLock$1$116.17$storm_KeInitializeSpinLock := 0];
    goto inline$storm_KeInitializeSpinLock$0$anon2#2;

  inline$storm_KeInitializeSpinLock$0$anon3_Then#2:
    assume k == 0;
    Res_0_LOCK := Res_0_LOCK[inline$storm_KeInitializeSpinLock$0$$SpinLock$1$116.17$storm_KeInitializeSpinLock := 0];
    goto inline$storm_KeInitializeSpinLock$0$anon2#2;

  inline$storm_KeInitializeSpinLock$0$anon2#2:
    call contextSwitch();
    goto inline$storm_KeInitializeSpinLock$0$label_1#2;

  inline$storm_KeInitializeSpinLock$0$label_1#2:
    goto inline$storm_KeInitializeSpinLock$0$Return#2;

  inline$storm_KeInitializeSpinLock$0$Return#2:
    goto inline$myInitDriver$0$label_5$1#2;

  inline$myInitDriver$0$label_5$1#2:
    goto inline$myInitDriver$0$anon7_Then#2, inline$myInitDriver$0$anon7_Else#2;

  inline$myInitDriver$0$anon7_Else#2:
    assume !raiseException;
    goto inline$myInitDriver$0$anon4#2;

  inline$myInitDriver$0$anon4#2:
    havoc inline$myInitDriver$0$myNondetVar_0;
    goto inline$myInitDriver$0$label_1#2;

  inline$myInitDriver$0$label_1#2:
    goto inline$myInitDriver$0$Return#2;

  inline$myInitDriver$0$anon7_Then#2:
    assume raiseException;
    goto inline$myInitDriver$0$Return#2;

  inline$myInitDriver$0$Return#2:
    goto label_19$1#2;

  label_19$1#2:
    goto anon30_Then#2, anon30_Else#2;

  anon30_Else#2:
    assume !raiseException;
    goto anon15#2;

  anon15#2:
    goto label_22#2;

  label_22#2:
    goto label_23#2;

  label_23#2:
    k_old_0 := k;
    tid_old_0 := tid;
    tidCount_old := tidCount;
    havoc tidCount;
    assume tidCount_old < tidCount;
    tid := tidCount;
    raiseException := false;
    call contextSwitch();
    goto inline$dispatch$0$Entry#2;

  inline$dispatch$0$Entry#2:
    inline$dispatch$0$$Irp$1$8.19$dispatch_.1 := $irp$1$91.7$storm_main;
    goto inline$dispatch$0$start#2;

  inline$dispatch$0$start#2:
    inline$dispatch$0$$Irp$1$8.19$dispatch := inline$dispatch$0$$Irp$1$8.19$dispatch_.1;
    goto inline$dispatch$0$label_3#2;

  inline$dispatch$0$label_3#2:
    goto inline$dispatch$0$label_4#2;

  inline$dispatch$0$label_4#2:
    goto inline$IoGetCurrentIrpStackLocation$1$Entry#2;

  inline$IoGetCurrentIrpStackLocation$1$Entry#2:
    goto inline$IoGetCurrentIrpStackLocation$1$start#2;

  inline$IoGetCurrentIrpStackLocation$1$start#2:
    goto inline$IoGetCurrentIrpStackLocation$1$label_3#2;

  inline$IoGetCurrentIrpStackLocation$1$label_3#2:
    goto inline$IoGetCurrentIrpStackLocation$1$anon3_Then#2, inline$IoGetCurrentIrpStackLocation$1$anon3_Else#2;

  inline$IoGetCurrentIrpStackLocation$1$anon3_Else#2:
    assume k != 0;
    goto inline$IoGetCurrentIrpStackLocation$1$anon4_Then#2, inline$IoGetCurrentIrpStackLocation$1$anon4_Else#2;

  inline$IoGetCurrentIrpStackLocation$1$anon4_Else#2:
    assume k != 1;
    goto inline$IoGetCurrentIrpStackLocation$1$anon2#2;

  inline$IoGetCurrentIrpStackLocation$1$anon4_Then#2:
    assume k == 1;
    goto inline$IoGetCurrentIrpStackLocation$1$anon2#2;

  inline$IoGetCurrentIrpStackLocation$1$anon3_Then#2:
    assume k == 0;
    goto inline$IoGetCurrentIrpStackLocation$1$anon2#2;

  inline$IoGetCurrentIrpStackLocation$1$anon2#2:
    call contextSwitch();
    goto inline$IoGetCurrentIrpStackLocation$1$label_1#2;

  inline$IoGetCurrentIrpStackLocation$1$label_1#2:
    goto inline$IoGetCurrentIrpStackLocation$1$Return#2;

  inline$IoGetCurrentIrpStackLocation$1$Return#2:
    goto inline$dispatch$0$label_4$1#2;

  inline$dispatch$0$label_4$1#2:
    goto inline$dispatch$0$anon4_Then#2, inline$dispatch$0$anon4_Else#2;

  inline$dispatch$0$anon4_Else#2:
    assume !raiseException;
    goto inline$dispatch$0$anon1#2;

  inline$dispatch$0$anon1#2:
    goto inline$dispatch$0$label_7#2;

  inline$dispatch$0$label_7#2:
    goto inline$dispatch$0$label_8#2;

  inline$dispatch$0$label_8#2:
    goto inline$I8xDeviceControl$0$Entry#2;

  inline$I8xDeviceControl$0$Entry#2:
    inline$I8xDeviceControl$0$$DeviceObject$1$464.22$I8xDeviceControl_.1 := hdevobj;
    inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl_.1 := inline$dispatch$0$$Irp$1$8.19$dispatch;
    goto inline$I8xDeviceControl$0$start#2;

  inline$I8xDeviceControl$0$start#2:
    inline$I8xDeviceControl$0$$DeviceObject$1$464.22$I8xDeviceControl := inline$I8xDeviceControl$0$$DeviceObject$1$464.22$I8xDeviceControl_.1;
    inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl := inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl_.1;
    goto inline$I8xDeviceControl$0$label_3#2;

  inline$I8xDeviceControl$0$label_3#2:
    goto inline$I8xDeviceControl$0$label_4#2;

  inline$I8xDeviceControl$0$label_4#2:
    goto inline$I8xDeviceControl$0$label_5#2;

  inline$I8xDeviceControl$0$label_5#2:
    goto inline$I8xDeviceControl$0$label_6#2;

  inline$I8xDeviceControl$0$label_6#2:
    goto inline$I8xDeviceControl$0$label_7#2;

  inline$I8xDeviceControl$0$label_7#2:
    call __PREfastPagedCode();
    goto inline$I8xDeviceControl$0$anon13_Then#2, inline$I8xDeviceControl$0$anon13_Else#2;

  inline$I8xDeviceControl$0$anon13_Else#2:
    assume !raiseException;
    goto inline$I8xDeviceControl$0$anon1#2;

  inline$I8xDeviceControl$0$anon1#2:
    goto inline$I8xDeviceControl$0$label_10#2;

  inline$I8xDeviceControl$0$label_10#2:
    goto inline$I8xDeviceControl$0$anon14_Then#2, inline$I8xDeviceControl$0$anon14_Else#2;

  inline$I8xDeviceControl$0$anon14_Else#2:
    assume k != 0;
    goto inline$I8xDeviceControl$0$anon15_Then#2, inline$I8xDeviceControl$0$anon15_Else#2;

  inline$I8xDeviceControl$0$anon15_Else#2:
    assume k != 1;
    goto inline$I8xDeviceControl$0$anon4#2;

  inline$I8xDeviceControl$0$anon15_Then#2:
    assume k == 1;
    inline$I8xDeviceControl$0$myVar_0 := Mem_1_T.DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(inline$I8xDeviceControl$0$$DeviceObject$1$464.22$I8xDeviceControl)];
    goto inline$I8xDeviceControl$0$anon4#2;

  inline$I8xDeviceControl$0$anon14_Then#2:
    assume k == 0;
    inline$I8xDeviceControl$0$myVar_0 := Mem_0_T.DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(inline$I8xDeviceControl$0$$DeviceObject$1$464.22$I8xDeviceControl)];
    goto inline$I8xDeviceControl$0$anon4#2;

  inline$I8xDeviceControl$0$anon4#2:
    call contextSwitch();
    inline$I8xDeviceControl$0$$kbExtension$3$468.32$I8xDeviceControl := inline$I8xDeviceControl$0$myVar_0;
    goto inline$I8xDeviceControl$0$label_11#2;

  inline$I8xDeviceControl$0$label_11#2:
    goto inline$I8xDeviceControl$0$label_11_true#2, inline$I8xDeviceControl$0$label_11_false#2;

  inline$I8xDeviceControl$0$label_11_false#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 == 0;
    goto inline$I8xDeviceControl$0$label_12#2;

  inline$I8xDeviceControl$0$label_11_true#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 != 0;
    goto inline$I8xDeviceControl$0$label_13#2;

  inline$I8xDeviceControl$0$label_13#2:
    goto inline$I8xDeviceControl$0$label_13_true#2, inline$I8xDeviceControl$0$label_13_false#2;

  inline$I8xDeviceControl$0$label_13_false#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 == 0;
    goto inline$I8xDeviceControl$0$label_12#2;

  inline$I8xDeviceControl$0$label_13_true#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 != 0;
    goto inline$I8xDeviceControl$0$label_14#2;

  inline$I8xDeviceControl$0$label_14#2:
    goto inline$I8xDeviceControl$0$label_14_true#2, inline$I8xDeviceControl$0$label_14_false#2;

  inline$I8xDeviceControl$0$label_14_false#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xDeviceControl$0$myNondetVar_0, 8) == 0;
    goto inline$I8xDeviceControl$0$label_15#2;

  inline$I8xDeviceControl$0$label_15#2:
    goto inline$IoGetCurrentIrpStackLocation$2$Entry#2;

  inline$IoGetCurrentIrpStackLocation$2$Entry#2:
    goto inline$IoGetCurrentIrpStackLocation$2$start#2;

  inline$IoGetCurrentIrpStackLocation$2$start#2:
    goto inline$IoGetCurrentIrpStackLocation$2$label_3#2;

  inline$IoGetCurrentIrpStackLocation$2$label_3#2:
    goto inline$IoGetCurrentIrpStackLocation$2$anon3_Then#2, inline$IoGetCurrentIrpStackLocation$2$anon3_Else#2;

  inline$IoGetCurrentIrpStackLocation$2$anon3_Else#2:
    assume k != 0;
    goto inline$IoGetCurrentIrpStackLocation$2$anon4_Then#2, inline$IoGetCurrentIrpStackLocation$2$anon4_Else#2;

  inline$IoGetCurrentIrpStackLocation$2$anon4_Else#2:
    assume k != 1;
    goto inline$IoGetCurrentIrpStackLocation$2$anon2#2;

  inline$IoGetCurrentIrpStackLocation$2$anon4_Then#2:
    assume k == 1;
    goto inline$IoGetCurrentIrpStackLocation$2$anon2#2;

  inline$IoGetCurrentIrpStackLocation$2$anon3_Then#2:
    assume k == 0;
    goto inline$IoGetCurrentIrpStackLocation$2$anon2#2;

  inline$IoGetCurrentIrpStackLocation$2$anon2#2:
    call contextSwitch();
    goto inline$IoGetCurrentIrpStackLocation$2$label_1#2;

  inline$IoGetCurrentIrpStackLocation$2$label_1#2:
    goto inline$IoGetCurrentIrpStackLocation$2$Return#2;

  inline$IoGetCurrentIrpStackLocation$2$Return#2:
    goto inline$I8xDeviceControl$0$label_15$1#2;

  inline$I8xDeviceControl$0$label_15$1#2:
    goto inline$I8xDeviceControl$0$anon16_Then#2, inline$I8xDeviceControl$0$anon16_Else#2;

  inline$I8xDeviceControl$0$anon16_Else#2:
    assume !raiseException;
    goto inline$I8xDeviceControl$0$anon6#2;

  inline$I8xDeviceControl$0$anon6#2:
    goto inline$I8xDeviceControl$0$label_18#2;

  inline$I8xDeviceControl$0$label_18#2:
    goto inline$I8xDeviceControl$0$label_19#2;

  inline$I8xDeviceControl$0$label_19#2:
    goto inline$I8xDeviceControl$0$label_19_case_0#2, inline$I8xDeviceControl$0$label_19_case_1#2, inline$I8xDeviceControl$0$label_19_case_2#2;

  inline$I8xDeviceControl$0$label_19_case_2#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 == 2703684;
    goto inline$I8xDeviceControl$0$label_24#2;

  inline$I8xDeviceControl$0$label_24#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$Entry#2;

  inline$I8xKeyboardGetSysButtonEvent$0$Entry#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$KeyboardExtension$1$148.29$I8xKeyboardGetSysButtonEvent_.1 := inline$I8xDeviceControl$0$$kbExtension$3$468.32$I8xDeviceControl;
    inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent_.1 := inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl;
    goto inline$I8xKeyboardGetSysButtonEvent$0$start#2;

  inline$I8xKeyboardGetSysButtonEvent$0$start#2:
    call inline$I8xKeyboardGetSysButtonEvent$0$$irql$8$156.24$I8xKeyboardGetSysButtonEvent := __HAVOC_malloc(1);
    inline$I8xKeyboardGetSysButtonEvent$0$$KeyboardExtension$1$148.29$I8xKeyboardGetSysButtonEvent := inline$I8xKeyboardGetSysButtonEvent$0$$KeyboardExtension$1$148.29$I8xKeyboardGetSysButtonEvent_.1;
    inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent_.1;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_3#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_3#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_4#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_4#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_5#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_5#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_6#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_6#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_7#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_7#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_8#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_8#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_9#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_9#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_10#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_10#2:
    goto inline$IoGetCurrentIrpStackLocation$4$Entry#2;

  inline$IoGetCurrentIrpStackLocation$4$Entry#2:
    goto inline$IoGetCurrentIrpStackLocation$4$start#2;

  inline$IoGetCurrentIrpStackLocation$4$start#2:
    goto inline$IoGetCurrentIrpStackLocation$4$label_3#2;

  inline$IoGetCurrentIrpStackLocation$4$label_3#2:
    goto inline$IoGetCurrentIrpStackLocation$4$anon3_Then#2, inline$IoGetCurrentIrpStackLocation$4$anon3_Else#2;

  inline$IoGetCurrentIrpStackLocation$4$anon3_Else#2:
    assume k != 0;
    goto inline$IoGetCurrentIrpStackLocation$4$anon4_Then#2, inline$IoGetCurrentIrpStackLocation$4$anon4_Else#2;

  inline$IoGetCurrentIrpStackLocation$4$anon4_Else#2:
    assume k != 1;
    goto inline$IoGetCurrentIrpStackLocation$4$anon2#2;

  inline$IoGetCurrentIrpStackLocation$4$anon4_Then#2:
    assume k == 1;
    goto inline$IoGetCurrentIrpStackLocation$4$anon2#2;

  inline$IoGetCurrentIrpStackLocation$4$anon3_Then#2:
    assume k == 0;
    goto inline$IoGetCurrentIrpStackLocation$4$anon2#2;

  inline$IoGetCurrentIrpStackLocation$4$anon2#2:
    call contextSwitch();
    goto inline$IoGetCurrentIrpStackLocation$4$label_1#2;

  inline$IoGetCurrentIrpStackLocation$4$label_1#2:
    goto inline$IoGetCurrentIrpStackLocation$4$Return#2;

  inline$IoGetCurrentIrpStackLocation$4$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_10$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_10$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon34_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon34_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon34_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_13#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_13#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_14#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_14#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_14_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_14_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_14_false#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume !INT_ULT(inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0, 4);
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_15#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_15#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_15_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_15_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_15_false#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 == 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_23#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_23#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_1;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 == inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_1;
    goto inline$storm_KeAcquireSpinLock$0$Entry#2;

  inline$storm_KeAcquireSpinLock$0$Entry#2:
    inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock_.1 := SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(inline$I8xKeyboardGetSysButtonEvent$0$$KeyboardExtension$1$148.29$I8xKeyboardGetSysButtonEvent);
    goto inline$storm_KeAcquireSpinLock$0$start#2;

  inline$storm_KeAcquireSpinLock$0$start#2:
    inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock_.1;
    goto inline$storm_KeAcquireSpinLock$0$label_3#2;

  inline$storm_KeAcquireSpinLock$0$label_3#2:
    goto inline$storm_KeAcquireSpinLock$0$label_4#2;

  inline$storm_KeAcquireSpinLock$0$label_4#2:
    goto inline$storm_getThreadID$0$Entry#2;

  inline$storm_getThreadID$0$Entry#2:
    goto inline$storm_getThreadID$0$anon0#2;

  inline$storm_getThreadID$0$anon0#2:
    inline$storm_getThreadID$0$tidRet := tid;
    goto inline$storm_getThreadID$0$Return#2;

  inline$storm_getThreadID$0$Return#2:
    inline$storm_KeAcquireSpinLock$0$$result.storm_getThreadID$128.29$1$ := inline$storm_getThreadID$0$tidRet;
    goto inline$storm_KeAcquireSpinLock$0$label_4$1#2;

  inline$storm_KeAcquireSpinLock$0$label_4$1#2:
    goto inline$storm_KeAcquireSpinLock$0$label_7#2;

  inline$storm_KeAcquireSpinLock$0$label_7#2:
    inline$storm_KeAcquireSpinLock$0$$tid$3$128.6$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$0$$result.storm_getThreadID$128.29$1$;
    goto inline$storm_KeAcquireSpinLock$0$label_8#2;

  inline$storm_KeAcquireSpinLock$0$label_8#2:
    goto inline$storm_KeAcquireSpinLock$0$label_9#2;

  inline$storm_KeAcquireSpinLock$0$label_9#2:
    __storm_atomic := true;
    goto inline$storm_KeAcquireSpinLock$0$label_12#2;

  inline$storm_KeAcquireSpinLock$0$label_12#2:
    havoc raiseException;
    goto inline$storm_KeAcquireSpinLock$0$anon10_Then#2, inline$storm_KeAcquireSpinLock$0$anon10_Else#2;

  inline$storm_KeAcquireSpinLock$0$anon10_Else#2:
    assume !raiseException;
    goto inline$storm_KeAcquireSpinLock$0$anon1#2;

  inline$storm_KeAcquireSpinLock$0$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_LOCK[inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock], inline$storm_KeAcquireSpinLock$0$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    assume k == 1 ==> INT_EQ(Res_1_LOCK[inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock], inline$storm_KeAcquireSpinLock$0$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    call contextSwitch();
    goto inline$storm_KeAcquireSpinLock$0$label_13#2;

  inline$storm_KeAcquireSpinLock$0$label_13#2:
    goto inline$storm_KeAcquireSpinLock$0$label_13_true#2, inline$storm_KeAcquireSpinLock$0$label_13_false#2;

  inline$storm_KeAcquireSpinLock$0$label_13_false#2:
    assume !INT_NEQ(inline$storm_KeAcquireSpinLock$0$$tid$3$128.6$storm_KeAcquireSpinLock, inline$storm_KeAcquireSpinLock$0$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    goto inline$storm_KeAcquireSpinLock$0$label_14#2;

  inline$storm_KeAcquireSpinLock$0$label_14#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_KeAcquireSpinLock$0$label_1#2;

  inline$storm_KeAcquireSpinLock$0$label_13_true#2:
    assume INT_NEQ(inline$storm_KeAcquireSpinLock$0$$tid$3$128.6$storm_KeAcquireSpinLock, inline$storm_KeAcquireSpinLock$0$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    goto inline$storm_KeAcquireSpinLock$0$label_17#2;

  inline$storm_KeAcquireSpinLock$0$label_17#2:
    havoc raiseException;
    goto inline$storm_KeAcquireSpinLock$0$anon11_Then#2, inline$storm_KeAcquireSpinLock$0$anon11_Else#2;

  inline$storm_KeAcquireSpinLock$0$anon11_Else#2:
    assume !raiseException;
    goto inline$storm_KeAcquireSpinLock$0$anon4#2;

  inline$storm_KeAcquireSpinLock$0$anon4#2:
    assume INT_EQ(inline$storm_KeAcquireSpinLock$0$$lockStatus$4$129.6$storm_KeAcquireSpinLock, 0);
    goto inline$storm_KeAcquireSpinLock$0$label_18#2;

  inline$storm_KeAcquireSpinLock$0$label_18#2:
    goto inline$storm_KeAcquireSpinLock$0$anon12_Then#2, inline$storm_KeAcquireSpinLock$0$anon12_Else#2;

  inline$storm_KeAcquireSpinLock$0$anon12_Else#2:
    assume k != 0;
    goto inline$storm_KeAcquireSpinLock$0$anon13_Then#2, inline$storm_KeAcquireSpinLock$0$anon13_Else#2;

  inline$storm_KeAcquireSpinLock$0$anon13_Else#2:
    assume k != 1;
    goto inline$storm_KeAcquireSpinLock$0$anon7#2;

  inline$storm_KeAcquireSpinLock$0$anon13_Then#2:
    assume k == 1;
    Res_1_LOCK := Res_1_LOCK[inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$0$$tid$3$128.6$storm_KeAcquireSpinLock];
    goto inline$storm_KeAcquireSpinLock$0$anon7#2;

  inline$storm_KeAcquireSpinLock$0$anon12_Then#2:
    assume k == 0;
    Res_0_LOCK := Res_0_LOCK[inline$storm_KeAcquireSpinLock$0$$SpinLock$1$124.17$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$0$$tid$3$128.6$storm_KeAcquireSpinLock];
    goto inline$storm_KeAcquireSpinLock$0$anon7#2;

  inline$storm_KeAcquireSpinLock$0$anon7#2:
    call contextSwitch();
    goto inline$storm_KeAcquireSpinLock$0$label_19#2;

  inline$storm_KeAcquireSpinLock$0$label_19#2:
    goto inline$storm_KeAcquireSpinLock$0$anon14_Then#2, inline$storm_KeAcquireSpinLock$0$anon14_Else#2;

  inline$storm_KeAcquireSpinLock$0$anon14_Else#2:
    assume __storm_init;
    goto inline$storm_KeAcquireSpinLock$0$anon9#2;

  inline$storm_KeAcquireSpinLock$0$anon14_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_KeAcquireSpinLock$0$anon9#2;

  inline$storm_KeAcquireSpinLock$0$anon9#2:
    call contextSwitch();
    goto inline$storm_KeAcquireSpinLock$0$label_1#2;

  inline$storm_KeAcquireSpinLock$0$label_1#2:
    goto inline$storm_KeAcquireSpinLock$0$Return#2;

  inline$storm_KeAcquireSpinLock$0$anon11_Then#2:
    assume raiseException;
    goto inline$storm_KeAcquireSpinLock$0$Return#2;

  inline$storm_KeAcquireSpinLock$0$anon10_Then#2:
    assume raiseException;
    goto inline$storm_KeAcquireSpinLock$0$Return#2;

  inline$storm_KeAcquireSpinLock$0$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_23$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_23$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon36_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon36_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon36_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon5#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon5#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_56#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_56#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_56_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_56_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_56_false#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 == 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_57#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_57#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_62#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_62#2:
    goto inline$storm_IoSetCancelRoutine$0$Entry#2;

  inline$storm_IoSetCancelRoutine$0$Entry#2:
    inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine_.1 := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent;
    inline$storm_IoSetCancelRoutine$0$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine_.1 := I8xSysButtonCancelRoutine;
    goto inline$storm_IoSetCancelRoutine$0$start#2;

  inline$storm_IoSetCancelRoutine$0$start#2:
    inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine := inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine_.1;
    inline$storm_IoSetCancelRoutine$0$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine := inline$storm_IoSetCancelRoutine$0$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine_.1;
    goto inline$storm_IoSetCancelRoutine$0$label_3#2;

  inline$storm_IoSetCancelRoutine$0$label_3#2:
    goto inline$storm_IoSetCancelRoutine$0$label_4#2;

  inline$storm_IoSetCancelRoutine$0$label_4#2:
    call inline$storm_IoSetCancelRoutine$0$$result.storm_nondet$391.2$2$ := storm_nondet();
    goto inline$storm_IoSetCancelRoutine$0$label_7#2;

  inline$storm_IoSetCancelRoutine$0$label_7#2:
    goto inline$storm_IoSetCancelRoutine$0$label_7_true#2, inline$storm_IoSetCancelRoutine$0$label_7_false#2;

  inline$storm_IoSetCancelRoutine$0$label_7_false#2:
    assume inline$storm_IoSetCancelRoutine$0$$result.storm_nondet$391.2$2$ == 0;
    goto inline$storm_IoSetCancelRoutine$0$label_8#2;

  inline$storm_IoSetCancelRoutine$0$label_7_true#2:
    assume inline$storm_IoSetCancelRoutine$0$$result.storm_nondet$391.2$2$ != 0;
    goto inline$storm_IoSetCancelRoutine$0$label_11#2;

  inline$storm_IoSetCancelRoutine$0$label_11#2:
    havoc raiseException;
    goto inline$storm_IoSetCancelRoutine$0$anon11_Then#2, inline$storm_IoSetCancelRoutine$0$anon11_Else#2;

  inline$storm_IoSetCancelRoutine$0$anon11_Else#2:
    assume !raiseException;
    goto inline$storm_IoSetCancelRoutine$0$anon1#2;

  inline$storm_IoSetCancelRoutine$0$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine], 1);
    call contextSwitch();
    goto inline$storm_IoSetCancelRoutine$0$label_12#2;

  inline$storm_IoSetCancelRoutine$0$label_12#2:
    goto inline$storm_IoSetCancelRoutine$0$label_12_true#2, inline$storm_IoSetCancelRoutine$0$label_12_false#2;

  inline$storm_IoSetCancelRoutine$0$label_12_false#2:
    assume 0 == 0;
    goto inline$storm_IoSetCancelRoutine$0$label_13#2;

  inline$storm_IoSetCancelRoutine$0$label_13#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoSetCancelRoutine$0$label_1#2;

  inline$storm_IoSetCancelRoutine$0$label_12_true#2:
    assume 0 != 0;
    goto inline$storm_IoSetCancelRoutine$0$label_8#2;

  inline$storm_IoSetCancelRoutine$0$label_8#2:
    __storm_atomic := true;
    goto inline$storm_IoSetCancelRoutine$0$label_16#2;

  inline$storm_IoSetCancelRoutine$0$label_16#2:
    goto inline$storm_IoSetCancelRoutine$0$anon12_Then#2, inline$storm_IoSetCancelRoutine$0$anon12_Else#2;

  inline$storm_IoSetCancelRoutine$0$anon12_Else#2:
    assume k != 0;
    goto inline$storm_IoSetCancelRoutine$0$anon13_Then#2, inline$storm_IoSetCancelRoutine$0$anon13_Else#2;

  inline$storm_IoSetCancelRoutine$0$anon13_Else#2:
    assume k != 1;
    goto inline$storm_IoSetCancelRoutine$0$anon5#2;

  inline$storm_IoSetCancelRoutine$0$anon13_Then#2:
    assume k == 1;
    goto inline$storm_IoSetCancelRoutine$0$anon5#2;

  inline$storm_IoSetCancelRoutine$0$anon12_Then#2:
    assume k == 0;
    goto inline$storm_IoSetCancelRoutine$0$anon5#2;

  inline$storm_IoSetCancelRoutine$0$anon5#2:
    call contextSwitch();
    goto inline$storm_IoSetCancelRoutine$0$label_17#2;

  inline$storm_IoSetCancelRoutine$0$label_17#2:
    goto inline$storm_IoSetCancelRoutine$0$anon14_Then#2, inline$storm_IoSetCancelRoutine$0$anon14_Else#2;

  inline$storm_IoSetCancelRoutine$0$anon14_Else#2:
    assume k != 0;
    goto inline$storm_IoSetCancelRoutine$0$anon15_Then#2, inline$storm_IoSetCancelRoutine$0$anon15_Else#2;

  inline$storm_IoSetCancelRoutine$0$anon15_Else#2:
    assume k != 1;
    goto inline$storm_IoSetCancelRoutine$0$anon8#2;

  inline$storm_IoSetCancelRoutine$0$anon15_Then#2:
    assume k == 1;
    Mem_1_T.CancelRoutine__IRP := Mem_1_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine) := inline$storm_IoSetCancelRoutine$0$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine];
    goto inline$storm_IoSetCancelRoutine$0$anon8#2;

  inline$storm_IoSetCancelRoutine$0$anon14_Then#2:
    assume k == 0;
    Mem_0_T.CancelRoutine__IRP := Mem_0_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoSetCancelRoutine$0$$pirp$1$386.10$storm_IoSetCancelRoutine) := inline$storm_IoSetCancelRoutine$0$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine];
    goto inline$storm_IoSetCancelRoutine$0$anon8#2;

  inline$storm_IoSetCancelRoutine$0$anon8#2:
    call contextSwitch();
    goto inline$storm_IoSetCancelRoutine$0$label_18#2;

  inline$storm_IoSetCancelRoutine$0$label_18#2:
    goto inline$storm_IoSetCancelRoutine$0$anon16_Then#2, inline$storm_IoSetCancelRoutine$0$anon16_Else#2;

  inline$storm_IoSetCancelRoutine$0$anon16_Else#2:
    assume __storm_init;
    goto inline$storm_IoSetCancelRoutine$0$anon10#2;

  inline$storm_IoSetCancelRoutine$0$anon16_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_IoSetCancelRoutine$0$anon10#2;

  inline$storm_IoSetCancelRoutine$0$anon10#2:
    call contextSwitch();
    goto inline$storm_IoSetCancelRoutine$0$label_21#2;

  inline$storm_IoSetCancelRoutine$0$label_21#2:
    goto inline$storm_IoSetCancelRoutine$0$label_1#2;

  inline$storm_IoSetCancelRoutine$0$label_1#2:
    goto inline$storm_IoSetCancelRoutine$0$Return#2;

  inline$storm_IoSetCancelRoutine$0$anon11_Then#2:
    assume raiseException;
    goto inline$storm_IoSetCancelRoutine$0$Return#2;

  inline$storm_IoSetCancelRoutine$0$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_62$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_62$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon44_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon44_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon44_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon21#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon21#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_65#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_65#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_65_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_65_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_65_false#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon47_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon47_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon47_Else#2:
    assume k != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon48_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon48_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon48_Else#2:
    assume k != 1;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon27#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon48_Then#2:
    assume k == 1;
    inline$I8xKeyboardGetSysButtonEvent$0$myVar_0 := Mem_1_T.Cancel__IRP[Cancel__IRP(inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent)];
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon27#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon47_Then#2:
    assume k == 0;
    inline$I8xKeyboardGetSysButtonEvent$0$myVar_0 := Mem_0_T.Cancel__IRP[Cancel__IRP(inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent)];
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon27#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon27#2:
    call contextSwitch();
    assume inline$I8xKeyboardGetSysButtonEvent$0$myVar_0 == 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_66#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_66#2:
    goto inline$storm_IoMarkIrpPending$1$Entry#2;

  inline$storm_IoMarkIrpPending$1$Entry#2:
    inline$storm_IoMarkIrpPending$1$$pirp$1$376.14$storm_IoMarkIrpPending_.1 := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent;
    goto inline$storm_IoMarkIrpPending$1$start#2;

  inline$storm_IoMarkIrpPending$1$start#2:
    inline$storm_IoMarkIrpPending$1$$pirp$1$376.14$storm_IoMarkIrpPending := inline$storm_IoMarkIrpPending$1$$pirp$1$376.14$storm_IoMarkIrpPending_.1;
    goto inline$storm_IoMarkIrpPending$1$label_3#2;

  inline$storm_IoMarkIrpPending$1$label_3#2:
    call inline$storm_IoMarkIrpPending$1$$result.storm_nondet$379.2$1$ := storm_nondet();
    goto inline$storm_IoMarkIrpPending$1$label_6#2;

  inline$storm_IoMarkIrpPending$1$label_6#2:
    goto inline$storm_IoMarkIrpPending$1$label_6_true#2, inline$storm_IoMarkIrpPending$1$label_6_false#2;

  inline$storm_IoMarkIrpPending$1$label_6_false#2:
    assume inline$storm_IoMarkIrpPending$1$$result.storm_nondet$379.2$1$ == 0;
    goto inline$storm_IoMarkIrpPending$1$label_1#2;

  inline$storm_IoMarkIrpPending$1$label_6_true#2:
    assume inline$storm_IoMarkIrpPending$1$$result.storm_nondet$379.2$1$ != 0;
    goto inline$storm_IoMarkIrpPending$1$label_7#2;

  inline$storm_IoMarkIrpPending$1$label_7#2:
    havoc raiseException;
    goto inline$storm_IoMarkIrpPending$1$anon3_Then#2, inline$storm_IoMarkIrpPending$1$anon3_Else#2;

  inline$storm_IoMarkIrpPending$1$anon3_Else#2:
    assume !raiseException;
    goto inline$storm_IoMarkIrpPending$1$anon1#2;

  inline$storm_IoMarkIrpPending$1$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoMarkIrpPending$1$$pirp$1$376.14$storm_IoMarkIrpPending], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoMarkIrpPending$1$$pirp$1$376.14$storm_IoMarkIrpPending], 1);
    call contextSwitch();
    goto inline$storm_IoMarkIrpPending$1$label_8#2;

  inline$storm_IoMarkIrpPending$1$label_8#2:
    goto inline$storm_IoMarkIrpPending$1$label_8_true#2, inline$storm_IoMarkIrpPending$1$label_8_false#2;

  inline$storm_IoMarkIrpPending$1$label_8_false#2:
    assume 0 == 0;
    goto inline$storm_IoMarkIrpPending$1$label_9#2;

  inline$storm_IoMarkIrpPending$1$label_9#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoMarkIrpPending$1$label_1#2;

  inline$storm_IoMarkIrpPending$1$label_8_true#2:
    assume 0 != 0;
    goto inline$storm_IoMarkIrpPending$1$label_1#2;

  inline$storm_IoMarkIrpPending$1$label_1#2:
    goto inline$storm_IoMarkIrpPending$1$Return#2;

  inline$storm_IoMarkIrpPending$1$anon3_Then#2:
    assume raiseException;
    goto inline$storm_IoMarkIrpPending$1$Return#2;

  inline$storm_IoMarkIrpPending$1$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_66$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_66$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon49_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon49_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon49_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon29#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon29#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_82#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_82#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent := 259;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_59#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon49_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_65_true#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon45_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon45_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon45_Else#2:
    assume k != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon46_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon46_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon46_Else#2:
    assume k != 1;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon24#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon46_Then#2:
    assume k == 1;
    inline$I8xKeyboardGetSysButtonEvent$0$myVar_0 := Mem_1_T.Cancel__IRP[Cancel__IRP(inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent)];
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon24#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon45_Then#2:
    assume k == 0;
    inline$I8xKeyboardGetSysButtonEvent$0$myVar_0 := Mem_0_T.Cancel__IRP[Cancel__IRP(inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent)];
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon24#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon24#2:
    call contextSwitch();
    assume inline$I8xKeyboardGetSysButtonEvent$0$myVar_0 != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_69#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_69#2:
    goto inline$storm_IoSetCancelRoutine$1$Entry#2;

  inline$storm_IoSetCancelRoutine$1$Entry#2:
    inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine_.1 := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent;
    inline$storm_IoSetCancelRoutine$1$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine_.1 := 0;
    goto inline$storm_IoSetCancelRoutine$1$start#2;

  inline$storm_IoSetCancelRoutine$1$start#2:
    inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine := inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine_.1;
    inline$storm_IoSetCancelRoutine$1$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine := inline$storm_IoSetCancelRoutine$1$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine_.1;
    goto inline$storm_IoSetCancelRoutine$1$label_3#2;

  inline$storm_IoSetCancelRoutine$1$label_3#2:
    goto inline$storm_IoSetCancelRoutine$1$label_4#2;

  inline$storm_IoSetCancelRoutine$1$label_4#2:
    call inline$storm_IoSetCancelRoutine$1$$result.storm_nondet$391.2$2$ := storm_nondet();
    goto inline$storm_IoSetCancelRoutine$1$label_7#2;

  inline$storm_IoSetCancelRoutine$1$label_7#2:
    goto inline$storm_IoSetCancelRoutine$1$label_7_true#2, inline$storm_IoSetCancelRoutine$1$label_7_false#2;

  inline$storm_IoSetCancelRoutine$1$label_7_false#2:
    assume inline$storm_IoSetCancelRoutine$1$$result.storm_nondet$391.2$2$ == 0;
    goto inline$storm_IoSetCancelRoutine$1$label_8#2;

  inline$storm_IoSetCancelRoutine$1$label_7_true#2:
    assume inline$storm_IoSetCancelRoutine$1$$result.storm_nondet$391.2$2$ != 0;
    goto inline$storm_IoSetCancelRoutine$1$label_11#2;

  inline$storm_IoSetCancelRoutine$1$label_11#2:
    havoc raiseException;
    goto inline$storm_IoSetCancelRoutine$1$anon11_Then#2, inline$storm_IoSetCancelRoutine$1$anon11_Else#2;

  inline$storm_IoSetCancelRoutine$1$anon11_Else#2:
    assume !raiseException;
    goto inline$storm_IoSetCancelRoutine$1$anon1#2;

  inline$storm_IoSetCancelRoutine$1$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine], 1);
    call contextSwitch();
    goto inline$storm_IoSetCancelRoutine$1$label_12#2;

  inline$storm_IoSetCancelRoutine$1$label_12#2:
    goto inline$storm_IoSetCancelRoutine$1$label_12_true#2, inline$storm_IoSetCancelRoutine$1$label_12_false#2;

  inline$storm_IoSetCancelRoutine$1$label_12_false#2:
    assume 0 == 0;
    goto inline$storm_IoSetCancelRoutine$1$label_13#2;

  inline$storm_IoSetCancelRoutine$1$label_13#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoSetCancelRoutine$1$label_1#2;

  inline$storm_IoSetCancelRoutine$1$label_12_true#2:
    assume 0 != 0;
    goto inline$storm_IoSetCancelRoutine$1$label_8#2;

  inline$storm_IoSetCancelRoutine$1$label_8#2:
    __storm_atomic := true;
    goto inline$storm_IoSetCancelRoutine$1$label_16#2;

  inline$storm_IoSetCancelRoutine$1$label_16#2:
    goto inline$storm_IoSetCancelRoutine$1$anon12_Then#2, inline$storm_IoSetCancelRoutine$1$anon12_Else#2;

  inline$storm_IoSetCancelRoutine$1$anon12_Else#2:
    assume k != 0;
    goto inline$storm_IoSetCancelRoutine$1$anon13_Then#2, inline$storm_IoSetCancelRoutine$1$anon13_Else#2;

  inline$storm_IoSetCancelRoutine$1$anon13_Else#2:
    assume k != 1;
    goto inline$storm_IoSetCancelRoutine$1$anon5#2;

  inline$storm_IoSetCancelRoutine$1$anon13_Then#2:
    assume k == 1;
    inline$storm_IoSetCancelRoutine$1$myVar_0 := Mem_1_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine)];
    goto inline$storm_IoSetCancelRoutine$1$anon5#2;

  inline$storm_IoSetCancelRoutine$1$anon12_Then#2:
    assume k == 0;
    inline$storm_IoSetCancelRoutine$1$myVar_0 := Mem_0_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine)];
    goto inline$storm_IoSetCancelRoutine$1$anon5#2;

  inline$storm_IoSetCancelRoutine$1$anon5#2:
    call contextSwitch();
    inline$storm_IoSetCancelRoutine$1$$oldCancelRoutine$3$390.17$storm_IoSetCancelRoutine := inline$storm_IoSetCancelRoutine$1$myVar_0;
    goto inline$storm_IoSetCancelRoutine$1$label_17#2;

  inline$storm_IoSetCancelRoutine$1$label_17#2:
    goto inline$storm_IoSetCancelRoutine$1$anon14_Then#2, inline$storm_IoSetCancelRoutine$1$anon14_Else#2;

  inline$storm_IoSetCancelRoutine$1$anon14_Else#2:
    assume k != 0;
    goto inline$storm_IoSetCancelRoutine$1$anon15_Then#2, inline$storm_IoSetCancelRoutine$1$anon15_Else#2;

  inline$storm_IoSetCancelRoutine$1$anon15_Else#2:
    assume k != 1;
    goto inline$storm_IoSetCancelRoutine$1$anon8#2;

  inline$storm_IoSetCancelRoutine$1$anon15_Then#2:
    assume k == 1;
    Mem_1_T.CancelRoutine__IRP := Mem_1_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine) := inline$storm_IoSetCancelRoutine$1$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine];
    goto inline$storm_IoSetCancelRoutine$1$anon8#2;

  inline$storm_IoSetCancelRoutine$1$anon14_Then#2:
    assume k == 0;
    Mem_0_T.CancelRoutine__IRP := Mem_0_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoSetCancelRoutine$1$$pirp$1$386.10$storm_IoSetCancelRoutine) := inline$storm_IoSetCancelRoutine$1$$CancelRoutine$2$387.20$storm_IoSetCancelRoutine];
    goto inline$storm_IoSetCancelRoutine$1$anon8#2;

  inline$storm_IoSetCancelRoutine$1$anon8#2:
    call contextSwitch();
    goto inline$storm_IoSetCancelRoutine$1$label_18#2;

  inline$storm_IoSetCancelRoutine$1$label_18#2:
    goto inline$storm_IoSetCancelRoutine$1$anon16_Then#2, inline$storm_IoSetCancelRoutine$1$anon16_Else#2;

  inline$storm_IoSetCancelRoutine$1$anon16_Else#2:
    assume __storm_init;
    goto inline$storm_IoSetCancelRoutine$1$anon10#2;

  inline$storm_IoSetCancelRoutine$1$anon16_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_IoSetCancelRoutine$1$anon10#2;

  inline$storm_IoSetCancelRoutine$1$anon10#2:
    call contextSwitch();
    goto inline$storm_IoSetCancelRoutine$1$label_21#2;

  inline$storm_IoSetCancelRoutine$1$label_21#2:
    inline$storm_IoSetCancelRoutine$1$$result.storm_IoSetCancelRoutine$385.0$1$ := inline$storm_IoSetCancelRoutine$1$$oldCancelRoutine$3$390.17$storm_IoSetCancelRoutine;
    goto inline$storm_IoSetCancelRoutine$1$label_1#2;

  inline$storm_IoSetCancelRoutine$1$label_1#2:
    goto inline$storm_IoSetCancelRoutine$1$Return#2;

  inline$storm_IoSetCancelRoutine$1$anon11_Then#2:
    assume raiseException;
    goto inline$storm_IoSetCancelRoutine$1$Return#2;

  inline$storm_IoSetCancelRoutine$1$Return#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_IoSetCancelRoutine$237.37$6$ := inline$storm_IoSetCancelRoutine$1$$result.storm_IoSetCancelRoutine$385.0$1$;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_69$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_69$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon50_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon50_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon50_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon31#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon31#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_72#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_72#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_72_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_72_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_72_false#2:
    assume inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_IoSetCancelRoutine$237.37$6$ == 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_73#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_73#2:
    goto inline$storm_IoMarkIrpPending$2$Entry#2;

  inline$storm_IoMarkIrpPending$2$Entry#2:
    inline$storm_IoMarkIrpPending$2$$pirp$1$376.14$storm_IoMarkIrpPending_.1 := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent;
    goto inline$storm_IoMarkIrpPending$2$start#2;

  inline$storm_IoMarkIrpPending$2$start#2:
    inline$storm_IoMarkIrpPending$2$$pirp$1$376.14$storm_IoMarkIrpPending := inline$storm_IoMarkIrpPending$2$$pirp$1$376.14$storm_IoMarkIrpPending_.1;
    goto inline$storm_IoMarkIrpPending$2$label_3#2;

  inline$storm_IoMarkIrpPending$2$label_3#2:
    call inline$storm_IoMarkIrpPending$2$$result.storm_nondet$379.2$1$ := storm_nondet();
    goto inline$storm_IoMarkIrpPending$2$label_6#2;

  inline$storm_IoMarkIrpPending$2$label_6#2:
    goto inline$storm_IoMarkIrpPending$2$label_6_true#2, inline$storm_IoMarkIrpPending$2$label_6_false#2;

  inline$storm_IoMarkIrpPending$2$label_6_false#2:
    assume inline$storm_IoMarkIrpPending$2$$result.storm_nondet$379.2$1$ == 0;
    goto inline$storm_IoMarkIrpPending$2$label_1#2;

  inline$storm_IoMarkIrpPending$2$label_6_true#2:
    assume inline$storm_IoMarkIrpPending$2$$result.storm_nondet$379.2$1$ != 0;
    goto inline$storm_IoMarkIrpPending$2$label_7#2;

  inline$storm_IoMarkIrpPending$2$label_7#2:
    havoc raiseException;
    goto inline$storm_IoMarkIrpPending$2$anon3_Then#2, inline$storm_IoMarkIrpPending$2$anon3_Else#2;

  inline$storm_IoMarkIrpPending$2$anon3_Else#2:
    assume !raiseException;
    goto inline$storm_IoMarkIrpPending$2$anon1#2;

  inline$storm_IoMarkIrpPending$2$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoMarkIrpPending$2$$pirp$1$376.14$storm_IoMarkIrpPending], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoMarkIrpPending$2$$pirp$1$376.14$storm_IoMarkIrpPending], 1);
    call contextSwitch();
    goto inline$storm_IoMarkIrpPending$2$label_8#2;

  inline$storm_IoMarkIrpPending$2$label_8#2:
    goto inline$storm_IoMarkIrpPending$2$label_8_true#2, inline$storm_IoMarkIrpPending$2$label_8_false#2;

  inline$storm_IoMarkIrpPending$2$label_8_false#2:
    assume 0 == 0;
    goto inline$storm_IoMarkIrpPending$2$label_9#2;

  inline$storm_IoMarkIrpPending$2$label_9#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoMarkIrpPending$2$label_1#2;

  inline$storm_IoMarkIrpPending$2$label_8_true#2:
    assume 0 != 0;
    goto inline$storm_IoMarkIrpPending$2$label_1#2;

  inline$storm_IoMarkIrpPending$2$label_1#2:
    goto inline$storm_IoMarkIrpPending$2$Return#2;

  inline$storm_IoMarkIrpPending$2$anon3_Then#2:
    assume raiseException;
    goto inline$storm_IoMarkIrpPending$2$Return#2;

  inline$storm_IoMarkIrpPending$2$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_73$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_73$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon51_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon51_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon51_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon33#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon33#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_78#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_78#2:
    call inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_nondet$257.41$7$ := storm_nondet();
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_81#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_81#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent := inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_nondet$257.41$7$;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_59#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon51_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_72_true#2:
    assume inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_IoSetCancelRoutine$237.37$6$ != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_76#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_76#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_77#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_77#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent := 0 - 1073741536;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_59#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon50_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon44_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_56_true#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_58#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_58#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent := 0 - 1073741823;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_59#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_59#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_1;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 == inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_1;
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    goto inline$storm_KeReleaseSpinLock$0$Entry#2;

  inline$storm_KeReleaseSpinLock$0$Entry#2:
    inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock_.1 := SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(inline$I8xKeyboardGetSysButtonEvent$0$$KeyboardExtension$1$148.29$I8xKeyboardGetSysButtonEvent);
    goto inline$storm_KeReleaseSpinLock$0$start#2;

  inline$storm_KeReleaseSpinLock$0$start#2:
    inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock := inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock_.1;
    goto inline$storm_KeReleaseSpinLock$0$label_3#2;

  inline$storm_KeReleaseSpinLock$0$label_3#2:
    goto inline$storm_KeReleaseSpinLock$0$label_4#2;

  inline$storm_KeReleaseSpinLock$0$label_4#2:
    __storm_atomic := true;
    goto inline$storm_KeReleaseSpinLock$0$label_7#2;

  inline$storm_KeReleaseSpinLock$0$label_7#2:
    havoc raiseException;
    goto inline$storm_KeReleaseSpinLock$0$anon8_Then#2, inline$storm_KeReleaseSpinLock$0$anon8_Else#2;

  inline$storm_KeReleaseSpinLock$0$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_KeReleaseSpinLock$0$anon1#2;

  inline$storm_KeReleaseSpinLock$0$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_LOCK[inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock], inline$storm_KeReleaseSpinLock$0$$lockStatus$3$144.6$storm_KeReleaseSpinLock);
    assume k == 1 ==> INT_EQ(Res_1_LOCK[inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock], inline$storm_KeReleaseSpinLock$0$$lockStatus$3$144.6$storm_KeReleaseSpinLock);
    call contextSwitch();
    goto inline$storm_KeReleaseSpinLock$0$label_8#2;

  inline$storm_KeReleaseSpinLock$0$label_8#2:
    goto inline$storm_getThreadID$1$Entry#2;

  inline$storm_getThreadID$1$Entry#2:
    goto inline$storm_getThreadID$1$anon0#2;

  inline$storm_getThreadID$1$anon0#2:
    inline$storm_getThreadID$1$tidRet := tid;
    goto inline$storm_getThreadID$1$Return#2;

  inline$storm_getThreadID$1$Return#2:
    inline$storm_KeReleaseSpinLock$0$$result.storm_getThreadID$145.0$1$ := inline$storm_getThreadID$1$tidRet;
    goto inline$storm_KeReleaseSpinLock$0$label_8$1#2;

  inline$storm_KeReleaseSpinLock$0$label_8$1#2:
    goto inline$storm_KeReleaseSpinLock$0$label_11#2;

  inline$storm_KeReleaseSpinLock$0$label_11#2:
    goto inline$storm_KeReleaseSpinLock$0$label_11_true#2, inline$storm_KeReleaseSpinLock$0$label_11_false#2;

  inline$storm_KeReleaseSpinLock$0$label_11_false#2:
    assume !INT_EQ(inline$storm_KeReleaseSpinLock$0$$lockStatus$3$144.6$storm_KeReleaseSpinLock, inline$storm_KeReleaseSpinLock$0$$result.storm_getThreadID$145.0$1$);
    goto inline$storm_KeReleaseSpinLock$0$label_12#2;

  inline$storm_KeReleaseSpinLock$0$label_12#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_KeReleaseSpinLock$0$label_1#2;

  inline$storm_KeReleaseSpinLock$0$label_11_true#2:
    assume INT_EQ(inline$storm_KeReleaseSpinLock$0$$lockStatus$3$144.6$storm_KeReleaseSpinLock, inline$storm_KeReleaseSpinLock$0$$result.storm_getThreadID$145.0$1$);
    goto inline$storm_KeReleaseSpinLock$0$label_15#2;

  inline$storm_KeReleaseSpinLock$0$label_15#2:
    goto inline$storm_KeReleaseSpinLock$0$anon9_Then#2, inline$storm_KeReleaseSpinLock$0$anon9_Else#2;

  inline$storm_KeReleaseSpinLock$0$anon9_Else#2:
    assume k != 0;
    goto inline$storm_KeReleaseSpinLock$0$anon10_Then#2, inline$storm_KeReleaseSpinLock$0$anon10_Else#2;

  inline$storm_KeReleaseSpinLock$0$anon10_Else#2:
    assume k != 1;
    goto inline$storm_KeReleaseSpinLock$0$anon5#2;

  inline$storm_KeReleaseSpinLock$0$anon10_Then#2:
    assume k == 1;
    Res_1_LOCK := Res_1_LOCK[inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock := 0];
    goto inline$storm_KeReleaseSpinLock$0$anon5#2;

  inline$storm_KeReleaseSpinLock$0$anon9_Then#2:
    assume k == 0;
    Res_0_LOCK := Res_0_LOCK[inline$storm_KeReleaseSpinLock$0$$SpinLock$1$140.17$storm_KeReleaseSpinLock := 0];
    goto inline$storm_KeReleaseSpinLock$0$anon5#2;

  inline$storm_KeReleaseSpinLock$0$anon5#2:
    call contextSwitch();
    goto inline$storm_KeReleaseSpinLock$0$label_16#2;

  inline$storm_KeReleaseSpinLock$0$label_16#2:
    goto inline$storm_KeReleaseSpinLock$0$anon11_Then#2, inline$storm_KeReleaseSpinLock$0$anon11_Else#2;

  inline$storm_KeReleaseSpinLock$0$anon11_Else#2:
    assume __storm_init;
    goto inline$storm_KeReleaseSpinLock$0$anon7#2;

  inline$storm_KeReleaseSpinLock$0$anon11_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_KeReleaseSpinLock$0$anon7#2;

  inline$storm_KeReleaseSpinLock$0$anon7#2:
    call contextSwitch();
    goto inline$storm_KeReleaseSpinLock$0$label_1#2;

  inline$storm_KeReleaseSpinLock$0$label_1#2:
    goto inline$storm_KeReleaseSpinLock$0$Return#2;

  inline$storm_KeReleaseSpinLock$0$anon8_Then#2:
    assume raiseException;
    goto inline$storm_KeReleaseSpinLock$0$Return#2;

  inline$storm_KeReleaseSpinLock$0$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_59$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_59$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon43_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon43_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon43_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon19#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon19#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_51#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon43_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon36_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_15_true#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_26#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_26#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_27#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_27#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent := 0 - 1073741670;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_28#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_28#2:
    goto inline$storm_ExAllocatePoolWithTag$0$Entry#2;

  inline$storm_ExAllocatePoolWithTag$0$Entry#2:
    inline$storm_ExAllocatePoolWithTag$0$$NumberOfBytes$2$511.12$storm_ExAllocatePoolWithTag_.1 := 12;
    goto inline$storm_ExAllocatePoolWithTag$0$start#2;

  inline$storm_ExAllocatePoolWithTag$0$start#2:
    inline$storm_ExAllocatePoolWithTag$0$$NumberOfBytes$2$511.12$storm_ExAllocatePoolWithTag := inline$storm_ExAllocatePoolWithTag$0$$NumberOfBytes$2$511.12$storm_ExAllocatePoolWithTag_.1;
    goto inline$storm_ExAllocatePoolWithTag$0$label_3#2;

  inline$storm_ExAllocatePoolWithTag$0$label_3#2:
    call inline$storm_ExAllocatePoolWithTag$0$$result.malloc$515.15$2$ := __HAVOC_malloc(inline$storm_ExAllocatePoolWithTag$0$$NumberOfBytes$2$511.12$storm_ExAllocatePoolWithTag);
    goto inline$storm_ExAllocatePoolWithTag$0$label_6#2;

  inline$storm_ExAllocatePoolWithTag$0$label_6#2:
    inline$storm_ExAllocatePoolWithTag$0$$result.storm_ExAllocatePoolWithTag$509.0$1$ := inline$storm_ExAllocatePoolWithTag$0$$result.malloc$515.15$2$;
    goto inline$storm_ExAllocatePoolWithTag$0$label_1#2;

  inline$storm_ExAllocatePoolWithTag$0$label_1#2:
    goto inline$storm_ExAllocatePoolWithTag$0$Return#2;

  inline$storm_ExAllocatePoolWithTag$0$Return#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_ExAllocatePoolWithTag$177.12$3$ := inline$storm_ExAllocatePoolWithTag$0$$result.storm_ExAllocatePoolWithTag$509.0$1$;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_28$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_28$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon37_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon37_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon37_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon7#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon7#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_31#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_31#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$item$9$172.32$I8xKeyboardGetSysButtonEvent := inline$I8xKeyboardGetSysButtonEvent$0$$result.storm_ExAllocatePoolWithTag$177.12$3$;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_32#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_32#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_32_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_32_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_32_false#2:
    assume inline$I8xKeyboardGetSysButtonEvent$0$$item$9$172.32$I8xKeyboardGetSysButtonEvent == 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_33#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_32_true#2:
    assume inline$I8xKeyboardGetSysButtonEvent$0$$item$9$172.32$I8xKeyboardGetSysButtonEvent != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_34#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_34#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    call inline$I8xKeyboardGetSysButtonEvent$0$$result.IoAllocateWorkItem$180.43$4$ := IoAllocateWorkItem(inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0);
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon38_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon38_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon38_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon9#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon9#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_37#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_37#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_38#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_38#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_38_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_38_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_38_false#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 == 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_39#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_39#2:
    call ExFreePoolWithTag(inline$I8xKeyboardGetSysButtonEvent$0$$item$9$172.32$I8xKeyboardGetSysButtonEvent, 0);
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon39_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon39_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon39_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon11#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon11#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_33#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon39_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_38_true#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0 != 0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_42#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_42#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_43#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_43#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_44#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_44#2:
    goto inline$storm_IoMarkIrpPending$0$Entry#2;

  inline$storm_IoMarkIrpPending$0$Entry#2:
    inline$storm_IoMarkIrpPending$0$$pirp$1$376.14$storm_IoMarkIrpPending_.1 := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent;
    goto inline$storm_IoMarkIrpPending$0$start#2;

  inline$storm_IoMarkIrpPending$0$start#2:
    inline$storm_IoMarkIrpPending$0$$pirp$1$376.14$storm_IoMarkIrpPending := inline$storm_IoMarkIrpPending$0$$pirp$1$376.14$storm_IoMarkIrpPending_.1;
    goto inline$storm_IoMarkIrpPending$0$label_3#2;

  inline$storm_IoMarkIrpPending$0$label_3#2:
    call inline$storm_IoMarkIrpPending$0$$result.storm_nondet$379.2$1$ := storm_nondet();
    goto inline$storm_IoMarkIrpPending$0$label_6#2;

  inline$storm_IoMarkIrpPending$0$label_6#2:
    goto inline$storm_IoMarkIrpPending$0$label_6_true#2, inline$storm_IoMarkIrpPending$0$label_6_false#2;

  inline$storm_IoMarkIrpPending$0$label_6_false#2:
    assume inline$storm_IoMarkIrpPending$0$$result.storm_nondet$379.2$1$ == 0;
    goto inline$storm_IoMarkIrpPending$0$label_1#2;

  inline$storm_IoMarkIrpPending$0$label_6_true#2:
    assume inline$storm_IoMarkIrpPending$0$$result.storm_nondet$379.2$1$ != 0;
    goto inline$storm_IoMarkIrpPending$0$label_7#2;

  inline$storm_IoMarkIrpPending$0$label_7#2:
    havoc raiseException;
    goto inline$storm_IoMarkIrpPending$0$anon3_Then#2, inline$storm_IoMarkIrpPending$0$anon3_Else#2;

  inline$storm_IoMarkIrpPending$0$anon3_Else#2:
    assume !raiseException;
    goto inline$storm_IoMarkIrpPending$0$anon1#2;

  inline$storm_IoMarkIrpPending$0$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoMarkIrpPending$0$$pirp$1$376.14$storm_IoMarkIrpPending], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoMarkIrpPending$0$$pirp$1$376.14$storm_IoMarkIrpPending], 1);
    call contextSwitch();
    goto inline$storm_IoMarkIrpPending$0$label_8#2;

  inline$storm_IoMarkIrpPending$0$label_8#2:
    goto inline$storm_IoMarkIrpPending$0$label_8_true#2, inline$storm_IoMarkIrpPending$0$label_8_false#2;

  inline$storm_IoMarkIrpPending$0$label_8_false#2:
    assume 0 == 0;
    goto inline$storm_IoMarkIrpPending$0$label_9#2;

  inline$storm_IoMarkIrpPending$0$label_9#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoMarkIrpPending$0$label_1#2;

  inline$storm_IoMarkIrpPending$0$label_8_true#2:
    assume 0 != 0;
    goto inline$storm_IoMarkIrpPending$0$label_1#2;

  inline$storm_IoMarkIrpPending$0$label_1#2:
    goto inline$storm_IoMarkIrpPending$0$Return#2;

  inline$storm_IoMarkIrpPending$0$anon3_Then#2:
    assume raiseException;
    goto inline$storm_IoMarkIrpPending$0$Return#2;

  inline$storm_IoMarkIrpPending$0$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_44$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_44$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon40_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon40_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon40_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon13#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon13#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_47#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_47#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    call IoQueueWorkItem(inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0, I8xCompleteSysButtonEventWorker, 1, inline$I8xKeyboardGetSysButtonEvent$0$$item$9$172.32$I8xKeyboardGetSysButtonEvent);
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon41_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon41_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon41_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon15#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon15#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_50#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_50#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent := 259;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_33#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_33#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_51#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_51#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_51_true#2, inline$I8xKeyboardGetSysButtonEvent$0$label_51_false#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_51_false#2:
    assume !INT_NEQ(inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent, 259);
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_52#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_51_true#2:
    assume INT_NEQ(inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent, 259);
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_53#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_53#2:
    goto inline$I8xCompleteSysButtonIrp$0$Entry#2;

  inline$I8xCompleteSysButtonIrp$0$Entry#2:
    inline$I8xCompleteSysButtonIrp$0$$Irp$1$50.9$I8xCompleteSysButtonIrp_.1 := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent;
    goto inline$I8xCompleteSysButtonIrp$0$start#2;

  inline$I8xCompleteSysButtonIrp$0$start#2:
    inline$I8xCompleteSysButtonIrp$0$$Irp$1$50.9$I8xCompleteSysButtonIrp := inline$I8xCompleteSysButtonIrp$0$$Irp$1$50.9$I8xCompleteSysButtonIrp_.1;
    goto inline$I8xCompleteSysButtonIrp$0$label_3#2;

  inline$I8xCompleteSysButtonIrp$0$label_3#2:
    havoc inline$I8xCompleteSysButtonIrp$0$myNondetVar_0;
    goto inline$I8xCompleteSysButtonIrp$0$label_4#2;

  inline$I8xCompleteSysButtonIrp$0$label_4#2:
    goto inline$I8xCompleteSysButtonIrp$0$label_5#2;

  inline$I8xCompleteSysButtonIrp$0$label_5#2:
    goto inline$I8xCompleteSysButtonIrp$0$label_6#2;

  inline$I8xCompleteSysButtonIrp$0$label_6#2:
    goto inline$storm_IoCompleteRequest$2$Entry#2;

  inline$storm_IoCompleteRequest$2$Entry#2:
    inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest_.1 := inline$I8xCompleteSysButtonIrp$0$$Irp$1$50.9$I8xCompleteSysButtonIrp;
    goto inline$storm_IoCompleteRequest$2$start#2;

  inline$storm_IoCompleteRequest$2$start#2:
    inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest := inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest_.1;
    goto inline$storm_IoCompleteRequest$2$label_3#2;

  inline$storm_IoCompleteRequest$2$label_3#2:
    call inline$storm_IoCompleteRequest$2$$result.storm_nondet$343.2$1$ := storm_nondet();
    goto inline$storm_IoCompleteRequest$2$label_6#2;

  inline$storm_IoCompleteRequest$2$label_6#2:
    goto inline$storm_IoCompleteRequest$2$label_6_true#2, inline$storm_IoCompleteRequest$2$label_6_false#2;

  inline$storm_IoCompleteRequest$2$label_6_false#2:
    assume inline$storm_IoCompleteRequest$2$$result.storm_nondet$343.2$1$ == 0;
    goto inline$storm_IoCompleteRequest$2$label_7#2;

  inline$storm_IoCompleteRequest$2$label_6_true#2:
    assume inline$storm_IoCompleteRequest$2$$result.storm_nondet$343.2$1$ != 0;
    goto inline$storm_IoCompleteRequest$2$label_8#2;

  inline$storm_IoCompleteRequest$2$label_8#2:
    havoc raiseException;
    goto inline$storm_IoCompleteRequest$2$anon8_Then#2, inline$storm_IoCompleteRequest$2$anon8_Else#2;

  inline$storm_IoCompleteRequest$2$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_IoCompleteRequest$2$anon4#2;

  inline$storm_IoCompleteRequest$2$anon4#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$2$label_9#2;

  inline$storm_IoCompleteRequest$2$label_9#2:
    goto inline$storm_IoCompleteRequest$2$label_9_true#2, inline$storm_IoCompleteRequest$2$label_9_false#2;

  inline$storm_IoCompleteRequest$2$label_9_false#2:
    assume 0 == 0;
    goto inline$storm_IoCompleteRequest$2$label_10#2;

  inline$storm_IoCompleteRequest$2$label_10#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoCompleteRequest$2$label_1#2;

  inline$storm_IoCompleteRequest$2$label_9_true#2:
    assume 0 != 0;
    goto inline$storm_IoCompleteRequest$2$label_7#2;

  inline$storm_IoCompleteRequest$2$label_7#2:
    goto inline$storm_IoCompleteRequest$2$anon6_Then#2, inline$storm_IoCompleteRequest$2$anon6_Else#2;

  inline$storm_IoCompleteRequest$2$anon6_Else#2:
    assume k != 0;
    goto inline$storm_IoCompleteRequest$2$anon7_Then#2, inline$storm_IoCompleteRequest$2$anon7_Else#2;

  inline$storm_IoCompleteRequest$2$anon7_Else#2:
    assume k != 1;
    goto inline$storm_IoCompleteRequest$2$anon2#2;

  inline$storm_IoCompleteRequest$2$anon7_Then#2:
    assume k == 1;
    Res_1_COMPLETED := Res_1_COMPLETED[inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$2$anon2#2;

  inline$storm_IoCompleteRequest$2$anon6_Then#2:
    assume k == 0;
    Res_0_COMPLETED := Res_0_COMPLETED[inline$storm_IoCompleteRequest$2$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$2$anon2#2;

  inline$storm_IoCompleteRequest$2$anon2#2:
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$2$label_1#2;

  inline$storm_IoCompleteRequest$2$label_1#2:
    goto inline$storm_IoCompleteRequest$2$Return#2;

  inline$storm_IoCompleteRequest$2$anon8_Then#2:
    assume raiseException;
    goto inline$storm_IoCompleteRequest$2$Return#2;

  inline$storm_IoCompleteRequest$2$Return#2:
    goto inline$I8xCompleteSysButtonIrp$0$label_6$1#2;

  inline$I8xCompleteSysButtonIrp$0$label_6$1#2:
    goto inline$I8xCompleteSysButtonIrp$0$anon2_Then#2, inline$I8xCompleteSysButtonIrp$0$anon2_Else#2;

  inline$I8xCompleteSysButtonIrp$0$anon2_Else#2:
    assume !raiseException;
    goto inline$I8xCompleteSysButtonIrp$0$anon1#2;

  inline$I8xCompleteSysButtonIrp$0$anon1#2:
    goto inline$I8xCompleteSysButtonIrp$0$label_1#2;

  inline$I8xCompleteSysButtonIrp$0$label_1#2:
    goto inline$I8xCompleteSysButtonIrp$0$Return#2;

  inline$I8xCompleteSysButtonIrp$0$anon2_Then#2:
    assume raiseException;
    goto inline$I8xCompleteSysButtonIrp$0$Return#2;

  inline$I8xCompleteSysButtonIrp$0$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_53$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_53$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon42_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon42_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon42_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon17#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon17#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_52#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_52#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon42_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon41_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon40_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon38_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon37_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_14_true#2:
    havoc inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0;
    assume INT_ULT(inline$I8xKeyboardGetSysButtonEvent$0$myNondetVar_0, 4);
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_16#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_16#2:
    inline$I8xKeyboardGetSysButtonEvent$0$$status$6$154.24$I8xKeyboardGetSysButtonEvent := 0 - 1073741306;
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_17#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_17#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_18#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_18#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_19#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_19#2:
    goto inline$storm_IoCompleteRequest$1$Entry#2;

  inline$storm_IoCompleteRequest$1$Entry#2:
    inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest_.1 := inline$I8xKeyboardGetSysButtonEvent$0$$Irp$2$149.9$I8xKeyboardGetSysButtonEvent;
    goto inline$storm_IoCompleteRequest$1$start#2;

  inline$storm_IoCompleteRequest$1$start#2:
    inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest := inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest_.1;
    goto inline$storm_IoCompleteRequest$1$label_3#2;

  inline$storm_IoCompleteRequest$1$label_3#2:
    call inline$storm_IoCompleteRequest$1$$result.storm_nondet$343.2$1$ := storm_nondet();
    goto inline$storm_IoCompleteRequest$1$label_6#2;

  inline$storm_IoCompleteRequest$1$label_6#2:
    goto inline$storm_IoCompleteRequest$1$label_6_true#2, inline$storm_IoCompleteRequest$1$label_6_false#2;

  inline$storm_IoCompleteRequest$1$label_6_false#2:
    assume inline$storm_IoCompleteRequest$1$$result.storm_nondet$343.2$1$ == 0;
    goto inline$storm_IoCompleteRequest$1$label_7#2;

  inline$storm_IoCompleteRequest$1$label_6_true#2:
    assume inline$storm_IoCompleteRequest$1$$result.storm_nondet$343.2$1$ != 0;
    goto inline$storm_IoCompleteRequest$1$label_8#2;

  inline$storm_IoCompleteRequest$1$label_8#2:
    havoc raiseException;
    goto inline$storm_IoCompleteRequest$1$anon8_Then#2, inline$storm_IoCompleteRequest$1$anon8_Else#2;

  inline$storm_IoCompleteRequest$1$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_IoCompleteRequest$1$anon4#2;

  inline$storm_IoCompleteRequest$1$anon4#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$1$label_9#2;

  inline$storm_IoCompleteRequest$1$label_9#2:
    goto inline$storm_IoCompleteRequest$1$label_9_true#2, inline$storm_IoCompleteRequest$1$label_9_false#2;

  inline$storm_IoCompleteRequest$1$label_9_false#2:
    assume 0 == 0;
    goto inline$storm_IoCompleteRequest$1$label_10#2;

  inline$storm_IoCompleteRequest$1$label_10#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoCompleteRequest$1$label_1#2;

  inline$storm_IoCompleteRequest$1$label_9_true#2:
    assume 0 != 0;
    goto inline$storm_IoCompleteRequest$1$label_7#2;

  inline$storm_IoCompleteRequest$1$label_7#2:
    goto inline$storm_IoCompleteRequest$1$anon6_Then#2, inline$storm_IoCompleteRequest$1$anon6_Else#2;

  inline$storm_IoCompleteRequest$1$anon6_Else#2:
    assume k != 0;
    goto inline$storm_IoCompleteRequest$1$anon7_Then#2, inline$storm_IoCompleteRequest$1$anon7_Else#2;

  inline$storm_IoCompleteRequest$1$anon7_Else#2:
    assume k != 1;
    goto inline$storm_IoCompleteRequest$1$anon2#2;

  inline$storm_IoCompleteRequest$1$anon7_Then#2:
    assume k == 1;
    Res_1_COMPLETED := Res_1_COMPLETED[inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$1$anon2#2;

  inline$storm_IoCompleteRequest$1$anon6_Then#2:
    assume k == 0;
    Res_0_COMPLETED := Res_0_COMPLETED[inline$storm_IoCompleteRequest$1$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$1$anon2#2;

  inline$storm_IoCompleteRequest$1$anon2#2:
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$1$label_1#2;

  inline$storm_IoCompleteRequest$1$label_1#2:
    goto inline$storm_IoCompleteRequest$1$Return#2;

  inline$storm_IoCompleteRequest$1$anon8_Then#2:
    assume raiseException;
    goto inline$storm_IoCompleteRequest$1$Return#2;

  inline$storm_IoCompleteRequest$1$Return#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_19$1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_19$1#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon35_Then#2, inline$I8xKeyboardGetSysButtonEvent$0$anon35_Else#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon35_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$anon3#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon3#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_22#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_22#2:
    goto inline$I8xKeyboardGetSysButtonEvent$0$label_1#2;

  inline$I8xKeyboardGetSysButtonEvent$0$label_1#2:
    call __HAVOC_free(inline$I8xKeyboardGetSysButtonEvent$0$$irql$8$156.24$I8xKeyboardGetSysButtonEvent);
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon35_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$anon34_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonEvent$0$Return#2;

  inline$I8xKeyboardGetSysButtonEvent$0$Return#2:
    goto inline$I8xDeviceControl$0$label_24$1#2;

  inline$I8xDeviceControl$0$label_24$1#2:
    goto inline$I8xDeviceControl$0$anon18_Then#2, inline$I8xDeviceControl$0$anon18_Else#2;

  inline$I8xDeviceControl$0$anon18_Else#2:
    assume !raiseException;
    goto inline$I8xDeviceControl$0$anon10#2;

  inline$I8xDeviceControl$0$anon10#2:
    goto inline$I8xDeviceControl$0$label_27#2;

  inline$I8xDeviceControl$0$label_27#2:
    goto inline$I8xDeviceControl$0$label_1#2;

  inline$I8xDeviceControl$0$anon18_Then#2:
    assume raiseException;
    goto inline$I8xDeviceControl$0$Return#2;

  inline$I8xDeviceControl$0$label_19_case_1#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 == 2703680;
    goto inline$I8xDeviceControl$0$label_21#2;

  inline$I8xDeviceControl$0$label_21#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$Entry#2;

  inline$I8xKeyboardGetSysButtonCaps$0$Entry#2:
    inline$I8xKeyboardGetSysButtonCaps$0$$Irp$2$70.9$I8xKeyboardGetSysButtonCaps_.1 := inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl;
    goto inline$I8xKeyboardGetSysButtonCaps$0$start#2;

  inline$I8xKeyboardGetSysButtonCaps$0$start#2:
    inline$I8xKeyboardGetSysButtonCaps$0$$Irp$2$70.9$I8xKeyboardGetSysButtonCaps := inline$I8xKeyboardGetSysButtonCaps$0$$Irp$2$70.9$I8xKeyboardGetSysButtonCaps_.1;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_3#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_3#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_4#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_4#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_5#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_5#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_6#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_6#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_7#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_7#2:
    call __PREfastPagedCode();
    goto inline$I8xKeyboardGetSysButtonCaps$0$anon6_Then#2, inline$I8xKeyboardGetSysButtonCaps$0$anon6_Else#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon6_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonCaps$0$anon1#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon1#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_10#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_10#2:
    goto inline$IoGetCurrentIrpStackLocation$3$Entry#2;

  inline$IoGetCurrentIrpStackLocation$3$Entry#2:
    goto inline$IoGetCurrentIrpStackLocation$3$start#2;

  inline$IoGetCurrentIrpStackLocation$3$start#2:
    goto inline$IoGetCurrentIrpStackLocation$3$label_3#2;

  inline$IoGetCurrentIrpStackLocation$3$label_3#2:
    goto inline$IoGetCurrentIrpStackLocation$3$anon3_Then#2, inline$IoGetCurrentIrpStackLocation$3$anon3_Else#2;

  inline$IoGetCurrentIrpStackLocation$3$anon3_Else#2:
    assume k != 0;
    goto inline$IoGetCurrentIrpStackLocation$3$anon4_Then#2, inline$IoGetCurrentIrpStackLocation$3$anon4_Else#2;

  inline$IoGetCurrentIrpStackLocation$3$anon4_Else#2:
    assume k != 1;
    goto inline$IoGetCurrentIrpStackLocation$3$anon2#2;

  inline$IoGetCurrentIrpStackLocation$3$anon4_Then#2:
    assume k == 1;
    goto inline$IoGetCurrentIrpStackLocation$3$anon2#2;

  inline$IoGetCurrentIrpStackLocation$3$anon3_Then#2:
    assume k == 0;
    goto inline$IoGetCurrentIrpStackLocation$3$anon2#2;

  inline$IoGetCurrentIrpStackLocation$3$anon2#2:
    call contextSwitch();
    goto inline$IoGetCurrentIrpStackLocation$3$label_1#2;

  inline$IoGetCurrentIrpStackLocation$3$label_1#2:
    goto inline$IoGetCurrentIrpStackLocation$3$Return#2;

  inline$IoGetCurrentIrpStackLocation$3$Return#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_10$1#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_10$1#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$anon7_Then#2, inline$I8xKeyboardGetSysButtonCaps$0$anon7_Else#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon7_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonCaps$0$anon3#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon3#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_13#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_13#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_14#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_14#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_15#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_15#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_15_true#2, inline$I8xKeyboardGetSysButtonCaps$0$label_15_false#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_15_false#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume !INT_ULT(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 4);
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_16#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_16#2:
    inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps := 0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_24#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_24#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_25#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_25#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_25_true#2, inline$I8xKeyboardGetSysButtonCaps$0$label_25_false#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_25_false#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 1) == 0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_26#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_25_true#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 1) != 0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_27#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_27#2:
    inline$I8xKeyboardGetSysButtonCaps$0$tempBoogie0 := BIT_BOR(inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps, 1);
    inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps := inline$I8xKeyboardGetSysButtonCaps$0$tempBoogie0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_26#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_26#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_26_true#2, inline$I8xKeyboardGetSysButtonCaps$0$label_26_false#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_26_false#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 2) == 0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_28#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_26_true#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 2) != 0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_29#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_29#2:
    inline$I8xKeyboardGetSysButtonCaps$0$tempBoogie0 := BIT_BOR(inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps, 2);
    inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps := inline$I8xKeyboardGetSysButtonCaps$0$tempBoogie0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_28#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_28#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_28_true#2, inline$I8xKeyboardGetSysButtonCaps$0$label_28_false#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_28_false#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 4) == 0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_30#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_28_true#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 4) != 0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_31#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_31#2:
    inline$I8xKeyboardGetSysButtonCaps$0$tempBoogie0 := BIT_BOR(inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps, BOOGIE_LARGE_INT_2147483648);
    inline$I8xKeyboardGetSysButtonCaps$0$$caps$5$75.24$I8xKeyboardGetSysButtonCaps := inline$I8xKeyboardGetSysButtonCaps$0$tempBoogie0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_30#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_30#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_32#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_32#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_18#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_15_true#2:
    havoc inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0;
    assume INT_ULT(inline$I8xKeyboardGetSysButtonCaps$0$myNondetVar_0, 4);
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_17#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_17#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_18#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_18#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_19#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_19#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_20#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_20#2:
    goto inline$storm_IoCompleteRequest$0$Entry#2;

  inline$storm_IoCompleteRequest$0$Entry#2:
    inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest_.1 := inline$I8xKeyboardGetSysButtonCaps$0$$Irp$2$70.9$I8xKeyboardGetSysButtonCaps;
    goto inline$storm_IoCompleteRequest$0$start#2;

  inline$storm_IoCompleteRequest$0$start#2:
    inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest := inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest_.1;
    goto inline$storm_IoCompleteRequest$0$label_3#2;

  inline$storm_IoCompleteRequest$0$label_3#2:
    call inline$storm_IoCompleteRequest$0$$result.storm_nondet$343.2$1$ := storm_nondet();
    goto inline$storm_IoCompleteRequest$0$label_6#2;

  inline$storm_IoCompleteRequest$0$label_6#2:
    goto inline$storm_IoCompleteRequest$0$label_6_true#2, inline$storm_IoCompleteRequest$0$label_6_false#2;

  inline$storm_IoCompleteRequest$0$label_6_false#2:
    assume inline$storm_IoCompleteRequest$0$$result.storm_nondet$343.2$1$ == 0;
    goto inline$storm_IoCompleteRequest$0$label_7#2;

  inline$storm_IoCompleteRequest$0$label_6_true#2:
    assume inline$storm_IoCompleteRequest$0$$result.storm_nondet$343.2$1$ != 0;
    goto inline$storm_IoCompleteRequest$0$label_8#2;

  inline$storm_IoCompleteRequest$0$label_8#2:
    havoc raiseException;
    goto inline$storm_IoCompleteRequest$0$anon8_Then#2, inline$storm_IoCompleteRequest$0$anon8_Else#2;

  inline$storm_IoCompleteRequest$0$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_IoCompleteRequest$0$anon4#2;

  inline$storm_IoCompleteRequest$0$anon4#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$0$label_9#2;

  inline$storm_IoCompleteRequest$0$label_9#2:
    goto inline$storm_IoCompleteRequest$0$label_9_true#2, inline$storm_IoCompleteRequest$0$label_9_false#2;

  inline$storm_IoCompleteRequest$0$label_9_false#2:
    assume 0 == 0;
    goto inline$storm_IoCompleteRequest$0$label_10#2;

  inline$storm_IoCompleteRequest$0$label_10#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoCompleteRequest$0$label_1#2;

  inline$storm_IoCompleteRequest$0$label_9_true#2:
    assume 0 != 0;
    goto inline$storm_IoCompleteRequest$0$label_7#2;

  inline$storm_IoCompleteRequest$0$label_7#2:
    goto inline$storm_IoCompleteRequest$0$anon6_Then#2, inline$storm_IoCompleteRequest$0$anon6_Else#2;

  inline$storm_IoCompleteRequest$0$anon6_Else#2:
    assume k != 0;
    goto inline$storm_IoCompleteRequest$0$anon7_Then#2, inline$storm_IoCompleteRequest$0$anon7_Else#2;

  inline$storm_IoCompleteRequest$0$anon7_Else#2:
    assume k != 1;
    goto inline$storm_IoCompleteRequest$0$anon2#2;

  inline$storm_IoCompleteRequest$0$anon7_Then#2:
    assume k == 1;
    Res_1_COMPLETED := Res_1_COMPLETED[inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$0$anon2#2;

  inline$storm_IoCompleteRequest$0$anon6_Then#2:
    assume k == 0;
    Res_0_COMPLETED := Res_0_COMPLETED[inline$storm_IoCompleteRequest$0$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$0$anon2#2;

  inline$storm_IoCompleteRequest$0$anon2#2:
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$0$label_1#2;

  inline$storm_IoCompleteRequest$0$label_1#2:
    goto inline$storm_IoCompleteRequest$0$Return#2;

  inline$storm_IoCompleteRequest$0$anon8_Then#2:
    assume raiseException;
    goto inline$storm_IoCompleteRequest$0$Return#2;

  inline$storm_IoCompleteRequest$0$Return#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_20$1#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_20$1#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$anon8_Then#2, inline$I8xKeyboardGetSysButtonCaps$0$anon8_Else#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon8_Else#2:
    assume !raiseException;
    goto inline$I8xKeyboardGetSysButtonCaps$0$anon5#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon5#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_23#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_23#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$label_1#2;

  inline$I8xKeyboardGetSysButtonCaps$0$label_1#2:
    goto inline$I8xKeyboardGetSysButtonCaps$0$Return#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon8_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonCaps$0$Return#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon7_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonCaps$0$Return#2;

  inline$I8xKeyboardGetSysButtonCaps$0$anon6_Then#2:
    assume raiseException;
    goto inline$I8xKeyboardGetSysButtonCaps$0$Return#2;

  inline$I8xKeyboardGetSysButtonCaps$0$Return#2:
    goto inline$I8xDeviceControl$0$label_21$1#2;

  inline$I8xDeviceControl$0$label_21$1#2:
    goto inline$I8xDeviceControl$0$anon17_Then#2, inline$I8xDeviceControl$0$anon17_Else#2;

  inline$I8xDeviceControl$0$anon17_Else#2:
    assume !raiseException;
    goto inline$I8xDeviceControl$0$anon8#2;

  inline$I8xDeviceControl$0$anon8#2:
    goto inline$I8xDeviceControl$0$label_28#2;

  inline$I8xDeviceControl$0$label_28#2:
    goto inline$I8xDeviceControl$0$label_1#2;

  inline$I8xDeviceControl$0$anon17_Then#2:
    assume raiseException;
    goto inline$I8xDeviceControl$0$Return#2;

  inline$I8xDeviceControl$0$label_19_case_0#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 != 2703680;
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume inline$I8xDeviceControl$0$myNondetVar_0 != 2703684;
    goto inline$I8xDeviceControl$0$label_20#2;

  inline$I8xDeviceControl$0$label_20#2:
    goto inline$I8xDeviceControl$0$label_29#2;

  inline$I8xDeviceControl$0$anon16_Then#2:
    assume raiseException;
    goto inline$I8xDeviceControl$0$Return#2;

  inline$I8xDeviceControl$0$label_14_true#2:
    havoc inline$I8xDeviceControl$0$myNondetVar_0;
    assume BIT_BAND(inline$I8xDeviceControl$0$myNondetVar_0, 8) != 0;
    goto inline$I8xDeviceControl$0$label_12#2;

  inline$I8xDeviceControl$0$label_12#2:
    goto inline$I8xDeviceControl$0$label_29#2;

  inline$I8xDeviceControl$0$label_29#2:
    goto inline$I8xDeviceControl$0$label_30#2;

  inline$I8xDeviceControl$0$label_30#2:
    goto inline$storm_IoCompleteRequest$3$Entry#2;

  inline$storm_IoCompleteRequest$3$Entry#2:
    inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest_.1 := inline$I8xDeviceControl$0$$Irp$2$465.12$I8xDeviceControl;
    goto inline$storm_IoCompleteRequest$3$start#2;

  inline$storm_IoCompleteRequest$3$start#2:
    inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest := inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest_.1;
    goto inline$storm_IoCompleteRequest$3$label_3#2;

  inline$storm_IoCompleteRequest$3$label_3#2:
    call inline$storm_IoCompleteRequest$3$$result.storm_nondet$343.2$1$ := storm_nondet();
    goto inline$storm_IoCompleteRequest$3$label_6#2;

  inline$storm_IoCompleteRequest$3$label_6#2:
    goto inline$storm_IoCompleteRequest$3$label_6_true#2, inline$storm_IoCompleteRequest$3$label_6_false#2;

  inline$storm_IoCompleteRequest$3$label_6_false#2:
    assume inline$storm_IoCompleteRequest$3$$result.storm_nondet$343.2$1$ == 0;
    goto inline$storm_IoCompleteRequest$3$label_7#2;

  inline$storm_IoCompleteRequest$3$label_6_true#2:
    assume inline$storm_IoCompleteRequest$3$$result.storm_nondet$343.2$1$ != 0;
    goto inline$storm_IoCompleteRequest$3$label_8#2;

  inline$storm_IoCompleteRequest$3$label_8#2:
    havoc raiseException;
    goto inline$storm_IoCompleteRequest$3$anon8_Then#2, inline$storm_IoCompleteRequest$3$anon8_Else#2;

  inline$storm_IoCompleteRequest$3$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_IoCompleteRequest$3$anon4#2;

  inline$storm_IoCompleteRequest$3$anon4#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$3$label_9#2;

  inline$storm_IoCompleteRequest$3$label_9#2:
    goto inline$storm_IoCompleteRequest$3$label_9_true#2, inline$storm_IoCompleteRequest$3$label_9_false#2;

  inline$storm_IoCompleteRequest$3$label_9_false#2:
    assume 0 == 0;
    goto inline$storm_IoCompleteRequest$3$label_10#2;

  inline$storm_IoCompleteRequest$3$label_10#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoCompleteRequest$3$label_1#2;

  inline$storm_IoCompleteRequest$3$label_9_true#2:
    assume 0 != 0;
    goto inline$storm_IoCompleteRequest$3$label_7#2;

  inline$storm_IoCompleteRequest$3$label_7#2:
    goto inline$storm_IoCompleteRequest$3$anon6_Then#2, inline$storm_IoCompleteRequest$3$anon6_Else#2;

  inline$storm_IoCompleteRequest$3$anon6_Else#2:
    assume k != 0;
    goto inline$storm_IoCompleteRequest$3$anon7_Then#2, inline$storm_IoCompleteRequest$3$anon7_Else#2;

  inline$storm_IoCompleteRequest$3$anon7_Else#2:
    assume k != 1;
    goto inline$storm_IoCompleteRequest$3$anon2#2;

  inline$storm_IoCompleteRequest$3$anon7_Then#2:
    assume k == 1;
    Res_1_COMPLETED := Res_1_COMPLETED[inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$3$anon2#2;

  inline$storm_IoCompleteRequest$3$anon6_Then#2:
    assume k == 0;
    Res_0_COMPLETED := Res_0_COMPLETED[inline$storm_IoCompleteRequest$3$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$3$anon2#2;

  inline$storm_IoCompleteRequest$3$anon2#2:
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$3$label_1#2;

  inline$storm_IoCompleteRequest$3$label_1#2:
    goto inline$storm_IoCompleteRequest$3$Return#2;

  inline$storm_IoCompleteRequest$3$anon8_Then#2:
    assume raiseException;
    goto inline$storm_IoCompleteRequest$3$Return#2;

  inline$storm_IoCompleteRequest$3$Return#2:
    goto inline$I8xDeviceControl$0$label_30$1#2;

  inline$I8xDeviceControl$0$label_30$1#2:
    goto inline$I8xDeviceControl$0$anon19_Then#2, inline$I8xDeviceControl$0$anon19_Else#2;

  inline$I8xDeviceControl$0$anon19_Else#2:
    assume !raiseException;
    goto inline$I8xDeviceControl$0$anon12#2;

  inline$I8xDeviceControl$0$anon12#2:
    goto inline$I8xDeviceControl$0$label_33#2;

  inline$I8xDeviceControl$0$label_33#2:
    goto inline$I8xDeviceControl$0$label_1#2;

  inline$I8xDeviceControl$0$label_1#2:
    goto inline$I8xDeviceControl$0$Return#2;

  inline$I8xDeviceControl$0$anon19_Then#2:
    assume raiseException;
    goto inline$I8xDeviceControl$0$Return#2;

  inline$I8xDeviceControl$0$anon13_Then#2:
    assume raiseException;
    goto inline$I8xDeviceControl$0$Return#2;

  inline$I8xDeviceControl$0$Return#2:
    goto inline$dispatch$0$label_8$1#2;

  inline$dispatch$0$label_8$1#2:
    goto inline$dispatch$0$anon5_Then#2, inline$dispatch$0$anon5_Else#2;

  inline$dispatch$0$anon5_Else#2:
    assume !raiseException;
    goto inline$dispatch$0$anon3#2;

  inline$dispatch$0$anon3#2:
    goto inline$dispatch$0$label_11#2;

  inline$dispatch$0$label_11#2:
    goto inline$dispatch$0$label_1#2;

  inline$dispatch$0$label_1#2:
    goto inline$dispatch$0$Return#2;

  inline$dispatch$0$anon5_Then#2:
    assume raiseException;
    goto inline$dispatch$0$Return#2;

  inline$dispatch$0$anon4_Then#2:
    assume raiseException;
    goto inline$dispatch$0$Return#2;

  inline$dispatch$0$Return#2:
    goto label_23$1#2;

  label_23$1#2:
    goto anon31_Then#2, anon31_Else#2;

  anon31_Else#2:
    assume !(errorReached || !raiseException);
    goto anon17#2;

  anon31_Then#2:
    assume errorReached || !raiseException;
    __storm_thread_done_1 := true;
    goto anon17#2;

  anon17#2:
    k := k_old_0;
    tid := tid_old_0;
    goto label_26#2;

  label_26#2:
    goto label_27#2;

  label_27#2:
    k_old_1 := k;
    tid_old_1 := tid;
    tidCount_old := tidCount;
    havoc tidCount;
    assume tidCount_old < tidCount;
    tid := tidCount;
    raiseException := false;
    call contextSwitch();
    goto inline$cancel$0$Entry#2;

  inline$cancel$0$Entry#2:
    inline$cancel$0$$Irp$1$64.17$cancel_.1 := $irp$1$91.7$storm_main;
    goto inline$cancel$0$start#2;

  inline$cancel$0$start#2:
    inline$cancel$0$$Irp$1$64.17$cancel := inline$cancel$0$$Irp$1$64.17$cancel_.1;
    goto inline$cancel$0$label_3#2;

  inline$cancel$0$label_3#2:
    goto inline$storm_IoCancelIrp$0$Entry#2;

  inline$storm_IoCancelIrp$0$Entry#2:
    inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp_.1 := inline$cancel$0$$Irp$1$64.17$cancel;
    goto inline$storm_IoCancelIrp$0$start#2;

  inline$storm_IoCancelIrp$0$start#2:
    inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp := inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp_.1;
    goto inline$storm_IoCancelIrp$0$label_3#2;

  inline$storm_IoCancelIrp$0$label_3#2:
    goto inline$storm_IoCancelIrp$0$label_4#2;

  inline$storm_IoCancelIrp$0$label_4#2:
    goto inline$storm_IoCancelIrp$0$anon23_Then#2, inline$storm_IoCancelIrp$0$anon23_Else#2;

  inline$storm_IoCancelIrp$0$anon23_Else#2:
    assume k != 0;
    goto inline$storm_IoCancelIrp$0$anon24_Then#2, inline$storm_IoCancelIrp$0$anon24_Else#2;

  inline$storm_IoCancelIrp$0$anon24_Else#2:
    assume k != 1;
    goto inline$storm_IoCancelIrp$0$anon2#2;

  inline$storm_IoCancelIrp$0$anon24_Then#2:
    assume k == 1;
    Mem_1_T.Cancel__IRP := Mem_1_T.Cancel__IRP[Cancel__IRP(inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp) := 1];
    goto inline$storm_IoCancelIrp$0$anon2#2;

  inline$storm_IoCancelIrp$0$anon23_Then#2:
    assume k == 0;
    Mem_0_T.Cancel__IRP := Mem_0_T.Cancel__IRP[Cancel__IRP(inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp) := 1];
    goto inline$storm_IoCancelIrp$0$anon2#2;

  inline$storm_IoCancelIrp$0$anon2#2:
    call contextSwitch();
    goto inline$storm_IoCancelIrp$0$label_5#2;

  inline$storm_IoCancelIrp$0$label_5#2:
    __storm_atomic := true;
    goto inline$storm_IoCancelIrp$0$label_8#2;

  inline$storm_IoCancelIrp$0$label_8#2:
    goto inline$storm_IoCancelIrp$0$anon25_Then#2, inline$storm_IoCancelIrp$0$anon25_Else#2;

  inline$storm_IoCancelIrp$0$anon25_Else#2:
    assume k != 0;
    goto inline$storm_IoCancelIrp$0$anon26_Then#2, inline$storm_IoCancelIrp$0$anon26_Else#2;

  inline$storm_IoCancelIrp$0$anon26_Else#2:
    assume k != 1;
    goto inline$storm_IoCancelIrp$0$anon5#2;

  inline$storm_IoCancelIrp$0$anon26_Then#2:
    assume k == 1;
    inline$storm_IoCancelIrp$0$myVar_0 := Mem_1_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp)];
    goto inline$storm_IoCancelIrp$0$anon5#2;

  inline$storm_IoCancelIrp$0$anon25_Then#2:
    assume k == 0;
    inline$storm_IoCancelIrp$0$myVar_0 := Mem_0_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp)];
    goto inline$storm_IoCancelIrp$0$anon5#2;

  inline$storm_IoCancelIrp$0$anon5#2:
    call contextSwitch();
    inline$storm_IoCancelIrp$0$$oldCancelRoutine$2$352.17$storm_IoCancelIrp := inline$storm_IoCancelIrp$0$myVar_0;
    goto inline$storm_IoCancelIrp$0$label_9#2;

  inline$storm_IoCancelIrp$0$label_9#2:
    goto inline$storm_IoCancelIrp$0$anon27_Then#2, inline$storm_IoCancelIrp$0$anon27_Else#2;

  inline$storm_IoCancelIrp$0$anon27_Else#2:
    assume k != 0;
    goto inline$storm_IoCancelIrp$0$anon28_Then#2, inline$storm_IoCancelIrp$0$anon28_Else#2;

  inline$storm_IoCancelIrp$0$anon28_Else#2:
    assume k != 1;
    goto inline$storm_IoCancelIrp$0$anon8#2;

  inline$storm_IoCancelIrp$0$anon28_Then#2:
    assume k == 1;
    Mem_1_T.CancelRoutine__IRP := Mem_1_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp) := 0];
    goto inline$storm_IoCancelIrp$0$anon8#2;

  inline$storm_IoCancelIrp$0$anon27_Then#2:
    assume k == 0;
    Mem_0_T.CancelRoutine__IRP := Mem_0_T.CancelRoutine__IRP[CancelRoutine__IRP(inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp) := 0];
    goto inline$storm_IoCancelIrp$0$anon8#2;

  inline$storm_IoCancelIrp$0$anon8#2:
    call contextSwitch();
    goto inline$storm_IoCancelIrp$0$label_10#2;

  inline$storm_IoCancelIrp$0$label_10#2:
    goto inline$storm_IoCancelIrp$0$anon29_Then#2, inline$storm_IoCancelIrp$0$anon29_Else#2;

  inline$storm_IoCancelIrp$0$anon29_Else#2:
    assume __storm_init;
    goto inline$storm_IoCancelIrp$0$anon10#2;

  inline$storm_IoCancelIrp$0$anon29_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_IoCancelIrp$0$anon10#2;

  inline$storm_IoCancelIrp$0$anon10#2:
    call contextSwitch();
    goto inline$storm_IoCancelIrp$0$label_13#2;

  inline$storm_IoCancelIrp$0$label_13#2:
    havoc inline$storm_IoCancelIrp$0$myNondetVar_0;
    havoc inline$storm_IoCancelIrp$0$myNondetVar_1;
    assume inline$storm_IoCancelIrp$0$myNondetVar_0 == inline$storm_IoCancelIrp$0$myNondetVar_1;
    goto inline$storm_IoAcquireCancelSpinLock$0$Entry#2;

  inline$storm_IoAcquireCancelSpinLock$0$Entry#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$start#2;

  inline$storm_IoAcquireCancelSpinLock$0$start#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$label_3#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_3#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$label_4#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_4#2:
    goto inline$storm_getThreadID$2$Entry#2;

  inline$storm_getThreadID$2$Entry#2:
    goto inline$storm_getThreadID$2$anon0#2;

  inline$storm_getThreadID$2$anon0#2:
    inline$storm_getThreadID$2$tidRet := tid;
    goto inline$storm_getThreadID$2$Return#2;

  inline$storm_getThreadID$2$Return#2:
    inline$storm_IoAcquireCancelSpinLock$0$$result.storm_getThreadID$185.29$1$ := inline$storm_getThreadID$2$tidRet;
    goto inline$storm_IoAcquireCancelSpinLock$0$label_4$1#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_4$1#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$label_7#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_7#2:
    inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock := inline$storm_IoAcquireCancelSpinLock$0$$result.storm_getThreadID$185.29$1$;
    goto inline$storm_IoAcquireCancelSpinLock$0$label_8#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_8#2:
    __storm_atomic := true;
    goto inline$storm_IoAcquireCancelSpinLock$0$label_11#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_11#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$label_11_true#2, inline$storm_IoAcquireCancelSpinLock$0$label_11_false#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_11_false#2:
    assume k == 0 ==> !INT_NEQ(inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock, cancelLockStatus_0);
    assume k == 1 ==> !INT_NEQ(inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock, cancelLockStatus_1);
    call contextSwitch();
    goto inline$storm_IoAcquireCancelSpinLock$0$label_12#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_12#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoAcquireCancelSpinLock$0$label_1#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_11_true#2:
    assume k == 0 ==> INT_NEQ(inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock, cancelLockStatus_0);
    assume k == 1 ==> INT_NEQ(inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock, cancelLockStatus_1);
    call contextSwitch();
    goto inline$storm_IoAcquireCancelSpinLock$0$label_15#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_15#2:
    havoc raiseException;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon8_Then#2, inline$storm_IoAcquireCancelSpinLock$0$anon8_Else#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon2#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon2#2:
    assume k == 0 ==> INT_EQ(cancelLockStatus_0, 0);
    assume k == 1 ==> INT_EQ(cancelLockStatus_1, 0);
    call contextSwitch();
    goto inline$storm_IoAcquireCancelSpinLock$0$label_16#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_16#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$anon9_Then#2, inline$storm_IoAcquireCancelSpinLock$0$anon9_Else#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon9_Else#2:
    assume k != 0;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon10_Then#2, inline$storm_IoAcquireCancelSpinLock$0$anon10_Else#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon10_Else#2:
    assume k != 1;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon5#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon10_Then#2:
    assume k == 1;
    cancelLockStatus_1 := inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon5#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon9_Then#2:
    assume k == 0;
    cancelLockStatus_0 := inline$storm_IoAcquireCancelSpinLock$0$$tid$2$185.6$storm_IoAcquireCancelSpinLock;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon5#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon5#2:
    call contextSwitch();
    goto inline$storm_IoAcquireCancelSpinLock$0$label_17#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_17#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$anon11_Then#2, inline$storm_IoAcquireCancelSpinLock$0$anon11_Else#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon11_Else#2:
    assume __storm_init;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon7#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon11_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_IoAcquireCancelSpinLock$0$anon7#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon7#2:
    call contextSwitch();
    goto inline$storm_IoAcquireCancelSpinLock$0$label_1#2;

  inline$storm_IoAcquireCancelSpinLock$0$label_1#2:
    goto inline$storm_IoAcquireCancelSpinLock$0$Return#2;

  inline$storm_IoAcquireCancelSpinLock$0$anon8_Then#2:
    assume raiseException;
    goto inline$storm_IoAcquireCancelSpinLock$0$Return#2;

  inline$storm_IoAcquireCancelSpinLock$0$Return#2:
    goto inline$storm_IoCancelIrp$0$label_13$1#2;

  inline$storm_IoCancelIrp$0$label_13$1#2:
    goto inline$storm_IoCancelIrp$0$anon30_Then#2, inline$storm_IoCancelIrp$0$anon30_Else#2;

  inline$storm_IoCancelIrp$0$anon30_Else#2:
    assume !raiseException;
    goto inline$storm_IoCancelIrp$0$anon12#2;

  inline$storm_IoCancelIrp$0$anon12#2:
    havoc inline$storm_IoCancelIrp$0$myNondetVar_0;
    goto inline$storm_IoCancelIrp$0$label_16#2;

  inline$storm_IoCancelIrp$0$label_16#2:
    goto inline$storm_IoCancelIrp$0$label_16_true#2, inline$storm_IoCancelIrp$0$label_16_false#2;

  inline$storm_IoCancelIrp$0$label_16_false#2:
    assume inline$storm_IoCancelIrp$0$$oldCancelRoutine$2$352.17$storm_IoCancelIrp == 0;
    goto inline$storm_IoCancelIrp$0$label_17#2;

  inline$storm_IoCancelIrp$0$label_17#2:
    goto inline$storm_IoCancelIrp$0$label_1#2;

  inline$storm_IoCancelIrp$0$label_16_true#2:
    assume inline$storm_IoCancelIrp$0$$oldCancelRoutine$2$352.17$storm_IoCancelIrp != 0;
    goto inline$storm_IoCancelIrp$0$label_18#2;

  inline$storm_IoCancelIrp$0$label_18#2:
    goto inline$storm_IoCancelIrp$0$label_19#2;

  inline$storm_IoCancelIrp$0$label_19#2:
    call inline$storm_IoCancelIrp$0$$result.storm_nondet$365.4$2$ := storm_nondet();
    goto inline$storm_IoCancelIrp$0$label_22#2;

  inline$storm_IoCancelIrp$0$label_22#2:
    goto inline$storm_IoCancelIrp$0$label_22_true#2, inline$storm_IoCancelIrp$0$label_22_false#2;

  inline$storm_IoCancelIrp$0$label_22_false#2:
    assume inline$storm_IoCancelIrp$0$$result.storm_nondet$365.4$2$ == 0;
    goto inline$storm_IoCancelIrp$0$label_23#2;

  inline$storm_IoCancelIrp$0$label_22_true#2:
    assume inline$storm_IoCancelIrp$0$$result.storm_nondet$365.4$2$ != 0;
    goto inline$storm_IoCancelIrp$0$label_26#2;

  inline$storm_IoCancelIrp$0$label_26#2:
    havoc raiseException;
    goto inline$storm_IoCancelIrp$0$anon32_Then#2, inline$storm_IoCancelIrp$0$anon32_Else#2;

  inline$storm_IoCancelIrp$0$anon32_Else#2:
    assume !raiseException;
    goto inline$storm_IoCancelIrp$0$anon16#2;

  inline$storm_IoCancelIrp$0$anon16#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp], 1);
    call contextSwitch();
    goto inline$storm_IoCancelIrp$0$label_27#2;

  inline$storm_IoCancelIrp$0$label_27#2:
    goto inline$storm_IoCancelIrp$0$label_27_true#2, inline$storm_IoCancelIrp$0$label_27_false#2;

  inline$storm_IoCancelIrp$0$label_27_false#2:
    assume 0 == 0;
    goto inline$storm_IoCancelIrp$0$label_28#2;

  inline$storm_IoCancelIrp$0$label_28#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoCancelIrp$0$label_1#2;

  inline$storm_IoCancelIrp$0$label_27_true#2:
    assume 0 != 0;
    goto inline$storm_IoCancelIrp$0$label_23#2;

  inline$storm_IoCancelIrp$0$label_23#2:
    goto inline$IoGetCurrentIrpStackLocation$5$Entry#2;

  inline$IoGetCurrentIrpStackLocation$5$Entry#2:
    inline$IoGetCurrentIrpStackLocation$5$$Irp$1$23298.14$IoGetCurrentIrpStackLocation_.1 := inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp;
    goto inline$IoGetCurrentIrpStackLocation$5$start#2;

  inline$IoGetCurrentIrpStackLocation$5$start#2:
    inline$IoGetCurrentIrpStackLocation$5$$Irp$1$23298.14$IoGetCurrentIrpStackLocation := inline$IoGetCurrentIrpStackLocation$5$$Irp$1$23298.14$IoGetCurrentIrpStackLocation_.1;
    goto inline$IoGetCurrentIrpStackLocation$5$label_3#2;

  inline$IoGetCurrentIrpStackLocation$5$label_3#2:
    goto inline$IoGetCurrentIrpStackLocation$5$anon3_Then#2, inline$IoGetCurrentIrpStackLocation$5$anon3_Else#2;

  inline$IoGetCurrentIrpStackLocation$5$anon3_Else#2:
    assume k != 0;
    goto inline$IoGetCurrentIrpStackLocation$5$anon4_Then#2, inline$IoGetCurrentIrpStackLocation$5$anon4_Else#2;

  inline$IoGetCurrentIrpStackLocation$5$anon4_Else#2:
    assume k != 1;
    goto inline$IoGetCurrentIrpStackLocation$5$anon2#2;

  inline$IoGetCurrentIrpStackLocation$5$anon4_Then#2:
    assume k == 1;
    inline$IoGetCurrentIrpStackLocation$5$myVar_0 := Mem_1_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoGetCurrentIrpStackLocation$5$$Irp$1$23298.14$IoGetCurrentIrpStackLocation)))))];
    goto inline$IoGetCurrentIrpStackLocation$5$anon2#2;

  inline$IoGetCurrentIrpStackLocation$5$anon3_Then#2:
    assume k == 0;
    inline$IoGetCurrentIrpStackLocation$5$myVar_0 := Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23[CurrentStackLocation___unnamed_4_3c640f23(__unnamed_4_3c640f23___unnamed_12_41c62b26(__unnamed_12_41c62b26___unnamed_40_32307de2(Overlay___unnamed_48_e2bbfb0b(Tail__IRP(inline$IoGetCurrentIrpStackLocation$5$$Irp$1$23298.14$IoGetCurrentIrpStackLocation)))))];
    goto inline$IoGetCurrentIrpStackLocation$5$anon2#2;

  inline$IoGetCurrentIrpStackLocation$5$anon2#2:
    call contextSwitch();
    inline$IoGetCurrentIrpStackLocation$5$$result.IoGetCurrentIrpStackLocation$23297.0$1$ := inline$IoGetCurrentIrpStackLocation$5$myVar_0;
    goto inline$IoGetCurrentIrpStackLocation$5$label_1#2;

  inline$IoGetCurrentIrpStackLocation$5$label_1#2:
    goto inline$IoGetCurrentIrpStackLocation$5$Return#2;

  inline$IoGetCurrentIrpStackLocation$5$Return#2:
    inline$storm_IoCancelIrp$0$$result.IoGetCurrentIrpStackLocation$366.40$3$ := inline$IoGetCurrentIrpStackLocation$5$$result.IoGetCurrentIrpStackLocation$23297.0$1$;
    goto inline$storm_IoCancelIrp$0$label_23$1#2;

  inline$storm_IoCancelIrp$0$label_23$1#2:
    goto inline$storm_IoCancelIrp$0$anon31_Then#2, inline$storm_IoCancelIrp$0$anon31_Else#2;

  inline$storm_IoCancelIrp$0$anon31_Else#2:
    assume !raiseException;
    goto inline$storm_IoCancelIrp$0$anon14#2;

  inline$storm_IoCancelIrp$0$anon14#2:
    goto inline$storm_IoCancelIrp$0$label_31#2;

  inline$storm_IoCancelIrp$0$label_31#2:
    inline$storm_IoCancelIrp$0$$irpSp$3$364.23$storm_IoCancelIrp := inline$storm_IoCancelIrp$0$$result.IoGetCurrentIrpStackLocation$366.40$3$;
    goto inline$storm_IoCancelIrp$0$label_32#2;

  inline$storm_IoCancelIrp$0$label_32#2:
    goto inline$storm_IoCancelIrp$0$label_32_icall_1#2;

  inline$storm_IoCancelIrp$0$label_32_icall_1#2:
    assume inline$storm_IoCancelIrp$0$$oldCancelRoutine$2$352.17$storm_IoCancelIrp == I8xSysButtonCancelRoutine;
    goto inline$storm_IoCancelIrp$0$anon33_Then#2, inline$storm_IoCancelIrp$0$anon33_Else#2;

  inline$storm_IoCancelIrp$0$anon33_Else#2:
    assume k != 0;
    goto inline$storm_IoCancelIrp$0$anon34_Then#2, inline$storm_IoCancelIrp$0$anon34_Else#2;

  inline$storm_IoCancelIrp$0$anon34_Else#2:
    assume k != 1;
    goto inline$storm_IoCancelIrp$0$anon20#2;

  inline$storm_IoCancelIrp$0$anon34_Then#2:
    assume k == 1;
    inline$storm_IoCancelIrp$0$myVar_0 := Mem_1_T.DeviceObject__IO_STACK_LOCATION[DeviceObject__IO_STACK_LOCATION(inline$storm_IoCancelIrp$0$$irpSp$3$364.23$storm_IoCancelIrp)];
    goto inline$storm_IoCancelIrp$0$anon20#2;

  inline$storm_IoCancelIrp$0$anon33_Then#2:
    assume k == 0;
    inline$storm_IoCancelIrp$0$myVar_0 := Mem_0_T.DeviceObject__IO_STACK_LOCATION[DeviceObject__IO_STACK_LOCATION(inline$storm_IoCancelIrp$0$$irpSp$3$364.23$storm_IoCancelIrp)];
    goto inline$storm_IoCancelIrp$0$anon20#2;

  inline$storm_IoCancelIrp$0$anon20#2:
    call contextSwitch();
    goto inline$I8xSysButtonCancelRoutine$0$Entry#2;

  inline$I8xSysButtonCancelRoutine$0$Entry#2:
    inline$I8xSysButtonCancelRoutine$0$$DeviceObject$1$373.22$I8xSysButtonCancelRoutine_.1 := inline$storm_IoCancelIrp$0$myVar_0;
    inline$I8xSysButtonCancelRoutine$0$$Irp$2$374.12$I8xSysButtonCancelRoutine_.1 := inline$storm_IoCancelIrp$0$$Irp$1$349.10$storm_IoCancelIrp;
    goto inline$I8xSysButtonCancelRoutine$0$start#2;

  inline$I8xSysButtonCancelRoutine$0$start#2:
    call inline$I8xSysButtonCancelRoutine$0$$irql$5$379.10$I8xSysButtonCancelRoutine := __HAVOC_malloc(1);
    inline$I8xSysButtonCancelRoutine$0$$DeviceObject$1$373.22$I8xSysButtonCancelRoutine := inline$I8xSysButtonCancelRoutine$0$$DeviceObject$1$373.22$I8xSysButtonCancelRoutine_.1;
    inline$I8xSysButtonCancelRoutine$0$$Irp$2$374.12$I8xSysButtonCancelRoutine := inline$I8xSysButtonCancelRoutine$0$$Irp$2$374.12$I8xSysButtonCancelRoutine_.1;
    goto inline$I8xSysButtonCancelRoutine$0$label_3#2;

  inline$I8xSysButtonCancelRoutine$0$label_3#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_4#2;

  inline$I8xSysButtonCancelRoutine$0$label_4#2:
    goto inline$I8xSysButtonCancelRoutine$0$anon11_Then#2, inline$I8xSysButtonCancelRoutine$0$anon11_Else#2;

  inline$I8xSysButtonCancelRoutine$0$anon11_Else#2:
    assume k != 0;
    goto inline$I8xSysButtonCancelRoutine$0$anon12_Then#2, inline$I8xSysButtonCancelRoutine$0$anon12_Else#2;

  inline$I8xSysButtonCancelRoutine$0$anon12_Else#2:
    assume k != 1;
    goto inline$I8xSysButtonCancelRoutine$0$anon2#2;

  inline$I8xSysButtonCancelRoutine$0$anon12_Then#2:
    assume k == 1;
    inline$I8xSysButtonCancelRoutine$0$myVar_0 := Mem_1_T.DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(inline$I8xSysButtonCancelRoutine$0$$DeviceObject$1$373.22$I8xSysButtonCancelRoutine)];
    goto inline$I8xSysButtonCancelRoutine$0$anon2#2;

  inline$I8xSysButtonCancelRoutine$0$anon11_Then#2:
    assume k == 0;
    inline$I8xSysButtonCancelRoutine$0$myVar_0 := Mem_0_T.DeviceExtension__DEVICE_OBJECT[DeviceExtension__DEVICE_OBJECT(inline$I8xSysButtonCancelRoutine$0$$DeviceObject$1$373.22$I8xSysButtonCancelRoutine)];
    goto inline$I8xSysButtonCancelRoutine$0$anon2#2;

  inline$I8xSysButtonCancelRoutine$0$anon2#2:
    call contextSwitch();
    inline$I8xSysButtonCancelRoutine$0$$kbExtension$3$377.29$I8xSysButtonCancelRoutine := inline$I8xSysButtonCancelRoutine$0$myVar_0;
    goto inline$I8xSysButtonCancelRoutine$0$label_5#2;

  inline$I8xSysButtonCancelRoutine$0$label_5#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_6#2;

  inline$I8xSysButtonCancelRoutine$0$label_6#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_7#2;

  inline$I8xSysButtonCancelRoutine$0$label_7#2:
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_0;
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_1;
    assume inline$I8xSysButtonCancelRoutine$0$myNondetVar_0 == inline$I8xSysButtonCancelRoutine$0$myNondetVar_1;
    goto inline$storm_KeAcquireSpinLock$1$Entry#2;

  inline$storm_KeAcquireSpinLock$1$Entry#2:
    inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock_.1 := SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(inline$I8xSysButtonCancelRoutine$0$$kbExtension$3$377.29$I8xSysButtonCancelRoutine);
    goto inline$storm_KeAcquireSpinLock$1$start#2;

  inline$storm_KeAcquireSpinLock$1$start#2:
    inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock_.1;
    goto inline$storm_KeAcquireSpinLock$1$label_3#2;

  inline$storm_KeAcquireSpinLock$1$label_3#2:
    goto inline$storm_KeAcquireSpinLock$1$label_4#2;

  inline$storm_KeAcquireSpinLock$1$label_4#2:
    goto inline$storm_getThreadID$3$Entry#2;

  inline$storm_getThreadID$3$Entry#2:
    goto inline$storm_getThreadID$3$anon0#2;

  inline$storm_getThreadID$3$anon0#2:
    inline$storm_getThreadID$3$tidRet := tid;
    goto inline$storm_getThreadID$3$Return#2;

  inline$storm_getThreadID$3$Return#2:
    inline$storm_KeAcquireSpinLock$1$$result.storm_getThreadID$128.29$1$ := inline$storm_getThreadID$3$tidRet;
    goto inline$storm_KeAcquireSpinLock$1$label_4$1#2;

  inline$storm_KeAcquireSpinLock$1$label_4$1#2:
    goto inline$storm_KeAcquireSpinLock$1$label_7#2;

  inline$storm_KeAcquireSpinLock$1$label_7#2:
    inline$storm_KeAcquireSpinLock$1$$tid$3$128.6$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$1$$result.storm_getThreadID$128.29$1$;
    goto inline$storm_KeAcquireSpinLock$1$label_8#2;

  inline$storm_KeAcquireSpinLock$1$label_8#2:
    goto inline$storm_KeAcquireSpinLock$1$label_9#2;

  inline$storm_KeAcquireSpinLock$1$label_9#2:
    __storm_atomic := true;
    goto inline$storm_KeAcquireSpinLock$1$label_12#2;

  inline$storm_KeAcquireSpinLock$1$label_12#2:
    havoc raiseException;
    goto inline$storm_KeAcquireSpinLock$1$anon10_Then#2, inline$storm_KeAcquireSpinLock$1$anon10_Else#2;

  inline$storm_KeAcquireSpinLock$1$anon10_Else#2:
    assume !raiseException;
    goto inline$storm_KeAcquireSpinLock$1$anon1#2;

  inline$storm_KeAcquireSpinLock$1$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_LOCK[inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock], inline$storm_KeAcquireSpinLock$1$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    assume k == 1 ==> INT_EQ(Res_1_LOCK[inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock], inline$storm_KeAcquireSpinLock$1$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    call contextSwitch();
    goto inline$storm_KeAcquireSpinLock$1$label_13#2;

  inline$storm_KeAcquireSpinLock$1$label_13#2:
    goto inline$storm_KeAcquireSpinLock$1$label_13_true#2, inline$storm_KeAcquireSpinLock$1$label_13_false#2;

  inline$storm_KeAcquireSpinLock$1$label_13_false#2:
    assume !INT_NEQ(inline$storm_KeAcquireSpinLock$1$$tid$3$128.6$storm_KeAcquireSpinLock, inline$storm_KeAcquireSpinLock$1$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    goto inline$storm_KeAcquireSpinLock$1$label_14#2;

  inline$storm_KeAcquireSpinLock$1$label_14#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_KeAcquireSpinLock$1$label_1#2;

  inline$storm_KeAcquireSpinLock$1$label_13_true#2:
    assume INT_NEQ(inline$storm_KeAcquireSpinLock$1$$tid$3$128.6$storm_KeAcquireSpinLock, inline$storm_KeAcquireSpinLock$1$$lockStatus$4$129.6$storm_KeAcquireSpinLock);
    goto inline$storm_KeAcquireSpinLock$1$label_17#2;

  inline$storm_KeAcquireSpinLock$1$label_17#2:
    havoc raiseException;
    goto inline$storm_KeAcquireSpinLock$1$anon11_Then#2, inline$storm_KeAcquireSpinLock$1$anon11_Else#2;

  inline$storm_KeAcquireSpinLock$1$anon11_Else#2:
    assume !raiseException;
    goto inline$storm_KeAcquireSpinLock$1$anon4#2;

  inline$storm_KeAcquireSpinLock$1$anon4#2:
    assume INT_EQ(inline$storm_KeAcquireSpinLock$1$$lockStatus$4$129.6$storm_KeAcquireSpinLock, 0);
    goto inline$storm_KeAcquireSpinLock$1$label_18#2;

  inline$storm_KeAcquireSpinLock$1$label_18#2:
    goto inline$storm_KeAcquireSpinLock$1$anon12_Then#2, inline$storm_KeAcquireSpinLock$1$anon12_Else#2;

  inline$storm_KeAcquireSpinLock$1$anon12_Else#2:
    assume k != 0;
    goto inline$storm_KeAcquireSpinLock$1$anon13_Then#2, inline$storm_KeAcquireSpinLock$1$anon13_Else#2;

  inline$storm_KeAcquireSpinLock$1$anon13_Else#2:
    assume k != 1;
    goto inline$storm_KeAcquireSpinLock$1$anon7#2;

  inline$storm_KeAcquireSpinLock$1$anon13_Then#2:
    assume k == 1;
    Res_1_LOCK := Res_1_LOCK[inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$1$$tid$3$128.6$storm_KeAcquireSpinLock];
    goto inline$storm_KeAcquireSpinLock$1$anon7#2;

  inline$storm_KeAcquireSpinLock$1$anon12_Then#2:
    assume k == 0;
    Res_0_LOCK := Res_0_LOCK[inline$storm_KeAcquireSpinLock$1$$SpinLock$1$124.17$storm_KeAcquireSpinLock := inline$storm_KeAcquireSpinLock$1$$tid$3$128.6$storm_KeAcquireSpinLock];
    goto inline$storm_KeAcquireSpinLock$1$anon7#2;

  inline$storm_KeAcquireSpinLock$1$anon7#2:
    call contextSwitch();
    goto inline$storm_KeAcquireSpinLock$1$label_19#2;

  inline$storm_KeAcquireSpinLock$1$label_19#2:
    goto inline$storm_KeAcquireSpinLock$1$anon14_Then#2, inline$storm_KeAcquireSpinLock$1$anon14_Else#2;

  inline$storm_KeAcquireSpinLock$1$anon14_Else#2:
    assume __storm_init;
    goto inline$storm_KeAcquireSpinLock$1$anon9#2;

  inline$storm_KeAcquireSpinLock$1$anon14_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_KeAcquireSpinLock$1$anon9#2;

  inline$storm_KeAcquireSpinLock$1$anon9#2:
    call contextSwitch();
    goto inline$storm_KeAcquireSpinLock$1$label_1#2;

  inline$storm_KeAcquireSpinLock$1$label_1#2:
    goto inline$storm_KeAcquireSpinLock$1$Return#2;

  inline$storm_KeAcquireSpinLock$1$anon11_Then#2:
    assume raiseException;
    goto inline$storm_KeAcquireSpinLock$1$Return#2;

  inline$storm_KeAcquireSpinLock$1$anon10_Then#2:
    assume raiseException;
    goto inline$storm_KeAcquireSpinLock$1$Return#2;

  inline$storm_KeAcquireSpinLock$1$Return#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_7$1#2;

  inline$I8xSysButtonCancelRoutine$0$label_7$1#2:
    goto inline$I8xSysButtonCancelRoutine$0$anon13_Then#2, inline$I8xSysButtonCancelRoutine$0$anon13_Else#2;

  inline$I8xSysButtonCancelRoutine$0$anon13_Else#2:
    assume !raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$anon4#2;

  inline$I8xSysButtonCancelRoutine$0$anon4#2:
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_0;
    goto inline$I8xSysButtonCancelRoutine$0$label_10#2;

  inline$I8xSysButtonCancelRoutine$0$label_10#2:
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_0;
    goto inline$I8xSysButtonCancelRoutine$0$label_11#2;

  inline$I8xSysButtonCancelRoutine$0$label_11#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_12#2;

  inline$I8xSysButtonCancelRoutine$0$label_12#2:
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_0;
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_1;
    assume inline$I8xSysButtonCancelRoutine$0$myNondetVar_0 == inline$I8xSysButtonCancelRoutine$0$myNondetVar_1;
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_0;
    goto inline$storm_KeReleaseSpinLock$1$Entry#2;

  inline$storm_KeReleaseSpinLock$1$Entry#2:
    inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock_.1 := SysButtonSpinLock__PORT_KEYBOARD_EXTENSION(inline$I8xSysButtonCancelRoutine$0$$kbExtension$3$377.29$I8xSysButtonCancelRoutine);
    goto inline$storm_KeReleaseSpinLock$1$start#2;

  inline$storm_KeReleaseSpinLock$1$start#2:
    inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock := inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock_.1;
    goto inline$storm_KeReleaseSpinLock$1$label_3#2;

  inline$storm_KeReleaseSpinLock$1$label_3#2:
    goto inline$storm_KeReleaseSpinLock$1$label_4#2;

  inline$storm_KeReleaseSpinLock$1$label_4#2:
    __storm_atomic := true;
    goto inline$storm_KeReleaseSpinLock$1$label_7#2;

  inline$storm_KeReleaseSpinLock$1$label_7#2:
    havoc raiseException;
    goto inline$storm_KeReleaseSpinLock$1$anon8_Then#2, inline$storm_KeReleaseSpinLock$1$anon8_Else#2;

  inline$storm_KeReleaseSpinLock$1$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_KeReleaseSpinLock$1$anon1#2;

  inline$storm_KeReleaseSpinLock$1$anon1#2:
    assume k == 0 ==> INT_EQ(Res_0_LOCK[inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock], inline$storm_KeReleaseSpinLock$1$$lockStatus$3$144.6$storm_KeReleaseSpinLock);
    assume k == 1 ==> INT_EQ(Res_1_LOCK[inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock], inline$storm_KeReleaseSpinLock$1$$lockStatus$3$144.6$storm_KeReleaseSpinLock);
    call contextSwitch();
    goto inline$storm_KeReleaseSpinLock$1$label_8#2;

  inline$storm_KeReleaseSpinLock$1$label_8#2:
    goto inline$storm_getThreadID$4$Entry#2;

  inline$storm_getThreadID$4$Entry#2:
    goto inline$storm_getThreadID$4$anon0#2;

  inline$storm_getThreadID$4$anon0#2:
    inline$storm_getThreadID$4$tidRet := tid;
    goto inline$storm_getThreadID$4$Return#2;

  inline$storm_getThreadID$4$Return#2:
    inline$storm_KeReleaseSpinLock$1$$result.storm_getThreadID$145.0$1$ := inline$storm_getThreadID$4$tidRet;
    goto inline$storm_KeReleaseSpinLock$1$label_8$1#2;

  inline$storm_KeReleaseSpinLock$1$label_8$1#2:
    goto inline$storm_KeReleaseSpinLock$1$label_11#2;

  inline$storm_KeReleaseSpinLock$1$label_11#2:
    goto inline$storm_KeReleaseSpinLock$1$label_11_true#2, inline$storm_KeReleaseSpinLock$1$label_11_false#2;

  inline$storm_KeReleaseSpinLock$1$label_11_false#2:
    assume !INT_EQ(inline$storm_KeReleaseSpinLock$1$$lockStatus$3$144.6$storm_KeReleaseSpinLock, inline$storm_KeReleaseSpinLock$1$$result.storm_getThreadID$145.0$1$);
    goto inline$storm_KeReleaseSpinLock$1$label_12#2;

  inline$storm_KeReleaseSpinLock$1$label_12#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_KeReleaseSpinLock$1$label_1#2;

  inline$storm_KeReleaseSpinLock$1$label_11_true#2:
    assume INT_EQ(inline$storm_KeReleaseSpinLock$1$$lockStatus$3$144.6$storm_KeReleaseSpinLock, inline$storm_KeReleaseSpinLock$1$$result.storm_getThreadID$145.0$1$);
    goto inline$storm_KeReleaseSpinLock$1$label_15#2;

  inline$storm_KeReleaseSpinLock$1$label_15#2:
    goto inline$storm_KeReleaseSpinLock$1$anon9_Then#2, inline$storm_KeReleaseSpinLock$1$anon9_Else#2;

  inline$storm_KeReleaseSpinLock$1$anon9_Else#2:
    assume k != 0;
    goto inline$storm_KeReleaseSpinLock$1$anon10_Then#2, inline$storm_KeReleaseSpinLock$1$anon10_Else#2;

  inline$storm_KeReleaseSpinLock$1$anon10_Else#2:
    assume k != 1;
    goto inline$storm_KeReleaseSpinLock$1$anon5#2;

  inline$storm_KeReleaseSpinLock$1$anon10_Then#2:
    assume k == 1;
    Res_1_LOCK := Res_1_LOCK[inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock := 0];
    goto inline$storm_KeReleaseSpinLock$1$anon5#2;

  inline$storm_KeReleaseSpinLock$1$anon9_Then#2:
    assume k == 0;
    Res_0_LOCK := Res_0_LOCK[inline$storm_KeReleaseSpinLock$1$$SpinLock$1$140.17$storm_KeReleaseSpinLock := 0];
    goto inline$storm_KeReleaseSpinLock$1$anon5#2;

  inline$storm_KeReleaseSpinLock$1$anon5#2:
    call contextSwitch();
    goto inline$storm_KeReleaseSpinLock$1$label_16#2;

  inline$storm_KeReleaseSpinLock$1$label_16#2:
    goto inline$storm_KeReleaseSpinLock$1$anon11_Then#2, inline$storm_KeReleaseSpinLock$1$anon11_Else#2;

  inline$storm_KeReleaseSpinLock$1$anon11_Else#2:
    assume __storm_init;
    goto inline$storm_KeReleaseSpinLock$1$anon7#2;

  inline$storm_KeReleaseSpinLock$1$anon11_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_KeReleaseSpinLock$1$anon7#2;

  inline$storm_KeReleaseSpinLock$1$anon7#2:
    call contextSwitch();
    goto inline$storm_KeReleaseSpinLock$1$label_1#2;

  inline$storm_KeReleaseSpinLock$1$label_1#2:
    goto inline$storm_KeReleaseSpinLock$1$Return#2;

  inline$storm_KeReleaseSpinLock$1$anon8_Then#2:
    assume raiseException;
    goto inline$storm_KeReleaseSpinLock$1$Return#2;

  inline$storm_KeReleaseSpinLock$1$Return#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_12$1#2;

  inline$I8xSysButtonCancelRoutine$0$label_12$1#2:
    goto inline$I8xSysButtonCancelRoutine$0$anon14_Then#2, inline$I8xSysButtonCancelRoutine$0$anon14_Else#2;

  inline$I8xSysButtonCancelRoutine$0$anon14_Else#2:
    assume !raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$anon6#2;

  inline$I8xSysButtonCancelRoutine$0$anon6#2:
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_0;
    goto inline$I8xSysButtonCancelRoutine$0$label_15#2;

  inline$I8xSysButtonCancelRoutine$0$label_15#2:
    havoc inline$I8xSysButtonCancelRoutine$0$myNondetVar_0;
    goto inline$storm_IoReleaseCancelSpinLock$0$Entry#2;

  inline$storm_IoReleaseCancelSpinLock$0$Entry#2:
    goto inline$storm_IoReleaseCancelSpinLock$0$start#2;

  inline$storm_IoReleaseCancelSpinLock$0$start#2:
    goto inline$storm_IoReleaseCancelSpinLock$0$label_3#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_3#2:
    __storm_atomic := true;
    goto inline$storm_IoReleaseCancelSpinLock$0$label_6#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_6#2:
    goto inline$storm_getThreadID$5$Entry#2;

  inline$storm_getThreadID$5$Entry#2:
    goto inline$storm_getThreadID$5$anon0#2;

  inline$storm_getThreadID$5$anon0#2:
    inline$storm_getThreadID$5$tidRet := tid;
    goto inline$storm_getThreadID$5$Return#2;

  inline$storm_getThreadID$5$Return#2:
    inline$storm_IoReleaseCancelSpinLock$0$$result.storm_getThreadID$198.0$1$ := inline$storm_getThreadID$5$tidRet;
    goto inline$storm_IoReleaseCancelSpinLock$0$label_6$1#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_6$1#2:
    goto inline$storm_IoReleaseCancelSpinLock$0$label_9#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_9#2:
    goto inline$storm_IoReleaseCancelSpinLock$0$label_9_true#2, inline$storm_IoReleaseCancelSpinLock$0$label_9_false#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_9_false#2:
    assume k == 0 ==> !INT_EQ(cancelLockStatus_0, inline$storm_IoReleaseCancelSpinLock$0$$result.storm_getThreadID$198.0$1$);
    assume k == 1 ==> !INT_EQ(cancelLockStatus_1, inline$storm_IoReleaseCancelSpinLock$0$$result.storm_getThreadID$198.0$1$);
    call contextSwitch();
    goto inline$storm_IoReleaseCancelSpinLock$0$label_10#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_10#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoReleaseCancelSpinLock$0$label_1#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_9_true#2:
    assume k == 0 ==> INT_EQ(cancelLockStatus_0, inline$storm_IoReleaseCancelSpinLock$0$$result.storm_getThreadID$198.0$1$);
    assume k == 1 ==> INT_EQ(cancelLockStatus_1, inline$storm_IoReleaseCancelSpinLock$0$$result.storm_getThreadID$198.0$1$);
    call contextSwitch();
    goto inline$storm_IoReleaseCancelSpinLock$0$label_13#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_13#2:
    goto inline$storm_IoReleaseCancelSpinLock$0$anon6_Then#2, inline$storm_IoReleaseCancelSpinLock$0$anon6_Else#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon6_Else#2:
    assume k != 0;
    goto inline$storm_IoReleaseCancelSpinLock$0$anon7_Then#2, inline$storm_IoReleaseCancelSpinLock$0$anon7_Else#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon7_Else#2:
    assume k != 1;
    goto inline$storm_IoReleaseCancelSpinLock$0$anon3#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon7_Then#2:
    assume k == 1;
    cancelLockStatus_1 := 0;
    goto inline$storm_IoReleaseCancelSpinLock$0$anon3#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon6_Then#2:
    assume k == 0;
    cancelLockStatus_0 := 0;
    goto inline$storm_IoReleaseCancelSpinLock$0$anon3#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon3#2:
    call contextSwitch();
    goto inline$storm_IoReleaseCancelSpinLock$0$label_14#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_14#2:
    goto inline$storm_IoReleaseCancelSpinLock$0$anon8_Then#2, inline$storm_IoReleaseCancelSpinLock$0$anon8_Else#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon8_Else#2:
    assume __storm_init;
    goto inline$storm_IoReleaseCancelSpinLock$0$anon5#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon8_Then#2:
    assume !__storm_init;
    __storm_atomic := false;
    goto inline$storm_IoReleaseCancelSpinLock$0$anon5#2;

  inline$storm_IoReleaseCancelSpinLock$0$anon5#2:
    call contextSwitch();
    goto inline$storm_IoReleaseCancelSpinLock$0$label_1#2;

  inline$storm_IoReleaseCancelSpinLock$0$label_1#2:
    goto inline$storm_IoReleaseCancelSpinLock$0$Return#2;

  inline$storm_IoReleaseCancelSpinLock$0$Return#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_15$1#2;

  inline$I8xSysButtonCancelRoutine$0$label_15$1#2:
    goto inline$I8xSysButtonCancelRoutine$0$anon15_Then#2, inline$I8xSysButtonCancelRoutine$0$anon15_Else#2;

  inline$I8xSysButtonCancelRoutine$0$anon15_Else#2:
    assume !raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$anon8#2;

  inline$I8xSysButtonCancelRoutine$0$anon8#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_18#2;

  inline$I8xSysButtonCancelRoutine$0$label_18#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_19#2;

  inline$I8xSysButtonCancelRoutine$0$label_19#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_20#2;

  inline$I8xSysButtonCancelRoutine$0$label_20#2:
    goto inline$storm_IoCompleteRequest$4$Entry#2;

  inline$storm_IoCompleteRequest$4$Entry#2:
    inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest_.1 := inline$I8xSysButtonCancelRoutine$0$$Irp$2$374.12$I8xSysButtonCancelRoutine;
    goto inline$storm_IoCompleteRequest$4$start#2;

  inline$storm_IoCompleteRequest$4$start#2:
    inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest := inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest_.1;
    goto inline$storm_IoCompleteRequest$4$label_3#2;

  inline$storm_IoCompleteRequest$4$label_3#2:
    call inline$storm_IoCompleteRequest$4$$result.storm_nondet$343.2$1$ := storm_nondet();
    goto inline$storm_IoCompleteRequest$4$label_6#2;

  inline$storm_IoCompleteRequest$4$label_6#2:
    goto inline$storm_IoCompleteRequest$4$label_6_true#2, inline$storm_IoCompleteRequest$4$label_6_false#2;

  inline$storm_IoCompleteRequest$4$label_6_false#2:
    assume inline$storm_IoCompleteRequest$4$$result.storm_nondet$343.2$1$ == 0;
    goto inline$storm_IoCompleteRequest$4$label_7#2;

  inline$storm_IoCompleteRequest$4$label_6_true#2:
    assume inline$storm_IoCompleteRequest$4$$result.storm_nondet$343.2$1$ != 0;
    goto inline$storm_IoCompleteRequest$4$label_8#2;

  inline$storm_IoCompleteRequest$4$label_8#2:
    havoc raiseException;
    goto inline$storm_IoCompleteRequest$4$anon8_Then#2, inline$storm_IoCompleteRequest$4$anon8_Else#2;

  inline$storm_IoCompleteRequest$4$anon8_Else#2:
    assume !raiseException;
    goto inline$storm_IoCompleteRequest$4$anon4#2;

  inline$storm_IoCompleteRequest$4$anon4#2:
    assume k == 0 ==> INT_EQ(Res_0_COMPLETED[inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    assume k == 1 ==> INT_EQ(Res_1_COMPLETED[inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest], 1);
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$4$label_9#2;

  inline$storm_IoCompleteRequest$4$label_9#2:
    goto inline$storm_IoCompleteRequest$4$label_9_true#2, inline$storm_IoCompleteRequest$4$label_9_false#2;

  inline$storm_IoCompleteRequest$4$label_9_false#2:
    assume 0 == 0;
    goto inline$storm_IoCompleteRequest$4$label_10#2;

  inline$storm_IoCompleteRequest$4$label_10#2:
    errorReached := true;
    raiseException := true;
    __storm_atomic := false;
    __storm_init := false;
    goto inline$storm_IoCompleteRequest$4$label_1#2;

  inline$storm_IoCompleteRequest$4$label_9_true#2:
    assume 0 != 0;
    goto inline$storm_IoCompleteRequest$4$label_7#2;

  inline$storm_IoCompleteRequest$4$label_7#2:
    goto inline$storm_IoCompleteRequest$4$anon6_Then#2, inline$storm_IoCompleteRequest$4$anon6_Else#2;

  inline$storm_IoCompleteRequest$4$anon6_Else#2:
    assume k != 0;
    goto inline$storm_IoCompleteRequest$4$anon7_Then#2, inline$storm_IoCompleteRequest$4$anon7_Else#2;

  inline$storm_IoCompleteRequest$4$anon7_Else#2:
    assume k != 1;
    goto inline$storm_IoCompleteRequest$4$anon2#2;

  inline$storm_IoCompleteRequest$4$anon7_Then#2:
    assume k == 1;
    Res_1_COMPLETED := Res_1_COMPLETED[inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$4$anon2#2;

  inline$storm_IoCompleteRequest$4$anon6_Then#2:
    assume k == 0;
    Res_0_COMPLETED := Res_0_COMPLETED[inline$storm_IoCompleteRequest$4$$pirp$1$339.10$storm_IoCompleteRequest := 1];
    goto inline$storm_IoCompleteRequest$4$anon2#2;

  inline$storm_IoCompleteRequest$4$anon2#2:
    call contextSwitch();
    goto inline$storm_IoCompleteRequest$4$label_1#2;

  inline$storm_IoCompleteRequest$4$label_1#2:
    goto inline$storm_IoCompleteRequest$4$Return#2;

  inline$storm_IoCompleteRequest$4$anon8_Then#2:
    assume raiseException;
    goto inline$storm_IoCompleteRequest$4$Return#2;

  inline$storm_IoCompleteRequest$4$Return#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_20$1#2;

  inline$I8xSysButtonCancelRoutine$0$label_20$1#2:
    goto inline$I8xSysButtonCancelRoutine$0$anon16_Then#2, inline$I8xSysButtonCancelRoutine$0$anon16_Else#2;

  inline$I8xSysButtonCancelRoutine$0$anon16_Else#2:
    assume !raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$anon10#2;

  inline$I8xSysButtonCancelRoutine$0$anon10#2:
    goto inline$I8xSysButtonCancelRoutine$0$label_1#2;

  inline$I8xSysButtonCancelRoutine$0$label_1#2:
    call __HAVOC_free(inline$I8xSysButtonCancelRoutine$0$$irql$5$379.10$I8xSysButtonCancelRoutine);
    goto inline$I8xSysButtonCancelRoutine$0$Return#2;

  inline$I8xSysButtonCancelRoutine$0$anon16_Then#2:
    assume raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$Return#2;

  inline$I8xSysButtonCancelRoutine$0$anon15_Then#2:
    assume raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$Return#2;

  inline$I8xSysButtonCancelRoutine$0$anon14_Then#2:
    assume raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$Return#2;

  inline$I8xSysButtonCancelRoutine$0$anon13_Then#2:
    assume raiseException;
    goto inline$I8xSysButtonCancelRoutine$0$Return#2;

  inline$I8xSysButtonCancelRoutine$0$Return#2:
    goto inline$storm_IoCancelIrp$0$anon20$1#2;

  inline$storm_IoCancelIrp$0$anon20$1#2:
    goto inline$storm_IoCancelIrp$0$anon35_Then#2, inline$storm_IoCancelIrp$0$anon35_Else#2;

  inline$storm_IoCancelIrp$0$anon35_Else#2:
    assume !raiseException;
    goto inline$storm_IoCancelIrp$0$anon22#2;

  inline$storm_IoCancelIrp$0$anon22#2:
    goto inline$storm_IoCancelIrp$0$label_32_icall_return#2;

  inline$storm_IoCancelIrp$0$label_32_icall_return#2:
    goto inline$storm_IoCancelIrp$0$label_35#2;

  inline$storm_IoCancelIrp$0$label_35#2:
    goto inline$storm_IoCancelIrp$0$label_1#2;

  inline$storm_IoCancelIrp$0$label_1#2:
    goto inline$storm_IoCancelIrp$0$Return#2;

  inline$storm_IoCancelIrp$0$anon35_Then#2:
    assume raiseException;
    goto inline$storm_IoCancelIrp$0$Return#2;

  inline$storm_IoCancelIrp$0$anon31_Then#2:
    assume raiseException;
    goto inline$storm_IoCancelIrp$0$Return#2;

  inline$storm_IoCancelIrp$0$anon32_Then#2:
    assume raiseException;
    goto inline$storm_IoCancelIrp$0$Return#2;

  inline$storm_IoCancelIrp$0$anon30_Then#2:
    assume raiseException;
    goto inline$storm_IoCancelIrp$0$Return#2;

  inline$storm_IoCancelIrp$0$Return#2:
    goto inline$cancel$0$label_3$1#2;

  inline$cancel$0$label_3$1#2:
    goto inline$cancel$0$anon2_Then#2, inline$cancel$0$anon2_Else#2;

  inline$cancel$0$anon2_Else#2:
    assume !raiseException;
    goto inline$cancel$0$anon1#2;

  inline$cancel$0$anon1#2:
    goto inline$cancel$0$label_1#2;

  inline$cancel$0$label_1#2:
    goto inline$cancel$0$Return#2;

  inline$cancel$0$anon2_Then#2:
    assume raiseException;
    goto inline$cancel$0$Return#2;

  inline$cancel$0$Return#2:
    goto label_27$1#2;

  label_27$1#2:
    goto anon32_Then#2, anon32_Else#2;

  anon32_Else#2:
    assume !(errorReached || !raiseException);
    goto anon19#2;

  anon32_Then#2:
    assume errorReached || !raiseException;
    __storm_thread_done_2 := true;
    goto anon19#2;

  anon19#2:
    k := k_old_1;
    tid := tid_old_1;
    goto label_30#2;

  label_30#2:
    goto label_31#2;

  label_31#2:
    k_old_2 := k;
    tid_old_2 := tid;
    tidCount_old := tidCount;
    havoc tidCount;
    assume tidCount_old < tidCount;
    tid := tidCount;
    raiseException := false;
    call contextSwitch();
    goto inline$dpc$0$Entry#2;

  inline$dpc$0$Entry#2:
    goto inline$dpc$0$start#2;

  inline$dpc$0$start#2:
    goto inline$dpc$0$label_1#2;

  inline$dpc$0$label_1#2:
    goto inline$dpc$0$Return#2;

  inline$dpc$0$Return#2:
    goto label_31$1#2;

  label_31$1#2:
    goto anon33_Then#2, anon33_Else#2;

  anon33_Else#2:
    assume !(errorReached || !raiseException);
    goto anon21#2;

  anon33_Then#2:
    assume errorReached || !raiseException;
    __storm_thread_done_3 := true;
    goto anon21#2;

  anon21#2:
    k := k_old_2;
    tid := tid_old_2;
    goto label_1#2;

  label_1#2:
    assume Mem_0_T.CancelRoutine__IRP == Mem_s_1_T.CancelRoutine__IRP;
    assume Mem_0_T.Cancel__IRP == Mem_s_1_T.Cancel__IRP;
    assume Mem_0_T.CurrentStackLocation___unnamed_4_3c640f23 == Mem_s_1_T.CurrentStackLocation___unnamed_4_3c640f23;
    assume Mem_0_T.DeviceExtension__DEVICE_OBJECT == Mem_s_1_T.DeviceExtension__DEVICE_OBJECT;
    assume Mem_0_T.DeviceObject__IO_STACK_LOCATION == Mem_s_1_T.DeviceObject__IO_STACK_LOCATION;
    assume cancelLockStatus_0 == cancelLockStatus_s_1;
    assume Res_0_COMPLETED == Res_s_1_COMPLETED;
    assume Res_0_LOCK == Res_s_1_LOCK;
    assert !errorReached;
    return;

  anon30_Then#2:
    assume raiseException;
    return;

  anon27_Then#2:
    assume raiseException;
    return;

  anon26_Then#2:
    assume raiseException;
    return;

  anon25_Then#2:
    assume raiseException;
    return;

  anon24_Then#2:
    assume raiseException;
    return;
}



