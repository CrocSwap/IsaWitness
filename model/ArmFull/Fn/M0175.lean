module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0010
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0037
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0060
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0172 set_option backward.proofsInPublic true @[expose] public section

set_option maxHeartbeats 1_000_000_000
set_option maxRecDepth 1_000_000
set_option linter.unusedVariables false
set_option match.ignoreUnusedAlts true

open Sail
open Sail.ConcurrencyInterfaceV1

namespace ArmFull

variable {real : Type} [Sail.SailReal real]

open ConcurrencyInterfaceV1

namespace Functions

open signal
open option
open exception
open arm_acc_type
open __InstrEnc
open WFxType
open VFPNegMul
open VCGTtype
open VCGEType
open VBitOps
open VBitOp
open VARange
open Unpredictable
open TranslationStage
open TimeStamp
open TMFailure
open TLBIOp
open TLBIMemAttr
open TLBILevel
open TGx
open SystemHintOp
open Signal
open ShiftType
open Shareability
open SecurityState
open SVECmp
open SRType
open SMEExceptionType
open SDFType
open RestrictType
open Register
open Regime
open ReduceOp
open PrivilegeLevel
open PrefetchHint
open PSTATEField
open PGSe
open PASpace
open PARTIDspaceType
open OpType
open MoveWideOp
open MemType
open MemTagType
open MemOp
open MemAtomicOp
open MOPSStage
open MBReqTypes
open MBReqDomain
open LogicalOp
open InterruptID
open InstrSet
open ImmediateOp
open GPCF
open GCSInstruction
open Feature
open Fault
open FPUnaryOp
open FPType
open FPRounding
open FPMaxMinOp
open FPExc
open FPConvOp
open ExtendType
open ExceptionalOccurrenceTargetState
open Exception
open ErrorState
open DeviceType
open DescriptorType
open DSBAlias
open CrossTriggerIn
open CountOp
open Constraint
open CompareOp
open CacheType
open CachePASpace
open CacheOpScope
open CacheOp
open BranchType
open BarrierExt
open Barrier
open ArchVersion
open AccessType
open ATAccess

def DebugWriteExternalAbort (memstatus : PhysMemRetStatus) (addrdesc : AddressDescriptor) (start_vaddr : (BitVec 64)) : SailM Unit := do
  let iswrite : Bool := true
  let handle_as_SError : Bool := false
  let async_external_abort : Bool := false
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 2437) 64) ) : SailM (BitVec 64) )
  let (async_external_abort, handle_as_SError, syndrome) ← (( do
    match addrdesc.fault.access.acctype with
    | .AccessType_SPE =>
      (do
        let w__0 ← (( do (__IMPDEF_boolean "SPE SyncExternal as SError") ) : SailM Bool )
        let handle_as_SError := (w__0 : Bool)
        let w__1 ← (( do (__IMPDEF_boolean "SPE async External abort") ) : SailM Bool )
        let async_external_abort := (w__1 : Bool)
        let w__2 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
        let syndrome := ((Sail.BitVec.extractLsb w__2 63 0) : (BitVec 64))
        (pure ((async_external_abort, handle_as_SError, syndrome))))
    | _ =>
      (do
        (Unreachable ())
        (pure ((async_external_abort, handle_as_SError, syndrome)))) ) : SailM
    (Bool × Bool × (BitVec 64)) )
  let ttw_abort : Bool :=
    ((BEq.beq addrdesc.fault.statuscode Fault_SyncExternalOnWalk) || (BEq.beq
        addrdesc.fault.statuscode Fault_SyncParityOnWalk))
  let statuscode : Fault :=
    if (ttw_abort : Bool)
    then addrdesc.fault.statuscode
    else memstatus.statuscode
  let extflag : (BitVec 1) :=
    if (ttw_abort : Bool)
    then addrdesc.fault.extflag
    else memstatus.extflag
  if ((((BEq.beq statuscode Fault_AsyncExternal) || (BEq.beq statuscode Fault_AsyncParity)) || handle_as_SError) : Bool)
  then
    (do
      let fault ← (( do (NoFault ()) ) : SailM FaultRecord )
      let parity : Bool :=
        ((BEq.beq statuscode Fault_SyncParity) || ((BEq.beq statuscode Fault_AsyncParity) || (BEq.beq
              statuscode Fault_SyncParityOnWalk)))
      let fault : FaultRecord :=
        { fault with statuscode := if (parity : Bool)
          then Fault_AsyncParity
          else Fault_AsyncExternal }
      let w__3 ← (( do (HaveRASExt ()) ) : SailM Bool )
      let fault : FaultRecord :=
        if (w__3 : Bool)
        then { fault with merrorstate := memstatus.merrorstate }
        else fault
      let fault : FaultRecord := { fault with extflag := extflag }
      let fault : FaultRecord :=
        { fault with access := { fault.access with acctype := addrdesc.fault.access.acctype } }
      (pure ((PendSErrorInterrupt fault))))
  else
    (do
      let syndrome : (BitVec 64) := (BitVec.update syndrome 18 (Bit 1#1))
      let syndrome : (BitVec 64) :=
        if (((BEq.beq addrdesc.fault.access.acctype AccessType_SPE) && (async_external_abort || (start_vaddr != addrdesc.vaddress))) : Bool)
        then (BitVec.update syndrome 19 (Bit 1#1))
        else syndrome
      let syndrome ← (( do
        if ((IsZero (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access syndrome 17)]))) : Bool)
        then
          (do
            let syndrome : (BitVec 64) := (BitVec.update syndrome 17 (Bit 1#1))
            let ec ← (( do (undefined_bitvector_at (← occLabel 2438) 6) ) : SailM (BitVec 6) )
            let w__6 ← (( do
              (pure ((← do
                    (pure ((← do
                          (HaveRME ())) && ((bne addrdesc.fault.gpcf.gpf GPCF_None) : Bool)))) && ((bne
                    addrdesc.fault.gpcf.gpf GPCF_Fail) : Bool))) ) : SailM Bool )
            let ec : (BitVec 6) :=
              if (w__6 : Bool)
              then 0b011110#6
              else
                (if (addrdesc.fault.secondstage : Bool)
                then 0b100101#6
                else 0b100100#6)
            let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 31 26 ec)
            if (async_external_abort : Bool)
            then
              (let syndrome : (BitVec 64) :=
                (Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ 0b010001#6))
              (pure (syndrome)))
            else
              (do
                let w__7 ← (( do (EncodeLDFSC statuscode addrdesc.fault.level) ) : SailM
                  (BitVec 6) )
                let syndrome :=
                  ((Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ w__7)) : (BitVec 64))
                (pure (syndrome))))
        else (pure (syndrome)) ) : SailM (BitVec 64) )
      match addrdesc.fault.access.acctype with
      | .AccessType_SPE =>
        (do
          let w__8 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
          writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__8 63 0 syndrome))
      | _ =>
        (do
          (Unreachable ())))


def BRBEBranchOnISB (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "ISB generates Branch records")


def AArch32_EL2Enabled (ss : SecurityState) : SailM Bool := do
  if ((BEq.beq ss SS_Secure) : Bool)
  then
    (do
      let w__2 ← (( do
        if ((← do
             (HaveEL EL2)) : Bool)
        then
          (do
            (HaveSecureEL2Ext ()))
        else (pure false) ) : SailM Bool )
      if ((! w__2) : Bool)
      then (pure (false))
      else
        (do
          let w__3 ← (( do (HaveEL EL3) ) : SailM Bool )
          if (w__3 : Bool)
          then
            (do
              let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure (((_get_SCR_EL3_Type_EEL2 w__4) == 1#1))))
          else
            (do
              (__IMPDEF_boolean "Secure-only implementation"))))
  else
    (do
      (HaveEL EL2))


def DBGDTR_EL0_read__1 (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _DBGDTR_EL0 ) : SailM DBGDTR_EL0_Type )
  let w__0 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
  let r ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
        let r := ((Sail.BitVec.updateSubrange r 63 32 (BitVec.slice w__1 0 32)) : (BitVec 64))
        (pure (r)))
    else
      (do
        let w__2 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
            let r := ((Sail.BitVec.updateSubrange r 63 32 (BitVec.slice w__3 0 32)) : (BitVec 64))
            (pure (r)))
        else
          (do
            let w__4 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
            let r := ((Sail.BitVec.updateSubrange r 63 32 (BitVec.slice w__4 0 32)) : (BitVec 64))
            (pure (r)))) ) : SailM (BitVec 64) )
  let w__5 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__6 0 32)) : (BitVec 64))
      (pure (r)))
  else
    (do
      let w__7 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let w__8 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__8 0 32)) : (BitVec 64))
          (pure (r)))
      else
        (do
          let w__9 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
          let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__9 0 32)) : (BitVec 64))
          (pure (r))))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV87 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap7_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV86 enabled))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV91 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap1_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV90 enabled)
      (__ConfigureV86 enabled))
  else (pure (()))


def __set_SCTLR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : SCTLR_EL1_Type := value_name
  let w__0 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__0 4 0 (BitVec.slice r 0 5))
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (BitVec.update w__1 6 (Bit (BitVec.slice r 6 1)))
  let w__2 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__2 63 8 (BitVec.slice r 8 56))
  let w__3 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  if ((! (! w__3)) : Bool)
  then
    (do
      let w__4 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__4 7 7 (_get_SCTLR_EL1_Type_ITD r)))
  else (pure (()))
  let w__5 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  if ((! (! w__5)) : Bool)
  then
    (do
      let w__6 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__6 5 5 (_get_SCTLR_EL1_Type_CP15BEN r)))
  else (pure (()))


def __set_PMSSCR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMSSCR_EL1_Type := value_name
  let w__0 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__0 63 1 (BitVec.slice r 1 63))
  let w__1 ← (( do (__IMPDEF_boolean "Capture events are disabled") ) : SailM Bool )
  if ((! w__1) : Bool)
  then
    (do
      let w__2 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
      writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__2 0 0 (_get_PMSSCR_EL1_Type_SS r)))
  else (pure (()))


def __set_FPCR (value_name : (BitVec 64)) : SailM Unit := do
  let r : FPCR_Type := value_name
  let w__0 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__0 7 0 (BitVec.slice r 0 8))
  let w__1 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__1 14 13 (BitVec.slice r 13 2))
  let w__2 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (BitVec.update w__2 19 (Bit (BitVec.slice r 19 1)))
  let w__3 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__3 63 22 (BitVec.slice r 22 42))
  let w__4 ← (( do (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ") ) : SailM Bool )
  if ((! w__4) : Bool)
  then
    (do
      let w__5 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__5 21 20 (_get_FPCR_Type_Stride r)))
  else (pure (()))
  let w__6 ← (( do (__IMPDEF_boolean "IMPLEMENTED_FPSCR.LEN,STRIDE as RAZ") ) : SailM Bool )
  if ((! w__6) : Bool)
  then
    (do
      let w__7 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__7 18 16 (_get_FPCR_Type_length r)))
  else (pure (()))
  let w__8 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions") ) : SailM
    Bool )
  if ((! (! w__8)) : Bool)
  then
    (do
      let w__9 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__9 15 15 (_get_FPCR_Type_IDE r)))
  else (pure (()))
  let w__10 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")
    ) : SailM Bool )
  if ((! (! w__10)) : Bool)
  then
    (do
      let w__11 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__11 12 12 (_get_FPCR_Type_IXE r)))
  else (pure (()))
  let w__12 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions") ) : SailM Bool
    )
  if ((! (! w__12)) : Bool)
  then
    (do
      let w__13 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__13 11 11 (_get_FPCR_Type_UFE r)))
  else (pure (()))
  let w__14 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions") ) : SailM Bool )
  if ((! (! w__14)) : Bool)
  then
    (do
      let w__15 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__15 10 10 (_get_FPCR_Type_OFE r)))
  else (pure (()))
  let w__16 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions") ) : SailM
    Bool )
  if ((! (! w__16)) : Bool)
  then
    (do
      let w__17 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__17 9 9 (_get_FPCR_Type_DZE r)))
  else (pure (()))
  let w__18 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions") ) :
    SailM Bool )
  if ((! (! w__18)) : Bool)
  then
    (do
      let w__19 ← (( do readReg FPCR ) : SailM (BitVec 64) )
      writeReg FPCR (Sail.BitVec.updateSubrange w__19 8 8 (_get_FPCR_Type_IOE r)))
  else (pure (()))


def __set_FPEXC32_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : FPEXC32_EL2_Type := value_name
  let w__0 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__0 6 5 (BitVec.slice r 5 2))
  let w__1 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__1 30 8 (BitVec.slice r 8 23))
  let w__2 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__2 63 32 (BitVec.slice r 32 32))
  let w__3 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions") ) : SailM
    Bool )
  if ((! (! w__3)) : Bool)
  then
    (do
      let w__4 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
      writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__4 7 7 (_get_FPEXC32_EL2_Type_IDF r)))
  else (pure (()))
  let w__5 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")
    ) : SailM Bool )
  if ((! (! w__5)) : Bool)
  then
    (do
      let w__6 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
      writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__6 4 4 (_get_FPEXC32_EL2_Type_IXF r)))
  else (pure (()))
  let w__7 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions") ) : SailM Bool
    )
  if ((! (! w__7)) : Bool)
  then
    (do
      let w__8 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
      writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__8 3 3 (_get_FPEXC32_EL2_Type_UFF r)))
  else (pure (()))
  let w__9 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")
    ) : SailM Bool )
  if ((! (! w__9)) : Bool)
  then
    (do
      let w__10 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
      writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__10 2 2 (_get_FPEXC32_EL2_Type_OFF r)))
  else (pure (()))
  let w__11 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions") ) : SailM
    Bool )
  if ((! (! w__11)) : Bool)
  then
    (do
      let w__12 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
      writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__12 1 1 (_get_FPEXC32_EL2_Type_DZF r)))
  else (pure (()))
  let w__13 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions") ) :
    SailM Bool )
  if ((! (! w__13)) : Bool)
  then
    (do
      let w__14 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
      writeReg FPEXC32_EL2 (Sail.BitVec.updateSubrange w__14 0 0 (_get_FPEXC32_EL2_Type_IOF r)))
  else (pure (()))


def __set_SCTLR_EL2 (value_name : (BitVec 64)) : SailM Unit := do
  let r : SCTLR_EL2_Type := value_name
  let w__0 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__0 6 0 (BitVec.slice r 0 7))
  let w__1 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__1 63 8 (BitVec.slice r 8 56))
  let w__2 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  if ((! (! w__2)) : Bool)
  then
    (do
      let w__3 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__3 7 7 (_get_SCTLR_EL2_Type_ITD r)))
  else (pure (()))


def DBGDTR_EL0_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : DBGDTR_EL0_Type := value_name
  let w__0 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
      writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange w__1 31 0 (BitVec.slice r 32 32)))
  else
    (do
      let w__2 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let w__3 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
          writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange w__3 31 0 (BitVec.slice r 32 32)))
      else
        (do
          let w__4 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
          writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange w__4 31 0 (BitVec.slice r 32 32))))
  let w__5 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
      writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange w__6 31 0 (BitVec.slice r 0 32)))
  else
    (do
      let w__7 ← (( do (__IMPDEF_boolean "read") ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let w__8 ← (( do readReg DBGDTRRX_EL0 ) : SailM (BitVec 64) )
          writeReg DBGDTRRX_EL0 (Sail.BitVec.updateSubrange w__8 31 0 (BitVec.slice r 0 32)))
      else
        (do
          let w__9 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
          writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange w__9 31 0 (BitVec.slice r 0 32))))
  writeReg _DBGDTR_EL0 r


def __set_PMSNEVFR_EL1 (value_name : (BitVec 64)) : SailM Unit := do
  let r : PMSNEVFR_EL1_Type := value_name
  let w__0 ← (( do
    (__IMPDEF_boolean "event 63 is not implemented, or filtering on event 63 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__1 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 63 63 (_get_PMSNEVFR_EL1_Type_E63 w__1)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__2 ← (( do
    (__IMPDEF_boolean "event 62 is not implemented, or filtering on event 62 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__2) : Bool)
    then
      (do
        let w__3 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 62 62 (_get_PMSNEVFR_EL1_Type_E62 w__3)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__4 ← (( do
    (__IMPDEF_boolean "event 61 is not implemented, or filtering on event 61 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__4) : Bool)
    then
      (do
        let w__5 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 61 61 (_get_PMSNEVFR_EL1_Type_E61 w__5)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__6 ← (( do
    (__IMPDEF_boolean "event 60 is not implemented, or filtering on event 60 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__6) : Bool)
    then
      (do
        let w__7 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 60 60 (_get_PMSNEVFR_EL1_Type_E60 w__7)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__8 ← (( do
    (__IMPDEF_boolean "event 59 is not implemented, or filtering on event 59 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__8) : Bool)
    then
      (do
        let w__9 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 59 59 (_get_PMSNEVFR_EL1_Type_E59 w__9)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__10 ← (( do
    (__IMPDEF_boolean "event 58 is not implemented, or filtering on event 58 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__10) : Bool)
    then
      (do
        let w__11 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 58 58 (_get_PMSNEVFR_EL1_Type_E58 w__11)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__12 ← (( do
    (__IMPDEF_boolean "event 57 is not implemented, or filtering on event 57 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__12) : Bool)
    then
      (do
        let w__13 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 57 57 (_get_PMSNEVFR_EL1_Type_E57 w__13)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__14 ← (( do
    (__IMPDEF_boolean "event 56 is not implemented, or filtering on event 56 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__14) : Bool)
    then
      (do
        let w__15 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 56 56 (_get_PMSNEVFR_EL1_Type_E56 w__15)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__16 ← (( do
    (__IMPDEF_boolean "event 55 is not implemented, or filtering on event 55 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__16) : Bool)
    then
      (do
        let w__17 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 55 55 (_get_PMSNEVFR_EL1_Type_E55 w__17)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__18 ← (( do
    (__IMPDEF_boolean "event 54 is not implemented, or filtering on event 54 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__18) : Bool)
    then
      (do
        let w__19 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 54 54 (_get_PMSNEVFR_EL1_Type_E54 w__19)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__20 ← (( do
    (__IMPDEF_boolean "event 53 is not implemented, or filtering on event 53 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__20) : Bool)
    then
      (do
        let w__21 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 53 53 (_get_PMSNEVFR_EL1_Type_E53 w__21)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__22 ← (( do
    (__IMPDEF_boolean "event 52 is not implemented, or filtering on event 52 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__22) : Bool)
    then
      (do
        let w__23 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 52 52 (_get_PMSNEVFR_EL1_Type_E52 w__23)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__24 ← (( do
    (__IMPDEF_boolean "event 51 is not implemented, or filtering on event 51 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__24) : Bool)
    then
      (do
        let w__25 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 51 51 (_get_PMSNEVFR_EL1_Type_E51 w__25)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__26 ← (( do
    (__IMPDEF_boolean "event 50 is not implemented, or filtering on event 50 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__26) : Bool)
    then
      (do
        let w__27 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 50 50 (_get_PMSNEVFR_EL1_Type_E50 w__27)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__28 ← (( do
    (__IMPDEF_boolean "event 49 is not implemented, or filtering on event 49 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__28) : Bool)
    then
      (do
        let w__29 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 49 49 (_get_PMSNEVFR_EL1_Type_E49 w__29)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__30 ← (( do
    (__IMPDEF_boolean "event 48 is not implemented, or filtering on event 48 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__30) : Bool)
    then
      (do
        let w__31 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 48 48 (_get_PMSNEVFR_EL1_Type_E48 w__31)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__32 ← (( do
    (__IMPDEF_boolean "event 31 is not implemented, or filtering on event 31 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__32) : Bool)
    then
      (do
        let w__33 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 31 31 (_get_PMSNEVFR_EL1_Type_E31 w__33)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__34 ← (( do
    (__IMPDEF_boolean "event 30 is not implemented, or filtering on event 30 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__34) : Bool)
    then
      (do
        let w__35 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 30 30 (_get_PMSNEVFR_EL1_Type_E30 w__35)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__36 ← (( do
    (__IMPDEF_boolean "event 29 is not implemented, or filtering on event 29 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__36) : Bool)
    then
      (do
        let w__37 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 29 29 (_get_PMSNEVFR_EL1_Type_E29 w__37)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__38 ← (( do
    (__IMPDEF_boolean "event 28 is not implemented, or filtering on event 28 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__38) : Bool)
    then
      (do
        let w__39 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 28 28 (_get_PMSNEVFR_EL1_Type_E28 w__39)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__40 ← (( do
    (__IMPDEF_boolean "event 27 is not implemented, or filtering on event 27 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__40) : Bool)
    then
      (do
        let w__41 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 27 27 (_get_PMSNEVFR_EL1_Type_E27 w__41)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__42 ← (( do
    (__IMPDEF_boolean "event 26 is not implemented, or filtering on event 26 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__42) : Bool)
    then
      (do
        let w__43 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 26 26 (_get_PMSNEVFR_EL1_Type_E26 w__43)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__44 ← (( do
    (__IMPDEF_boolean "event 25 is not implemented, or filtering on event 25 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__44) : Bool)
    then
      (do
        let w__45 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 25 25 (_get_PMSNEVFR_EL1_Type_E25 w__45)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__46 ← (( do
    (__IMPDEF_boolean "event 24 is not implemented, or filtering on event 24 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__46) : Bool)
    then
      (do
        let w__47 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 24 24 (_get_PMSNEVFR_EL1_Type_E24 w__47)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__48 ← (( do
    (__IMPDEF_boolean "event 15 is not implemented, or filtering on event 15 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__48) : Bool)
    then
      (do
        let w__49 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 15 15 (_get_PMSNEVFR_EL1_Type_E15 w__49)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__50 ← (( do
    (__IMPDEF_boolean "event 14 is not implemented, or filtering on event 14 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__50) : Bool)
    then
      (do
        let w__51 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 14 14 (_get_PMSNEVFR_EL1_Type_E14 w__51)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__52 ← (( do
    (__IMPDEF_boolean "event 13 is not implemented, or filtering on event 13 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__52) : Bool)
    then
      (do
        let w__53 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 13 13 (_get_PMSNEVFR_EL1_Type_E13 w__53)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  let w__54 ← (( do
    (__IMPDEF_boolean "event 12 is not implemented, or filtering on event 12 is not supported") ) :
    SailM Bool )
  let r ← (( do
    if ((! w__54) : Bool)
    then
      (do
        let w__55 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let r :=
          ((Sail.BitVec.updateSubrange r 12 12 (_get_PMSNEVFR_EL1_Type_E12 w__55)) : (BitVec 64))
        (pure (r)))
    else (pure (r)) ) : SailM (BitVec 64) )
  writeReg PMSNEVFR_EL1 r


end ArmFull.Functions
