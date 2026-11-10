import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0010
import ArmFull.Fn.M0015
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0047
import ArmFull.Fn.M0054
import ArmFull.Fn.M0060
import ArmFull.Fn.M0061
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167

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

def InITBlock (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (CurrentInstrSet ()) ) : SailM InstrSet )
  if ((BEq.beq w__0 InstrSet_T32) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (pure (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb w__1.IT 3 0)) != 0b0000#4))))
  else (pure (false))


def SPSRWriteByInstr (value_name : (BitVec 32)) (bytemask : (BitVec 4)) : SailM Unit := do
  let new_spsr ← (( do (SPSR_read (N := 32)) ) : SailM (BitVec 32) )
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 3)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 31 24 (Sail.BitVec.extractLsb value_name 31 24))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 2)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 23 16 (Sail.BitVec.extractLsb value_name 23 16))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 1)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 15 8 (Sail.BitVec.extractLsb value_name 15 8))
    else new_spsr
  let new_spsr : (BitVec 32) :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 0)])) == 1#1) : Bool)
    then (Sail.BitVec.updateSubrange new_spsr 7 0 (Sail.BitVec.extractLsb value_name 7 0))
    else new_spsr
  (SPSR_set (N := 32) new_spsr)


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


def __set_HSCTLR (value_name : (BitVec 32)) : SailM Unit := do
  let r : HSCTLR_Type := value_name
  let w__0 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 5 w__0 0 (BitVec.slice r 0 5))))
  let w__1 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 w__1 6 (BitVec.slice r 6 1))))
  let w__2 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 24 w__2 8 (BitVec.slice r 8 24))))
  let w__3 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  if ((! (! w__3)) : Bool)
  then
    (do
      let w__4 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      (HSCTLR_write (_update_HSCTLR_Type_ITD w__4 (_get_HSCTLR_Type_ITD r))))
  else (pure (()))
  let w__5 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  if ((! (! w__5)) : Bool)
  then
    (do
      let w__6 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
      (HSCTLR_write (_update_HSCTLR_Type_CP15BEN w__6 (_get_HSCTLR_Type_CP15BEN r))))
  else (pure (()))


end ArmFull.Functions
