module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0121
public import ArmFull.Fn.M0144 set_option backward.proofsInPublic true @[expose] public section

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

def SDER_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : SDER_Type := value_name
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
      (SDER32_EL3_write (Mk_SDER32_EL3_Type (set_slice 32 w__1 0 (BitVec.slice r 0 32)))))
  else
    (do
      let w__2 ← (( do readReg SDER32_EL2 ) : SailM (BitVec 64) )
      writeReg SDER32_EL2 (Sail.BitVec.updateSubrange w__2 31 0 (BitVec.slice r 0 32)))
  writeReg _SDER r


def MPAM1_EL1_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : MPAM1_EL1_Type := value_name
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      (MPAM3_EL3_write (Mk_MPAM3_EL3_Type (set_slice 1 w__1 63 (BitVec.slice r 63 1)))))
  else
    (do
      let w__2 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      writeReg MPAM2_EL2 (BitVec.update w__2 63 (Bit (BitVec.slice r 63 1))))
  writeReg _MPAM1_EL1 r


/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg0 (cold : Bool) : SailM Bool := do
  let w__0 ← (( do readReg ID_MMFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR2_EL1 (Sail.BitVec.updateSubrange w__0 63 32 0b00000000000000000000000000000000#32)
  let w__1 ← (( do readReg ID_MMFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR2_EL1 (Sail.BitVec.updateSubrange w__1 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__2 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__2 63 32 0b00000000000000000000000000000000#32)
  let w__3 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__3 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__4 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__4 47 44 0b0000#4)
  let w__5 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange w__5 63 45 0b0000000000000000000#19)
  let w__6 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange w__6 43 42 0b00#2)
  let w__7 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (BitVec.update w__7 39 (Bit 0#1))
  let w__8 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (BitVec.update w__8 31 (Bit 1#1))
  let w__9 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (Sail.BitVec.updateSubrange w__9 24 23 0b00#2)
  let w__10 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
  writeReg VTCR_EL2 (BitVec.update w__10 20 (Bit 0#1))
  let w__11 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__11 63 63 0#1)
  let w__12 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__12 62 62 0#1)
  let w__13 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__13 61 61 0#1)
  let w__14 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__14 60 60 0#1)
  let w__15 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__15 59 59 0#1)
  let w__16 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__16 58 58 0#1)
  let w__17 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__17 57 57 0#1)
  let w__18 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__18 56 49 0b00000000#8)
  let w__19 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__19 48 48 0#1)
  let w__20 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__20 47 47 0#1)
  let w__21 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__21 46 46 0#1)
  let w__22 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__22 45 45 0#1)
  let w__23 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__23 44 44 0#1)
  let w__24 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__24 43 43 0#1)
  let w__25 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (BitVec.update w__25 42 (Bit 0#1))
  let w__26 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__26 41 41 0#1)
  let w__27 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__27 40 40 0#1)
  let w__28 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__28 39 38 0b00#2)
  let w__29 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__29 37 37 0#1)
  let w__30 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__30 36 36 0#1)
  let w__31 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__31 35 35 0#1)
  let w__32 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__32 34 34 0#1)
  let w__33 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__33 33 33 0#1)
  let w__34 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__34 32 32 0#1)
  let w__35 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__35 31 31 0#1)
  let w__36 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__36 30 30 0#1)
  let w__37 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__37 29 29 0#1)
  let w__38 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__38 28 28 0#1)
  let w__39 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__39 27 27 0#1)
  let w__40 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__40 26 26 0#1)
  let w__41 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__41 25 25 0#1)
  let w__42 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__42 24 24 0#1)
  let w__43 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__43 23 23 0#1)
  let w__44 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__44 22 22 0#1)
  let w__45 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__45 21 20 0b00#2)
  let w__46 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__46 19 19 0#1)
  let w__47 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__47 18 18 0#1)
  let w__48 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__48 17 17 0#1)
  let w__49 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__49 16 16 0#1)
  let w__50 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__50 15 15 0#1)
  let w__51 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__51 14 14 0#1)
  let w__52 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__52 13 13 0#1)
  let w__53 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__53 12 12 0#1)
  let w__54 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__54 11 11 0#1)
  let w__55 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__55 10 10 0#1)
  let w__56 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__56 9 9 0#1)
  let w__57 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (BitVec.update w__57 8 (Bit 0#1))
  let w__58 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__58 7 7 0#1)
  let w__59 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__59 6 6 0#1)
  let w__60 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__60 5 5 0#1)
  let w__61 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__61 4 4 0#1)
  let w__62 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__62 3 3 0#1)
  let w__63 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__63 2 2 0#1)
  let w__64 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__64 1 1 0#1)
  let w__65 ← (( do readReg HDFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR_EL2 (Sail.BitVec.updateSubrange w__65 0 0 0#1)
  let w__66 ← (( do readReg ICV_NMIAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_NMIAR1_EL1 (Sail.BitVec.updateSubrange w__66 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__67 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
  writeReg SPSR_abt (Sail.BitVec.updateSubrange w__67 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__68 ← (( do readReg SPSR_abt ) : SailM (BitVec 64) )
  writeReg SPSR_abt (Sail.BitVec.updateSubrange w__68 63 32 0b00000000000000000000000000000000#32)
  let w__69 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__69 63 31
    0b000000000000000000000000000000000#33)
  let w__70 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__70 30 30 0#1)
  let w__71 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__71 29 29 0#1)
  let w__72 ← (( do readReg MDCCINT_EL1 ) : SailM (BitVec 64) )
  writeReg MDCCINT_EL1 (Sail.BitVec.updateSubrange w__72 28 0 0b00000000000000000000000000000#29)
  let w__73 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR0_EL1 (Sail.BitVec.updateSubrange w__73 63 32 0b00000000000000000000000000000000#32)
  let w__74 ← (( do readReg MVFR0_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR0_EL1 (Sail.BitVec.updateSubrange w__74 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__75 ← (( do readReg ICC_HPPIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR1_EL1 (Sail.BitVec.updateSubrange w__75 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__76 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__76 63 13
    0b000000000000000000000000000000000000000000000000000#51)
  let w__78 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__77 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__77) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__78 : Bool)
  then
    (do
      let w__79 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__79 12 12 0#1))
  else
    (do
      let w__80 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__81 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__80 12 12 w__81))
  let w__83 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__82 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__82) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__83 : Bool)
  then
    (do
      let w__84 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__84 11 11 0#1))
  else
    (do
      let w__85 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__86 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__85 11 11 w__86))
  let w__88 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__87 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__87) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__88 : Bool)
  then
    (do
      let w__89 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__89 10 10 0#1))
  else
    (do
      let w__90 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__91 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__90 10 10 w__91))
  let w__92 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__92 9 5 0b00000#5)
  let w__94 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__93 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__93) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__94 : Bool)
  then
    (do
      let w__95 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__95 4 4 0#1))
  else
    (do
      let w__96 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__97 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__96 4 4 w__97))
  let w__99 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__98 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__98) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__99 : Bool)
  then
    (do
      let w__100 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__100 3 3 0#1))
  else
    (do
      let w__101 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__102 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__101 3 3 w__102))
  let w__103 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (BitVec.update w__103 2 (Bit 0#1))
  let w__105 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__104 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__104) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__105 : Bool)
  then
    (do
      let w__106 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__106 1 1 0#1))
  else
    (do
      let w__107 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__108 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__107 1 1 w__108))
  let w__110 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__109 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__109) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__110 : Bool)
  then
    (do
      let w__111 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__111 0 0 0#1))
  else
    (do
      let w__112 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__113 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__112 0 0 w__113))
  let w__114 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
  writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__114 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__116 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__115 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__115) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__116 : Bool)
  then
    (do
      let w__117 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__117 13 13 0#1))
  else
    (do
      let w__118 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__119 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__118 13 13 w__119))
  let w__121 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__120 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__120) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__121 : Bool)
  then
    (do
      let w__122 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__122 12 12 0#1))
  else
    (do
      let w__123 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__124 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__123 12 12 w__124))
  let w__126 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__125 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__125) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__126 : Bool)
  then
    (do
      let w__127 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__127 11 11 0#1))
  else
    (do
      let w__128 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__129 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__128 11 11 w__129))
  let w__131 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__130 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__130) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__131 : Bool)
  then
    (do
      let w__132 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__132 10 10 0#1))
  else
    (do
      let w__133 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__134 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__133 10 10 w__134))
  let w__136 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__135 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__135) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__136 : Bool)
  then
    (do
      let w__137 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__137 9 8 0b00#2))
  else
    (do
      let w__138 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__139 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__138 9 8 w__139))
  let w__141 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__140 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__140) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__141 : Bool)
  then
    (do
      let w__142 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__142 7 6 0b00#2))
  else
    (do
      let w__143 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__144 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__143 7 6 w__144))
  let w__146 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__145 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__145) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__146 : Bool)
  then
    (do
      let w__147 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__147 5 5 0#1))
  else
    (do
      let w__148 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__149 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__148 5 5 w__149))
  let w__151 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__150 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__150) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__151 : Bool)
  then
    (do
      let w__152 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__152 4 4 0#1))
  else
    (do
      let w__153 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__154 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__153 4 4 w__154))
  let w__156 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__155 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__155) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__156 : Bool)
  then
    (do
      let w__157 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__157 3 3 0#1))
  else
    (do
      let w__158 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__159 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__158 3 3 w__159))
  let w__161 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__160 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__160) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__161 : Bool)
  then
    (do
      let w__162 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__162 2 2 0#1))
  else
    (do
      let w__163 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__164 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__163 2 2 w__164))
  let w__166 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__165 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__165) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__166 : Bool)
  then
    (do
      let w__167 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__167 1 1 0#1))
  else
    (do
      let w__168 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__169 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__168 1 1 w__169))
  let w__171 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__170 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__170) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__171 : Bool)
  then
    (do
      let w__172 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__172 0 0 0#1))
  else
    (do
      let w__173 ← (( do readReg TCR2_EL2 ) : SailM (BitVec 64) )
      let w__174 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL2 (Sail.BitVec.updateSubrange w__173 0 0 w__174))
  let w__175 ← (( do readReg ESR_EL1 ) : SailM (BitVec 64) )
  writeReg ESR_EL1 (Sail.BitVec.updateSubrange w__175 63 56 0b00000000#8)
  let w__176 ← (( do readReg ICV_BPR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_BPR1_EL1 (Sail.BitVec.updateSubrange w__176 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__177 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (Sail.BitVec.updateSubrange w__177 63 44 0b00000000000000000000#20)
  let w__178 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (Sail.BitVec.updateSubrange w__178 40 39 0b00#2)
  let w__179 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (BitVec.update w__179 31 (Bit 1#1))
  let w__180 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (BitVec.update w__180 23 (Bit 1#1))
  let w__181 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (BitVec.update w__181 19 (Bit 0#1))
  let w__182 ← (( do readReg TCR_EL3 ) : SailM (BitVec 64) )
  writeReg TCR_EL3 (Sail.BitVec.updateSubrange w__182 7 6 0b00#2)
  let w__183 ← (( do readReg ID_ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR2_EL1 (Sail.BitVec.updateSubrange w__183 63 32
    0b00000000000000000000000000000000#32)
  let w__184 ← (( do readReg ID_ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR2_EL1 (Sail.BitVec.updateSubrange w__184 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__185 ← (( do readReg PMECR_EL1 ) : SailM (BitVec 64) )
  writeReg PMECR_EL1 (Sail.BitVec.updateSubrange w__185 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  if ((cold && true) : Bool)
  then
    (do
      let w__186 ← (( do readReg PMECR_EL1 ) : SailM (BitVec 64) )
      let w__187 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg PMECR_EL1 (Sail.BitVec.updateSubrange w__186 4 3 w__187))
  else
    (do
      let w__191 ← (( do
        if ((← do
             if ((cold : Bool) : Bool)
             then
               (do
                 let w__188 ← (( do (HaveEL EL3) ) : SailM Bool )
                 (pure (((! w__188) : Bool))))
             else (pure false)) : Bool)
        then
          (do
            let w__190 ← (( do (HaveEL EL2) ) : SailM Bool )
            (pure (((! w__190) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__191 : Bool)
      then
        (do
          let w__192 ← (( do readReg PMECR_EL1 ) : SailM (BitVec 64) )
          writeReg PMECR_EL1 (Sail.BitVec.updateSubrange w__192 4 3 0b00#2))
      else (pure (())))
  let w__193 ← (( do readReg ICC_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_PMR_EL1 (Sail.BitVec.updateSubrange w__193 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__194 ← (( do readReg ICC_PMR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_PMR_EL1 (Sail.BitVec.updateSubrange w__194 7 0 0b00000000#8)
  let w__195 ← (( do readReg ICV_EOIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_EOIR1_EL1 (Sail.BitVec.updateSubrange w__195 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__196 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
  writeReg RMR_EL1 (Sail.BitVec.updateSubrange w__196 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__197 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
  writeReg RMR_EL1 (Sail.BitVec.updateSubrange w__197 1 1 0#1)
  let w__198 ← (( do readReg OSLAR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLAR_EL1 (Sail.BitVec.updateSubrange w__198 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__199 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (Sail.BitVec.updateSubrange w__199 63 59 0b00000#5)
  let w__200 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (Sail.BitVec.updateSubrange w__200 57 32 0b00000000000000000000000000#26)
  let w__201 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (BitVec.update w__201 25 (Bit 0#1))
  let w__202 ← (( do readReg PMICFILTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMICFILTR_EL0 (Sail.BitVec.updateSubrange w__202 19 16 0b0000#4)
  let w__203 ← (( do readReg ICC_HPPIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_HPPIR0_EL1 (Sail.BitVec.updateSubrange w__203 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__204 ← (( do readReg CNTHPS_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHPS_CTL_EL2 (Sail.BitVec.updateSubrange w__204 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__205 ← (( do readReg VMECID_A_EL2 ) : SailM (BitVec 64) )
  writeReg VMECID_A_EL2 (Sail.BitVec.updateSubrange w__205 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__206 ← (( do readReg MECID_RL_A_EL3 ) : SailM (BitVec 64) )
  writeReg MECID_RL_A_EL3 (Sail.BitVec.updateSubrange w__206 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__207 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__207 63 16
    (Sail.BitVec.extractLsb 0b00000000000000000000000000000000000000000000000000#50 49 2))
  let w__208 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__208 14 14
    (Sail.BitVec.extractLsb 0b00000000000000000000000000000000000000000000000000#50 1 1))
  let w__209 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__209 4 4
    (Sail.BitVec.extractLsb 0b00000000000000000000000000000000000000000000000000#50 0 0))
  let w__210 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__210 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__211 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSCLR_EL0 (Sail.BitVec.updateSubrange w__211 63 33
    0b0000000000000000000000000000000#31)
  let w__212 ← (( do readReg PMOVSCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMOVSCLR_EL0 (BitVec.update w__212 32 (Bit 0#1))
  let w__213 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__213 63 50 0b00000000000000#14)
  let w__214 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__214 49 49
    (Sail.BitVec.extractLsb 0b0000000000000000#16 15 15))
  let w__215 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__215 47 47
    (Sail.BitVec.extractLsb 0b0000000000000000#16 14 14))
  let w__216 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__216 45 45
    (Sail.BitVec.extractLsb 0b0000000000000000#16 13 13))
  let w__217 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__217 43 43
    (Sail.BitVec.extractLsb 0b0000000000000000#16 12 12))
  let w__218 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__218 41 41
    (Sail.BitVec.extractLsb 0b0000000000000000#16 11 11))
  let w__219 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__219 39 39
    (Sail.BitVec.extractLsb 0b0000000000000000#16 10 10))
  let w__220 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__220 37 37
    (Sail.BitVec.extractLsb 0b0000000000000000#16 9 9))
  let w__221 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__221 35 35
    (Sail.BitVec.extractLsb 0b0000000000000000#16 8 8))
  let w__222 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__222 33 33
    (Sail.BitVec.extractLsb 0b0000000000000000#16 7 7))
  let w__223 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__223 31 31
    (Sail.BitVec.extractLsb 0b0000000000000000#16 6 6))
  let w__224 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__224 29 29
    (Sail.BitVec.extractLsb 0b0000000000000000#16 5 5))
  let w__225 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__225 27 27
    (Sail.BitVec.extractLsb 0b0000000000000000#16 4 4))
  let w__226 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__226 25 25
    (Sail.BitVec.extractLsb 0b0000000000000000#16 3 3))
  let w__227 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__227 23 23
    (Sail.BitVec.extractLsb 0b0000000000000000#16 2 2))
  let w__228 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__228 21 21
    (Sail.BitVec.extractLsb 0b0000000000000000#16 1 1))
  let w__229 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__229 19 19
    (Sail.BitVec.extractLsb 0b0000000000000000#16 0 0))
  let w__230 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__230 48 48
    (Sail.BitVec.extractLsb 0b0000000000000000#16 15 15))
  let w__231 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__231 46 46
    (Sail.BitVec.extractLsb 0b0000000000000000#16 14 14))
  let w__232 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__232 44 44
    (Sail.BitVec.extractLsb 0b0000000000000000#16 13 13))
  let w__233 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__233 42 42
    (Sail.BitVec.extractLsb 0b0000000000000000#16 12 12))
  let w__234 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__234 40 40
    (Sail.BitVec.extractLsb 0b0000000000000000#16 11 11))
  let w__235 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__235 38 38
    (Sail.BitVec.extractLsb 0b0000000000000000#16 10 10))
  let w__236 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__236 36 36
    (Sail.BitVec.extractLsb 0b0000000000000000#16 9 9))
  let w__237 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__237 34 34
    (Sail.BitVec.extractLsb 0b0000000000000000#16 8 8))
  let w__238 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__238 32 32
    (Sail.BitVec.extractLsb 0b0000000000000000#16 7 7))
  let w__239 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__239 30 30
    (Sail.BitVec.extractLsb 0b0000000000000000#16 6 6))
  let w__240 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__240 28 28
    (Sail.BitVec.extractLsb 0b0000000000000000#16 5 5))
  let w__241 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__241 26 26
    (Sail.BitVec.extractLsb 0b0000000000000000#16 4 4))
  let w__242 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__242 24 24
    (Sail.BitVec.extractLsb 0b0000000000000000#16 3 3))
  let w__243 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__243 22 22
    (Sail.BitVec.extractLsb 0b0000000000000000#16 2 2))
  let w__244 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__244 20 20
    (Sail.BitVec.extractLsb 0b0000000000000000#16 1 1))
  let w__245 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__245 18 18
    (Sail.BitVec.extractLsb 0b0000000000000000#16 0 0))
  let w__246 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__246 17 17 0#1)
  let w__247 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__247 0 0 0#1)
  let w__248 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__248 16 5 0b000000000000#12)
  let w__249 ← (( do readReg HAFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HAFGRTR_EL2 (Sail.BitVec.updateSubrange w__249 4 1 0b0000#4)
  let w__250 ← (( do readReg ICC_BPR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_BPR0_EL1 (Sail.BitVec.updateSubrange w__250 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__251 ← (( do readReg ACCDATA_EL1 ) : SailM (BitVec 64) )
  writeReg ACCDATA_EL1 (Sail.BitVec.updateSubrange w__251 63 32
    0b00000000000000000000000000000000#32)
  let w__252 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
  writeReg OSDLR_EL1 (Sail.BitVec.updateSubrange w__252 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__253 ← (( do readReg OSDLR_EL1 ) : SailM (BitVec 64) )
  writeReg OSDLR_EL1 (Sail.BitVec.updateSubrange w__253 0 0 0#1)
  let w__257 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__254 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__254) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__256 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__256) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__257 : Bool)
  then
    (do
      let w__258 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__258 61 61 0#1))
  else
    (do
      let w__259 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__260 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__259 61 61 w__260))
  let w__261 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (BitVec.update w__261 34 (Bit 0#1))
  let w__262 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (BitVec.update w__262 17 (Bit 0#1))
  let w__266 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__263 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__263) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__265 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__265) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__266 : Bool)
  then
    (do
      let w__267 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__267 12 12 0#1))
  else
    (do
      let w__268 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__269 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__268 12 12 w__269))
  let w__273 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__270 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__270) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__272 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__272) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__273 : Bool)
  then
    (do
      let w__274 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__274 2 2 0#1))
  else
    (do
      let w__275 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__276 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__275 2 2 w__276))
  let w__280 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__277 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__277) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__279 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__279) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__280 : Bool)
  then
    (do
      let w__281 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__281 0 0 0#1))
  else
    (do
      let w__282 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      let w__283 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__282 0 0 w__283))
  let w__284 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__284 63 33 0b0000000000000000000000000000000#31)
  let w__285 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__285 32 32 1#1)
  let w__286 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__286 31 1 0b0000000000000000000000000000000#31)
  let w__287 ← (( do readReg PMSSCR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSSCR_EL1 (Sail.BitVec.updateSubrange w__287 0 0 0#1)
  let w__288 ← (( do readReg LORID_EL1 ) : SailM (BitVec 64) )
  writeReg LORID_EL1 (Sail.BitVec.updateSubrange w__288 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__289 ← (( do readReg LORID_EL1 ) : SailM (BitVec 64) )
  writeReg LORID_EL1 (Sail.BitVec.updateSubrange w__289 15 8 0b00000000#8)
  let w__290 ← (( do readReg CONTEXTIDR_EL2 ) : SailM (BitVec 64) )
  writeReg CONTEXTIDR_EL2 (Sail.BitVec.updateSubrange w__290 63 32
    0b00000000000000000000000000000000#32)
  let w__291 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__291 63 32 0b00000000000000000000000000000000#32)
  let w__292 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__292 26 8 0b0000000000000000000#19)
  let w__293 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__293 6 5 0b00#2)
  let w__294 ← (( do readReg CNTP_TVAL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTP_TVAL_EL0 (Sail.BitVec.updateSubrange w__294 63 32
    0b00000000000000000000000000000000#32)
  let w__295 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR4_EL1 (Sail.BitVec.updateSubrange w__295 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__296 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR4_EL1 (Sail.BitVec.updateSubrange w__296 3 0 0b0000#4)
  let w__297 ← (( do readReg ICH_EISR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_EISR_EL2 (Sail.BitVec.updateSubrange w__297 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__298 ← (( do readReg MIDR_EL1 ) : SailM (BitVec 64) )
  writeReg MIDR_EL1 (Sail.BitVec.updateSubrange w__298 63 32 0b00000000000000000000000000000000#32)
  let w__299 ← (( do readReg ICC_RPR_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_RPR_EL1 (Sail.BitVec.updateSubrange w__299 61 8
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__300 ← (( do readReg ICH_ELRSR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_ELRSR_EL2 (Sail.BitVec.updateSubrange w__300 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__301 ← (( do readReg VBAR_EL2 ) : SailM (BitVec 64) )
  writeReg VBAR_EL2 (Sail.BitVec.updateSubrange w__301 10 0 0b00000000000#11)
  let w__302 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__302 63 61 0b000#3)
  let w__303 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__303 60 60 0#1)
  let w__305 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__304 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__304) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__305 : Bool)
  then
    (do
      let w__306 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__306 59 59 0#1))
  else
    (do
      let w__307 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      let w__308 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__307 59 59 w__308))
  let w__310 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__309 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__309) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__310 : Bool)
  then
    (do
      let w__311 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__311 58 58 0#1))
  else
    (do
      let w__312 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      let w__313 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__312 58 58 w__313))
  let w__315 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__314 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__314) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__315 : Bool)
  then
    (do
      let w__316 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__316 57 57 0#1))
  else
    (do
      let w__317 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
      let w__318 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__317 57 57 w__318))
  let w__319 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__319 56 56 0#1)
  let w__320 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__320 55 55 0#1)
  let w__321 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__321 54 54 0#1)
  let w__322 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__322 53 53 0#1)
  let w__323 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__323 52 52 0#1)
  let w__324 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__324 51 51 0#1)
  let w__325 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__325 50 50 0#1)
  let w__326 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__326 49 49 0#1)
  let w__327 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__327 48 48 0#1)
  let w__328 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__328 47 47 0#1)
  let w__329 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__329 46 46 0#1)
  let w__330 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__330 45 45 0#1)
  let w__331 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__331 44 44 0#1)
  let w__332 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__332 43 43 0#1)
  let w__333 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__333 42 42 0#1)
  let w__334 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__334 41 41 0#1)
  let w__335 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__335 40 40 0#1)
  let w__336 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__336 39 39 0#1)
  let w__337 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__337 38 38 0#1)
  let w__338 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__338 37 37 0#1)
  let w__339 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__339 36 36 0#1)
  let w__340 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__340 35 35 0#1)
  let w__341 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__341 34 34 0#1)
  let w__342 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__342 33 33 0#1)
  let w__343 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__343 32 32 0#1)
  let w__344 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__344 31 31 0#1)
  let w__345 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__345 30 30 0#1)
  let w__346 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__346 29 29 0#1)
  let w__347 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__347 28 28 0#1)
  let w__348 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__348 27 27 0#1)
  let w__349 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__349 26 26 0#1)
  let w__350 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__350 25 25 0#1)
  let w__351 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__351 24 24 0#1)
  let w__352 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__352 23 23 0#1)
  let w__353 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGITR_EL2 (Sail.BitVec.updateSubrange w__353 22 22 0#1)
  (pure true)


end ArmFull.Functions
