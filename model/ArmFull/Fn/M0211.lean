import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0044
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0092
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0158
import ArmFull.Fn.M0181
import ArmFull.Fn.M0200

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

def AArch64_IMPDEFResets (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg DCZID_EL0 ) : SailM (BitVec 64) )
  writeReg DCZID_EL0 (Sail.BitVec.updateSubrange w__0 4 4 0#1)
  let w__1 ← (( do readReg DCZID_EL0 ) : SailM (BitVec 64) )
  let w__2 ← (( do readReg __dczid_log2_block_size ) : SailM Int )
  writeReg DCZID_EL0 (Sail.BitVec.updateSubrange w__1 3 0 (integer_subrange w__2 3 0))
  let w__3 ← (( do readReg ERRIDR_EL1 ) : SailM (BitVec 64) )
  writeReg ERRIDR_EL1 (Sail.BitVec.updateSubrange w__3 15 0 (Sail.BitVec.zeroExtend 0x4#4 16))
  let w__4 ← (( do readReg ERRIDR_EL1 ) : SailM (BitVec 64) )
  let loop_i_lower : Nat := 0
  let loop_i_upper : Int := ((BitVec.toNat (_get_ERRIDR_EL1_Type_NUM w__4)) -i 1)
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        ArmFull.assert ((0 ≤b i) && (i <b 4)) "sail-arm/reset.sail:432.55-432.56"
        let w__5 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        let w__6 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        writeReg ERRnFR (vectorUpdate w__5 (Sail.Int.toNatChecked (i))
          (Sail.BitVec.updateSubrange (GetElem?.getElem! w__6 (Sail.Int.toNatChecked (i))) 54 53
            0b11#2))
        let w__7 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        let w__8 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        writeReg ERRnFR (vectorUpdate w__7 (Sail.Int.toNatChecked (i))
          (Sail.BitVec.updateSubrange (GetElem?.getElem! w__8 (Sail.Int.toNatChecked (i))) 52 52 1#1))
        let w__9 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        let w__10 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        writeReg ERRnFR (vectorUpdate w__9 (Sail.Int.toNatChecked (i))
          (Sail.BitVec.updateSubrange (GetElem?.getElem! w__10 (Sail.Int.toNatChecked (i))) 51 51
            1#1))
        let w__11 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        let w__12 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        writeReg ERRnFR (vectorUpdate w__11 (Sail.Int.toNatChecked (i))
          (Sail.BitVec.updateSubrange (GetElem?.getElem! w__12 (Sail.Int.toNatChecked (i))) 50 50
            1#1))
        let w__13 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        let w__14 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        writeReg ERRnFR (vectorUpdate w__13 (Sail.Int.toNatChecked (i))
          (Sail.BitVec.updateSubrange (GetElem?.getElem! w__14 (Sail.Int.toNatChecked (i))) 49 49
            1#1))
        let w__15 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        let w__16 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        writeReg ERRnFR (vectorUpdate w__15 (Sail.Int.toNatChecked (i))
          (Sail.BitVec.updateSubrange (GetElem?.getElem! w__16 (Sail.Int.toNatChecked (i))) 48 48
            1#1))
        let w__17 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        let w__18 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
        writeReg ERRnFR (vectorUpdate w__17 (Sail.Int.toNatChecked (i))
          (Sail.BitVec.updateSubrange (GetElem?.getElem! w__18 (Sail.Int.toNatChecked (i))) 31 31
            1#1))
    (pure loop_vars))
  let w__19 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__20 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__19 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__20 0) 25 24 0b01#2))
  let w__21 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__22 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__21 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__22 0) 23 22 0b10#2))
  let w__23 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__24 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__23 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__24 0) 21 20 0b01#2))
  let w__25 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__26 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__25 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__26 0) 19 18 0b01#2))
  let w__27 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__28 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__27 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__28 0) 17 16 0b10#2))
  let w__29 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__30 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__29 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__30 0) 15 15 1#1))
  let w__31 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__32 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__31 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__32 0) 14 12 0b100#3))
  let w__33 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__34 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__33 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__34 0) 11 10 0b10#2))
  let w__35 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__36 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__35 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__36 0) 9 8 0b11#2))
  let w__37 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__38 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__37 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__38 0) 7 6 0b10#2))
  let w__39 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__40 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__39 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__40 0) 5 4 0b11#2))
  let w__41 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  let w__42 ← (( do readReg ERRnFR ) : SailM (Vector (BitVec 64) 4) )
  writeReg ERRnFR (vectorUpdate w__41 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__42 0) 1 0 0b10#2))
  let w__43 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__43 31 24 (Zeros (n := 8)))
  let w__44 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  let w__45 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  let w__46 : (BitVec 8) :=
    if ((IsZero (_get_PMCR_EL0_Type_IMP w__45)) : Bool)
    then (Zeros (n := 8))
    else CFG_PMCR_IDCODE
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__44 23 16 w__46)
  let w__47 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  let w__48 ← (( do readReg NUM_PMU_COUNTERS ) : SailM Int )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__47 15 11 (integer_subrange w__48 4 0))
  let w__49 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__49 2 2 0#1)
  let w__50 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__50 1 1 0#1)
  writeReg PMCEID0_EL0 (Mk_PMCEID0_EL0_Type
    (Sail.BitVec.zeroExtend 0b111101001000000000100000000100000001#36 64))
  writeReg PMCEID1_EL0 (Mk_PMCEID1_EL0_Type (Zeros (n := 64)))
  let w__51 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__51 31 28 0b0000#4)
  let w__52 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__52 21 21 1#1)
  let w__53 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__53 19 19 0#1)
  let w__54 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__54 18 18 0#1)
  let w__55 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__55 17 17 0#1)
  let w__56 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__56 16 16 0#1)
  let w__57 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__57 15 15 1#1)
  let w__58 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__58 14 14 1#1)
  let w__59 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__59 13 8 0b111111#6)
  let w__60 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  let w__61 ← (( do readReg NUM_PMU_COUNTERS ) : SailM Int )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__60 7 0 (0b000#3 +++ (integer_subrange w__61 4 0)))
  let w__62 ← (( do readReg PMDEVTYPE ) : SailM (BitVec 32) )
  writeReg PMDEVTYPE (Sail.BitVec.updateSubrange w__62 7 4 0b0001#4)
  let w__63 ← (( do readReg PMDEVTYPE ) : SailM (BitVec 32) )
  writeReg PMDEVTYPE (Sail.BitVec.updateSubrange w__63 3 0 0b0110#4)
  let w__64 ← (( do readReg PMPIDR0 ) : SailM (BitVec 32) )
  writeReg PMPIDR0 (Sail.BitVec.updateSubrange w__64 7 0 0b00001111#8)
  let w__65 ← (( do readReg PMPIDR1 ) : SailM (BitVec 32) )
  writeReg PMPIDR1 (Sail.BitVec.updateSubrange w__65 7 4 0b1011#4)
  let w__66 ← (( do readReg PMPIDR1 ) : SailM (BitVec 32) )
  writeReg PMPIDR1 (Sail.BitVec.updateSubrange w__66 3 0 0b1101#4)
  let w__67 ← (( do readReg PMPIDR2 ) : SailM (BitVec 32) )
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange w__67 7 4 0b0000#4)
  let w__68 ← (( do readReg PMPIDR2 ) : SailM (BitVec 32) )
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange w__68 3 3 1#1)
  let w__69 ← (( do readReg PMPIDR2 ) : SailM (BitVec 32) )
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange w__69 2 0 0b011#3)
  let w__70 ← (( do readReg PMPIDR3 ) : SailM (BitVec 32) )
  writeReg PMPIDR3 (Sail.BitVec.updateSubrange w__70 7 4 0b0000#4)
  let w__71 ← (( do readReg PMPIDR3 ) : SailM (BitVec 32) )
  writeReg PMPIDR3 (Sail.BitVec.updateSubrange w__71 3 0 0b0000#4)
  let w__72 ← (( do readReg PMPIDR4 ) : SailM (BitVec 32) )
  writeReg PMPIDR4 (Sail.BitVec.updateSubrange w__72 7 4 0b0000#4)
  let w__73 ← (( do readReg PMPIDR4 ) : SailM (BitVec 32) )
  writeReg PMPIDR4 (Sail.BitVec.updateSubrange w__73 3 0 0b0100#4)
  let w__74 ← (( do readReg PMCIDR0 ) : SailM (BitVec 32) )
  writeReg PMCIDR0 (Sail.BitVec.updateSubrange w__74 7 0 0b00001101#8)
  let w__75 ← (( do readReg PMCIDR1 ) : SailM (BitVec 32) )
  writeReg PMCIDR1 (Sail.BitVec.updateSubrange w__75 7 4 0b1001#4)
  let w__76 ← (( do readReg PMCIDR1 ) : SailM (BitVec 32) )
  writeReg PMCIDR1 (Sail.BitVec.updateSubrange w__76 3 0 0b0000#4)
  let w__77 ← (( do readReg PMCIDR2 ) : SailM (BitVec 32) )
  writeReg PMCIDR2 (Sail.BitVec.updateSubrange w__77 7 0 0b00000101#8)
  let w__78 ← (( do readReg PMCIDR3 ) : SailM (BitVec 32) )
  writeReg PMCIDR3 (Sail.BitVec.updateSubrange w__78 7 0 0b10110001#8)
  let w__79 ← (( do readReg __CNTbase_frequency ) : SailM (BitVec 32) )
  writeReg CNTFID0 (Mk_CNTFID0_Type w__79)
  let w__80 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__80 51 48 0b0001#4)
  let w__81 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__81 39 36 0b1111#4)
  let w__82 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__82 35 32 0b0010#4)
  let w__83 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__83 43 40 0b0001#4)
  let w__84 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  let w__85 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__84 31 28
    (integer_subrange (w__85 -i 1) 3 0))
  let w__86 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  let w__87 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__86 23 20
    (integer_subrange (w__87 -i 1) 3 0))
  let w__88 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  let w__89 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__88 15 12
    (integer_subrange (w__89 -i 1) 3 0))
  let w__90 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__90 7 4 0b0001#4)
  let w__91 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__91 3 0 0b1001#4)
  let w__92 ← (( do (IsFeatureImplemented FEAT_RME) ) : SailM Bool )
  if (w__92 : Bool)
  then
    (do
      let w__93 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__93 55 52 0b0001#4)
      let w__94 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
      let w__95 ← (( do readReg __rme_l0gptsz ) : SailM (BitVec 4) )
      writeReg GPCCR_EL3 (Sail.BitVec.updateSubrange w__94 23 20 w__95))
  else
    (do
      let w__96 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__96 55 52 0b0000#4))
  let w__97 ← (( do (IsFeatureImplemented FEAT_BRBE) ) : SailM Bool )
  if (w__97 : Bool)
  then
    (do
      let w__98 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__98 55 52 0b0010#4)
      let w__99 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
      writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange w__99 15 12 0b0101#4)
      let w__100 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
      writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange w__100 11 8 0b0000#4)
      let w__101 ← (( do readReg BRBIDR0_EL1 ) : SailM (BitVec 64) )
      let w__102 ← (( do readReg NUM_BRBE_RECORDS ) : SailM Int )
      writeReg BRBIDR0_EL1 (Sail.BitVec.updateSubrange w__101 7 0 (integer_subrange w__102 7 0)))
  else (pure (()))
  let w__103 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__103 47 44 0b0000#4)
  let w__104 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__104 43 40 0b0000#4)
  let w__105 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__105 39 36 0b0000#4)
  let w__106 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__106 35 32 0b0000#4)
  let w__107 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__107 31 28 0b0000#4)
  let w__108 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__108 23 20 0b0000#4)
  let w__109 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__109 19 16 0b0000#4)
  let w__110 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__110 15 12 0b0001#4)
  let w__111 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__111 11 8 0b0001#4)
  let w__112 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__112 7 4 0b0010#4)
  let w__113 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__113 3 0 0b0000#4)
  let w__114 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__114 43 40 0b0011#4)
  let w__115 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__115 35 32 0b0011#4)
  let w__116 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__116 39 36 0b0010#4)
  let w__117 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__117 47 44 0b0001#4)
  let w__118 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__118 59 56 0b0001#4)
  let w__119 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__119 63 60 0b0010#4)
  let w__120 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__120 31 28 0b0001#4)
  let w__121 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__121 23 20 0b0010#4)
  let w__122 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__122 27 24 0b0000#4)
  let w__123 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__123 19 16 0b0000#4)
  let w__124 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__124 15 12 0b0001#4)
  let w__125 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__125 11 8 0b0001#4)
  let w__126 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__126 7 4 0b0010#4)
  let w__127 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  let w__128 ← (( do (EncodePARange ()) ) : SailM (BitVec 4) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__127 3 0 w__128)
  let w__129 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
  let w__130 ← (( do (EncodeVARange ()) ) : SailM (BitVec 4) )
  writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__129 19 16 w__130)
  let w__131 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__131 31 28 0b0000#4)
  let w__132 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__132 27 24 0b0000#4)
  let w__133 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__133 23 20 0b0000#4)
  let w__134 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__134 19 16 0b0000#4)
  let w__135 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__135 11 8 0b0000#4)
  let w__136 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__136 15 12 0b0000#4)
  let w__137 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__137 7 4 0b0000#4)
  let w__138 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__138 3 0 0b0000#4)
  let w__139 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__139 35 32 0b0001#4)
  let w__140 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__140 15 12 0b0001#4)
  let w__141 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__141 11 8 0b0001#4)
  let w__142 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__142 7 4 0b0001#4)
  let w__143 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__143 3 0 0b0010#4)
  let w__144 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__144 63 60 0b0001#4)
  let w__145 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__145 59 56 0b0010#4)
  let w__146 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange w__146 3 0 0b0001#4)
  let w__147 ← (( do readReg ID_PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR2_EL1 (Sail.BitVec.updateSubrange w__147 7 4 0b0001#4)
  let w__148 ← (( do (HaveCNTSCExt ()) ) : SailM Bool )
  if (w__148 : Bool)
  then
    (do
      let w__149 ← (( do readReg CNTID ) : SailM (BitVec 32) )
      writeReg CNTID (Sail.BitVec.updateSubrange w__149 3 0 0b0001#4))
  else (pure (()))
  let w__150 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__150 47 44 0b0001#4)
  let w__151 ← (( do readReg AMCIDR0 ) : SailM (BitVec 32) )
  writeReg AMCIDR0 (Sail.BitVec.updateSubrange w__151 7 0 0b00001101#8)
  let w__152 ← (( do readReg AMCIDR1 ) : SailM (BitVec 32) )
  writeReg AMCIDR1 (Sail.BitVec.updateSubrange w__152 7 4 0b1001#4)
  let w__153 ← (( do readReg AMCIDR2 ) : SailM (BitVec 32) )
  writeReg AMCIDR2 (Sail.BitVec.updateSubrange w__153 7 0 0b00000101#8)
  let w__154 ← (( do readReg AMCIDR3 ) : SailM (BitVec 32) )
  writeReg AMCIDR3 (Sail.BitVec.updateSubrange w__154 7 0 0b10110001#8)
  let w__155 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__155 7 0 0b00010011#8)
  let w__156 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__156 13 8 0b111111#6)
  let w__157 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__157 24 24 1#1)
  let w__158 ← (( do readReg AMCFGR_EL0 ) : SailM (BitVec 64) )
  let w__159 ← (( do readReg NUM_AMU_COUNTER_GROUPS ) : SailM Int )
  writeReg AMCFGR_EL0 (Sail.BitVec.updateSubrange w__158 31 28 (integer_subrange (w__159 -i 1) 3 0))
  let w__160 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
  let w__161 ← (( do readReg NUM_AMU_CG0_MONITORS ) : SailM Int )
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange w__160 7 0 (integer_subrange w__161 7 0))
  let w__162 ← (( do readReg AMCGCR_EL0 ) : SailM (BitVec 64) )
  let w__163 ← (( do readReg NUM_AMU_CG1_MONITORS ) : SailM Int )
  writeReg AMCGCR_EL0 (Sail.BitVec.updateSubrange w__162 15 8 (integer_subrange w__163 7 0))
  let w__164 ← (( do readReg AMDEVARCH ) : SailM (BitVec 32) )
  writeReg AMDEVARCH (Sail.BitVec.updateSubrange w__164 31 21 (0b0100#4 +++ 0b0111011#7))
  let w__165 ← (( do readReg AMDEVARCH ) : SailM (BitVec 32) )
  writeReg AMDEVARCH (Sail.BitVec.updateSubrange w__165 20 20 1#1)
  let w__166 ← (( do readReg AMDEVARCH ) : SailM (BitVec 32) )
  writeReg AMDEVARCH (Sail.BitVec.updateSubrange w__166 15 0 (0b0000#4 +++ 0b101001100110#12))
  let w__167 ← (( do readReg AMDEVTYPE ) : SailM (BitVec 32) )
  writeReg AMDEVTYPE (Sail.BitVec.updateSubrange w__167 7 4 0b0001#4)
  let w__168 ← (( do readReg AMDEVTYPE ) : SailM (BitVec 32) )
  writeReg AMDEVTYPE (Sail.BitVec.updateSubrange w__168 3 0 0b0110#4)
  let w__169 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  let w__170 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  writeReg AMEVTYPER0_EL0 (vectorUpdate w__169 0
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__170 0) 15 0 0b0000000000010001#16))
  let w__171 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  let w__172 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  writeReg AMEVTYPER0_EL0 (vectorUpdate w__171 1
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__172 1) 15 0 0b0100000000000100#16))
  let w__173 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  let w__174 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  writeReg AMEVTYPER0_EL0 (vectorUpdate w__173 2
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__174 2) 15 0 0b0000000000001000#16))
  let w__175 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  let w__176 ← (( do readReg AMEVTYPER0_EL0 ) : SailM (Vector (BitVec 64) 4) )
  writeReg AMEVTYPER0_EL0 (vectorUpdate w__175 3
    (Sail.BitVec.updateSubrange (GetElem?.getElem! w__176 3) 15 0 0b0100000000000101#16))
  let w__177 ← (( do readReg AMIIDR ) : SailM (BitVec 32) )
  writeReg AMIIDR (Sail.BitVec.updateSubrange w__177 11 0 0b010000111011#12)
  let w__178 ← (( do readReg AMPIDR1 ) : SailM (BitVec 32) )
  writeReg AMPIDR1 (Sail.BitVec.updateSubrange w__178 7 4 0b1011#4)
  let w__179 ← (( do readReg AMPIDR2 ) : SailM (BitVec 32) )
  writeReg AMPIDR2 (Sail.BitVec.updateSubrange w__179 3 3 1#1)
  let w__180 ← (( do readReg AMPIDR2 ) : SailM (BitVec 32) )
  writeReg AMPIDR2 (Sail.BitVec.updateSubrange w__180 2 0 0b011#3)
  let w__181 ← (( do readReg AMPIDR4 ) : SailM (BitVec 32) )
  writeReg AMPIDR4 (Sail.BitVec.updateSubrange w__181 3 0 0b0100#4)
  let w__182 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__182 51 48 0b0001#4)
  let w__183 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__183 31 28 0b0000#4)
  let w__184 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__184 27 24 0b0000#4)
  let w__185 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__185 23 20 0b0000#4)
  let w__186 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__186 19 16 0b0000#4)
  let w__187 ← (( do readReg MPIDR_EL1 ) : SailM (BitVec 64) )
  let w__188 ← (( do readReg CFG_MPIDR ) : SailM (BitVec 32) )
  writeReg MPIDR_EL1 (Sail.BitVec.updateSubrange w__187 31 0 w__188)
  let w__189 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__189 39 32 0b00000000#8)
  let w__190 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__190 30 30 0#1)
  let w__191 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__191 24 24 0#1)
  let w__192 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__192 23 16 0b00000000#8)
  let w__193 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__193 15 8 0b00000000#8)
  let w__194 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__194 7 0 0b00000000#8)
  let w__195 ← (( do (VMPIDR_read ()) ) : SailM (BitVec 32) )
  (VMPIDR_write (_update_VMPIDR_Type_M w__195 1#1))
  if ((HasArchVersion v8Ap1) : Bool)
  then
    (do
      let w__196 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__196 27 24 0b0001#4)
      let w__197 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__197 23 20 0b0010#4)
      let w__198 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__198 31 28 0b0001#4)
      let w__199 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__199 19 16 0b0001#4)
      let w__200 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__200 11 8 0b0001#4)
      let w__201 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__201 15 12 0b0001#4)
      let w__202 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__202 3 0 0b0010#4))
  else (pure (()))
  let w__203 ← (( do (IsFeatureImplemented FEAT_CRC32) ) : SailM Bool )
  if (w__203 : Bool)
  then
    (do
      let w__204 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__204 19 16 0b0001#4)
      let w__205 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__205 19 16 0b0001#4))
  else (pure (()))
  let w__206 ← (( do (IsFeatureImplemented FEAT_VMID16) ) : SailM Bool )
  if (w__206 : Bool)
  then
    (do
      let w__207 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__207 7 4 0b0010#4))
  else (pure (()))
  let w__208 ← (( do (IsFeatureImplemented FEAT_PAN) ) : SailM Bool )
  if (w__208 : Bool)
  then
    (do
      let w__209 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__209 23 20 0b0001#4)
      let w__210 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__210 19 16 0b0001#4))
  else (pure (()))
  let w__211 ← (( do (IsFeatureImplemented FEAT_AES) ) : SailM Bool )
  if ((! w__211) : Bool)
  then
    (do
      let w__212 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__212 7 4 0b0000#4))
  else (pure (()))
  let w__213 ← (( do (IsFeatureImplemented FEAT_AES) ) : SailM Bool )
  if (w__213 : Bool)
  then
    (do
      let w__214 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__214 7 4 0b0001#4))
  else (pure (()))
  let w__217 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_AES)) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_PMULL))
    else (pure false) ) : SailM Bool )
  if (w__217 : Bool)
  then
    (do
      let w__218 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__218 7 4 0b0010#4))
  else (pure (()))
  let w__219 ← (( do (IsFeatureImplemented FEAT_SHA1) ) : SailM Bool )
  if ((! w__219) : Bool)
  then
    (do
      let w__220 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__220 11 8 0b0000#4))
  else (pure (()))
  let w__221 ← (( do (IsFeatureImplemented FEAT_SHA256) ) : SailM Bool )
  if ((! w__221) : Bool)
  then
    (do
      let w__222 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__222 15 12 0b0000#4))
  else (pure (()))
  if ((HasArchVersion v8Ap2) : Bool)
  then
    (do
      let w__223 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__223 31 28 0b0001#4)
      let w__224 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__224 23 20 0b0010#4)
      let w__225 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__225 3 0 0b0001#4)
      let w__226 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__226 7 4 0b0001#4)
      let w__227 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__227 11 8 0b0001#4)
      let w__228 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__228 15 12 0b0001#4)
      let w__229 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__229 19 16 0b0010#4)
      let w__230 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__230 39 36 0b0001#4)
      let w__231 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__231 11 8 0b0001#4)
      let w__232 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__232 15 12 0b0001#4)
      let w__233 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__233 23 20 0b0001#4)
      let w__234 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__234 7 4 0b0001#4)
      if ((HaveEL EL2) : Bool)
      then
        (do
          let w__235 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
          writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__235 31 28 0b0010#4)
          let w__236 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__236 59 56 0b0010#4))
      else
        (do
          let w__237 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
          writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__237 31 28 0b0000#4)
          let w__238 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__238 59 56 0b0000#4))
      let w__239 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__239 31 28 0b0000#4)
      let w__240 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__240 63 63 1#1)
      let w__241 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__241 32 32 1#1)
      let w__242 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__242 34 34 1#1)
      let w__243 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__243 35 35 1#1)
      let w__244 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__244 39 36 0b1111#4)
      let w__245 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__245 48 48 1#1)
      let w__246 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__246 55 52 0b1111#4)
      let w__247 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__247 43 40 0b0001#4)
      let w__248 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__248 39 36 0b0001#4)
      let w__249 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__249 3 0 0b0010#4)
      let w__250 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__250 7 4 0b0001#4)
      let w__251 ← (( do (HaveDoPD ()) ) : SailM Bool )
      if (w__251 : Bool)
      then
        (do
          let w__252 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
          writeReg EDDEVID (Sail.BitVec.updateSubrange w__252 7 4 0b0001#4)
          let w__253 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
          writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__253 19 16 0b0001#4))
      else
        (do
          let w__254 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
          writeReg EDDEVID (Sail.BitVec.updateSubrange w__254 7 4 0b0000#4)
          let w__255 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
          writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__255 19 16 0b0000#4))
      let w__256 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__256 43 40 0b0001#4)
      let w__257 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__257 35 32 0b0001#4)
      let w__258 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__258 19 16 0b0001#4)
      let w__259 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__259 7 4 0b0010#4)
      let w__260 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__260 3 0 0b0001#4)
      let w__261 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__261 23 20 0b0001#4)
      let w__262 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__262 47 44 0b0001#4)
      let w__263 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__263 23 20 0b0010#4)
      let w__264 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__264 47 44 0b0010#4)
      let w__265 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__265 51 48 0b0001#4)
      let w__266 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__266 23 20 0b0001#4)
      let w__267 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__267 47 44 0b0001#4)
      let w__268 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__268 55 52 0b0001#4)
      let w__269 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__269 27 24 0b0001#4))
  else (pure (()))
  if ((HasArchVersion v8Ap6) : Bool)
  then
    (do
      let w__270 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__270 47 44 0b0010#4)
      let w__271 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__271 23 20 0b0010#4)
      let w__272 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__272 55 52 0b0001#4)
      let w__273 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__273 59 56 0b0001#4))
  else (pure (()))
  let w__274 ← (( do (IsFeatureImplemented FEAT_DotProd) ) : SailM Bool )
  if (w__274 : Bool)
  then
    (do
      let w__275 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__275 47 44 0b0001#4))
  else (pure (()))
  let w__276 ← (( do (IsFeatureImplemented FEAT_FP16) ) : SailM Bool )
  if (w__276 : Bool)
  then
    (do
      let w__277 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__277 19 16 0b0001#4)
      let w__278 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__278 23 20 0b0001#4))
  else (pure (()))
  let w__279 ← (( do (IsFeatureImplemented FEAT_AA32HPD) ) : SailM Bool )
  if (w__279 : Bool)
  then
    (do
      let w__280 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__280 15 12 0b0010#4)
      let w__281 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__281 19 16 0b0010#4))
  else (pure (()))
  let w__282 ← (( do (HaveMPAMExt ()) ) : SailM Bool )
  if (w__282 : Bool)
  then
    (do
      let w__283 ← (( do readReg __empam_force_ns_implemented ) : SailM Bool )
      if (w__283 : Bool)
      then
        (do
          writeReg __mpam_major CFG_MPAM_v0p1
          writeReg __mpam_frac CFG_MPAM_frac_v0p1
          let w__284 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__284 60 60 1#1))
      else
        (do
          writeReg __mpam_major CFG_MPAM_v1p1
          writeReg __mpam_frac CFG_MPAM_frac_v1p1)
      let w__285 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      let w__286 ← (( do readReg __mpam_major ) : SailM (BitVec 4) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__285 43 40 w__286)
      let w__287 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
      let w__288 ← (( do readReg __mpam_partid_max ) : SailM (BitVec 16) )
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__287 15 0 w__288)
      let w__289 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
      let w__290 ← (( do readReg __mpam_pmg_max ) : SailM (BitVec 8) )
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__289 39 32 w__290)
      let w__291 ← (( do readReg __mpam_has_hcr ) : SailM Bool )
      if (w__291 : Bool)
      then
        (do
          let w__292 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__292 17 17 1#1)
          let w__293 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          let w__294 ← (( do readReg __mpam_vpmr_max ) : SailM (BitVec 3) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__293 20 18 w__294))
      else (pure (()))
      let w__295 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      let w__296 ← (( do readReg __mpam_frac ) : SailM (BitVec 4) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__295 19 16 w__296)
      let w__301 ← (( do
        if ((← do
             let w__297 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
             (pure ((((BitVec.toNat (_get_ID_AA64PFR0_EL1_Type_MPAM w__297)) >b 1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__298 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
                 let b__0 := (_get_ID_AA64PFR0_EL1_Type_MPAM w__298)
                 (pure ((if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
                   then true
                   else false : Bool)))) : Bool)
            then
              (do
                let w__299 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
                (pure ((((_get_ID_AA64PFR1_EL1_Type_MPAM_frac w__299) == 0b0001#4) : Bool))))
            else (pure false)) ) : SailM Bool )
      ArmFull.assert w__301 "sail-arm/reset.sail:720.56-720.57"
      let w__302 ← (( do readReg __empam_sdeflt_implemented ) : SailM Bool )
      if (w__302 : Bool)
      then
        (do
          let w__303 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__303 61 61 1#1))
      else (pure (()))
      let w__304 ← (( do readReg __empam_tidr_implemented ) : SailM Bool )
      if (w__304 : Bool)
      then
        (do
          let w__305 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__305 58 58 1#1))
      else (pure (())))
  else (pure (()))
  let w__307 ← (( do
    if (((HasArchVersion v9Ap2) : Bool) : Bool)
    then
      (do
        (HaveRME ()))
    else (pure false) ) : SailM Bool )
  if (w__307 : Bool)
  then
    (do
      let w__308 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__308 59 59 1#1)
      let w__309 ← (( do readReg __mpam_has_altsp ) : SailM Bool )
      if (w__309 : Bool)
      then
        (do
          let w__310 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__310 57 57 1#1))
      else (pure (())))
  else (pure (()))
  if ((HasArchVersion v8Ap3) : Bool)
  then
    (do
      let w__311 ← (( do (IsFeatureImplemented FEAT_PACQARMA3) ) : SailM Bool )
      if (w__311 : Bool)
      then
        (do
          let w__312 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__312 11 8 0b0001#4)
          let w__313 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__313 15 12 0b0101#4)
          let w__314 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__314 7 4 0b0000#4)
          let w__315 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__315 27 24 0b0000#4))
      else (pure (()))
      let w__316 ← (( do (IsFeatureImplemented FEAT_PACQARMA5) ) : SailM Bool )
      if (w__316 : Bool)
      then
        (do
          let w__317 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__317 11 8 0b0000#4)
          let w__318 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__318 15 12 0b0000#4)
          let w__319 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__319 7 4 0b0101#4)
          let w__320 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__320 27 24 0b0001#4))
      else (pure (()))
      let w__321 ← (( do (IsFeatureImplemented FEAT_CONSTPACFIELD) ) : SailM Bool )
      if (w__321 : Bool)
      then
        (do
          let w__322 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__322 27 24 0b0001#4))
      else
        (do
          let w__323 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__323 27 24 0b0000#4))
      let w__324 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__324 15 12 0b0001#4)
      let w__325 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__325 19 16 0b0001#4)
      let w__326 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__326 3 0 0b0001#4)
      let w__327 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__327 27 24 0b0001#4)
      let w__328 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__328 27 24 0b0001#4)
      let w__329 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__329 31 28 0b0001#4)
      let w__330 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__330 23 20 0b0001#4)
      let w__331 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__331 23 20 0b0001#4))
  else (pure (()))
  if ((HasArchVersion v8Ap4) : Bool)
  then
    (do
      let w__332 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__332 23 20 0b0010#4)
      let w__333 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__333 31 28 0b0001#4)
      let w__334 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__334 35 32 0b0001#4)
      let w__335 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__335 51 48 0b0001#4)
      let w__336 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__336 43 40 0b0001#4)
      let w__337 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__337 27 24 0b0010#4)
      let w__338 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__338 3 0 0b1001#4)
      let w__340 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then
          (do
            let w__339 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__339) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__340 : Bool)
      then
        (do
          let w__341 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__341 7 4 0b0000#4))
      else
        (do
          let w__342 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          let w__343 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__342 7 4
            (_get_ID_DFR0_EL1_Type_CopDbg w__343)))
      let w__344 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__344 39 36 0b0001#4)
      let w__345 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__345 59 56 0b0010#4)
      let w__346 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__346 55 52 0b0000#4)
      let w__347 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__347 51 48 0b0001#4)
      let w__348 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__348 11 8 0b0001#4)
      let w__349 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__349 31 28 0b0010#4)
      let w__350 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      let w__351 ← (( do readReg __block_bbm_implemented ) : SailM Int )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__350 55 52
        (integer_subrange w__351 3 0))
      let w__352 ← (( do (IsFeatureImplemented FEAT_SHA512) ) : SailM Bool )
      if (w__352 : Bool)
      then
        (do
          let w__353 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__353 15 12 0b0010#4))
      else (pure (()))
      let w__354 ← (( do (IsFeatureImplemented FEAT_SHA3) ) : SailM Bool )
      if (w__354 : Bool)
      then
        (do
          let w__355 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__355 35 32 0b0001#4))
      else (pure (()))
      let w__356 ← (( do (IsFeatureImplemented FEAT_SM3) ) : SailM Bool )
      if (w__356 : Bool)
      then
        (do
          let w__357 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__357 39 36 0b0001#4))
      else (pure (()))
      let w__358 ← (( do (IsFeatureImplemented FEAT_SM4) ) : SailM Bool )
      if (w__358 : Bool)
      then
        (do
          let w__359 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__359 43 40 0b0001#4))
      else (pure (()))
      let w__360 ← (( do (HavePMUv3p4 ()) ) : SailM Bool )
      if (w__360 : Bool)
      then
        (do
          let w__361 ← (( do (HavePMUv3TH ()) ) : SailM Bool )
          if (w__361 : Bool)
          then
            (do
              let w__362 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
              writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__362 23 20 0b1100#4))
          else (pure (()))
          let w__363 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
          writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__363 19 16 0b0100#4)
          let w__364 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
          writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__364 15 8 0b00000011#8))
      else (pure (())))
  else (pure (()))
  let w__365 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__365 7 4 0b0010#4)
  if ((HasArchVersion v8Ap5) : Bool)
  then
    (do
      let w__366 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__366 55 52 0b0010#4)
      let w__367 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__367 35 32 0b0001#4)
      let w__368 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__368 3 0 0b0001#4)
      let w__369 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__369 27 24 0b0110#4)
      let w__370 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__370 63 60 0b0001#4)
      let w__371 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__371 63 60 0b0001#4)
      let w__372 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
      if (w__372 : Bool)
      then
        (do
          let w__373 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__373 11 8 0b0010#4))
      else (pure (()))
      let w__374 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__374 11 8 0b0110#4)
      let w__375 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
      writeReg EDDFR (Sail.BitVec.updateSubrange w__375 11 8 0b0000#4)
      let w__376 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__376 15 12 0b0001#4)
      let w__377 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__377 19 16 0b0001#4))
  else (pure (()))
  let w__378 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__378 23 20 0b0000#4)
  let w__379 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__379 11 8 0b0000#4)
  if ((HasArchVersion v8Ap6) : Bool)
  then
    (do
      let w__380 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__380 35 32 0b0001#4))
  else (pure (()))
  let w__381 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__381 19 16 0b0010#4)
  let w__382 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__382 51 48 0b0001#4)
  let w__383 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__383 3 0 0b0001#4)
  if ((HasArchVersion v8Ap7) : Bool)
  then
    (do
      let w__384 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__384 43 40 0b0001#4)
      if (((! (HaveEL EL3)) && (HaveEL EL2)) : Bool)
      then
        (do
          writeReg HCRX_EL2 (Mk_HCRX_EL2_Type (Zeros (n := 64))))
      else (pure (()))
      let w__385 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__385 47 44 0b0001#4)
      let w__386 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__386 11 8 0b0111#4)
      let w__387 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__387 27 24 0b0111#4)
      let w__388 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__388 35 32 0b0011#4)
      let w__389 ← (( do readReg __feat_rpres ) : SailM Bool )
      if (w__389 : Bool)
      then
        (do
          let w__390 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__390 7 4 0b0001#4))
      else (pure (()))
      let w__391 ← (( do (Have52BitIPAAndPASpaceExt ()) ) : SailM Bool )
      if (w__391 : Bool)
      then
        (do
          let w__392 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__392 31 28 0b0001#4)
          let w__393 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__393 43 40 0b0011#4)
          let w__394 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__394 23 20 0b0010#4)
          let w__395 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__395 35 32 0b0011#4))
      else (pure (()))
      let w__396 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__396 59 56 0b0001#4)
      let w__397 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__397 3 0 0b0010#4)
      let w__398 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__398 23 20 0b0011#4)
      let w__399 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__399 11 8 0b0011#4)
      let w__400 ← (( do (HaveFeatLS64_ACCDATA ()) ) : SailM Bool )
      if (w__400 : Bool)
      then
        (do
          let w__401 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__401 63 60 0b0011#4))
      else
        (do
          let w__402 ← (( do (HaveFeatLS64_V ()) ) : SailM Bool )
          if (w__402 : Bool)
          then
            (do
              let w__403 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
              writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__403 63 60 0b0010#4))
          else
            (do
              let w__404 ← (( do (HaveFeatLS64 ()) ) : SailM Bool )
              if (w__404 : Bool)
              then
                (do
                  let w__405 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
                  writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__405 63 60 0b0001#4))
              else
                (do
                  let w__406 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
                  writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__406 63 60 0b0000#4)))))
  else (pure (()))
  let w__407 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (BitVec.update w__407 9 (Bit 1#1))
  let w__408 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__408 31 27 0b11111#5)
  let w__409 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__409 18 18 1#1)
  let w__410 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__410 17 17 1#1)
  let w__411 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__411 16 16 1#1)
  let w__412 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__412 8 8 1#1)
  let w__413 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__413 10 10 1#1)
  let w__414 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__414 4 0 0b00111#5)
  let w__415 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__415 23 19 0b01111#5)
  let w__416 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__416 5 5 1#1)
  let w__417 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__417 4 4 0#1)
  let w__418 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__418 3 0 0b0000#4)
  let w__419 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__419 32 32 0#1)
  let w__420 ← (( do (IsFeatureImplemented FEAT_SME) ) : SailM Bool )
  if (w__420 : Bool)
  then
    (do
      let w__421 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
      writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__421 31 24 0b01000001#8)
      let w__422 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
      writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__422 15 15 1#1)
      let w__423 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__423 27 24 0b0001#4)
      let w__424 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__424 7 4 0b0001#4))
  else (pure (()))
  if ((HasArchVersion v9Ap3) : Bool)
  then
    (do
      let w__425 ← (( do (IsFeatureImplemented FEAT_MEC) ) : SailM Bool )
      if (w__425 : Bool)
      then
        (do
          let w__426 ← (( do readReg MECIDR_EL2 ) : SailM (BitVec 64) )
          let w__427 ← (( do readReg __mecid_width ) : SailM (BitVec 4) )
          writeReg MECIDR_EL2 (Sail.BitVec.updateSubrange w__426 3 0 w__427)
          let w__428 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__428 31 28 0b0001#4))
      else (pure (())))
  else (pure (()))
  let w__429 ← (( do (IsFeatureImplemented FEAT_SME2) ) : SailM Bool )
  if (w__429 : Bool)
  then
    (do
      let w__430 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__430 27 24 0b0010#4)
      let w__431 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__431 59 56 0b0001#4)
      let w__432 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__432 47 44 0b0101#4)
      let w__433 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__433 33 33 1#1))
  else (pure (()))
  if ((HasArchVersion v8Ap8) : Bool)
  then
    (do
      let w__434 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__434 39 36 0b0010#4)
      let w__435 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__435 3 0 0b0010#4)
      let w__436 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__436 39 36 0b0001#4)
      let w__437 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__437 31 28 0b0001#4)
      let w__438 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__438 19 16 0b0001#4)
      let w__439 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__439 23 20 0b0001#4)
      let w__440 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
      if (w__440 : Bool)
      then
        (do
          let w__441 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__441 35 32 0b0100#4))
      else (pure (()))
      let w__442 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__442 63 60 0b0001#4)
      let w__443 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__443 7 4 0b0001#4)
      let w__444 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__444 3 0 0b1010#4)
      let w__445 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__445 3 0 0b1010#4)
      let w__447 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then
          (do
            let w__446 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__446) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__447 : Bool)
      then
        (do
          let w__448 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__448 7 4 0b0000#4))
      else
        (do
          let w__449 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          let w__450 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__449 7 4
            (_get_ID_DFR0_EL1_Type_CopDbg w__450)))
      let w__451 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__451 55 52 0b0001#4)
      let w__452 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__452 55 52 0b0001#4)
      let w__453 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__453 59 56 0b0001#4)
      let w__454 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__454 11 8 0b1000#4)
      let w__455 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__455 27 24 0b1000#4))
  else (pure (()))
  let w__456 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__456 27 24 0b0001#4)
  let w__457 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__457 19 16 0b0001#4)
  let w__458 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__458 15 12 0b0001#4)
  let w__459 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__459 18 18 0#1)
  let w__460 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__460 17 17 0#1)
  let w__461 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__461 16 16 0#1)
  let w__462 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__462 15 15 0#1)
  let w__463 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__463 14 14 0#1)
  let w__464 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__464 13 13 0#1)
  let w__465 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__465 12 12 0#1)
  let w__466 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__466 11 11 0#1)
  let w__467 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__467 10 10 0#1)
  let w__468 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__468 9 9 0#1)
  let w__469 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__469 8 8 0#1)
  let w__470 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__470 7 7 0#1)
  let w__471 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__471 3 3 0#1)
  let w__472 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__472 2 2 0#1)
  let w__473 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__473 1 1 0#1)
  let w__474 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__474 0 0 0#1)
  let w__475 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__475 31 31 0#1)
  let w__476 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let w__479 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_VHE)) : Bool)
    then
      (do
        let w__478 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_E2H w__478) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__480 : Int :=
    if (w__479 : Bool)
    then 28
    else 20
  writeReg CPTR_EL2 (BitVec.update w__476 (Sail.Int.toNatChecked (w__480)) (Bit 0#1))
  let w__481 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__481 49 49 0#1)
  let w__482 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__482 52 52 0#1)
  let w__483 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__483 50 50 0#1)
  let w__484 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__484 44 44 0#1)
  let w__485 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__485 43 43 0#1)
  let w__486 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__486 42 42 0#1)
  let w__487 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__487 41 41 0#1)
  let w__488 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__488 40 40 0#1)
  let w__489 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__489 38 38 0#1)
  let w__490 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__490 37 37 0#1)
  let w__491 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__491 36 36 0#1)
  let w__492 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__492 33 33 0#1)
  let w__493 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__493 32 32 0#1)
  let w__494 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__494 31 31 0#1)
  let w__495 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__495 30 30 0#1)
  let w__496 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__496 29 29 0#1)
  let w__497 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__497 28 28 0#1)
  let w__498 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__498 27 27 0#1)
  let w__499 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__499 26 26 0#1)
  let w__500 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__500 25 25 0#1)
  let w__501 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__501 24 24 0#1)
  let w__502 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__502 23 23 0#1)
  let w__503 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__503 22 22 0#1)
  let w__504 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__504 21 21 0#1)
  let w__505 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__505 20 20 0#1)
  let w__506 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__506 19 19 0#1)
  let w__507 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__507 18 18 0#1)
  let w__508 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__508 17 17 0#1)
  let w__509 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__509 16 16 0#1)
  let w__510 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__510 15 15 0#1)
  let w__511 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__511 14 14 0#1)
  let w__512 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__512 13 13 0#1)
  let w__513 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__513 12 12 0#1)
  let w__514 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__514 11 10 0b00#2)
  let w__515 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__515 9 9 0#1)
  let w__516 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__516 8 8 0#1)
  let w__517 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__517 7 7 0#1)
  let w__518 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__518 6 6 0#1)
  let w__519 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__519 5 5 0#1)
  let w__520 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__520 4 4 0#1)
  let w__521 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__521 3 3 0#1)
  let w__522 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__522 2 2 0#1)
  let w__523 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__523 1 1 0#1)
  let w__524 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__524 0 0 0#1)
  let w__525 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__525 15 0 (Zeros (n := 16)))
  let w__526 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__526 31 31 0#1)
  let w__527 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__527 30 30 0#1)
  let w__528 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__528 27 27 0#1)
  let w__529 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__529 25 25 0#1)
  let w__530 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__530 13 13 0#1)
  let w__531 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__531 31 31 0#1)
  let w__532 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__532 30 30 0#1)
  let w__533 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__533 27 27 0#1)
  let w__534 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__534 25 25 0#1)
  let w__535 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__535 13 13 0#1)
  let w__536 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__536 28 28 0#1)
  let w__537 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__537 21 20 0b00#2)
  let w__538 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__538 31 31 0#1)
  let w__539 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__539 30 30 0#1)
  let w__540 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__540 27 27 0#1)
  let w__541 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__541 25 25 0#1)
  let w__542 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__542 13 13 0#1)
  let w__543 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__543 31 31 0#1)
  let w__544 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__544 30 30 0#1)
  let w__545 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__545 27 27 0#1)
  let w__546 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__546 25 25 0#1)
  let w__547 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__547 13 13 0#1)
  let w__548 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__548 24 24 1#1)
  let w__549 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__549 6 6 1#1)
  let w__550 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__550 19 16 0b0011#4)
  match SPEMaxRecordSize with
  | 64 =>
    (do
      let w__551 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
      writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__551 15 12 0b0110#4))
  | _ =>
    (do
      (Unreachable ()))
  let w__552 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__552 3 3 1#1)
  let w__553 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__553 2 2 1#1)
  let w__554 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__554 1 1 1#1)
  let w__555 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__555 0 0 1#1)
  let w__556 ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (w__556 : Bool)
  then
    (do
      let w__557 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__557 14 14 0#1)
      let w__558 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__558 13 12 0b10#2))
  else (pure (()))
  let w__559 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let w__560 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__559 4 0 (_get_PMCR_EL0_Type_N w__560))
  let w__561 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__561 0 0 1#1)
  let w__562 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__562 3 3 1#1)
  let w__563 ← (( do readReg ICC_SRE_EL1_S ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_S (Sail.BitVec.updateSubrange w__563 0 0 1#1)
  let w__564 ← (( do readReg ICC_SRE_EL1_NS ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_NS (Sail.BitVec.updateSubrange w__564 0 0 1#1)
  let w__565 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__565 0 0 1#1)
  let w__566 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__566 27 24 0b0100#4)
  let w__567 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  let w__568 ← (( do readReg __exclusive_granule_size ) : SailM (BitVec 4) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__567 23 20 w__568)
  let w__569 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__569 19 16 0b0100#4)
  let w__570 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__570 15 14 0b10#2)
  let w__571 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__571 3 0 0b0100#4)
  let w__572 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if (w__572 : Bool)
  then
    (do
      let w__573 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
      writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__573 37 32 0b000100#6))
  else (pure (()))
  let w__574 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if (w__574 : Bool)
  then
    (do
      let w__575 ← (( do readReg GMID_EL1 ) : SailM (BitVec 64) )
      let w__576 ← (( do readReg __gmid_log2_block_size ) : SailM Int )
      writeReg GMID_EL1 (Sail.BitVec.updateSubrange w__575 3 0 (integer_subrange w__576 3 0)))
  else (pure (()))
  let w__577 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__577 23 21 0b010#3)
  let w__578 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__578 20 18 0b011#3)
  let w__579 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_ExtRange w__579 1#1))
  let w__580 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_PRIbits w__580 0b100#3))
  let w__581 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_A3V w__581 1#1))
  let w__582 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_IDbits w__582 0b001#3))
  let w__583 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__583 19 19 1#1)
  let w__584 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__584 10 8 0b100#3)
  let w__585 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__585 13 11 0b001#3)
  let w__586 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__586 15 15 1#1)
  let w__587 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__587 31 29 0b100#3)
  let w__588 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__588 28 26 0b100#3)
  let w__589 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__589 25 23 0b001#3)
  let w__590 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__590 21 21 1#1)
  let w__591 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  let w__592 ← (( do (IsFeatureImplemented FEAT_CCIDX) ) : SailM Bool )
  let w__593 : Int :=
    if (w__592 : Bool)
    then 32
    else 13
  writeReg CCSIDR_EL1 (Mk_CCSIDR_EL1_Type
    (set_slice 24 w__591 (Sail.Int.toNatChecked (w__593)) (Sail.BitVec.zeroExtend 0xFF#8 24)))
  let w__594 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__594 23 3 (Sail.BitVec.zeroExtend 0x1#4 21))
  let w__595 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__595 2 0 0b010#3)
  let w__596 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR2_EL1 (Sail.BitVec.updateSubrange w__596 23 0 (Sail.BitVec.zeroExtend 0xFF#8 24))
  let w__597 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__597 3 0 0b0000#4)
  let w__598 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__598 7 4 0b0000#4)
  let w__599 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__599 15 12 0b0000#4)
  let w__600 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__600 3 3 (Sail.BitVec.extractLsb 0b10#2 1 1))
  let w__601 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__601 0 0 (Sail.BitVec.extractLsb 0b10#2 0 0))
  let w__602 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__602 1 0 0b11#2)
  let w__603 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__603 55 12 (Sail.BitVec.zeroExtend 0x22000#20 44))
  let w__604 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__605 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__604 11 8 (_get_ID_AA64DFR0_EL1_Type_PMUVer w__605))
  let w__606 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__606 11 0 0xA15#12)
  let w__607 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
  writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__607 7 4 0b0010#4)
  let w__608 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__608 15 12 0b1011#4)
  let w__609 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__609 20 20 1#1)
  let w__610 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__610 31 21 0b01000111011#11)
  let w__611 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
  writeReg EDDEVID (Sail.BitVec.updateSubrange w__611 27 24 0b0001#4)
  let w__612 ← (( do readReg EDDEVTYPE ) : SailM (BitVec 32) )
  writeReg EDDEVTYPE (Sail.BitVec.updateSubrange w__612 3 0 0b0101#4)
  let w__613 ← (( do readReg EDDEVTYPE ) : SailM (BitVec 32) )
  writeReg EDDEVTYPE (Sail.BitVec.updateSubrange w__613 7 4 0b0001#4)
  let w__614 ← (( do readReg EDPIDR0 ) : SailM (BitVec 32) )
  writeReg EDPIDR0 (Sail.BitVec.updateSubrange w__614 7 0 (Sail.BitVec.zeroExtend 0xF#4 8))
  let w__615 ← (( do readReg EDPIDR1 ) : SailM (BitVec 32) )
  writeReg EDPIDR1 (Sail.BitVec.updateSubrange w__615 3 0 0xD#4)
  let w__616 ← (( do readReg EDPIDR1 ) : SailM (BitVec 32) )
  writeReg EDPIDR1 (Sail.BitVec.updateSubrange w__616 7 4 (Sail.BitVec.truncate 0x0B#8 4))
  let w__617 ← (( do readReg EDPIDR2 ) : SailM (BitVec 32) )
  writeReg EDPIDR2 (Sail.BitVec.updateSubrange w__617 2 0 0b011#3)
  let w__618 ← (( do readReg EDPIDR2 ) : SailM (BitVec 32) )
  writeReg EDPIDR2 (Sail.BitVec.updateSubrange w__618 3 3 1#1)
  let w__619 ← (( do readReg EDCIDR0 ) : SailM (BitVec 32) )
  writeReg EDCIDR0 (Sail.BitVec.updateSubrange w__619 7 0 0x0D#8)
  let w__620 ← (( do readReg EDCIDR1 ) : SailM (BitVec 32) )
  writeReg EDCIDR1 (Sail.BitVec.updateSubrange w__620 7 4 0b1001#4)
  let w__621 ← (( do readReg EDCIDR2 ) : SailM (BitVec 32) )
  writeReg EDCIDR2 (Sail.BitVec.updateSubrange w__621 7 0 0x05#8)
  let w__622 ← (( do readReg EDCIDR3 ) : SailM (BitVec 32) )
  writeReg EDCIDR3 (Sail.BitVec.updateSubrange w__622 7 0 0xB1#8)
  let w__623 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__624 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__623 7 4 (_get_ID_AA64DFR0_EL1_Type_TraceVer w__624))
  let w__625 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__626 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__625 15 12 (_get_ID_AA64DFR0_EL1_Type_BRPs w__626))
  let w__627 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__628 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__627 23 20 (_get_ID_AA64DFR0_EL1_Type_WRPs w__628))
  let w__629 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__630 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__629 31 28
    (_get_ID_AA64DFR0_EL1_Type_CTX_CMPs w__630))
  let w__631 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__632 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__631 43 40
    (_get_ID_AA64DFR0_EL1_Type_TraceFilt w__632))
  let w__633 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__633 0 0 1#1)
  let w__634 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__635 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__634 3 0 (_get_ID_AA64PFR0_EL1_Type_EL0 w__635))
  let w__636 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__637 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__636 7 4 (_get_ID_AA64PFR0_EL1_Type_EL1 w__637))
  let w__638 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__639 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__638 11 8 (_get_ID_AA64PFR0_EL1_Type_EL2 w__639))
  let w__640 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__641 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__640 15 12 (_get_ID_AA64PFR0_EL1_Type_EL3 w__641))
  let w__642 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__643 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__642 23 20 (_get_ID_AA64PFR0_EL1_Type_AdvSIMD w__643))
  let w__644 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__645 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__644 27 24 (_get_ID_AA64PFR0_EL1_Type_GIC w__645))
  let w__646 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__646 13 8 0b100000#6)
  let w__647 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__647 21 16 0b100000#6)
  let w__648 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__648 25 24 0b01#2)
  let w__649 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__649 31 21 0b01000111011#11)
  let w__650 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__650 20 20 1#1)
  let w__651 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__651 15 0 0b0001101000010100#16)
  let w__652 ← (( do readReg CTIDEVTYPE ) : SailM (BitVec 32) )
  writeReg CTIDEVTYPE (Sail.BitVec.updateSubrange w__652 7 4 0b0001#4)
  let w__653 ← (( do readReg CTIDEVTYPE ) : SailM (BitVec 32) )
  writeReg CTIDEVTYPE (Sail.BitVec.updateSubrange w__653 3 0 0b0100#4)
  let w__654 ← (( do readReg CTIPIDR4 ) : SailM (BitVec 32) )
  writeReg CTIPIDR4 (Sail.BitVec.updateSubrange w__654 7 4 0b0000#4)
  let w__655 ← (( do readReg CTIPIDR4 ) : SailM (BitVec 32) )
  writeReg CTIPIDR4 (Sail.BitVec.updateSubrange w__655 3 0 0b0100#4)
  let w__656 ← (( do readReg CTIPIDR2 ) : SailM (BitVec 32) )
  writeReg CTIPIDR2 (Sail.BitVec.updateSubrange w__656 3 3 1#1)
  let w__657 ← (( do readReg CTIPIDR2 ) : SailM (BitVec 32) )
  writeReg CTIPIDR2 (Sail.BitVec.updateSubrange w__657 2 0 0b011#3)
  let w__658 ← (( do readReg CTIPIDR1 ) : SailM (BitVec 32) )
  writeReg CTIPIDR1 (Sail.BitVec.updateSubrange w__658 7 4 0b1011#4)
  let w__659 ← (( do readReg CTIPIDR1 ) : SailM (BitVec 32) )
  writeReg CTIPIDR1 (Sail.BitVec.updateSubrange w__659 3 0 0b1101#4)
  let w__660 ← (( do readReg CTIPIDR0 ) : SailM (BitVec 32) )
  writeReg CTIPIDR0 (Sail.BitVec.updateSubrange w__660 7 0 0b00001111#8)
  let w__661 ← (( do readReg CTICIDR3 ) : SailM (BitVec 32) )
  writeReg CTICIDR3 (Sail.BitVec.updateSubrange w__661 7 0 0b10110001#8)
  let w__662 ← (( do readReg CTICIDR2 ) : SailM (BitVec 32) )
  writeReg CTICIDR2 (Sail.BitVec.updateSubrange w__662 7 0 0b00000101#8)
  let w__663 ← (( do readReg CTICIDR1 ) : SailM (BitVec 32) )
  writeReg CTICIDR1 (Sail.BitVec.updateSubrange w__663 7 4 0b1001#4)
  let w__664 ← (( do readReg CTICIDR1 ) : SailM (BitVec 32) )
  writeReg CTICIDR1 (Sail.BitVec.updateSubrange w__664 3 0 0b0000#4)
  let w__665 ← (( do readReg CTICIDR0 ) : SailM (BitVec 32) )
  writeReg CTICIDR0 (Sail.BitVec.updateSubrange w__665 7 0 0b00001101#8)
  let w__666 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  let w__667 ← (( do readReg NUM_GIC_PREEMPTION_BITS ) : SailM Int )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__666 28 26 (integer_subrange (w__667 -i 1) 2 0))
  let w__668 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  let w__669 ← (( do readReg NUM_GIC_LIST_REGS ) : SailM Int )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__668 4 0 (integer_subrange (w__669 -i 1) 4 0))
  let w__670 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  let w__671 ← (( do readReg NUM_GIC_PRIORITY_BITS ) : SailM Int )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__670 31 29 (integer_subrange (w__671 -i 1) 2 0))
  let w__672 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__673 ← (( do (IsG1ActivityMonitorImplemented 0) ) : SailM Bool )
  let w__674 : (BitVec 1) :=
    if (w__673 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__672 0 0 w__674)
  let w__675 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__676 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
  let w__677 : (BitVec 1) :=
    if (w__676 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__675 1 1 w__677)
  let w__678 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__679 ← (( do (IsG1ActivityMonitorImplemented 2) ) : SailM Bool )
  let w__680 : (BitVec 1) :=
    if (w__679 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__678 2 2 w__680)
  let w__681 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__682 ← (( do (IsG1ActivityMonitorImplemented 3) ) : SailM Bool )
  let w__683 : (BitVec 1) :=
    if (w__682 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__681 3 3 w__683)
  let w__684 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__685 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  let w__686 : (BitVec 1) :=
    if (w__685 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__684 4 4 w__686)
  let w__687 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__688 ← (( do (IsG1ActivityMonitorImplemented 5) ) : SailM Bool )
  let w__689 : (BitVec 1) :=
    if (w__688 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__687 5 5 w__689)
  let w__690 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__691 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  let w__692 : (BitVec 1) :=
    if (w__691 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__690 6 6 w__692)
  let w__693 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__694 ← (( do (IsG1ActivityMonitorImplemented 7) ) : SailM Bool )
  let w__695 : (BitVec 1) :=
    if (w__694 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__693 7 7 w__695)
  let w__696 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__697 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  let w__698 : (BitVec 1) :=
    if (w__697 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__696 8 8 w__698)
  let w__699 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__700 ← (( do (IsG1ActivityMonitorImplemented 9) ) : SailM Bool )
  let w__701 : (BitVec 1) :=
    if (w__700 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__699 9 9 w__701)
  let w__702 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__703 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
  let w__704 : (BitVec 1) :=
    if (w__703 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__702 10 10 w__704)
  let w__705 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__706 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  let w__707 : (BitVec 1) :=
    if (w__706 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__705 11 11 w__707)
  let w__708 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__709 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  let w__710 : (BitVec 1) :=
    if (w__709 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__708 12 12 w__710)
  let w__711 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__712 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  let w__713 : (BitVec 1) :=
    if (w__712 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__711 13 13 w__713)
  let w__714 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__715 ← (( do (IsG1ActivityMonitorImplemented 14) ) : SailM Bool )
  let w__716 : (BitVec 1) :=
    if (w__715 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__714 14 14 w__716)
  let w__717 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__718 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  let w__719 : (BitVec 1) :=
    if (w__718 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__717 15 15 w__719)
  let w__720 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__721 ← (( do (IsG1ActivityMonitorOffsetImplemented 0) ) : SailM Bool )
  let w__722 : (BitVec 1) :=
    if (w__721 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__720 16 16 w__722)
  let w__723 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__724 ← (( do (IsG1ActivityMonitorOffsetImplemented 1) ) : SailM Bool )
  let w__725 : (BitVec 1) :=
    if (w__724 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__723 17 17 w__725)
  let w__726 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__727 ← (( do (IsG1ActivityMonitorOffsetImplemented 2) ) : SailM Bool )
  let w__728 : (BitVec 1) :=
    if (w__727 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__726 18 18 w__728)
  let w__729 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__730 ← (( do (IsG1ActivityMonitorOffsetImplemented 3) ) : SailM Bool )
  let w__731 : (BitVec 1) :=
    if (w__730 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__729 19 19 w__731)
  let w__732 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__733 ← (( do (IsG1ActivityMonitorOffsetImplemented 4) ) : SailM Bool )
  let w__734 : (BitVec 1) :=
    if (w__733 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__732 20 20 w__734)
  let w__735 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__736 ← (( do (IsG1ActivityMonitorOffsetImplemented 5) ) : SailM Bool )
  let w__737 : (BitVec 1) :=
    if (w__736 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__735 21 21 w__737)
  let w__738 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__739 ← (( do (IsG1ActivityMonitorOffsetImplemented 6) ) : SailM Bool )
  let w__740 : (BitVec 1) :=
    if (w__739 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__738 22 22 w__740)
  let w__741 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__742 ← (( do (IsG1ActivityMonitorOffsetImplemented 7) ) : SailM Bool )
  let w__743 : (BitVec 1) :=
    if (w__742 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__741 23 23 w__743)
  let w__744 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__745 ← (( do (IsG1ActivityMonitorOffsetImplemented 8) ) : SailM Bool )
  let w__746 : (BitVec 1) :=
    if (w__745 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__744 24 24 w__746)
  let w__747 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__748 ← (( do (IsG1ActivityMonitorOffsetImplemented 9) ) : SailM Bool )
  let w__749 : (BitVec 1) :=
    if (w__748 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__747 25 25 w__749)
  let w__750 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__751 ← (( do (IsG1ActivityMonitorOffsetImplemented 10) ) : SailM Bool )
  let w__752 : (BitVec 1) :=
    if (w__751 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__750 26 26 w__752)
  let w__753 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__754 ← (( do (IsG1ActivityMonitorOffsetImplemented 11) ) : SailM Bool )
  let w__755 : (BitVec 1) :=
    if (w__754 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__753 27 27 w__755)
  let w__756 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__757 ← (( do (IsG1ActivityMonitorOffsetImplemented 12) ) : SailM Bool )
  let w__758 : (BitVec 1) :=
    if (w__757 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__756 28 28 w__758)
  let w__759 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__760 ← (( do (IsG1ActivityMonitorOffsetImplemented 13) ) : SailM Bool )
  let w__761 : (BitVec 1) :=
    if (w__760 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__759 29 29 w__761)
  let w__762 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__763 ← (( do (IsG1ActivityMonitorOffsetImplemented 14) ) : SailM Bool )
  let w__764 : (BitVec 1) :=
    if (w__763 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__762 30 30 w__764)
  let w__765 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__766 ← (( do (IsG1ActivityMonitorOffsetImplemented 15) ) : SailM Bool )
  let w__767 : (BitVec 1) :=
    if (w__766 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__765 31 31 w__767)
  if ((HasArchVersion v9Ap4) : Bool)
  then
    (do
      let w__768 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__768 63 56 0x3F#8)
      let w__769 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__769 43 40 0b0001#4)
      let w__770 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__770 35 32 0b0001#4)
      let w__771 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__771 39 36 0b0001#4)
      let w__772 ← (( do (HaveLSE128 ()) ) : SailM Bool )
      if (w__772 : Bool)
      then
        (do
          let w__773 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__773 23 20 0b0011#4))
      else (pure (()))
      let w__774 ← (( do (HaveGCS ()) ) : SailM Bool )
      if (w__774 : Bool)
      then
        (do
          let w__775 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__775 47 44 0b0001#4))
      else (pure (()))
      let w__776 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__776 3 0 0b0010#4)
      let w__777 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__777 47 44 0b0001#4)
      let w__778 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__778 59 56 0b0010#4)
      let w__781 ← (( do
        if ((← do
             (HaveSVE2p1 ())) : Bool)
        then (pure true)
        else
          (do
            (HaveSME2p1 ())) ) : SailM Bool )
      if (w__781 : Bool)
      then
        (do
          let w__782 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__782 43 43 1#1)
          let w__783 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__783 27 24 0b0001#4))
      else (pure (()))
      let w__784 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__784 42 42 1#1)
      let w__785 ← (( do readReg PMDEVID ) : SailM (BitVec 32) )
      writeReg PMDEVID (Sail.BitVec.updateSubrange w__785 7 4 0b0001#4)
      let w__786 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__786 27 24 0b0001#4)
      let w__787 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__787 11 8 0b0011#4)
      let w__788 ← (( do (HaveFeatEBEP ()) ) : SailM Bool )
      if (w__788 : Bool)
      then
        (do
          let w__789 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__789 51 48 0b0001#4))
      else (pure (()))
      let w__790 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__790 19 16 0b0010#4)
      let w__791 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__791 3 0 0b0111#4)
      let w__792 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__792 35 32 0b0001#4)
      let w__793 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__793 39 36 0b0001#4)
      let w__794 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__794 7 4 0b0010#4)
      let w__795 ← (( do (HaveMTEPermExt ()) ) : SailM Bool )
      if (w__795 : Bool)
      then
        (do
          let w__796 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__796 3 0 0b0001#4))
      else (pure (()))
      let w__797 ← (( do (HavePFAR ()) ) : SailM Bool )
      if (w__797 : Bool)
      then
        (do
          let w__798 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__798 63 60 0b0001#4))
      else (pure (()))
      let w__799 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
      if (w__799 : Bool)
      then
        (do
          let w__800 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__800 59 56 0b0001#4))
      else (pure (()))
      let w__801 ← (( do (HaveTHExt ()) ) : SailM Bool )
      if (w__801 : Bool)
      then
        (do
          let w__802 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__802 51 48 0b0001#4))
      else (pure (()))
      let w__803 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
      if (w__803 : Bool)
      then
        (do
          let w__804 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__804 55 52 0b0001#4)
          let w__805 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__805 7 4 0b0001#4)
          let w__806 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__806 11 8 0b0001#4))
      else (pure (()))
      let w__807 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR4_EL1 (Sail.BitVec.updateSubrange w__807 7 4 0b0001#4)
      let w__808 ← (( do (HaveRASv2Ext ()) ) : SailM Bool )
      if (w__808 : Bool)
      then
        (do
          let w__809 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__809 31 28 0b0011#4)
          let w__810 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__810 31 28 0b0011#4))
      else (pure (()))
      let w__811 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__811 43 40 0b0010#4)
      let w__812 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__812 47 44 0b0010#4)
      let w__813 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__813 55 52 0b0010#4)
      let w__814 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__814 59 56 0b0010#4)
      let w__815 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__815 39 36 0b0001#4)
      let w__816 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__816 35 32 0b0001#4)
      let w__817 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__817 31 24 0x3F#8)
      let w__818 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__818 23 16 0x3F#8)
      let w__819 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__819 15 8 0x3F#8)
      let w__820 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__820 7 0 0x1F#8)
      let w__821 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__821 55 52 0b0001#4)
      let w__822 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__822 47 44 0b0010#4)
      let w__823 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__823 23 20 0b0010#4)
      let w__824 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__824 43 40 0b0010#4)
      let w__825 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__825 23 20 0b0011#4)
      let w__826 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__826 31 28 0b0001#4)
      let w__827 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__827 55 52 0b0001#4)
      let w__828 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__828 51 48 0b0001#4)
      let w__829 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__829 43 40 0b0001#4)
      let w__830 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__830 3 0 0b0011#4)
      let w__831 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__831 59 56 0b0011#4)
      let w__832 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__832 63 60 0b0001#4)
      let w__833 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__833 3 0 0b0001#4)
      let w__834 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__834 11 8 0b0001#4)
      let w__835 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__835 19 16 0b0001#4)
      let w__836 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__836 15 12 0b0001#4)
      let w__837 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__837 23 20 0b0001#4)
      let w__838 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__838 27 24 0b0001#4)
      let w__839 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__839 7 4 0b0001#4)
      let w__840 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__840 63 60 0b0001#4)
      let w__841 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__841 3 0 0b1011#4)
      let w__842 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__842 11 8 0b1001#4)
      let w__843 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__843 35 32 0b0101#4)
      let w__844 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__844 59 56 0b0001#4)
      let w__845 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__845 19 16 0b0001#4)
      let w__846 ← (( do readReg PMDEVID ) : SailM (BitVec 32) )
      writeReg PMDEVID (Sail.BitVec.updateSubrange w__846 3 0 0b0010#4)
      let w__847 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
      writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__847 27 24 0b0001#4)
      let w__848 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
      writeReg PMCFGR (BitVec.update w__848 22 (Bit 1#1))
      let w__849 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__849 59 56 0b0010#4)
      let w__850 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__850 7 4 0b1011#4)
      let w__851 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__851 3 0 0b1011#4)
      let w__852 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__852 27 24 0b1001#4)
      let w__853 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__853 19 16 0b0010#4)
      let w__854 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__854 31 28 0b0001#4)
      let w__855 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      let w__856 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
      let w__858 ← (( do
        if ((w__856 ≥b 16) : Bool)
        then (pure (0b1111#4))
        else
          (do
            let w__857 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
            (pure ((integer_subrange (w__857 -i 1) 3 0)))) ) : SailM (BitVec 4) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__855 23 20 w__858)
      let w__859 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      let w__860 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
      let w__862 ← (( do
        if ((w__860 ≥b 16) : Bool)
        then (pure (0b1111#4))
        else
          (do
            let w__861 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
            (pure ((integer_subrange (w__861 -i 1) 3 0)))) ) : SailM (BitVec 4) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__859 15 12 w__862))
  else (pure (()))


end ArmFull.Functions
