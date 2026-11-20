module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0057
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0158
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199 set_option backward.proofsInPublic true @[expose] public section

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
        ArmFull.assert ((0 ≤b i) && (i <b 4)) "sail-inputs/13-reset.sail:432.55-432.56"
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
  let w__196 ← (( do (HasArchVersion v8Ap1) ) : SailM Bool )
  if (w__196 : Bool)
  then
    (do
      let w__197 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__197 27 24 0b0001#4)
      let w__198 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__198 23 20 0b0010#4)
      let w__199 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__199 31 28 0b0001#4)
      let w__200 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__200 19 16 0b0001#4)
      let w__201 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__201 11 8 0b0001#4)
      let w__202 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__202 15 12 0b0001#4)
      let w__203 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__203 3 0 0b0010#4))
  else (pure (()))
  let w__204 ← (( do (IsFeatureImplemented FEAT_CRC32) ) : SailM Bool )
  if (w__204 : Bool)
  then
    (do
      let w__205 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__205 19 16 0b0001#4)
      let w__206 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__206 19 16 0b0001#4))
  else (pure (()))
  let w__207 ← (( do (IsFeatureImplemented FEAT_VMID16) ) : SailM Bool )
  if (w__207 : Bool)
  then
    (do
      let w__208 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__208 7 4 0b0010#4))
  else (pure (()))
  let w__209 ← (( do (IsFeatureImplemented FEAT_PAN) ) : SailM Bool )
  if (w__209 : Bool)
  then
    (do
      let w__210 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__210 23 20 0b0001#4)
      let w__211 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__211 19 16 0b0001#4))
  else (pure (()))
  let w__212 ← (( do (IsFeatureImplemented FEAT_AES) ) : SailM Bool )
  if ((! w__212) : Bool)
  then
    (do
      let w__213 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__213 7 4 0b0000#4))
  else (pure (()))
  let w__214 ← (( do (IsFeatureImplemented FEAT_AES) ) : SailM Bool )
  if (w__214 : Bool)
  then
    (do
      let w__215 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__215 7 4 0b0001#4))
  else (pure (()))
  let w__218 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_AES)) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_PMULL))
    else (pure false) ) : SailM Bool )
  if (w__218 : Bool)
  then
    (do
      let w__219 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__219 7 4 0b0010#4))
  else (pure (()))
  let w__220 ← (( do (IsFeatureImplemented FEAT_SHA1) ) : SailM Bool )
  if ((! w__220) : Bool)
  then
    (do
      let w__221 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__221 11 8 0b0000#4))
  else (pure (()))
  let w__222 ← (( do (IsFeatureImplemented FEAT_SHA256) ) : SailM Bool )
  if ((! w__222) : Bool)
  then
    (do
      let w__223 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__223 15 12 0b0000#4))
  else (pure (()))
  let w__224 ← (( do (HasArchVersion v8Ap2) ) : SailM Bool )
  if (w__224 : Bool)
  then
    (do
      let w__225 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__225 31 28 0b0001#4)
      let w__226 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__226 23 20 0b0010#4)
      let w__227 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__227 3 0 0b0001#4)
      let w__228 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__228 7 4 0b0001#4)
      let w__229 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__229 11 8 0b0001#4)
      let w__230 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__230 15 12 0b0001#4)
      let w__231 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__231 19 16 0b0010#4)
      let w__232 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__232 39 36 0b0001#4)
      let w__233 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__233 11 8 0b0001#4)
      let w__234 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__234 15 12 0b0001#4)
      let w__235 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__235 23 20 0b0001#4)
      let w__236 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__236 7 4 0b0001#4)
      let w__237 ← (( do (HaveEL EL2) ) : SailM Bool )
      if (w__237 : Bool)
      then
        (do
          let w__238 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
          writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__238 31 28 0b0010#4)
          let w__239 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__239 59 56 0b0010#4))
      else
        (do
          let w__240 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
          writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__240 31 28 0b0000#4)
          let w__241 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__241 59 56 0b0000#4))
      let w__242 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__242 31 28 0b0000#4)
      let w__243 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__243 63 63 1#1)
      let w__244 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__244 32 32 1#1)
      let w__245 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__245 34 34 1#1)
      let w__246 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__246 35 35 1#1)
      let w__247 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__247 39 36 0b1111#4)
      let w__248 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__248 48 48 1#1)
      let w__249 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__249 55 52 0b1111#4)
      let w__250 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__250 43 40 0b0001#4)
      let w__251 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__251 39 36 0b0001#4)
      let w__252 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__252 3 0 0b0010#4)
      let w__253 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__253 7 4 0b0001#4)
      let w__254 ← (( do (HaveDoPD ()) ) : SailM Bool )
      if (w__254 : Bool)
      then
        (do
          let w__255 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
          writeReg EDDEVID (Sail.BitVec.updateSubrange w__255 7 4 0b0001#4)
          let w__256 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
          writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__256 19 16 0b0001#4))
      else
        (do
          let w__257 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
          writeReg EDDEVID (Sail.BitVec.updateSubrange w__257 7 4 0b0000#4)
          let w__258 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
          writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__258 19 16 0b0000#4))
      let w__259 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__259 43 40 0b0001#4)
      let w__260 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__260 35 32 0b0001#4)
      let w__261 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__261 19 16 0b0001#4)
      let w__262 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__262 7 4 0b0010#4)
      let w__263 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__263 3 0 0b0001#4)
      let w__264 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__264 23 20 0b0001#4)
      let w__265 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__265 47 44 0b0001#4)
      let w__266 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__266 23 20 0b0010#4)
      let w__267 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__267 47 44 0b0010#4)
      let w__268 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__268 51 48 0b0001#4)
      let w__269 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__269 23 20 0b0001#4)
      let w__270 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__270 47 44 0b0001#4)
      let w__271 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__271 55 52 0b0001#4)
      let w__272 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__272 27 24 0b0001#4))
  else (pure (()))
  let w__273 ← (( do (HasArchVersion v8Ap6) ) : SailM Bool )
  if (w__273 : Bool)
  then
    (do
      let w__274 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__274 47 44 0b0010#4)
      let w__275 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__275 23 20 0b0010#4)
      let w__276 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__276 55 52 0b0001#4)
      let w__277 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__277 59 56 0b0001#4))
  else (pure (()))
  let w__278 ← (( do (IsFeatureImplemented FEAT_DotProd) ) : SailM Bool )
  if (w__278 : Bool)
  then
    (do
      let w__279 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__279 47 44 0b0001#4))
  else (pure (()))
  let w__280 ← (( do (IsFeatureImplemented FEAT_FP16) ) : SailM Bool )
  if (w__280 : Bool)
  then
    (do
      let w__281 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__281 19 16 0b0001#4)
      let w__282 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__282 23 20 0b0001#4))
  else (pure (()))
  let w__283 ← (( do (IsFeatureImplemented FEAT_AA32HPD) ) : SailM Bool )
  if (w__283 : Bool)
  then
    (do
      let w__284 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__284 15 12 0b0010#4)
      let w__285 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__285 19 16 0b0010#4))
  else (pure (()))
  let w__286 ← (( do (HaveMPAMExt ()) ) : SailM Bool )
  if (w__286 : Bool)
  then
    (do
      let w__287 ← (( do readReg __empam_force_ns_implemented ) : SailM Bool )
      if (w__287 : Bool)
      then
        (do
          writeReg __mpam_major CFG_MPAM_v0p1
          writeReg __mpam_frac CFG_MPAM_frac_v0p1
          let w__288 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__288 60 60 1#1))
      else
        (do
          writeReg __mpam_major CFG_MPAM_v1p1
          writeReg __mpam_frac CFG_MPAM_frac_v1p1)
      let w__289 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      let w__290 ← (( do readReg __mpam_major ) : SailM (BitVec 4) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__289 43 40 w__290)
      let w__291 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
      let w__292 ← (( do readReg __mpam_partid_max ) : SailM (BitVec 16) )
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__291 15 0 w__292)
      let w__293 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
      let w__294 ← (( do readReg __mpam_pmg_max ) : SailM (BitVec 8) )
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__293 39 32 w__294)
      let w__295 ← (( do readReg __mpam_has_hcr ) : SailM Bool )
      if (w__295 : Bool)
      then
        (do
          let w__296 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__296 17 17 1#1)
          let w__297 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          let w__298 ← (( do readReg __mpam_vpmr_max ) : SailM (BitVec 3) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__297 20 18 w__298))
      else (pure (()))
      let w__299 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      let w__300 ← (( do readReg __mpam_frac ) : SailM (BitVec 4) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__299 19 16 w__300)
      let w__305 ← (( do
        if ((← do
             let w__301 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
             (pure ((((BitVec.toNat (_get_ID_AA64PFR0_EL1_Type_MPAM w__301)) >b 1) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 let w__302 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
                 let b__0 := (_get_ID_AA64PFR0_EL1_Type_MPAM w__302)
                 (pure ((if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
                   then true
                   else false : Bool)))) : Bool)
            then
              (do
                let w__303 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
                (pure ((((_get_ID_AA64PFR1_EL1_Type_MPAM_frac w__303) == 0b0001#4) : Bool))))
            else (pure false)) ) : SailM Bool )
      ArmFull.assert w__305 "sail-inputs/13-reset.sail:720.56-720.57"
      let w__306 ← (( do readReg __empam_sdeflt_implemented ) : SailM Bool )
      if (w__306 : Bool)
      then
        (do
          let w__307 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__307 61 61 1#1))
      else (pure (()))
      let w__308 ← (( do readReg __empam_tidr_implemented ) : SailM Bool )
      if (w__308 : Bool)
      then
        (do
          let w__309 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__309 58 58 1#1))
      else (pure (())))
  else (pure (()))
  let w__312 ← (( do
    if ((← do
         (HasArchVersion v9Ap2)) : Bool)
    then
      (do
        (HaveRME ()))
    else (pure false) ) : SailM Bool )
  if (w__312 : Bool)
  then
    (do
      let w__313 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
      writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__313 59 59 1#1)
      let w__314 ← (( do readReg __mpam_has_altsp ) : SailM Bool )
      if (w__314 : Bool)
      then
        (do
          let w__315 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
          writeReg MPAMIDR_EL1 (Sail.BitVec.updateSubrange w__315 57 57 1#1))
      else (pure (())))
  else (pure (()))
  let w__316 ← (( do (HasArchVersion v8Ap3) ) : SailM Bool )
  if (w__316 : Bool)
  then
    (do
      let w__317 ← (( do (IsFeatureImplemented FEAT_PACQARMA3) ) : SailM Bool )
      if (w__317 : Bool)
      then
        (do
          let w__318 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__318 11 8 0b0001#4)
          let w__319 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__319 15 12 0b0101#4)
          let w__320 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__320 7 4 0b0000#4)
          let w__321 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__321 27 24 0b0000#4))
      else (pure (()))
      let w__322 ← (( do (IsFeatureImplemented FEAT_PACQARMA5) ) : SailM Bool )
      if (w__322 : Bool)
      then
        (do
          let w__323 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__323 11 8 0b0000#4)
          let w__324 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__324 15 12 0b0000#4)
          let w__325 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__325 7 4 0b0101#4)
          let w__326 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__326 27 24 0b0001#4))
      else (pure (()))
      let w__327 ← (( do (IsFeatureImplemented FEAT_CONSTPACFIELD) ) : SailM Bool )
      if (w__327 : Bool)
      then
        (do
          let w__328 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__328 27 24 0b0001#4))
      else
        (do
          let w__329 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__329 27 24 0b0000#4))
      let w__330 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__330 15 12 0b0001#4)
      let w__331 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__331 19 16 0b0001#4)
      let w__332 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__332 3 0 0b0001#4)
      let w__333 ← (( do readReg ID_MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR4_EL1 (Sail.BitVec.updateSubrange w__333 27 24 0b0001#4)
      let w__334 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__334 27 24 0b0001#4)
      let w__335 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__335 31 28 0b0001#4)
      let w__336 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__336 23 20 0b0001#4)
      let w__337 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__337 23 20 0b0001#4))
  else (pure (()))
  let w__338 ← (( do (HasArchVersion v8Ap4) ) : SailM Bool )
  if (w__338 : Bool)
  then
    (do
      let w__339 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__339 23 20 0b0010#4)
      let w__340 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__340 31 28 0b0001#4)
      let w__341 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__341 35 32 0b0001#4)
      let w__342 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__342 51 48 0b0001#4)
      let w__343 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__343 43 40 0b0001#4)
      let w__344 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__344 27 24 0b0010#4)
      let w__345 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__345 3 0 0b1001#4)
      let w__348 ← (( do
        if ((← do
             let w__346 ← (( do (HaveEL EL3) ) : SailM Bool )
             (pure (((! w__346) : Bool)))) : Bool)
        then
          (do
            let w__347 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__347) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__348 : Bool)
      then
        (do
          let w__349 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__349 7 4 0b0000#4))
      else
        (do
          let w__350 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          let w__351 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__350 7 4
            (_get_ID_DFR0_EL1_Type_CopDbg w__351)))
      let w__352 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__352 39 36 0b0001#4)
      let w__353 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__353 59 56 0b0010#4)
      let w__354 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__354 55 52 0b0000#4)
      let w__355 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__355 51 48 0b0001#4)
      let w__356 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__356 11 8 0b0001#4)
      let w__357 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__357 31 28 0b0010#4)
      let w__358 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      let w__359 ← (( do readReg __block_bbm_implemented ) : SailM Int )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__358 55 52
        (integer_subrange w__359 3 0))
      let w__360 ← (( do (IsFeatureImplemented FEAT_SHA512) ) : SailM Bool )
      if (w__360 : Bool)
      then
        (do
          let w__361 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__361 15 12 0b0010#4))
      else (pure (()))
      let w__362 ← (( do (IsFeatureImplemented FEAT_SHA3) ) : SailM Bool )
      if (w__362 : Bool)
      then
        (do
          let w__363 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__363 35 32 0b0001#4))
      else (pure (()))
      let w__364 ← (( do (IsFeatureImplemented FEAT_SM3) ) : SailM Bool )
      if (w__364 : Bool)
      then
        (do
          let w__365 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__365 39 36 0b0001#4))
      else (pure (()))
      let w__366 ← (( do (IsFeatureImplemented FEAT_SM4) ) : SailM Bool )
      if (w__366 : Bool)
      then
        (do
          let w__367 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__367 43 40 0b0001#4))
      else (pure (()))
      let w__368 ← (( do (HavePMUv3p4 ()) ) : SailM Bool )
      if (w__368 : Bool)
      then
        (do
          let w__369 ← (( do (HavePMUv3TH ()) ) : SailM Bool )
          if (w__369 : Bool)
          then
            (do
              let w__370 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
              writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__370 23 20 0b1100#4))
          else (pure (()))
          let w__371 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
          writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__371 19 16 0b0100#4)
          let w__372 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
          writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__372 15 8 0b00000011#8))
      else (pure (())))
  else (pure (()))
  let w__373 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__373 7 4 0b0010#4)
  let w__374 ← (( do (HasArchVersion v8Ap5) ) : SailM Bool )
  if (w__374 : Bool)
  then
    (do
      let w__375 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__375 55 52 0b0010#4)
      let w__376 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__376 35 32 0b0001#4)
      let w__377 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__377 3 0 0b0001#4)
      let w__378 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__378 27 24 0b0110#4)
      let w__379 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__379 63 60 0b0001#4)
      let w__380 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__380 63 60 0b0001#4)
      let w__381 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
      if (w__381 : Bool)
      then
        (do
          let w__382 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__382 11 8 0b0010#4))
      else (pure (()))
      let w__383 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__383 11 8 0b0110#4)
      let w__384 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
      writeReg EDDFR (Sail.BitVec.updateSubrange w__384 11 8 0b0000#4)
      let w__385 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__385 15 12 0b0001#4)
      let w__386 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__386 19 16 0b0001#4))
  else (pure (()))
  let w__387 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__387 23 20 0b0000#4)
  let w__388 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__388 11 8 0b0000#4)
  let w__389 ← (( do (HasArchVersion v8Ap6) ) : SailM Bool )
  if (w__389 : Bool)
  then
    (do
      let w__390 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__390 35 32 0b0001#4))
  else (pure (()))
  let w__391 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__391 19 16 0b0010#4)
  let w__392 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__392 51 48 0b0001#4)
  let w__393 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__393 3 0 0b0001#4)
  let w__394 ← (( do (HasArchVersion v8Ap7) ) : SailM Bool )
  if (w__394 : Bool)
  then
    (do
      let w__395 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__395 43 40 0b0001#4)
      let w__398 ← (( do
        if ((← do
             let w__396 ← (( do (HaveEL EL3) ) : SailM Bool )
             (pure (((! w__396) : Bool)))) : Bool)
        then
          (do
            (HaveEL EL2))
        else (pure false) ) : SailM Bool )
      if (w__398 : Bool)
      then
        (do
          writeReg HCRX_EL2 (Mk_HCRX_EL2_Type (Zeros (n := 64))))
      else (pure (()))
      let w__399 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__399 47 44 0b0001#4)
      let w__400 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__400 11 8 0b0111#4)
      let w__401 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__401 27 24 0b0111#4)
      let w__402 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__402 35 32 0b0011#4)
      let w__403 ← (( do readReg __feat_rpres ) : SailM Bool )
      if (w__403 : Bool)
      then
        (do
          let w__404 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__404 7 4 0b0001#4))
      else (pure (()))
      let w__405 ← (( do (Have52BitIPAAndPASpaceExt ()) ) : SailM Bool )
      if (w__405 : Bool)
      then
        (do
          let w__406 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__406 31 28 0b0001#4)
          let w__407 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__407 43 40 0b0011#4)
          let w__408 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__408 23 20 0b0010#4)
          let w__409 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__409 35 32 0b0011#4))
      else (pure (()))
      let w__410 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__410 59 56 0b0001#4)
      let w__411 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__411 3 0 0b0010#4)
      let w__412 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__412 23 20 0b0011#4)
      let w__413 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__413 11 8 0b0011#4)
      let w__414 ← (( do (HaveFeatLS64_ACCDATA ()) ) : SailM Bool )
      if (w__414 : Bool)
      then
        (do
          let w__415 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__415 63 60 0b0011#4))
      else
        (do
          let w__416 ← (( do (HaveFeatLS64_V ()) ) : SailM Bool )
          if (w__416 : Bool)
          then
            (do
              let w__417 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
              writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__417 63 60 0b0010#4))
          else
            (do
              let w__418 ← (( do (HaveFeatLS64 ()) ) : SailM Bool )
              if (w__418 : Bool)
              then
                (do
                  let w__419 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
                  writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__419 63 60 0b0001#4))
              else
                (do
                  let w__420 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
                  writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__420 63 60 0b0000#4)))))
  else (pure (()))
  let w__421 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (BitVec.update w__421 9 (Bit 1#1))
  let w__422 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__422 31 27 0b11111#5)
  let w__423 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__423 18 18 1#1)
  let w__424 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__424 17 17 1#1)
  let w__425 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__425 16 16 1#1)
  let w__426 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__426 8 8 1#1)
  let w__427 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__427 10 10 1#1)
  let w__428 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__428 4 0 0b00111#5)
  let w__429 ← (( do readReg GICD_TYPER ) : SailM (BitVec 32) )
  writeReg GICD_TYPER (Sail.BitVec.updateSubrange w__429 23 19 0b01111#5)
  let w__430 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__430 5 5 1#1)
  let w__431 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__431 4 4 0#1)
  let w__432 ← (( do readReg PMBIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMBIDR_EL1 (Sail.BitVec.updateSubrange w__432 3 0 0b0000#4)
  let w__433 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__433 32 32 0#1)
  let w__434 ← (( do (IsFeatureImplemented FEAT_SME) ) : SailM Bool )
  if (w__434 : Bool)
  then
    (do
      let w__435 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
      writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__435 31 24 0b01000001#8)
      let w__436 ← (( do readReg SMIDR_EL1 ) : SailM (BitVec 64) )
      writeReg SMIDR_EL1 (Sail.BitVec.updateSubrange w__436 15 15 1#1)
      let w__437 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__437 27 24 0b0001#4)
      let w__438 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__438 7 4 0b0001#4))
  else (pure (()))
  let w__439 ← (( do (HasArchVersion v9Ap3) ) : SailM Bool )
  if (w__439 : Bool)
  then
    (do
      let w__440 ← (( do (IsFeatureImplemented FEAT_MEC) ) : SailM Bool )
      if (w__440 : Bool)
      then
        (do
          let w__441 ← (( do readReg MECIDR_EL2 ) : SailM (BitVec 64) )
          let w__442 ← (( do readReg __mecid_width ) : SailM (BitVec 4) )
          writeReg MECIDR_EL2 (Sail.BitVec.updateSubrange w__441 3 0 w__442)
          let w__443 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__443 31 28 0b0001#4))
      else (pure (())))
  else (pure (()))
  let w__444 ← (( do (IsFeatureImplemented FEAT_SME2) ) : SailM Bool )
  if (w__444 : Bool)
  then
    (do
      let w__445 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__445 27 24 0b0010#4)
      let w__446 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__446 59 56 0b0001#4)
      let w__447 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__447 47 44 0b0101#4)
      let w__448 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__448 33 33 1#1))
  else (pure (()))
  let w__449 ← (( do (HasArchVersion v8Ap8) ) : SailM Bool )
  if (w__449 : Bool)
  then
    (do
      let w__450 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__450 39 36 0b0010#4)
      let w__451 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
      writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__451 3 0 0b0010#4)
      let w__452 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__452 39 36 0b0001#4)
      let w__453 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__453 31 28 0b0001#4)
      let w__454 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__454 19 16 0b0001#4)
      let w__455 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__455 23 20 0b0001#4)
      let w__456 ← (( do (HaveStatisticalProfiling ()) ) : SailM Bool )
      if (w__456 : Bool)
      then
        (do
          let w__457 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__457 35 32 0b0100#4))
      else (pure (()))
      let w__458 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__458 63 60 0b0001#4)
      let w__459 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__459 7 4 0b0001#4)
      let w__460 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__460 3 0 0b1010#4)
      let w__461 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__461 3 0 0b1010#4)
      let w__464 ← (( do
        if ((← do
             let w__462 ← (( do (HaveEL EL3) ) : SailM Bool )
             (pure (((! w__462) : Bool)))) : Bool)
        then
          (do
            let w__463 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__463) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__464 : Bool)
      then
        (do
          let w__465 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__465 7 4 0b0000#4))
      else
        (do
          let w__466 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          let w__467 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__466 7 4
            (_get_ID_DFR0_EL1_Type_CopDbg w__467)))
      let w__468 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__468 55 52 0b0001#4)
      let w__469 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__469 55 52 0b0001#4)
      let w__470 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__470 59 56 0b0001#4)
      let w__471 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__471 11 8 0b1000#4)
      let w__472 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__472 27 24 0b1000#4))
  else (pure (()))
  let w__473 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__473 27 24 0b0001#4)
  let w__474 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__474 19 16 0b0001#4)
  let w__475 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__475 15 12 0b0001#4)
  let w__476 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__476 18 18 0#1)
  let w__477 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__477 17 17 0#1)
  let w__478 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__478 16 16 0#1)
  let w__479 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__479 15 15 0#1)
  let w__480 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__480 14 14 0#1)
  let w__481 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__481 13 13 0#1)
  let w__482 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__482 12 12 0#1)
  let w__483 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__483 11 11 0#1)
  let w__484 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__484 10 10 0#1)
  let w__485 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__485 9 9 0#1)
  let w__486 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__486 8 8 0#1)
  let w__487 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__487 7 7 0#1)
  let w__488 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__488 3 3 0#1)
  let w__489 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__489 2 2 0#1)
  let w__490 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__490 1 1 0#1)
  let w__491 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__491 0 0 0#1)
  let w__492 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__492 31 31 0#1)
  let w__493 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  let w__496 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_VHE)) : Bool)
    then
      (do
        let w__495 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_HCR_EL2_Type_E2H w__495) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let w__497 : Int :=
    if (w__496 : Bool)
    then 28
    else 20
  writeReg CPTR_EL2 (BitVec.update w__493 (Sail.Int.toNatChecked (w__497)) (Bit 0#1))
  let w__498 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__498 49 49 0#1)
  let w__499 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__499 52 52 0#1)
  let w__500 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__500 50 50 0#1)
  let w__501 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__501 44 44 0#1)
  let w__502 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__502 43 43 0#1)
  let w__503 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__503 42 42 0#1)
  let w__504 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__504 41 41 0#1)
  let w__505 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__505 40 40 0#1)
  let w__506 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__506 38 38 0#1)
  let w__507 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__507 37 37 0#1)
  let w__508 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__508 36 36 0#1)
  let w__509 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__509 33 33 0#1)
  let w__510 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__510 32 32 0#1)
  let w__511 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__511 31 31 0#1)
  let w__512 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__512 30 30 0#1)
  let w__513 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__513 29 29 0#1)
  let w__514 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__514 28 28 0#1)
  let w__515 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__515 27 27 0#1)
  let w__516 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__516 26 26 0#1)
  let w__517 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__517 25 25 0#1)
  let w__518 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__518 24 24 0#1)
  let w__519 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__519 23 23 0#1)
  let w__520 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__520 22 22 0#1)
  let w__521 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__521 21 21 0#1)
  let w__522 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__522 20 20 0#1)
  let w__523 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__523 19 19 0#1)
  let w__524 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__524 18 18 0#1)
  let w__525 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__525 17 17 0#1)
  let w__526 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__526 16 16 0#1)
  let w__527 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__527 15 15 0#1)
  let w__528 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__528 14 14 0#1)
  let w__529 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__529 13 13 0#1)
  let w__530 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__530 12 12 0#1)
  let w__531 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__531 11 10 0b00#2)
  let w__532 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__532 9 9 0#1)
  let w__533 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__533 8 8 0#1)
  let w__534 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__534 7 7 0#1)
  let w__535 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__535 6 6 0#1)
  let w__536 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__536 5 5 0#1)
  let w__537 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__537 4 4 0#1)
  let w__538 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__538 3 3 0#1)
  let w__539 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__539 2 2 0#1)
  let w__540 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__540 1 1 0#1)
  let w__541 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__541 0 0 0#1)
  let w__542 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  writeReg HSTR_EL2 (Sail.BitVec.updateSubrange w__542 15 0 (Zeros (n := 16)))
  let w__543 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__543 31 31 0#1)
  let w__544 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__544 30 30 0#1)
  let w__545 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__545 27 27 0#1)
  let w__546 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__546 25 25 0#1)
  let w__547 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__547 13 13 0#1)
  let w__548 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__548 31 31 0#1)
  let w__549 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__549 30 30 0#1)
  let w__550 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__550 27 27 0#1)
  let w__551 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__551 25 25 0#1)
  let w__552 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__552 13 13 0#1)
  let w__553 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__553 28 28 0#1)
  let w__554 ← (( do readReg CPACR_EL1 ) : SailM (BitVec 64) )
  writeReg CPACR_EL1 (Sail.BitVec.updateSubrange w__554 21 20 0b00#2)
  let w__555 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__555 31 31 0#1)
  let w__556 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__556 30 30 0#1)
  let w__557 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__557 27 27 0#1)
  let w__558 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__558 25 25 0#1)
  let w__559 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL1 (Sail.BitVec.updateSubrange w__559 13 13 0#1)
  let w__560 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__560 31 31 0#1)
  let w__561 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__561 30 30 0#1)
  let w__562 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__562 27 27 0#1)
  let w__563 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__563 25 25 0#1)
  let w__564 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL3 (Sail.BitVec.updateSubrange w__564 13 13 0#1)
  let w__565 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__565 24 24 1#1)
  let w__566 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__566 6 6 1#1)
  let w__567 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__567 19 16 0b0011#4)
  match SPEMaxRecordSize with
  | 64 =>
    (do
      let w__568 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
      writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__568 15 12 0b0110#4))
  | _ =>
    (do
      (Unreachable ()))
  let w__569 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__569 3 3 1#1)
  let w__570 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__570 2 2 1#1)
  let w__571 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__571 1 1 1#1)
  let w__572 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSIDR_EL1 (Sail.BitVec.updateSubrange w__572 0 0 1#1)
  let w__573 ← (( do (EL2Enabled ()) ) : SailM Bool )
  if (w__573 : Bool)
  then
    (do
      let w__574 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__574 14 14 0#1)
      let w__575 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__575 13 12 0b10#2))
  else (pure (()))
  let w__576 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let w__577 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__576 4 0 (_get_PMCR_EL0_Type_N w__577))
  let w__578 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__578 0 0 1#1)
  let w__579 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__579 3 3 1#1)
  let w__580 ← (( do readReg ICC_SRE_EL1_S ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_S (Sail.BitVec.updateSubrange w__580 0 0 1#1)
  let w__581 ← (( do readReg ICC_SRE_EL1_NS ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL1_NS (Sail.BitVec.updateSubrange w__581 0 0 1#1)
  let w__582 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__582 0 0 1#1)
  let w__583 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__583 27 24 0b0100#4)
  let w__584 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  let w__585 ← (( do readReg __exclusive_granule_size ) : SailM (BitVec 4) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__584 23 20 w__585)
  let w__586 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__586 19 16 0b0100#4)
  let w__587 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__587 15 14 0b10#2)
  let w__588 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__588 3 0 0b0100#4)
  let w__589 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if (w__589 : Bool)
  then
    (do
      let w__590 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
      writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__590 37 32 0b000100#6))
  else (pure (()))
  let w__591 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if (w__591 : Bool)
  then
    (do
      let w__592 ← (( do readReg GMID_EL1 ) : SailM (BitVec 64) )
      let w__593 ← (( do readReg __gmid_log2_block_size ) : SailM Int )
      writeReg GMID_EL1 (Sail.BitVec.updateSubrange w__592 3 0 (integer_subrange w__593 3 0)))
  else (pure (()))
  let w__594 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__594 23 21 0b010#3)
  let w__595 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__595 20 18 0b011#3)
  let w__596 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_ExtRange w__596 1#1))
  let w__597 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_PRIbits w__597 0b100#3))
  let w__598 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_A3V w__598 1#1))
  let w__599 ← (( do (ICC_CTLR_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_CTLR_EL1_write (_update_ICC_CTLR_EL1_Type_IDbits w__599 0b001#3))
  let w__600 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__600 19 19 1#1)
  let w__601 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__601 10 8 0b100#3)
  let w__602 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__602 13 11 0b001#3)
  let w__603 ← (( do readReg ICV_CTLR_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_CTLR_EL1 (Sail.BitVec.updateSubrange w__603 15 15 1#1)
  let w__604 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__604 31 29 0b100#3)
  let w__605 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__605 28 26 0b100#3)
  let w__606 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__606 25 23 0b001#3)
  let w__607 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__607 21 21 1#1)
  let w__608 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  let w__609 ← (( do (IsFeatureImplemented FEAT_CCIDX) ) : SailM Bool )
  let w__610 : Int :=
    if (w__609 : Bool)
    then 32
    else 13
  writeReg CCSIDR_EL1 (Mk_CCSIDR_EL1_Type
    (set_slice 24 w__608 (Sail.Int.toNatChecked (w__610)) (Sail.BitVec.zeroExtend 0xFF#8 24)))
  let w__611 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__611 23 3 (Sail.BitVec.zeroExtend 0x1#4 21))
  let w__612 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__612 2 0 0b010#3)
  let w__613 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR2_EL1 (Sail.BitVec.updateSubrange w__613 23 0 (Sail.BitVec.zeroExtend 0xFF#8 24))
  let w__614 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__614 3 0 0b0000#4)
  let w__615 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__615 7 4 0b0000#4)
  let w__616 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__616 15 12 0b0000#4)
  let w__617 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__617 3 3 (Sail.BitVec.extractLsb 0b10#2 1 1))
  let w__618 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__618 0 0 (Sail.BitVec.extractLsb 0b10#2 0 0))
  let w__619 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__619 1 0 0b11#2)
  let w__620 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__620 55 12 (Sail.BitVec.zeroExtend 0x22000#20 44))
  let w__621 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__622 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__621 11 8 (_get_ID_AA64DFR0_EL1_Type_PMUVer w__622))
  let w__623 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__623 11 0 0xA15#12)
  let w__624 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
  writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__624 7 4 0b0010#4)
  let w__625 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__625 15 12 0b1011#4)
  let w__626 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__626 20 20 1#1)
  let w__627 ← (( do readReg EDDEVARCH ) : SailM (BitVec 32) )
  writeReg EDDEVARCH (Sail.BitVec.updateSubrange w__627 31 21 0b01000111011#11)
  let w__628 ← (( do readReg EDDEVID ) : SailM (BitVec 32) )
  writeReg EDDEVID (Sail.BitVec.updateSubrange w__628 27 24 0b0001#4)
  let w__629 ← (( do readReg EDDEVTYPE ) : SailM (BitVec 32) )
  writeReg EDDEVTYPE (Sail.BitVec.updateSubrange w__629 3 0 0b0101#4)
  let w__630 ← (( do readReg EDDEVTYPE ) : SailM (BitVec 32) )
  writeReg EDDEVTYPE (Sail.BitVec.updateSubrange w__630 7 4 0b0001#4)
  let w__631 ← (( do readReg EDPIDR0 ) : SailM (BitVec 32) )
  writeReg EDPIDR0 (Sail.BitVec.updateSubrange w__631 7 0 (Sail.BitVec.zeroExtend 0xF#4 8))
  let w__632 ← (( do readReg EDPIDR1 ) : SailM (BitVec 32) )
  writeReg EDPIDR1 (Sail.BitVec.updateSubrange w__632 3 0 0xD#4)
  let w__633 ← (( do readReg EDPIDR1 ) : SailM (BitVec 32) )
  writeReg EDPIDR1 (Sail.BitVec.updateSubrange w__633 7 4 (Sail.BitVec.truncate 0x0B#8 4))
  let w__634 ← (( do readReg EDPIDR2 ) : SailM (BitVec 32) )
  writeReg EDPIDR2 (Sail.BitVec.updateSubrange w__634 2 0 0b011#3)
  let w__635 ← (( do readReg EDPIDR2 ) : SailM (BitVec 32) )
  writeReg EDPIDR2 (Sail.BitVec.updateSubrange w__635 3 3 1#1)
  let w__636 ← (( do readReg EDCIDR0 ) : SailM (BitVec 32) )
  writeReg EDCIDR0 (Sail.BitVec.updateSubrange w__636 7 0 0x0D#8)
  let w__637 ← (( do readReg EDCIDR1 ) : SailM (BitVec 32) )
  writeReg EDCIDR1 (Sail.BitVec.updateSubrange w__637 7 4 0b1001#4)
  let w__638 ← (( do readReg EDCIDR2 ) : SailM (BitVec 32) )
  writeReg EDCIDR2 (Sail.BitVec.updateSubrange w__638 7 0 0x05#8)
  let w__639 ← (( do readReg EDCIDR3 ) : SailM (BitVec 32) )
  writeReg EDCIDR3 (Sail.BitVec.updateSubrange w__639 7 0 0xB1#8)
  let w__640 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__641 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__640 7 4 (_get_ID_AA64DFR0_EL1_Type_TraceVer w__641))
  let w__642 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__643 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__642 15 12 (_get_ID_AA64DFR0_EL1_Type_BRPs w__643))
  let w__644 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__645 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__644 23 20 (_get_ID_AA64DFR0_EL1_Type_WRPs w__645))
  let w__646 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__647 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__646 31 28
    (_get_ID_AA64DFR0_EL1_Type_CTX_CMPs w__647))
  let w__648 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  let w__649 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__648 43 40
    (_get_ID_AA64DFR0_EL1_Type_TraceFilt w__649))
  let w__650 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
  writeReg EDPRSR (Sail.BitVec.updateSubrange w__650 0 0 1#1)
  let w__651 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__652 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__651 3 0 (_get_ID_AA64PFR0_EL1_Type_EL0 w__652))
  let w__653 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__654 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__653 7 4 (_get_ID_AA64PFR0_EL1_Type_EL1 w__654))
  let w__655 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__656 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__655 11 8 (_get_ID_AA64PFR0_EL1_Type_EL2 w__656))
  let w__657 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__658 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__657 15 12 (_get_ID_AA64PFR0_EL1_Type_EL3 w__658))
  let w__659 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__660 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__659 23 20 (_get_ID_AA64PFR0_EL1_Type_AdvSIMD w__660))
  let w__661 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  let w__662 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__661 27 24 (_get_ID_AA64PFR0_EL1_Type_GIC w__662))
  let w__663 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__663 13 8 0b100000#6)
  let w__664 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__664 21 16 0b100000#6)
  let w__665 ← (( do readReg CTIDEVID ) : SailM (BitVec 32) )
  writeReg CTIDEVID (Sail.BitVec.updateSubrange w__665 25 24 0b01#2)
  let w__666 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__666 31 21 0b01000111011#11)
  let w__667 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__667 20 20 1#1)
  let w__668 ← (( do readReg CTIDEVARCH ) : SailM (BitVec 32) )
  writeReg CTIDEVARCH (Sail.BitVec.updateSubrange w__668 15 0 0b0001101000010100#16)
  let w__669 ← (( do readReg CTIDEVTYPE ) : SailM (BitVec 32) )
  writeReg CTIDEVTYPE (Sail.BitVec.updateSubrange w__669 7 4 0b0001#4)
  let w__670 ← (( do readReg CTIDEVTYPE ) : SailM (BitVec 32) )
  writeReg CTIDEVTYPE (Sail.BitVec.updateSubrange w__670 3 0 0b0100#4)
  let w__671 ← (( do readReg CTIPIDR4 ) : SailM (BitVec 32) )
  writeReg CTIPIDR4 (Sail.BitVec.updateSubrange w__671 7 4 0b0000#4)
  let w__672 ← (( do readReg CTIPIDR4 ) : SailM (BitVec 32) )
  writeReg CTIPIDR4 (Sail.BitVec.updateSubrange w__672 3 0 0b0100#4)
  let w__673 ← (( do readReg CTIPIDR2 ) : SailM (BitVec 32) )
  writeReg CTIPIDR2 (Sail.BitVec.updateSubrange w__673 3 3 1#1)
  let w__674 ← (( do readReg CTIPIDR2 ) : SailM (BitVec 32) )
  writeReg CTIPIDR2 (Sail.BitVec.updateSubrange w__674 2 0 0b011#3)
  let w__675 ← (( do readReg CTIPIDR1 ) : SailM (BitVec 32) )
  writeReg CTIPIDR1 (Sail.BitVec.updateSubrange w__675 7 4 0b1011#4)
  let w__676 ← (( do readReg CTIPIDR1 ) : SailM (BitVec 32) )
  writeReg CTIPIDR1 (Sail.BitVec.updateSubrange w__676 3 0 0b1101#4)
  let w__677 ← (( do readReg CTIPIDR0 ) : SailM (BitVec 32) )
  writeReg CTIPIDR0 (Sail.BitVec.updateSubrange w__677 7 0 0b00001111#8)
  let w__678 ← (( do readReg CTICIDR3 ) : SailM (BitVec 32) )
  writeReg CTICIDR3 (Sail.BitVec.updateSubrange w__678 7 0 0b10110001#8)
  let w__679 ← (( do readReg CTICIDR2 ) : SailM (BitVec 32) )
  writeReg CTICIDR2 (Sail.BitVec.updateSubrange w__679 7 0 0b00000101#8)
  let w__680 ← (( do readReg CTICIDR1 ) : SailM (BitVec 32) )
  writeReg CTICIDR1 (Sail.BitVec.updateSubrange w__680 7 4 0b1001#4)
  let w__681 ← (( do readReg CTICIDR1 ) : SailM (BitVec 32) )
  writeReg CTICIDR1 (Sail.BitVec.updateSubrange w__681 3 0 0b0000#4)
  let w__682 ← (( do readReg CTICIDR0 ) : SailM (BitVec 32) )
  writeReg CTICIDR0 (Sail.BitVec.updateSubrange w__682 7 0 0b00001101#8)
  let w__683 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  let w__684 ← (( do readReg NUM_GIC_PREEMPTION_BITS ) : SailM Int )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__683 28 26 (integer_subrange (w__684 -i 1) 2 0))
  let w__685 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  let w__686 ← (( do readReg NUM_GIC_LIST_REGS ) : SailM Int )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__685 4 0 (integer_subrange (w__686 -i 1) 4 0))
  let w__687 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  let w__688 ← (( do readReg NUM_GIC_PRIORITY_BITS ) : SailM Int )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__687 31 29 (integer_subrange (w__688 -i 1) 2 0))
  let w__689 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__690 ← (( do (IsG1ActivityMonitorImplemented 0) ) : SailM Bool )
  let w__691 : (BitVec 1) :=
    if (w__690 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__689 0 0 w__691)
  let w__692 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__693 ← (( do (IsG1ActivityMonitorImplemented 1) ) : SailM Bool )
  let w__694 : (BitVec 1) :=
    if (w__693 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__692 1 1 w__694)
  let w__695 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__696 ← (( do (IsG1ActivityMonitorImplemented 2) ) : SailM Bool )
  let w__697 : (BitVec 1) :=
    if (w__696 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__695 2 2 w__697)
  let w__698 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__699 ← (( do (IsG1ActivityMonitorImplemented 3) ) : SailM Bool )
  let w__700 : (BitVec 1) :=
    if (w__699 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__698 3 3 w__700)
  let w__701 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__702 ← (( do (IsG1ActivityMonitorImplemented 4) ) : SailM Bool )
  let w__703 : (BitVec 1) :=
    if (w__702 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__701 4 4 w__703)
  let w__704 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__705 ← (( do (IsG1ActivityMonitorImplemented 5) ) : SailM Bool )
  let w__706 : (BitVec 1) :=
    if (w__705 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__704 5 5 w__706)
  let w__707 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__708 ← (( do (IsG1ActivityMonitorImplemented 6) ) : SailM Bool )
  let w__709 : (BitVec 1) :=
    if (w__708 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__707 6 6 w__709)
  let w__710 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__711 ← (( do (IsG1ActivityMonitorImplemented 7) ) : SailM Bool )
  let w__712 : (BitVec 1) :=
    if (w__711 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__710 7 7 w__712)
  let w__713 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__714 ← (( do (IsG1ActivityMonitorImplemented 8) ) : SailM Bool )
  let w__715 : (BitVec 1) :=
    if (w__714 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__713 8 8 w__715)
  let w__716 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__717 ← (( do (IsG1ActivityMonitorImplemented 9) ) : SailM Bool )
  let w__718 : (BitVec 1) :=
    if (w__717 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__716 9 9 w__718)
  let w__719 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__720 ← (( do (IsG1ActivityMonitorImplemented 10) ) : SailM Bool )
  let w__721 : (BitVec 1) :=
    if (w__720 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__719 10 10 w__721)
  let w__722 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__723 ← (( do (IsG1ActivityMonitorImplemented 11) ) : SailM Bool )
  let w__724 : (BitVec 1) :=
    if (w__723 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__722 11 11 w__724)
  let w__725 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__726 ← (( do (IsG1ActivityMonitorImplemented 12) ) : SailM Bool )
  let w__727 : (BitVec 1) :=
    if (w__726 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__725 12 12 w__727)
  let w__728 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__729 ← (( do (IsG1ActivityMonitorImplemented 13) ) : SailM Bool )
  let w__730 : (BitVec 1) :=
    if (w__729 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__728 13 13 w__730)
  let w__731 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__732 ← (( do (IsG1ActivityMonitorImplemented 14) ) : SailM Bool )
  let w__733 : (BitVec 1) :=
    if (w__732 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__731 14 14 w__733)
  let w__734 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__735 ← (( do (IsG1ActivityMonitorImplemented 15) ) : SailM Bool )
  let w__736 : (BitVec 1) :=
    if (w__735 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__734 15 15 w__736)
  let w__737 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__738 ← (( do (IsG1ActivityMonitorOffsetImplemented 0) ) : SailM Bool )
  let w__739 : (BitVec 1) :=
    if (w__738 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__737 16 16 w__739)
  let w__740 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__741 ← (( do (IsG1ActivityMonitorOffsetImplemented 1) ) : SailM Bool )
  let w__742 : (BitVec 1) :=
    if (w__741 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__740 17 17 w__742)
  let w__743 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__744 ← (( do (IsG1ActivityMonitorOffsetImplemented 2) ) : SailM Bool )
  let w__745 : (BitVec 1) :=
    if (w__744 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__743 18 18 w__745)
  let w__746 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__747 ← (( do (IsG1ActivityMonitorOffsetImplemented 3) ) : SailM Bool )
  let w__748 : (BitVec 1) :=
    if (w__747 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__746 19 19 w__748)
  let w__749 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__750 ← (( do (IsG1ActivityMonitorOffsetImplemented 4) ) : SailM Bool )
  let w__751 : (BitVec 1) :=
    if (w__750 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__749 20 20 w__751)
  let w__752 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__753 ← (( do (IsG1ActivityMonitorOffsetImplemented 5) ) : SailM Bool )
  let w__754 : (BitVec 1) :=
    if (w__753 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__752 21 21 w__754)
  let w__755 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__756 ← (( do (IsG1ActivityMonitorOffsetImplemented 6) ) : SailM Bool )
  let w__757 : (BitVec 1) :=
    if (w__756 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__755 22 22 w__757)
  let w__758 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__759 ← (( do (IsG1ActivityMonitorOffsetImplemented 7) ) : SailM Bool )
  let w__760 : (BitVec 1) :=
    if (w__759 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__758 23 23 w__760)
  let w__761 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__762 ← (( do (IsG1ActivityMonitorOffsetImplemented 8) ) : SailM Bool )
  let w__763 : (BitVec 1) :=
    if (w__762 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__761 24 24 w__763)
  let w__764 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__765 ← (( do (IsG1ActivityMonitorOffsetImplemented 9) ) : SailM Bool )
  let w__766 : (BitVec 1) :=
    if (w__765 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__764 25 25 w__766)
  let w__767 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__768 ← (( do (IsG1ActivityMonitorOffsetImplemented 10) ) : SailM Bool )
  let w__769 : (BitVec 1) :=
    if (w__768 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__767 26 26 w__769)
  let w__770 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__771 ← (( do (IsG1ActivityMonitorOffsetImplemented 11) ) : SailM Bool )
  let w__772 : (BitVec 1) :=
    if (w__771 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__770 27 27 w__772)
  let w__773 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__774 ← (( do (IsG1ActivityMonitorOffsetImplemented 12) ) : SailM Bool )
  let w__775 : (BitVec 1) :=
    if (w__774 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__773 28 28 w__775)
  let w__776 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__777 ← (( do (IsG1ActivityMonitorOffsetImplemented 13) ) : SailM Bool )
  let w__778 : (BitVec 1) :=
    if (w__777 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__776 29 29 w__778)
  let w__779 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__780 ← (( do (IsG1ActivityMonitorOffsetImplemented 14) ) : SailM Bool )
  let w__781 : (BitVec 1) :=
    if (w__780 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__779 30 30 w__781)
  let w__782 ← (( do readReg AMCG1IDR_EL0 ) : SailM (BitVec 64) )
  let w__783 ← (( do (IsG1ActivityMonitorOffsetImplemented 15) ) : SailM Bool )
  let w__784 : (BitVec 1) :=
    if (w__783 : Bool)
    then 1#1
    else 0#1
  writeReg AMCG1IDR_EL0 (Sail.BitVec.updateSubrange w__782 31 31 w__784)
  let w__785 ← (( do (HasArchVersion v9Ap4) ) : SailM Bool )
  if (w__785 : Bool)
  then
    (do
      let w__786 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__786 63 56 0x3F#8)
      let w__787 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__787 43 40 0b0001#4)
      let w__788 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__788 35 32 0b0001#4)
      let w__789 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__789 39 36 0b0001#4)
      let w__790 ← (( do (HaveLSE128 ()) ) : SailM Bool )
      if (w__790 : Bool)
      then
        (do
          let w__791 ← (( do readReg ID_AA64ISAR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ISAR0_EL1 (Sail.BitVec.updateSubrange w__791 23 20 0b0011#4))
      else (pure (()))
      let w__792 ← (( do (HaveGCS ()) ) : SailM Bool )
      if (w__792 : Bool)
      then
        (do
          let w__793 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__793 47 44 0b0001#4))
      else (pure (()))
      let w__794 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__794 3 0 0b0010#4)
      let w__795 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__795 47 44 0b0001#4)
      let w__796 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__796 59 56 0b0010#4)
      let w__799 ← (( do
        if ((← do
             (HaveSVE2p1 ())) : Bool)
        then (pure true)
        else
          (do
            (HaveSME2p1 ())) ) : SailM Bool )
      if (w__799 : Bool)
      then
        (do
          let w__800 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__800 43 43 1#1)
          let w__801 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__801 27 24 0b0001#4))
      else (pure (()))
      let w__802 ← (( do readReg ID_AA64SMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64SMFR0_EL1 (Sail.BitVec.updateSubrange w__802 42 42 1#1)
      let w__803 ← (( do readReg PMDEVID ) : SailM (BitVec 32) )
      writeReg PMDEVID (Sail.BitVec.updateSubrange w__803 7 4 0b0001#4)
      let w__804 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__804 27 24 0b0001#4)
      let w__805 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__805 11 8 0b0011#4)
      let w__806 ← (( do (HaveFeatEBEP ()) ) : SailM Bool )
      if (w__806 : Bool)
      then
        (do
          let w__807 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__807 51 48 0b0001#4))
      else (pure (()))
      let w__808 ← (( do readReg ID_AA64MMFR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR2_EL1 (Sail.BitVec.updateSubrange w__808 19 16 0b0010#4)
      let w__809 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__809 3 0 0b0111#4)
      let w__810 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__810 35 32 0b0001#4)
      let w__811 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__811 39 36 0b0001#4)
      let w__812 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__812 7 4 0b0010#4)
      let w__813 ← (( do (HaveMTEPermExt ()) ) : SailM Bool )
      if (w__813 : Bool)
      then
        (do
          let w__814 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__814 3 0 0b0001#4))
      else (pure (()))
      let w__815 ← (( do (HavePFAR ()) ) : SailM Bool )
      if (w__815 : Bool)
      then
        (do
          let w__816 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__816 63 60 0b0001#4))
      else (pure (()))
      let w__817 ← (( do (HaveDoubleFault2Ext ()) ) : SailM Bool )
      if (w__817 : Bool)
      then
        (do
          let w__818 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__818 59 56 0b0001#4))
      else (pure (()))
      let w__819 ← (( do (HaveTHExt ()) ) : SailM Bool )
      if (w__819 : Bool)
      then
        (do
          let w__820 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__820 51 48 0b0001#4))
      else (pure (()))
      let w__821 ← (( do (HaveMTE4Ext ()) ) : SailM Bool )
      if (w__821 : Bool)
      then
        (do
          let w__822 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__822 55 52 0b0001#4)
          let w__823 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__823 7 4 0b0001#4)
          let w__824 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__824 11 8 0b0001#4))
      else (pure (()))
      let w__825 ← (( do readReg ID_AA64MMFR4_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR4_EL1 (Sail.BitVec.updateSubrange w__825 7 4 0b0001#4)
      let w__826 ← (( do (HaveRASv2Ext ()) ) : SailM Bool )
      if (w__826 : Bool)
      then
        (do
          let w__827 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__827 31 28 0b0011#4)
          let w__828 ← (( do readReg ID_PFR0_EL1 ) : SailM (BitVec 64) )
          writeReg ID_PFR0_EL1 (Sail.BitVec.updateSubrange w__828 31 28 0b0011#4))
      else (pure (()))
      let w__829 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__829 43 40 0b0010#4)
      let w__830 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__830 47 44 0b0010#4)
      let w__831 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__831 55 52 0b0010#4)
      let w__832 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__832 59 56 0b0010#4)
      let w__833 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__833 39 36 0b0001#4)
      let w__834 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__834 35 32 0b0001#4)
      let w__835 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__835 31 24 0x3F#8)
      let w__836 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__836 23 16 0x3F#8)
      let w__837 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__837 15 8 0x3F#8)
      let w__838 ← (( do readReg ID_AA64DFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR1_EL1 (Sail.BitVec.updateSubrange w__838 7 0 0x1F#8)
      let w__839 ← (( do readReg ID_AA64PFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR1_EL1 (Sail.BitVec.updateSubrange w__839 55 52 0b0001#4)
      let w__840 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__840 47 44 0b0010#4)
      let w__841 ← (( do readReg ID_AA64ZFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ZFR0_EL1 (Sail.BitVec.updateSubrange w__841 23 20 0b0010#4)
      let w__842 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__842 43 40 0b0010#4)
      let w__843 ← (( do readReg ID_AA64ISAR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR1_EL1 (Sail.BitVec.updateSubrange w__843 23 20 0b0011#4)
      let w__844 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__844 31 28 0b0001#4)
      let w__845 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__845 55 52 0b0001#4)
      let w__846 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__846 51 48 0b0001#4)
      let w__847 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__847 43 40 0b0001#4)
      let w__848 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__848 3 0 0b0011#4)
      let w__849 ← (( do readReg ID_AA64PFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64PFR0_EL1 (Sail.BitVec.updateSubrange w__849 59 56 0b0011#4)
      let w__850 ← (( do readReg ID_AA64MMFR1_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR1_EL1 (Sail.BitVec.updateSubrange w__850 63 60 0b0001#4)
      let w__851 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__851 3 0 0b0001#4)
      let w__852 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__852 11 8 0b0001#4)
      let w__853 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__853 19 16 0b0001#4)
      let w__854 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__854 15 12 0b0001#4)
      let w__855 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__855 23 20 0b0001#4)
      let w__856 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__856 27 24 0b0001#4)
      let w__857 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__857 7 4 0b0001#4)
      let w__858 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__858 63 60 0b0001#4)
      let w__859 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__859 3 0 0b1011#4)
      let w__860 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__860 11 8 0b1001#4)
      let w__861 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__861 35 32 0b0101#4)
      let w__862 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__862 59 56 0b0001#4)
      let w__863 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__863 19 16 0b0001#4)
      let w__864 ← (( do readReg PMDEVID ) : SailM (BitVec 32) )
      writeReg PMDEVID (Sail.BitVec.updateSubrange w__864 3 0 0b0010#4)
      let w__865 ← (( do readReg PMMIR_EL1 ) : SailM (BitVec 64) )
      writeReg PMMIR_EL1 (Sail.BitVec.updateSubrange w__865 27 24 0b0001#4)
      let w__866 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
      writeReg PMCFGR (BitVec.update w__866 22 (Bit 1#1))
      let w__867 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__867 59 56 0b0010#4)
      let w__868 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__868 7 4 0b1011#4)
      let w__869 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__869 3 0 0b1011#4)
      let w__870 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
      writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__870 27 24 0b1001#4)
      let w__871 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__871 19 16 0b0010#4)
      let w__872 ← (( do readReg ID_ISAR6_EL1 ) : SailM (BitVec 64) )
      writeReg ID_ISAR6_EL1 (Sail.BitVec.updateSubrange w__872 31 28 0b0001#4)
      let w__873 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      let w__874 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
      let w__876 ← (( do
        if ((w__874 ≥b 16) : Bool)
        then (pure (0b1111#4))
        else
          (do
            let w__875 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
            (pure ((integer_subrange (w__875 -i 1) 3 0)))) ) : SailM (BitVec 4) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__873 23 20 w__876)
      let w__877 ← (( do readReg ID_AA64DFR0_EL1 ) : SailM (BitVec 64) )
      let w__878 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
      let w__880 ← (( do
        if ((w__878 ≥b 16) : Bool)
        then (pure (0b1111#4))
        else
          (do
            let w__879 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
            (pure ((integer_subrange (w__879 -i 1) 3 0)))) ) : SailM (BitVec 4) )
      writeReg ID_AA64DFR0_EL1 (Sail.BitVec.updateSubrange w__877 15 12 w__880))
  else (pure (()))


end ArmFull.Functions
