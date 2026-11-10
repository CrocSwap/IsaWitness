import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0008
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0021
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0037
import ArmFull.Fn.M0039
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0045
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0058
import ArmFull.Fn.M0092
import ArmFull.Fn.M0196
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

def AArch32_IMPDEFResets (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_IMP w__0 (Zeros (n := 8))))
  let w__1 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  let w__2 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  let w__3 : (BitVec 8) :=
    if ((IsZero (_get_PMCR_Type_IMP w__2)) : Bool)
    then (Zeros (n := 8))
    else CFG_PMCR_IDCODE
  (PMCR_write (_update_PMCR_Type_IDCODE w__1 w__3))
  let w__4 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  let w__5 ← (( do readReg NUM_PMU_COUNTERS ) : SailM Int )
  (PMCR_write (_update_PMCR_Type_N w__4 (integer_subrange w__5 4 0)))
  let w__6 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_C w__6 0#1))
  let w__7 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_P w__7 0#1))
  (PMCEID0_write (Mk_PMCEID0_Type 0b01001000000000100000000100000001#32))
  (PMCEID2_write (Mk_PMCEID2_Type (Sail.BitVec.zeroExtend 0b1111#4 32)))
  (PMCEID1_write (Mk_PMCEID1_Type (Zeros (n := 32))))
  (PMCEID3_write (Mk_PMCEID3_Type (Zeros (n := 32))))
  let w__8 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__8 31 28 0b0000#4)
  let w__9 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__9 21 21 1#1)
  let w__10 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__10 19 19 0#1)
  let w__11 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__11 18 18 0#1)
  let w__12 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__12 17 17 0#1)
  let w__13 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__13 16 16 0#1)
  let w__14 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__14 15 15 1#1)
  let w__15 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__15 14 14 1#1)
  let w__16 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__16 13 8 0b111111#6)
  let w__17 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  let w__18 ← (( do readReg NUM_PMU_COUNTERS ) : SailM Int )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__17 7 0 (0b000#3 +++ (integer_subrange w__18 4 0)))
  let w__19 ← (( do readReg PMDEVTYPE ) : SailM (BitVec 32) )
  writeReg PMDEVTYPE (Sail.BitVec.updateSubrange w__19 7 4 0b0001#4)
  let w__20 ← (( do readReg PMDEVTYPE ) : SailM (BitVec 32) )
  writeReg PMDEVTYPE (Sail.BitVec.updateSubrange w__20 3 0 0b0110#4)
  let w__21 ← (( do readReg PMPIDR0 ) : SailM (BitVec 32) )
  writeReg PMPIDR0 (Sail.BitVec.updateSubrange w__21 7 0 0b00001111#8)
  let w__22 ← (( do readReg PMPIDR1 ) : SailM (BitVec 32) )
  writeReg PMPIDR1 (Sail.BitVec.updateSubrange w__22 7 4 0b1011#4)
  let w__23 ← (( do readReg PMPIDR1 ) : SailM (BitVec 32) )
  writeReg PMPIDR1 (Sail.BitVec.updateSubrange w__23 3 0 0b1101#4)
  let w__24 ← (( do readReg PMPIDR2 ) : SailM (BitVec 32) )
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange w__24 7 4 0b0000#4)
  let w__25 ← (( do readReg PMPIDR2 ) : SailM (BitVec 32) )
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange w__25 3 3 1#1)
  let w__26 ← (( do readReg PMPIDR2 ) : SailM (BitVec 32) )
  writeReg PMPIDR2 (Sail.BitVec.updateSubrange w__26 2 0 0b011#3)
  let w__27 ← (( do readReg PMPIDR3 ) : SailM (BitVec 32) )
  writeReg PMPIDR3 (Sail.BitVec.updateSubrange w__27 7 4 0b0000#4)
  let w__28 ← (( do readReg PMPIDR3 ) : SailM (BitVec 32) )
  writeReg PMPIDR3 (Sail.BitVec.updateSubrange w__28 3 0 0b0000#4)
  let w__29 ← (( do readReg PMPIDR4 ) : SailM (BitVec 32) )
  writeReg PMPIDR4 (Sail.BitVec.updateSubrange w__29 7 4 0b0000#4)
  let w__30 ← (( do readReg PMPIDR4 ) : SailM (BitVec 32) )
  writeReg PMPIDR4 (Sail.BitVec.updateSubrange w__30 3 0 0b0100#4)
  let w__31 ← (( do readReg PMCIDR0 ) : SailM (BitVec 32) )
  writeReg PMCIDR0 (Sail.BitVec.updateSubrange w__31 7 0 0b00001101#8)
  let w__32 ← (( do readReg PMCIDR1 ) : SailM (BitVec 32) )
  writeReg PMCIDR1 (Sail.BitVec.updateSubrange w__32 7 4 0b1001#4)
  let w__33 ← (( do readReg PMCIDR1 ) : SailM (BitVec 32) )
  writeReg PMCIDR1 (Sail.BitVec.updateSubrange w__33 3 0 0b0000#4)
  let w__34 ← (( do readReg PMCIDR2 ) : SailM (BitVec 32) )
  writeReg PMCIDR2 (Sail.BitVec.updateSubrange w__34 7 0 0b00000101#8)
  let w__35 ← (( do readReg PMCIDR3 ) : SailM (BitVec 32) )
  writeReg PMCIDR3 (Sail.BitVec.updateSubrange w__35 7 0 0b10110001#8)
  let w__36 ← (( do readReg VBAR_S ) : SailM (BitVec 32) )
  writeReg VBAR_S (Sail.BitVec.updateSubrange w__36 31 5 (Zeros (n := 27)))
  let w__37 ← (( do (CCSIDR_read ()) ) : SailM (BitVec 32) )
  (CCSIDR_write (_update_CCSIDR_Type_Associativity w__37 (Sail.BitVec.zeroExtend 0x1#4 21)))
  let w__38 ← (( do (CCSIDR_read ()) ) : SailM (BitVec 32) )
  (CCSIDR_write (_update_CCSIDR_Type_LineSize w__38 0b010#3))
  let w__39 ← (( do (CLIDR_read ()) ) : SailM (BitVec 32) )
  (CLIDR_write (_update_CLIDR_Type_ICB w__39 0b00#2))
  let w__40 ← (( do (CLIDR_read ()) ) : SailM (BitVec 32) )
  (CLIDR_write (_update_CLIDR_Type_LoUU w__40 0b000#3))
  let w__41 ← (( do (CLIDR_read ()) ) : SailM (BitVec 32) )
  (CLIDR_write (_update_CLIDR_Type_LoUIS w__41 0b000#3))
  let w__42 ← (( do (CLIDR_read ()) ) : SailM (BitVec 32) )
  (CLIDR_write (Mk_CLIDR_Type (Sail.BitVec.updateSubrange w__42 20 0 0b000000000000000100011#21)))
  let w__43 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (_update_CTR_Type_DIC w__43 0#1))
  let w__44 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (_update_CTR_Type_IDC w__44 0#1))
  let w__45 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (_update_CTR_Type_CWG w__45 0b0100#4))
  let w__46 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  let w__47 ← (( do readReg __exclusive_granule_size ) : SailM (BitVec 4) )
  (CTR_write (_update_CTR_Type_ERG w__46 w__47))
  let w__48 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (_update_CTR_Type_DminLine w__48 0b0100#4))
  let w__49 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (_update_CTR_Type_L1Ip w__49 0b10#2))
  let w__50 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (_update_CTR_Type_IminLine w__50 0b0100#4))
  let w__51 ← (( do readReg FPSID ) : SailM (BitVec 32) )
  writeReg FPSID (Sail.BitVec.updateSubrange w__51 31 24 0b01000001#8)
  let w__52 ← (( do readReg FPSID ) : SailM (BitVec 32) )
  writeReg FPSID (Sail.BitVec.updateSubrange w__52 23 23 0#1)
  let w__53 ← (( do readReg FPSID ) : SailM (BitVec 32) )
  writeReg FPSID (Sail.BitVec.updateSubrange w__53 22 16 0b0000100#7)
  let w__54 ← (( do readReg FPSID ) : SailM (BitVec 32) )
  writeReg FPSID (Sail.BitVec.updateSubrange w__54 15 8 0b00110000#8)
  let w__55 ← (( do readReg FPSID ) : SailM (BitVec 32) )
  writeReg FPSID (Sail.BitVec.updateSubrange w__55 7 4 0b0111#4)
  let w__56 ← (( do readReg FPSID ) : SailM (BitVec 32) )
  writeReg FPSID (Sail.BitVec.updateSubrange w__56 3 0 0b0000#4)
  let w__57 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
  (ID_DFR0_write (_update_ID_DFR0_Type_MProfDbg w__57 0b0000#4))
  let w__58 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
  (ID_DFR0_write (_update_ID_DFR0_Type_MMapDbg w__58 0b0000#4))
  let w__60 ← (( do
    if (((! (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__59 ← (( do readReg SCR ) : SailM (BitVec 32) )
        (pure ((((_get_SCR_Type_NS w__59) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__60 : Bool)
  then
    (do
      let w__61 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg w__61 0b0000#4)))
  else
    (do
      let w__62 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      let w__63 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg w__62 (_get_ID_DFR0_Type_CopDbg w__63))))
  let w__64 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Divide w__64 0b0010#4))
  let w__65 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Debug w__65 0b0001#4))
  let w__66 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Coproc w__66 0b0000#4))
  let w__67 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (_update_ID_ISAR0_Type_CmpBranch w__67 0b0001#4))
  let w__68 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (_update_ID_ISAR0_Type_BitField w__68 0b0001#4))
  let w__69 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (_update_ID_ISAR0_Type_BitCount w__69 0b0001#4))
  let w__70 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (_update_ID_ISAR0_Type_Swap w__70 0b0000#4))
  let w__71 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Jazelle w__71 0b0001#4))
  let w__72 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Interwork w__72 0b0011#4))
  let w__73 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Immediate w__73 0b0001#4))
  let w__74 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_IfThen w__74 0b0001#4))
  let w__75 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Extend w__75 0b0010#4))
  let w__76 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Except_AR w__76 0b0001#4))
  let w__77 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Except w__77 0b0001#4))
  let w__78 ← (( do (ID_ISAR1_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR1_write (_update_ID_ISAR1_Type_Endian w__78 0b0001#4))
  let w__79 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_Reversal w__79 0b0010#4))
  let w__80 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_PSR_AR w__80 0b0001#4))
  let w__81 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MultU w__81 0b0010#4))
  let w__82 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MultS w__82 0b0011#4))
  let w__83 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_Mult w__83 0b0010#4))
  let w__84 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MultiAccessInt w__84 0b0000#4))
  let w__85 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_MemHint w__85 0b0100#4))
  let w__86 ← (( do (ID_ISAR2_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR2_write (_update_ID_ISAR2_Type_LoadStore w__86 0b0010#4))
  let w__87 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_T32EE w__87 0b0000#4))
  let w__88 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_TrueNOP w__88 0b0001#4))
  let w__89 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_T32Copy w__89 0b0001#4))
  let w__90 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_TabBranch w__90 0b0001#4))
  let w__91 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_SynchPrim w__91 0b0010#4))
  let w__92 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_SVC w__92 0b0001#4))
  let w__93 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_SIMD w__93 0b0011#4))
  let w__94 ← (( do (ID_ISAR3_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR3_write (_update_ID_ISAR3_Type_Saturate w__94 0b0001#4))
  let w__95 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_SWP_frac w__95 0b0000#4))
  let w__96 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_PSR_M w__96 0b0000#4))
  let w__97 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_SynchPrim_frac w__97 0b0000#4))
  let w__98 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_Barrier w__98 0b0001#4))
  let w__99 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_SMC w__99 0b0000#4))
  let w__100 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_Writeback w__100 0b0001#4))
  let w__101 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_WithShifts w__101 0b0100#4))
  let w__102 ← (( do (ID_ISAR4_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR4_write (_update_ID_ISAR4_Type_Unpriv w__102 0b0010#4))
  let w__103 ← (( do readReg ID_MMFR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR5_EL1 (Sail.BitVec.updateSubrange w__103 7 4 0b0001#4)
  let w__104 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (_update_ID_ISAR5_Type_VCMA w__104 0b0001#4))
  let w__105 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (_update_ID_ISAR5_Type_RDM w__105 0b0001#4))
  let w__106 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (_update_ID_ISAR5_Type_CRC32 w__106 0b0000#4))
  let w__107 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (_update_ID_ISAR5_Type_SHA2 w__107 0b0001#4))
  let w__108 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (_update_ID_ISAR5_Type_SHA1 w__108 0b0001#4))
  let w__109 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (_update_ID_ISAR5_Type_AES w__109 0b0010#4))
  let w__110 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (_update_ID_ISAR5_Type_SEVL w__110 0b0001#4))
  let w__111 ← (( do (ID_ISAR6_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR6_write (_update_ID_ISAR6_Type_DP w__111 0b0001#4))
  let w__112 ← (( do (ID_ISAR6_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR6_write (_update_ID_ISAR6_Type_BF16 w__112 0b0001#4))
  let w__113 ← (( do (ID_ISAR6_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR6_write (_update_ID_ISAR6_Type_I8MM w__113 0b0001#4))
  let w__114 ← (( do (IsFeatureImplemented FEAT_FP16) ) : SailM Bool )
  if (w__114 : Bool)
  then
    (do
      let w__115 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
      (MVFR1_write (_update_MVFR1_Type_FPHP w__115 0b0011#4))
      let w__116 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
      (MVFR1_write (_update_MVFR1_Type_SIMDHP w__116 0b0010#4)))
  else
    (do
      let w__117 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
      (MVFR1_write (_update_MVFR1_Type_FPHP w__117 0b0010#4))
      let w__118 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
      (MVFR1_write (_update_MVFR1_Type_SIMDHP w__118 0b0001#4)))
  if ((HasArchVersion v8Ap3) : Bool)
  then
    (do
      let w__119 ← (( do (ID_MMFR4_read ()) ) : SailM (BitVec 32) )
      (ID_MMFR4_write (_update_ID_MMFR4_Type_CCIDX w__119 0b0001#4))
      let w__120 ← (( do (ID_ISAR6_read ()) ) : SailM (BitVec 32) )
      (ID_ISAR6_write (_update_ID_ISAR6_Type_JSCVT w__120 0b0001#4))
      let w__121 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_TraceFilt w__121 0b0001#4)))
  else (pure (()))
  if ((HasArchVersion v8Ap4) : Bool)
  then
    (do
      let w__122 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
      writeReg EDPFR (Sail.BitVec.updateSubrange w__122 39 36 0b0001#4)
      let w__123 ← (( do (ID_ISAR6_read ()) ) : SailM (BitVec 32) )
      (ID_ISAR6_write (_update_ID_ISAR6_Type_FHM w__123 0b0001#4))
      let w__124 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
      (ID_PFR0_write (_update_ID_PFR0_Type_AMU w__124 0b0001#4))
      let w__125 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
      (ID_PFR0_write (_update_ID_PFR0_Type_DIT w__125 0b0001#4))
      let w__126 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_CopDbg w__126 0b1001#4))
      let w__128 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then
          (do
            let w__127 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__127) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__128 : Bool)
      then
        (do
          let w__129 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
          (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg w__129 0b0000#4)))
      else
        (do
          let w__130 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
          let w__131 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
          (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg w__130 (_get_ID_DFR0_EL1_Type_CopDbg w__131)))))
  else (pure (()))
  if ((HasArchVersion v8Ap7) : Bool)
  then
    (do
      let w__132 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon w__132 0b0111#4)))
  else (pure (()))
  if ((HasArchVersion v8Ap8) : Bool)
  then
    (do
      let w__133 ← (( do (ID_MMFR5_read ()) ) : SailM (BitVec 32) )
      (ID_MMFR5_write (_update_ID_MMFR5_Type_ETS w__133 0b0010#4))
      let w__134 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_CopDbg w__134 0b1010#4))
      let w__136 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then
          (do
            let w__135 ← (( do readReg SCR ) : SailM (BitVec 32) )
            (pure ((((_get_SCR_Type_NS w__135) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__136 : Bool)
      then
        (do
          let w__137 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
          (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg w__137 0b0000#4)))
      else
        (do
          let w__138 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
          let w__139 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
          (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg w__138 (_get_ID_DFR0_Type_CopDbg w__139)))))
  else (pure (()))
  if ((HasArchVersion v8Ap6) : Bool)
  then
    (do
      let w__140 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
      (ID_PFR1_write (_update_ID_PFR1_Type_GenTimer w__140 0b0010#4))
      let w__141 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
      (ID_PFR0_write (_update_ID_PFR0_Type_AMU w__141 0b0010#4)))
  else (pure (()))
  let w__142 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_InnerShr w__142 0b0001#4))
  let w__143 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_FCSE w__143 0b0000#4))
  let w__144 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_AuxReg w__144 0b0010#4))
  let w__145 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_TCM w__145 0b0000#4))
  let w__146 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_ShareLvl w__146 0b0001#4))
  let w__147 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_OuterShr w__147 0b0001#4))
  let w__148 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_PMSA w__148 0b0000#4))
  let w__149 ← (( do (ID_MMFR0_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR0_write (_update_ID_MMFR0_Type_VMSA w__149 0b0101#4))
  let w__150 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_BPred w__150 0b0010#4))
  let w__151 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1TstCln w__151 0b0000#4))
  let w__152 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1Uni w__152 0b0000#4))
  let w__153 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1Hvd w__153 0b0000#4))
  let w__154 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1UniSW w__154 0b0000#4))
  let w__155 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1HvdSW w__155 0b0000#4))
  let w__156 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1UniVA w__156 0b0000#4))
  let w__157 ← (( do (ID_MMFR1_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR1_write (_update_ID_MMFR1_Type_L1HvdVA w__157 0b0000#4))
  let w__158 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_HWAccFlg w__158 0b0000#4))
  let w__159 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_WFIStall w__159 0b0001#4))
  let w__160 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_MemBarr w__160 0b0010#4))
  let w__161 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_UniTLB w__161 0b0110#4))
  let w__162 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_HvdTLB w__162 0b0000#4))
  let w__163 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_L1HvdRng w__163 0b0000#4))
  let w__164 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_L1HvdBG w__164 0b0000#4))
  let w__165 ← (( do (ID_MMFR2_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR2_write (_update_ID_MMFR2_Type_L1HvdFG w__165 0b0000#4))
  let w__166 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_Supersec w__166 0b0000#4))
  let w__167 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CMemSz w__167 0b0010#4))
  let w__168 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CohWalk w__168 0b0001#4))
  let w__169 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_PAN w__169 0b0001#4))
  let w__170 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_MaintBcst w__170 0b0010#4))
  let w__171 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_BPMaint w__171 0b0010#4))
  let w__172 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CMaintSW w__172 0b0001#4))
  let w__173 ← (( do (ID_MMFR3_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR3_write (_update_ID_MMFR3_Type_CMaintVA w__173 0b0001#4))
  let w__174 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
  (ID_PFR0_write (_update_ID_PFR0_Type_RAS w__174 0b0010#4))
  let w__175 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
  (ID_PFR0_write (_update_ID_PFR0_Type_State3 w__175 0b0000#4))
  let w__176 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
  (ID_PFR0_write (_update_ID_PFR0_Type_State2 w__176 0b0001#4))
  let w__177 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
  (ID_PFR0_write (_update_ID_PFR0_Type_State1 w__177 0b0011#4))
  let w__178 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
  (ID_PFR0_write (_update_ID_PFR0_Type_State0 w__178 0b0001#4))
  let w__179 ← (( do (ID_DFR1_read ()) ) : SailM (BitVec 32) )
  (ID_DFR1_write (_update_ID_DFR1_Type_MTPMU w__179 0b0001#4))
  if ((HasArchVersion v8Ap5) : Bool)
  then
    (do
      let w__180 ← (( do (ID_PFR0_read ()) ) : SailM (BitVec 32) )
      (ID_PFR0_write (_update_ID_PFR0_Type_CSV2 w__180 0b0001#4))
      let w__181 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon w__181 0b0110#4)))
  else (pure (()))
  let w__182 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
  (ID_DFR0_write (_update_ID_DFR0_Type_MMapTrc w__182 0b0001#4))
  let w__183 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
  (ID_DFR0_write (_update_ID_DFR0_Type_CopTrc w__183 0b0001#4))
  let w__184 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
  (ID_PFR1_write (_update_ID_PFR1_Type_GIC w__184 0b0000#4))
  let w__185 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
  (ID_PFR1_write (_update_ID_PFR1_Type_Virt_frac w__185 0b0000#4))
  let w__186 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
  (ID_PFR1_write (_update_ID_PFR1_Type_Sec_frac w__186 0b0000#4))
  let w__187 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
  (ID_PFR1_write (_update_ID_PFR1_Type_MProgMod w__187 0b0000#4))
  let w__188 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
  (ID_PFR1_write (_update_ID_PFR1_Type_ProgMod w__188 0b0000#4))
  let w__189 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
  (ID_PFR1_write (_update_ID_PFR1_Type_Security w__189 0b0000#4))
  let w__190 ← (( do (ID_PFR1_read ()) ) : SailM (BitVec 32) )
  (ID_PFR1_write (_update_ID_PFR1_Type_Virtualization w__190 0b0000#4))
  let w__191 ← (( do (MIDR_read ()) ) : SailM (BitVec 32) )
  (MIDR_write (_update_MIDR_Type_Implementer w__191 0b01000001#8))
  let w__192 ← (( do (MIDR_read ()) ) : SailM (BitVec 32) )
  (MIDR_write (_update_MIDR_Type_Variant w__192 0b0000#4))
  let w__193 ← (( do (MIDR_read ()) ) : SailM (BitVec 32) )
  (MIDR_write (_update_MIDR_Type_Architecture w__193 0b1111#4))
  let w__194 ← (( do (MIDR_read ()) ) : SailM (BitVec 32) )
  (MIDR_write (_update_MIDR_Type_PartNum w__194 0b110100001111#12))
  let w__195 ← (( do (MIDR_read ()) ) : SailM (BitVec 32) )
  (MIDR_write (_update_MIDR_Type_Revision w__195 0b0000#4))
  let w__196 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  (VPIDR_write (_update_VPIDR_Type_Implementer w__196 0b01000001#8))
  let w__197 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  (VPIDR_write (_update_VPIDR_Type_Variant w__197 0b0000#4))
  let w__198 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  (VPIDR_write (_update_VPIDR_Type_Architecture w__198 0b1111#4))
  let w__199 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  (VPIDR_write (_update_VPIDR_Type_PartNum w__199 0b110100001111#12))
  let w__200 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  (VPIDR_write (_update_VPIDR_Type_Revision w__200 0b0000#4))
  let w__201 ← (( do (MPIDR_read ()) ) : SailM (BitVec 32) )
  (MPIDR_write (_update_MPIDR_Type_M w__201 1#1))
  let w__202 ← (( do (MPIDR_read ()) ) : SailM (BitVec 32) )
  (MPIDR_write (_update_MPIDR_Type_U w__202 0#1))
  let w__203 ← (( do (MPIDR_read ()) ) : SailM (BitVec 32) )
  (MPIDR_write (_update_MPIDR_Type_MT w__203 0#1))
  let w__204 ← (( do (MPIDR_read ()) ) : SailM (BitVec 32) )
  (MPIDR_write (_update_MPIDR_Type_Aff2 w__204 0b00000000#8))
  let w__205 ← (( do (MPIDR_read ()) ) : SailM (BitVec 32) )
  (MPIDR_write (_update_MPIDR_Type_Aff1 w__205 0b00000000#8))
  let w__206 ← (( do (MPIDR_read ()) ) : SailM (BitVec 32) )
  (MPIDR_write (_update_MPIDR_Type_Aff0 w__206 0b00000000#8))
  let w__207 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_FPRound w__207 0b0001#4))
  let w__208 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_FPShVec w__208 0b0000#4))
  let w__209 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_FPSqrt w__209 0b0001#4))
  let w__210 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_FPDivide w__210 0b0001#4))
  let w__211 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_FPTrap w__211 0b0001#4))
  let w__212 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_FPDP w__212 0b0010#4))
  let w__213 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_FPSP w__213 0b0010#4))
  let w__214 ← (( do (MVFR0_read ()) ) : SailM (BitVec 32) )
  (MVFR0_write (_update_MVFR0_Type_SIMDReg w__214 0b0010#4))
  let w__215 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
  (MVFR1_write (_update_MVFR1_Type_SIMDFMAC w__215 0b0001#4))
  let w__216 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
  (MVFR1_write (_update_MVFR1_Type_SIMDSP w__216 0b0001#4))
  let w__217 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
  (MVFR1_write (_update_MVFR1_Type_SIMDInt w__217 0b0001#4))
  let w__218 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
  (MVFR1_write (_update_MVFR1_Type_SIMDLS w__218 0b0001#4))
  let w__219 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
  (MVFR1_write (_update_MVFR1_Type_FPDNaN w__219 0b0001#4))
  let w__220 ← (( do (MVFR1_read ()) ) : SailM (BitVec 32) )
  (MVFR1_write (_update_MVFR1_Type_FPFtZ w__220 0b0001#4))
  let w__221 ← (( do (MVFR2_read ()) ) : SailM (BitVec 32) )
  (MVFR2_write (_update_MVFR2_Type_FPMisc w__221 0b0100#4))
  let w__222 ← (( do (MVFR2_read ()) ) : SailM (BitVec 32) )
  (MVFR2_write (_update_MVFR2_Type_SIMDMisc w__222 0b0011#4))
  let w__223 ← (( do readReg TLBTR ) : SailM (BitVec 32) )
  writeReg TLBTR (Sail.BitVec.updateSubrange w__223 0 0 0#1)
  let w__224 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (_update_HSCTLR_Type_EE w__224 0#1))
  let w__225 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let w__226 ← (( do readReg _ConfigReg ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_TE w__225 (_get_Configuration_Type_ExceptInit w__226)))
  let w__227 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  let w__228 ← (( do readReg _ConfigReg ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_EE w__227 (_get_Configuration_Type_CFGEND w__228)))
  let w__229 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_SPAN w__229 0#1))
  let w__230 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_V w__230 0#1))
  let w__231 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_UNK w__231 0#1))
  let w__232 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_EX w__232 0#1))
  let w__233 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_FP2V w__233 0#1))
  let w__234 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_VV w__234 0#1))
  let w__235 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_TFV w__235 0#1))
  let w__236 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_VECITR w__236 0b111#3))
  let w__237 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_HWU62 w__237 0#1))
  let w__238 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_HWU61 w__238 0#1))
  let w__239 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_HWU60 w__239 0#1))
  let w__240 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_HWU59 w__240 0#1))
  let w__241 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_HPD w__241 0#1))
  let w__242 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_SH0 w__242 0b00#2))
  let w__243 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_ORGN0 w__243 0b00#2))
  let w__244 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_IRGN0 w__244 0b00#2))
  let w__245 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (_update_HTCR_Type_T0SZ w__245 0b000#3))
  let w__246 ← (( do (NMRR_read ()) ) : SailM (BitVec 32) )
  (NMRR_write (Mk_NMRR_Type (Sail.BitVec.updateSubrange w__246 31 16 0b0100010011100000#16)))
  let w__247 ← (( do (NMRR_read ()) ) : SailM (BitVec 32) )
  (NMRR_write (Mk_NMRR_Type (Sail.BitVec.updateSubrange w__247 15 0 0b0100100011100000#16)))
  let w__248 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (Sail.BitVec.updateSubrange w__248 11 11 0#1)
  let w__249 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (Sail.BitVec.updateSubrange w__249 10 10 0#1)
  let w__250 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
  (PRRR_write (Mk_PRRR_Type (Sail.BitVec.updateSubrange w__250 31 24 (Zeros (n := 8)))))
  let w__251 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
  (PRRR_write (_update_PRRR_Type_NS1 w__251 1#1))
  let w__252 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
  (PRRR_write (_update_PRRR_Type_NS0 w__252 0#1))
  let w__253 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
  (PRRR_write (_update_PRRR_Type_DS1 w__253 0#1))
  let w__254 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
  (PRRR_write (_update_PRRR_Type_DS0 w__254 1#1))
  let w__255 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
  (PRRR_write (Mk_PRRR_Type (Sail.BitVec.updateSubrange w__255 15 0 0b1000101010100100#16)))
  let w__256 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  let w__257 ← (( do readReg NUM_WATCHPOINTS ) : SailM Int )
  writeReg DBGDIDR (Sail.BitVec.updateSubrange w__256 31 28 (integer_subrange (w__257 -i 1) 3 0))
  let w__258 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  let w__259 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  writeReg DBGDIDR (Sail.BitVec.updateSubrange w__258 27 24 (integer_subrange (w__259 -i 1) 3 0))
  let w__260 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  let w__261 ← (( do readReg __num_ctx_breakpoints ) : SailM Int )
  writeReg DBGDIDR (Sail.BitVec.updateSubrange w__260 23 20 (integer_subrange (w__261 -i 1) 3 0))
  if ((HasArchVersion v8Ap2) : Bool)
  then
    (do
      let w__262 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
      writeReg DBGDIDR (Sail.BitVec.updateSubrange w__262 19 16 0b1000#4))
  else (pure (()))
  if ((HasArchVersion v8Ap4) : Bool)
  then
    (do
      let w__263 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
      writeReg DBGDIDR (Sail.BitVec.updateSubrange w__263 19 16 0b1001#4))
  else (pure (()))
  if ((HasArchVersion v8Ap8) : Bool)
  then
    (do
      let w__264 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
      writeReg DBGDIDR (Sail.BitVec.updateSubrange w__264 19 16 0b1010#4)
      let w__265 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon w__265 0b1000#4)))
  else (pure (()))
  let w__266 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  writeReg DBGDIDR (Sail.BitVec.updateSubrange w__266 14 14 1#1)
  let w__267 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  writeReg DBGDIDR (Sail.BitVec.updateSubrange w__267 12 12 1#1)
  let w__268 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
  writeReg DBGDEVID (Sail.BitVec.updateSubrange w__268 7 4 0b0001#4)
  let w__269 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
  writeReg DBGDEVID (Sail.BitVec.updateSubrange w__269 11 8 0b1111#4)
  let w__270 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
  writeReg DBGDEVID (Sail.BitVec.updateSubrange w__270 15 12 0b0000#4)
  let w__271 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
  writeReg DBGDEVID (Sail.BitVec.updateSubrange w__271 19 16 0b0001#4)
  let w__272 ← (( do readReg DBGDEVID ) : SailM (BitVec 32) )
  writeReg DBGDEVID (Sail.BitVec.updateSubrange w__272 27 24 0b0001#4)
  let w__273 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let w__274 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (HDCR_write (_update_HDCR_Type_HPMN w__273 (_get_PMCR_Type_N w__274)))
  let w__275 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  writeReg ICC_MSRE (Sail.BitVec.updateSubrange w__275 0 0 1#1)
  let w__276 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  (ICC_HSRE_write (_update_ICC_HSRE_Type_SRE w__276 1#1))
  writeReg JMCR (Zeros (n := 32))
  writeReg JOSCR (Zeros (n := 32))
  writeReg JIDR (Zeros (n := 32))
  let w__277 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLM w__277 0b10#2))
  let w__278 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK w__278 1#1))
  let w__279 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (_update_HCPTR_Type_TCPAC w__279 0#1))
  let w__280 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (_update_HCPTR_Type_TTA w__280 0#1))
  let w__281 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (_update_HCPTR_Type_TASE w__281 0#1))
  let w__282 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (_update_HCPTR_Type_TCP11 w__282 0#1))
  let w__283 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (_update_HCPTR_Type_TCP10 w__283 0#1))
  if ((HasArchVersion v9Ap4) : Bool)
  then
    (do
      let w__284 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_CopSDbg w__284 0b1011#4))
      let w__285 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_CopDbg w__285 0b1011#4))
      let w__286 ← (( do (ID_DFR0_read ()) ) : SailM (BitVec 32) )
      (ID_DFR0_write (_update_ID_DFR0_Type_PerfMon w__286 0b1001#4))
      let w__287 ← (( do (ID_ISAR6_read ()) ) : SailM (BitVec 32) )
      (ID_ISAR6_write (_update_ID_ISAR6_Type_SPECRES w__287 0b0010#4))
      let w__288 ← (( do (ID_ISAR6_read ()) ) : SailM (BitVec 32) )
      (ID_ISAR6_write (Mk_ID_ISAR6_Type (Sail.BitVec.updateSubrange w__288 31 28 0b0001#4)))
      let w__289 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
      writeReg DBGDIDR (Sail.BitVec.updateSubrange w__289 19 16 0b1011#4)
      let w__290 ← (( do readReg EDDEVID1 ) : SailM (BitVec 32) )
      writeReg EDDEVID1 (Sail.BitVec.updateSubrange w__290 7 4 0b0010#4))
  else (pure (()))


end ArmFull.Functions
