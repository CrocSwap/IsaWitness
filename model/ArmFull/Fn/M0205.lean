import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0019
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0087
import ArmFull.Fn.M0166
import ArmFull.Fn.M0197
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

/-- Type quantifiers: k_cold : Bool -/
def AArch32_AutoGen_ArchitectureReset__seg0 (cold : Bool) : SailM Bool := do
  let w__0 ← (( do (ICC_SGI1R_read ()) ) : SailM (BitVec 64) )
  (ICC_SGI1R_write (Mk_ICC_SGI1R_Type (set_slice 8 w__0 56 0b00000000#8)))
  let w__1 ← (( do (ICC_SGI1R_read ()) ) : SailM (BitVec 64) )
  (ICC_SGI1R_write (Mk_ICC_SGI1R_Type (set_slice 3 w__1 41 0b000#3)))
  let w__2 ← (( do (ICC_SGI1R_read ()) ) : SailM (BitVec 64) )
  (ICC_SGI1R_write (Mk_ICC_SGI1R_Type (set_slice 4 w__2 28 0b0000#4)))
  let w__3 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
  writeReg DBGDSAR (Sail.BitVec.updateSubrange w__3 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__4 ← (( do readReg DBGDSAR ) : SailM (BitVec 64) )
  writeReg DBGDSAR (Sail.BitVec.updateSubrange w__4 1 0 0b00#2)
  let w__5 ← (( do (ICC_SGI0R_read ()) ) : SailM (BitVec 64) )
  (ICC_SGI0R_write (Mk_ICC_SGI0R_Type (set_slice 8 w__5 56 0b00000000#8)))
  let w__6 ← (( do (ICC_SGI0R_read ()) ) : SailM (BitVec 64) )
  (ICC_SGI0R_write (Mk_ICC_SGI0R_Type (set_slice 3 w__6 41 0b000#3)))
  let w__7 ← (( do (ICC_SGI0R_read ()) ) : SailM (BitVec 64) )
  (ICC_SGI0R_write (Mk_ICC_SGI0R_Type (set_slice 4 w__7 28 0b0000#4)))
  let w__8 ← (( do (ICC_ASGI1R_read ()) ) : SailM (BitVec 64) )
  (ICC_ASGI1R_write (Mk_ICC_ASGI1R_Type (set_slice 8 w__8 56 0b00000000#8)))
  let w__9 ← (( do (ICC_ASGI1R_read ()) ) : SailM (BitVec 64) )
  (ICC_ASGI1R_write (Mk_ICC_ASGI1R_Type (set_slice 3 w__9 41 0b000#3)))
  let w__10 ← (( do (ICC_ASGI1R_read ()) ) : SailM (BitVec 64) )
  (ICC_ASGI1R_write (Mk_ICC_ASGI1R_Type (set_slice 4 w__10 28 0b0000#4)))
  let w__11 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 32 w__11 32 0b00000000000000000000000000000000#32)))
  let w__12 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 32 w__12 32 0b00000000000000000000000000000000#32)))
  let w__13 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 4 w__13 12 0b0000#4)))
  let w__14 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 4 w__14 7 0b0000#4)))
  let w__15 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 16 w__15 40 0b0000000000000000#16)))
  let w__16 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 6 w__16 1 0b000000#6)))
  let w__17 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 36 w__17 12 0b000000000000000000000000000000000000#36)))
  let w__18 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 1 w__18 10 0#1)))
  let w__19 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
  (PAR_write (Mk_PAR_Type (set_slice 1 w__19 7 0#1)))
  let w__20 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
  (TTBR1_write (Mk_TTBR1_Type (set_slice 32 w__20 32 0b00000000000000000000000000000000#32)))
  let w__21 ← (( do (TTBR1_read ()) ) : SailM (BitVec 64) )
  (TTBR1_write (Mk_TTBR1_Type (set_slice 8 w__21 56 0b00000000#8)))
  let w__22 ← (( do readReg HTTBR ) : SailM (BitVec 64) )
  writeReg HTTBR (Sail.BitVec.updateSubrange w__22 63 48 0b0000000000000000#16)
  let w__23 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
  (TTBR0_write (Mk_TTBR0_Type (set_slice 32 w__23 32 0b00000000000000000000000000000000#32)))
  let w__24 ← (( do (TTBR0_read ()) ) : SailM (BitVec 64) )
  (TTBR0_write (Mk_TTBR0_Type (set_slice 8 w__24 56 0b00000000#8)))
  let w__25 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
  (DBGDRAR_write (Mk_DBGDRAR_Type (set_slice 16 w__25 48 0b0000000000000000#16)))
  let w__26 ← (( do (DBGDRAR_read ()) ) : SailM (BitVec 64) )
  (DBGDRAR_write (Mk_DBGDRAR_Type (set_slice 10 w__26 2 0b0000000000#10)))
  let w__27 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
  writeReg VTTBR (Sail.BitVec.updateSubrange w__27 63 56 0b00000000#8)
  let w__29 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__29 : Bool)
  then
    (do
      let w__30 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
      writeReg VTTBR (Sail.BitVec.updateSubrange w__30 55 48 0b00000000#8))
  else
    (do
      let w__31 ← (( do readReg VTTBR ) : SailM (BitVec 64) )
      let w__32 ← (( do (__UNKNOWN_bits 8) ) : SailM (BitVec 8) )
      writeReg VTTBR (Sail.BitVec.updateSubrange w__31 55 48 w__32))
  let w__33 ← (( do readReg GITS_CREADR ) : SailM (BitVec 64) )
  writeReg GITS_CREADR (Sail.BitVec.updateSubrange w__33 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__34 ← (( do readReg GITS_CREADR ) : SailM (BitVec 64) )
  writeReg GITS_CREADR (Sail.BitVec.updateSubrange w__34 4 1 0b0000#4)
  let w__35 ← (( do readReg GICR_PENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_PENDBASER (BitVec.update w__35 63 (Bit 0#1))
  let w__36 ← (( do readReg GICR_PENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_PENDBASER (Sail.BitVec.updateSubrange w__36 61 59 0b000#3)
  let w__37 ← (( do readReg GICR_PENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_PENDBASER (Sail.BitVec.updateSubrange w__37 55 52 0b0000#4)
  let w__38 ← (( do readReg GICR_PENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_PENDBASER (Sail.BitVec.updateSubrange w__38 15 12 0b0000#4)
  let w__39 ← (( do readReg GICR_PENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_PENDBASER (Sail.BitVec.updateSubrange w__39 6 0 0b0000000#7)
  let w__40 ← (( do readReg GICR_PROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_PROPBASER (Sail.BitVec.updateSubrange w__40 63 59 0b00000#5)
  let w__41 ← (( do readReg GICR_PROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_PROPBASER (Sail.BitVec.updateSubrange w__41 55 52 0b0000#4)
  let w__42 ← (( do readReg GICR_PROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_PROPBASER (Sail.BitVec.updateSubrange w__42 6 5 0b00#2)
  let w__43 ← (( do readReg GICR_VPROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPROPBASER (Sail.BitVec.updateSubrange w__43 63 63 0#1)
  let w__44 ← (( do readReg GICR_VPROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPROPBASER (BitVec.update w__44 62 (Bit 0#1))
  let w__45 ← (( do readReg GICR_VPROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPROPBASER (Sail.BitVec.updateSubrange w__45 63 59 0b00000#5)
  let w__46 ← (( do readReg GICR_VPROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPROPBASER (Sail.BitVec.updateSubrange w__46 55 52 0b0000#4)
  let w__47 ← (( do readReg GICR_VPROPBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPROPBASER (Sail.BitVec.updateSubrange w__47 6 5 0b00#2)
  let w__48 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__48 63 60 0b0000#4)
  let w__49 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__49 59 56 0b0000#4)
  let w__50 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__50 55 52 0b0000#4)
  let w__51 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__51 51 48 0b0000#4)
  let w__52 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__52 43 40 0b0000#4)
  let w__53 ← (( do readReg EDPFR ) : SailM (BitVec 64) )
  writeReg EDPFR (Sail.BitVec.updateSubrange w__53 31 28 0b0000#4)
  let w__54 ← (( do readReg GICR_CLRLPIR ) : SailM (BitVec 64) )
  writeReg GICR_CLRLPIR (Sail.BitVec.updateSubrange w__54 63 32
    0b00000000000000000000000000000000#32)
  let w__55 ← (( do readReg GICR_INVALLR ) : SailM (BitVec 64) )
  writeReg GICR_INVALLR (Sail.BitVec.updateSubrange w__55 62 48 0b000000000000000#15)
  let w__56 ← (( do readReg GICR_INVALLR ) : SailM (BitVec 64) )
  writeReg GICR_INVALLR (Sail.BitVec.updateSubrange w__56 31 0 0b00000000000000000000000000000000#32)
  let w__57 ← (( do readReg EDHSR ) : SailM (BitVec 64) )
  writeReg EDHSR (Sail.BitVec.updateSubrange w__57 63 41 0b00000000000000000000000#23)
  let w__58 ← (( do readReg EDHSR ) : SailM (BitVec 64) )
  writeReg EDHSR (Sail.BitVec.updateSubrange w__58 39 24 0b0000000000000000#16)
  let w__59 ← (( do readReg EDHSR ) : SailM (BitVec 64) )
  writeReg EDHSR (BitVec.update w__59 14 (Bit 0#1))
  let w__60 ← (( do readReg EDHSR ) : SailM (BitVec 64) )
  writeReg EDHSR (Sail.BitVec.updateSubrange w__60 12 11 0b00#2)
  let w__61 ← (( do readReg EDHSR ) : SailM (BitVec 64) )
  writeReg EDHSR (BitVec.update w__61 9 (Bit 0#1))
  let w__62 ← (( do readReg EDHSR ) : SailM (BitVec 64) )
  writeReg EDHSR (BitVec.update w__62 7 (Bit 0#1))
  let w__63 ← (( do readReg EDHSR ) : SailM (BitVec 64) )
  writeReg EDHSR (Sail.BitVec.updateSubrange w__63 5 0 0b000000#6)
  let w__64 ← (( do readReg EDPCSR ) : SailM (BitVec 64) )
  writeReg EDPCSR (Sail.BitVec.updateSubrange w__64 60 56 0b00000#5)
  let w__65 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__65 63 63 0#1)
  let w__66 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__66 60 60 0#1)
  let w__67 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__67 57 16
    0b000000000000000000000000000000000000000000#42)
  let w__68 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__68 63 63 0#1)
  let w__69 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__69 61 61 0#1)
  let w__70 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__70 60 60 0#1)
  let w__71 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (BitVec.update w__71 59 (Bit 0#1))
  let w__72 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__72 55 52 0b0000#4)
  let w__73 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__73 15 12 0b0000#4)
  let w__74 ← (( do readReg GICR_VPENDBASER ) : SailM (BitVec 64) )
  writeReg GICR_VPENDBASER (Sail.BitVec.updateSubrange w__74 6 0 0b0000000#7)
  let w__75 ← (( do readReg GITS_TYPER ) : SailM (BitVec 64) )
  writeReg GITS_TYPER (Sail.BitVec.updateSubrange w__75 63 47 0b00000000000000000#17)
  let w__76 ← (( do readReg GITS_TYPER ) : SailM (BitVec 64) )
  writeReg GITS_TYPER (Sail.BitVec.updateSubrange w__76 23 20 0b0000#4)
  let w__77 ← (( do readReg GITS_SGIR ) : SailM (BitVec 64) )
  writeReg GITS_SGIR (Sail.BitVec.updateSubrange w__77 63 48 0b0000000000000000#16)
  let w__78 ← (( do readReg GITS_SGIR ) : SailM (BitVec 64) )
  writeReg GITS_SGIR (Sail.BitVec.updateSubrange w__78 31 4 0b0000000000000000000000000000#28)
  let w__79 ← (( do readReg EDDFR1 ) : SailM (BitVec 64) )
  writeReg EDDFR1 (Sail.BitVec.updateSubrange w__79 55 52 0b0000#4)
  let w__80 ← (( do readReg GITS_CWRITER ) : SailM (BitVec 64) )
  writeReg GITS_CWRITER (Sail.BitVec.updateSubrange w__80 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__81 ← (( do readReg GITS_CWRITER ) : SailM (BitVec 64) )
  writeReg GITS_CWRITER (Sail.BitVec.updateSubrange w__81 4 1 0b0000#4)
  let w__82 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__82 63 60 0b0000#4)
  let w__83 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__83 55 44 0b000000000000#12)
  let w__84 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__84 39 32 0b00000000#8)
  let w__85 ← (( do readReg EDDFR ) : SailM (BitVec 64) )
  writeReg EDDFR (Sail.BitVec.updateSubrange w__85 3 0 0b0000#4)
  let w__86 ← (( do readReg GICR_INVLPIR ) : SailM (BitVec 64) )
  writeReg GICR_INVLPIR (Sail.BitVec.updateSubrange w__86 62 48 0b000000000000000#15)
  let w__87 ← (( do readReg EDAA32PFR ) : SailM (BitVec 64) )
  writeReg EDAA32PFR (Sail.BitVec.updateSubrange w__87 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__88 ← (( do readReg GITS_CBASER ) : SailM (BitVec 64) )
  writeReg GITS_CBASER (Sail.BitVec.updateSubrange w__88 63 63 0#1)
  let w__89 ← (( do readReg GITS_CBASER ) : SailM (BitVec 64) )
  writeReg GITS_CBASER (BitVec.update w__89 62 (Bit 0#1))
  let w__90 ← (( do readReg GITS_CBASER ) : SailM (BitVec 64) )
  writeReg GITS_CBASER (Sail.BitVec.updateSubrange w__90 58 56 0b000#3)
  let w__91 ← (( do readReg GITS_CBASER ) : SailM (BitVec 64) )
  writeReg GITS_CBASER (BitVec.update w__91 52 (Bit 0#1))
  let w__92 ← (( do readReg GITS_CBASER ) : SailM (BitVec 64) )
  writeReg GITS_CBASER (Sail.BitVec.updateSubrange w__92 9 8 0b00#2)
  let w__93 ← (( do readReg GICR_SETLPIR ) : SailM (BitVec 64) )
  writeReg GICR_SETLPIR (Sail.BitVec.updateSubrange w__93 63 32
    0b00000000000000000000000000000000#32)
  let w__94 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__94 63 32 0b00000000000000000000000000000000#32)
  let w__95 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__95 27 23 0b00000#5)
  let w__96 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (BitVec.update w__96 20 (Bit 0#1))
  let w__97 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (Sail.BitVec.updateSubrange w__97 27 23 0b00000#5)
  let w__98 ← (( do readReg PMCFGR ) : SailM (BitVec 64) )
  writeReg PMCFGR (BitVec.update w__98 20 (Bit 0#1))
  let w__99 ← (( do (PMCNTEN_read ()) ) : SailM (BitVec 64) )
  (PMCNTEN_write (Mk_PMCNTEN_Type (set_slice 31 w__99 33 0b0000000000000000000000000000000#31)))
  let w__100 ← (( do readReg PMIIDR ) : SailM (BitVec 64) )
  writeReg PMIIDR (Sail.BitVec.updateSubrange w__100 63 32 0b00000000000000000000000000000000#32)
  let w__101 ← (( do readReg PMIIDR ) : SailM (BitVec 64) )
  writeReg PMIIDR (BitVec.update w__101 7 (Bit 0#1))
  let w__102 ← (( do readReg PMIIDR ) : SailM (BitVec 64) )
  writeReg PMIIDR (BitVec.update w__102 7 (Bit 0#1))
  let w__103 ← (( do (PMINTEN_read ()) ) : SailM (BitVec 64) )
  (PMINTEN_write (Mk_PMINTEN_Type (set_slice 31 w__103 33 0b0000000000000000000000000000000#31)))
  let w__104 ← (( do (PMOVS_read ()) ) : SailM (BitVec 64) )
  (PMOVS_write (Mk_PMOVS_Type (set_slice 31 w__104 33 0b0000000000000000000000000000000#31)))
  let w__105 ← (( do readReg PMPCSCTL ) : SailM (BitVec 64) )
  writeReg PMPCSCTL (Sail.BitVec.updateSubrange w__105 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__106 ← (( do readReg PMPCSCTL ) : SailM (BitVec 64) )
  writeReg PMPCSCTL (Sail.BitVec.updateSubrange w__106 4 4 0#1)
  let w__107 ← (( do readReg PMPCSCTL ) : SailM (BitVec 64) )
  writeReg PMPCSCTL (Sail.BitVec.updateSubrange w__107 3 2 0b00#2)
  let w__108 ← (( do readReg PMPCSCTL ) : SailM (BitVec 64) )
  writeReg PMPCSCTL (Sail.BitVec.updateSubrange w__108 0 0 0#1)
  let w__109 ← (( do readReg PMPCSR ) : SailM (BitVec 64) )
  writeReg PMPCSR (Sail.BitVec.updateSubrange w__109 58 56 0b000#3)
  let w__110 ← (( do readReg PMVCIDSR ) : SailM (BitVec 64) )
  writeReg PMVCIDSR (Sail.BitVec.updateSubrange w__110 63 48 0b0000000000000000#16)
  let w__111 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_EAE w__111 0#1))
  let w__112 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (Mk_TTBCR_Type (set_slice 25 w__112 6 0b0000000000000000000000000#25)))
  let w__113 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_PD1 w__113 0#1))
  let w__114 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_PD0 w__114 0#1))
  let w__115 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (Mk_TTBCR_Type (set_slice 1 w__115 3 0#1)))
  let w__116 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_N w__116 0b000#3))
  let w__117 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_EAE w__117 0#1))
  let w__118 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (Mk_TTBCR_Type (set_slice 1 w__118 30 0#1)))
  let w__119 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_SH1 w__119 0b00#2))
  let w__120 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_ORGN1 w__120 0b00#2))
  let w__121 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_IRGN1 w__121 0b00#2))
  let w__122 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_EPD1 w__122 0#1))
  let w__123 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_A1 w__123 0#1))
  let w__124 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (Mk_TTBCR_Type (set_slice 3 w__124 19 0b000#3)))
  let w__125 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_T1SZ w__125 0b000#3))
  let w__126 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (Mk_TTBCR_Type (set_slice 2 w__126 14 0b00#2)))
  let w__127 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_SH0 w__127 0b00#2))
  let w__128 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_ORGN0 w__128 0b00#2))
  let w__129 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_IRGN0 w__129 0b00#2))
  let w__130 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_EPD0 w__130 0#1))
  let w__131 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (Mk_TTBCR_Type (set_slice 3 w__131 3 0b000#3)))
  let w__132 ← (( do (TTBCR_read ()) ) : SailM (BitVec 32) )
  (TTBCR_write (_update_TTBCR_Type_T0SZ w__132 0b000#3))
  let w__133 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  (HCR_write (Mk_HCR_Type (set_slice 1 w__133 31 0#1)))
  let w__135 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__135 : Bool)
  then
    (do
      let w__136 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TRVM w__136 0#1)))
  else
    (do
      let w__137 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__138 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TRVM w__137 w__138)))
  let w__140 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__140 : Bool)
  then
    (do
      let w__141 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_HCD w__141 0#1)))
  else
    (do
      let w__142 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__143 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_HCD w__142 w__143)))
  let w__144 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  (HCR_write (Mk_HCR_Type (set_slice 1 w__144 28 0#1)))
  let w__146 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__146 : Bool)
  then
    (do
      let w__147 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TGE w__147 0#1)))
  else
    (do
      let w__148 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__149 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TGE w__148 w__149)))
  let w__151 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__151 : Bool)
  then
    (do
      let w__152 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TVM w__152 0#1)))
  else
    (do
      let w__153 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__154 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TVM w__153 w__154)))
  let w__156 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__156 : Bool)
  then
    (do
      let w__157 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TTLB w__157 0#1)))
  else
    (do
      let w__158 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__159 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TTLB w__158 w__159)))
  let w__161 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__161 : Bool)
  then
    (do
      let w__162 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TPU w__162 0#1)))
  else
    (do
      let w__163 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__164 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TPU w__163 w__164)))
  let w__166 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__166 : Bool)
  then
    (do
      let w__167 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TPC w__167 0#1)))
  else
    (do
      let w__168 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__169 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TPC w__168 w__169)))
  let w__171 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__171 : Bool)
  then
    (do
      let w__172 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TSW w__172 0#1)))
  else
    (do
      let w__173 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__174 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TSW w__173 w__174)))
  let w__176 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__176 : Bool)
  then
    (do
      let w__177 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TAC w__177 0#1)))
  else
    (do
      let w__178 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__179 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TAC w__178 w__179)))
  let w__181 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__181 : Bool)
  then
    (do
      let w__182 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TIDCP w__182 0#1)))
  else
    (do
      let w__183 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__184 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TIDCP w__183 w__184)))
  let w__186 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__186 : Bool)
  then
    (do
      let w__187 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TSC w__187 0#1)))
  else
    (do
      let w__188 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__189 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TSC w__188 w__189)))
  let w__191 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__191 : Bool)
  then
    (do
      let w__192 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TID3 w__192 0#1)))
  else
    (do
      let w__193 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__194 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TID3 w__193 w__194)))
  let w__196 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__196 : Bool)
  then
    (do
      let w__197 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TID2 w__197 0#1)))
  else
    (do
      let w__198 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__199 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TID2 w__198 w__199)))
  let w__201 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__201 : Bool)
  then
    (do
      let w__202 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TID1 w__202 0#1)))
  else
    (do
      let w__203 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__204 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TID1 w__203 w__204)))
  let w__206 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__206 : Bool)
  then
    (do
      let w__207 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TID0 w__207 0#1)))
  else
    (do
      let w__208 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__209 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TID0 w__208 w__209)))
  let w__211 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__211 : Bool)
  then
    (do
      let w__212 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TWE w__212 0#1)))
  else
    (do
      let w__213 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__214 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TWE w__213 w__214)))
  let w__216 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__216 : Bool)
  then
    (do
      let w__217 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_TWI w__217 0#1)))
  else
    (do
      let w__218 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__219 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_TWI w__218 w__219)))
  let w__221 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__221 : Bool)
  then
    (do
      let w__222 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_DC w__222 0#1)))
  else
    (do
      let w__223 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__224 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_DC w__223 w__224)))
  let w__226 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__226 : Bool)
  then
    (do
      let w__227 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_BSU w__227 0b00#2)))
  else
    (do
      let w__228 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__229 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      (HCR_write (_update_HCR_Type_BSU w__228 w__229)))
  let w__231 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__231 : Bool)
  then
    (do
      let w__232 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_FB w__232 0#1)))
  else
    (do
      let w__233 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__234 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_FB w__233 w__234)))
  let w__236 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__236 : Bool)
  then
    (do
      let w__237 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_VA w__237 0#1)))
  else
    (do
      let w__238 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__239 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_VA w__238 w__239)))
  let w__241 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__241 : Bool)
  then
    (do
      let w__242 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_VI w__242 0#1)))
  else
    (do
      let w__243 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__244 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_VI w__243 w__244)))
  let w__246 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__246 : Bool)
  then
    (do
      let w__247 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_VF w__247 0#1)))
  else
    (do
      let w__248 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__249 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_VF w__248 w__249)))
  let w__251 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__251 : Bool)
  then
    (do
      let w__252 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_AMO w__252 0#1)))
  else
    (do
      let w__253 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__254 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_AMO w__253 w__254)))
  let w__256 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__256 : Bool)
  then
    (do
      let w__257 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_IMO w__257 0#1)))
  else
    (do
      let w__258 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__259 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_IMO w__258 w__259)))
  let w__261 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__261 : Bool)
  then
    (do
      let w__262 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_FMO w__262 0#1)))
  else
    (do
      let w__263 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__264 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_FMO w__263 w__264)))
  let w__266 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__266 : Bool)
  then
    (do
      let w__267 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_PTW w__267 0#1)))
  else
    (do
      let w__268 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__269 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_PTW w__268 w__269)))
  let w__271 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__271 : Bool)
  then
    (do
      let w__272 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_SWIO w__272 0#1)))
  else
    (do
      let w__273 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__274 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_SWIO w__273 w__274)))
  let w__276 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__276 : Bool)
  then
    (do
      let w__277 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      (HCR_write (_update_HCR_Type_VM w__277 0#1)))
  else
    (do
      let w__278 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
      let w__279 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR_write (_update_HCR_Type_VM w__278 w__279)))
  let w__280 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
  (DBGOSDLR_write (Mk_DBGOSDLR_Type (set_slice 31 w__280 1 0b0000000000000000000000000000000#31)))
  let w__281 ← (( do (DBGOSDLR_read ()) ) : SailM (BitVec 32) )
  (DBGOSDLR_write (_update_DBGOSDLR_Type_DLK w__281 0#1))
  let w__282 ← (( do (ICH_ELRSR_read ()) ) : SailM (BitVec 32) )
  (ICH_ELRSR_write (Mk_ICH_ELRSR_Type (set_slice 16 w__282 16 0b0000000000000000#16)))
  let w__283 ← (( do (ICC_IAR1_read ()) ) : SailM (BitVec 32) )
  (ICC_IAR1_write (Mk_ICC_IAR1_Type (set_slice 8 w__283 24 0b00000000#8)))
  let w__284 ← (( do readReg JOSCR ) : SailM (BitVec 32) )
  writeReg JOSCR (Sail.BitVec.updateSubrange w__284 31 0 0b00000000000000000000000000000000#32)
  let w__286 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__286 : Bool)
  then
    (do
      let w__287 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TCPAC w__287 0#1)))
  else
    (do
      let w__288 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      let w__289 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCPTR_write (_update_HCPTR_Type_TCPAC w__288 w__289)))
  let w__291 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__291 : Bool)
  then
    (do
      let w__292 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TAM w__292 0#1)))
  else
    (do
      let w__293 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      let w__294 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCPTR_write (_update_HCPTR_Type_TAM w__293 w__294)))
  let w__295 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (Mk_HCPTR_Type (set_slice 9 w__295 21 0b000000000#9)))
  let w__297 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__297 : Bool)
  then
    (do
      let w__298 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TTA w__298 0#1)))
  else
    (do
      let w__299 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      let w__300 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCPTR_write (_update_HCPTR_Type_TTA w__299 w__300)))
  let w__301 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (Mk_HCPTR_Type (set_slice 4 w__301 16 0b0000#4)))
  let w__303 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__303 : Bool)
  then
    (do
      let w__304 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TASE w__304 0#1)))
  else
    (do
      let w__305 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      let w__306 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCPTR_write (_update_HCPTR_Type_TASE w__305 w__306)))
  let w__307 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (Mk_HCPTR_Type (set_slice 1 w__307 14 0#1)))
  let w__308 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (Mk_HCPTR_Type (set_slice 2 w__308 12 0b11#2)))
  let w__310 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__310 : Bool)
  then
    (do
      let w__311 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TCP11 w__311 0#1)))
  else
    (do
      let w__312 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      let w__313 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCPTR_write (_update_HCPTR_Type_TCP11 w__312 w__313)))
  let w__315 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__315 : Bool)
  then
    (do
      let w__316 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TCP10 w__316 0#1)))
  else
    (do
      let w__317 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      let w__318 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCPTR_write (_update_HCPTR_Type_TCP10 w__317 w__318)))
  let w__319 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (Mk_HCPTR_Type (set_slice 10 w__319 0 0b1111111111#10)))
  let w__320 ← (( do (ICV_IGRPEN1_read ()) ) : SailM (BitVec 32) )
  (ICV_IGRPEN1_write
    (Mk_ICV_IGRPEN1_Type (set_slice 31 w__320 1 0b0000000000000000000000000000000#31)))
  let w__321 ← (( do (ICV_IGRPEN1_read ()) ) : SailM (BitVec 32) )
  (ICV_IGRPEN1_write (_update_ICV_IGRPEN1_Type_Enable w__321 0#1))
  let w__322 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (Mk_CTR_Type (set_slice 1 w__322 31 1#1)))
  let w__323 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (Mk_CTR_Type (set_slice 1 w__323 30 0#1)))
  let w__324 ← (( do (CTR_read ()) ) : SailM (BitVec 32) )
  (CTR_write (Mk_CTR_Type (set_slice 10 w__324 4 0b0000000000#10)))
  let w__325 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
  (PMUSERENR_write (Mk_PMUSERENR_Type (set_slice 25 w__325 7 0b0000000000000000000000000#25)))
  let w__326 ← (( do (PMUSERENR_read ()) ) : SailM (BitVec 32) )
  (PMUSERENR_write (Mk_PMUSERENR_Type (set_slice 2 w__326 4 0b00#2)))
  let w__327 ← (( do (CNTHPS_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTHPS_CTL_write (Mk_CNTHPS_CTL_Type (set_slice 29 w__327 3 0b00000000000000000000000000000#29)))
  let w__328 ← (( do (DBGAUTHSTATUS_read ()) ) : SailM (BitVec 32) )
  (DBGAUTHSTATUS_write (Mk_DBGAUTHSTATUS_Type (set_slice 24 w__328 8 0b000000000000000000000000#24)))
  let w__329 ← (( do (ICC_IAR0_read ()) ) : SailM (BitVec 32) )
  (ICC_IAR0_write (Mk_ICC_IAR0_Type (set_slice 8 w__329 24 0b00000000#8)))
  let w__330 ← (( do (ICV_IGRPEN0_read ()) ) : SailM (BitVec 32) )
  (ICV_IGRPEN0_write
    (Mk_ICV_IGRPEN0_Type (set_slice 31 w__330 1 0b0000000000000000000000000000000#31)))
  let w__331 ← (( do (ICV_IGRPEN0_read ()) ) : SailM (BitVec 32) )
  (ICV_IGRPEN0_write (_update_ICV_IGRPEN0_Type_Enable w__331 0#1))
  let w__332 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
  (PRRR_write (Mk_PRRR_Type (set_slice 4 w__332 20 0b0000#4)))
  let w__333 ← (( do (ICV_CTLR_read ()) ) : SailM (BitVec 32) )
  (ICV_CTLR_write (Mk_ICV_CTLR_Type (set_slice 12 w__333 20 0b000000000000#12)))
  let w__334 ← (( do (ICV_CTLR_read ()) ) : SailM (BitVec 32) )
  (ICV_CTLR_write (Mk_ICV_CTLR_Type (set_slice 2 w__334 16 0b00#2)))
  let w__335 ← (( do (ICV_CTLR_read ()) ) : SailM (BitVec 32) )
  (ICV_CTLR_write (Mk_ICV_CTLR_Type (set_slice 6 w__335 2 0b000000#6)))
  let w__336 ← (( do (HPFAR_read ()) ) : SailM (BitVec 32) )
  (HPFAR_write (Mk_HPFAR_Type (set_slice 4 w__336 0 0b0000#4)))
  let w__337 ← (( do (DBGCLAIMCLR_read ()) ) : SailM (BitVec 32) )
  (DBGCLAIMCLR_write (Mk_DBGCLAIMCLR_Type (set_slice 24 w__337 8 0b000000000000000000000000#24)))
  if (cold : Bool)
  then
    (do
      let w__338 ← (( do (DBGCLAIMCLR_read ()) ) : SailM (BitVec 32) )
      (DBGCLAIMCLR_write (_update_DBGCLAIMCLR_Type_CLAIM w__338 0b00000000#8)))
  else (pure (()))
  let w__339 ← (( do (ICV_HPPIR1_read ()) ) : SailM (BitVec 32) )
  (ICV_HPPIR1_write (Mk_ICV_HPPIR1_Type (set_slice 8 w__339 24 0b00000000#8)))
  let w__340 ← (( do (ID_MMFR5_read ()) ) : SailM (BitVec 32) )
  (ID_MMFR5_write (Mk_ID_MMFR5_Type (set_slice 24 w__340 8 0b000000000000000000000000#24)))
  let w__341 ← (( do (HRMR_read ()) ) : SailM (BitVec 32) )
  (HRMR_write (Mk_HRMR_Type (set_slice 30 w__341 2 0b000000000000000000000000000000#30)))
  let w__342 ← (( do (HRMR_read ()) ) : SailM (BitVec 32) )
  (HRMR_write (_update_HRMR_Type_RR w__342 0#1))
  let w__343 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  (HCR2_write (Mk_HCR2_Type (set_slice 9 w__343 23 0b000000000#9)))
  let w__345 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__345 : Bool)
  then
    (do
      let w__346 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_TTLBIS w__346 0#1)))
  else
    (do
      let w__347 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__348 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_TTLBIS w__347 w__348)))
  let w__349 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  (HCR2_write (Mk_HCR2_Type (set_slice 1 w__349 21 0#1)))
  let w__351 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__351 : Bool)
  then
    (do
      let w__352 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_TOCU w__352 0#1)))
  else
    (do
      let w__353 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__354 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_TOCU w__353 w__354)))
  let w__355 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  (HCR2_write (Mk_HCR2_Type (set_slice 1 w__355 19 0#1)))
  let w__357 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__357 : Bool)
  then
    (do
      let w__358 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_TICAB w__358 0#1)))
  else
    (do
      let w__359 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__360 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_TICAB w__359 w__360)))
  let w__362 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__362 : Bool)
  then
    (do
      let w__363 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_TID4 w__363 0#1)))
  else
    (do
      let w__364 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__365 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_TID4 w__364 w__365)))
  let w__366 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  (HCR2_write (Mk_HCR2_Type (set_slice 10 w__366 7 0b0000000000#10)))
  let w__368 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__368 : Bool)
  then
    (do
      let w__369 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_TEA w__369 0#1)))
  else
    (do
      let w__370 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__371 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_TEA w__370 w__371)))
  let w__373 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__373 : Bool)
  then
    (do
      let w__374 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_TERR w__374 0#1)))
  else
    (do
      let w__375 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__376 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_TERR w__375 w__376)))
  let w__377 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  (HCR2_write (Mk_HCR2_Type (set_slice 2 w__377 2 0b00#2)))
  let w__379 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__379 : Bool)
  then
    (do
      let w__380 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_ID w__380 0#1)))
  else
    (do
      let w__381 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__382 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_ID w__381 w__382)))
  (pure true)


end ArmFull.Functions
