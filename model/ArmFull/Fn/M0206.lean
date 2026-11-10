import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0087
import ArmFull.Fn.M0108
import ArmFull.Fn.M0121
import ArmFull.Fn.M0144
import ArmFull.Fn.M0166
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0199
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
def AArch32_AutoGen_ArchitectureReset__seg1 (cold : Bool) : SailM Bool := do
  let w__384 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__384 : Bool)
  then
    (do
      let w__385 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      (HCR2_write (_update_HCR2_Type_CD w__385 0#1)))
  else
    (do
      let w__386 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
      let w__387 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HCR2_write (_update_HCR2_Type_CD w__386 w__387)))
  let w__388 ← (( do (ID_PFR2_read ()) ) : SailM (BitVec 32) )
  (ID_PFR2_write (Mk_ID_PFR2_Type (set_slice 20 w__388 12 0b00000000000000000000#20)))
  let w__389 ← (( do (ICV_EOIR0_read ()) ) : SailM (BitVec 32) )
  (ICV_EOIR0_write (Mk_ICV_EOIR0_Type (set_slice 8 w__389 24 0b00000000#8)))
  let w__390 ← (( do (ICH_VTR_read ()) ) : SailM (BitVec 32) )
  (ICH_VTR_write (Mk_ICH_VTR_Type (set_slice 14 w__390 5 0b00000000000000#14)))
  let w__391 ← (( do (CSSELR_read ()) ) : SailM (BitVec 32) )
  (CSSELR_write (Mk_CSSELR_Type (set_slice 28 w__391 4 0b0000000000000000000000000000#28)))
  let w__392 ← (( do readReg JIDR ) : SailM (BitVec 32) )
  writeReg JIDR (Sail.BitVec.updateSubrange w__392 31 0 0b00000000000000000000000000000000#32)
  let w__393 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (Mk_PMCR_Type (set_slice 1 w__393 10 0#1)))
  let w__394 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (Mk_PMCR_Type (set_slice 1 w__394 8 0#1)))
  let w__395 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_LP w__395 0#1))
  let w__396 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_DP w__396 0#1))
  let w__397 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_X w__397 0#1))
  let w__398 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_D w__398 0#1))
  let w__399 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
  (PMCR_write (_update_PMCR_Type_E w__399 0#1))
  let w__400 ← (( do (ICH_VMCR_read ()) ) : SailM (BitVec 32) )
  (ICH_VMCR_write (Mk_ICH_VMCR_Type (set_slice 8 w__400 10 0b00000000#8)))
  let w__401 ← (( do (ICH_VMCR_read ()) ) : SailM (BitVec 32) )
  (ICH_VMCR_write (Mk_ICH_VMCR_Type (set_slice 4 w__401 5 0b0000#4)))
  let w__402 ← (( do readReg DBGDEVID1 ) : SailM (BitVec 32) )
  writeReg DBGDEVID1 (Sail.BitVec.updateSubrange w__402 31 4 0b0000000000000000000000000000#28)
  let w__403 ← (( do (ICC_BPR1_read ()) ) : SailM (BitVec 32) )
  (ICC_BPR1_write (Mk_ICC_BPR1_Type (set_slice 29 w__403 3 0b00000000000000000000000000000#29)))
  let w__404 ← (( do (ICV_RPR_read ()) ) : SailM (BitVec 32) )
  (ICV_RPR_write (Mk_ICV_RPR_Type (set_slice 24 w__404 8 0b000000000000000000000000#24)))
  let w__405 ← (( do (VBAR_read__2 ()) ) : SailM (BitVec 32) )
  (VBAR_write (set_slice 5 w__405 0 0b00000#5))
  let w__406 ← (( do (ID_ISAR0_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR0_write (Mk_ID_ISAR0_Type (set_slice 4 w__406 28 0b0000#4)))
  let w__407 ← (( do (ICV_IAR1_read ()) ) : SailM (BitVec 32) )
  (ICV_IAR1_write (Mk_ICV_IAR1_Type (set_slice 8 w__407 24 0b00000000#8)))
  let w__408 ← (( do (DBGPRCR_read ()) ) : SailM (BitVec 32) )
  (DBGPRCR_write (Mk_DBGPRCR_Type (set_slice 31 w__408 1 0b0000000000000000000000000000000#31)))
  let w__409 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
  (SDER_write (Mk_SDER_Type (set_slice 30 w__409 2 0b000000000000000000000000000000#30)))
  let w__410 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
  (SDER_write (_update_SDER_Type_SUNIDEN w__410 0#1))
  let w__411 ← (( do (SDER_read ()) ) : SailM (BitVec 32) )
  (SDER_write (_update_SDER_Type_SUIDEN w__411 0#1))
  let w__412 ← (( do (ICC_EOIR1_read ()) ) : SailM (BitVec 32) )
  (ICC_EOIR1_write (Mk_ICC_EOIR1_Type (set_slice 8 w__412 24 0b00000000#8)))
  let w__413 ← (( do (ICC_BPR0_read ()) ) : SailM (BitVec 32) )
  (ICC_BPR0_write (Mk_ICC_BPR0_Type (set_slice 29 w__413 3 0b00000000000000000000000000000#29)))
  let w__414 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
  (CNTHCTL_write (Mk_CNTHCTL_Type (set_slice 14 w__414 18 0b00000000000000#14)))
  let w__415 ← (( do (CNTHCTL_read ()) ) : SailM (BitVec 32) )
  (CNTHCTL_write (Mk_CNTHCTL_Type (set_slice 9 w__415 8 0b000000000#9)))
  let w__416 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__416 29 0#1)))
  let w__417 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 9 w__417 16 0b000000000#9)))
  let w__418 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__418 13 0#1)))
  let w__419 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 2 w__419 8 0b00#2)))
  let w__420 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__420 5 0#1)))
  let w__421 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__421 0 0#1)))
  let w__422 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__422 29 0#1)))
  let w__423 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 17 w__423 8 0b00000000000000000#17)))
  let w__424 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__424 5 0#1)))
  let w__425 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__425 0 0#1)))
  let w__426 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 24 w__426 8 0b000000000000000000000000#24)))
  let w__427 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__427 5 0#1)))
  let w__428 ← (( do (DBGVCR_read ()) ) : SailM (BitVec 32) )
  (DBGVCR_write (Mk_DBGVCR_Type (set_slice 1 w__428 0 0#1)))
  let w__429 ← (( do (ICC_EOIR0_read ()) ) : SailM (BitVec 32) )
  (ICC_EOIR0_write (Mk_ICC_EOIR0_Type (set_slice 8 w__429 24 0b00000000#8)))
  let w__430 ← (( do (ICV_BPR1_read ()) ) : SailM (BitVec 32) )
  (ICV_BPR1_write (Mk_ICV_BPR1_Type (set_slice 29 w__430 3 0b00000000000000000000000000000#29)))
  let w__431 ← (( do (ICC_RPR_read ()) ) : SailM (BitVec 32) )
  (ICC_RPR_write (Mk_ICC_RPR_Type (set_slice 24 w__431 8 0b000000000000000000000000#24)))
  let w__432 ← (( do (MVFR2_read ()) ) : SailM (BitVec 32) )
  (MVFR2_write (Mk_MVFR2_Type (set_slice 24 w__432 8 0b000000000000000000000000#24)))
  let w__433 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  writeReg ICC_MSRE (Sail.BitVec.updateSubrange w__433 31 4 0b0000000000000000000000000000#28)
  let w__434 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  writeReg ICC_MSRE (Sail.BitVec.updateSubrange w__434 2 2 0#1)
  let w__435 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  writeReg ICC_MSRE (Sail.BitVec.updateSubrange w__435 1 1 0#1)
  let w__436 ← (( do readReg ICC_MSRE ) : SailM (BitVec 32) )
  writeReg ICC_MSRE (Sail.BitVec.updateSubrange w__436 0 0 0#1)
  let w__437 ← (( do readReg PMMIR ) : SailM (BitVec 32) )
  writeReg PMMIR (Sail.BitVec.updateSubrange w__437 31 28 0b0000#4)
  let w__438 ← (( do (VMPIDR_read ()) ) : SailM (BitVec 32) )
  let w__439 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
  (VMPIDR_write (_update_VMPIDR_Type_U w__438 w__439))
  let w__440 ← (( do (VMPIDR_read ()) ) : SailM (BitVec 32) )
  (VMPIDR_write (Mk_VMPIDR_Type (set_slice 5 w__440 25 0b00000#5)))
  let w__441 ← (( do (VMPIDR_read ()) ) : SailM (BitVec 32) )
  let w__442 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
  (VMPIDR_write (_update_VMPIDR_Type_MT w__441 w__442))
  let w__443 ← (( do (VMPIDR_read ()) ) : SailM (BitVec 32) )
  let w__444 ← (( do (__UNKNOWN_bits 8) ) : SailM (BitVec 8) )
  (VMPIDR_write (_update_VMPIDR_Type_Aff2 w__443 w__444))
  let w__445 ← (( do (VMPIDR_read ()) ) : SailM (BitVec 32) )
  let w__446 ← (( do (__UNKNOWN_bits 8) ) : SailM (BitVec 8) )
  (VMPIDR_write (_update_VMPIDR_Type_Aff1 w__445 w__446))
  let w__447 ← (( do (VMPIDR_read ()) ) : SailM (BitVec 32) )
  let w__448 ← (( do (__UNKNOWN_bits 8) ) : SailM (BitVec 8) )
  (VMPIDR_write (_update_VMPIDR_Type_Aff0 w__447 w__448))
  let w__449 ← (( do (ICC_IGRPEN1_read ()) ) : SailM (BitVec 32) )
  (ICC_IGRPEN1_write
    (Mk_ICC_IGRPEN1_Type (set_slice 31 w__449 1 0b0000000000000000000000000000000#31)))
  let w__450 ← (( do (ICC_IGRPEN1_read ()) ) : SailM (BitVec 32) )
  (ICC_IGRPEN1_write (_update_ICC_IGRPEN1_Type_Enable w__450 0#1))
  let w__451 ← (( do (HVBAR_read ()) ) : SailM (BitVec 32) )
  (HVBAR_write (set_slice 5 w__451 0 0b00000#5))
  let w__452 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  (HSTR_write (Mk_HSTR_Type (set_slice 16 w__452 16 (BitVec.slice 0b000000000000000000#18 2 16))))
  let w__453 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  (HSTR_write (Mk_HSTR_Type (set_slice 1 w__453 14 (BitVec.slice 0b000000000000000000#18 1 1))))
  let w__454 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  (HSTR_write (Mk_HSTR_Type (set_slice 1 w__454 4 (BitVec.slice 0b000000000000000000#18 0 1))))
  let w__456 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__456 : Bool)
  then
    (do
      let w__457 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T15 w__457 0#1)))
  else
    (do
      let w__458 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__459 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T15 w__458 w__459)))
  let w__461 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__461 : Bool)
  then
    (do
      let w__462 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T13 w__462 0#1)))
  else
    (do
      let w__463 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__464 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T13 w__463 w__464)))
  let w__466 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__466 : Bool)
  then
    (do
      let w__467 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T12 w__467 0#1)))
  else
    (do
      let w__468 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__469 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T12 w__468 w__469)))
  let w__471 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__471 : Bool)
  then
    (do
      let w__472 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T11 w__472 0#1)))
  else
    (do
      let w__473 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__474 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T11 w__473 w__474)))
  let w__476 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__476 : Bool)
  then
    (do
      let w__477 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T10 w__477 0#1)))
  else
    (do
      let w__478 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__479 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T10 w__478 w__479)))
  let w__481 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__481 : Bool)
  then
    (do
      let w__482 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T9 w__482 0#1)))
  else
    (do
      let w__483 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__484 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T9 w__483 w__484)))
  let w__486 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__486 : Bool)
  then
    (do
      let w__487 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T8 w__487 0#1)))
  else
    (do
      let w__488 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__489 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T8 w__488 w__489)))
  let w__491 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__491 : Bool)
  then
    (do
      let w__492 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T7 w__492 0#1)))
  else
    (do
      let w__493 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__494 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T7 w__493 w__494)))
  let w__496 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__496 : Bool)
  then
    (do
      let w__497 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T6 w__497 0#1)))
  else
    (do
      let w__498 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__499 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T6 w__498 w__499)))
  let w__501 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__501 : Bool)
  then
    (do
      let w__502 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T5 w__502 0#1)))
  else
    (do
      let w__503 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__504 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T5 w__503 w__504)))
  let w__506 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__506 : Bool)
  then
    (do
      let w__507 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T3 w__507 0#1)))
  else
    (do
      let w__508 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__509 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T3 w__508 w__509)))
  let w__511 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__511 : Bool)
  then
    (do
      let w__512 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T2 w__512 0#1)))
  else
    (do
      let w__513 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__514 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T2 w__513 w__514)))
  let w__516 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__516 : Bool)
  then
    (do
      let w__517 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T1 w__517 0#1)))
  else
    (do
      let w__518 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__519 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T1 w__518 w__519)))
  let w__521 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__521 : Bool)
  then
    (do
      let w__522 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      (HSTR_write (_update_HSTR_Type_T0 w__522 0#1)))
  else
    (do
      let w__523 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
      let w__524 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HSTR_write (_update_HSTR_Type_T0 w__523 w__524)))
  let w__525 ← (( do readReg ICC_MCTLR ) : SailM (BitVec 32) )
  writeReg ICC_MCTLR (Sail.BitVec.updateSubrange w__525 31 20 0b000000000000#12)
  let w__526 ← (( do readReg ICC_MCTLR ) : SailM (BitVec 32) )
  writeReg ICC_MCTLR (BitVec.update w__526 16 (Bit 0#1))
  let w__527 ← (( do readReg ICC_MCTLR ) : SailM (BitVec 32) )
  writeReg ICC_MCTLR (BitVec.update w__527 7 (Bit 0#1))
  let w__528 ← (( do readReg ICC_MCTLR ) : SailM (BitVec 32) )
  writeReg ICC_MCTLR (Sail.BitVec.updateSubrange w__528 6 6 0#1)
  let w__529 ← (( do (ICC_DIR_read ()) ) : SailM (BitVec 32) )
  (ICC_DIR_write (Mk_ICC_DIR_Type (set_slice 8 w__529 24 0b00000000#8)))
  let w__530 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
  (PMSELR_write (Mk_PMSELR_Type (set_slice 27 w__530 5 0b000000000000000000000000000#27)))
  let w__531 ← (( do (ID_AFR0_read ()) ) : SailM (BitVec 32) )
  (ID_AFR0_write (set_slice 16 w__531 16 0b0000000000000000#16))
  let w__532 ← (( do (DBGCLAIMSET_read ()) ) : SailM (BitVec 32) )
  (DBGCLAIMSET_write (Mk_DBGCLAIMSET_Type (set_slice 24 w__532 8 0b000000000000000000000000#24)))
  if (cold : Bool)
  then
    (do
      let w__533 ← (( do (DBGCLAIMSET_read ()) ) : SailM (BitVec 32) )
      (DBGCLAIMSET_write (_update_DBGCLAIMSET_Type_CLAIM w__533 0b00000000#8)))
  else (pure (()))
  let w__534 ← (( do (ICC_IGRPEN0_read ()) ) : SailM (BitVec 32) )
  (ICC_IGRPEN0_write
    (Mk_ICC_IGRPEN0_Type (set_slice 31 w__534 1 0b0000000000000000000000000000000#31)))
  let w__535 ← (( do (ICC_IGRPEN0_read ()) ) : SailM (BitVec 32) )
  (ICC_IGRPEN0_write (_update_ICC_IGRPEN0_Type_Enable w__535 0#1))
  let w__536 ← (( do (ICC_CTLR_read ()) ) : SailM (BitVec 32) )
  (ICC_CTLR_write (Mk_ICC_CTLR_Type (set_slice 12 w__536 20 0b000000000000#12)))
  let w__537 ← (( do (ICC_CTLR_read ()) ) : SailM (BitVec 32) )
  (ICC_CTLR_write (Mk_ICC_CTLR_Type (set_slice 2 w__537 16 0b00#2)))
  let w__538 ← (( do (ICC_CTLR_read ()) ) : SailM (BitVec 32) )
  (ICC_CTLR_write (Mk_ICC_CTLR_Type (set_slice 1 w__538 7 0#1)))
  let w__539 ← (( do (ICC_CTLR_read ()) ) : SailM (BitVec 32) )
  (ICC_CTLR_write (Mk_ICC_CTLR_Type (set_slice 4 w__539 2 0b0000#4)))
  let w__540 ← (( do (CNTHVS_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTHVS_CTL_write (Mk_CNTHVS_CTL_Type (set_slice 29 w__540 3 0b00000000000000000000000000000#29)))
  let w__541 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__541 31 16 0b0000000000000000#16)
  let w__542 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__542 15 15 0#1)
  let w__543 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (BitVec.update w__543 14 (Bit 0#1))
  let w__544 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__544 13 13 0#1)
  let w__545 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__545 12 12 0#1)
  let w__546 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__546 11 10 0b00#2)
  let w__547 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__547 9 9 0#1)
  let w__548 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__548 8 8 0#1)
  let w__549 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__549 7 7 0#1)
  let w__550 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__550 6 6 0#1)
  let w__551 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__551 5 5 0#1)
  let w__552 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__552 4 4 0#1)
  let w__553 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__553 3 3 0#1)
  let w__554 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__554 2 2 0#1)
  let w__555 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__555 1 1 0#1)
  let w__556 ← (( do readReg SCR ) : SailM (BitVec 32) )
  writeReg SCR (Sail.BitVec.updateSubrange w__556 0 0 0#1)
  let w__557 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (Sail.BitVec.updateSubrange w__557 31 21 0b00000000000#11)
  let w__558 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (Sail.BitVec.updateSubrange w__558 20 20 0#1)
  let w__559 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (BitVec.update w__559 19 (Bit 0#1))
  let w__560 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (Sail.BitVec.updateSubrange w__560 15 15 0#1)
  let w__561 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (Sail.BitVec.updateSubrange w__561 14 12 0b000#3)
  let w__562 ← (( do readReg NSACR ) : SailM (BitVec 32) )
  writeReg NSACR (Sail.BitVec.updateSubrange w__562 9 0 0b0000000000#10)
  let w__563 ← (( do (ICV_BPR0_read ()) ) : SailM (BitVec 32) )
  (ICV_BPR0_write (Mk_ICV_BPR0_Type (set_slice 29 w__563 3 0b00000000000000000000000000000#29)))
  let w__564 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (Mk_ICH_EISR_Type (set_slice 16 w__564 16 0b0000000000000000#16)))
  let w__565 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status15 w__565 0#1))
  let w__566 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status14 w__566 0#1))
  let w__567 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status13 w__567 0#1))
  let w__568 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status12 w__568 0#1))
  let w__569 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status11 w__569 0#1))
  let w__570 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status10 w__570 0#1))
  let w__571 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status9 w__571 0#1))
  let w__572 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status8 w__572 0#1))
  let w__573 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status7 w__573 0#1))
  let w__574 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status6 w__574 0#1))
  let w__575 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status5 w__575 0#1))
  let w__576 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status4 w__576 0#1))
  let w__577 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status3 w__577 0#1))
  let w__578 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status2 w__578 0#1))
  let w__579 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status1 w__579 0#1))
  let w__580 ← (( do (ICH_EISR_read ()) ) : SailM (BitVec 32) )
  (ICH_EISR_write (_update_ICH_EISR_Type_Status0 w__580 0#1))
  let w__581 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  (HDCR_write (Mk_HDCR_Type (set_slice 2 w__581 30 0b00#2)))
  if ((cold && true) : Bool)
  then
    (do
      let w__582 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__583 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_MTPME w__582 w__583)))
  else
    (do
      let w__585 ← (( do
        if ((cold : Bool) : Bool)
        then
          (do
            (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
        else (pure false) ) : SailM Bool )
      if (w__585 : Bool)
      then
        (do
          let w__586 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
          (HDCR_write (_update_HDCR_Type_MTPME w__586 1#1)))
      else (pure (())))
  let w__588 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__588 : Bool)
  then
    (do
      let w__589 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TDCC w__589 0#1)))
  else
    (do
      let w__590 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__591 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TDCC w__590 w__591)))
  let w__592 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  (HDCR_write (Mk_HDCR_Type (set_slice 2 w__592 24 0b00#2)))
  let w__594 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__594 : Bool)
  then
    (do
      let w__595 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_HCCD w__595 0#1)))
  else
    (do
      let w__596 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__597 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_HCCD w__596 w__597)))
  let w__598 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  (HDCR_write (Mk_HDCR_Type (set_slice 3 w__598 20 0b000#3)))
  let w__600 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__600 : Bool)
  then
    (do
      let w__601 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TTRF w__601 0#1)))
  else
    (do
      let w__602 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__603 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TTRF w__602 w__603)))
  let w__604 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  (HDCR_write (Mk_HDCR_Type (set_slice 1 w__604 18 0#1)))
  let w__606 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__605 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        (pure (((! w__605) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__606 : Bool)
  then
    (do
      let w__607 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_HPMD w__607 0#1)))
  else
    (do
      let w__608 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__609 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_HPMD w__608 w__609)))
  let w__610 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  (HDCR_write (Mk_HDCR_Type (set_slice 5 w__610 12 0b00000#5)))
  let w__612 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__612 : Bool)
  then
    (do
      let w__613 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TDRA w__613 0#1)))
  else
    (do
      let w__614 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__615 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TDRA w__614 w__615)))
  let w__617 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__617 : Bool)
  then
    (do
      let w__618 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TDOSA w__618 0#1)))
  else
    (do
      let w__619 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__620 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TDOSA w__619 w__620)))
  let w__622 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__622 : Bool)
  then
    (do
      let w__623 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TDA w__623 0#1)))
  else
    (do
      let w__624 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__625 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TDA w__624 w__625)))
  let w__627 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__627 : Bool)
  then
    (do
      let w__628 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TDE w__628 0#1)))
  else
    (do
      let w__629 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__630 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TDE w__629 w__630)))
  let w__632 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__631 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        (pure (((! w__631) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__632 : Bool)
  then
    (do
      let w__633 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_HPME w__633 0#1)))
  else
    (do
      let w__634 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__635 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_HPME w__634 w__635)))
  let w__637 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__636 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        (pure (((! w__636) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__637 : Bool)
  then
    (do
      let w__638 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TPM w__638 0#1)))
  else
    (do
      let w__639 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__640 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TPM w__639 w__640)))
  let w__642 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__642 : Bool)
  then
    (do
      let w__643 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      (HDCR_write (_update_HDCR_Type_TPMCR w__643 0#1)))
  else
    (do
      let w__644 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
      let w__645 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HDCR_write (_update_HDCR_Type_TPMCR w__644 w__645)))
  let w__646 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let w__647 ← (( do (__UNKNOWN_bits 5) ) : SailM (BitVec 5) )
  (HDCR_write (_update_HDCR_Type_HPMN w__646 w__647))
  let w__648 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  (ICC_HSRE_write (Mk_ICC_HSRE_Type (set_slice 28 w__648 4 0b0000000000000000000000000000#28)))
  let w__649 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  (ICC_HSRE_write (_update_ICC_HSRE_Type_DIB w__649 0#1))
  let w__650 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  (ICC_HSRE_write (_update_ICC_HSRE_Type_DFB w__650 0#1))
  let w__651 ← (( do (ICC_HSRE_read ()) ) : SailM (BitVec 32) )
  (ICC_HSRE_write (_update_ICC_HSRE_Type_SRE w__651 0#1))
  let w__652 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
  (PMCCFILTR_write (_update_PMCCFILTR_Type_P w__652 0#1))
  let w__653 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
  (PMCCFILTR_write (_update_PMCCFILTR_Type_U w__653 0#1))
  let w__654 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
  (PMCCFILTR_write (_update_PMCCFILTR_Type_NSK w__654 0#1))
  let w__655 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
  (PMCCFILTR_write (_update_PMCCFILTR_Type_NSU w__655 0#1))
  let w__656 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
  (PMCCFILTR_write (_update_PMCCFILTR_Type_NSH w__656 0#1))
  let w__657 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
  (PMCCFILTR_write (Mk_PMCCFILTR_Type (set_slice 5 w__657 22 0b00000#5)))
  let w__658 ← (( do (PMCCFILTR_read ()) ) : SailM (BitVec 32) )
  (PMCCFILTR_write (Mk_PMCCFILTR_Type (set_slice 21 w__658 0 0b000000000000000000000#21)))
  let w__659 ← (( do (ID_ISAR5_read ()) ) : SailM (BitVec 32) )
  (ID_ISAR5_write (Mk_ID_ISAR5_Type (set_slice 4 w__659 20 0b0000#4)))
  let w__660 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (Mk_HTCR_Type (set_slice 1 w__660 31 1#1)))
  let w__661 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (Mk_HTCR_Type (set_slice 1 w__661 29 0#1)))
  let w__662 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (Mk_HTCR_Type (set_slice 1 w__662 23 1#1)))
  let w__663 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (Mk_HTCR_Type (set_slice 9 w__663 14 0b000000000#9)))
  let w__664 ← (( do (HTCR_read ()) ) : SailM (BitVec 32) )
  (HTCR_write (Mk_HTCR_Type (set_slice 5 w__664 3 0b00000#5)))
  let w__665 ← (( do (ICC_PMR_read ()) ) : SailM (BitVec 32) )
  (ICC_PMR_write (Mk_ICC_PMR_Type (set_slice 24 w__665 8 0b000000000000000000000000#24)))
  let w__666 ← (( do (ICC_PMR_read ()) ) : SailM (BitVec 32) )
  (ICC_PMR_write (_update_ICC_PMR_Type_Priority w__666 0b00000000#8))
  let w__667 ← (( do (ICV_EOIR1_read ()) ) : SailM (BitVec 32) )
  (ICV_EOIR1_write (Mk_ICV_EOIR1_Type (set_slice 8 w__667 24 0b00000000#8)))
  let w__668 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_EOIcount w__668 0b00000#5))
  let w__669 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (Mk_ICH_HCR_Type (set_slice 12 w__669 15 0b000000000000#12)))
  let w__670 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_TDIR w__670 0#1))
  let w__671 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_TSEI w__671 0#1))
  let w__672 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_TALL1 w__672 0#1))
  let w__673 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_TALL0 w__673 0#1))
  let w__674 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_TC w__674 0#1))
  let w__675 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (Mk_ICH_HCR_Type (set_slice 1 w__675 9 0#1)))
  let w__676 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_vSGIEOICount w__676 0#1))
  let w__677 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_VGrp1DIE w__677 0#1))
  let w__678 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_VGrp1EIE w__678 0#1))
  let w__679 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_VGrp0DIE w__679 0#1))
  let w__680 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_VGrp0EIE w__680 0#1))
  let w__681 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_NPIE w__681 0#1))
  let w__682 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_LRENPIE w__682 0#1))
  let w__683 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_UIE w__683 0#1))
  let w__684 ← (( do (ICH_HCR_read ()) ) : SailM (BitVec 32) )
  (ICH_HCR_write (_update_ICH_HCR_Type_En w__684 0#1))
  let w__685 ← (( do (RMR_read ()) ) : SailM (BitVec 32) )
  (RMR_write (Mk_RMR_Type (set_slice 30 w__685 2 0b000000000000000000000000000000#30)))
  let w__686 ← (( do (RMR_read ()) ) : SailM (BitVec 32) )
  (RMR_write (_update_RMR_Type_RR w__686 0#1))
  let w__687 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (_update_FPEXC_Type_EN w__687 0#1))
  let w__688 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (Mk_FPEXC_Type (set_slice 15 w__688 11 0b000000000000000#15)))
  let w__689 ← (( do (FPEXC_read ()) ) : SailM (BitVec 32) )
  (FPEXC_write (Mk_FPEXC_Type (set_slice 2 w__689 5 0b00#2)))
  let w__690 ← (( do (ICC_HPPIR0_read ()) ) : SailM (BitVec 32) )
  (ICC_HPPIR0_write (Mk_ICC_HPPIR0_Type (set_slice 8 w__690 24 0b00000000#8)))
  let w__691 ← (( do (TTBCR2_read ()) ) : SailM (BitVec 32) )
  (TTBCR2_write (Mk_TTBCR2_Type (set_slice 13 w__691 19 0b0000000000000#13)))
  let w__692 ← (( do (TTBCR2_read ()) ) : SailM (BitVec 32) )
  (TTBCR2_write (Mk_TTBCR2_Type (set_slice 9 w__692 0 0b000000000#9)))
  let w__693 ← (( do readReg FCSEIDR ) : SailM (BitVec 32) )
  writeReg FCSEIDR (Sail.BitVec.updateSubrange w__693 31 0 0b00000000000000000000000000000000#32)
  let w__694 ← (( do (ID_DFR1_read ()) ) : SailM (BitVec 32) )
  (ID_DFR1_write (Mk_ID_DFR1_Type (set_slice 24 w__694 8 0b000000000000000000000000#24)))
  let w__695 ← (( do readReg JMCR ) : SailM (BitVec 32) )
  writeReg JMCR (Sail.BitVec.updateSubrange w__695 31 0 0b00000000000000000000000000000000#32)
  let w__696 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  (CNTKCTL_write (Mk_CNTKCTL_Type (set_slice 14 w__696 18 0b00000000000000#14)))
  let w__697 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
  (CNTKCTL_write (Mk_CNTKCTL_Type (set_slice 7 w__697 10 0b0000000#7)))
  let w__698 ← (( do (ICV_PMR_read ()) ) : SailM (BitVec 32) )
  (ICV_PMR_write (Mk_ICV_PMR_Type (set_slice 24 w__698 8 0b000000000000000000000000#24)))
  let w__699 ← (( do (ICV_PMR_read ()) ) : SailM (BitVec 32) )
  (ICV_PMR_write (_update_ICV_PMR_Type_Priority w__699 0b00000000#8))
  let w__700 ← (( do (ICV_HPPIR0_read ()) ) : SailM (BitVec 32) )
  (ICV_HPPIR0_write (Mk_ICV_HPPIR0_Type (set_slice 8 w__700 24 0b00000000#8)))
  let w__701 ← (( do readReg DBGWFAR ) : SailM (BitVec 32) )
  writeReg DBGWFAR (Sail.BitVec.updateSubrange w__701 31 0 0b00000000000000000000000000000000#32)
  let w__702 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 2 w__702 28 0b11#2)))
  let w__703 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 2 w__703 26 0b00#2)))
  let w__704 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 w__704 24 0#1)))
  let w__705 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 2 w__705 22 0b11#2)))
  let w__706 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 2 w__706 20 0b00#2)))
  let w__707 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 w__707 18 1#1)))
  let w__708 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 w__708 17 0#1)))
  let w__709 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 w__709 16 1#1)))
  let w__710 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 3 w__710 13 0b000#3)))
  let w__711 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (_update_HSCTLR_Type_I w__711 0#1))
  let w__712 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 w__712 11 1#1)))
  let w__713 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 2 w__713 9 0b00#2)))
  let w__714 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (Mk_HSCTLR_Type (set_slice 1 w__714 6 0#1)))
  let w__715 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (_update_HSCTLR_Type_LSMAOE w__715 1#1))
  let w__716 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (_update_HSCTLR_Type_nTLSMD w__716 1#1))
  let w__717 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (_update_HSCTLR_Type_C w__717 0#1))
  let w__718 ← (( do (HSCTLR_read ()) ) : SailM (BitVec 32) )
  (HSCTLR_write (_update_HSCTLR_Type_M w__718 0#1))
  let w__719 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  (VTCR_write (Mk_VTCR_Type (set_slice 1 w__719 31 1#1)))
  let w__720 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  (VTCR_write (Mk_VTCR_Type (set_slice 2 w__720 29 0b00#2)))
  let w__721 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  (VTCR_write (Mk_VTCR_Type (set_slice 11 w__721 14 0b00000000000#11)))
  let w__722 ← (( do (VTCR_read ()) ) : SailM (BitVec 32) )
  (VTCR_write (Mk_VTCR_Type (set_slice 1 w__722 5 0#1)))
  let w__723 ← (( do readReg ICC_MGRPEN1 ) : SailM (BitVec 32) )
  writeReg ICC_MGRPEN1 (Sail.BitVec.updateSubrange w__723 31 2 0b000000000000000000000000000000#30)
  let w__724 ← (( do readReg ICC_MGRPEN1 ) : SailM (BitVec 32) )
  writeReg ICC_MGRPEN1 (Sail.BitVec.updateSubrange w__724 1 1 0#1)
  let w__725 ← (( do readReg ICC_MGRPEN1 ) : SailM (BitVec 32) )
  writeReg ICC_MGRPEN1 (Sail.BitVec.updateSubrange w__725 0 0 0#1)
  let w__726 ← (( do (DFSR_read ()) ) : SailM (BitVec 32) )
  (DFSR_write (Mk_DFSR_Type (set_slice 15 w__726 17 0b000000000000000#15)))
  let w__727 ← (( do (DFSR_read ()) ) : SailM (BitVec 32) )
  (DFSR_write (Mk_DFSR_Type (set_slice 1 w__727 8 0#1)))
  let w__728 ← (( do (DFSR_read ()) ) : SailM (BitVec 32) )
  (DFSR_write (Mk_DFSR_Type (set_slice 15 w__728 17 0b000000000000000#15)))
  let w__729 ← (( do (DFSR_read ()) ) : SailM (BitVec 32) )
  (DFSR_write (Mk_DFSR_Type (set_slice 1 w__729 10 0#1)))
  let w__730 ← (( do (DFSR_read ()) ) : SailM (BitVec 32) )
  (DFSR_write (Mk_DFSR_Type (set_slice 3 w__730 6 0b000#3)))
  let w__731 ← (( do (CCSIDR2_read ()) ) : SailM (BitVec 32) )
  (CCSIDR2_write (Mk_CCSIDR2_Type (set_slice 8 w__731 24 0b00000000#8)))
  let w__732 ← (( do (CNTHV_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTHV_CTL_write (Mk_CNTHV_CTL_Type (set_slice 29 w__732 3 0b00000000000000000000000000000#29)))
  let w__733 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (Mk_ICH_MISR_Type (set_slice 24 w__733 8 0b000000000000000000000000#24)))
  let w__734 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_VGrp1D w__734 0#1))
  (pure true)


end ArmFull.Functions
