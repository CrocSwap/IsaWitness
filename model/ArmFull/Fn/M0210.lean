import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0058
import ArmFull.Fn.M0087
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
def AArch64_AutoGen_ArchitectureReset__seg2 (cold : Bool) : SailM Bool := do
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__631 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__631 11 11 0#1))
  else
    (do
      let w__632 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__633 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__632 11 11 w__633))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__634 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__634 10 10 0#1))
  else
    (do
      let w__635 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__636 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__635 10 10 w__636))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__637 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__637 9 9 0#1))
  else
    (do
      let w__638 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__639 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__638 9 9 w__639))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__640 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__640 8 8 0#1))
  else
    (do
      let w__641 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__642 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__641 8 8 w__642))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__643 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__643 7 7 0#1))
  else
    (do
      let w__644 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__645 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__644 7 7 w__645))
  let w__646 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (BitVec.update w__646 6 (Bit 0#1))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__647 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__647 5 5 0#1))
  else
    (do
      let w__648 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__649 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__648 5 5 w__649))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__650 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__650 4 4 0#1))
  else
    (do
      let w__651 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__652 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__651 4 4 w__652))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__653 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__653 3 3 0#1))
  else
    (do
      let w__654 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__655 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__654 3 3 w__655))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__656 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__656 2 2 0#1))
  else
    (do
      let w__657 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__658 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__657 2 2 w__658))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__659 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__659 1 1 0#1))
  else
    (do
      let w__660 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__661 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__660 1 1 w__661))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__662 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__662 0 0 0#1))
  else
    (do
      let w__663 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__664 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__663 0 0 w__664))
  let w__665 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
  writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__665 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__666 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
  writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__666 13 12 0b00#2)
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__667 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__667 11 11 0#1))
  else
    (do
      let w__668 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__669 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__668 11 11 w__669))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__670 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__670 10 10 0#1))
  else
    (do
      let w__671 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__672 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__671 10 10 w__672))
  let w__673 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
  writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__673 9 6 0b0000#4)
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__674 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__674 5 5 0#1))
  else
    (do
      let w__675 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__676 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__675 5 5 w__676))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__677 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__677 4 4 0#1))
  else
    (do
      let w__678 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__679 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__678 4 4 w__679))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__680 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__680 3 3 0#1))
  else
    (do
      let w__681 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__682 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__681 3 3 w__682))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__683 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__683 2 2 0#1))
  else
    (do
      let w__684 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__685 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__684 2 2 w__685))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__686 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__686 1 1 0#1))
  else
    (do
      let w__687 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__688 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__687 1 1 w__688))
  if ((((! cold) && (! (HaveEL EL2))) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__689 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__689 0 0 0#1))
  else
    (do
      let w__690 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__691 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__690 0 0 w__691))
  let w__692 ← (( do readReg ID_ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR0_EL1 (Sail.BitVec.updateSubrange w__692 63 28
    0b000000000000000000000000000000000000#36)
  let w__693 ← (( do readReg ID_ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR0_EL1 (Sail.BitVec.updateSubrange w__693 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__694 ← (( do readReg DCZID_EL0 ) : SailM (BitVec 64) )
  writeReg DCZID_EL0 (Sail.BitVec.updateSubrange w__694 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__695 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTTBR_EL2 (Sail.BitVec.updateSubrange w__695 63 56 0b00000000#8)
  let w__696 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTTBR_EL2 (Sail.BitVec.updateSubrange w__696 4 3 0b00#2)
  let w__697 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTTBR_EL2 (Sail.BitVec.updateSubrange w__697 63 48 0b0000000000000000#16)
  let w__698 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__698 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__699 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__699 6 5 0b00#2)
  let w__700 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (BitVec.update w__700 4 (Bit 0#1))
  let w__701 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__701 3 3 0#1)
  let w__702 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (BitVec.update w__702 2 (Bit 0#1))
  let w__703 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__703 1 1 0#1)
  let w__704 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__704 0 0 0#1)
  let w__705 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__705 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__706 ← (( do readReg CNTHVS_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHVS_TVAL_EL2 (Sail.BitVec.updateSubrange w__706 63 32
    0b00000000000000000000000000000000#32)
  let w__707 ← (( do readReg CNTHP_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHP_TVAL_EL2 (Sail.BitVec.updateSubrange w__707 63 32
    0b00000000000000000000000000000000#32)
  let w__708 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
  writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange w__708 63 32
    0b00000000000000000000000000000000#32)
  let w__709 ← (( do readReg PMZR_EL0 ) : SailM (BitVec 64) )
  writeReg PMZR_EL0 (Sail.BitVec.updateSubrange w__709 63 33 0b0000000000000000000000000000000#31)
  let w__710 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange w__710 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__711 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange w__711 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__712 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange w__712 11 8 0b0000#4)
  let w__713 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__713 63 56 0b00000000#8)
  let w__714 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__714 11 2 0b0000000000#10)
  let w__715 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64) )
  writeReg OSDTRRX_EL1 (Sail.BitVec.updateSubrange w__715 63 32
    0b00000000000000000000000000000000#32)
  let w__716 ← (( do readReg PFAR_EL1 ) : SailM (BitVec 64) )
  writeReg PFAR_EL1 (Sail.BitVec.updateSubrange w__716 61 56 0b000000#6)
  let w__717 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__717 63 17
    0b00000000000000000000000000000000000000000000000#47)
  let w__718 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__718 15 13 0b000#3)
  let w__719 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (BitVec.update w__719 11 (Bit 0#1))
  let w__720 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__720 8 4 0b00000#5)
  let w__721 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__721 63 17
    0b00000000000000000000000000000000000000000000000#47)
  let w__722 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__722 15 13 0b000#3)
  let w__723 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__723 11 10 0b00#2)
  let w__724 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__724 8 6 0b000#3)
  let w__725 ← (( do readReg ICC_IGRPEN1_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL3 (Sail.BitVec.updateSubrange w__725 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__726 ← (( do readReg ICC_IGRPEN1_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL3 (Sail.BitVec.updateSubrange w__726 1 1 0#1)
  let w__727 ← (( do readReg ICC_IGRPEN1_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL3 (Sail.BitVec.updateSubrange w__727 0 0 0#1)
  let w__728 ← (( do readReg ID_MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR1_EL1 (Sail.BitVec.updateSubrange w__728 63 32
    0b00000000000000000000000000000000#32)
  let w__729 ← (( do readReg ID_MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR1_EL1 (Sail.BitVec.updateSubrange w__729 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__730 ← (( do readReg LORSA_EL1 ) : SailM (BitVec 64) )
  writeReg LORSA_EL1 (Sail.BitVec.updateSubrange w__730 63 56 0b00000000#8)
  let w__731 ← (( do readReg LORSA_EL1 ) : SailM (BitVec 64) )
  writeReg LORSA_EL1 (Sail.BitVec.updateSubrange w__731 15 1 0b000000000000000#15)
  let w__732 ← (( do readReg LORSA_EL1 ) : SailM (BitVec 64) )
  writeReg LORSA_EL1 (Sail.BitVec.updateSubrange w__732 0 0 0#1)
  let w__733 ← (( do readReg PMSWINC_EL0 ) : SailM (BitVec 64) )
  writeReg PMSWINC_EL0 (Sail.BitVec.updateSubrange w__733 63 31
    0b000000000000000000000000000000000#33)
  let w__734 ← (( do readReg ESR_EL3 ) : SailM (BitVec 64) )
  writeReg ESR_EL3 (Sail.BitVec.updateSubrange w__734 63 56 0b00000000#8)
  let w__735 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__735 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__736 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__736 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__737 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__737 4 2 0b000#3)
  let w__738 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__738 1 1 0#1)
  let w__739 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__739 0 0 0#1)
  let w__740 ← (( do readReg ID_MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR0_EL1 (Sail.BitVec.updateSubrange w__740 63 32
    0b00000000000000000000000000000000#32)
  let w__741 ← (( do readReg ID_MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR0_EL1 (Sail.BitVec.updateSubrange w__741 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__742 ← (( do readReg OSDTRTX_EL1 ) : SailM (BitVec 64) )
  writeReg OSDTRTX_EL1 (Sail.BitVec.updateSubrange w__742 63 32
    0b00000000000000000000000000000000#32)
  let w__743 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__743 63 32
    0b00000000000000000000000000000000#32)
  let w__744 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__744 17 10 0b00000000#8)
  let w__745 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__745 8 5 0b0000#4)
  let w__746 ← (( do readReg VPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VPIDR_EL2 (Sail.BitVec.updateSubrange w__746 63 32 0b00000000000000000000000000000000#32)
  let w__747 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (Sail.BitVec.updateSubrange w__747 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__748 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (BitVec.update w__748 16 (Bit 0#1))
  let w__749 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (BitVec.update w__749 7 (Bit 0#1))
  let w__750 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (Sail.BitVec.updateSubrange w__750 6 6 0#1)
  let w__751 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__751 61 61 0#1)
  let w__752 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (BitVec.update w__752 34 (Bit 0#1))
  let w__753 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (BitVec.update w__753 17 (Bit 0#1))
  let w__754 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__754 12 12 0#1)
  let w__755 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (BitVec.update w__755 9 (Bit 0#1))
  let w__756 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__756 2 2 0#1)
  let w__757 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__757 0 0 0#1)
  let w__758 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__758 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  if (cold : Bool)
  then
    (do
      let w__759 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__759 1 1 1#1))
  else (pure (()))
  let w__760 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__760 63 47 0b00000000000000000#17)
  let w__761 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__761 46 45 0b00#2)
  let w__762 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__762 43 43 0#1)
  let w__763 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__763 39 (Bit 0#1))
  if (cold : Bool)
  then
    (do
      let w__764 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
      writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__764 38 38 0#1))
  else (pure (()))
  let w__765 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__765 37 37 0#1)
  let w__766 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__766 35 35 0#1)
  let w__767 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__767 34 34 0#1)
  if (cold : Bool)
  then
    (do
      let w__768 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
      writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__768 31 30 0b00#2))
  else (pure (()))
  let w__769 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__769 29 (Bit 0#1))
  if (cold : Bool)
  then
    (do
      let w__770 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
      writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__770 28 28 1#1))
  else (pure (()))
  let w__771 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__771 26 24 0b000#3)
  let w__772 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__772 23 23 0#1)
  let w__773 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__773 22 (Bit 0#1))
  let w__774 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__774 21 21 0#1)
  let w__775 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__775 20 20 0#1)
  let w__776 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__776 18 18 0#1)
  let w__777 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__777 17 17 0#1)
  let w__778 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__778 8 (Bit 0#1))
  let w__779 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__779 5 (Bit 0#1))
  let w__780 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__780 4 4 0#1)
  let w__781 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__781 3 (Bit 0#1))
  let w__782 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__782 2 2 0#1)
  let w__783 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__783 1 (Bit 0#1))
  let w__784 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__784 0 0 0#1)
  let w__785 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__785 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__786 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__786 4 4 0#1)
  let w__787 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__787 3 3 0#1)
  let w__788 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (BitVec.update w__788 2 (Bit 0#1))
  let w__789 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__789 1 1 0#1)
  let w__790 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (BitVec.update w__790 0 (Bit 0#1))
  let w__791 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENSET_EL0 (Sail.BitVec.updateSubrange w__791 63 33
    0b0000000000000000000000000000000#31)
  let w__792 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENSET_EL0 (BitVec.update w__792 32 (Bit 0#1))
  let w__793 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__793 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__794 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__794 2 2 0#1)
  let w__795 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__795 1 1 0#1)
  let w__796 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__796 0 0 0#1)
  let w__797 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange w__797 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__798 ← (( do readReg DACR32_EL2 ) : SailM (BitVec 64) )
  writeReg DACR32_EL2 (Sail.BitVec.updateSubrange w__798 63 32 0b00000000000000000000000000000000#32)
  let w__799 ← (( do readReg LORC_EL1 ) : SailM (BitVec 64) )
  writeReg LORC_EL1 (Sail.BitVec.updateSubrange w__799 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__800 ← (( do readReg LORC_EL1 ) : SailM (BitVec 64) )
  writeReg LORC_EL1 (BitVec.update w__800 1 (Bit 0#1))
  let w__801 ← (( do readReg LORC_EL1 ) : SailM (BitVec 64) )
  writeReg LORC_EL1 (Sail.BitVec.updateSubrange w__801 0 0 0#1)
  let w__802 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__802 63 12
    0b0000000000000000000000000000000000000000000000000000#52)
  let w__803 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange w__803 63 34 0b000000000000000000000000000000#30)
  let w__804 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__804 31 (Bit 1#1))
  let w__805 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__805 23 (Bit 1#1))
  let w__806 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__806 19 (Bit 0#1))
  let w__807 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange w__807 7 6 0b00#2)
  let w__808 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange w__808 63 62 0b00#2)
  let w__809 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__809 35 (Bit 0#1))
  let w__810 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__810 6 (Bit 0#1))
  let w__811 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR2_EL1 (Sail.BitVec.updateSubrange w__811 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__812 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange w__812 63 56 0b00000000#8)
  let w__813 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange w__813 43 41 0b000#3)
  let w__814 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange w__814 31 28 0b0000#4)
  let w__815 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__815 63 38 0b00000000000000000000000000#26)
  let w__816 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (BitVec.update w__816 31 (Bit 1#1))
  let w__817 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (BitVec.update w__817 30 (Bit 0#1))
  let w__818 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__818 13 4 0b0000000000#10)
  let w__819 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
  writeReg SPSR_und (Sail.BitVec.updateSubrange w__819 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__820 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
  writeReg SPSR_und (Sail.BitVec.updateSubrange w__820 63 32 0b00000000000000000000000000000000#32)
  let w__821 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__821 63 56 0b00000000#8)
  let w__822 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__822 47 44 0b0000#4)
  let w__823 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__823 63 32 0b00000000000000000000000000000000#32)
  let w__824 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__824 29 21 0b000000000#9)
  let w__825 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__825 19 13 0b0000000#7)
  let w__826 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (BitVec.update w__826 11 (Bit 0#1))
  let w__827 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (BitVec.update w__827 9 (Bit 0#1))
  let w__828 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__828 7 0 0b00000000#8)
  let w__829 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__829 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__830 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__830 2 2 0#1))
  else
    (do
      let w__831 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__832 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__831 2 2 w__832))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__833 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__833 1 1 0#1))
  else
    (do
      let w__834 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__835 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__834 1 1 w__835))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__836 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__836 0 0 0#1))
  else
    (do
      let w__837 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__838 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__837 0 0 w__838))
  let w__839 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__839 63 32
    0b00000000000000000000000000000000#32)
  let w__840 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__840 23 20 0b0000#4)
  let w__841 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__841 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__842 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
  writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__842 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__843 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
  writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__843 1 1 0#1)
  let w__844 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__844 63 32
    0b00000000000000000000000000000000#32)
  let w__845 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__845 31 27 0b00000#5)
  let w__846 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__846 26 16 0b00000000000#11)
  let w__847 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__847 15 15 0#1)
  let w__848 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__848 14 14 0#1)
  let w__849 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__849 13 13 0#1)
  let w__850 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__850 12 12 0#1)
  let w__851 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__851 11 11 0#1)
  let w__852 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__852 10 10 0#1)
  let w__853 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (BitVec.update w__853 9 (Bit 0#1))
  let w__854 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__854 8 8 0#1)
  let w__855 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__855 7 7 0#1)
  let w__856 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__856 6 6 0#1)
  let w__857 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__857 5 5 0#1)
  let w__858 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__858 4 4 0#1)
  let w__859 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__859 3 3 0#1)
  let w__860 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__860 2 2 0#1)
  let w__861 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__861 1 1 0#1)
  let w__862 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__862 0 0 0#1)
  let w__863 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__863 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__864 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__864 0 0 0#1)
  let w__865 ← (( do readReg CNTHPS_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHPS_TVAL_EL2 (Sail.BitVec.updateSubrange w__865 63 32
    0b00000000000000000000000000000000#32)
  let w__866 ← (( do (ICC_BPR1_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_BPR1_EL1_write
    (Mk_ICC_BPR1_EL1_Type
      (set_slice 61 w__866 3 0b0000000000000000000000000000000000000000000000000000000000000#61)))
  let w__867 ← (( do readReg MECID_A1_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_A1_EL2 (Sail.BitVec.updateSubrange w__867 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__868 ← (( do readReg ICC_EOIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_EOIR1_EL1 (Sail.BitVec.updateSubrange w__868 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__869 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__869 55 48 0b00000000#8)
  let w__870 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__870 63 33 0b0000000000000000000000000000000#31)
  if (((! cold) && (HaveAArch32 ())) : Bool)
  then
    (do
      let w__871 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__871 32 32 0#1))
  else
    (do
      let w__872 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      let w__873 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__872 32 32 w__873))
  let w__874 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (BitVec.update w__874 10 (Bit 0#1))
  let w__875 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (BitVec.update w__875 8 (Bit 0#1))
  let w__876 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__876 0 0 0#1)
  let w__877 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__877 63 20
    0b00000000000000000000000000000000000000000000#44)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__878 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__878 19 19 0#1))
  else
    (do
      let w__879 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__880 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__879 19 19 w__880))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__881 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__881 18 18 0#1))
  else
    (do
      let w__882 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__883 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__882 18 18 w__883))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__884 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__884 17 17 0#1))
  else
    (do
      let w__885 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__886 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__885 17 17 w__886))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__887 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__887 16 16 0#1))
  else
    (do
      let w__888 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__889 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__888 16 16 w__889))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__890 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__890 15 15 0#1))
  else
    (do
      let w__891 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__892 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__891 15 15 w__892))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__893 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__893 14 14 0#1))
  else
    (do
      let w__894 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__895 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__894 14 14 w__895))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__896 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__896 13 13 0#1))
  else
    (do
      let w__897 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__898 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__897 13 13 w__898))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__899 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__899 12 12 0#1))
  else
    (do
      let w__900 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__901 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__900 12 12 w__901))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__902 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__902 11 11 0#1))
  else
    (do
      let w__903 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__904 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__903 11 11 w__904))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__905 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__905 10 10 0#1))
  else
    (do
      let w__906 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__907 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__906 10 10 w__907))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__908 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__908 9 9 0#1))
  else
    (do
      let w__909 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__910 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__909 9 9 w__910))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__911 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__911 8 8 0#1))
  else
    (do
      let w__912 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__913 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__912 8 8 w__913))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__914 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__914 7 7 0#1))
  else
    (do
      let w__915 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__916 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__915 7 7 w__916))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__917 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__917 6 6 0#1))
  else
    (do
      let w__918 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__919 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__918 6 6 w__919))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__920 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__920 5 5 0#1))
  else
    (do
      let w__921 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__922 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__921 5 5 w__922))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__923 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__923 4 4 0#1))
  else
    (do
      let w__924 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__925 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__924 4 4 w__925))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__926 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__926 3 3 0#1))
  else
    (do
      let w__927 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__928 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__927 3 3 w__928))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__929 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__929 2 2 0#1))
  else
    (do
      let w__930 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__931 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__930 2 2 w__931))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__932 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__932 1 1 0#1))
  else
    (do
      let w__933 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__934 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__933 1 1 w__934))
  (pure true)


end ArmFull.Functions
