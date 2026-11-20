module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0058
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0144
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

/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg2 (cold : Bool) : SailM Bool := do
  let w__720 ← (( do readReg MVFR1_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR1_EL1 (Sail.BitVec.updateSubrange w__720 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__721 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__721 63 22
    0b000000000000000000000000000000000000000000#42)
  let w__723 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__722 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__722) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__723 : Bool)
  then
    (do
      let w__724 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__724 21 21 0#1))
  else
    (do
      let w__725 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__726 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__725 21 21 w__726))
  let w__727 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (BitVec.update w__727 20 (Bit 0#1))
  let w__729 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__728 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__728) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__729 : Bool)
  then
    (do
      let w__730 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__730 19 19 0#1))
  else
    (do
      let w__731 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__732 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__731 19 19 w__732))
  let w__733 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__733 18 17 0b00#2)
  let w__735 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__734 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__734) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__735 : Bool)
  then
    (do
      let w__736 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__736 16 16 0#1))
  else
    (do
      let w__737 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__738 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__737 16 16 w__738))
  let w__740 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__739 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__739) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__740 : Bool)
  then
    (do
      let w__741 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__741 15 15 0#1))
  else
    (do
      let w__742 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__743 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__742 15 15 w__743))
  let w__745 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__744 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__744) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__745 : Bool)
  then
    (do
      let w__746 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__746 14 14 0#1))
  else
    (do
      let w__747 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__748 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__747 14 14 w__748))
  let w__750 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__749 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__749) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__750 : Bool)
  then
    (do
      let w__751 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__751 13 13 0#1))
  else
    (do
      let w__752 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__753 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__752 13 13 w__753))
  let w__755 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__754 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__754) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__755 : Bool)
  then
    (do
      let w__756 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__756 12 12 0#1))
  else
    (do
      let w__757 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__758 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__757 12 12 w__758))
  let w__760 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__759 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__759) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__760 : Bool)
  then
    (do
      let w__761 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__761 11 11 0#1))
  else
    (do
      let w__762 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__763 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__762 11 11 w__763))
  let w__765 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__764 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__764) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__765 : Bool)
  then
    (do
      let w__766 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__766 10 10 0#1))
  else
    (do
      let w__767 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__768 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__767 10 10 w__768))
  let w__770 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__769 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__769) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__770 : Bool)
  then
    (do
      let w__771 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__771 9 9 0#1))
  else
    (do
      let w__772 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__773 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__772 9 9 w__773))
  let w__775 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__774 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__774) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__775 : Bool)
  then
    (do
      let w__776 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__776 8 8 0#1))
  else
    (do
      let w__777 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__778 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__777 8 8 w__778))
  let w__780 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__779 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__779) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__780 : Bool)
  then
    (do
      let w__781 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__781 7 7 0#1))
  else
    (do
      let w__782 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__783 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__782 7 7 w__783))
  let w__784 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR2_EL2 (BitVec.update w__784 6 (Bit 0#1))
  let w__786 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__785 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__785) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__786 : Bool)
  then
    (do
      let w__787 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__787 5 5 0#1))
  else
    (do
      let w__788 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__789 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__788 5 5 w__789))
  let w__791 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__790 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__790) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__791 : Bool)
  then
    (do
      let w__792 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__792 4 4 0#1))
  else
    (do
      let w__793 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__794 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__793 4 4 w__794))
  let w__796 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__795 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__795) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__796 : Bool)
  then
    (do
      let w__797 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__797 3 3 0#1))
  else
    (do
      let w__798 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__799 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__798 3 3 w__799))
  let w__801 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__800 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__800) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__801 : Bool)
  then
    (do
      let w__802 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__802 2 2 0#1))
  else
    (do
      let w__803 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__804 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__803 2 2 w__804))
  let w__806 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__805 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__805) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__806 : Bool)
  then
    (do
      let w__807 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__807 1 1 0#1))
  else
    (do
      let w__808 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__809 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__808 1 1 w__809))
  let w__811 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__810 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__810) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__811 : Bool)
  then
    (do
      let w__812 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__812 0 0 0#1))
  else
    (do
      let w__813 ← (( do readReg HDFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__814 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR2_EL2 (Sail.BitVec.updateSubrange w__813 0 0 w__814))
  let w__815 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
  writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__815 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__816 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
  writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__816 13 12 0b00#2)
  let w__820 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__817 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__817) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__819 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__819) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__820 : Bool)
  then
    (do
      let w__821 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__821 11 11 0#1))
  else
    (do
      let w__822 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__823 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__822 11 11 w__823))
  let w__827 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__824 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__824) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__826 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__826) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__827 : Bool)
  then
    (do
      let w__828 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__828 10 10 0#1))
  else
    (do
      let w__829 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__830 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__829 10 10 w__830))
  let w__831 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
  writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__831 9 6 0b0000#4)
  let w__835 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__832 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__832) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__834 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__834) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__835 : Bool)
  then
    (do
      let w__836 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__836 5 5 0#1))
  else
    (do
      let w__837 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__838 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__837 5 5 w__838))
  let w__842 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__839 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__839) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__841 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__841) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__842 : Bool)
  then
    (do
      let w__843 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__843 4 4 0#1))
  else
    (do
      let w__844 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__845 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__844 4 4 w__845))
  let w__849 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__846 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__846) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__848 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__848) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__849 : Bool)
  then
    (do
      let w__850 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__850 3 3 0#1))
  else
    (do
      let w__851 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__852 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__851 3 3 w__852))
  let w__856 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__853 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__853) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__855 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__855) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__856 : Bool)
  then
    (do
      let w__857 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__857 2 2 0#1))
  else
    (do
      let w__858 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__859 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__858 2 2 w__859))
  let w__863 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__860 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__860) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__862 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__862) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__863 : Bool)
  then
    (do
      let w__864 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__864 1 1 0#1))
  else
    (do
      let w__865 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__866 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__865 1 1 w__866))
  let w__870 ← (( do
    if ((← do
         if (((! cold) : Bool) : Bool)
         then
           (do
             let w__867 ← (( do (HaveEL EL2) ) : SailM Bool )
             (pure (((! w__867) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__869 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__869) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__870 : Bool)
  then
    (do
      let w__871 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__871 0 0 0#1))
  else
    (do
      let w__872 ← (( do readReg TCR2_EL1 ) : SailM (BitVec 64) )
      let w__873 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg TCR2_EL1 (Sail.BitVec.updateSubrange w__872 0 0 w__873))
  let w__874 ← (( do readReg ID_ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR0_EL1 (Sail.BitVec.updateSubrange w__874 63 28
    0b000000000000000000000000000000000000#36)
  let w__875 ← (( do readReg ID_ISAR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR0_EL1 (Sail.BitVec.updateSubrange w__875 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__876 ← (( do readReg DCZID_EL0 ) : SailM (BitVec 64) )
  writeReg DCZID_EL0 (Sail.BitVec.updateSubrange w__876 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__877 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTTBR_EL2 (Sail.BitVec.updateSubrange w__877 63 56 0b00000000#8)
  let w__878 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTTBR_EL2 (Sail.BitVec.updateSubrange w__878 4 3 0b00#2)
  let w__879 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
  writeReg VSTTBR_EL2 (Sail.BitVec.updateSubrange w__879 63 48 0b0000000000000000#16)
  let w__880 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__880 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__881 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__881 6 5 0b00#2)
  let w__882 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (BitVec.update w__882 4 (Bit 0#1))
  let w__883 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__883 3 3 0#1)
  let w__884 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (BitVec.update w__884 2 (Bit 0#1))
  let w__885 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__885 1 1 0#1)
  let w__886 ← (( do readReg TRFCR_EL2 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL2 (Sail.BitVec.updateSubrange w__886 0 0 0#1)
  let w__887 ← (( do readReg CNTHP_CTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHP_CTL_EL2 (Sail.BitVec.updateSubrange w__887 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__888 ← (( do readReg CNTHVS_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHVS_TVAL_EL2 (Sail.BitVec.updateSubrange w__888 63 32
    0b00000000000000000000000000000000#32)
  let w__889 ← (( do readReg CNTHP_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHP_TVAL_EL2 (Sail.BitVec.updateSubrange w__889 63 32
    0b00000000000000000000000000000000#32)
  let w__890 ← (( do readReg DBGDTRTX_EL0 ) : SailM (BitVec 64) )
  writeReg DBGDTRTX_EL0 (Sail.BitVec.updateSubrange w__890 63 32
    0b00000000000000000000000000000000#32)
  let w__891 ← (( do readReg PMZR_EL0 ) : SailM (BitVec 64) )
  writeReg PMZR_EL0 (Sail.BitVec.updateSubrange w__891 63 33 0b0000000000000000000000000000000#31)
  let w__892 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange w__892 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__893 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange w__893 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__894 ← (( do readReg CNTHCTL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHCTL_EL2 (Sail.BitVec.updateSubrange w__894 11 8 0b0000#4)
  let w__895 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__895 63 56 0b00000000#8)
  let w__896 ← (( do readReg MDRAR_EL1 ) : SailM (BitVec 64) )
  writeReg MDRAR_EL1 (Sail.BitVec.updateSubrange w__896 11 2 0b0000000000#10)
  let w__897 ← (( do readReg OSDTRRX_EL1 ) : SailM (BitVec 64) )
  writeReg OSDTRRX_EL1 (Sail.BitVec.updateSubrange w__897 63 32
    0b00000000000000000000000000000000#32)
  let w__898 ← (( do readReg PFAR_EL1 ) : SailM (BitVec 64) )
  writeReg PFAR_EL1 (Sail.BitVec.updateSubrange w__898 61 56 0b000000#6)
  let w__899 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__899 63 17
    0b00000000000000000000000000000000000000000000000#47)
  let w__900 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__900 15 13 0b000#3)
  let w__901 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (BitVec.update w__901 11 (Bit 0#1))
  let w__902 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__902 8 4 0b00000#5)
  let w__903 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__903 63 17
    0b00000000000000000000000000000000000000000000000#47)
  let w__904 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__904 15 13 0b000#3)
  let w__905 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__905 11 10 0b00#2)
  let w__906 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__906 8 6 0b000#3)
  let w__907 ← (( do readReg ICC_IGRPEN1_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL3 (Sail.BitVec.updateSubrange w__907 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__908 ← (( do readReg ICC_IGRPEN1_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL3 (Sail.BitVec.updateSubrange w__908 1 1 0#1)
  let w__909 ← (( do readReg ICC_IGRPEN1_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN1_EL3 (Sail.BitVec.updateSubrange w__909 0 0 0#1)
  let w__910 ← (( do readReg ID_MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR1_EL1 (Sail.BitVec.updateSubrange w__910 63 32
    0b00000000000000000000000000000000#32)
  let w__911 ← (( do readReg ID_MMFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR1_EL1 (Sail.BitVec.updateSubrange w__911 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__912 ← (( do readReg LORSA_EL1 ) : SailM (BitVec 64) )
  writeReg LORSA_EL1 (Sail.BitVec.updateSubrange w__912 63 56 0b00000000#8)
  let w__913 ← (( do readReg LORSA_EL1 ) : SailM (BitVec 64) )
  writeReg LORSA_EL1 (Sail.BitVec.updateSubrange w__913 15 1 0b000000000000000#15)
  let w__914 ← (( do readReg LORSA_EL1 ) : SailM (BitVec 64) )
  writeReg LORSA_EL1 (Sail.BitVec.updateSubrange w__914 0 0 0#1)
  let w__915 ← (( do readReg PMSWINC_EL0 ) : SailM (BitVec 64) )
  writeReg PMSWINC_EL0 (Sail.BitVec.updateSubrange w__915 63 31
    0b000000000000000000000000000000000#33)
  let w__916 ← (( do readReg ESR_EL3 ) : SailM (BitVec 64) )
  writeReg ESR_EL3 (Sail.BitVec.updateSubrange w__916 63 56 0b00000000#8)
  let w__917 ← (( do readReg CNTV_CTL_EL0 ) : SailM (BitVec 64) )
  writeReg CNTV_CTL_EL0 (Sail.BitVec.updateSubrange w__917 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__918 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__918 63 7
    0b000000000000000000000000000000000000000000000000000000000#57)
  let w__919 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__919 4 2 0b000#3)
  let w__920 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__920 1 1 0#1)
  let w__921 ← (( do readReg TRFCR_EL1 ) : SailM (BitVec 64) )
  writeReg TRFCR_EL1 (Sail.BitVec.updateSubrange w__921 0 0 0#1)
  let w__922 ← (( do readReg ID_MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR0_EL1 (Sail.BitVec.updateSubrange w__922 63 32
    0b00000000000000000000000000000000#32)
  let w__923 ← (( do readReg ID_MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR0_EL1 (Sail.BitVec.updateSubrange w__923 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__924 ← (( do readReg OSDTRTX_EL1 ) : SailM (BitVec 64) )
  writeReg OSDTRTX_EL1 (Sail.BitVec.updateSubrange w__924 63 32
    0b00000000000000000000000000000000#32)
  let w__925 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__925 63 32
    0b00000000000000000000000000000000#32)
  let w__926 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__926 17 10 0b00000000#8)
  let w__927 ← (( do readReg ICH_VMCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VMCR_EL2 (Sail.BitVec.updateSubrange w__927 8 5 0b0000#4)
  let w__928 ← (( do readReg VPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VPIDR_EL2 (Sail.BitVec.updateSubrange w__928 63 32 0b00000000000000000000000000000000#32)
  let w__929 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (Sail.BitVec.updateSubrange w__929 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__930 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (BitVec.update w__930 16 (Bit 0#1))
  let w__931 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (BitVec.update w__931 7 (Bit 0#1))
  let w__932 ← (( do readReg ICC_CTLR_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_CTLR_EL3 (Sail.BitVec.updateSubrange w__932 6 6 0#1)
  let w__933 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__933 61 61 0#1)
  let w__934 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (BitVec.update w__934 34 (Bit 0#1))
  let w__935 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (BitVec.update w__935 17 (Bit 0#1))
  let w__936 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__936 12 12 0#1)
  let w__937 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (BitVec.update w__937 9 (Bit 0#1))
  let w__938 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__938 2 2 0#1)
  let w__939 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  writeReg SCTLR_EL2 (Sail.BitVec.updateSubrange w__939 0 0 0#1)
  let w__940 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
  writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__940 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  if (cold : Bool)
  then
    (do
      let w__941 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
      writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__941 1 1 1#1))
  else (pure (()))
  let w__942 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__942 63 47 0b00000000000000000#17)
  let w__943 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__943 46 45 0b00#2)
  let w__944 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__944 43 43 0#1)
  let w__945 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__945 39 (Bit 0#1))
  if (cold : Bool)
  then
    (do
      let w__946 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
      writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__946 38 38 0#1))
  else (pure (()))
  let w__947 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__947 37 37 0#1)
  let w__948 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__948 35 35 0#1)
  let w__949 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__949 34 34 0#1)
  if (cold : Bool)
  then
    (do
      let w__950 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
      writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__950 31 30 0b00#2))
  else (pure (()))
  let w__951 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__951 29 (Bit 0#1))
  if (cold : Bool)
  then
    (do
      let w__952 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
      writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__952 28 28 1#1))
  else (pure (()))
  let w__953 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__953 26 24 0b000#3)
  let w__954 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__954 23 23 0#1)
  let w__955 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__955 22 (Bit 0#1))
  let w__956 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__956 21 21 0#1)
  let w__957 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__957 20 20 0#1)
  let w__958 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__958 18 18 0#1)
  let w__959 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__959 17 17 0#1)
  let w__960 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__960 8 (Bit 0#1))
  let w__961 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__961 5 (Bit 0#1))
  let w__962 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__962 4 4 0#1)
  let w__963 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__963 3 (Bit 0#1))
  let w__964 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__964 2 2 0#1)
  let w__965 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (BitVec.update w__965 1 (Bit 0#1))
  let w__966 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  writeReg MDCR_EL3 (Sail.BitVec.updateSubrange w__966 0 0 0#1)
  let w__967 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__967 63 5
    0b00000000000000000000000000000000000000000000000000000000000#59)
  let w__968 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__968 4 4 0#1)
  let w__969 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__969 3 3 0#1)
  let w__970 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (BitVec.update w__970 2 (Bit 0#1))
  let w__971 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (Sail.BitVec.updateSubrange w__971 1 1 0#1)
  let w__972 ← (( do readReg SCTLR2_EL3 ) : SailM (BitVec 64) )
  writeReg SCTLR2_EL3 (BitVec.update w__972 0 (Bit 0#1))
  let w__973 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENSET_EL0 (Sail.BitVec.updateSubrange w__973 63 33
    0b0000000000000000000000000000000#31)
  let w__974 ← (( do readReg PMCNTENSET_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENSET_EL0 (BitVec.update w__974 32 (Bit 0#1))
  let w__975 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__975 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__976 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__976 2 2 0#1)
  let w__977 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__977 1 1 0#1)
  let w__978 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL2 (Sail.BitVec.updateSubrange w__978 0 0 0#1)
  let w__979 ← (( do readReg CNTPS_CTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTPS_CTL_EL1 (Sail.BitVec.updateSubrange w__979 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__980 ← (( do readReg DACR32_EL2 ) : SailM (BitVec 64) )
  writeReg DACR32_EL2 (Sail.BitVec.updateSubrange w__980 63 32 0b00000000000000000000000000000000#32)
  let w__981 ← (( do readReg LORC_EL1 ) : SailM (BitVec 64) )
  writeReg LORC_EL1 (Sail.BitVec.updateSubrange w__981 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__982 ← (( do readReg LORC_EL1 ) : SailM (BitVec 64) )
  writeReg LORC_EL1 (BitVec.update w__982 1 (Bit 0#1))
  let w__983 ← (( do readReg LORC_EL1 ) : SailM (BitVec 64) )
  writeReg LORC_EL1 (Sail.BitVec.updateSubrange w__983 0 0 0#1)
  let w__984 ← (( do readReg ID_AA64PFR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64PFR2_EL1 (Sail.BitVec.updateSubrange w__984 63 12
    0b0000000000000000000000000000000000000000000000000000#52)
  let w__985 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange w__985 63 34 0b000000000000000000000000000000#30)
  let w__986 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__986 31 (Bit 1#1))
  let w__987 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__987 23 (Bit 1#1))
  let w__988 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__988 19 (Bit 0#1))
  let w__989 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange w__989 7 6 0b00#2)
  let w__990 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (Sail.BitVec.updateSubrange w__990 63 62 0b00#2)
  let w__991 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__991 35 (Bit 0#1))
  let w__992 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  writeReg TCR_EL2 (BitVec.update w__992 6 (Bit 0#1))
  let w__993 ← (( do readReg CCSIDR2_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR2_EL1 (Sail.BitVec.updateSubrange w__993 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__994 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange w__994 63 56 0b00000000#8)
  let w__995 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange w__995 43 41 0b000#3)
  let w__996 ← (( do readReg ICC_ASGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_ASGI1R_EL1 (Sail.BitVec.updateSubrange w__996 31 28 0b0000#4)
  let w__997 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__997 63 38 0b00000000000000000000000000#26)
  let w__998 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (BitVec.update w__998 31 (Bit 1#1))
  let w__999 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (BitVec.update w__999 30 (Bit 0#1))
  let w__1000 ← (( do readReg CTR_EL0 ) : SailM (BitVec 64) )
  writeReg CTR_EL0 (Sail.BitVec.updateSubrange w__1000 13 4 0b0000000000#10)
  let w__1001 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
  writeReg SPSR_und (Sail.BitVec.updateSubrange w__1001 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1002 ← (( do readReg SPSR_und ) : SailM (BitVec 64) )
  writeReg SPSR_und (Sail.BitVec.updateSubrange w__1002 63 32 0b00000000000000000000000000000000#32)
  let w__1003 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__1003 63 56 0b00000000#8)
  let w__1004 ← (( do readReg ID_AA64ISAR2_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64ISAR2_EL1 (Sail.BitVec.updateSubrange w__1004 47 44 0b0000#4)
  let w__1005 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__1005 63 32 0b00000000000000000000000000000000#32)
  let w__1006 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__1006 29 21 0b000000000#9)
  let w__1007 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__1007 19 13 0b0000000#7)
  let w__1008 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (BitVec.update w__1008 11 (Bit 0#1))
  let w__1009 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (BitVec.update w__1009 9 (Bit 0#1))
  let w__1010 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
  writeReg CPTR_EL3 (Sail.BitVec.updateSubrange w__1010 7 0 0b00000000#8)
  let w__1011 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1011 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__1013 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1012 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1012) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1013 : Bool)
  then
    (do
      let w__1014 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1014 2 2 0#1))
  else
    (do
      let w__1015 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1016 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1015 2 2 w__1016))
  let w__1018 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1017 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1017) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1018 : Bool)
  then
    (do
      let w__1019 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1019 1 1 0#1))
  else
    (do
      let w__1020 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1021 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1020 1 1 w__1021))
  let w__1023 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1022 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1022) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1023 : Bool)
  then
    (do
      let w__1024 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1024 0 0 0#1))
  else
    (do
      let w__1025 ← (( do readReg HFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1026 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1025 0 0 w__1026))
  let w__1027 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__1027 63 32
    0b00000000000000000000000000000000#32)
  let w__1028 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__1028 23 20 0b0000#4)
  let w__1029 ← (( do readReg ID_ISAR5_EL1 ) : SailM (BitVec 64) )
  writeReg ID_ISAR5_EL1 (Sail.BitVec.updateSubrange w__1029 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1030 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
  writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__1030 63 2
    0b00000000000000000000000000000000000000000000000000000000000000#62)
  let w__1031 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
  writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__1031 1 1 0#1)
  let w__1032 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1032 63 32
    0b00000000000000000000000000000000#32)
  let w__1033 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1033 31 27 0b00000#5)
  let w__1034 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1034 26 16 0b00000000000#11)
  let w__1035 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1035 15 15 0#1)
  let w__1036 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1036 14 14 0#1)
  let w__1037 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1037 13 13 0#1)
  let w__1038 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1038 12 12 0#1)
  let w__1039 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1039 11 11 0#1)
  let w__1040 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1040 10 10 0#1)
  let w__1041 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (BitVec.update w__1041 9 (Bit 0#1))
  let w__1042 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1042 8 8 0#1)
  let w__1043 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1043 7 7 0#1)
  let w__1044 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1044 6 6 0#1)
  let w__1045 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1045 5 5 0#1)
  let w__1046 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1046 4 4 0#1)
  let w__1047 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1047 3 3 0#1)
  let w__1048 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1048 2 2 0#1)
  let w__1049 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1049 1 1 0#1)
  let w__1050 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_HCR_EL2 (Sail.BitVec.updateSubrange w__1050 0 0 0#1)
  let w__1051 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__1051 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1052 ← (( do readReg ICC_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__1052 0 0 0#1)
  let w__1053 ← (( do readReg CNTHPS_TVAL_EL2 ) : SailM (BitVec 64) )
  writeReg CNTHPS_TVAL_EL2 (Sail.BitVec.updateSubrange w__1053 63 32
    0b00000000000000000000000000000000#32)
  let w__1054 ← (( do (ICC_BPR1_EL1_read ()) ) : SailM (BitVec 64) )
  (ICC_BPR1_EL1_write
    (Mk_ICC_BPR1_EL1_Type
      (set_slice 61 w__1054 3 0b0000000000000000000000000000000000000000000000000000000000000#61)))
  let w__1055 ← (( do readReg MECID_A1_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_A1_EL2 (Sail.BitVec.updateSubrange w__1055 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1056 ← (( do readReg ICC_EOIR1_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_EOIR1_EL1 (Sail.BitVec.updateSubrange w__1056 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1057 ← (( do readReg ID_AA64MMFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR0_EL1 (Sail.BitVec.updateSubrange w__1057 55 48 0b00000000#8)
  let w__1058 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__1058 63 33 0b0000000000000000000000000000000#31)
  let w__1060 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (HaveAArch32 ()))
    else (pure false) ) : SailM Bool )
  if (w__1060 : Bool)
  then
    (do
      let w__1061 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__1061 32 32 0#1))
  else
    (do
      let w__1062 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
      let w__1063 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__1062 32 32 w__1063))
  let w__1064 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (BitVec.update w__1064 10 (Bit 0#1))
  let w__1065 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (BitVec.update w__1065 8 (Bit 0#1))
  let w__1066 ← (( do readReg PMCR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCR_EL0 (Sail.BitVec.updateSubrange w__1066 0 0 0#1)
  let w__1067 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1067 63 20
    0b00000000000000000000000000000000000000000000#44)
  let w__1069 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1068 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1068) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1069 : Bool)
  then
    (do
      let w__1070 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1070 19 19 0#1))
  else
    (do
      let w__1071 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1072 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1071 19 19 w__1072))
  let w__1074 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1073 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1073) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1074 : Bool)
  then
    (do
      let w__1075 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1075 18 18 0#1))
  else
    (do
      let w__1076 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1077 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1076 18 18 w__1077))
  let w__1079 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1078 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1078) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1079 : Bool)
  then
    (do
      let w__1080 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1080 17 17 0#1))
  else
    (do
      let w__1081 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1082 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1081 17 17 w__1082))
  let w__1084 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1083 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1083) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1084 : Bool)
  then
    (do
      let w__1085 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1085 16 16 0#1))
  else
    (do
      let w__1086 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1087 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1086 16 16 w__1087))
  let w__1089 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1088 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1088) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1089 : Bool)
  then
    (do
      let w__1090 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1090 15 15 0#1))
  else
    (do
      let w__1091 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1092 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1091 15 15 w__1092))
  (pure true)


end ArmFull.Functions
