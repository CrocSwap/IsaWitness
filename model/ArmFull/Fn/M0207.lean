import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0023
import ArmFull.Fn.M0035
import ArmFull.Fn.M0038
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0050
import ArmFull.Fn.M0052
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0099
import ArmFull.Fn.M0116
import ArmFull.Fn.M0145
import ArmFull.Fn.M0166
import ArmFull.Fn.M0196
import ArmFull.Fn.M0197
import ArmFull.Fn.M0198
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
def AArch32_AutoGen_ArchitectureReset__seg2 (cold : Bool) : SailM Bool := do
  let w__735 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_VGrp1E w__735 0#1))
  let w__736 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_VGrp0D w__736 0#1))
  let w__737 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_VGrp0E w__737 0#1))
  let w__738 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_NP w__738 0#1))
  let w__739 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_LRENP w__739 0#1))
  let w__740 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_U w__740 0#1))
  let w__741 ← (( do (ICH_MISR_read ()) ) : SailM (BitVec 32) )
  (ICH_MISR_write (_update_ICH_MISR_Type_EOI w__741 0#1))
  let w__742 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (_update_CPACR_Type_ASEDIS w__742 0#1))
  let w__743 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (Mk_CPACR_Type (set_slice 2 w__743 29 0b00#2)))
  let w__744 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (Mk_CPACR_Type (set_slice 4 w__744 24 0b0000#4)))
  let w__745 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (_update_CPACR_Type_cp11 w__745 0b00#2))
  let w__746 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (_update_CPACR_Type_cp10 w__746 0b00#2))
  let w__747 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (Mk_CPACR_Type (set_slice 20 w__747 0 0b00000000000000000000#20)))
  let w__748 ← (( do (ICV_IAR0_read ()) ) : SailM (BitVec 32) )
  (ICV_IAR0_write (Mk_ICV_IAR0_Type (set_slice 8 w__748 24 0b00000000#8)))
  let w__749 ← (( do (ISR_read ()) ) : SailM (BitVec 32) )
  (ISR_write (Mk_ISR_Type (set_slice 23 w__749 9 0b00000000000000000000000#23)))
  let w__750 ← (( do (ISR_read ()) ) : SailM (BitVec 32) )
  (ISR_write (Mk_ISR_Type (set_slice 6 w__750 0 0b000000#6)))
  let w__751 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_AFE w__751 0#1))
  let w__752 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_TRE w__752 0#1))
  let w__753 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 2 w__753 26 0b00#2)))
  let w__754 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 1 w__754 24 0#1)))
  let w__755 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 1 w__755 22 1#1)))
  let w__756 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 1 w__756 21 0#1)))
  let w__757 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_UWXN w__757 0#1))
  let w__758 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_WXN w__758 0#1))
  let w__759 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_nTWE w__759 1#1))
  let w__760 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 1 w__760 17 0#1)))
  let w__761 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_nTWI w__761 1#1))
  let w__762 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 2 w__762 14 0b00#2)))
  let w__763 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_I w__763 0#1))
  let w__764 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 1 w__764 11 1#1)))
  let w__765 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (Mk_SCTLR_Type (set_slice 1 w__765 9 0#1)))
  let w__766 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_SED w__766 0#1))
  let w__767 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_ITD w__767 0#1))
  let w__768 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_CP15BEN w__768 1#1))
  let w__769 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_LSMAOE w__769 1#1))
  let w__770 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_nTLSMD w__770 1#1))
  let w__771 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_C w__771 0#1))
  let w__772 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_A w__772 0#1))
  let w__773 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
  (SCTLR_write (_update_SCTLR_Type_M w__773 0#1))
  let w__774 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 1 w__774 31 0#1)))
  let w__775 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 10 w__775 19 0b0000000000#10)))
  let w__776 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 2 w__776 13 0b00#2)))
  let w__777 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 6 w__777 6 0b000000#6)))
  let w__778 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRint_write (Mk_DBGDSCRint_Type (set_slice 2 w__778 0 0b00#2)))
  let w__779 ← (( do (DBGDCCINT_read ()) ) : SailM (BitVec 32) )
  (DBGDCCINT_write (Mk_DBGDCCINT_Type (set_slice 1 w__779 31 0#1)))
  let w__780 ← (( do (DBGDCCINT_read ()) ) : SailM (BitVec 32) )
  (DBGDCCINT_write (_update_DBGDCCINT_Type_RX w__780 0#1))
  let w__781 ← (( do (DBGDCCINT_read ()) ) : SailM (BitVec 32) )
  (DBGDCCINT_write (_update_DBGDCCINT_Type_TX w__781 0#1))
  let w__782 ← (( do (DBGDCCINT_read ()) ) : SailM (BitVec 32) )
  (DBGDCCINT_write (Mk_DBGDCCINT_Type (set_slice 29 w__782 0 0b00000000000000000000000000000#29)))
  let w__783 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 w__783 28 0#1)))
  let w__784 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 2 w__784 24 0b00#2)))
  let w__785 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 w__785 20 0#1)))
  let w__786 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (_update_DBGDSCRext_Type_MDBGen w__786 0#1))
  let w__787 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 1 w__787 13 0#1)))
  let w__788 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (_update_DBGDSCRext_Type_UDCCdis w__788 0#1))
  let w__789 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 5 w__789 7 0b00000#5)))
  let w__790 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  (DBGDSCRext_write (Mk_DBGDSCRext_Type (set_slice 2 w__790 0 0b00#2)))
  let w__791 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 15 w__791 17 0b000000000000000#15)))
  let w__792 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 3 w__792 13 0b000#3)))
  let w__793 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 1 w__793 11 0#1)))
  let w__794 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 5 w__794 4 0b00000#5)))
  let w__795 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 15 w__795 17 0b000000000000000#15)))
  let w__796 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 3 w__796 13 0b000#3)))
  let w__797 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 2 w__797 10 0b00#2)))
  let w__798 ← (( do (IFSR_read ()) ) : SailM (BitVec 32) )
  (IFSR_write (Mk_IFSR_Type (set_slice 3 w__798 6 0b000#3)))
  let w__799 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  writeReg DBGDIDR (BitVec.update w__799 15 (Bit 1#1))
  let w__800 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  writeReg DBGDIDR (BitVec.update w__800 13 (Bit 0#1))
  let w__801 ← (( do readReg DBGDIDR ) : SailM (BitVec 32) )
  writeReg DBGDIDR (Sail.BitVec.updateSubrange w__801 11 0 0b000000000000#12)
  let w__802 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTP_CTL_write (Mk_CNTP_CTL_Type (set_slice 29 w__802 3 0b00000000000000000000000000000#29)))
  let w__803 ← (( do (CNTP_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTP_CTL_write (_update_CNTP_CTL_Type_ENABLE w__803 0#1))
  let w__804 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  (FPSCR_write (Mk_FPSCR_Type (set_slice 2 w__804 13 0b00#2)))
  let w__805 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
  (FPSCR_write (Mk_FPSCR_Type (set_slice 2 w__805 5 0b00#2)))
  let w__806 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
  (HTRFCR_write (Mk_HTRFCR_Type (set_slice 25 w__806 7 0b0000000000000000000000000#25)))
  let w__808 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__808 : Bool)
  then
    (do
      let w__809 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      (HTRFCR_write (_update_HTRFCR_Type_TS w__809 0b00#2)))
  else
    (do
      let w__810 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      let w__811 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      (HTRFCR_write (_update_HTRFCR_Type_TS w__810 w__811)))
  let w__812 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
  (HTRFCR_write (Mk_HTRFCR_Type (set_slice 1 w__812 4 0#1)))
  let w__814 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__814 : Bool)
  then
    (do
      let w__815 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      (HTRFCR_write (_update_HTRFCR_Type_CX w__815 0#1)))
  else
    (do
      let w__816 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      let w__817 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HTRFCR_write (_update_HTRFCR_Type_CX w__816 w__817)))
  let w__818 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
  (HTRFCR_write (Mk_HTRFCR_Type (set_slice 1 w__818 2 0#1)))
  let w__820 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__820 : Bool)
  then
    (do
      let w__821 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      (HTRFCR_write (_update_HTRFCR_Type_E2TRE w__821 0#1)))
  else
    (do
      let w__822 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      let w__823 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HTRFCR_write (_update_HTRFCR_Type_E2TRE w__822 w__823)))
  let w__825 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__825 : Bool)
  then
    (do
      let w__826 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      (HTRFCR_write (_update_HTRFCR_Type_E0HTRE w__826 0#1)))
  else
    (do
      let w__827 ← (( do (HTRFCR_read ()) ) : SailM (BitVec 32) )
      let w__828 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (HTRFCR_write (_update_HTRFCR_Type_E0HTRE w__827 w__828)))
  let w__829 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  let w__830 ← (( do (__UNKNOWN_bits 8) ) : SailM (BitVec 8) )
  (VPIDR_write (_update_VPIDR_Type_Implementer w__829 w__830))
  let w__831 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  let w__832 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
  (VPIDR_write (_update_VPIDR_Type_Variant w__831 w__832))
  let w__833 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  let w__834 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
  (VPIDR_write (_update_VPIDR_Type_Architecture w__833 w__834))
  let w__835 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  let w__836 ← (( do (__UNKNOWN_bits 12) ) : SailM (BitVec 12) )
  (VPIDR_write (_update_VPIDR_Type_PartNum w__835 w__836))
  let w__837 ← (( do (VPIDR_read ()) ) : SailM (BitVec 32) )
  let w__838 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
  (VPIDR_write (_update_VPIDR_Type_Revision w__837 w__838))
  let w__839 ← (( do (PMSWINC_read ()) ) : SailM (BitVec 32) )
  (PMSWINC_write (Mk_PMSWINC_Type (set_slice 1 w__839 31 0#1)))
  let w__840 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTV_CTL_write (Mk_CNTV_CTL_Type (set_slice 29 w__840 3 0b00000000000000000000000000000#29)))
  let w__841 ← (( do (CNTV_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTV_CTL_write (_update_CNTV_CTL_Type_ENABLE w__841 0#1))
  let w__842 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
  (DBGOSLSR_write (Mk_DBGOSLSR_Type (set_slice 28 w__842 4 0b0000000000000000000000000000#28)))
  if (cold : Bool)
  then
    (do
      let w__843 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
      (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK w__843 1#1)))
  else (pure (()))
  let w__844 ← (( do (TRFCR_read ()) ) : SailM (BitVec 32) )
  (TRFCR_write (Mk_TRFCR_Type (set_slice 25 w__844 7 0b0000000000000000000000000#25)))
  let w__845 ← (( do (TRFCR_read ()) ) : SailM (BitVec 32) )
  (TRFCR_write (Mk_TRFCR_Type (set_slice 3 w__845 2 0b000#3)))
  let w__846 ← (( do (TRFCR_read ()) ) : SailM (BitVec 32) )
  (TRFCR_write (_update_TRFCR_Type_E1TRE w__846 0#1))
  let w__847 ← (( do (TRFCR_read ()) ) : SailM (BitVec 32) )
  (TRFCR_write (_update_TRFCR_Type_E0TRE w__847 0#1))
  let w__848 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
  (CNTHP_CTL_write (Mk_CNTHP_CTL_Type (set_slice 29 w__848 3 0b00000000000000000000000000000#29)))
  let w__850 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "the PE resets into EL2 or EL3"))
    else (pure false) ) : SailM Bool )
  if (w__850 : Bool)
  then
    (do
      let w__851 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
      (CNTHP_CTL_write (_update_CNTHP_CTL_Type_ENABLE w__851 0#1)))
  else
    (do
      let w__852 ← (( do (CNTHP_CTL_read ()) ) : SailM (BitVec 32) )
      let w__853 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      (CNTHP_CTL_write (_update_CNTHP_CTL_Type_ENABLE w__852 w__853)))
  let w__854 ← (( do (CCSIDR_read ()) ) : SailM (BitVec 32) )
  (CCSIDR_write (Mk_CCSIDR_Type (set_slice 8 w__854 24 0b00000000#8)))
  let w__855 ← (( do (CCSIDR_read ()) ) : SailM (BitVec 32) )
  (CCSIDR_write (Mk_CCSIDR_Type (set_slice 4 w__855 28 0b0000#4)))
  let w__856 ← (( do readReg DBGDEVID2 ) : SailM (BitVec 32) )
  writeReg DBGDEVID2 (Sail.BitVec.updateSubrange w__856 31 0 0b00000000000000000000000000000000#32)
  let w__857 ← (( do (ICV_DIR_read ()) ) : SailM (BitVec 32) )
  (ICV_DIR_write (Mk_ICV_DIR_Type (set_slice 8 w__857 24 0b00000000#8)))
  let w__858 ← (( do (MPIDR_read ()) ) : SailM (BitVec 32) )
  (MPIDR_write (Mk_MPIDR_Type (set_slice 5 w__858 25 0b00000#5)))
  let w__859 ← (( do (DSPSR2_read ()) ) : SailM (BitVec 32) )
  (DSPSR2_write (Mk_DSPSR2_Type (set_slice 30 w__859 2 0b000000000000000000000000000000#30)))
  let w__860 ← (( do (DSPSR2_read ()) ) : SailM (BitVec 32) )
  (DSPSR2_write (Mk_DSPSR2_Type (set_slice 1 w__860 0 0#1)))
  let w__861 ← (( do (ICC_HPPIR1_read ()) ) : SailM (BitVec 32) )
  (ICC_HPPIR1_write (Mk_ICC_HPPIR1_Type (set_slice 8 w__861 24 0b00000000#8)))
  let w__862 ← (( do (ICC_SRE_read ()) ) : SailM (BitVec 32) )
  (ICC_SRE_write (Mk_ICC_SRE_Type (set_slice 29 w__862 3 0b00000000000000000000000000000#29)))
  let w__863 ← (( do (ICC_SRE_read ()) ) : SailM (BitVec 32) )
  (ICC_SRE_write (_update_ICC_SRE_Type_DIB w__863 0#1))
  let w__864 ← (( do (ICC_SRE_read ()) ) : SailM (BitVec 32) )
  (ICC_SRE_write (_update_ICC_SRE_Type_DFB w__864 0#1))
  let w__865 ← (( do (ICC_SRE_read ()) ) : SailM (BitVec 32) )
  (ICC_SRE_write (_update_ICC_SRE_Type_SRE w__865 0#1))
  let w__866 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__866 31 29 0b000#3)
  if (cold : Bool)
  then
    (do
      let w__867 ← (( do readReg SDCR ) : SailM (BitVec 32) )
      writeReg SDCR (Sail.BitVec.updateSubrange w__867 28 28 1#1))
  else (pure (()))
  let w__868 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__868 26 24 0b000#3)
  let w__869 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__869 23 23 0#1)
  let w__870 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (BitVec.update w__870 22 (Bit 0#1))
  let w__871 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__871 21 21 0#1)
  let w__872 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__872 20 20 0#1)
  let w__873 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__873 19 19 0#1)
  let w__874 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__874 18 18 0#1)
  let w__875 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__875 17 17 0#1)
  let w__876 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (BitVec.update w__876 16 (Bit 0#1))
  let w__877 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__877 15 14 0b00#2)
  let w__878 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  writeReg SDCR (Sail.BitVec.updateSubrange w__878 13 0 0b00000000000000#14)
  let w__879 ← (( do (AMUSERENR_read ()) ) : SailM (BitVec 32) )
  (AMUSERENR_write (Mk_AMUSERENR_Type (set_slice 31 w__879 1 0b0000000000000000000000000000000#31)))
  let w__880 ← (( do (AMCGCR_read ()) ) : SailM (BitVec 32) )
  (AMCGCR_write (Mk_AMCGCR_Type (set_slice 16 w__880 16 0b0000000000000000#16)))
  let w__881 ← (( do (AMCFGR_read ()) ) : SailM (BitVec 32) )
  (AMCFGR_write (Mk_AMCFGR_Type (set_slice 3 w__881 25 0b000#3)))
  let w__882 ← (( do (AMCFGR_read ()) ) : SailM (BitVec 32) )
  (AMCFGR_write (Mk_AMCFGR_Type (set_slice 10 w__882 14 0b0000000000#10)))
  let w__883 ← (( do (AMCNTENCLR1_read ()) ) : SailM (BitVec 32) )
  (AMCNTENCLR1_write (Mk_AMCNTENCLR1_Type (set_slice 16 w__883 16 0b0000000000000000#16)))
  if (cold : Bool)
  then
    (do
      let w__884 ← (( do (AMCNTENCLR1_read ()) ) : SailM (BitVec 32) )
      (AMCNTENCLR1_write (Mk_AMCNTENCLR1_Type (set_slice 16 w__884 0 0b0000000000000000#16))))
  else (pure (()))
  let w__885 ← (( do (AMCNTENSET0_read ()) ) : SailM (BitVec 32) )
  (AMCNTENSET0_write (Mk_AMCNTENSET0_Type (set_slice 16 w__885 16 0b0000000000000000#16)))
  let w__886 ← (( do (AMCNTENSET0_read ()) ) : SailM (BitVec 32) )
  (AMCNTENSET0_write (Mk_AMCNTENSET0_Type (set_slice 12 w__886 4 0b000000000000#12)))
  if (cold : Bool)
  then
    (do
      let w__887 ← (( do (AMCNTENSET0_read ()) ) : SailM (BitVec 32) )
      (AMCNTENSET0_write (Mk_AMCNTENSET0_Type (set_slice 4 w__887 0 0b0000#4))))
  else (pure (()))
  let w__888 ← (( do (AMCNTENCLR0_read ()) ) : SailM (BitVec 32) )
  (AMCNTENCLR0_write (Mk_AMCNTENCLR0_Type (set_slice 16 w__888 16 0b0000000000000000#16)))
  let w__889 ← (( do (AMCNTENCLR0_read ()) ) : SailM (BitVec 32) )
  (AMCNTENCLR0_write (Mk_AMCNTENCLR0_Type (set_slice 12 w__889 4 0b000000000000#12)))
  if (cold : Bool)
  then
    (do
      let w__890 ← (( do (AMCNTENCLR0_read ()) ) : SailM (BitVec 32) )
      (AMCNTENCLR0_write (Mk_AMCNTENCLR0_Type (set_slice 4 w__890 0 0b0000#4))))
  else (pure (()))
  let w__891 ← (( do (AMCNTENSET1_read ()) ) : SailM (BitVec 32) )
  (AMCNTENSET1_write (Mk_AMCNTENSET1_Type (set_slice 16 w__891 16 0b0000000000000000#16)))
  if (cold : Bool)
  then
    (do
      let w__892 ← (( do (AMCNTENSET1_read ()) ) : SailM (BitVec 32) )
      (AMCNTENSET1_write (Mk_AMCNTENSET1_Type (set_slice 16 w__892 0 0b0000000000000000#16))))
  else (pure (()))
  let w__893 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
  (AMCR_write (Mk_AMCR_Type (set_slice 14 w__893 18 0b00000000000000#14)))
  let w__894 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
  (AMCR_write (Mk_AMCR_Type (set_slice 6 w__894 11 0b000000#6)))
  let w__895 ← (( do (AMCR_read ()) ) : SailM (BitVec 32) )
  (AMCR_write (Mk_AMCR_Type (set_slice 10 w__895 0 0b0000000000#10)))
  let w__896 ← (( do (ERRIDR_read ()) ) : SailM (BitVec 32) )
  (ERRIDR_write (Mk_ERRIDR_Type (set_slice 16 w__896 16 0b0000000000000000#16)))
  let w__897 ← (( do (ERRSELR_read ()) ) : SailM (BitVec 32) )
  (ERRSELR_write (Mk_ERRSELR_Type (set_slice 16 w__897 16 0b0000000000000000#16)))
  let w__898 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 19 w__898 12 0b0000000000000000000#19)))
  let w__899 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 3 w__899 6 0b000#3)))
  let w__900 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 15 w__900 16 0b000000000000000#15)))
  let w__901 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 1 w__901 13 0#1)))
  let w__902 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 1 w__902 11 0#1)))
  let w__903 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 5 w__903 4 0b00000#5)))
  let w__904 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 15 w__904 16 0b000000000000000#15)))
  let w__905 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 1 w__905 13 0#1)))
  let w__906 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 2 w__906 10 0b00#2)))
  let w__907 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
  (DISR_write (Mk_DISR_Type (set_slice 3 w__907 6 0b000#3)))
  let w__908 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
  (VDFSR_write (Mk_VDFSR_Type (set_slice 16 w__908 16 0b0000000000000000#16)))
  let w__909 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
  (VDFSR_write (Mk_VDFSR_Type (set_slice 1 w__909 13 0#1)))
  let w__910 ← (( do (VDFSR_read ()) ) : SailM (BitVec 32) )
  (VDFSR_write (Mk_VDFSR_Type (set_slice 12 w__910 0 0b000000000000#12)))
  let w__911 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 15 w__911 16 0b000000000000000#15)))
  let w__912 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 1 w__912 13 0#1)))
  let w__913 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 1 w__913 11 0#1)))
  let w__914 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 5 w__914 4 0b00000#5)))
  let w__915 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 15 w__915 16 0b000000000000000#15)))
  let w__916 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 1 w__916 13 0#1)))
  let w__917 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 2 w__917 10 0b00#2)))
  let w__918 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
  (VDISR_write (Mk_VDISR_Type (set_slice 3 w__918 6 0b000#3)))
  let w__919 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__919 30 8 0b00000000000000000000000#23)
  let w__920 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__920 6 6 0#1)
  let w__921 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  let w__922 ← (( do
    (__IMPDEF_boolean "access is Secure, in a system that supports two Security states") ) : SailM
    Bool )
  let w__923 : Int :=
    if (w__922 : Bool)
    then 5
    else 4
  writeReg GICD_CTLR (BitVec.update w__921 (Sail.Int.toNatChecked (w__923)) (Bit 0#1))
  let w__924 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__924 4 4 0#1)
  let w__925 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (BitVec.update w__925 3 (Bit 0#1))
  let w__926 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__926 30 5 0b00000000000000000000000000#26)
  let w__927 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__927 3 2 0b00#2)
  let w__928 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__928 30 9 0b0000000000000000000000#22)
  let w__929 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__929 8 8 0#1)
  let w__930 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (BitVec.update w__930 5 (Bit 0#1))
  let w__931 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__931 4 4 0#1)
  let w__932 ← (( do readReg GICD_CTLR ) : SailM (BitVec 32) )
  writeReg GICD_CTLR (Sail.BitVec.updateSubrange w__932 3 2 0b00#2)
  let w__933 ← (( do readReg GICC_IAR ) : SailM (BitVec 32) )
  writeReg GICC_IAR (Sail.BitVec.updateSubrange w__933 31 24 0b00000000#8)
  let w__934 ← (( do readReg CTILAR ) : SailM (BitVec 32) )
  writeReg CTILAR (Sail.BitVec.updateSubrange w__934 31 0 0b00000000000000000000000000000000#32)
  let w__935 ← (( do readReg CTIPIDR2 ) : SailM (BitVec 32) )
  writeReg CTIPIDR2 (Sail.BitVec.updateSubrange w__935 31 8 0b000000000000000000000000#24)
  let w__936 ← (( do readReg CTICIDR1 ) : SailM (BitVec 32) )
  writeReg CTICIDR1 (Sail.BitVec.updateSubrange w__936 31 8 0b000000000000000000000000#24)
  let w__937 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__937 31 8 0b000000000000000000000000#24)
  let w__938 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__938 7 7 0#1)
  let w__939 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__939 6 6 0#1)
  let w__940 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__940 5 5 0#1)
  let w__941 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__941 4 4 0#1)
  let w__942 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__942 3 3 0#1)
  let w__943 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__943 2 2 0#1)
  let w__944 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__944 1 1 0#1)
  let w__945 ← (( do readReg GICH_MISR ) : SailM (BitVec 32) )
  writeReg GICH_MISR (Sail.BitVec.updateSubrange w__945 0 0 0#1)
  let w__946 ← (( do readReg CTIDEVTYPE ) : SailM (BitVec 32) )
  writeReg CTIDEVTYPE (Sail.BitVec.updateSubrange w__946 31 8 0b000000000000000000000000#24)
  let w__947 ← (( do readReg GITS_CTLR ) : SailM (BitVec 32) )
  writeReg GITS_CTLR (Sail.BitVec.updateSubrange w__947 31 31 1#1)
  let w__948 ← (( do readReg GITS_CTLR ) : SailM (BitVec 32) )
  writeReg GITS_CTLR (Sail.BitVec.updateSubrange w__948 30 9 0b0000000000000000000000#22)
  let w__949 ← (( do readReg GITS_CTLR ) : SailM (BitVec 32) )
  writeReg GITS_CTLR (Sail.BitVec.updateSubrange w__949 8 8 0#1)
  let w__950 ← (( do readReg GITS_CTLR ) : SailM (BitVec 32) )
  writeReg GITS_CTLR (Sail.BitVec.updateSubrange w__950 3 2 0b00#2)
  let w__951 ← (( do readReg GITS_CTLR ) : SailM (BitVec 32) )
  writeReg GITS_CTLR (Sail.BitVec.updateSubrange w__951 1 1 0#1)
  let w__952 ← (( do readReg GITS_CTLR ) : SailM (BitVec 32) )
  writeReg GITS_CTLR (Sail.BitVec.updateSubrange w__952 0 0 0#1)
  let w__953 ← (( do readReg GICR_IIDR ) : SailM (BitVec 32) )
  writeReg GICR_IIDR (Sail.BitVec.updateSubrange w__953 23 20 0b0000#4)
  let w__954 ← (( do readReg EDLSR ) : SailM (BitVec 32) )
  writeReg EDLSR (Sail.BitVec.updateSubrange w__954 31 3 0b00000000000000000000000000000#29)
  let w__956 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_DoPD))
    else (pure false) ) : SailM Bool )
  if (w__956 : Bool)
  then
    (do
      let w__957 ← (( do readReg EDLSR ) : SailM (BitVec 32) )
      writeReg EDLSR (Sail.BitVec.updateSubrange w__957 1 1 1#1))
  else (pure (()))
  let w__958 ← (( do (IsFeatureImplemented FEAT_DoPD) ) : SailM Bool )
  if ((! w__958) : Bool)
  then
    (do
      let w__959 ← (( do readReg EDLSR ) : SailM (BitVec 32) )
      writeReg EDLSR (Sail.BitVec.updateSubrange w__959 1 1 1#1))
  else (pure (()))
  let w__960 ← (( do readReg CTIPIDR1 ) : SailM (BitVec 32) )
  writeReg CTIPIDR1 (Sail.BitVec.updateSubrange w__960 31 8 0b000000000000000000000000#24)
  let w__961 ← (( do readReg GICV_IAR ) : SailM (BitVec 32) )
  writeReg GICV_IAR (Sail.BitVec.updateSubrange w__961 31 25 0b0000000#7)
  let w__962 ← (( do readReg CNTSR ) : SailM (BitVec 32) )
  writeReg CNTSR (Sail.BitVec.updateSubrange w__962 31 18 0b00000000000000#14)
  let w__963 ← (( do readReg CNTSR ) : SailM (BitVec 32) )
  writeReg CNTSR (Sail.BitVec.updateSubrange w__963 17 8 0b0000000000#10)
  let w__964 ← (( do readReg CNTSR ) : SailM (BitVec 32) )
  writeReg CNTSR (Sail.BitVec.updateSubrange w__964 7 2 0b000000#6)
  let w__965 ← (( do readReg CNTSR ) : SailM (BitVec 32) )
  writeReg CNTSR (BitVec.update w__965 0 (Bit 0#1))
  let w__966 ← (( do readReg EDCIDR3 ) : SailM (BitVec 32) )
  writeReg EDCIDR3 (Sail.BitVec.updateSubrange w__966 31 8 0b000000000000000000000000#24)
  let w__967 ← (( do readReg GICM_SETSPI_NSR ) : SailM (BitVec 32) )
  writeReg GICM_SETSPI_NSR (Sail.BitVec.updateSubrange w__967 31 13 0b0000000000000000000#19)
  let w__968 ← (( do readReg GICR_WAKER ) : SailM (BitVec 32) )
  writeReg GICR_WAKER (Sail.BitVec.updateSubrange w__968 30 3 0b0000000000000000000000000000#28)
  let w__969 ← (( do readReg GICR_WAKER ) : SailM (BitVec 32) )
  writeReg GICR_WAKER (Sail.BitVec.updateSubrange w__969 2 2 1#1)
  let w__970 ← (( do readReg GICR_WAKER ) : SailM (BitVec 32) )
  writeReg GICR_WAKER (Sail.BitVec.updateSubrange w__970 1 1 1#1)
  let w__971 ← (( do readReg GITS_PARTIDR ) : SailM (BitVec 32) )
  writeReg GITS_PARTIDR (Sail.BitVec.updateSubrange w__971 31 24 0b00000000#8)
  let w__972 ← (( do readReg GITS_PARTIDR ) : SailM (BitVec 32) )
  writeReg GITS_PARTIDR (Sail.BitVec.updateSubrange w__972 23 16 0b00000000#8)
  let w__973 ← (( do readReg GITS_PARTIDR ) : SailM (BitVec 32) )
  writeReg GITS_PARTIDR (Sail.BitVec.updateSubrange w__973 15 0 0b0000000000000000#16)
  let w__974 ← (( do readReg GICV_HPPIR ) : SailM (BitVec 32) )
  writeReg GICV_HPPIR (Sail.BitVec.updateSubrange w__974 31 25 0b0000000#7)
  let w__975 ← (( do readReg CTIPIDR0 ) : SailM (BitVec 32) )
  writeReg CTIPIDR0 (Sail.BitVec.updateSubrange w__975 31 8 0b000000000000000000000000#24)
  let w__976 ← (( do readReg GICM_SETSPI_SR ) : SailM (BitVec 32) )
  writeReg GICM_SETSPI_SR (Sail.BitVec.updateSubrange w__976 31 13 0b0000000000000000000#19)
  let w__977 ← (( do readReg GICV_DIR ) : SailM (BitVec 32) )
  writeReg GICV_DIR (Sail.BitVec.updateSubrange w__977 31 25 0b0000000#7)
  let w__978 ← (( do readReg CTIDEVID2 ) : SailM (BitVec 32) )
  writeReg CTIDEVID2 (Sail.BitVec.updateSubrange w__978 31 0 0b00000000000000000000000000000000#32)
  let w__979 ← (( do readReg EDPIDR3 ) : SailM (BitVec 32) )
  writeReg EDPIDR3 (Sail.BitVec.updateSubrange w__979 31 8 0b000000000000000000000000#24)
  let w__980 ← (( do readReg GICC_STATUSR ) : SailM (BitVec 32) )
  writeReg GICC_STATUSR (Sail.BitVec.updateSubrange w__980 31 5 0b000000000000000000000000000#27)
  let w__981 ← (( do readReg GICM_IIDR ) : SailM (BitVec 32) )
  writeReg GICM_IIDR (Sail.BitVec.updateSubrange w__981 23 20 0b0000#4)
  let w__982 ← (( do (EDSCR2_read ()) ) : SailM (BitVec 32) )
  (EDSCR2_write (Mk_EDSCR2_Type (set_slice 28 w__982 4 0b0000000000000000000000000000#28)))
  if (cold : Bool)
  then
    (do
      let w__983 ← (( do (EDSCR2_read ()) ) : SailM (BitVec 32) )
      (EDSCR2_write (_update_EDSCR2_Type_EHBWE w__983 0#1)))
  else (pure (()))
  let w__984 ← (( do (EDSCR2_read ()) ) : SailM (BitVec 32) )
  (EDSCR2_write (Mk_EDSCR2_Type (set_slice 3 w__984 0 0b000#3)))
  let w__985 ← (( do readReg GICR_VSGIR ) : SailM (BitVec 32) )
  writeReg GICR_VSGIR (Sail.BitVec.updateSubrange w__985 31 16 0b0000000000000000#16)
  let w__986 ← (( do readReg EDDEVTYPE ) : SailM (BitVec 32) )
  writeReg EDDEVTYPE (Sail.BitVec.updateSubrange w__986 31 8 0b000000000000000000000000#24)
  let w__987 ← (( do readReg CTIDEVCTL ) : SailM (BitVec 32) )
  writeReg CTIDEVCTL (Sail.BitVec.updateSubrange w__987 31 2 0b000000000000000000000000000000#30)
  let w__988 ← (( do readReg CTIDEVCTL ) : SailM (BitVec 32) )
  writeReg CTIDEVCTL (Sail.BitVec.updateSubrange w__988 1 1 0#1)
  let w__989 ← (( do readReg CTIDEVCTL ) : SailM (BitVec 32) )
  writeReg CTIDEVCTL (Sail.BitVec.updateSubrange w__989 0 0 0#1)
  let w__990 ← (( do readReg GICM_TYPER ) : SailM (BitVec 32) )
  writeReg GICM_TYPER (Sail.BitVec.updateSubrange w__990 15 11 0b00000#5)
  let w__991 ← (( do readReg GICD_TYPER2 ) : SailM (BitVec 32) )
  writeReg GICD_TYPER2 (Sail.BitVec.updateSubrange w__991 31 9 0b00000000000000000000000#23)
  let w__992 ← (( do readReg GICD_TYPER2 ) : SailM (BitVec 32) )
  writeReg GICD_TYPER2 (Sail.BitVec.updateSubrange w__992 6 5 0b00#2)
  let w__993 ← (( do readReg GICH_EISR ) : SailM (BitVec 32) )
  writeReg GICH_EISR (Sail.BitVec.updateSubrange w__993 31 16 0b0000000000000000#16)
  let w__994 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__994 31 16 0b0000000000000000#16)
  let w__995 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__995 15 15 1#1)
  let w__996 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__996 14 14 1#1)
  let w__997 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__997 13 13 1#1)
  let w__998 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__998 12 12 1#1)
  let w__999 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__999 11 11 1#1)
  let w__1000 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1000 10 10 1#1)
  let w__1001 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1001 9 9 1#1)
  let w__1002 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1002 8 8 1#1)
  let w__1003 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1003 7 7 1#1)
  let w__1004 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1004 6 6 1#1)
  let w__1005 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1005 5 5 1#1)
  let w__1006 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1006 4 4 1#1)
  let w__1007 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1007 3 3 1#1)
  let w__1008 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1008 2 2 1#1)
  let w__1009 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1009 1 1 1#1)
  let w__1010 ← (( do readReg GICH_ELRSR ) : SailM (BitVec 32) )
  writeReg GICH_ELRSR (Sail.BitVec.updateSubrange w__1010 0 0 1#1)
  let w__1011 ← (( do readReg GICM_CLRSPI_NSR ) : SailM (BitVec 32) )
  writeReg GICM_CLRSPI_NSR (Sail.BitVec.updateSubrange w__1011 31 13 0b0000000000000000000#19)
  let w__1012 ← (( do readReg GICV_STATUSR ) : SailM (BitVec 32) )
  writeReg GICV_STATUSR (Sail.BitVec.updateSubrange w__1012 31 4 0b0000000000000000000000000000#28)
  let w__1013 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
  writeReg CNTCR (Sail.BitVec.updateSubrange w__1013 31 18 0b00000000000000#14)
  let w__1014 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
  writeReg CNTCR (Sail.BitVec.updateSubrange w__1014 17 8 0b0000000000#10)
  let w__1015 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
  writeReg CNTCR (Sail.BitVec.updateSubrange w__1015 7 3 0b00000#5)
  let w__1016 ← (( do readReg CNTCR ) : SailM (BitVec 32) )
  writeReg CNTCR (Sail.BitVec.updateSubrange w__1016 0 0 0#1)
  let w__1017 ← (( do readReg EDESR ) : SailM (BitVec 32) )
  writeReg EDESR (Sail.BitVec.updateSubrange w__1017 31 4 0b0000000000000000000000000000#28)
  let w__1018 ← (( do readReg EDESR ) : SailM (BitVec 32) )
  writeReg EDESR (Sail.BitVec.updateSubrange w__1018 3 3 0#1)
  if (cold : Bool)
  then
    (do
      let w__1019 ← (( do readReg EDESR ) : SailM (BitVec 32) )
      writeReg EDESR (Sail.BitVec.updateSubrange w__1019 2 2 0#1))
  else (pure (()))
  let w__1020 ← (( do readReg EDESR ) : SailM (BitVec 32) )
  writeReg EDESR (Sail.BitVec.updateSubrange w__1020 0 0 0#1)
  let w__1021 ← (( do readReg EDPIDR1 ) : SailM (BitVec 32) )
  writeReg EDPIDR1 (Sail.BitVec.updateSubrange w__1021 31 8 0b000000000000000000000000#24)
  let w__1022 ← (( do readReg GICM_CLRSPI_SR ) : SailM (BitVec 32) )
  writeReg GICM_CLRSPI_SR (Sail.BitVec.updateSubrange w__1022 31 13 0b0000000000000000000#19)
  let w__1023 ← (( do readReg EDECR ) : SailM (BitVec 32) )
  writeReg EDECR (Sail.BitVec.updateSubrange w__1023 31 5 0b000000000000000000000000000#27)
  if (cold : Bool)
  then
    (do
      let w__1024 ← (( do readReg EDECR ) : SailM (BitVec 32) )
      writeReg EDECR (Sail.BitVec.updateSubrange w__1024 4 4 0#1))
  else (pure (()))
  let w__1025 ← (( do readReg EDECR ) : SailM (BitVec 32) )
  writeReg EDECR (BitVec.update w__1025 3 (Bit 0#1))
  let w__1027 ← (( do
    if ((cold : Bool) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_DoPD))
    else (pure false) ) : SailM Bool )
  if (w__1027 : Bool)
  then
    (do
      let w__1028 ← (( do readReg EDECR ) : SailM (BitVec 32) )
      writeReg EDECR (Sail.BitVec.updateSubrange w__1028 2 2 0#1))
  else (pure (()))
  let w__1029 ← (( do (IsFeatureImplemented FEAT_DoPD) ) : SailM Bool )
  if ((! w__1029) : Bool)
  then
    (do
      let w__1030 ← (( do readReg EDECR ) : SailM (BitVec 32) )
      writeReg EDECR (Sail.BitVec.updateSubrange w__1030 2 2 0#1))
  else (pure (()))
  let w__1031 ← (( do readReg EDECR ) : SailM (BitVec 32) )
  writeReg EDECR (Sail.BitVec.updateSubrange w__1031 1 1 0#1)
  let w__1032 ← (( do readReg EDECR ) : SailM (BitVec 32) )
  writeReg EDECR (Sail.BitVec.updateSubrange w__1032 0 0 0#1)
  let w__1033 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
  (EDECCR_write (Mk_EDECCR_Type (set_slice 9 w__1033 23 0b000000000#9)))
  if (cold : Bool)
  then
    (do
      let w__1034 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_RLR2 w__1034 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1035 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_RLR1 w__1035 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1036 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_RLR0 w__1036 0#1)))
  else (pure (()))
  let w__1037 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
  (EDECCR_write (Mk_EDECCR_Type (set_slice 1 w__1037 19 0#1)))
  if (cold : Bool)
  then
    (do
      let w__1038 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_RLE2 w__1038 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1039 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_RLE1 w__1039 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1040 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_NSR2 w__1040 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1041 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_NSR1 w__1041 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1042 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_NSR0 w__1042 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1043 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_SR3 w__1043 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1044 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_SR2 w__1044 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1045 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_SR1 w__1045 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1046 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_SR0 w__1046 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1047 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_NSE2 w__1047 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1048 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_NSE1 w__1048 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1049 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_SE3 w__1049 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1050 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_SE2 w__1050 0#1)))
  else (pure (()))
  if (cold : Bool)
  then
    (do
      let w__1051 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
      (EDECCR_write (_update_EDECCR_Type_SE1 w__1051 0#1)))
  else (pure (()))
  (pure true)


end ArmFull.Functions
