import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0036
import ArmFull.Fn.M0056
import ArmFull.Fn.M0087

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
def AArch64_AutoGen_ArchitectureReset__seg3 (cold : Bool) : SailM Bool := do
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__935 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__935 0 0 0#1))
  else
    (do
      let w__936 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__937 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__936 0 0 w__937))
  let w__938 ← (( do readReg DBGPRCR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGPRCR_EL1 (Sail.BitVec.updateSubrange w__938 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__939 ← (( do readReg PMCNTENCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENCLR_EL0 (Sail.BitVec.updateSubrange w__939 63 33
    0b0000000000000000000000000000000#31)
  let w__940 ← (( do readReg PMCNTENCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENCLR_EL0 (BitVec.update w__940 32 (Bit 0#1))
  let w__941 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
  (SDER32_EL3_write
    (Mk_SDER32_EL3_Type
      (set_slice 62 w__941 2 0b00000000000000000000000000000000000000000000000000000000000000#62)))
  let w__942 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
  writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__942 62 48 0b000000000000000#15)
  let w__943 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
  writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__943 3 0 0b0000#4)
  let w__944 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__944 63 40 0b000000000000000000000000#24)
  let w__945 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (BitVec.update w__945 31 (Bit 1#1))
  let w__946 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__946 29 25 0b00000#5)
  let w__947 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__947 51 48 0b0000#4)
  let w__948 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__948 63 32
    0b00000000000000000000000000000000#32)
  let w__949 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__949 17 5 0b0000000000000#13)
  let w__950 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__950 63 32
    0b00000000000000000000000000000000#32)
  let w__951 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__951 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__952 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange w__952 63 6
    0b0000000000000000000000000000000000000000000000000000000000#58)
  let w__953 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange w__953 3 0 0b0000#4)
  let w__954 ← (( do readReg ICV_EOIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_EOIR0_EL1 (Sail.BitVec.updateSubrange w__954 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__955 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__955 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__956 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__956 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__957 ← (( do readReg VBAR_EL3 ) : SailM (BitVec 64) )
  writeReg VBAR_EL3 (Sail.BitVec.updateSubrange w__957 10 0 0b00000000000#11)
  let w__958 ← (( do readReg ID_AFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AFR0_EL1 (Sail.BitVec.updateSubrange w__958 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__959 ← (( do readReg ID_AFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AFR0_EL1 (Sail.BitVec.updateSubrange w__959 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__960 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__960 63 44 0b00000000000000000000#20)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__961 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__961 43 43 0#1))
  else
    (do
      let w__962 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      let w__963 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__962 43 43 w__963))
  let w__964 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (BitVec.update w__964 42 (Bit 0#1))
  let w__965 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__965 39 37 0b000#3)
  let w__966 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__966 35 32 0b0000#4)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__967 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__967 31 30 0b00#2))
  else
    (do
      let w__968 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      let w__969 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__968 31 30 w__969))
  if (cold : Bool)
  then
    (do
      let w__970 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__970 28 28 1#1))
  else (pure (()))
  let w__971 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__971 25 24 0b00#2)
  let w__972 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__972 23 23 0#1)
  let w__973 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__973 22 20 0b000#3)
  let w__974 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (BitVec.update w__974 18 (Bit 0#1))
  let w__975 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__975 17 17 0#1)
  let w__976 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (BitVec.update w__976 16 (Bit 0#1))
  let w__977 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTKCTL_EL1 (Sail.BitVec.updateSubrange w__977 63 18
    0b0000000000000000000000000000000000000000000000#46)
  let w__978 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTKCTL_EL1 (Sail.BitVec.updateSubrange w__978 16 10 0b0000000#7)
  let w__979 ← (( do readReg LORN_EL1 ) : SailM (BitVec 64) )
  writeReg LORN_EL1 (Sail.BitVec.updateSubrange w__979 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__980 ← (( do readReg ICV_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__980 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__981 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__981 63 34 0b000000000000000000000000000000#30)
  let w__982 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (BitVec.update w__982 32 (Bit 0#1))
  let w__983 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__983 63 35 0b00000000000000000000000000000#29)
  let w__984 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__984 27 26 0b00#2)
  let w__985 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__985 19 14 0b000000#6)
  let w__986 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (BitVec.update w__986 5 (Bit 0#1))
  let w__987 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__987 63 56 0b00000000#8)
  let w__988 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__988 31 24 0b00000000#8)
  let w__989 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__989 63 32 0b00000000000000000000000000000000#32)
  let w__990 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__990 31 28 0b0000#4)
  let w__991 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
  writeReg VMECID_P_EL2 (Sail.BitVec.updateSubrange w__991 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__992 ← (( do readReg OSECCR_EL1 ) : SailM (BitVec 64) )
  writeReg OSECCR_EL1 (Sail.BitVec.updateSubrange w__992 63 32 0b00000000000000000000000000000000#32)
  let w__993 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange w__993 63 32
    0b00000000000000000000000000000000#32)
  let w__994 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__994 29 (Bit 0#1))
  let w__995 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange w__995 24 8 0b00000000000000000#17)
  let w__996 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__996 5 (Bit 0#1))
  let w__997 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__997 0 (Bit 0#1))
  let w__998 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange w__998 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__999 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__999 5 (Bit 0#1))
  let w__1000 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__1000 0 (Bit 0#1))
  let w__1001 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1001 63 63 0#1)
  let w__1002 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1002 62 62 0#1)
  let w__1003 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1003 61 61 0#1)
  let w__1004 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1004 60 60 0#1)
  let w__1005 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1005 59 59 0#1)
  let w__1006 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1006 58 58 0#1)
  let w__1007 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1007 57 57 0#1)
  let w__1008 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1008 56 56 0#1)
  let w__1009 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1009 55 55 0#1)
  let w__1010 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1010 54 54 0#1)
  let w__1011 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1011 53 53 0#1)
  let w__1012 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1012 52 52 0#1)
  let w__1013 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (BitVec.update w__1013 51 (Bit 0#1))
  let w__1014 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1014 50 50 0#1)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1015 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1015 49 49 0#1))
  else
    (do
      let w__1016 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1017 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1016 49 49 w__1017))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1018 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1018 48 48 0#1))
  else
    (do
      let w__1019 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1020 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1019 48 48 w__1020))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1021 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1021 47 47 0#1))
  else
    (do
      let w__1022 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1023 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1022 47 47 w__1023))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1024 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1024 46 46 0#1))
  else
    (do
      let w__1025 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1026 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1025 46 46 w__1026))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1027 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1027 45 45 0#1))
  else
    (do
      let w__1028 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1029 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1028 45 45 w__1029))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1030 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1030 44 44 0#1))
  else
    (do
      let w__1031 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1032 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1031 44 44 w__1032))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1033 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1033 43 43 0#1))
  else
    (do
      let w__1034 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1035 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1034 43 43 w__1035))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1036 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1036 42 42 0#1))
  else
    (do
      let w__1037 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1038 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1037 42 42 w__1038))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1039 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1039 41 41 0#1))
  else
    (do
      let w__1040 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1041 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1040 41 41 w__1041))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1042 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1042 40 40 0#1))
  else
    (do
      let w__1043 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1044 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1043 40 40 w__1044))
  let w__1045 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1045 39 39 0#1)
  let w__1046 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1046 38 38 0#1)
  let w__1047 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1047 37 37 0#1)
  let w__1048 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1048 36 36 0#1)
  let w__1049 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1049 35 35 0#1)
  let w__1050 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1050 34 34 0#1)
  let w__1051 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1051 33 33 0#1)
  let w__1052 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1052 32 32 0#1)
  let w__1053 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1053 31 31 0#1)
  let w__1054 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1054 30 30 0#1)
  let w__1055 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1055 29 29 0#1)
  let w__1056 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1056 28 28 0#1)
  let w__1057 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1057 27 27 0#1)
  let w__1058 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1058 26 26 0#1)
  let w__1059 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1059 25 25 0#1)
  let w__1060 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1060 24 24 0#1)
  let w__1061 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1061 23 23 0#1)
  let w__1062 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1062 22 22 0#1)
  let w__1063 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1063 21 21 0#1)
  let w__1064 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1064 20 20 0#1)
  let w__1065 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1065 19 19 0#1)
  let w__1066 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1066 18 18 0#1)
  let w__1067 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1067 17 17 0#1)
  let w__1068 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1068 16 16 0#1)
  let w__1069 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1069 15 15 0#1)
  let w__1070 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1070 14 14 0#1)
  let w__1071 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1071 13 13 0#1)
  let w__1072 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1072 12 12 0#1)
  let w__1073 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1073 11 11 0#1)
  let w__1074 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1074 10 10 0#1)
  let w__1075 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1075 9 9 0#1)
  let w__1076 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1076 8 8 0#1)
  let w__1077 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1077 7 7 0#1)
  let w__1078 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1078 6 6 0#1)
  let w__1079 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1079 5 5 0#1)
  let w__1080 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1080 4 4 0#1)
  let w__1081 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1081 3 3 0#1)
  let w__1082 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1082 2 2 0#1)
  let w__1083 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1083 1 1 0#1)
  let w__1084 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1084 0 0 0#1)
  let w__1085 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__1085 63 32
    0b00000000000000000000000000000000#32)
  let w__1086 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__1086 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1087 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1087 63 32 0b00000000000000000000000000000000#32)
  let w__1088 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1088 27 26 0b00#2)
  let w__1089 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1089 23 22 0b00#2)
  let w__1090 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1090 19 18 0b00#2)
  let w__1091 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1091 15 0 0b0000000000000000#16)
  let w__1092 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1092 63 32 0b00000000000000000000000000000000#32)
  let w__1093 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1093 29 21 0b000000000#9)
  let w__1094 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1094 19 14 0b000000#6)
  let w__1095 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (BitVec.update w__1095 13 (Bit 1#1))
  let w__1096 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (BitVec.update w__1096 11 (Bit 0#1))
  let w__1097 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (BitVec.update w__1097 9 (Bit 1#1))
  let w__1098 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1098 7 0 0b11111111#8)
  let w__1099 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CLIDR_EL1 (Sail.BitVec.updateSubrange w__1099 63 47 0b00000000000000000#17)
  let w__1100 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1100 63 23
    0b00000000000000000000000000000000000000000#41)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1101 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1101 22 22 0#1))
  else
    (do
      let w__1102 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1103 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1102 22 22 w__1103))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1104 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1104 20 20 0#1))
  else
    (do
      let w__1105 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1106 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1105 20 20 w__1106))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1107 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1107 19 19 0#1))
  else
    (do
      let w__1108 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1109 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1108 19 19 w__1109))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1110 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1110 18 18 0#1))
  else
    (do
      let w__1111 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1112 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1111 18 18 w__1112))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1113 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1113 17 17 0#1))
  else
    (do
      let w__1114 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1115 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1114 17 17 w__1115))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1116 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1116 15 15 0#1))
  else
    (do
      let w__1117 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1118 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1117 15 15 w__1118))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1119 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1119 14 14 0#1))
  else
    (do
      let w__1120 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1121 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1120 14 14 w__1121))
  let w__1122 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1122 13 12 0b00#2)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1123 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1123 11 11 0#1))
  else
    (do
      let w__1124 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1125 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1124 11 11 w__1125))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1126 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1126 10 10 0#1))
  else
    (do
      let w__1127 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1128 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1127 10 10 w__1128))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1129 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1129 9 9 0#1))
  else
    (do
      let w__1130 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1131 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1130 9 9 w__1131))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1132 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1132 8 8 0#1))
  else
    (do
      let w__1133 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1134 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1133 8 8 w__1134))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1135 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1135 7 7 0#1))
  else
    (do
      let w__1136 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1137 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1136 7 7 w__1137))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1138 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1138 6 6 0#1))
  else
    (do
      let w__1139 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1140 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1139 6 6 w__1140))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1141 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1141 5 5 0#1))
  else
    (do
      let w__1142 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1143 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1142 5 5 w__1143))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1144 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1144 4 4 0#1))
  else
    (do
      let w__1145 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1146 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1145 4 4 w__1146))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1147 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1147 3 3 0#1))
  else
    (do
      let w__1148 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1149 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1148 3 3 w__1149))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1150 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1150 2 2 0#1))
  else
    (do
      let w__1151 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1152 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1151 2 2 w__1152))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1153 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1153 1 1 0#1))
  else
    (do
      let w__1154 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1155 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1154 1 1 w__1155))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1156 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1156 0 0 0#1))
  else
    (do
      let w__1157 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1158 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1157 0 0 w__1158))
  let w__1159 ← (( do readReg ICV_IGRPEN1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN1_EL1 (Sail.BitVec.updateSubrange w__1159 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1160 ← (( do readReg PMXEVCNTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMXEVCNTR_EL0 (Sail.BitVec.updateSubrange w__1160 63 32
    0b00000000000000000000000000000000#32)
  let w__1161 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1161 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1162 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1162 2 2 0#1))
  else
    (do
      let w__1163 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__1164 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1163 2 2 w__1164))
  let w__1165 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR2_EL2 (BitVec.update w__1165 1 (Bit 0#1))
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1166 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1166 0 0 0#1))
  else
    (do
      let w__1167 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__1168 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1167 0 0 w__1168))
  let w__1169 ← (( do readReg MECID_P1_EL2 ) : SailM (BitVec 64) )
  writeReg MECID_P1_EL2 (Sail.BitVec.updateSubrange w__1169 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1170 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange w__1170 63 56 0b00000000#8)
  let w__1171 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange w__1171 43 41 0b000#3)
  let w__1172 ← (( do readReg ICC_SGI1R_EL1 ) : SailM (BitVec 64) )
  writeReg ICC_SGI1R_EL1 (Sail.BitVec.updateSubrange w__1172 31 28 0b0000#4)
  let w__1173 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR2_EL1 (Sail.BitVec.updateSubrange w__1173 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1174 ← (( do readReg MVFR2_EL1 ) : SailM (BitVec 64) )
  writeReg MVFR2_EL1 (Sail.BitVec.updateSubrange w__1174 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1175 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
  writeReg SPMSELR_EL0 (Sail.BitVec.updateSubrange w__1175 63 10
    0b000000000000000000000000000000000000000000000000000000#54)
  let w__1176 ← (( do readReg SPMSELR_EL0 ) : SailM (BitVec 64) )
  writeReg SPMSELR_EL0 (Sail.BitVec.updateSubrange w__1176 3 2 0b00#2)
  let w__1177 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange w__1177 63 28
    0b000000000000000000000000000000000000#36)
  let w__1178 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange w__1178 23 16 0b00000000#8)
  let w__1179 ← (( do readReg DBGAUTHSTATUS_EL1 ) : SailM (BitVec 64) )
  writeReg DBGAUTHSTATUS_EL1 (Sail.BitVec.updateSubrange w__1179 11 8 0b0000#4)
  let w__1180 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1180 63 (Bit 0#1))
  let w__1181 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1181 61 60 0b00#2)
  let w__1182 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1182 58 56 0b000#3)
  let w__1183 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1183 54 (Bit 0#1))
  let w__1184 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1184 50 (Bit 0#1))
  let w__1185 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1185 40 40 0#1)
  let w__1186 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1186 24 22 0b000#3)
  let w__1187 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1187 20 20 0#1)
  let w__1188 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1188 19 19 0#1)
  let w__1189 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (BitVec.update w__1189 6 (Bit 0#1))
  let w__1190 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  writeReg SCR_EL3 (Sail.BitVec.updateSubrange w__1190 5 4 0b11#2)
  let w__1191 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1191 63 4
    0b000000000000000000000000000000000000000000000000000000000000#60)
  let w__1192 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1192 2 2 0#1)
  let w__1193 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1193 1 1 0#1)
  let w__1194 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  writeReg ICC_SRE_EL3 (Sail.BitVec.updateSubrange w__1194 0 0 0#1)
  let w__1195 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__1195 63 32
    0b00000000000000000000000000000000#32)
  let w__1196 ← (( do readReg ID_MMFR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_MMFR3_EL1 (Sail.BitVec.updateSubrange w__1196 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1197 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1197 63 (Bit 0#1))
  let w__1198 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1198 62 62 0#1)
  let w__1199 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1199 61 61 0#1)
  let w__1200 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1200 60 60 0#1)
  let w__1201 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1201 59 58 0b00#2)
  let w__1202 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1202 57 57 0#1)
  let w__1203 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1203 56 50 0b0000000#7)
  let w__1204 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1204 49 49 0#1)
  let w__1205 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1205 48 48 0#1)
  let w__1206 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1206 47 (Bit 0#1))
  let w__1207 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1207 46 46 0#1)
  let w__1208 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1208 45 45 0#1)
  let w__1209 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1209 44 44 0#1)
  let w__1210 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1210 43 (Bit 0#1))
  let w__1211 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1211 42 42 0#1)
  let w__1212 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1212 41 41 0#1)
  let w__1213 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1213 40 38 0b000#3)
  let w__1214 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1214 37 37 0#1)
  let w__1215 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1215 36 36 0#1)
  let w__1216 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1216 35 35 0#1)
  let w__1217 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1217 34 (Bit 0#1))
  let w__1218 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1218 33 33 0#1)
  let w__1219 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1219 32 32 0#1)
  let w__1220 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1220 31 31 0#1)
  let w__1221 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1221 30 (Bit 0#1))
  let w__1222 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1222 29 29 0#1)
  let w__1223 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1223 28 28 0#1)
  let w__1224 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1224 27 27 0#1)
  let w__1225 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1225 26 26 0#1)
  let w__1226 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1226 25 25 0#1)
  let w__1227 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1227 24 24 0#1)
  let w__1228 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1228 23 23 0#1)
  let w__1229 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1229 22 (Bit 0#1))
  let w__1230 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1230 21 21 0#1)
  let w__1231 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1231 20 20 0#1)
  let w__1232 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1232 19 19 0#1)
  let w__1233 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1233 18 18 0#1)
  let w__1234 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1234 17 17 0#1)
  let w__1235 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1235 16 16 0#1)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1236 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1236 15 15 0#1))
  else
    (do
      let w__1237 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__1238 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1237 15 15 w__1238))
  let w__1239 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1239 14 14 0#1)
  let w__1240 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1240 13 13 0#1)
  if (((! cold) && (! (HaveEL EL3))) : Bool)
  then
    (do
      let w__1241 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1241 12 12 0#1))
  else
    (do
      let w__1242 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
      let w__1243 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1242 12 12 w__1243))
  let w__1244 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1244 11 11 0#1)
  let w__1245 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1245 10 10 0#1)
  let w__1246 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1246 9 (Bit 0#1))
  let w__1247 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1247 8 8 0#1)
  let w__1248 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (Sail.BitVec.updateSubrange w__1248 7 7 0#1)
  let w__1249 ← (( do readReg HDFGWTR_EL2 ) : SailM (BitVec 64) )
  writeReg HDFGWTR_EL2 (BitVec.update w__1249 6 (Bit 0#1))
  (pure true)


end ArmFull.Functions
