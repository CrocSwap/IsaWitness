import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork

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

def _update_SCR_EL3_Type_EEL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_SCR_EL3_Type_EnAS0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 36 36)


def _update_SCR_EL3_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 36 36 x)


def _update_HCRX_EL2_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_SCTLR_EL1_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _update_SCTLR_EL2_Type_EnAS0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _get_HCRX_EL2_Type_EnAS0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_SCTLR_EL1_Type_EnAS0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def _get_SCTLR_EL2_Type_EnAS0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def _get_SCR_EL3_Type_EnIDCP128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def _update_SCR_EL3_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _update_HCRX_EL2_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 21 x)


def _update_SCTLR2_EL1_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _update_SCTLR2_EL2_Type_EnIDCP128 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_HCRX_EL2_Type_EnIDCP128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 21 21)


def _get_SCTLR2_EL1_Type_EnIDCP128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SCTLR2_EL2_Type_EnIDCP128 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _get_SCR_EL3_Type_EnTP2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 41 41)


def _update_SCR_EL3_Type_EnTP2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 41 41 x)


def _update_SCTLR_EL1_Type_EnTP2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _update_SCTLR_EL2_Type_EnTP2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_SCTLR_EL1_Type_EnTP2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _get_SCTLR_EL2_Type_EnTP2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _get_SCR_EL3_Type_FGTEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_SCR_EL3_Type_FGTEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_SCR_EL3_Type_FGTEn2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _update_SCR_EL3_Type_FGTEn2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _get_SCR_EL3_Type_GCSEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 39 39)


def _update_SCR_EL3_Type_GCSEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 39 x)


def _update_HCRX_EL2_Type_GCSEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 22 22 x)


def _get_HCRX_EL2_Type_GCSEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 22 22)


def _get_SCR_EL3_Type_HXEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 38 38)


def _update_SCR_EL3_Type_HXEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 38 38 x)


def _get_SCR_EL3_Type_MECEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)


def _update_SCR_EL3_Type_MECEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)


def _get_SCR_EL3_Type_NMEA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_SCR_EL3_Type_NMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _update_SCTLR2_EL1_Type_NMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_SCTLR2_EL2_Type_NMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_SCTLR2_EL1_Type_NMEA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_SCTLR2_EL2_Type_NMEA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_SCR_EL3_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _update_SCR_EL3_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _update_EDSCR_Type_NSE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_MFAR_EL3_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _update_PAR_EL1_Type_NSE (v : (BitVec 128)) (x : (BitVec 1)) : (BitVec 128) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_PFAR_EL1_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _update_PFAR_EL2_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def _update_PMPCSR_Type_NSE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _get_EDSCR_Type_NSE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_MFAR_EL3_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _get_PAR_EL1_Type_NSE (v : (BitVec 128)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_PFAR_EL1_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _get_PFAR_EL2_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _get_PMPCSR_Type_NSE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _get_SCR_EL3_Type_PFAREn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 53 53)


def _update_SCR_EL3_Type_PFAREn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 53 53 x)


def _get_SCR_EL3_Type_PIEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 45 45)


def _update_SCR_EL3_Type_PIEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 45 45 x)


def _get_SCR_EL3_Type_RCWMASKEn (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 42 42)


def _update_SCR_EL3_Type_RCWMASKEn (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 42 42 x)


def _get_SCR_EL3_Type_SCTLR2En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 44 44)


def _update_SCR_EL3_Type_SCTLR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 44 44 x)


def _update_HCRX_EL2_Type_SCTLR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_HCRX_EL2_Type_SCTLR2En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_SCR_EL3_Type_TCR2En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 43 43)


def _update_SCR_EL3_Type_TCR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 43 43 x)


def _update_HCRX_EL2_Type_TCR2En (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_HCRX_EL2_Type_TCR2En (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _get_SCR_EL3_Type_TMEA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)


def _update_SCR_EL3_Type_TMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)


def _update_HCRX_EL2_Type_TMEA (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 19 x)


def _get_HCRX_EL2_Type_TMEA (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


def _get_SCR_EL3_Type_TRNDR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 40 40)


def _update_SCR_EL3_Type_TRNDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 40 40 x)


def _get_SCR_EL3_Type_TWERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _update_SCR_EL3_Type_TWERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def HaveEL (el : (BitVec 2)) : Bool :=
  true


def undefined_SCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_SCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HasArchVersion (version : ArchVersion) : Bool :=
  true


def undefined_FPSCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_FPSCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_ERRnFR_ElemType (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_ERRnFR_ElemType (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_ERRnFR_ElemType_CE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 54 53)


def _update_ERRnFR_ElemType_CE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 53 x)


def _get_ERRnFR_ElemType_CEC (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 14 12)


def _update_ERRnFR_ElemType_CEC (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 12 x)


def _get_ERRnFR_ElemType_CEO (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 19 18)


def _update_ERRnFR_ElemType_CEO (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 18 x)


def _get_ERRnFR_ElemType_CFI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 11 10)


def _update_ERRnFR_ElemType_CFI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 10 x)


def _get_ERRnFR_ElemType_CI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 23 22)


def _update_ERRnFR_ElemType_CI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 22 x)


def _get_ERRnFR_ElemType_DE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _update_ERRnFR_ElemType_DE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _get_ERRnFR_ElemType_DUI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 17 16)


def _update_ERRnFR_ElemType_DUI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 16 x)


def _get_ERRnFR_ElemType_ED (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 1 0)


def _update_ERRnFR_ElemType_ED (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 0 x)


def _get_ERRnFR_ElemType_FI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 7 6)


def _update_ERRnFR_ElemType_FI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 6 x)


def _get_ERRnFR_ElemType_FRX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_ERRnFR_ElemType_FRX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _get_ERRnFR_ElemType_INJ (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 21 20)


def _update_ERRnFR_ElemType_INJ (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 21 20 x)


def _get_ERRnFR_ElemType_RP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_ERRnFR_ElemType_RP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_ERRnFR_ElemType_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 25 24)


def _update_ERRnFR_ElemType_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 25 24 x)


def _update_BRBCR_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)


def _update_BRBCR_EL2_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)


def _update_BRBTS_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 0 x)


def _update_HTRFCR_Type_TS (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 5 x)


def _update_ID_AA64ISAR0_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 52 x)


def _update_PMSCR_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_PMSCR_EL2_Type_TS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _update_TRFCR_EL1_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)


def _update_TRFCR_EL2_Type_TS (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 5 x)


def _update_TRFCR_Type_TS (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 6 5 x)


def _get_BRBCR_EL1_Type_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)


def _get_BRBCR_EL2_Type_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)


def _get_BRBTS_EL1_Type_TS (v : (BitVec 64)) : (BitVec 64) :=
  (Sail.BitVec.extractLsb v 63 0)


def _get_HTRFCR_Type_TS (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)


def _get_ID_AA64ISAR0_EL1_Type_TS (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 55 52)


def _get_PMSCR_EL1_Type_TS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_PMSCR_EL2_Type_TS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _get_TRFCR_EL1_Type_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)


def _get_TRFCR_EL2_Type_TS (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)


def _get_TRFCR_Type_TS (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 6 5)


def _get_ERRnFR_ElemType_UC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)


def _update_ERRnFR_ElemType_UC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)


def _get_ERRnFR_ElemType_UE (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 9 8)


def _update_ERRnFR_ElemType_UE (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 8 x)


def _get_ERRnFR_ElemType_UEO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 51 51)


def _update_ERRnFR_ElemType_UEO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 51 51 x)


def _get_ERRnFR_ElemType_UER (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)


def _update_ERRnFR_ElemType_UER (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)


def _get_ERRnFR_ElemType_UEU (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)


def _update_ERRnFR_ElemType_UEU (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)


def _get_ERRnFR_ElemType_UI (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 5 4)


def _update_ERRnFR_ElemType_UI (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 4 x)


def undefined_CTR_EL0_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_CTR_EL0_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_CTR_EL0_Type_CWG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _update_CTR_EL0_Type_CWG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _update_CTR_Type_CWG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 24 x)


def _get_CTR_Type_CWG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 27 24)


def _get_CTR_EL0_Type_DIC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_CTR_EL0_Type_DIC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_CTR_Type_DIC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_CTR_Type_DIC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_CTR_EL0_Type_DminLine (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _update_CTR_EL0_Type_DminLine (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _update_CTR_Type_DminLine (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 19 16 x)


def _get_CTR_Type_DminLine (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 19 16)


def _get_CTR_EL0_Type_ERG (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _update_CTR_EL0_Type_ERG (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _update_CTR_Type_ERG (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 20 x)


def _get_CTR_Type_ERG (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 23 20)


def _get_CTR_EL0_Type_IminLine (v : (BitVec 64)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _update_CTR_EL0_Type_IminLine (v : (BitVec 64)) (x : (BitVec 4)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _update_CTR_Type_IminLine (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 0 x)


def _get_CTR_Type_IminLine (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 3 0)


def _get_CTR_EL0_Type_L1Ip (v : (BitVec 64)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _update_CTR_EL0_Type_L1Ip (v : (BitVec 64)) (x : (BitVec 2)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _update_CTR_Type_L1Ip (v : (BitVec 32)) (x : (BitVec 2)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 14 x)


def _get_CTR_Type_L1Ip (v : (BitVec 32)) : (BitVec 2) :=
  (Sail.BitVec.extractLsb v 15 14)


def _get_CTR_EL0_Type_TminLine (v : (BitVec 64)) : (BitVec 6) :=
  (Sail.BitVec.extractLsb v 37 32)


def _update_CTR_EL0_Type_TminLine (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 37 32 x)


def undefined_HDCR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_HDCR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_HDCR_Type_HCCD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _update_HDCR_Type_HCCD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _update_MDCR_EL2_Type_HCCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 23 23 x)


def _get_MDCR_EL2_Type_HCCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 23 23)


def _get_HDCR_Type_HLP (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_HDCR_Type_HLP (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_MDCR_EL2_Type_HLP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_MDCR_EL2_Type_HLP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_HDCR_Type_HPMD (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_HDCR_Type_HPMD (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_MDCR_EL2_Type_HPMD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_MDCR_EL2_Type_HPMD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _get_HDCR_Type_HPME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_HDCR_Type_HPME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_MDCR_EL2_Type_HPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_MDCR_EL2_Type_HPME (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_HDCR_Type_HPMFZO (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_HDCR_Type_HPMFZO (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_MDCR_EL2_Type_HPMFZO (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_MDCR_EL2_Type_HPMFZO (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_HDCR_Type_HPMN (v : (BitVec 32)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _update_HDCR_Type_HPMN (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _update_MDCR_EL2_Type_HPMN (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 0 x)


def _get_MDCR_EL2_Type_HPMN (v : (BitVec 64)) : (BitVec 5) :=
  (Sail.BitVec.extractLsb v 4 0)


def _get_HDCR_Type_MTPME (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_HDCR_Type_MTPME (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_MDCR_EL2_Type_MTPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


end ArmFull.Functions
