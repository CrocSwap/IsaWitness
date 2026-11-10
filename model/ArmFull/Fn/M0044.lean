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

def _update_EDECCR_Type_SR2 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_EDECCR_Type_SR3 (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_EDECCR_Type_SR3 (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def undefined_OSECCR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_OSECCR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_OSECCR_EL1_Type_EDECCR (v : (BitVec 64)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def _update_OSECCR_EL1_Type_EDECCR (v : (BitVec 64)) (x : (BitVec 32)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _update_DBGOSECCR_Type_EDECCR (v : (BitVec 32)) (x : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 0 x)


def _get_DBGOSECCR_Type_EDECCR (v : (BitVec 32)) : (BitVec 32) :=
  (Sail.BitVec.extractLsb v 31 0)


def EDECCR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _EDECCR ) : SailM EDECCR_Type )
  let w__0 ← (( do readReg OSECCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def undefined_EDESR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_EDESR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_EDESR_Type_OSUC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_EDESR_Type_OSUC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_EDESR_Type_RC (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_EDESR_Type_RC (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def VBAR_NS_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _VBAR_NS ) : SailM VBAR_Type )
  let w__0 ← (( do readReg VBAR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


def FIQPending (_ : Unit) : (Bool × Bool) :=
  (false, false)


def IsPhysicalSErrorPending (_ : Unit) : Bool :=
  false


def ThisInstr (_ : Unit) : SailM (BitVec 32) := do
  readReg __ThisInstr


def AArch32_CurrentCond (_ : Unit) : SailM (BitVec 4) := do
  readReg __currentCond


def ClearEventRegister (_ : Unit) : SailM Unit := do
  writeReg EventRegister 0#1


def IsEventRegisterSet (_ : Unit) : SailM Bool := do
  let w__0 ← (( do readReg EventRegister ) : SailM (BitVec 1) )
  (pure ((w__0 == 1#1)))


def EnterLowPowerState (_ : Unit) : Unit :=
  ()


def SendEventLocal (_ : Unit) : SailM Unit := do
  writeReg EventRegister 1#1


def undefined_GCSCRE0_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_GCSCRE0_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_GCSCRE0_EL1_Type_nTR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_GCSCRE0_EL1_Type_nTR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def undefined_HCRX_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_HCRX_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_HCRX_EL2_Type_EnSDERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 20 20)


def _update_HCRX_EL2_Type_EnSDERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 20 x)


def _get_HCRX_EL2_Type_EnSNERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_HCRX_EL2_Type_EnSNERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_HCRX_EL2_Type_FGTnXS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_HCRX_EL2_Type_FGTnXS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_HCRX_EL2_Type_FnXS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_HCRX_EL2_Type_FnXS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_HCRX_EL2_Type_MCE2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_HCRX_EL2_Type_MCE2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_HCRX_EL2_Type_SMPME (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 5 5)


def _update_HCRX_EL2_Type_SMPME (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 5 5 x)


def _get_HCRX_EL2_Type_TALLINT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def _update_HCRX_EL2_Type_TALLINT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_HCRX_EL2_Type_VFNMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_HCRX_EL2_Type_VFNMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_HCRX_EL2_Type_VINMI (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_HCRX_EL2_Type_VINMI (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def TAG_GRANULE : Nat := 16


def IsDataAccess (acctype : AccessType) : Bool :=
  (! ((BEq.beq acctype AccessType_IFETCH) || ((BEq.beq acctype AccessType_TTW) || ((BEq.beq acctype
            AccessType_DC) || ((BEq.beq acctype AccessType_IC) || (BEq.beq acctype AccessType_AT))))))


def undefined_MPAM2_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAM2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAM2_EL2_Type_ALTSP_EL2 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def _update_MPAM2_EL2_Type_ALTSP_EL2 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _get_MPAM2_EL2_Type_ALTSP_FRCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)


def _update_MPAM2_EL2_Type_ALTSP_FRCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)


def _update_MPAM1_EL1_Type_ALTSP_FRCD (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 54 54 x)


def _get_MPAM1_EL1_Type_ALTSP_FRCD (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 54 54)


def _get_MPAM2_EL2_Type_ALTSP_HFC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)


def _update_MPAM2_EL2_Type_ALTSP_HFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)


def _update_MPAM3_EL3_Type_ALTSP_HFC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 56 56 x)


def _get_MPAM3_EL3_Type_ALTSP_HFC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 56 56)


def _get_MPAM2_EL2_Type_EnMPAMSM (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 50 50)


def _update_MPAM2_EL2_Type_EnMPAMSM (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 50 50 x)


def _get_MPAM2_EL2_Type_MPAMEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _update_MPAM2_EL2_Type_MPAMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_MPAM1_EL1_Type_MPAMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _update_MPAM3_EL3_Type_MPAMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 63 x)


def _get_MPAM1_EL1_Type_MPAMEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_MPAM3_EL3_Type_MPAMEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 63 63)


def _get_MPAM2_EL2_Type_PARTID_D (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAM2_EL2_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _update_MPAM0_EL1_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _update_MPAM1_EL1_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _update_MPAM3_EL3_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _update_MPAMSM_EL1_Type_PARTID_D (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAM0_EL1_Type_PARTID_D (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _get_MPAM1_EL1_Type_PARTID_D (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _get_MPAM3_EL3_Type_PARTID_D (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _get_MPAMSM_EL1_Type_PARTID_D (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _get_MPAM2_EL2_Type_PARTID_I (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAM2_EL2_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_MPAM0_EL1_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_MPAM1_EL1_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _update_MPAM3_EL3_Type_PARTID_I (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAM0_EL1_Type_PARTID_I (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_MPAM1_EL1_Type_PARTID_I (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_MPAM3_EL3_Type_PARTID_I (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _get_MPAM2_EL2_Type_PMG_D (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)


def _update_MPAM2_EL2_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)


def _update_MPAM0_EL1_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)


def _update_MPAM1_EL1_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)


def _update_MPAM3_EL3_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)


def _update_MPAMSM_EL1_Type_PMG_D (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 40 x)


def _get_MPAM0_EL1_Type_PMG_D (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)


def _get_MPAM1_EL1_Type_PMG_D (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)


def _get_MPAM3_EL3_Type_PMG_D (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)


def _get_MPAMSM_EL1_Type_PMG_D (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 47 40)


def _get_MPAM2_EL2_Type_PMG_I (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _update_MPAM2_EL2_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_MPAM0_EL1_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_MPAM1_EL1_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _update_MPAM3_EL3_Type_PMG_I (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _get_MPAM0_EL1_Type_PMG_I (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_MPAM1_EL1_Type_PMG_I (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_MPAM3_EL3_Type_PMG_I (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _get_MPAM2_EL2_Type_TIDR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _update_MPAM2_EL2_Type_TIDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _get_MPAM2_EL2_Type_TRAPMPAM0EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 49 49)


def _update_MPAM2_EL2_Type_TRAPMPAM0EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 49 49 x)


def _get_MPAM2_EL2_Type_TRAPMPAM1EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 48 48)


def _update_MPAM2_EL2_Type_TRAPMPAM1EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 48 48 x)


def undefined_MPAM3_EL3_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAM3_EL3_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAM3_EL3_Type_ALTSP_EL3 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 55 55)


def _update_MPAM3_EL3_Type_ALTSP_EL3 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 55 55 x)


def _get_MPAM3_EL3_Type_ALTSP_HEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)


def _update_MPAM3_EL3_Type_ALTSP_HEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)


def _get_MPAM3_EL3_Type_FORCE_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_MPAM3_EL3_Type_FORCE_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_MPAM3_EL3_Type_RT_ALTSP_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 52 52)


def _update_MPAM3_EL3_Type_RT_ALTSP_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 52 52 x)


def _get_MPAM3_EL3_Type_SDEFLT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _update_MPAM3_EL3_Type_SDEFLT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _get_MPAM3_EL3_Type_TRAPLOWER (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 62 62)


def _update_MPAM3_EL3_Type_TRAPLOWER (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 62 62 x)


def undefined_MPAM1_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAM1_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAM1_EL1_Type_FORCED_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_MPAM1_EL1_Type_FORCED_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def undefined_MPAMIDR_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMIDR_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMIDR_EL1_Type_HAS_ALTSP (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 57 57)


def _update_MPAMIDR_EL1_Type_HAS_ALTSP (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 57 57 x)


def _get_MPAMIDR_EL1_Type_HAS_FORCE_NS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 60 60)


def _update_MPAMIDR_EL1_Type_HAS_FORCE_NS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 60 60 x)


def _get_MPAMIDR_EL1_Type_HAS_HCR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_MPAMIDR_EL1_Type_HAS_HCR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_MPAMIDR_EL1_Type_HAS_SDEFLT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 61 61)


def _update_MPAMIDR_EL1_Type_HAS_SDEFLT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 61 61 x)


def _get_MPAMIDR_EL1_Type_HAS_TIDR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 58 58)


def _update_MPAMIDR_EL1_Type_HAS_TIDR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 58 58 x)


def _get_MPAMIDR_EL1_Type_PARTID_MAX (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMIDR_EL1_Type_PARTID_MAX (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMIDR_EL1_Type_PMG_MAX (v : (BitVec 64)) : (BitVec 8) :=
  (Sail.BitVec.extractLsb v 39 32)


def _update_MPAMIDR_EL1_Type_PMG_MAX (v : (BitVec 64)) (x : (BitVec 8)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 39 32 x)


def _get_MPAMIDR_EL1_Type_SP4 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 59 59)


def _update_MPAMIDR_EL1_Type_SP4 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 59 59 x)


def _get_MPAMIDR_EL1_Type_VPMR_MAX (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 20 18)


def _update_MPAMIDR_EL1_Type_VPMR_MAX (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 20 18 x)


def PARTIDspaceFromSS (security : SecurityState) : PARTIDspaceType :=
  match security with
  | .SS_NonSecure => PIdSpace_NonSecure
  | .SS_Root => PIdSpace_Root
  | .SS_Realm => PIdSpace_Realm
  | .SS_Secure => PIdSpace_Secure


def undefined_MPAMHCR_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMHCR_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMHCR_EL2_Type_EL0_VPMEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_MPAMHCR_EL2_Type_EL0_VPMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_MPAMHCR_EL2_Type_EL1_VPMEN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_MPAMHCR_EL2_Type_EL1_VPMEN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_MPAMHCR_EL2_Type_GSTAPP_PLK (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 8 8)


def _update_MPAMHCR_EL2_Type_GSTAPP_PLK (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 8 8 x)


def _get_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_MPAMHCR_EL2_Type_TRAP_MPAMIDR_EL1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def undefined_MPAMVPM0_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPM0_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPM0_EL2_Type_PhyPARTID0 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 15 0)


def _update_MPAMVPM0_EL2_Type_PhyPARTID0 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 0 x)


def _get_MPAMVPM0_EL2_Type_PhyPARTID1 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 31 16)


def _update_MPAMVPM0_EL2_Type_PhyPARTID1 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 16 x)


def _get_MPAMVPM0_EL2_Type_PhyPARTID2 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 47 32)


def _update_MPAMVPM0_EL2_Type_PhyPARTID2 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 47 32 x)


def _get_MPAMVPM0_EL2_Type_PhyPARTID3 (v : (BitVec 64)) : (BitVec 16) :=
  (Sail.BitVec.extractLsb v 63 48)


def _update_MPAMVPM0_EL2_Type_PhyPARTID3 (v : (BitVec 64)) (x : (BitVec 16)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 63 48 x)


def undefined_MPAMVPMV_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_MPAMVPMV_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_MPAMVPMV_EL2_Type_VPM_V0 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_MPAMVPMV_EL2_Type_VPM_V0 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_MPAMVPMV_EL2_Type_VPM_V1 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_MPAMVPMV_EL2_Type_VPM_V1 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_MPAMVPMV_EL2_Type_VPM_V10 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _update_MPAMVPMV_EL2_Type_VPM_V10 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _get_MPAMVPMV_EL2_Type_VPM_V11 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_MPAMVPMV_EL2_Type_VPM_V11 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _get_MPAMVPMV_EL2_Type_VPM_V12 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_MPAMVPMV_EL2_Type_VPM_V12 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_MPAMVPMV_EL2_Type_VPM_V13 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 13 13)


def _update_MPAMVPMV_EL2_Type_VPM_V13 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 13 13 x)


def _get_MPAMVPMV_EL2_Type_VPM_V14 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 14 14)


def _update_MPAMVPMV_EL2_Type_VPM_V14 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 14 14 x)


def _get_MPAMVPMV_EL2_Type_VPM_V15 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_MPAMVPMV_EL2_Type_VPM_V15 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_MPAMVPMV_EL2_Type_VPM_V16 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_MPAMVPMV_EL2_Type_VPM_V16 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_MPAMVPMV_EL2_Type_VPM_V17 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_MPAMVPMV_EL2_Type_VPM_V17 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_MPAMVPMV_EL2_Type_VPM_V18 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 18 18)


def _update_MPAMVPMV_EL2_Type_VPM_V18 (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 18 18 x)


def _get_MPAMVPMV_EL2_Type_VPM_V19 (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 19 19)


end ArmFull.Functions
