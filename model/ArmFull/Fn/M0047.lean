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

def _update_VSESR_EL2_Type_ExT (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_DISR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_IFSR32_EL2_Type_ExT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_IFSR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_VDFSR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_VDISR_EL2_Type_ExT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_VDISR_Type_ExT (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_VSESR_EL2_Type_ExT (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _get_DFSR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))


def _update_DFSR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 10 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((5 -i 1)))
        (Sail.Int.toNatChecked ((((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))))) 3 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((5 -i 1) -i ((10 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))))


def _update_DISR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 10 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((5 -i 1)))
        (Sail.Int.toNatChecked ((((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))))) 3 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((5 -i 1) -i ((10 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))))


def _update_IFSR32_EL2_Type_FS (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 10 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((5 -i 1)))
        (Sail.Int.toNatChecked ((((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))))) 3 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((5 -i 1) -i ((10 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))))


def _update_IFSR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 10 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((5 -i 1)))
        (Sail.Int.toNatChecked ((((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))))) 3 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((5 -i 1) -i ((10 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))))


def _update_ISR_EL1_Type_FS (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_PAR_Type_FS (v : (BitVec 64)) (x : (BitVec 6)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 6 6
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((6 -i 1)))
        (Sail.Int.toNatChecked ((((6 -i 1) -i ((6 -i 6) +i 1)) +i 1))))) 5 1
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((6 -i 1) -i ((6 -i 6) +i 1))))
      (Sail.Int.toNatChecked (((((6 -i 1) -i ((6 -i 6) +i 1)) -i ((5 -i 1) +i 1)) +i 1)))))


def _update_VDISR_EL2_Type_FS (v : (BitVec 64)) (x : (BitVec 5)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 10 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((5 -i 1)))
        (Sail.Int.toNatChecked ((((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))))) 3 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((5 -i 1) -i ((10 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))))


def _update_VDISR_Type_FS (v : (BitVec 32)) (x : (BitVec 5)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange
    (Sail.BitVec.updateSubrange v 10 10
      (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked ((5 -i 1)))
        (Sail.Int.toNatChecked ((((5 -i 1) -i ((10 -i 10) +i 1)) +i 1))))) 3 0
    (Sail.BitVec.extractLsb x (Sail.Int.toNatChecked (((5 -i 1) -i ((10 -i 10) +i 1))))
      (Sail.Int.toNatChecked (((((5 -i 1) -i ((10 -i 10) +i 1)) -i ((3 -i 0) +i 1)) +i 1)))))


def _get_DISR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))


def _get_IFSR32_EL2_Type_FS (v : (BitVec 64)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))


def _get_IFSR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))


def _get_ISR_EL1_Type_FS (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_PAR_Type_FS (v : (BitVec 64)) : (BitVec 6) :=
  ((Sail.BitVec.extractLsb v 6 6) +++ (Sail.BitVec.extractLsb v 5 1))


def _get_VDISR_EL2_Type_FS (v : (BitVec 64)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))


def _get_VDISR_Type_FS (v : (BitVec 32)) : (BitVec 5) :=
  ((Sail.BitVec.extractLsb v 10 10) +++ (Sail.BitVec.extractLsb v 3 0))


def _get_DFSR_Type_FnV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_DFSR_Type_FnV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_EDHSR_Type_FnV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 10 x)


def _update_IFSR32_EL2_Type_FnV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_IFSR_Type_FnV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_EDHSR_Type_FnV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 10 10)


def _get_IFSR32_EL2_Type_FnV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_IFSR_Type_FnV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_DFSR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _update_DFSR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_DISR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_IFSR32_EL2_Type_LPAE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_IFSR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_PAR_Type_LPAE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_VDISR_EL2_Type_LPAE (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _update_VDISR_Type_LPAE (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 9 9 x)


def _get_DISR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_IFSR32_EL2_Type_LPAE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_IFSR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_PAR_Type_LPAE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _get_VDISR_EL2_Type_LPAE (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_VDISR_Type_LPAE (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 9 9)


def _get_DFSR_Type_WnR (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 11 11)


def _update_DFSR_Type_WnR (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 11 11 x)


def _update_EDHSR_Type_WnR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 6 6 x)


def _get_EDHSR_Type_WnR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 6 6)


def DFSR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DFSR_Type := value_name
  let w__0 ← (( do readReg ESR_EL1 ) : SailM (BitVec 64) )
  writeReg ESR_EL1 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _DFSR_NS r


def undefined_IFSR32_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_IFSR32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def undefined_IFSR_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_IFSR_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def IFSR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : IFSR_Type := value_name
  let w__0 ← (( do readReg IFSR32_EL2 ) : SailM (BitVec 64) )
  writeReg IFSR32_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _IFSR_NS r


def undefined_DBGDSCRext_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGDSCRext_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def _get_DBGDSCRext_Type_MDBGen (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _update_DBGDSCRext_Type_MDBGen (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _update_DBGDSCRint_Type_MDBGen (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 15 15 x)


def _get_DBGDSCRint_Type_MDBGen (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 15 15)


def _get_DBGDSCRext_Type_MOE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 5 2)


def _update_DBGDSCRext_Type_MOE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 2 x)


def _update_DBGDSCRint_Type_MOE (v : (BitVec 32)) (x : (BitVec 4)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 5 2 x)


def _get_DBGDSCRint_Type_MOE (v : (BitVec 32)) : (BitVec 4) :=
  (Sail.BitVec.extractLsb v 5 2)


def _get_DBGDSCRext_Type_SPIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _update_DBGDSCRext_Type_SPIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _update_DBGDSCRint_Type_SPIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_DBGDSCRint_Type_SPIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_DBGDSCRext_Type_SPNIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _update_DBGDSCRext_Type_SPNIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _update_DBGDSCRint_Type_SPNIDdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 17 17 x)


def _get_DBGDSCRint_Type_SPNIDdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 17 17)


def _get_DBGDSCRext_Type_UDCCdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def _update_DBGDSCRext_Type_UDCCdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _update_DBGDSCRint_Type_UDCCdis (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 12 12 x)


def _get_DBGDSCRint_Type_UDCCdis (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 12 12)


def undefined_DBGDSCRint_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_DBGDSCRint_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def undefined_HCR2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_HCR2_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def HCR2_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HCR2 ) : SailM HCR2_Type )
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def IsDebugException (fault : FaultRecord) : SailM Bool := do
  ArmFull.assert (bne fault.statuscode Fault_None) "sail-arm/v8_base.sail:14522.41-14522.42"
  (pure ((BEq.beq fault.statuscode Fault_Debug)))


def IFAR_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : IFAR_Type := value_name
  let w__0 ← (( do readReg FAR_EL1 ) : SailM (BitVec 64) )
  writeReg FAR_EL1 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32))
  writeReg _IFAR_NS r


def HIFAR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _HIFAR ) : SailM HIFAR_Type )
  let w__0 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 32 32)) : (BitVec 32))
  (pure (r))


def LS64InstructionSyndrome (_ : Unit) : SailM ((BitVec 24) × (BitVec 11)) := do
  let w__0 ← (( do (undefined_bitvector_at (← occLabel 861) 24) ) : SailM (BitVec 24) )
  let w__1 ← (( do (undefined_bitvector_at (← occLabel 862) 11) ) : SailM (BitVec 11) )
  (pure (((w__0, w__1) : ((BitVec 24) × (BitVec 11)))))


def undefined_SCTLR2_EL1_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SCTLR2_EL1_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SCTLR2_EL1_Type_EnADERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_SCTLR2_EL1_Type_EnADERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_SCTLR2_EL2_Type_EnADERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_SCTLR2_EL3_Type_EnADERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_SCTLR2_EL2_Type_EnADERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_SCTLR2_EL3_Type_EnADERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_SCTLR2_EL1_Type_EnANERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_SCTLR2_EL1_Type_EnANERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_SCTLR2_EL2_Type_EnANERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_SCTLR2_EL3_Type_EnANERR (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_SCTLR2_EL2_Type_EnANERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_SCTLR2_EL3_Type_EnANERR (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def undefined_SCTLR2_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_SCTLR2_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_SCTLR2_EL2_Type_EMEC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_SCTLR2_EL2_Type_EMEC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_SCTLR2_EL3_Type_EMEC (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_SCTLR2_EL3_Type_EMEC (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def take_exception (fault : (Option FaultRecord)) : SailM Unit := do
  (sail_take_exception fault)


def HCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : HCR_Type := value_name
  let w__0 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  writeReg HCR_EL2 (Sail.BitVec.updateSubrange w__0 31 0 (BitVec.slice r 0 32))
  writeReg _HCR r


def undefined_FPEXC32_EL2_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 64) := do
  (undefined_bitvector_at (ℓ.child 0) 64)


def Mk_FPEXC32_EL2_Type (v : (BitVec 64)) : (BitVec 64) :=
  v


def _get_FPEXC32_EL2_Type_DEX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _update_FPEXC32_EL2_Type_DEX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _update_FPEXC_Type_DEX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 29 29 x)


def _get_FPEXC_Type_DEX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 29 29)


def _get_FPEXC32_EL2_Type_DZF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _update_FPEXC32_EL2_Type_DZF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _update_FPEXC_Type_DZF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 1 1 x)


def _get_FPEXC_Type_DZF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 1 1)


def _get_FPEXC32_EL2_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _update_FPEXC32_EL2_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_AMUSERENR_EL0_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_AMUSERENR_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_CNTCR_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_FPEXC_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 30 30 x)


def _update_LORC_EL1_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PMPCSCTL_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PMUSERENR_EL0_Type_EN (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_PMUSERENR_Type_EN (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_AMUSERENR_EL0_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_AMUSERENR_Type_EN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_CNTCR_Type_EN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_FPEXC_Type_EN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 30 30)


def _get_LORC_EL1_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMPCSCTL_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMUSERENR_EL0_Type_EN (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_PMUSERENR_Type_EN (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_FPEXC32_EL2_Type_EX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _update_FPEXC32_EL2_Type_EX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_FPEXC_Type_EX (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 31 31 x)


def _update_PMCFGR_Type_EX (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 16 16 x)


def _get_FPEXC_Type_EX (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 31 31)


def _get_PMCFGR_Type_EX (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 16 16)


def _get_FPEXC32_EL2_Type_FP2V (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _update_FPEXC32_EL2_Type_FP2V (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _update_FPEXC_Type_FP2V (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 28 28 x)


def _get_FPEXC_Type_FP2V (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 28 28)


def _get_FPEXC32_EL2_Type_IDF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _update_FPEXC32_EL2_Type_IDF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _update_FPEXC_Type_IDF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 7 7 x)


def _get_FPEXC_Type_IDF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 7 7)


def _get_FPEXC32_EL2_Type_IOF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _update_FPEXC32_EL2_Type_IOF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _update_FPEXC_Type_IOF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 0 0 x)


def _get_FPEXC_Type_IOF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 0 0)


def _get_FPEXC32_EL2_Type_IXF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _update_FPEXC32_EL2_Type_IXF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _update_FPEXC_Type_IXF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 4 4 x)


def _get_FPEXC_Type_IXF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 4 4)


def _get_FPEXC32_EL2_Type_OFF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _update_FPEXC32_EL2_Type_OFF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _update_FPEXC_Type_OFF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 2 2 x)


def _get_FPEXC_Type_OFF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 2 2)


def _get_FPEXC32_EL2_Type_TFV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _update_FPEXC32_EL2_Type_TFV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _update_FPEXC_Type_TFV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 26 26 x)


def _get_FPEXC_Type_TFV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 26 26)


def _get_FPEXC32_EL2_Type_UFF (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _update_FPEXC32_EL2_Type_UFF (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _update_FPEXC_Type_UFF (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 3 3 x)


def _get_FPEXC_Type_UFF (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 3 3)


def _get_FPEXC32_EL2_Type_VECITR (v : (BitVec 64)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _update_FPEXC32_EL2_Type_VECITR (v : (BitVec 64)) (x : (BitVec 3)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _update_FPEXC_Type_VECITR (v : (BitVec 32)) (x : (BitVec 3)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 10 8 x)


def _get_FPEXC_Type_VECITR (v : (BitVec 32)) : (BitVec 3) :=
  (Sail.BitVec.extractLsb v 10 8)


def _get_FPEXC32_EL2_Type_VV (v : (BitVec 64)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def _update_FPEXC32_EL2_Type_VV (v : (BitVec 64)) (x : (BitVec 1)) : (BitVec 64) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _update_FPEXC_Type_VV (v : (BitVec 32)) (x : (BitVec 1)) : (BitVec 32) :=
  (Sail.BitVec.updateSubrange v 27 27 x)


def _get_FPEXC_Type_VV (v : (BitVec 32)) : (BitVec 1) :=
  (Sail.BitVec.extractLsb v 27 27)


def undefined_FPEXC_Type (ℓ : ChoiceLabel) (_ : Unit) : SailM (BitVec 32) := do
  (undefined_bitvector_at (ℓ.child 0) 32)


def Mk_FPEXC_Type (v : (BitVec 32)) : (BitVec 32) :=
  v


def FPEXC_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _FPEXC ) : SailM FPEXC_Type )
  let w__0 ← (( do readReg FPEXC32_EL2 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
  (pure (r))


end ArmFull.Functions
