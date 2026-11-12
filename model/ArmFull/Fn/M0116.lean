import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048

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

def DFAR_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DFAR_Type := value_name
  let w__0 ← (( do (HDFAR_read ()) ) : SailM (BitVec 32) )
  (HDFAR_write (set_slice 32 w__0 0 (BitVec.slice r 0 32)))
  writeReg _DFAR_S r


def _set_DFSR_Type_AET (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_AET r v)


def _set_DISR_EL1_Type_AET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DISR_EL1_Type_AET r v)


def _set_VDFSR_Type_AET (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDFSR_Type_AET r v)


def _set_VDISR_EL2_Type_AET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_AET r v)


def _set_VDISR_Type_AET (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDISR_Type_AET r v)


def _set_VSESR_EL2_Type_AET (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSESR_EL2_Type_AET r v)


def _set_DFSR_Type_CM (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_CM r v)


def _set_EDHSR_Type_CM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_CM r v)


def _set_DFSR_Type_Domain (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_Domain r v)


def _set_DFSR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_ExT r v)


def _set_DISR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DISR_Type_ExT r v)


def _set_IFSR32_EL2_Type_ExT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_IFSR32_EL2_Type_ExT r v)


def _set_IFSR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_IFSR_Type_ExT r v)


def _set_VDFSR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDFSR_Type_ExT r v)


def _set_VDISR_EL2_Type_ExT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_ExT r v)


def _set_VDISR_Type_ExT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDISR_Type_ExT r v)


def _set_VSESR_EL2_Type_ExT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSESR_EL2_Type_ExT r v)


def _set_DFSR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_FS r v)


def _set_DISR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DISR_Type_FS r v)


def _set_IFSR32_EL2_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_IFSR32_EL2_Type_FS r v)


def _set_IFSR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_IFSR_Type_FS r v)


def _set_ISR_EL1_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ISR_EL1_Type_FS r v)


def _set_PAR_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 6)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_FS r v)


def _set_VDISR_EL2_Type_FS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_FS r v)


def _set_VDISR_Type_FS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDISR_Type_FS r v)


def _set_DFSR_Type_FnV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_FnV r v)


def _set_EDHSR_Type_FnV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_FnV r v)


def _set_IFSR32_EL2_Type_FnV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_IFSR32_EL2_Type_FnV r v)


def _set_IFSR_Type_FnV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_IFSR_Type_FnV r v)


def _set_DFSR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_LPAE r v)


def _set_DISR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DISR_Type_LPAE r v)


def _set_IFSR32_EL2_Type_LPAE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_IFSR32_EL2_Type_LPAE r v)


def _set_IFSR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_IFSR_Type_LPAE r v)


def _set_PAR_Type_LPAE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_LPAE r v)


def _set_VDISR_EL2_Type_LPAE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VDISR_EL2_Type_LPAE r v)


def _set_VDISR_Type_LPAE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VDISR_Type_LPAE r v)


def _set_DFSR_Type_WnR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DFSR_Type_WnR r v)


def _set_EDHSR_Type_WnR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_EDHSR_Type_WnR r v)


def _set_DBGDSCRext_Type_MDBGen (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_MDBGen r v)


def _set_DBGDSCRint_Type_MDBGen (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRint_Type_MDBGen r v)


def _set_DBGDSCRext_Type_MOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_MOE r v)


def _set_DBGDSCRint_Type_MOE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRint_Type_MOE r v)


def _set_DBGDSCRext_Type_SPIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_SPIDdis r v)


def _set_DBGDSCRint_Type_SPIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRint_Type_SPIDdis r v)


def _set_DBGDSCRext_Type_SPNIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_SPNIDdis r v)


def _set_DBGDSCRint_Type_SPNIDdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRint_Type_SPNIDdis r v)


def _set_DBGDSCRext_Type_UDCCdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRext_Type_UDCCdis r v)


def _set_DBGDSCRint_Type_UDCCdis (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGDSCRint_Type_UDCCdis r v)


def DBGDSCRint_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _DBGDSCRint ) : SailM DBGDSCRint_Type )
  let w__0 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 30 29 (BitVec.slice w__0 29 2)) : (BitVec 32))
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let r := ((BitVec.update r 15 (Bit (BitVec.slice w__1 15 1))) : (BitVec 32))
  let w__2 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let r := ((BitVec.update r 12 (Bit (BitVec.slice w__2 12 1))) : (BitVec 32))
  let w__3 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let r := ((Sail.BitVec.updateSubrange r 5 2 (BitVec.slice w__3 2 4)) : (BitVec 32))
  (pure (r))


def DBGDSCRint_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DBGDSCRint_Type := value_name
  let w__0 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
  writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__0 30 29 (BitVec.slice r 29 2))
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__1 15 (Bit (BitVec.slice r 15 1)))
  let w__2 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (BitVec.update w__2 12 (Bit (BitVec.slice r 12 1)))
  let w__3 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSCR_EL1 (Sail.BitVec.updateSubrange w__3 5 2 (BitVec.slice r 2 4))
  writeReg _DBGDSCRint r


def IFAR_S_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : IFAR_Type := value_name
  if ((HaveEL EL2) : Bool)
  then
    (do
      let w__0 ← (( do readReg FAR_EL2 ) : SailM (BitVec 64) )
      writeReg FAR_EL2 (Sail.BitVec.updateSubrange w__0 63 32 (BitVec.slice r 0 32)))
  else
    (do
      let w__1 ← (( do (HIFAR_read ()) ) : SailM (BitVec 32) )
      (HIFAR_write (set_slice 32 w__1 0 (BitVec.slice r 0 32))))
  writeReg _IFAR_S r


def AArch64_EncodeSyncErrorSyndrome (errorstate : ErrorState) : SailM (BitVec 2) := do
  match errorstate with
  | .ErrorState_UC => (pure (0b10#2))
  | .ErrorState_UEO => (pure (0b11#2))
  | .ErrorState_UER => (pure (0b00#2))
  | _ =>
    (do
      (Unreachable ())
      (undefined_bitvector_at (← occLabel 860) 2))


def FaultIsCorrected (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ReportErrorAsIMPDEF (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def ReportErrorAsUncategorized (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


def _set_SCTLR2_EL1_Type_EnADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_EnADERR r v)


def _set_SCTLR2_EL2_Type_EnADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EnADERR r v)


def _set_SCTLR2_EL3_Type_EnADERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_EnADERR r v)


def _set_SCTLR2_EL1_Type_EnANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL1_Type_EnANERR r v)


def _set_SCTLR2_EL2_Type_EnANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EnANERR r v)


def _set_SCTLR2_EL3_Type_EnANERR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_EnANERR r v)


def _set_SCTLR2_EL2_Type_EMEC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL2_Type_EMEC r v)


def _set_SCTLR2_EL3_Type_EMEC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR2_EL3_Type_EMEC r v)


def _set_FPEXC32_EL2_Type_DEX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_DEX r v)


def _set_FPEXC_Type_DEX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_DEX r v)


def _set_FPEXC32_EL2_Type_DZF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_DZF r v)


def _set_FPEXC_Type_DZF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_DZF r v)


def _set_FPEXC32_EL2_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_EN r v)


def _set_AMUSERENR_EL0_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMUSERENR_EL0_Type_EN r v)


def _set_AMUSERENR_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMUSERENR_Type_EN r v)


def _set_CNTCR_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTCR_Type_EN r v)


def _set_FPEXC_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_EN r v)


def _set_LORC_EL1_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_LORC_EL1_Type_EN r v)


def _set_PMPCSCTL_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMPCSCTL_Type_EN r v)


def _set_PMUSERENR_EL0_Type_EN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_EN r v)


def _set_PMUSERENR_Type_EN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMUSERENR_Type_EN r v)


def _set_FPEXC32_EL2_Type_EX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_EX r v)


def _set_FPEXC_Type_EX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_EX r v)


def _set_PMCFGR_Type_EX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_EX r v)


def _set_FPEXC32_EL2_Type_FP2V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_FP2V r v)


def _set_FPEXC_Type_FP2V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_FP2V r v)


def _set_FPEXC32_EL2_Type_IDF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_IDF r v)


def _set_FPEXC_Type_IDF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_IDF r v)


def _set_FPEXC32_EL2_Type_IOF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_IOF r v)


def _set_FPEXC_Type_IOF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_IOF r v)


def _set_FPEXC32_EL2_Type_IXF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_IXF r v)


def _set_FPEXC_Type_IXF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_IXF r v)


def _set_FPEXC32_EL2_Type_OFF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_OFF r v)


def _set_FPEXC_Type_OFF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_OFF r v)


def _set_FPEXC32_EL2_Type_TFV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_TFV r v)


def _set_FPEXC_Type_TFV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_TFV r v)


def _set_FPEXC32_EL2_Type_UFF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_UFF r v)


def _set_FPEXC_Type_UFF (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_UFF r v)


def _set_FPEXC32_EL2_Type_VECITR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_VECITR r v)


def _set_FPEXC_Type_VECITR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_VECITR r v)


def _set_FPEXC32_EL2_Type_VV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPEXC32_EL2_Type_VV r v)


def _set_FPEXC_Type_VV (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPEXC_Type_VV r v)


def FPSCR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : FPSCR_Type := value_name
  let w__0 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__0 31 27 (BitVec.slice r 27 5))
  let w__1 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (BitVec.update w__1 7 (Bit (BitVec.slice r 7 1)))
  let w__2 ← (( do readReg FPSR ) : SailM (BitVec 64) )
  writeReg FPSR (Sail.BitVec.updateSubrange w__2 4 0 (BitVec.slice r 0 5))
  let w__3 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__3 26 15 (BitVec.slice r 15 12))
  let w__4 ← (( do readReg FPCR ) : SailM (BitVec 64) )
  writeReg FPCR (Sail.BitVec.updateSubrange w__4 12 8 (BitVec.slice r 8 5))


def IsASEInstruction (_ : Unit) : SailM Bool := do
  (__UNKNOWN_boolean ())


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPZero (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:15627.38-15627.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (Sail.Int.toNatChecked E)) := (Sail.BitVec.castWidth (Zeros (n := E)))
  let frac : (BitVec (Sail.Int.toNatChecked (F : Int))) :=
    (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (F)))))
  let result : (BitVec (Sail.Int.toNatChecked (((1 : Int) +i (E : Int)) +i (F : Int)))) :=
    (Sail.BitVec.castWidth ((sign +++ exp) +++ frac))
  (pure ((Sail.BitVec.castWidth result)))


def FPDecodeRounding (rmode : (BitVec 2)) : SailM FPRounding := do
  match rmode with
  | 0b00 => (pure (FPRounding_TIEEVEN))
  | 0b01 => (pure (FPRounding_POSINF))
  | 0b10 => (pure (FPRounding_NEGINF))
  | 0b11 => (pure (FPRounding_ZERO))
  | _ =>
    (do
      (undefined_FPRounding (← occLabel 898) ()))


def FPDecodeRM (rm : (BitVec 2)) : SailM FPRounding := do
  let result ← (( do (undefined_FPRounding (← occLabel 972) ()) ) : SailM FPRounding )
  let result : FPRounding :=
    match rm with
    | 0b00 => FPRounding_TIEAWAY
    | 0b01 => FPRounding_TIEEVEN
    | 0b10 => FPRounding_POSINF
    | _ => FPRounding_NEGINF
  (pure (result))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPTwo (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:17017.38-17017.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (1 + ((Sail.Int.toNatChecked E) - 1))) :=
    (Sail.BitVec.castWidth (1#1 +++ (Zeros (n := (Sail.Int.toNatChecked ((E -i 1)))))))
  let frac : (BitVec (Sail.Int.toNatChecked (F : Int))) :=
    (Sail.BitVec.castWidth (Zeros (n := (Sail.Int.toNatChecked (F)))))
  let result : (BitVec (Sail.Int.toNatChecked (((1 : Int) +i ((1 : Int) +i ((E : Int) -i (1 : Int)))) +i (F : Int)))) :=
    (Sail.BitVec.castWidth ((sign +++ exp) +++ frac))
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def FPThree (sign : (BitVec 1)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:17825.38-17825.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := (N -i (E +i 1))
  let exp : (BitVec (1 + ((Sail.Int.toNatChecked E) - 1))) :=
    (Sail.BitVec.castWidth (1#1 +++ (Zeros (n := (Sail.Int.toNatChecked ((E -i 1)))))))
  let frac : (BitVec (Sail.Int.toNatChecked ((1 : Int) +i ((F : Int) -i (1 : Int))))) :=
    (Sail.BitVec.castWidth (1#1 +++ (Zeros (n := (Sail.Int.toNatChecked ((F -i 1)))))))
  let result : (BitVec (Sail.Int.toNatChecked (((1 : Int) +i ((1 : Int) +i ((E : Int) -i (1 : Int)))) +i ((1 : Int) +i ((F : Int) -i (1 : Int)))))) :=
    (Sail.BitVec.castWidth ((sign +++ exp) +++ frac))
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: N : Nat, List.elem N [16, 32, 64] -/
def VFPExpandImm (imm8 : (BitVec 8)) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert ((N == 16) || ((N == 32) || (N == 64))) "sail-arm/v8_base.sail:17939.38-17939.39"
  let E : Nat :=
    if ((N == 16) : Bool)
    then 5
    else
      (if ((N == 32) : Bool)
      then 8
      else 11)
  let F : Int := ((N -i E) -i 1)
  let sign : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 7)]))
  let exp : (BitVec (1 + ((Sail.Int.toNatChecked E) - 3) + 2)) :=
    (Sail.BitVec.castWidth (((Complement.complement
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)]))) +++ (BitVec.replicateBits
          (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm8 6)]))
          (Sail.Int.toNatChecked ((E -i 3))))) +++ (Sail.BitVec.extractLsb imm8 5 4)))
  let frac : (BitVec (Sail.Int.toNatChecked ((4 : Int) +i ((F : Int) -i (4 : Int))))) :=
    (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb imm8 3 0) +++ (Zeros
        (n := (Sail.Int.toNatChecked ((F -i 4)))))))
  let result : (BitVec (Sail.Int.toNatChecked (((1 : Int) +i (((1 : Int) +i ((E : Int) -i (3 : Int))) +i (2 : Int))) +i ((4 : Int) +i ((F : Int) -i (4 : Int)))))) :=
    (Sail.BitVec.castWidth ((sign +++ exp) +++ frac))
  (pure ((Sail.BitVec.castWidth result)))


def _set_CNTHP_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHP_CTL_EL2_Type_ENABLE r v)


def _set_CNTHPS_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHPS_CTL_EL2_Type_ENABLE r v)


def _set_CNTHPS_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHPS_CTL_Type_ENABLE r v)


def _set_CNTHP_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHP_CTL_Type_ENABLE r v)


def _set_CNTHVS_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHVS_CTL_EL2_Type_ENABLE r v)


def _set_CNTHVS_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHVS_CTL_Type_ENABLE r v)


def _set_CNTHV_CTL_EL2_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHV_CTL_EL2_Type_ENABLE r v)


def _set_CNTHV_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHV_CTL_Type_ENABLE r v)


def _set_CNTPS_CTL_EL1_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTPS_CTL_EL1_Type_ENABLE r v)


def _set_CNTP_CTL_EL0_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTP_CTL_EL0_Type_ENABLE r v)


def _set_CNTP_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTP_CTL_Type_ENABLE r v)


def _set_CNTV_CTL_EL0_Type_ENABLE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTV_CTL_EL0_Type_ENABLE r v)


def _set_CNTV_CTL_Type_ENABLE (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTV_CTL_Type_ENABLE r v)


def _set_CNTHP_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHP_CTL_EL2_Type_IMASK r v)


def _set_CNTHPS_CTL_EL2_Type_IMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHPS_CTL_EL2_Type_IMASK r v)


def _set_CNTHPS_CTL_Type_IMASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHPS_CTL_Type_IMASK r v)


end ArmFull.Functions
