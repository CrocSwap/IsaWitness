import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0016
import ArmFull.Fn.M0019
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0036
import ArmFull.Fn.M0039
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041

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

def _set_TCR_EL3_Type_TBI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_TBI r v)


def _set_TCR_EL2_Type_TBID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL2_Type_TBID r v)


def _set_TCR_EL3_Type_TBID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_TBID r v)


def _set_TCR_EL2_Type_TCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL2_Type_TCMA r v)


def _set_TCR_EL3_Type_TCMA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_TCMA r v)


def _set_TCR_EL3_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_AIE r v)


def _set_ID_AA64MMFR3_EL1_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_AIE r v)


def _set_TCR2_EL1_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_AIE r v)


def _set_TCR2_EL2_Type_AIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_AIE r v)


def _set_TCR_EL3_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_D128 r v)


def _set_ID_AA64MMFR3_EL1_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_D128 r v)


def _set_PAR_EL1_Type_D128 (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_D128 r v)


def _set_TCR2_EL1_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_D128 r v)


def _set_TCR2_EL2_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_D128 r v)


def _set_VTCR_EL2_Type_D128 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_D128 r v)


def _set_TCR_EL3_Type_DisCH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_DisCH0 r v)


def _set_TCR2_EL1_Type_DisCH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_DisCH0 r v)


def _set_TCR2_EL2_Type_DisCH0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_DisCH0 r v)


def _set_TCR_EL3_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_HAFT r v)


def _set_TCR2_EL1_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_HAFT r v)


def _set_TCR2_EL2_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_HAFT r v)


def _set_VTCR_EL2_Type_HAFT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_HAFT r v)


def _set_TCR_EL3_Type_PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_PIE r v)


def _set_TCR2_EL1_Type_PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_PIE r v)


def _set_TCR2_EL2_Type_PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_PIE r v)


def _set_TCR_EL3_Type_POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_POE r v)


def _set_TCR2_EL1_Type_POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_POE r v)


def _set_TCR2_EL2_Type_POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_POE r v)


def _set_TCR_EL3_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_PTTWI r v)


def _set_HCRX_EL2_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCRX_EL2_Type_PTTWI r v)


def _set_TCR2_EL1_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_PTTWI r v)


def _set_TCR2_EL2_Type_PTTWI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_PTTWI r v)


def _set_TCR_EL3_Type_PnCH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR_EL3_Type_PnCH r v)


def _set_TCR2_EL1_Type_PnCH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_PnCH r v)


def _set_TCR2_EL2_Type_PnCH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_PnCH r v)


def BRBEMispredictAllowed (_ : Unit) : SailM Bool := do
  let w__1 ← (( do
    if (((HaveEL EL2) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBCR_EL2_Type_MPRED w__0) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__3 : Bool :=
        if (((_get_BRBCR_EL1_Type_MPRED w__2) == 0#1) : Bool)
        then false
        else true
      (pure (w__3)))


def BRBCycleCountingEnabled (_ : Unit) : SailM Bool := do
  let w__1 ← (( do
    if (((HaveEL EL2) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBCR_EL2_Type_CC w__0) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__3 : Bool :=
        if (((_get_BRBCR_EL1_Type_CC w__2) == 0#1) : Bool)
        then false
        else true
      (pure (w__3)))


/-- Type quantifiers: k_cond : Bool -/
def FilterBranchRecord (br : BranchType) (cond : Bool) : SailM Bool := SailME.run do
  match br with
  | .BranchType_DIRCALL =>
    (do
      let w__0 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      let w__1 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      SailME.throw (((_get_BRBFCR_EL1_Type_DIRCALL w__0) != (_get_BRBFCR_EL1_Type_EnI w__1)) : Bool))
  | .BranchType_INDCALL =>
    (do
      let w__2 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      let w__3 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      SailME.throw (((_get_BRBFCR_EL1_Type_INDCALL w__2) != (_get_BRBFCR_EL1_Type_EnI w__3)) : Bool))
  | .BranchType_RET =>
    (do
      let w__4 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      let w__5 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      SailME.throw (((_get_BRBFCR_EL1_Type_RTN w__4) != (_get_BRBFCR_EL1_Type_EnI w__5)) : Bool))
  | .BranchType_DIR =>
    (do
      let w__10 ← (( do
        if (cond : Bool)
        then
          (do
            let w__6 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
            let w__7 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
            (pure (((_get_BRBFCR_EL1_Type_CONDDIR w__6) != (_get_BRBFCR_EL1_Type_EnI w__7)))))
        else
          (do
            let w__8 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
            let w__9 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
            (pure (((_get_BRBFCR_EL1_Type_DIRECT w__8) != (_get_BRBFCR_EL1_Type_EnI w__9))))) ) :
        SailME Bool Bool )
      SailME.throw (w__10 : Bool))
  | .BranchType_INDIR =>
    (do
      let w__11 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      let w__12 ← (( do readReg BRBFCR_EL1 ) : SailME Bool (BitVec 64) )
      SailME.throw (((_get_BRBFCR_EL1_Type_INDIRECT w__11) != (_get_BRBFCR_EL1_Type_EnI w__12)) : Bool))
  | _ =>
    (do
      (Unreachable ()))
  (pure (false))


/-- Type quantifiers: usr : Int, fiq : Int, irq : Int, svc : Int, abt : Int, und : Int, hyp : Int -/
def RBankSelect (mode : (BitVec 5)) (usr : Int) (fiq : Int) (irq : Int) (svc : Int) (abt : Int) (und : Int) (hyp : Int) : SailM Int := do
  let questionMark := mode
  if ((questionMark == M32_User) : Bool)
  then (pure (usr))
  else
    (do
      if ((questionMark == M32_FIQ) : Bool)
      then (pure (fiq))
      else
        (do
          if ((questionMark == M32_IRQ) : Bool)
          then (pure (irq))
          else
            (do
              if ((questionMark == M32_Svc) : Bool)
              then (pure (svc))
              else
                (do
                  if ((questionMark == M32_Abort) : Bool)
                  then (pure (abt))
                  else
                    (do
                      if ((questionMark == M32_Hyp) : Bool)
                      then (pure (hyp))
                      else
                        (do
                          if ((questionMark == M32_Undef) : Bool)
                          then (pure (und))
                          else
                            (do
                              if ((questionMark == M32_System) : Bool)
                              then (pure (usr))
                              else
                                (do
                                  ArmFull.assert false "Pattern match failure at /home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:6328.4-6337.5"
                                  throw Error.Exit))))))))


def _set_BRBIDR0_EL1_Type_FORMAT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBIDR0_EL1_Type_FORMAT r v)


def _set_BRBIDR0_EL1_Type_NUMREC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBIDR0_EL1_Type_NUMREC r v)


def _set_PMSIDR_EL1_Type_ArchInst (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_ArchInst r v)


def _set_PMSIDR_EL1_Type_CRR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_CRR r v)


def _set_PMSIDR_EL1_Type_CountSize (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_CountSize r v)


def _set_PMSIDR_EL1_Type_ERnd (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_ERnd r v)


def _set_PMSIDR_EL1_Type_FDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FDS r v)


def _set_PMSFCR_EL1_Type_FDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FDS r v)


def _set_PMSIDR_EL1_Type_FE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FE r v)


def _set_PMSFCR_EL1_Type_FE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FE r v)


def _set_PMSIDR_EL1_Type_FL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FL r v)


def _set_PMSFCR_EL1_Type_FL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FL r v)


def _set_PMSIDR_EL1_Type_FT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FT r v)


def _set_PMSFCR_EL1_Type_FT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FT r v)


def _set_PMSIDR_EL1_Type_FnE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_FnE r v)


def _set_PMSFCR_EL1_Type_FnE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSFCR_EL1_Type_FnE r v)


def _set_PMSIDR_EL1_Type_Format (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_Format r v)


def _set_PMSIDR_EL1_Type_Interval (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_Interval r v)


def _set_PMSIDR_EL1_Type_LDS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_LDS r v)


def _set_PMSIDR_EL1_Type_MaxSize (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_MaxSize r v)


def _set_PMSIDR_EL1_Type_PBT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSIDR_EL1_Type_PBT r v)


def _set_PMSCR_EL1_Type_CX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL1_Type_CX r v)


def _set_HTRFCR_Type_CX (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HTRFCR_Type_CX r v)


def _set_PMSCR_EL2_Type_CX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL2_Type_CX r v)


def _set_TRFCR_EL2_Type_CX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TRFCR_EL2_Type_CX r v)


def _set_PMSCR_EL1_Type_E0SPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL1_Type_E0SPE r v)


def _set_PMSCR_EL1_Type_E1SPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL1_Type_E1SPE r v)


def _set_PMSCR_EL1_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL1_Type_PA r v)


def _set_MFAR_EL3_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MFAR_EL3_Type_PA r v)


def _set_PAR_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 28)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PAR_Type_PA r v)


def _set_PFAR_EL1_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PFAR_EL1_Type_PA r v)


def _set_PFAR_EL2_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 56)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PFAR_EL2_Type_PA r v)


def _set_PMSCR_EL2_Type_PA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL2_Type_PA r v)


def _set_PMSCR_EL1_Type_PCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL1_Type_PCT r v)


def _set_PMSCR_EL2_Type_PCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL2_Type_PCT r v)


def _set_PMSCR_EL2_Type_E0HSPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL2_Type_E0HSPE r v)


def _set_PMSCR_EL2_Type_E2SPE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMSCR_EL2_Type_E2SPE r v)


def _set_PMBLIMITR_EL1_Type_FM (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_FM r v)


def _set_PMBLIMITR_EL1_Type_LIMIT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 52)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_LIMIT r v)


def _set_PMBLIMITR_EL1_Type_PMFZ (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBLIMITR_EL1_Type_PMFZ r v)


def _set_PMBSR_EL1_Type_AssuredOnly (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBSR_EL1_Type_AssuredOnly r v)


def _set_PAR_EL1_Type_AssuredOnly (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_AssuredOnly r v)


def _set_VTCR_EL2_Type_AssuredOnly (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_AssuredOnly r v)


def _set_PMBSR_EL1_Type_COLL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBSR_EL1_Type_COLL r v)


def _set_PMBSR_EL1_Type_DL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBSR_EL1_Type_DL r v)


def _set_PMBSR_EL1_Type_DirtyBit (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBSR_EL1_Type_DirtyBit r v)


def _set_PAR_EL1_Type_DirtyBit (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_DirtyBit r v)


def _set_PMBSR_EL1_Type_MSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBSR_EL1_Type_MSS r v)


def _set_PMBSR_EL1_Type_Overlay (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBSR_EL1_Type_Overlay r v)


def _set_PAR_EL1_Type_Overlay (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_Overlay r v)


def _set_PMBSR_EL1_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBSR_EL1_Type_S r v)


def _set_DBGVCR32_EL2_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGVCR32_EL2_Type_S r v)


def _set_DBGVCR_Type_S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGVCR_Type_S r v)


def _set_PAR_EL1_Type_S (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_PAR_EL1_Type_S r v)


def _set_TTBR0_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR0_Type_S r v)


def _set_TTBR1_Type_S (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TTBR1_Type_S r v)


def _set_VTCR_Type_S (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VTCR_Type_S r v)


/-- Type quantifiers: x : Int -/
def CeilPow2 (x : Int) : SailM Nat := do
  if ((x == 0) : Bool)
  then (pure (0))
  else
    (do
      if ((x == 1) : Bool)
      then (pure (2))
      else
        (do
          let w__0 ← (( do (FloorPow2 (x -i 1)) ) : SailM Nat )
          (pure ((Sail.Int.toNatChecked ((w__0 *i 2)))))))


def MaxImplementedVL (_ : Unit) : Int :=
  MAX_VL


def _set_ZCR_EL1_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ZCR_EL1_Type_LEN r v)


def _set_SMCR_EL1_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL1_Type_LEN r v)


def _set_SMCR_EL2_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL2_Type_LEN r v)


def _set_SMCR_EL3_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL3_Type_LEN r v)


def _set_ZCR_EL2_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ZCR_EL2_Type_LEN r v)


def _set_ZCR_EL3_Type_LEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ZCR_EL3_Type_LEN r v)


def _set_SMCR_EL1_Type_EZT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL1_Type_EZT0 r v)


def _set_SMCR_EL2_Type_EZT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL2_Type_EZT0 r v)


def _set_SMCR_EL3_Type_EZT0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL3_Type_EZT0 r v)


def _set_SMCR_EL1_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL1_Type_FA64 r v)


def _set_ID_AA64SMFR0_EL1_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64SMFR0_EL1_Type_FA64 r v)


def _set_SMCR_EL2_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL2_Type_FA64 r v)


def _set_SMCR_EL3_Type_FA64 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMCR_EL3_Type_FA64 r v)


def _set_GCSPR_EL0_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSPR_EL0_Type_PTR r v)


def _set_GCSPR_EL1_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSPR_EL1_Type_PTR r v)


def _set_GCSPR_EL2_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSPR_EL2_Type_PTR r v)


def _set_GCSPR_EL3_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 61)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCSPR_EL3_Type_PTR r v)


def _set_PMBPTR_EL1_Type_PTR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMBPTR_EL1_Type_PTR r v)


def _set_CPACR_EL1_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPACR_EL1_Type_E0POE r v)


def _set_CPTR_EL2_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_E0POE r v)


def _set_TCR2_EL1_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL1_Type_E0POE r v)


def _set_TCR2_EL2_Type_E0POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TCR2_EL2_Type_E0POE r v)


def _set_CPACR_EL1_Type_FPEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPACR_EL1_Type_FPEN r v)


def _set_CPTR_EL2_Type_FPEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CPTR_EL2_Type_FPEN r v)


end ArmFull.Functions
