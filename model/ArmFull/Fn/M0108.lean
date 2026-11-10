import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036

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

def _set_AMEVTYPER1_EL0_Type_evtCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMEVTYPER1_EL0_Type_evtCount r v)


def _set_AMEVTYPER1_Type_evtCount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMEVTYPER1_Type_evtCount r v)


def _set_PMEVTYPER_Type_evtCount (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMEVTYPER_Type_evtCount r v)


def _set_PMICFILTR_EL0_Type_evtCount (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMICFILTR_EL0_Type_evtCount r v)


def _set_SDCR_Type_SPD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDCR_Type_SPD r v)


def _set_EDPRSR_Type_SPD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDPRSR_Type_SPD r v)


def _set_SDER32_EL2_Type_SUIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SDER32_EL2_Type_SUIDEN r v)


def _set_SDER32_EL3_Type_SUIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SDER32_EL3_Type_SUIDEN r v)


def _set_SDER_Type_SUIDEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDER_Type_SUIDEN r v)


def _set_SDER32_EL2_Type_SUNIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SDER32_EL2_Type_SUNIDEN r v)


def _set_SDER32_EL3_Type_SUNIDEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SDER32_EL3_Type_SUNIDEN r v)


def _set_SDER_Type_SUNIDEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SDER_Type_SUNIDEN r v)


def SDER_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _SDER ) : SailM SDER_Type )
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__0 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__0 0 32)) : (BitVec 32))
      (pure (r)))
  else
    (do
      let w__1 ← (( do readReg SDER32_EL2 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__1 0 32)) : (BitVec 32))
      (pure (r)))


def _set_PMICNTR_EL0_Type_ICNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMICNTR_EL0_Type_ICNT r v)


def _set_PMICNTSVR_EL1_Type_ICNT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 64)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMICNTSVR_EL1_Type_ICNT r v)


def C27bSelect (allowed : (BitVec 256)) : SailM Int := SailME.run do
  let count : Int := 0
  let count ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 255
    (do
      let mut loop_vars := count
      for i in [loop_i_lower:loop_i_upper:1]i do
        let count := loop_vars
        loop_vars :=
          if (((BitVec.access allowed (Sail.Int.toNatChecked (i))) == 1#1) : Bool)
          then (count +i 1)
          else count
      (pure loop_vars)) ) : SailME Int Int )
  let count : Int := count
  ArmFull.assert (count ≥b 1) "/home/doug/boss-scratch/armcert-defects/c27b-accepted/armcert_c27b.sail:70.21-70.22"
  let w__0 ← (( do
    ((fun n => Sail.Int.toNatChecked n) <$> ((undefined_range_at (← occLabel 541) 0 (count -i 1))))
    ) : SailME Int Nat )
  let rank : Int := (w__0 : Nat)
  let rank ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 255
    (do
      let mut loop_vars := rank
      for i in [loop_i_lower:loop_i_upper:1]i do
        let rank := loop_vars
        loop_vars ← do
          if (((BitVec.access allowed (Sail.Int.toNatChecked (i))) == 1#1) : Bool)
          then
            (do
              if ((rank == 0) : Bool)
              then
                (do
                  SailME.throw (i : Int)
                  (pure (rank)))
              else
                (let rank : Int := (rank -i 1)
                (pure (rank))))
          else (pure (rank))
      (pure loop_vars)) ) : SailME Int Int )
  (Unreachable ())
  (pure (0))


def _set_BRBCR_EL1_Type_E0BRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_E0BRE r v)


def _set_BRBCR_EL1_Type_E1BRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_E1BRE r v)


def _set_BRBCR_EL1_Type_ERTN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_ERTN r v)


def _set_BRBCR_EL2_Type_ERTN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_ERTN r v)


def _set_BRBCR_EL1_Type_EXCEPTION (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_EXCEPTION r v)


def _set_BRBCR_EL2_Type_EXCEPTION (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_EXCEPTION r v)


def _set_BRBCR_EL1_Type_FZP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_FZP r v)


def _set_BRBCR_EL2_Type_FZP (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_FZP r v)


def _set_BRBCR_EL1_Type_FZPSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL1_Type_FZPSS r v)


def _set_BRBCR_EL2_Type_FZPSS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_FZPSS r v)


def _set_BRBCR_EL2_Type_E0HBRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_E0HBRE r v)


def _set_BRBCR_EL2_Type_E2BRE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBCR_EL2_Type_E2BRE r v)


def _set_BRBFCR_EL1_Type_BANK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_BANK r v)


def _set_MDSELR_EL1_Type_BANK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MDSELR_EL1_Type_BANK r v)


def _set_SPMSELR_EL0_Type_BANK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPMSELR_EL0_Type_BANK r v)


def _set_BRBFCR_EL1_Type_CONDDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_CONDDIR r v)


def _set_BRBFCR_EL1_Type_DIRCALL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_DIRCALL r v)


def _set_BRBFCR_EL1_Type_DIRECT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_DIRECT r v)


def _set_BRBFCR_EL1_Type_EnI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_EnI r v)


def _set_BRBFCR_EL1_Type_INDCALL (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_INDCALL r v)


def _set_BRBFCR_EL1_Type_INDIRECT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_INDIRECT r v)


def _set_BRBFCR_EL1_Type_PAUSED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_PAUSED r v)


def _set_BRBFCR_EL1_Type_RTN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_BRBFCR_EL1_Type_RTN r v)


def _set_CNTHCTL_EL2_Type_CNTPMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_CNTPMASK r v)


def _set_CNTHCTL_EL2_Type_CNTVMASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_CNTVMASK r v)


def _set_CNTHCTL_EL2_Type_ECV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_ECV r v)


def _set_ID_AA64MMFR0_EL1_Type_ECV (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR0_EL1_Type_ECV r v)


def _set_CNTHCTL_EL2_Type_EL0PCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0PCTEN r v)


def _set_CNTEL0ACR_Type_EL0PCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0PCTEN r v)


def _set_CNTKCTL_EL1_Type_EL0PCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0PCTEN r v)


def _set_CNTHCTL_EL2_Type_EL0PTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0PTEN r v)


def _set_CNTEL0ACR_Type_EL0PTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0PTEN r v)


def _set_CNTKCTL_EL1_Type_EL0PTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0PTEN r v)


def _set_CNTHCTL_EL2_Type_EL0VCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0VCTEN r v)


def _set_CNTEL0ACR_Type_EL0VCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0VCTEN r v)


def _set_CNTKCTL_EL1_Type_EL0VCTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0VCTEN r v)


def _set_CNTHCTL_EL2_Type_EL0VTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL0VTEN r v)


def _set_CNTEL0ACR_Type_EL0VTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTEL0ACR_Type_EL0VTEN r v)


def _set_CNTKCTL_EL1_Type_EL0VTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EL0VTEN r v)


def _set_CNTHCTL_EL2_Type_EL1NVPCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1NVPCT r v)


def _set_CNTHCTL_EL2_Type_EL1NVVCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1NVVCT r v)


def _set_CNTHCTL_EL2_Type_EL1PCEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1PCEN r v)


def _set_CNTHCTL_EL2_Type_EL1PTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1PTEN r v)


def _set_CNTHCTL_EL2_Type_EL1TVCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1TVCT r v)


def _set_CNTHCTL_EL2_Type_EL1TVT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EL1TVT r v)


def _set_CNTHCTL_EL2_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTDIR r v)


def _set_CNTHCTL_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTDIR r v)


def _set_CNTKCTL_EL1_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTDIR r v)


def _set_CNTKCTL_Type_EVNTDIR (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTDIR r v)


def _set_CNTHCTL_EL2_Type_EVNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTEN r v)


def _set_CNTHCTL_Type_EVNTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTEN r v)


def _set_CNTKCTL_EL1_Type_EVNTEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTEN r v)


def _set_CNTKCTL_Type_EVNTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTEN r v)


def _set_CNTHCTL_EL2_Type_EVNTI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTI r v)


def _set_CNTHCTL_Type_EVNTI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTI r v)


def _set_CNTKCTL_EL1_Type_EVNTI (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTI r v)


def _set_CNTKCTL_Type_EVNTI (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTI r v)


def _set_CNTHCTL_EL2_Type_EVNTIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTHCTL_EL2_Type_EVNTIS r v)


def _set_CNTHCTL_Type_EVNTIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTHCTL_Type_EVNTIS r v)


def _set_CNTKCTL_EL1_Type_EVNTIS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CNTKCTL_EL1_Type_EVNTIS r v)


def _set_CNTKCTL_Type_EVNTIS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_EVNTIS r v)


/-- Type quantifiers: N : Nat, N ≥ 0 -/
def ImpDefBits (x : String) (N : Nat) : SailM (BitVec N) := do
  if ((x == "Coresight timestamp") : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:759.54-759.55"
      let w__0 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
      (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((N -i 1)))
          0)))))
  else
    (do
      if ((x == "Synchronous Error") : Bool)
      then
        (do
          ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:762.53-762.54"
          (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb 0b00#2
              (Sail.Int.toNatChecked ((N -i 1))) 0)))))
      else
        (do
          if ((x == "Asynchronous Error") : Bool)
          then
            (do
              ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:765.53-765.54"
              (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb 0b11#2
                  (Sail.Int.toNatChecked ((N -i 1))) 0)))))
          else
            (do
              if ((x == "Virtual Asynchronous Abort ExT bit") : Bool)
              then (pure ((Sail.BitVec.castWidth (Zeros (n := N)))))
              else
                (do
                  if ((x == "FPEXC.EN value when TGE==1 and RW==0") : Bool)
                  then
                    (do
                      ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:770.38-770.39"
                      (pure ((Sail.BitVec.castWidth (integer_subrange 1 (N -i 1) 0)))))
                  else
                    (do
                      if ((x == "reset vector address") : Bool)
                      then
                        (do
                          ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:773.54-773.55"
                          let w__1 ← (( do readReg CFG_RVBAR ) : SailM (BitVec 64) )
                          (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__1
                              (Sail.Int.toNatChecked ((N -i 1))) 0)))))
                      else
                        (do
                          if ((x == "TG0 encoded granule size") : Bool)
                          then
                            (do
                              ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:776.53-776.54"
                              let w__2 ← (( do readReg __impdef_TG0 ) : SailM (BitVec 2) )
                              (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__2
                                  (Sail.Int.toNatChecked ((N -i 1))) 0)))))
                          else
                            (do
                              if ((x == "TG1 encoded granule size") : Bool)
                              then
                                (do
                                  ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 2)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:779.53-779.54"
                                  let w__3 ← (( do readReg __impdef_TG1 ) : SailM (BitVec 2) )
                                  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__3
                                      (Sail.Int.toNatChecked ((N -i 1))) 0)))))
                              else
                                (do
                                  if ((x == "Reserved short descriptor AP encoding") : Bool)
                                  then
                                    (do
                                      ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:782.38-782.39"
                                      (pure ((Sail.BitVec.castWidth (integer_subrange
                                          (BitVec.toNat 0b101#3) (N -i 1) 0)))))
                                  else
                                    (do
                                      if ((x == "Non-Faulting PAR") : Bool)
                                      then
                                        (do
                                          ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:785.53-785.54"
                                          (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb 0#1
                                              (Sail.Int.toNatChecked ((N -i 1))) 0)))))
                                      else
                                        (do
                                          if ((x == "Faulting PAR") : Bool)
                                          then (pure ((Sail.BitVec.castWidth (Zeros (n := N)))))
                                          else
                                            (do
                                              if ((x == "SPE mask 10:8,4,2") : Bool)
                                              then
                                                (do
                                                  ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 5)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:790.53-790.54"
                                                  (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                                                      0b11111#5 (Sail.Int.toNatChecked ((N -i 1))) 0)))))
                                              else
                                                (do
                                                  if ((x == "MPAM version") : Bool)
                                                  then
                                                    (do
                                                      ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:793.38-793.39"
                                                      let w__4 ← (( do readReg __mpam_major ) :
                                                        SailM (BitVec 4) )
                                                      (pure ((Sail.BitVec.castWidth (integer_subrange
                                                          (BitVec.toNat w__4) (N -i 1) 0)))))
                                                  else
                                                    (do
                                                      if ((x == "MPAM maximum PARTID") : Bool)
                                                      then
                                                        (do
                                                          ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:796.38-796.39"
                                                          let w__5 ← (( do
                                                            readReg __mpam_partid_max ) : SailM
                                                            (BitVec 16) )
                                                          (pure ((Sail.BitVec.castWidth (integer_subrange
                                                              (BitVec.toNat w__5) (N -i 1) 0)))))
                                                      else
                                                        (do
                                                          if ((x == "MPAM maximum PMG") : Bool)
                                                          then
                                                            (do
                                                              ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:799.38-799.39"
                                                              let w__6 ← (( do
                                                                readReg __mpam_pmg_max ) : SailM
                                                                (BitVec 8) )
                                                              (pure ((Sail.BitVec.castWidth (integer_subrange
                                                                  (BitVec.toNat w__6) (N -i 1) 0)))))
                                                          else
                                                            (do
                                                              if ((x == "Has MPAMHCR_EL2") : Bool)
                                                              then
                                                                (do
                                                                  let w__7 ← (( do
                                                                    readReg __mpam_has_hcr ) : SailM
                                                                    Bool )
                                                                  if (w__7 : Bool)
                                                                  then
                                                                    (do
                                                                      ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:803.42-803.43"
                                                                      (pure ((Sail.BitVec.castWidth (integer_subrange
                                                                          1 (N -i 1) 0)))))
                                                                  else
                                                                    (pure ((Sail.BitVec.castWidth (Zeros
                                                                        (n := N))))))
                                                              else
                                                                (do
                                                                  if ((x == "MPAM maximum VPMR") : Bool)
                                                                  then
                                                                    (do
                                                                      ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:807.38-807.39"
                                                                      let w__9 ← (( do
                                                                        readReg __mpam_vpmr_max ) :
                                                                        SailM (BitVec 3) )
                                                                      (pure ((Sail.BitVec.castWidth (integer_subrange
                                                                          (BitVec.toNat w__9)
                                                                          (N -i 1) 0)))))
                                                                  else
                                                                    (do
                                                                      if ((x == "SPE mask 63:48") : Bool)
                                                                      then
                                                                        (pure ((Sail.BitVec.castWidth (Zeros
                                                                            (n := N)))))
                                                                      else
                                                                        (do
                                                                          if ((x == "SPE mask 31:24") : Bool)
                                                                          then
                                                                            (pure ((Sail.BitVec.castWidth (Zeros
                                                                                (n := N)))))
                                                                          else
                                                                            (do
                                                                              if ((x == "SPE mask 15:12") : Bool)
                                                                              then
                                                                                (pure ((Sail.BitVec.castWidth (Zeros
                                                                                    (n := N)))))
                                                                              else
                                                                                (do
                                                                                  if ((x == "SPE EVENTS 63_48") : Bool)
                                                                                  then
                                                                                    (pure ((Sail.BitVec.castWidth (Zeros
                                                                                        (n := N)))))
                                                                                  else
                                                                                    (do
                                                                                      if ((x == "SPE EVENTS 31_24") : Bool)
                                                                                      then
                                                                                        (pure ((Sail.BitVec.castWidth (Zeros
                                                                                            (n := N)))))
                                                                                      else
                                                                                        (do
                                                                                          if ((x == "SPE EVENTS 15_12") : Bool)
                                                                                          then
                                                                                            (pure ((Sail.BitVec.castWidth (Zeros
                                                                                                (n := N)))))
                                                                                          else
                                                                                            (do
                                                                                              if ((x == "Default Memory Map XNX bit") : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  ArmFull.assert (0 ≤b (N -i 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:822.38-822.39"
                                                                                                  (pure ((Sail.BitVec.castWidth (integer_subrange
                                                                                                      0
                                                                                                      (N -i 1)
                                                                                                      0)))))
                                                                                              else
                                                                                                (do
                                                                                                  if ((x == "0") : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:825.53-825.54"
                                                                                                      (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                                                                                                          0#1
                                                                                                          (Sail.Int.toNatChecked ((N -i 1)))
                                                                                                          0)))))
                                                                                                  else
                                                                                                    (do
                                                                                                      if ((x == "1") : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          ArmFull.assert ((0 ≤b (N -i 1)) && ((N -i 1) <b 1)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:828.53-828.54"
                                                                                                          (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb
                                                                                                              1#1
                                                                                                              (Sail.Int.toNatChecked ((N -i 1)))
                                                                                                              0)))))
                                                                                                      else
                                                                                                        (do
                                                                                                          if ((x == "IMPDEF ErrorState") : Bool)
                                                                                                          then
                                                                                                            (pure ((Sail.BitVec.castWidth (Zeros
                                                                                                                (n := N)))))
                                                                                                          else
                                                                                                            (do
                                                                                                              if ((x == "Virtual External abort type") : Bool)
                                                                                                              then
                                                                                                                (pure ((Sail.BitVec.castWidth (Zeros
                                                                                                                    (n := N)))))
                                                                                                              else
                                                                                                                (do
                                                                                                                  if ((x == "Virtual SError syndrome") : Bool)
                                                                                                                  then
                                                                                                                    (pure ((Sail.BitVec.castWidth (Zeros
                                                                                                                        (n := N)))))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let _ : Unit :=
                                                                                                                        (print_endline
                                                                                                                          (String.append
                                                                                                                            x
                                                                                                                            " is not among the strings in the above list."))
                                                                                                                      ArmFull.assert false "/home/doug/boss-scratch/sail-lean-fork/integ/model/impdefs.sail:838.20-838.21"
                                                                                                                      throw Error.Exit)))))))))))))))))))))))))))))


end ArmFull.Functions
