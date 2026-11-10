import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0014
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0020
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022

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

def undefined_S2TTWParams (ℓ : ChoiceLabel) (_ : Unit) : SailM S2TTWParams := do
  let w__0 ← (( do (undefined_bitvector_at (ℓ.child 0) 1) ) : SailM (BitVec 1) )
  let w__1 ← (( do (undefined_bitvector_at (ℓ.child 1) 1) ) : SailM (BitVec 1) )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 1) ) : SailM (BitVec 1) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 1) ) : SailM (BitVec 1) )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 1) ) : SailM (BitVec 1) )
  let w__6 ← (( do (undefined_bitvector_at (ℓ.child 6) 1) ) : SailM (BitVec 1) )
  let w__7 ← (( do (undefined_bitvector_at (ℓ.child 7) 1) ) : SailM (BitVec 1) )
  let w__8 ← (( do (undefined_bitvector_at (ℓ.child 8) 1) ) : SailM (BitVec 1) )
  let w__9 ← (( do (undefined_bitvector_at (ℓ.child 9) 3) ) : SailM (BitVec 3) )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 10) 6) ) : SailM (BitVec 6) )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 11) 1) ) : SailM (BitVec 1) )
  let w__12 ← (( do (undefined_bitvector_at (ℓ.child 12) 1) ) : SailM (BitVec 1) )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 13) 2) ) : SailM (BitVec 2) )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 14) 1) ) : SailM (BitVec 1) )
  let w__15 ← (( do (undefined_S2PIRType (ℓ.child 15) ()) ) : SailM (BitVec 64) )
  let w__16 ← (( do (undefined_bitvector_at (ℓ.child 16) 1) ) : SailM (BitVec 1) )
  let w__17 ← (( do (undefined_bitvector_at (ℓ.child 17) 1) ) : SailM (BitVec 1) )
  let w__18 ← (( do (undefined_bitvector_at (ℓ.child 18) 1) ) : SailM (BitVec 1) )
  let w__19 ← (( do (undefined_bitvector_at (ℓ.child 19) 1) ) : SailM (BitVec 1) )
  let w__20 ← (( do (undefined_bitvector_at (ℓ.child 20) 1) ) : SailM (BitVec 1) )
  let w__21 ← (( do (undefined_bitvector_at (ℓ.child 21) 1) ) : SailM (BitVec 1) )
  let w__22 ← (( do (undefined_bitvector_at (ℓ.child 22) 4) ) : SailM (BitVec 4) )
  let w__23 ← (( do (undefined_TGx (ℓ.child 23) ()) ) : SailM TGx )
  let w__24 ← (( do (undefined_bitvector_at (ℓ.child 24) 2) ) : SailM (BitVec 2) )
  let w__25 ← (( do (undefined_bitvector_at (ℓ.child 25) 2) ) : SailM (BitVec 2) )
  let w__26 ← (( do (undefined_bitvector_at (ℓ.child 26) 2) ) : SailM (BitVec 2) )
  let w__27 ← (( do (undefined_bitvector_at (ℓ.child 27) 2) ) : SailM (BitVec 2) )
  let w__28 ← (( do (undefined_bitvector_at (ℓ.child 28) 1) ) : SailM (BitVec 1) )
  let w__29 ← (( do (undefined_bitvector_at (ℓ.child 29) 1) ) : SailM (BitVec 1) )
  let w__30 ← (( do (undefined_bitvector_at (ℓ.child 30) 1) ) : SailM (BitVec 1) )
  (pure ({ ha := w__0
           hd := w__1
           sl2 := w__2
           ds := w__3
           d128 := w__4
           sw := w__5
           nsw := w__6
           sa := w__7
           nsa := w__8
           ps := w__9
           txsz := w__10
           fwb := w__11
           cmow := w__12
           skl := w__13
           s2pie := w__14
           s2pir := w__15
           tl0 := w__16
           tl1 := w__17
           assuredonly := w__18
           haft := w__19
           emec := w__20
           s := w__21
           t0sz := w__22
           tgx := w__23
           sl0 := w__24
           irgn := w__25
           orgn := w__26
           sh := w__27
           ee := w__28
           ptw := w__29
           vm := w__30 }))


def undefined_TLBContext (ℓ : ChoiceLabel) (_ : Unit) : SailM TLBContext := do
  let w__0 ← (( do (undefined_SecurityState (ℓ.child 0) ()) ) : SailM SecurityState )
  let w__1 ← (( do (undefined_Regime (ℓ.child 1) ()) ) : SailM Regime )
  let w__2 ← (( do (undefined_bitvector_at (ℓ.child 2) 16) ) : SailM (BitVec 16) )
  let w__3 ← (( do (undefined_bitvector_at (ℓ.child 3) 16) ) : SailM (BitVec 16) )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 1) ) : SailM (BitVec 1) )
  let w__5 ← (( do (undefined_PASpace (ℓ.child 5) ()) ) : SailM PASpace )
  let w__6 ← (( do (undefined_bool_at (ℓ.child 6) ()) ) : SailM Bool )
  let w__7 ← (( do (undefined_bool_at (ℓ.child 7) ()) ) : SailM Bool )
  let w__8 ← (( do (undefined_bool_at (ℓ.child 8) ()) ) : SailM Bool )
  let w__9 ← (( do (undefined_bitvector_at (ℓ.child 9) 64) ) : SailM (BitVec 64) )
  let w__10 ← (( do (undefined_TGx (ℓ.child 10) ()) ) : SailM TGx )
  let w__11 ← (( do (undefined_bitvector_at (ℓ.child 11) 1) ) : SailM (BitVec 1) )
  let w__12 ← (( do (undefined_int_at (ℓ.child 12) ()) ) : SailM Int )
  let w__13 ← (( do (undefined_bool_at (ℓ.child 13) ()) ) : SailM Bool )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 14) 1) ) : SailM (BitVec 1) )
  (pure ({ ss := w__0
           regime := w__1
           vmid := w__2
           asid := w__3
           nG := w__4
           ipaspace := w__5
           includes_s1_name := w__6
           includes_s2_name := w__7
           includes_gpt_name := w__8
           ia := w__9
           tg := w__10
           cnp := w__11
           level := w__12
           isd128 := w__13
           xs := w__14 }))


def DEFAULT_MECID : (BitVec 16) := (Zeros (n := 16))


def _set_FPSR_Type_IDC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_IDC r v)


def _set_CTR_EL0_Type_IDC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_CTR_EL0_Type_IDC r v)


def _set_CTR_Type_IDC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CTR_Type_IDC r v)


def _set_FPSCR_Type_IDC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_IDC r v)


def _set_FPSR_Type_IXC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_IXC r v)


def _set_FPSCR_Type_IXC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_IXC r v)


def _set_FPSR_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_N r v)


def _set_AMCFGR_EL0_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_AMCFGR_EL0_Type_N r v)


def _set_AMCFGR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_AMCFGR_Type_N r v)


def _set_DSPSR_EL0_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DSPSR_EL0_Type_N r v)


def _set_DSPSR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DSPSR_Type_N r v)


def _set_FPSCR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_N r v)


def _set_PMCFGR_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_N r v)


def _set_PMCR_EL0_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCR_EL0_Type_N r v)


def _set_PMCR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMCR_Type_N r v)


def _set_SPSR_EL1_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL1_Type_N r v)


def _set_SPSR_EL2_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL2_Type_N r v)


def _set_SPSR_EL3_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL3_Type_N r v)


def _set_SPSR_abt_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_abt_Type_N r v)


def _set_SPSR_fiq_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_fiq_Type_N r v)


def _set_SPSR_hyp_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_hyp_Type_N r v)


def _set_SPSR_irq_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_irq_Type_N r v)


def _set_SPSR_mon_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_mon_Type_N r v)


def _set_SPSR_svc_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_svc_Type_N r v)


def _set_SPSR_und_Type_N (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_und_Type_N r v)


def _set_TTBCR_Type_N (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 3)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_TTBCR_Type_N r v)


def _set_FPSR_Type_QC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_QC r v)


def _set_FPSCR_Type_QC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_QC r v)


def _set_FPSR_Type_UFC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_UFC r v)


def _set_FPSCR_Type_UFC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_UFC r v)


def _set_FPSR_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_V r v)


def _set_DSPSR_EL0_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DSPSR_EL0_Type_V r v)


def _set_DSPSR_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DSPSR_Type_V r v)


def _set_FPSCR_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_V r v)


def _set_GICR_INVALLR_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_INVALLR_Type_V r v)


def _set_GICR_INVLPIR_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_INVLPIR_Type_V r v)


def _set_SCTLR_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SCTLR_Type_V r v)


def _set_SPSR_EL1_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL1_Type_V r v)


def _set_SPSR_EL2_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL2_Type_V r v)


def _set_SPSR_EL3_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL3_Type_V r v)


def _set_SPSR_abt_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_abt_Type_V r v)


def _set_SPSR_fiq_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_fiq_Type_V r v)


def _set_SPSR_hyp_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_hyp_Type_V r v)


def _set_SPSR_irq_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_irq_Type_V r v)


def _set_SPSR_mon_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_mon_Type_V r v)


def _set_SPSR_svc_Type_V (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_svc_Type_V r v)


def _set_SPSR_und_Type_V (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_und_Type_V r v)


def _set_FPSR_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_FPSR_Type_Z r v)


def _set_DSPSR_EL0_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DSPSR_EL0_Type_Z r v)


def _set_DSPSR_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DSPSR_Type_Z r v)


def _set_FPSCR_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSCR_Type_Z r v)


def _set_GICR_VPROPBASER_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GICR_VPROPBASER_Type_Z r v)


def _set_SPSR_EL1_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL1_Type_Z r v)


def _set_SPSR_EL2_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL2_Type_Z r v)


def _set_SPSR_EL3_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_EL3_Type_Z r v)


def _set_SPSR_abt_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_abt_Type_Z r v)


def _set_SPSR_fiq_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_fiq_Type_Z r v)


def _set_SPSR_hyp_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_hyp_Type_Z r v)


def _set_SPSR_irq_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_irq_Type_Z r v)


def _set_SPSR_mon_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_mon_Type_Z r v)


def _set_SPSR_svc_Type_Z (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_SPSR_svc_Type_Z r v)


def _set_SPSR_und_Type_Z (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SPSR_und_Type_Z r v)


def _set_ICC_PMR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_PMR_EL1_Type_Priority r v)


def _set_GICC_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_PMR_Type_Priority r v)


def _set_GICC_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICC_RPR_Type_Priority r v)


def _set_GICV_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_PMR_Type_Priority r v)


def _set_GICV_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_GICV_RPR_Type_Priority r v)


def _set_ICC_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_PMR_Type_Priority r v)


def _set_ICC_RPR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICC_RPR_EL1_Type_Priority r v)


def _set_ICC_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICC_RPR_Type_Priority r v)


def _set_ICH_LRC_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICH_LRC_Type_Priority r v)


def _set_ICH_LR_EL2_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICH_LR_EL2_Type_Priority r v)


def _set_ICV_PMR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_PMR_EL1_Type_Priority r v)


def _set_ICV_PMR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_PMR_Type_Priority r v)


def _set_ICV_RPR_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ICV_RPR_EL1_Type_Priority r v)


def _set_ICV_RPR_Type_Priority (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_ICV_RPR_Type_Priority r v)


def _set_SMPRI_EL1_Type_Priority (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SMPRI_EL1_Type_Priority r v)


def __UNKNOWN_GPTTable (_ : Unit) : SailM GPTTable := do
  (undefined_GPTTable (← occLabel 424) ())


def __UNKNOWN_GPTEntry (_ : Unit) : SailM GPTEntry := do
  (undefined_GPTEntry (← occLabel 430) ())


def VMID_NONE : (BitVec 16) := (Zeros (n := 16))


def undefined_TLBIRecord (ℓ : ChoiceLabel) (_ : Unit) : SailM TLBIRecord := do
  let w__0 ← (( do (undefined_TLBIOp (ℓ.child 0) ()) ) : SailM TLBIOp )
  let w__1 ← (( do (undefined_bool_at (ℓ.child 1) ()) ) : SailM Bool )
  let w__2 ← (( do (undefined_SecurityState (ℓ.child 2) ()) ) : SailM SecurityState )
  let w__3 ← (( do (undefined_Regime (ℓ.child 3) ()) ) : SailM Regime )
  let w__4 ← (( do (undefined_bitvector_at (ℓ.child 4) 16) ) : SailM (BitVec 16) )
  let w__5 ← (( do (undefined_bitvector_at (ℓ.child 5) 16) ) : SailM (BitVec 16) )
  let w__6 ← (( do (undefined_TLBILevel (ℓ.child 6) ()) ) : SailM TLBILevel )
  let w__7 ← (( do (undefined_TLBIMemAttr (ℓ.child 7) ()) ) : SailM TLBIMemAttr )
  let w__8 ← (( do (undefined_PASpace (ℓ.child 8) ()) ) : SailM PASpace )
  let w__9 ← (( do (undefined_bitvector_at (ℓ.child 9) 64) ) : SailM (BitVec 64) )
  let w__10 ← (( do (undefined_bitvector_at (ℓ.child 10) 64) ) : SailM (BitVec 64) )
  let w__11 ← (( do (undefined_bool_at (ℓ.child 11) ()) ) : SailM Bool )
  let w__12 ← (( do (undefined_bool_at (ℓ.child 12) ()) ) : SailM Bool )
  let w__13 ← (( do (undefined_bitvector_at (ℓ.child 13) 4) ) : SailM (BitVec 4) )
  let w__14 ← (( do (undefined_bitvector_at (ℓ.child 14) 2) ) : SailM (BitVec 2) )
  (pure ({ op := w__0
           from_aarch64 := w__1
           security := w__2
           regime := w__3
           vmid := w__4
           asid := w__5
           level := w__6
           attr := w__7
           ipaspace := w__8
           address := w__9
           end_address_name := w__10
           d64 := w__11
           d128 := w__12
           ttl := w__13
           tg := w__14 }))


def undefined_GPTTLBLine (ℓ : ChoiceLabel) (_ : Unit) : SailM GPTTLBLine := do
  let w__0 ← (( do (undefined_GPTEntry (ℓ.child 0) ()) ) : SailM GPTEntry )
  let w__1 ← (( do (undefined_bool_at (ℓ.child 1) ()) ) : SailM Bool )
  (pure ({ gpt_entry := w__0
           valid_name := w__1 }))


def _set_HCR_EL2_Type_AMO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_AMO r v)


def _set_HCR_Type_AMO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR_Type_AMO r v)


def _set_HCR_EL2_Type_AMVOFFEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_AMVOFFEN r v)


def _set_SCR_EL3_Type_AMVOFFEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_AMVOFFEN r v)


def _set_HCR_EL2_Type_API (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_API r v)


def _set_ID_AA64ISAR1_EL1_Type_API (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64ISAR1_EL1_Type_API r v)


def _set_SCR_EL3_Type_API (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_API r v)


def _set_HCR_EL2_Type_APK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_APK r v)


def _set_SCR_EL3_Type_APK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_APK r v)


def _set_HCR_EL2_Type_AT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_AT r v)


def _set_ID_AA64MMFR2_EL1_Type_AT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_AT r v)


def _set_HCR_EL2_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_ATA r v)


def _set_SCR_EL3_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_ATA r v)


def _set_SCTLR_EL1_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL1_Type_ATA r v)


def _set_SCTLR_EL2_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL2_Type_ATA r v)


def _set_SCTLR_EL3_Type_ATA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCTLR_EL3_Type_ATA r v)


def _set_HCR_EL2_Type_BSU (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_BSU r v)


def _set_HCR_Type_BSU (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR_Type_BSU r v)


def _set_HCR_EL2_Type_CD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_CD r v)


def _set_HCR2_Type_CD (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR2_Type_CD r v)


def _set_HCR_EL2_Type_DC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_DC r v)


def _set_HCR_Type_DC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR_Type_DC r v)


def _set_HCR_EL2_Type_DCT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_DCT r v)


def _set_HCR_EL2_Type_E2H (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_E2H r v)


def _set_HCR_EL2_Type_EnSCXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_EnSCXT r v)


def _set_SCR_EL3_Type_EnSCXT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_EnSCXT r v)


def _set_HCR_EL2_Type_FB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_FB r v)


def _set_HCR_Type_FB (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR_Type_FB r v)


def _set_HCR_EL2_Type_FIEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_FIEN r v)


def _set_SCR_EL3_Type_FIEN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_FIEN r v)


def _set_HCR_EL2_Type_FMO (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_FMO r v)


def _set_HCR_Type_FMO (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_HCR_Type_FMO r v)


def _set_HCR_EL2_Type_FWB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_FWB r v)


def _set_ID_AA64MMFR2_EL1_Type_FWB (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR2_EL1_Type_FWB r v)


def _set_HCR_EL2_Type_GPF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_GPF r v)


def _set_SCR_EL3_Type_GPF (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_SCR_EL3_Type_GPF r v)


def _set_HCR_EL2_Type_HCD (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_HCR_EL2_Type_HCD r v)


end ArmFull.Functions
