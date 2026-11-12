import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0014
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0038
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051

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

def _set_DBGWCR_EL1_Type_PAC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_PAC r v)


def _set_DBGWCR_Type_PAC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_PAC r v)


def _set_DBGWCR_EL1_Type_WT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_WT r v)


def _set_DBGWCR_Type_WT (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_WT r v)


def _set_PMCFGR_Type_WT (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMCFGR_Type_WT r v)


/-- Type quantifiers: size : Nat, size > 0 -/
def write_request (accdesc : AccessDescriptor) (ti : (Option TranslationInfo)) (size : Nat) (va : (BitVec 64)) (pa : (BitVec 56)) (value : (BitVec (8 * size))) : (Mem_write_request size 64 (BitVec 56) (Option TranslationInfo) arm_acc_type) :=
  { access_kind := (AccessDescriptor_to_Access_kind accdesc)
    va := (some va)
    pa := pa
    translation := ti
    size := size
    value := (some value)
    tag := none }


def AArch64_S1POR (regime : Regime) : SailM (BitVec 64) := do
  match regime with
  | .Regime_EL3 =>
    (do
      let w__0 ← (( do readReg POR_EL3 ) : SailM (BitVec 64) )
      (pure ((Mk_S1PORType w__0))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do readReg POR_EL2 ) : SailM (BitVec 64) )
      (pure ((Mk_S1PORType w__1))))
  | .Regime_EL20 =>
    (do
      let w__2 ← (( do readReg POR_EL2 ) : SailM (BitVec 64) )
      (pure ((Mk_S1PORType w__2))))
  | .Regime_EL10 =>
    (do
      let w__3 ← (( do readReg POR_EL1 ) : SailM (BitVec 64) )
      (pure ((Mk_S1PORType w__3))))
  | _ =>
    (do
      (undefined_S1PORType (← occLabel 1441) ()))


def AArch64_S1DCacheEnabled (regime : Regime) : SailM Bool := do
  match regime with
  | .Regime_EL3 =>
    (do
      let w__0 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL3_Type_C w__0) == 1#1))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_C w__1) == 1#1))))
  | .Regime_EL20 =>
    (do
      let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_C w__2) == 1#1))))
  | .Regime_EL10 =>
    (do
      let w__3 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL1_Type_C w__3) == 1#1))))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 1456) ()))


def _set_MECID_P0_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MECID_P0_EL2_Type_MECID r v)


def _set_MECID_A0_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MECID_A0_EL2_Type_MECID r v)


def _set_MECID_A1_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MECID_A1_EL2_Type_MECID r v)


def _set_MECID_P1_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MECID_P1_EL2_Type_MECID r v)


def _set_MECID_RL_A_EL3_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_MECID_RL_A_EL3_Type_MECID r v)


def _set_VMECID_A_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMECID_A_EL2_Type_MECID r v)


def _set_VMECID_P_EL2_Type_MECID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VMECID_P_EL2_Type_MECID r v)


def AArch64_S1ICacheEnabled (regime : Regime) : SailM Bool := do
  match regime with
  | .Regime_EL3 =>
    (do
      let w__0 ← (( do readReg SCTLR_EL3 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL3_Type_I w__0) == 1#1))))
  | .Regime_EL2 =>
    (do
      let w__1 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_I w__1) == 1#1))))
  | .Regime_EL20 =>
    (do
      let w__2 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL2_Type_I w__2) == 1#1))))
  | .Regime_EL10 =>
    (do
      let w__3 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
      (pure (((_get_SCTLR_EL1_Type_I w__3) == 1#1))))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 1459) ()))


def AArch64_S1EPD (regime : Regime) (va : (BitVec 64)) : SailM (BitVec 1) := do
  ArmFull.assert (HasUnprivileged regime) "sail-arm/v8_base.sail:25151.34-25151.35"
  let varange : VARange := (AArch64_GetVARange va)
  match regime with
  | .Regime_EL20 =>
    (do
      if ((BEq.beq varange VARange_LOWER) : Bool)
      then
        (do
          let w__0 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL2_Type_EPD0 w__0))))
      else
        (do
          let w__1 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL2_Type_EPD1 w__1)))))
  | .Regime_EL10 =>
    (do
      if ((BEq.beq varange VARange_LOWER) : Bool)
      then
        (do
          let w__3 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL1_Type_EPD0 w__3))))
      else
        (do
          let w__4 ← (( do readReg TCR_EL1 ) : SailM (BitVec 64) )
          (pure ((_get_TCR_EL1_Type_EPD1 w__4)))))
  | _ =>
    (do
      (undefined_bitvector_at (← occLabel 1479) 1))


def AArch64_S1StartLevel (walkparams : S1TTWParams) : Int :=
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  let granulebits : Int := (TGxGranuleBits walkparams.tgx)
  let descsizelog2 : Int :=
    if ((walkparams.d128 == 1#1) : Bool)
    then 4
    else 3
  let stride : Int := (granulebits -i descsizelog2)
  let s1startlevel : Int := (FINAL_LEVEL -i (fdiv_int ((iasize -i 1) -i granulebits) stride))
  let s1startlevel : Int :=
    if ((walkparams.d128 == 1#1) : Bool)
    then (s1startlevel +i (BitVec.toNat walkparams.skl))
    else s1startlevel
  let s1startlevel : Int := s1startlevel
  s1startlevel


def _set_VSTCR_EL2_Type_SW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSTCR_EL2_Type_SW r v)


def _set_FPSID_Type_SW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_FPSID_Type_SW r v)


def _set_PMUSERENR_EL0_Type_SW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMUSERENR_EL0_Type_SW r v)


def _set_PMUSERENR_Type_SW (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMUSERENR_Type_SW r v)


def AArch64_S2DirectBasePermissions (permissions : Permissions) (accdesc : AccessDescriptor) : SailM S2AccessControls := do
  let s2perms ← (( do (undefined_S2AccessControls (← occLabel 1509) ()) ) : SailM
    S2AccessControls )
  let r : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access permissions.s2ap 0)]))
  let w : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access permissions.s2ap 1)]))
  let px ← (( do (undefined_bitvector_at (← occLabel 1510) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 1511) 1) ) : SailM (BitVec 1) )
  let (px, ux) : ((BitVec 1) × (BitVec 1)) :=
    match (BitVec.setWidth 2 (permissions.s2xn +++ permissions.s2xnx)) with
    | 0b00 =>
      (let (tup__0, tup__1) := ((1#1, 1#1) : ((BitVec 1) × (BitVec 1)))
      let px : (BitVec 1) := tup__0
      let ux : (BitVec 1) := tup__1
      (px, ux))
    | 0b01 =>
      (let (tup__0, tup__1) := ((0#1, 1#1) : ((BitVec 1) × (BitVec 1)))
      let px : (BitVec 1) := tup__0
      let ux : (BitVec 1) := tup__1
      (px, ux))
    | 0b10 =>
      (let (tup__0, tup__1) := ((0#1, 0#1) : ((BitVec 1) × (BitVec 1)))
      let px : (BitVec 1) := tup__0
      let ux : (BitVec 1) := tup__1
      (px, ux))
    | _ =>
      (let (tup__0, tup__1) := ((1#1, 0#1) : ((BitVec 1) × (BitVec 1)))
      let px : (BitVec 1) := tup__0
      let ux : (BitVec 1) := tup__1
      (px, ux))
  let x : (BitVec 1) :=
    if ((accdesc.el == EL0) : Bool)
    then ux
    else px
  let s2perms : S2AccessControls := { s2perms with r := r }
  let s2perms : S2AccessControls := { s2perms with w := w }
  let s2perms : S2AccessControls := { s2perms with x := x }
  let s2perms : S2AccessControls := { s2perms with r_rcw := r }
  let s2perms : S2AccessControls := { s2perms with w_rcw := w }
  let s2perms : S2AccessControls := { s2perms with r_mmu := r }
  let s2perms : S2AccessControls := { s2perms with w_mmu := w }
  (pure (s2perms))


def AArch64_S2IndirectBasePermissions (permissions : Permissions) (accdesc : AccessDescriptor) : SailM S2AccessControls := do
  let r ← (( do (undefined_bitvector_at (← occLabel 1512) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 1513) 1) ) : SailM (BitVec 1) )
  let r_rcw ← (( do (undefined_bitvector_at (← occLabel 1514) 1) ) : SailM (BitVec 1) )
  let w_rcw ← (( do (undefined_bitvector_at (← occLabel 1515) 1) ) : SailM (BitVec 1) )
  let r_mmu ← (( do (undefined_bitvector_at (← occLabel 1516) 1) ) : SailM (BitVec 1) )
  let w_mmu ← (( do (undefined_bitvector_at (← occLabel 1517) 1) ) : SailM (BitVec 1) )
  let px ← (( do (undefined_bitvector_at (← occLabel 1518) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 1519) 1) ) : SailM (BitVec 1) )
  let toplevel0 ← (( do (undefined_bitvector_at (← occLabel 1520) 1) ) : SailM (BitVec 1) )
  let toplevel1 ← (( do (undefined_bitvector_at (← occLabel 1521) 1) ) : SailM (BitVec 1) )
  let s2perms ← (( do (undefined_S2AccessControls (← occLabel 1522) ()) ) : SailM
    S2AccessControls )
  let s2pi : (BitVec 4) := permissions.s2pi
  let (px, r, ux, w, w_mmu, w_rcw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
    match s2pi with
    | 0b0000 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0001 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0010 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0011 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0100 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 1#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0101 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0110 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0111 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1000 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1001 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1010 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1011 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1100 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1101 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 0#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1110 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 1#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | _ =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 1#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
  let x : (BitVec 1) :=
    if ((accdesc.el == EL0) : Bool)
    then ux
    else px
  let (tup__0, tup__1) := ((r, r) : ((BitVec 1) × (BitVec 1)))
  let r_rcw : (BitVec 1) := tup__0
  let r_mmu : (BitVec 1) := tup__1
  let (toplevel0, toplevel1) : ((BitVec 1) × (BitVec 1)) :=
    match s2pi with
    | 0b0110 =>
      (let (tup__0, tup__1) := ((1#1, 0#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
    | 0b0011 =>
      (let (tup__0, tup__1) := ((0#1, 1#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
    | 0b0111 =>
      (let (tup__0, tup__1) := ((1#1, 1#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
    | _ =>
      (let (tup__0, tup__1) := ((0#1, 0#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
  let s2perms : S2AccessControls := { s2perms with r := r }
  let s2perms : S2AccessControls := { s2perms with w := w }
  let s2perms : S2AccessControls := { s2perms with x := x }
  let s2perms : S2AccessControls := { s2perms with r_rcw := r_rcw }
  let s2perms : S2AccessControls := { s2perms with r_mmu := r_mmu }
  let s2perms : S2AccessControls := { s2perms with w_rcw := w_rcw }
  let s2perms : S2AccessControls := { s2perms with w_mmu := w_mmu }
  let s2perms : S2AccessControls := { s2perms with toplevel0 := toplevel0 }
  let s2perms : S2AccessControls := { s2perms with toplevel1 := toplevel1 }
  (pure (s2perms))


def AArch64_S2OverlayPermissions (permissions : Permissions) (accdesc : AccessDescriptor) : SailM S2AccessControls := do
  let r ← (( do (undefined_bitvector_at (← occLabel 1524) 1) ) : SailM (BitVec 1) )
  let w ← (( do (undefined_bitvector_at (← occLabel 1525) 1) ) : SailM (BitVec 1) )
  let r_rcw ← (( do (undefined_bitvector_at (← occLabel 1526) 1) ) : SailM (BitVec 1) )
  let w_rcw ← (( do (undefined_bitvector_at (← occLabel 1527) 1) ) : SailM (BitVec 1) )
  let r_mmu ← (( do (undefined_bitvector_at (← occLabel 1528) 1) ) : SailM (BitVec 1) )
  let w_mmu ← (( do (undefined_bitvector_at (← occLabel 1529) 1) ) : SailM (BitVec 1) )
  let px ← (( do (undefined_bitvector_at (← occLabel 1530) 1) ) : SailM (BitVec 1) )
  let ux ← (( do (undefined_bitvector_at (← occLabel 1531) 1) ) : SailM (BitVec 1) )
  let toplevel0 ← (( do (undefined_bitvector_at (← occLabel 1532) 1) ) : SailM (BitVec 1) )
  let toplevel1 ← (( do (undefined_bitvector_at (← occLabel 1533) 1) ) : SailM (BitVec 1) )
  let s2overlay_perms ← (( do (undefined_S2AccessControls (← occLabel 1534) ()) ) : SailM
    S2AccessControls )
  let index : Int := (4 *i (BitVec.toNat permissions.s2po_index))
  let w__0 ← (( do readReg S2POR_EL1 ) : SailM (BitVec 64) )
  let s2po : (BitVec 4) :=
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb w__0 (Sail.Int.toNatChecked ((index +i 3)))
      (Sail.Int.toNatChecked (index))))
  let (px, r, ux, w, w_mmu, w_rcw) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)) :=
    match s2po with
    | 0b0000 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0001 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0010 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0011 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0100 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 1#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0101 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((0#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0110 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b0111 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1000 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1001 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 0#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1010 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 1#1, 0#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1011 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 0#1, 1#1, 1#1, 0#1, 0#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1100 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 0#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1101 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 0#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | 0b1110 =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 1#1, 0#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
    | _ =>
      (let (tup__0, tup__1, tup__2, tup__3, tup__4, tup__5) :=
        ((1#1, 1#1, 1#1, 1#1, 1#1, 1#1) : ((BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1) × (BitVec 1)))
      let r : (BitVec 1) := tup__0
      let w : (BitVec 1) := tup__1
      let px : (BitVec 1) := tup__2
      let ux : (BitVec 1) := tup__3
      let w_rcw : (BitVec 1) := tup__4
      let w_mmu : (BitVec 1) := tup__5
      (px, r, ux, w, w_mmu, w_rcw))
  let x : (BitVec 1) :=
    if ((accdesc.el == EL0) : Bool)
    then ux
    else px
  let (tup__0, tup__1) := ((r, r) : ((BitVec 1) × (BitVec 1)))
  let r_rcw : (BitVec 1) := tup__0
  let r_mmu : (BitVec 1) := tup__1
  let (toplevel0, toplevel1) : ((BitVec 1) × (BitVec 1)) :=
    match s2po with
    | 0b0110 =>
      (let (tup__0, tup__1) := ((1#1, 0#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
    | 0b0011 =>
      (let (tup__0, tup__1) := ((0#1, 1#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
    | 0b0111 =>
      (let (tup__0, tup__1) := ((1#1, 1#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
    | _ =>
      (let (tup__0, tup__1) := ((0#1, 0#1) : ((BitVec 1) × (BitVec 1)))
      let toplevel0 : (BitVec 1) := tup__0
      let toplevel1 : (BitVec 1) := tup__1
      (toplevel0, toplevel1))
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with or := r }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with ow := w }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with ox := x }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with or_rcw := r_rcw }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with ow_rcw := w_rcw }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with or_mmu := r_mmu }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with ow_mmu := w_mmu }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with toplevel0 := toplevel0 }
  let s2overlay_perms : S2AccessControls := { s2overlay_perms with toplevel1 := toplevel1 }
  (pure (s2overlay_perms))


end ArmFull.Functions
