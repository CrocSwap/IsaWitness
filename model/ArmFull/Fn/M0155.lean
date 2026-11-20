module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0049
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0119
public import ArmFull.Fn.M0120
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147 set_option backward.proofsInPublic true @[expose] public section

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

def AArch64_TLBContextEL3 (ss : SecurityState) (va : (BitVec 64)) (tg : TGx) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1475) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL3 }
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := va }
  let w__0 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  let w__2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg TTBR0_EL3 ) : SailM (BitVec 64) )
        (pure ((_get_TTBR0_EL3_Type_CnP w__1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let tlbcontext := ({ tlbcontext with cnp := w__2 } : TLBContext)
  (pure (tlbcontext))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S1TTBaseAddress (walkparams : S1TTWParams) (regime : Regime) (ttbr : (BitVec k_N)) : SailM (BitVec 56) := do
  let tablebase : (BitVec 56) := (Zeros (n := 56))
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  let granulebits : Int := (TGxGranuleBits walkparams.tgx)
  let descsizelog2 : Int :=
    if ((walkparams.d128 == 1#1) : Bool)
    then 4
    else 3
  let stride : Int := (granulebits -i descsizelog2)
  let startlevel : Int := (AArch64_S1StartLevel walkparams)
  let levels : Int := (FINAL_LEVEL -i startlevel)
  let tsize : Int := ((iasize -i ((levels *i stride) +i granulebits)) +i descsizelog2)
  let w__1 ← (( do
    (pure ((← do
          (Have56BitPAExt ())) && ((walkparams.d128 == 1#1) : Bool))) ) : SailM Bool )
  let (tablebase, tsize) ← (( do
    if (w__1 : Bool)
    then
      (do
        let tsize : Int := (Max.max tsize 5)
        let tablebase ← (( do
          if ((BEq.beq regime Regime_EL3) : Bool)
          then
            (do
              ArmFull.assert (55 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:25239.38-25239.39"
              let tablebase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange tablebase 55 5 (Sail.BitVec.extractLsb ttbr 55 5))
              (pure (tablebase)))
          else
            (do
              ArmFull.assert (87 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:25242.38-25242.39"
              let tablebase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange tablebase 55 5
                  ((Sail.BitVec.extractLsb ttbr 87 80) +++ (Sail.BitVec.extractLsb ttbr 47 5)))
              (pure (tablebase))) ) : SailM (BitVec 56) )
        (pure ((tablebase, tsize))))
    else
      (do
        let w__5 ← (( do
          (pure ((← do
                (pure ((← do
                      (pure ((← do
                            (Have52BitPAExt ())) && ((BEq.beq walkparams.tgx TGx_64KB) : Bool)))) && ((walkparams.ps == 0b110#3) : Bool)))) || ((walkparams.ds == 1#1) : Bool)))
          ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            let tsize : Int := (Max.max tsize 6)
            ArmFull.assert (5 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:25247.33-25247.34"
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:25248.34-25248.35"
            let tablebase : (BitVec 56) :=
              (Sail.BitVec.updateSubrange tablebase 51 6
                ((Sail.BitVec.extractLsb ttbr 5 2) +++ (Sail.BitVec.extractLsb ttbr 47 6)))
            (pure ((tablebase, tsize))))
        else
          (do
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:25251.34-25251.35"
            let tablebase : (BitVec 56) :=
              (Sail.BitVec.updateSubrange tablebase 47 1 (Sail.BitVec.extractLsb ttbr 47 1))
            (pure ((tablebase, tsize))))) ) : SailM ((BitVec 56) × Int) )
  let tsize : Int := tsize
  let tablebase : (BitVec 56) := (Align_bits tablebase (_shl_int_general 1 tsize))
  (pure (tablebase))


/-- Type quantifiers: k_N : Nat, level : Int, k_N ≥ 0 -/
def AArch64_LeafBase (descriptor : (BitVec k_N)) (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) (level : Int) : SailM (BitVec 56) := do
  let leafbase : (BitVec 56) := (Zeros (n := 56))
  let granulebits : Int := (TGxGranuleBits tgx)
  let descsizelog2 : Int :=
    if ((d128 == 1#1) : Bool)
    then 4
    else 3
  let stride : Int := (granulebits -i descsizelog2)
  let leafsize : Int := (granulebits +i (stride *i (FINAL_LEVEL -i level)))
  ArmFull.assert ((0 ≤b leafsize) && ((leafsize ≤b 47) && (47 <b (Sail.BitVec.length descriptor)))) "sail-inputs/03-v8_base.sail:25336.67-25336.68"
  let leafbase : (BitVec 56) :=
    (Sail.BitVec.updateSubrange leafbase 47 0
      (Sail.BitVec.castWidth ((Sail.BitVec.extractLsb descriptor 47
          (Sail.Int.toNatChecked (leafsize))) +++ (Zeros (n := (Sail.Int.toNatChecked (leafsize)))))))
  let w__1 ← (( do
    (pure ((← do
          (Have56BitPAExt ())) && ((d128 == 1#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      ArmFull.assert (55 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25339.34-25339.35"
      let leafbase : (BitVec 56) :=
        (Sail.BitVec.updateSubrange leafbase 55 48 (Sail.BitVec.extractLsb descriptor 55 48))
      (pure (leafbase)))
  else
    (do
      let w__3 ← (( do
        (pure ((← do
              (Have52BitPAExt ())) && ((BEq.beq tgx TGx_64KB) : Bool))) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (let leafbase : (BitVec 56) :=
          (Sail.BitVec.updateSubrange leafbase 51 48 (Sail.BitVec.extractLsb descriptor 15 12))
        (pure (leafbase)))
      else
        (do
          if ((ds == 1#1) : Bool)
          then
            (do
              ArmFull.assert (49 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25346.34-25346.35"
              let leafbase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange leafbase 51 48
                  ((Sail.BitVec.extractLsb descriptor 9 8) +++ (Sail.BitVec.extractLsb descriptor 49
                      48)))
              (pure (leafbase)))
          else (pure (leafbase))))


/-- Type quantifiers: index : Int -/
def AArch64_MAIRAttr (index : Int) (mair2 : (BitVec 64)) (mair : (BitVec 64)) : SailM (BitVec 8) := do
  let bit_index : Int := (8 *i index)
  let w__2 ← (( do
    if (((index <b 8) : Bool) : Bool)
    then (pure true)
    else
      (do
        (pure ((← do
              (HaveAIEExt ())) && ((index <b 16) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:25357.48-25357.49"
  if ((index >b 7) : Bool)
  then
    (do
      let bit_index : Int := (bit_index -i 64)
      ArmFull.assert ((0 ≤b bit_index) && ((bit_index ≤b (bit_index +i 7)) && ((bit_index +i 7) <b 64))) "sail-inputs/03-v8_base.sail:25360.97-25360.98"
      (pure ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb mair2
          (Sail.Int.toNatChecked ((bit_index +i 7))) (Sail.Int.toNatChecked (bit_index)))))))
  else
    (do
      let bit_index : Int := bit_index
      ArmFull.assert ((0 ≤b bit_index) && ((bit_index ≤b (bit_index +i 7)) && ((bit_index +i 7) <b 64))) "sail-inputs/03-v8_base.sail:25364.97-25364.98"
      (pure ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb mair
          (Sail.Int.toNatChecked ((bit_index +i 7))) (Sail.Int.toNatChecked (bit_index)))))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_NextTableBase (descriptor : (BitVec k_N)) (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) : SailM (BitVec 56) := do
  let tablebase : (BitVec 56) := (Zeros (n := 56))
  let tablebase ← (( do
    match tgx with
    | .TGx_4KB =>
      (do
        ArmFull.assert (47 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25549.36-25549.37"
        let tablebase : (BitVec 56) :=
          (Sail.BitVec.updateSubrange tablebase 47 12 (Sail.BitVec.extractLsb descriptor 47 12))
        (pure (tablebase)))
    | .TGx_16KB =>
      (do
        ArmFull.assert (47 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25553.36-25553.37"
        let tablebase : (BitVec 56) :=
          (Sail.BitVec.updateSubrange tablebase 47 14 (Sail.BitVec.extractLsb descriptor 47 14))
        (pure (tablebase)))
    | .TGx_64KB =>
      (do
        ArmFull.assert (47 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25557.36-25557.37"
        let tablebase : (BitVec 56) :=
          (Sail.BitVec.updateSubrange tablebase 47 16 (Sail.BitVec.extractLsb descriptor 47 16))
        (pure (tablebase))) ) : SailM (BitVec 56) )
  let w__1 ← (( do
    (pure ((← do
          (Have56BitPAExt ())) && ((d128 == 1#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      ArmFull.assert (55 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25562.34-25562.35"
      let tablebase : (BitVec 56) :=
        (Sail.BitVec.updateSubrange tablebase 55 48 (Sail.BitVec.extractLsb descriptor 55 48))
      (pure (tablebase)))
  else
    (do
      let w__3 ← (( do
        (pure ((← do
              (Have52BitPAExt ())) && ((BEq.beq tgx TGx_64KB) : Bool))) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          ArmFull.assert (15 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25567.34-25567.35"
          let tablebase : (BitVec 56) :=
            (Sail.BitVec.updateSubrange tablebase 51 48 (Sail.BitVec.extractLsb descriptor 15 12))
          (pure (tablebase)))
      else
        (do
          if ((ds == 1#1) : Bool)
          then
            (do
              ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25572.33-25572.34"
              ArmFull.assert (49 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:25573.34-25573.35"
              let tablebase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange tablebase 51 48
                  ((Sail.BitVec.extractLsb descriptor 9 8) +++ (Sail.BitVec.extractLsb descriptor 49
                      48)))
              (pure (tablebase)))
          else (pure (tablebase))))


def AArch64_IPAIsOutOfRange (ipa : (BitVec 56)) (walkparams : S2TTWParams) : Bool :=
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  if ((iasize <b 56) : Bool)
  then (! (is_zero_subrange ipa 55 iasize))
  else false


def AArch64_S2ComputePermissions (permissions : Permissions) (walkparams : S2TTWParams) (accdesc : AccessDescriptor) : SailM S2AccessControls := do
  let s2overlay_perms ← (( do (undefined_S2AccessControls (← occLabel 1535) ()) ) : SailM
    S2AccessControls )
  let s2perms ← (( do (undefined_S2AccessControls (← occLabel 1536) ()) ) : SailM
    S2AccessControls )
  if ((walkparams.s2pie == 1#1) : Bool)
  then
    (do
      let w__0 ← (( do (AArch64_S2IndirectBasePermissions permissions accdesc) ) : SailM
        S2AccessControls )
      let s2perms := (w__0 : S2AccessControls)
      let w__3 ← (( do
        if ((← do
             (HaveS2POExt ())) : Bool)
        then
          (do
            let w__2 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_VTCR_EL2_Type_S2POE w__2) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let s2perms := ({ s2perms with overlay := w__3 } : S2AccessControls)
      if (s2perms.overlay : Bool)
      then
        (do
          let s2overlay_perms ← (( do (AArch64_S2OverlayPermissions permissions accdesc) ) : SailM
            S2AccessControls )
          let s2perms : S2AccessControls := { s2perms with or := s2overlay_perms.or }
          let s2perms : S2AccessControls := { s2perms with ow := s2overlay_perms.ow }
          let s2perms : S2AccessControls := { s2perms with ox := s2overlay_perms.ox }
          let s2perms : S2AccessControls := { s2perms with or_rcw := s2overlay_perms.or_rcw }
          let s2perms : S2AccessControls := { s2perms with ow_rcw := s2overlay_perms.ow_rcw }
          let s2perms : S2AccessControls := { s2perms with or_mmu := s2overlay_perms.or_mmu }
          let s2perms : S2AccessControls := { s2perms with ow_mmu := s2overlay_perms.ow_mmu }
          let s2perms : S2AccessControls :=
            if ((((s2perms.w +++ (s2perms.w_rcw +++ s2perms.w_mmu)) &&& (s2perms.ow +++ (s2perms.ow_rcw +++ s2perms.ow_mmu))) == 0b011#3) : Bool)
            then
              (let s2perms : S2AccessControls :=
                { s2perms with toplevel0 := (s2perms.toplevel0 ||| s2overlay_perms.toplevel0) }
              { s2perms with toplevel1 := (s2perms.toplevel1 ||| s2overlay_perms.toplevel1) })
            else
              (let s2perms : S2AccessControls := { s2perms with toplevel0 := 0#1 }
              { s2perms with toplevel1 := 0#1 })
          (pure (s2perms)))
      else (pure (s2perms)))
  else
    (do
      (AArch64_S2DirectBasePermissions permissions accdesc))


/-- Type quantifiers: k_aligned : Bool -/
def AArch64_S2HasAlignmentFault (accdesc : AccessDescriptor) (aligned : Bool) (memattrs : MemoryAttributes) : SailM Bool := do
  if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
  then (pure (false))
  else
    (do
      let w__2 ← (( do
        (pure ((← do
              (pure ((← do
                    (HaveMTEExt ())) && (accdesc.tagaccess : Bool)))) && (accdesc.write : Bool))) )
        : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          if (((BEq.beq memattrs.memtype MemType_Device) : Bool) : Bool)
          then
            (do
              let w__3 ← (( do (ConstrainUnpredictable Unpredictable_DEVICETAGSTORE) ) : SailM
                Constraint )
              (pure (((BEq.beq w__3 Constraint_FAULT) : Bool))))
          else (pure false))
      else
        (pure (if ((BEq.beq accdesc.acctype AccessType_DCZero) : Bool)
          then (BEq.beq memattrs.memtype MemType_Device)
          else ((BEq.beq memattrs.memtype MemType_Device) && (! aligned)))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S2TTBaseAddress (walkparams : S2TTWParams) (paspace : PASpace) (ttbr : (BitVec k_N)) : SailM (BitVec 56) := do
  let tablebase : (BitVec 56) := (Zeros (n := 56))
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  let granulebits : Int := (TGxGranuleBits walkparams.tgx)
  let descsizelog2 : Int :=
    if ((walkparams.d128 == 1#1) : Bool)
    then 4
    else 3
  let stride : Int := (granulebits -i descsizelog2)
  let startlevel ← (( do (AArch64_S2StartLevel walkparams) ) : SailM Int )
  let levels : Int := (FINAL_LEVEL -i startlevel)
  let tsize : Int := ((iasize -i ((levels *i stride) +i granulebits)) +i descsizelog2)
  let w__1 ← (( do
    (pure ((← do
          (Have56BitPAExt ())) && ((walkparams.d128 == 1#1) : Bool))) ) : SailM Bool )
  let (tablebase, tsize) ← (( do
    if (w__1 : Bool)
    then
      (do
        let tsize : Int := (Max.max tsize 5)
        let tablebase ← (( do
          if ((BEq.beq paspace PAS_Secure) : Bool)
          then
            (do
              ArmFull.assert (55 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:26722.38-26722.39"
              let tablebase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange tablebase 55 5 (Sail.BitVec.extractLsb ttbr 55 5))
              (pure (tablebase)))
          else
            (do
              ArmFull.assert (87 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:26725.38-26725.39"
              let tablebase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange tablebase 55 5
                  ((Sail.BitVec.extractLsb ttbr 87 80) +++ (Sail.BitVec.extractLsb ttbr 47 5)))
              (pure (tablebase))) ) : SailM (BitVec 56) )
        (pure ((tablebase, tsize))))
    else
      (do
        let w__5 ← (( do
          (pure ((← do
                (pure ((← do
                      (pure ((← do
                            (Have52BitPAExt ())) && ((BEq.beq walkparams.tgx TGx_64KB) : Bool)))) && ((walkparams.ps == 0b110#3) : Bool)))) || ((walkparams.ds == 1#1) : Bool)))
          ) : SailM Bool )
        if (w__5 : Bool)
        then
          (do
            let tsize : Int := (Max.max tsize 6)
            ArmFull.assert (5 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:26730.33-26730.34"
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:26731.34-26731.35"
            let tablebase : (BitVec 56) :=
              (Sail.BitVec.updateSubrange tablebase 51 6
                ((Sail.BitVec.extractLsb ttbr 5 2) +++ (Sail.BitVec.extractLsb ttbr 47 6)))
            (pure ((tablebase, tsize))))
        else
          (do
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-inputs/03-v8_base.sail:26734.34-26734.35"
            let tablebase : (BitVec 56) :=
              (Sail.BitVec.updateSubrange tablebase 47 1 (Sail.BitVec.extractLsb ttbr 47 1))
            (pure ((tablebase, tsize))))) ) : SailM ((BitVec 56) × Int) )
  let tsize : Int := tsize
  let tablebase : (BitVec 56) := (Align_bits tablebase (_shl_int_general 1 tsize))
  (pure (tablebase))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S2ApplyOutputPerms (descriptor : (BitVec k_N)) (walkparams : S2TTWParams) : SailM Permissions := do
  let bit_index ← (( do (undefined_int_at (← occLabel 1557) ()) ) : SailM Int )
  let permissions ← (( do (undefined_Permissions (← occLabel 1558) ()) ) : SailM Permissions )
  let s2pi_index ← (( do (undefined_bitvector_at (← occLabel 1559) 4) ) : SailM (BitVec 4) )
  let permissions ← (( do
    if ((walkparams.s2pie == 1#1) : Bool)
    then
      (do
        let s2pi_index ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (118 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26774.39-26774.40"
              let s2pi_index : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 118 115)
              (pure (s2pi_index)))
          else
            (do
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26777.38-26777.39"
              let s2pi_index : (BitVec 4) :=
                ((Sail.BitVec.extractLsb descriptor 54 53) +++ ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        descriptor 51)])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                        descriptor 6)]))))
              (pure (s2pi_index))) ) : SailM (BitVec 4) )
        let bit_index : Int := (4 *i (BitVec.toNat s2pi_index))
        let permissions : Permissions :=
          { permissions with s2pi := (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
              walkparams.s2pir (Sail.Int.toNatChecked ((bit_index +i 3)))
              (Sail.Int.toNatChecked (bit_index)))) }
        ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26782.33-26782.34"
        let permissions : Permissions :=
          { permissions with s2dirty := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor
                7)])) }
        (pure (permissions)))
    else
      (do
        ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26785.33-26785.34"
        let permissions : Permissions :=
          { permissions with s2ap := (Sail.BitVec.extractLsb descriptor 7 6) }
        let permissions ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (118 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26788.39-26788.40"
              let permissions : Permissions :=
                { permissions with s2xn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      descriptor 118)])) }
              (pure (permissions)))
          else
            (do
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26791.38-26791.39"
              let permissions : Permissions :=
                { permissions with s2xn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      descriptor 54)])) }
              (pure (permissions))) ) : SailM Permissions )
        let w__0 ← (( do (HaveExtendedExecuteNeverExt ()) ) : SailM Bool )
        let permissions ← (( do
          if (w__0 : Bool)
          then
            (do
              if ((walkparams.d128 == 1#1) : Bool)
              then
                (do
                  ArmFull.assert (117 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26796.43-26796.44"
                  let permissions : Permissions :=
                    { permissions with s2xnx := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 117)])) }
                  (pure (permissions)))
              else
                (do
                  ArmFull.assert (53 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26799.42-26799.43"
                  let permissions : Permissions :=
                    { permissions with s2xnx := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 53)])) }
                  (pure (permissions))))
          else
            (let permissions : Permissions := { permissions with s2xnx := 0#1 }
            (pure (permissions))) ) : SailM Permissions )
        let desc_dbm ← (( do (undefined_bitvector_at (← occLabel 1560) 1) ) : SailM (BitVec 1) )
        let desc_dbm ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (115 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26807.39-26807.40"
              let desc_dbm : (BitVec 1) :=
                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 115)]))
              (pure (desc_dbm)))
          else
            (do
              ArmFull.assert (51 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26810.38-26810.39"
              let desc_dbm : (BitVec 1) :=
                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 51)]))
              (pure (desc_dbm))) ) : SailM (BitVec 1) )
        let permissions : Permissions :=
          if ((((walkparams.ha == 1#1) && (walkparams.hd == 1#1)) && (desc_dbm == 1#1)) : Bool)
          then { permissions with s2ap := (BitVec.update permissions.s2ap 1 (Bit 1#1)) }
          else permissions
        (pure (permissions))) ) : SailM Permissions )
  let w__4 ← (( do
    if ((← do
         if (((walkparams.s2pie == 1#1) : Bool) : Bool)
         then
           (do
             (HaveS2POExt ()))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg VTCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_VTCR_EL2_Type_S2POE w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      if ((walkparams.d128 == 1#1) : Bool)
      then
        (do
          ArmFull.assert (124 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26820.39-26820.40"
          let permissions : Permissions :=
            { permissions with s2po_index := (Sail.BitVec.extractLsb descriptor 124 121) }
          (pure (permissions)))
      else
        (do
          ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26823.38-26823.39"
          let permissions : Permissions :=
            { permissions with s2po_index := (Sail.BitVec.extractLsb descriptor 62 59) }
          (pure (permissions))))
  else (pure (permissions))


def AArch64_VAIsOutOfRange (va_in : (BitVec 64)) (acctype : AccessType) (regime : Regime) (walkparams : S1TTWParams) : Bool :=
  let va : (BitVec 64) := va_in
  let addrtop : Int := (AArch64_AddrTop walkparams.tbid acctype walkparams.tbi)
  let va : (BitVec 64) :=
    if ((walkparams.mtx == 1#1) : Bool)
    then
      (Sail.BitVec.updateSubrange va 59 56
        (if ((BEq.beq (AArch64_GetVARange va) VARange_UPPER) : Bool)
        then 0b1111#4
        else 0b0000#4))
    else va
  let iasize : Int := (AArch64_IASize walkparams.txsz)
  if ((addrtop <b iasize) : Bool)
  then false
  else
    (if ((HasUnprivileged regime) : Bool)
    then
      (if ((BEq.beq (AArch64_GetVARange va) VARange_LOWER) : Bool)
      then (! (is_zero_subrange va addrtop iasize))
      else (! (is_ones_subrange va addrtop iasize)))
    else (! (is_zero_subrange va addrtop iasize)))


def SetPSTATE_SVCR (svcr : (BitVec 32)) : SailM Unit := do
  (SetPSTATE_SM (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access svcr 0)])))
  (SetPSTATE_ZA (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access svcr 1)])))


/-- Type quantifiers: N : Nat, N = 32 -/
def BFRound (op : real) (N : Nat) : SailM (BitVec N) := do
  ArmFull.assert (N == 32) "sail-inputs/03-v8_base.sail:32016.18-32016.19"
  ArmFull.assert (bne op (0)) "sail-inputs/03-v8_base.sail:32017.20-32017.21"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1764)
      (Sail.Int.toNatChecked (N)))) ) : SailM (BitVec N) )
  let minimum_exp : Int := (Neg.neg 126)
  let E : Nat := 8
  let F : Nat := 23
  let sign ← (( do (undefined_bitvector_at (← occLabel 1765) 1) ) : SailM (BitVec 1) )
  let mantissa ← (( do (undefined_real_at (← occLabel 1766) ()) ) : SailM real )
  let (mantissa, sign) : (real × (BitVec 1)) :=
    if ((lt_real op (0)) : Bool)
    then
      (let sign : (BitVec 1) := 1#1
      let mantissa : real := (neg_real op)
      (mantissa, sign))
    else
      (let sign : (BitVec 1) := 0#1
      let mantissa : real := op
      (mantissa, sign))
  let exponent : Int := 0
  let (exponent, mantissa) ← (( do
    let loop_vars ← sailWhileFuelM (fuel := 1048576) (fun (exponent, mantissa) => (pure (lt_real
        mantissa (1)))) (exponent, mantissa)
      fun (exponent, mantissa) => do
        (pure (let mantissa : real := (mult_real mantissa (2))
          let exponent : Int := (exponent -i 1)
          (exponent, mantissa) : (Int × real)))
    (pure loop_vars) ) : SailM (Int × real) )
  let (exponent, mantissa) ← (( do
    let loop_vars_1 ← sailWhileFuelM (fuel := 1048576) (fun (exponent, mantissa) => (pure (gteq_real
        mantissa (2)))) (exponent, mantissa)
      fun (exponent, mantissa) => do
        (pure (let mantissa : real := (div_real mantissa (2))
          let exponent : Int := (exponent +i 1)
          (exponent, mantissa) : (Int × real)))
    (pure loop_vars_1) ) : SailM (Int × real) )
  let exponent : Int := exponent
  if ((exponent <b minimum_exp) : Bool)
  then
    (do
      ((Sail.BitVec.castWidth ) <$> (FPZero sign N)))
  else
    (do
      let biased_exp : Int := (Max.max ((exponent -i minimum_exp) +i 1) 0)
      let mantissa := mantissa
      let int_mant : Int := (round_down (mult_real mantissa (real_power (2) F)))
      let error : real := (sub_real (mult_real mantissa (real_power (2) F)) (to_real int_mant))
      let int_mant : Int :=
        if ((bne error (0)) : Bool)
        then (integer_update_subrange int_mant 0 0 1#1)
        else int_mant
      let int_mant : Int := int_mant
      if ((biased_exp ≥b ((2 ^i E) -i 1)) : Bool)
      then
        (do
          ((Sail.BitVec.castWidth ) <$> (FPInfinity sign N)))
      else
        (let result : (BitVec N) :=
          (Sail.BitVec.castWidth ((sign +++ (integer_subrange biased_exp ((N -i 2) -i F) 0)) +++ (integer_subrange
              int_mant (F -i 1) 0)))
        (pure (result))))


def RMR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do readReg _RMR ) : SailM RMR_Type )
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__1 0 32)) : (BitVec 32))
      (pure (r)))
  else
    (do
      let w__2 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
      let r := ((Sail.BitVec.updateSubrange r 31 0 (BitVec.slice w__2 0 32)) : (BitVec 32))
      (pure (r)))


def RMR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : RMR_Type := value_name
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do readReg RMR_EL3 ) : SailM (BitVec 64) )
      writeReg RMR_EL3 (Sail.BitVec.updateSubrange w__1 31 0 (BitVec.slice r 0 32)))
  else
    (do
      let w__2 ← (( do readReg RMR_EL1 ) : SailM (BitVec 64) )
      writeReg RMR_EL1 (Sail.BitVec.updateSubrange w__2 31 0 (BitVec.slice r 0 32)))
  writeReg _RMR r


end ArmFull.Functions
