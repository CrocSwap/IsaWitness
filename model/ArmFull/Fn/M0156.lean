import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0017
import ArmFull.Fn.M0019
import ArmFull.Fn.M0038
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0051
import ArmFull.Fn.M0098
import ArmFull.Fn.M0117
import ArmFull.Fn.M0119
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147

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

/-- Type quantifiers: k_aligned : Bool -/
def AArch64_S1HasAlignmentFault (accdesc : AccessDescriptor) (aligned : Bool) (ntlsmd : (BitVec 1)) (memattrs : MemoryAttributes) : SailM Bool := do
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
        (pure (if ((accdesc.a32lsmd && (ntlsmd == 0#1)) : Bool)
          then ((BEq.beq memattrs.memtype MemType_Device) && (bne memattrs.device DeviceType_GRE))
          else
            (if ((BEq.beq accdesc.acctype AccessType_DCZero) : Bool)
            then (BEq.beq memattrs.memtype MemType_Device)
            else ((BEq.beq memattrs.memtype MemType_Device) && (! aligned))))))


def AArch64_TLBContextEL2 (ss : SecurityState) (va : (BitVec 64)) (tg : TGx) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1473) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL2 }
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := va }
  let w__0 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  let w__2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
        (pure ((_get_TTBR0_EL2_Type_CnP w__1))))
    else (pure (0#1)) ) : SailM (BitVec 1) )
  let tlbcontext := ({ tlbcontext with cnp := w__2 } : TLBContext)
  (pure (tlbcontext))


def AArch64_TLBContextEL20 (ss : SecurityState) (va : (BitVec 64)) (tg : TGx) : SailM TLBContext := do
  let tlbcontext ← (( do (undefined_TLBContext (← occLabel 1474) ()) ) : SailM TLBContext )
  let tlbcontext : TLBContext := { tlbcontext with ss := ss }
  let tlbcontext : TLBContext := { tlbcontext with regime := Regime_EL20 }
  let w__0 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let w__3 ← (( do
    if (((_get_TCR_EL2_Type_A1 w__0) == 0#1) : Bool)
    then
      (do
        let w__1 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
        (pure ((_get_TTBR0_EL2_Type_ASID w__1))))
    else
      (do
        let w__2 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
        (pure ((_get_TTBR1_EL2_Type_ASID w__2)))) ) : SailM (BitVec 16) )
  let tlbcontext := ({ tlbcontext with asid := w__3 } : TLBContext)
  let w__4 ← (( do readReg TCR_EL2 ) : SailM (BitVec 64) )
  let tlbcontext : TLBContext :=
    if (((_get_TCR_EL2_Type_AS w__4) == 0#1) : Bool)
    then
      { tlbcontext with asid := (Sail.BitVec.updateSubrange tlbcontext.asid 15 8 (Zeros (n := 8))) }
    else tlbcontext
  let tlbcontext : TLBContext := { tlbcontext with tg := tg }
  let tlbcontext : TLBContext := { tlbcontext with ia := va }
  let w__5 ← (( do (HaveCommonNotPrivateTransExt ()) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      if ((BEq.beq (AArch64_GetVARange va) VARange_LOWER) : Bool)
      then
        (do
          let w__6 ← (( do (TTBR0_EL2_read ()) ) : SailM (BitVec 128) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR0_EL2_Type_CnP w__6) } : TLBContext)
          (pure (tlbcontext)))
      else
        (do
          let w__7 ← (( do readReg TTBR1_EL2 ) : SailM (BitVec 128) )
          let tlbcontext := ({ tlbcontext with cnp := (_get_TTBR1_EL2_Type_CnP w__7) } : TLBContext)
          (pure (tlbcontext))))
  else
    (let tlbcontext : TLBContext := { tlbcontext with cnp := 0#1 }
    (pure (tlbcontext)))


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
              ArmFull.assert (55 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:25229.38-25229.39"
              let tablebase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange tablebase 55 5 (Sail.BitVec.extractLsb ttbr 55 5))
              (pure (tablebase)))
          else
            (do
              ArmFull.assert (87 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:25232.38-25232.39"
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
            ArmFull.assert (5 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:25237.33-25237.34"
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:25238.34-25238.35"
            let tablebase : (BitVec 56) :=
              (Sail.BitVec.updateSubrange tablebase 51 6
                ((Sail.BitVec.extractLsb ttbr 5 2) +++ (Sail.BitVec.extractLsb ttbr 47 6)))
            (pure ((tablebase, tsize))))
        else
          (do
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:25241.34-25241.35"
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
  ArmFull.assert ((0 ≤b leafsize) && ((leafsize ≤b 47) && (47 <b (Sail.BitVec.length descriptor)))) "sail-arm/v8_base.sail:25326.67-25326.68"
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
      ArmFull.assert (55 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25329.34-25329.35"
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
              ArmFull.assert (49 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25336.34-25336.35"
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
  ArmFull.assert w__2 "sail-arm/v8_base.sail:25347.48-25347.49"
  if ((index >b 7) : Bool)
  then
    (do
      let bit_index : Int := (bit_index -i 64)
      ArmFull.assert ((0 ≤b bit_index) && ((bit_index ≤b (bit_index +i 7)) && ((bit_index +i 7) <b 64))) "sail-arm/v8_base.sail:25350.97-25350.98"
      (pure ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb mair2
          (Sail.Int.toNatChecked ((bit_index +i 7))) (Sail.Int.toNatChecked (bit_index)))))))
  else
    (do
      let bit_index : Int := bit_index
      ArmFull.assert ((0 ≤b bit_index) && ((bit_index ≤b (bit_index +i 7)) && ((bit_index +i 7) <b 64))) "sail-arm/v8_base.sail:25354.97-25354.98"
      (pure ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb mair
          (Sail.Int.toNatChecked ((bit_index +i 7))) (Sail.Int.toNatChecked (bit_index)))))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_NextTableBase (descriptor : (BitVec k_N)) (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) : SailM (BitVec 56) := do
  let tablebase : (BitVec 56) := (Zeros (n := 56))
  let tablebase ← (( do
    match tgx with
    | .TGx_4KB =>
      (do
        ArmFull.assert (47 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25539.36-25539.37"
        let tablebase : (BitVec 56) :=
          (Sail.BitVec.updateSubrange tablebase 47 12 (Sail.BitVec.extractLsb descriptor 47 12))
        (pure (tablebase)))
    | .TGx_16KB =>
      (do
        ArmFull.assert (47 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25543.36-25543.37"
        let tablebase : (BitVec 56) :=
          (Sail.BitVec.updateSubrange tablebase 47 14 (Sail.BitVec.extractLsb descriptor 47 14))
        (pure (tablebase)))
    | .TGx_64KB =>
      (do
        ArmFull.assert (47 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25547.36-25547.37"
        let tablebase : (BitVec 56) :=
          (Sail.BitVec.updateSubrange tablebase 47 16 (Sail.BitVec.extractLsb descriptor 47 16))
        (pure (tablebase))) ) : SailM (BitVec 56) )
  let w__1 ← (( do
    (pure ((← do
          (Have56BitPAExt ())) && ((d128 == 1#1) : Bool))) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      ArmFull.assert (55 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25552.34-25552.35"
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
          ArmFull.assert (15 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25557.34-25557.35"
          let tablebase : (BitVec 56) :=
            (Sail.BitVec.updateSubrange tablebase 51 48 (Sail.BitVec.extractLsb descriptor 15 12))
          (pure (tablebase)))
      else
        (do
          if ((ds == 1#1) : Bool)
          then
            (do
              ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25562.33-25562.34"
              ArmFull.assert (49 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:25563.34-25563.35"
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
              ArmFull.assert (55 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:26712.38-26712.39"
              let tablebase : (BitVec 56) :=
                (Sail.BitVec.updateSubrange tablebase 55 5 (Sail.BitVec.extractLsb ttbr 55 5))
              (pure (tablebase)))
          else
            (do
              ArmFull.assert (87 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:26715.38-26715.39"
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
            ArmFull.assert (5 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:26720.33-26720.34"
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:26721.34-26721.35"
            let tablebase : (BitVec 56) :=
              (Sail.BitVec.updateSubrange tablebase 51 6
                ((Sail.BitVec.extractLsb ttbr 5 2) +++ (Sail.BitVec.extractLsb ttbr 47 6)))
            (pure ((tablebase, tsize))))
        else
          (do
            ArmFull.assert (47 <b (Sail.BitVec.length ttbr)) "sail-arm/v8_base.sail:26724.34-26724.35"
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
              ArmFull.assert (118 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26764.39-26764.40"
              let s2pi_index : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 118 115)
              (pure (s2pi_index)))
          else
            (do
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26767.38-26767.39"
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
        ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26772.33-26772.34"
        let permissions : Permissions :=
          { permissions with s2dirty := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor
                7)])) }
        (pure (permissions)))
    else
      (do
        ArmFull.assert (7 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26775.33-26775.34"
        let permissions : Permissions :=
          { permissions with s2ap := (Sail.BitVec.extractLsb descriptor 7 6) }
        let permissions ← (( do
          if ((walkparams.d128 == 1#1) : Bool)
          then
            (do
              ArmFull.assert (118 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26778.39-26778.40"
              let permissions : Permissions :=
                { permissions with s2xn := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                      descriptor 118)])) }
              (pure (permissions)))
          else
            (do
              ArmFull.assert (54 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26781.38-26781.39"
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
                  ArmFull.assert (117 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26786.43-26786.44"
                  let permissions : Permissions :=
                    { permissions with s2xnx := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                          descriptor 117)])) }
                  (pure (permissions)))
              else
                (do
                  ArmFull.assert (53 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26789.42-26789.43"
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
              ArmFull.assert (115 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26797.39-26797.40"
              let desc_dbm : (BitVec 1) :=
                (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 115)]))
              (pure (desc_dbm)))
          else
            (do
              ArmFull.assert (51 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26800.38-26800.39"
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
          ArmFull.assert (124 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26810.39-26810.40"
          let permissions : Permissions :=
            { permissions with s2po_index := (Sail.BitVec.extractLsb descriptor 124 121) }
          (pure (permissions)))
      else
        (do
          ArmFull.assert (62 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:26813.38-26813.39"
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


end ArmFull.Functions
