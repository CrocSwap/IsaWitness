import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0019
import ArmFull.Fn.M0023
import ArmFull.Fn.M0034
import ArmFull.Fn.M0040
import ArmFull.Fn.M0049
import ArmFull.Fn.M0051
import ArmFull.Fn.M0059
import ArmFull.Fn.M0061
import ArmFull.Fn.M0087
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0119
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0147
import ArmFull.Fn.M0149
import ArmFull.Fn.M0154
import ArmFull.Fn.M0156
import ArmFull.Fn.M0166
import ArmFull.Fn.M0168
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181
import ArmFull.Fn.M0183
import ArmFull.Fn.M0186
import ArmFull.Fn.M0195
import ArmFull.Fn.M0197
import ArmFull.Fn.M0203
import ArmFull.Fn.M0208
import ArmFull.Fn.M0211
import ArmFull.Fn.M0218
import ArmFull.Fn.M0226
import ArmFull.Fn.M0227
import ArmFull.Fn.M0228

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

def CreateAccDescS2TTW (accdesc_in : AccessDescriptor) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_TTW) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := accdesc_in.el }
  let accdesc : AccessDescriptor := { accdesc with ss := accdesc_in.ss }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with mpam := accdesc_in.mpam }
  (pure (accdesc))


/-- Type quantifiers: k_contiguous : Bool, k_tagchecked : Bool -/
def CreateAccDescSVENF (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SVE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with nonfault := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let w__0 ← (( do (InStreamingMode ()) ) : SailM Bool )
  let accdesc := ({ accdesc with streamingsve := w__0 } : AccessDescriptor)
  let w__2 ← (( do
    if ((accdesc.streamingsve : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode"))
    else (pure false) ) : SailM Bool )
  let accdesc : AccessDescriptor :=
    if (w__2 : Bool)
    then { accdesc with tagchecked := false }
    else { accdesc with tagchecked := tagchecked }
  let w__5 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__4 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__4.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__5 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_contiguous : Bool, k_tagchecked : Bool -/
def CreateAccDescSVEFF (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SVE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with firstfault := true }
  let accdesc : AccessDescriptor := { accdesc with first := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let w__0 ← (( do (InStreamingMode ()) ) : SailM Bool )
  let accdesc := ({ accdesc with streamingsve := w__0 } : AccessDescriptor)
  let w__2 ← (( do
    if ((accdesc.streamingsve : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode"))
    else (pure false) ) : SailM Bool )
  let accdesc : AccessDescriptor :=
    if (w__2 : Bool)
    then { accdesc with tagchecked := false }
    else { accdesc with tagchecked := tagchecked }
  let w__5 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__4 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__4.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__5 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_contiguous : Bool, k_nontemporal : Bool, k_tagchecked : Bool -/
def CreateAccDescSVE (memop : MemOp) (nontemporal : Bool) (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SVE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let w__0 ← (( do (InStreamingMode ()) ) : SailM Bool )
  let accdesc := ({ accdesc with streamingsve := w__0 } : AccessDescriptor)
  let w__2 ← (( do
    if ((accdesc.streamingsve : Bool) : Bool)
    then
      (do
        (__IMPDEF_boolean "No tag checking of SIMD&FP loads and stores in Streaming SVE mode"))
    else (pure false) ) : SailM Bool )
  let accdesc : AccessDescriptor :=
    if (w__2 : Bool)
    then { accdesc with tagchecked := false }
    else { accdesc with tagchecked := tagchecked }
  let w__5 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__4 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__4.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__5 } : AccessDescriptor)
  (pure (accdesc))


/-- Type quantifiers: k_contiguous : Bool, k_nontemporal : Bool, k_tagchecked : Bool -/
def CreateAccDescSME (memop : MemOp) (nontemporal : Bool) (contiguous : Bool) (tagchecked : Bool) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SME) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with nontemporal := nontemporal }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let accdesc : AccessDescriptor := { accdesc with pan := true }
  let accdesc : AccessDescriptor := { accdesc with contiguous := contiguous }
  let accdesc : AccessDescriptor := { accdesc with streamingsve := true }
  let w__0 ← (( do (__IMPDEF_boolean "No tag checking of SME LDR & STR instructions") ) : SailM
    Bool )
  let accdesc : AccessDescriptor :=
    if (w__0 : Bool)
    then { accdesc with tagchecked := false }
    else { accdesc with tagchecked := tagchecked }
  let w__3 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__2 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__2.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__3 } : AccessDescriptor)
  (pure (accdesc))


def CreateAccDescNV2 (memop : MemOp) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_NV2) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := EL2 }
  let w__0 ← (( do (SecurityStateAtEL EL2) ) : SailM SecurityState )
  let accdesc := ({ accdesc with ss := w__0 } : AccessDescriptor)
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  let w__3 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__2 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__2.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  let accdesc := ({ accdesc with transactional := w__3 } : AccessDescriptor)
  (pure (accdesc))


def CreateAccDescSPE (owning_ss : SecurityState) (owning_el : (BitVec 2)) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_SPE) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := owning_el }
  let accdesc : AccessDescriptor := { accdesc with ss := owning_ss }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  let w__0 ← (( do (GenMPAMatEL AccessType_SPE owning_el) ) : SailM MPAMinfo )
  let accdesc := ({ accdesc with mpam := w__0 } : AccessDescriptor)
  (pure (accdesc))


def CreateAccDescGPTW (accdesc_in : AccessDescriptor) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GPTW) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := accdesc_in.el }
  let accdesc : AccessDescriptor := { accdesc with ss := accdesc_in.ss }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with mpam := accdesc_in.mpam }
  (pure (accdesc))


def CreateAccDescGCS (el : (BitVec 2)) (memop : MemOp) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GCS) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := el }
  let accdesc : AccessDescriptor := { accdesc with read := (BEq.beq memop MemOp_LOAD) }
  let accdesc : AccessDescriptor := { accdesc with write := (BEq.beq memop MemOp_STORE) }
  (pure (accdesc))


def CreateAccDescGCSSS1 (el : (BitVec 2)) : SailM AccessDescriptor := do
  let accdesc ← (( do (NewAccDesc AccessType_GCS) ) : SailM AccessDescriptor )
  let accdesc : AccessDescriptor := { accdesc with el := el }
  let accdesc : AccessDescriptor := { accdesc with atomicop := true }
  let accdesc : AccessDescriptor := { accdesc with modop := MemAtomicOp_GCSSS1 }
  let accdesc : AccessDescriptor := { accdesc with read := true }
  let accdesc : AccessDescriptor := { accdesc with write := true }
  (pure (accdesc))


def CalculateBottomPACBit (top_bit : (BitVec 1)) : SailM Int := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let regime ← (( do (TranslationRegime w__0.EL) ) : SailM Regime )
  let ss ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
  let walkparams ← (( do (AArch64_GetS1TTWParams regime ss (BitVec.replicateBits top_bit 64)) ) :
    SailM S1TTWParams )
  let w__1 ← (( do (AArch64_PACEffectiveTxSZ regime walkparams) ) : SailM (BitVec 6) )
  let bottom_PAC_bit : Int := (64 -i (BitVec.toNat w__1))
  (pure (bottom_PAC_bit))


/-- Type quantifiers: n : Int -/
def AArch64_ReservedBreakpointType (n : Int) (bt2_in : (BitVec 1)) (bt_in : (BitVec 4)) : SailM (Constraint × (BitVec 1) × (BitVec 4)) := SailME.run do
  let bt2 : (BitVec 1) := bt2_in
  let bt : (BitVec 4) := bt_in
  let reserved : Bool := false
  let b ← (( do (NumBreakpointsImplemented ()) ) : SailME (Constraint × (BitVec 1) × (BitVec 4))
    Int )
  let w__0 ← (( do (NumContextAwareBreakpointsImplemented b) ) : SailME
    (Constraint × (BitVec 1) × (BitVec 4)) Int )
  let context_aware : Bool := (n ≥b (b -i w__0))
  let reserved ← (( do
    if ((bt2 == 0#1) : Bool)
    then
      (do
        let reserved : Bool :=
          if (((let b__1 := bt
               (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__1 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                          b__1 1 1)) == (0#1 : (BitVec 1)))) : Bool)
                 then true
                 else false : Bool))) && (! context_aware)) : Bool)
          then true
          else reserved
        let reserved : Bool :=
          if (((let b__2 := bt
               (if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__2 3 3)) == (1#1 : (BitVec 1))) : Bool)
               then true
               else false : Bool)) && (! (HaveEL EL2))) : Bool)
          then true
          else reserved
        let w__4 ← (( do
          if ((← do
               if ((let b__3 := bt
                  (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
                  then true
                  else
                    (if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__3 3 2)) == (0b11#2 : (BitVec 2))) : Bool)
                    then true
                    else false) : Bool)) : Bool)
               then
                 (do
                   let w__1 ← (( do (HaveVirtHostExt ()) ) : SailME
                     (Constraint × (BitVec 1) × (BitVec 4)) Bool )
                   (pure (((! w__1) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__3 ← (( do (HaveV82Debug ()) ) : SailME
                (Constraint × (BitVec 1) × (BitVec 4)) Bool )
              (pure (((! w__3) : Bool))))
          else (pure false) ) : SailME (Constraint × (BitVec 1) × (BitVec 4)) Bool )
        let reserved : Bool :=
          if (w__4 : Bool)
          then true
          else reserved
        let w__7 ← (( do
          (pure ((← do
                if ((let b__5 := bt
                   (if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__5 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
                   then true
                   else false : Bool)) : Bool)
                then
                  (do
                    let w__5 ← (( do (HaveFeatABLE ()) ) : SailME
                      (Constraint × (BitVec 1) × (BitVec 4)) Bool )
                    (pure (((! w__5) : Bool))))
                else (pure false)) && ((! (HaveAArch32EL EL1)) : Bool))) ) : SailME
          (Constraint × (BitVec 1) × (BitVec 4)) Bool )
        let reserved : Bool :=
          if (w__7 : Bool)
          then true
          else reserved
        (pure (reserved)))
    else
      (let reserved : Bool :=
        if ((let b__0 := bt
           (! (if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 3 3)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                      b__0 1 1)) == (0#1 : (BitVec 1)))) : Bool)
             then true
             else false : Bool))) : Bool)
        then true
        else reserved
      (pure (reserved))) ) : SailME (Constraint × (BitVec 1) × (BitVec 4)) Bool )
  let (bt, bt2) ← (( do
    if (reserved : Bool)
    then
      (do
        let c ← (( do (undefined_Constraint (← occLabel 1365) ()) ) : SailME
          (Constraint × (BitVec 1) × (BitVec 4)) Constraint )
        let w__8 ← (( do (C27bConstrainBP true context_aware) ) : SailME
          (Constraint × (BitVec 1) × (BitVec 4)) (Constraint × (BitVec 5)) )
        let (tup__0, tup__1) := (w__8 : (Constraint × (BitVec 5)))
        let c : Constraint := tup__0
        let bt2 : (BitVec 1) := (Sail.BitVec.extractLsb tup__1 4 4)
        let bt : (BitVec 4) := (Sail.BitVec.extractLsb tup__1 3 0)
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || (BEq.beq c Constraint_UNKNOWN)) "armcert/armcert_c27b.sail:362.65-362.66"
        if ((BEq.beq c Constraint_DISABLED) : Bool)
        then
          (do
            let w__9 ← (( do (__UNKNOWN_bit ()) ) : SailME
              (Constraint × (BitVec 1) × (BitVec 4)) (BitVec 1) )
            let w__10 ← (( do (__UNKNOWN_bits 4) ) : SailME
              (Constraint × (BitVec 1) × (BitVec 4)) (BitVec 4) )
            SailME.throw ((c, w__9, w__10) : (Constraint × (BitVec 1) × (BitVec 4))))
        else (pure (()))
        (pure ((bt, bt2))))
    else (pure ((bt, bt2))) ) : SailME (Constraint × (BitVec 1) × (BitVec 4))
    ((BitVec 4) × (BitVec 1)) )
  (pure ((Constraint_NONE, bt2, bt)))


/-- Type quantifiers: k_aligned : Bool -/
def AArch64_S1DisabledOutput (fault_in : FaultRecord) (regime : Regime) (va_in : (BitVec 64)) (accdesc : AccessDescriptor) (aligned : Bool) : SailM (FaultRecord × AddressDescriptor) := do
  let ipa ← (( do (undefined_AddressDescriptor (← occLabel 1460) ()) ) : SailM AddressDescriptor
    )
  let va : (BitVec 64) := va_in
  let walkparams ← (( do (AArch64_GetS1TTWParams regime accdesc.ss va) ) : SailM S1TTWParams )
  let fault : FaultRecord := fault_in
  (SetInGuardedPage false)
  let oa ← (( do (undefined_FullAddress (← occLabel 1461) ()) ) : SailM FullAddress )
  let oa : FullAddress := { oa with address := (Sail.BitVec.extractLsb va 55 0) }
  let oa : FullAddress :=
    match accdesc.ss with
    | .SS_Secure => { oa with paspace := PAS_Secure }
    | .SS_NonSecure => { oa with paspace := PAS_NonSecure }
    | .SS_Root => { oa with paspace := PAS_Root }
    | .SS_Realm => { oa with paspace := PAS_Realm }
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1462) ()) ) : SailM
    MemoryAttributes )
  let w__2 ← (( do
    (pure ((← do
          if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
          then
            (do
              (EL2Enabled ()))
          else (pure false)) && ((walkparams.dc == 1#1) : Bool))) ) : SailM Bool )
  let (memattrs, va) ← (( do
    if (w__2 : Bool)
    then
      (do
        let default_cacheability ← (( do (undefined_MemAttrHints (← occLabel 1464) ()) ) : SailM
          MemAttrHints )
        let default_cacheability : MemAttrHints := { default_cacheability with attrs := MemAttr_WB }
        let default_cacheability : MemAttrHints :=
          { default_cacheability with hints := MemHint_RWA }
        let default_cacheability : MemAttrHints := { default_cacheability with transient := false }
        let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
        let memattrs : MemoryAttributes := { memattrs with outer := default_cacheability }
        let memattrs : MemoryAttributes := { memattrs with inner := default_cacheability }
        let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_NSH }
        let (memattrs, va) : (MemoryAttributes × (BitVec 64)) :=
          if ((walkparams.dct == 1#1) : Bool)
          then
            (let memattrs : MemoryAttributes := { memattrs with tags := MemTag_AllocationTagged }
            (memattrs, va))
          else
            (let (memattrs, va) : (MemoryAttributes × (BitVec 64)) :=
              if ((walkparams.mtx == 1#1) : Bool)
              then
                (let memattrs : MemoryAttributes :=
                  { memattrs with tags := MemTag_CanonicallyTagged }
                let va : (BitVec 64) :=
                  if ((walkparams.tbi == 0#1) : Bool)
                  then
                    (Sail.BitVec.updateSubrange va 59 56
                      (BitVec.replicateBits
                        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access va 55)])) 4))
                  else va
                (memattrs, va))
              else
                (let memattrs : MemoryAttributes := { memattrs with tags := MemTag_Untagged }
                (memattrs, va))
            (memattrs, va))
        let memattrs : MemoryAttributes := { memattrs with xs := 0#1 }
        (pure ((memattrs, va))))
    else
      (do
        if ((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool)
        then
          (do
            let i_cache_attr ← (( do (undefined_MemAttrHints (← occLabel 1463) ()) ) : SailM
              MemAttrHints )
            let w__3 ← (( do (AArch64_S1ICacheEnabled regime) ) : SailM Bool )
            let i_cache_attr : MemAttrHints :=
              if (w__3 : Bool)
              then
                (let i_cache_attr : MemAttrHints := { i_cache_attr with attrs := MemAttr_WT }
                let i_cache_attr : MemAttrHints := { i_cache_attr with hints := MemHint_RA }
                { i_cache_attr with transient := false })
              else { i_cache_attr with attrs := MemAttr_NC }
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let memattrs : MemoryAttributes := { memattrs with outer := i_cache_attr }
            let memattrs : MemoryAttributes := { memattrs with inner := i_cache_attr }
            let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
            let memattrs : MemoryAttributes :=
              if ((walkparams.mtx == 1#1) : Bool)
              then { memattrs with tags := MemTag_CanonicallyTagged }
              else { memattrs with tags := MemTag_Untagged }
            let memattrs : MemoryAttributes := { memattrs with xs := 1#1 }
            (pure ((memattrs, va))))
        else
          (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
          let memattrs : MemoryAttributes := { memattrs with device := DeviceType_nGnRnE }
          let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
          let (memattrs, va) : (MemoryAttributes × (BitVec 64)) :=
            if ((walkparams.mtx == 1#1) : Bool)
            then
              (let memattrs : MemoryAttributes := { memattrs with tags := MemTag_CanonicallyTagged }
              let va : (BitVec 64) :=
                if ((walkparams.tbi == 0#1) : Bool)
                then
                  (if ((HasUnprivileged regime) : Bool)
                  then
                    (Sail.BitVec.updateSubrange va 59 56
                      (BitVec.replicateBits
                        (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access va 55)])) 4))
                  else (Sail.BitVec.updateSubrange va 59 56 0b0000#4))
                else va
              (memattrs, va))
            else
              (let memattrs : MemoryAttributes := { memattrs with tags := MemTag_Untagged }
              (memattrs, va))
          let memattrs : MemoryAttributes := { memattrs with xs := 1#1 }
          (pure ((memattrs, va))))) ) : SailM (MemoryAttributes × (BitVec 64)) )
  let memattrs : MemoryAttributes := { memattrs with notagaccess := false }
  let fault : FaultRecord := { fault with level := 0 }
  let addrtop : Int := (AArch64_AddrTop walkparams.tbid accdesc.acctype walkparams.tbi)
  let w__4 ← (( do (AArch64_PAMax ()) ) : SailM Int )
  let fault ← (( do
    if ((! (is_zero_subrange va addrtop w__4)) : Bool)
    then
      (let fault : FaultRecord := { fault with statuscode := Fault_AddressSize }
      (pure (fault)))
    else
      (do
        let w__5 ← (( do (AArch64_S1HasAlignmentFault accdesc aligned walkparams.ntlsmd memattrs)
          ) : SailM Bool )
        let fault : FaultRecord :=
          if (w__5 : Bool)
          then { fault with statuscode := Fault_Alignment }
          else fault
        (pure (fault))) ) : SailM FaultRecord )
  if ((bne fault.statuscode Fault_None) : Bool)
  then
    (do
      let w__6 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
      (pure ((fault, w__6))))
  else
    (do
      let w__7 ← (( do (CreateAddressDescriptor va_in oa memattrs) ) : SailM AddressDescriptor )
      let ipa : AddressDescriptor := (w__7 : AddressDescriptor)
      let w__8 ← (( do (AArch64_S1DisabledOutputMECID walkparams regime ipa.paddress.paspace) ) :
        SailM (BitVec 16) )
      let ipa := ({ ipa with mecid := w__8 } : AddressDescriptor)
      (pure ((fault, ipa))))


/-- Type quantifiers: size : Int -/
def AArch64_GetTranslationStartInfo (regime : Regime) (ss : SecurityState) (accdesc : AccessDescriptor) (va : (BitVec 64)) (size : Int) : SailM TranslationStartInfo := do
  let w__0 ← (( do (undefined_TGx (← occLabel 1477) ()) ) : SailM TGx )
  let tlbcontext ← (( do (AArch64_GetS1TLBContext regime ss va w__0) ) : SailM TLBContext )
  let tsi : TranslationStartInfo :=
    { ss := ss
      regime := regime
      vmid := tlbcontext.vmid
      asid := tlbcontext.asid
      va := va
      cnp := tlbcontext.cnp
      accdesc := accdesc
      size := size }
  (pure (tsi))


/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, k_vertical : Bool, width : Nat, width
  ≥ 0 -/
def ZAslice_read (tile : Int) (esize : Int) (vertical : Bool) (slice_name : Int) (width : Nat) : SailM (BitVec width) := do
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1752)
      (Sail.Int.toNatChecked (width)))) ) : SailM (BitVec width) )
  if (vertical : Bool)
  then
    (do
      ArmFull.assert (width ≥b 0) "sail-arm/v8_base.sail:31219.38-31219.39"
      ArmFull.assert (esize ≥b 0) "sail-arm/v8_base.sail:31220.38-31220.39"
      ArmFull.assert (((slice_name *i esize) ≤b (((slice_name *i esize) +i esize) -i 1)) || (! ((slice_name ≥b 0) && (((slice_name +i 1) *i esize) ≤b width)))) "sail-arm/v8_base.sail:31221.151-31221.152"
      ((Sail.BitVec.castWidth ) <$> (ZAvslice_read tile (Sail.Int.toNatChecked (esize)) slice_name
        width)))
  else
    (do
      ((Sail.BitVec.castWidth ) <$> (ZAhslice_read tile esize slice_name width)))


/-- Type quantifiers: esize : Int, slice_name : Int, tile : Int, k_vertical : Bool, width : Nat, width
  ≥ 0 -/
def ZAslice_set (tile : Int) (esize : Int) (vertical : Bool) (slice_name : Int) (width : Nat) (value_name : (BitVec width)) : SailM Unit := do
  if (vertical : Bool)
  then
    (do
      ArmFull.assert (width ≥b 0) "sail-arm/v8_base.sail:31235.38-31235.39"
      ArmFull.assert (esize ≥b 0) "sail-arm/v8_base.sail:31236.38-31236.39"
      (ZAvslice_set tile (Sail.Int.toNatChecked (esize)) slice_name width
        (Sail.BitVec.castWidth value_name)))
  else
    (do
      (ZAhslice_set tile esize slice_name width (Sail.BitVec.castWidth value_name)))


/-- Type quantifiers: k_cold : Bool -/
def ResetControlRegisters (cold : Bool) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch64_AutoGen_ArchitectureReset cold))
  else
    (do
      (AArch32_AutoGen_ArchitectureReset cold))
  (AArch32_IMPDEFResets ())
  (AArch64_IMPDEFResets ())
  (__Reset cold)


def SPEResetSampleCounter (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
  let w__1 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
  let w__2 ← (( do readReg PMSIRR_EL1 ) : SailM (BitVec 64) )
  writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__0 31 0
    (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb w__1 31 0) 31 8
      (_get_PMSIRR_EL1_Type_INTERVAL w__2)))
  let w__5 ← (( do
    if ((← do
         let w__3 ← (( do readReg PMSIRR_EL1 ) : SailM (BitVec 64) )
         (pure ((((_get_PMSIRR_EL1_Type_RND w__3) == 1#1) : Bool)))) : Bool)
    then
      (do
        let w__4 ← (( do readReg PMSIDR_EL1 ) : SailM (BitVec 64) )
        (pure ((((_get_PMSIDR_EL1_Type_ERnd w__4) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let w__6 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
      let w__7 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
      let w__8 ← (( do (SPEGetRandomInterval ()) ) : SailM (BitVec 8) )
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__6 31 0
        (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb w__7 31 0) 7 0 w__8)))
  else
    (do
      let w__9 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
      let w__10 ← (( do readReg PMSICR_EL1 ) : SailM (BitVec 64) )
      writeReg PMSICR_EL1 (Sail.BitVec.updateSubrange w__9 31 0
        (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb w__10 31 0) 7 0 (Zeros (n := 8)))))


def SPEBufferFilled (_ : Unit) : SailM Unit := do
  let w__0 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
  if ((IsZero (_get_PMBSR_EL1_Type_S w__0)) : Bool)
  then
    (do
      let w__1 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__1 17 17 1#1)
      let w__2 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__2 31 26 0b000000#6)
      let w__3 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__3 15 0
        (Sail.BitVec.zeroExtend 0b000001#6 16)))
  else (pure (()))
  (PMUEvent PMU_EVENT_SAMPLE_WRAP)


/-- Type quantifiers: total_latency : Int -/
def SPECollectRecord (events : (BitVec 64)) (total_latency : Int) (optype : OpType) : SailM Bool := do
  let w__0 ← (( do (StatisticalProfilingEnabled ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-arm/v8_base.sail:34983.40-34983.41"
  let mask : (BitVec 64) := (Sail.BitVec.zeroExtend 0xAA#8 64)
  let m ← (( do (undefined_bitvector_at (.site 2433) 64) ) : SailM (BitVec 64) )
  let w__1 ← (( do (HaveSVE ()) ) : SailM Bool )
  let mask : (BitVec 64) :=
    if (w__1 : Bool)
    then (Sail.BitVec.updateSubrange mask 18 17 0b11#2)
    else mask
  let w__2 ← (( do (HaveTME ()) ) : SailM Bool )
  let mask : (BitVec 64) :=
    if (w__2 : Bool)
    then (BitVec.update mask 16 (Bit 1#1))
    else mask
  let w__3 ← (( do (HaveStatisticalProfilingv1p1 ()) ) : SailM Bool )
  let mask : (BitVec 64) :=
    if (w__3 : Bool)
    then (BitVec.update mask 11 (Bit 1#1))
    else mask
  let w__4 ← (( do (HaveStatisticalProfilingv1p2 ()) ) : SailM Bool )
  let mask : (BitVec 64) :=
    if (w__4 : Bool)
    then (BitVec.update mask 6 (Bit 1#1))
    else mask
  let w__5 ← (( do (HaveStatisticalProfilingv1p4 ()) ) : SailM Bool )
  let mask ← (( do
    if (w__5 : Bool)
    then
      (let mask : (BitVec 64) :=
        (Sail.BitVec.updateSubrange mask 10 8 (Sail.BitVec.extractLsb 0b11111#5 4 2))
      let mask : (BitVec 64) :=
        (Sail.BitVec.updateSubrange mask 4 4 (Sail.BitVec.extractLsb 0b11111#5 1 1))
      let mask : (BitVec 64) :=
        (Sail.BitVec.updateSubrange mask 2 2 (Sail.BitVec.extractLsb 0b11111#5 0 0))
      (pure (mask)))
    else
      (do
        let impdef_mask ← (( do (__IMPDEF_bits 5 "SPE mask 10:8,4,2") ) : SailM (BitVec 5) )
        let mask : (BitVec 64) :=
          (Sail.BitVec.updateSubrange mask 10 8 (Sail.BitVec.extractLsb impdef_mask 4 2))
        let mask : (BitVec 64) :=
          (Sail.BitVec.updateSubrange mask 4 4 (Sail.BitVec.extractLsb impdef_mask 1 1))
        let mask : (BitVec 64) :=
          (Sail.BitVec.updateSubrange mask 2 2 (Sail.BitVec.extractLsb impdef_mask 0 0))
        (pure (mask))) ) : SailM (BitVec 64) )
  let w__6 ← (( do (__IMPDEF_bits 16 "SPE mask 63:48") ) : SailM (BitVec 16) )
  let mask := ((Sail.BitVec.updateSubrange mask 63 48 w__6) : (BitVec 64))
  let w__7 ← (( do (__IMPDEF_bits 8 "SPE mask 31:24") ) : SailM (BitVec 8) )
  let mask := ((Sail.BitVec.updateSubrange mask 31 24 w__7) : (BitVec 64))
  let w__8 ← (( do (__IMPDEF_bits 4 "SPE mask 15:12") ) : SailM (BitVec 4) )
  let mask := ((Sail.BitVec.updateSubrange mask 15 12 w__8) : (BitVec 64))
  let e : (BitVec 64) := (events &&& mask)
  let is_rejected_nevent : Bool := false
  let is_nevt ← (( do (undefined_bool_at (.site 2434) ()) ) : SailM Bool )
  let w__9 ← (( do (HaveStatisticalProfilingv1p2 ()) ) : SailM Bool )
  let (is_nevt, is_rejected_nevent, m) ← (( do
    if (w__9 : Bool)
    then
      (do
        let w__10 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        let m := ((w__10 &&& mask) : (BitVec 64))
        let is_nevt : Bool := (IsZero (e &&& m))
        let w__11 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        let is_rejected_nevent ← (( do
          if (((_get_PMSFCR_EL1_Type_FnE w__11) == 1#1) : Bool)
          then
            (do
              if ((! (IsZero m)) : Bool)
              then
                (let is_rejected_nevent : Bool := (! is_nevt)
                (pure (is_rejected_nevent)))
              else
                (do
                  (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
          else (pure (is_rejected_nevent)) ) : SailM Bool )
        (pure ((is_nevt, is_rejected_nevent, m))))
    else
      (let is_nevt : Bool := true
      (pure ((is_nevt, is_rejected_nevent, m)))) ) : SailM (Bool × Bool × (BitVec 64)) )
  let is_rejected_event : Bool := false
  let w__13 ← (( do readReg PMSEVFR_EL1 ) : SailM (BitVec 64) )
  let m : (BitVec 64) := (w__13 &&& mask)
  let is_evt : Bool := (IsZero ((Complement.complement e) &&& m))
  let w__14 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
  let is_rejected_event ← (( do
    if (((_get_PMSFCR_EL1_Type_FE w__14) == 1#1) : Bool)
    then
      (do
        if ((! (IsZero m)) : Bool)
        then
          (let is_rejected_event : Bool := (! is_evt)
          (pure (is_rejected_event)))
        else
          (do
            (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
    else (pure (is_rejected_event)) ) : SailM Bool )
  let w__22 ← (( do
    if ((← do
         if ((← do
              (HaveStatisticalProfilingv1p2 ())) : Bool)
         then
           (do
             let w__17 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
             let w__18 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
             (pure (((((_get_PMSFCR_EL1_Type_FnE w__17) +++ (_get_PMSFCR_EL1_Type_FE w__18)) == 0b11#2) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__20 ← (( do readReg PMSEVFR_EL1 ) : SailM (BitVec 64) )
        let w__21 ← (( do readReg PMSNEVFR_EL1 ) : SailM (BitVec 64) )
        (pure (((! (IsZero ((w__20 &&& w__21) &&& mask))) : Bool))))
    else (pure false) ) : SailM Bool )
  let (is_rejected_event, is_rejected_nevent) ← (( do
    if (w__22 : Bool)
    then
      (do
        let w__23 ← (( do (ConstrainUnpredictableBool Unpredictable_BADPMSFCR) ) : SailM Bool )
        let is_rejected_nevent := (w__23 : Bool)
        let w__24 ← (( do (ConstrainUnpredictableBool Unpredictable_BADPMSFCR) ) : SailM Bool )
        let is_rejected_event := (w__24 : Bool)
        (pure ((is_rejected_event, is_rejected_nevent))))
    else (pure ((is_rejected_event, is_rejected_nevent))) ) : SailM (Bool × Bool) )
  if ((is_evt && is_nevt) : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_FEED_EVENT))
  else (pure (()))
  let is_op_br : Bool := false
  let is_op_ld : Bool := false
  let is_op_st : Bool := false
  let is_op_br : Bool := (BEq.beq optype OpType_Branch)
  let is_op_ld : Bool := ((BEq.beq optype OpType_Load) || (BEq.beq optype OpType_LoadAtomic))
  let is_op_st : Bool := ((BEq.beq optype OpType_Store) || (BEq.beq optype OpType_LoadAtomic))
  if (is_op_br : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_FEED_BR))
  else (pure (()))
  if (is_op_ld : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_FEED_LD))
  else (pure (()))
  if (is_op_st : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_FEED_ST))
  else (pure (()))
  let is_op ← (( do
    if ((← if ((← if (is_op_br : Bool)
              then
                (do
                  let w__25 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
                  (pure ((((_get_PMSFCR_EL1_Type_B w__25) == 1#1) : Bool))))
              else (pure false)) : Bool)
         then (pure true)
         else
           if (is_op_ld : Bool)
           then
             (do
               let w__27 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
               (pure ((((_get_PMSFCR_EL1_Type_LD w__27) == 1#1) : Bool))))
           else (pure false)) : Bool)
    then (pure true)
    else
      if (is_op_st : Bool)
      then
        (do
          let w__30 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
          (pure ((((_get_PMSFCR_EL1_Type_ST w__30) == 1#1) : Bool))))
      else (pure false) ) : SailM Bool )
  if (is_op : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_FEED_OP))
  else (pure (()))
  let is_rejected_type : Bool := false
  let w__32 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
  let is_rejected_type ← (( do
    if (((_get_PMSFCR_EL1_Type_FT w__32) == 1#1) : Bool)
    then
      (do
        let w__33 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        let w__34 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        let w__35 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
        if ((! (IsZero
               ((_get_PMSFCR_EL1_Type_B w__33) +++ ((_get_PMSFCR_EL1_Type_LD w__34) +++ (_get_PMSFCR_EL1_Type_ST
                     w__35))))) : Bool)
        then
          (let is_rejected_type : Bool := (! is_op)
          (pure (is_rejected_type)))
        else
          (do
            (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
    else (pure (is_rejected_type)) ) : SailM Bool )
  let is_rejected_latency : Bool := false
  let w__37 ← (( do readReg PMSLATFR_EL1 ) : SailM (BitVec 64) )
  let is_lat : Bool := (total_latency <b (BitVec.toNat (_get_PMSLATFR_EL1_Type_MINLAT w__37)))
  if (is_lat : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_FEED_LAT))
  else (pure (()))
  let w__38 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
  let is_rejected_latency ← (( do
    if (((_get_PMSFCR_EL1_Type_FL w__38) == 1#1) : Bool)
    then
      (do
        let w__39 ← (( do readReg PMSLATFR_EL1 ) : SailM (BitVec 64) )
        if ((! (IsZero (_get_PMSLATFR_EL1_Type_MINLAT w__39))) : Bool)
        then
          (let is_rejected_latency : Bool := (! is_lat)
          (pure (is_rejected_latency)))
        else
          (do
            (ConstrainUnpredictableBool Unpredictable_BADPMSFCR)))
    else (pure (is_rejected_latency)) ) : SailM Bool )
  let is_rejected_data_source ← (( do (undefined_bool_at (.site 2435) ()) ) : SailM Bool )
  let w__46 ← (( do
    if (((← do
           if ((← do
                (HaveStatisticalProfilingFDS ())) : Bool)
           then
             (do
               let w__42 ← (( do readReg PMSFCR_EL1 ) : SailM (BitVec 64) )
               (pure ((((_get_PMSFCR_EL1_Type_FDS w__42) == 1#1) : Bool))))
           else (pure false)) && is_op_ld) : Bool)
    then
      (do
        readReg SPESampleDataSourceValid)
    else (pure false) ) : SailM Bool )
  if (w__46 : Bool)
  then
    (do
      let data_source ← (( do readReg SPESampleDataSource ) : SailM (BitVec 16) )
      let index : Int := (BitVec.toNat (Sail.BitVec.extractLsb data_source 5 0))
      let w__47 ← (( do readReg PMSDSFR_EL1 ) : SailM (BitVec 64) )
      let is_rejected_data_source :=
        (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__47 (Sail.Int.toNatChecked (index)))])) == 0#1) : Bool)
      (pure (())))
  else
    (let is_rejected_data_source : Bool := false
    (pure (())))
  let return_value : Bool :=
    (! (((is_rejected_nevent || is_rejected_event) || is_rejected_type) || is_rejected_latency))
  if (return_value : Bool)
  then
    (do
      (PMUEvent PMU_EVENT_SAMPLE_FILTRATE))
  else (pure (()))
  (pure (return_value))


end ArmFull.Functions
