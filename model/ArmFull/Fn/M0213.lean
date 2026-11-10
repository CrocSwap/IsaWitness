import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0037
import ArmFull.Fn.M0040
import ArmFull.Fn.M0041
import ArmFull.Fn.M0046
import ArmFull.Fn.M0047
import ArmFull.Fn.M0048
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0056
import ArmFull.Fn.M0057
import ArmFull.Fn.M0061
import ArmFull.Fn.M0062
import ArmFull.Fn.M0063
import ArmFull.Fn.M0070
import ArmFull.Fn.M0075
import ArmFull.Fn.M0092
import ArmFull.Fn.M0097
import ArmFull.Fn.M0117
import ArmFull.Fn.M0124
import ArmFull.Fn.M0144
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0150
import ArmFull.Fn.M0154
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0174
import ArmFull.Fn.M0178
import ArmFull.Fn.M0194
import ArmFull.Fn.M0196
import ArmFull.Fn.M0200

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

def AArch32_RemappedTEXDecode (regime : Regime) (TEX : (BitVec 3)) (C : (BitVec 1)) (B : (BitVec 1)) (s : (BitVec 1)) : SailM MemoryAttributes := do
  let NOSm ← (( do (undefined_bitvector_at (← occLabel 2592) 1) ) : SailM (BitVec 1) )
  let NSn ← (( do (undefined_bitvector_at (← occLabel 2593) 1) ) : SailM (BitVec 1) )
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 2594) ()) ) : SailM
    MemoryAttributes )
  let prrr ← (( do (undefined_PRRR_Type (← occLabel 2595) ()) ) : SailM PRRR_Type )
  let nmrr ← (( do (undefined_NMRR_Type (← occLabel 2596) ()) ) : SailM NMRR_Type )
  let region : Int :=
    (BitVec.toNat (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access TEX 0)])) +++ C) +++ B))
  if ((region == 6) : Bool)
  then
    (do
      (__IMPDEF_MemoryAttributes ""))
  else
    (do
      let (nmrr, prrr) ← (( do
        if ((BEq.beq regime Regime_EL30) : Bool)
        then
          (do
            let w__1 ← (( do readReg PRRR_S ) : SailM (BitVec 32) )
            let prrr := (w__1 : (BitVec 32))
            let w__2 ← (( do readReg NMRR_S ) : SailM (BitVec 32) )
            let nmrr := (w__2 : (BitVec 32))
            (pure ((nmrr, prrr))))
        else
          (do
            if ((HaveAArch32EL EL3) : Bool)
            then
              (do
                let w__3 ← (( do (PRRR_NS_read ()) ) : SailM (BitVec 32) )
                let prrr := (w__3 : (BitVec 32))
                let w__4 ← (( do (NMRR_NS_read ()) ) : SailM (BitVec 32) )
                let nmrr := (w__4 : (BitVec 32))
                (pure ((nmrr, prrr))))
            else
              (do
                let w__5 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
                let prrr := (w__5 : (BitVec 32))
                let w__6 ← (( do (NMRR_read ()) ) : SailM (BitVec 32) )
                let nmrr := (w__6 : (BitVec 32))
                (pure ((nmrr, prrr))))) ) : SailM ((BitVec 32) × (BitVec 32)) )
      let base : Int := (2 *i region)
      let attrfield : (BitVec 2) :=
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb prrr (Sail.Int.toNatChecked ((base +i 1)))
          (Sail.Int.toNatChecked (base))))
      let attrfield ← (( do
        if ((attrfield == 0b11#2) : Bool)
        then
          (do
            let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_RESPRRR 2) ) :
              SailM (Constraint × (BitVec 2)) )
            (pure (__tup_1)))
        else (pure (attrfield)) ) : SailM (BitVec 2) )
      let IRn ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2597)
          (Sail.Int.toNatChecked ((0 +i (((base +i 1) -i base) +i 1)))))) ) : SailM (BitVec 2) )
      let ORn ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2598)
          (Sail.Int.toNatChecked ((0 +i (((base +i 17) -i (base +i 16)) +i 1)))))) ) : SailM
        (BitVec 2) )
      let memattrs ← (( do
        match (BitVec.setWidth 2 attrfield) with
        | 0b00 =>
          (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
          let memattrs : MemoryAttributes := { memattrs with device := DeviceType_nGnRnE }
          let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
          (pure (memattrs)))
        | 0b01 =>
          (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
          let memattrs : MemoryAttributes := { memattrs with device := DeviceType_nGnRE }
          let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
          (pure (memattrs)))
        | 0b10 =>
          (do
            let NSn : (BitVec 1) :=
              if ((s == 0#1) : Bool)
              then (_get_PRRR_Type_NS0 prrr)
              else (_get_PRRR_Type_NS1 prrr)
            let NOSm : (BitVec 1) :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access prrr
                    (Sail.Int.toNatChecked ((region +i 24))))])) &&& NSn)
            let IRn : (BitVec 2) :=
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb nmrr
                (Sail.Int.toNatChecked ((base +i 1))) (Sail.Int.toNatChecked (base))))
            let ORn : (BitVec 2) :=
              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb nmrr
                (Sail.Int.toNatChecked ((base +i 17))) (Sail.Int.toNatChecked ((base +i 16)))))
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let w__7 ← (( do (DecodeSDFAttr IRn) ) : SailM MemAttrHints )
            let memattrs := ({ memattrs with inner := w__7 } : MemoryAttributes)
            let w__8 ← (( do (DecodeSDFAttr ORn) ) : SailM MemAttrHints )
            let memattrs := ({ memattrs with outer := w__8 } : MemoryAttributes)
            if (((memattrs.inner.attrs == MemAttr_NC) && (memattrs.outer.attrs == MemAttr_NC)) : Bool)
            then
              (let memattrs : MemoryAttributes := { memattrs with shareability := Shareability_OSH }
              (pure (memattrs)))
            else
              (do
                let sh : (BitVec 2) := (NSn +++ NOSm)
                let w__9 ← (( do (DecodeShareability sh) ) : SailM Shareability )
                let memattrs := ({ memattrs with shareability := w__9 } : MemoryAttributes)
                (pure (memattrs))))
        | 0b11 =>
          (do
            (Unreachable ())
            (pure (memattrs)))
        | _ => (pure (memattrs)) ) : SailM MemoryAttributes )
      let memattrs : MemoryAttributes :=
        { memattrs with inner := { memattrs.inner with transient := false } }
      let memattrs : MemoryAttributes :=
        { memattrs with outer := { memattrs.outer with transient := false } }
      let memattrs : MemoryAttributes := { memattrs with tags := MemTag_Untagged }
      let memattrs : MemoryAttributes :=
        if (((memattrs.inner.attrs == MemAttr_WB) && (memattrs.outer.attrs == MemAttr_WB)) : Bool)
        then { memattrs with xs := 0#1 }
        else { memattrs with xs := 1#1 }
      (pure (memattrs)))


def AArch32_EncodePARLD (addrdesc : AddressDescriptor) (ss : SecurityState) : SailM Unit := do
  if ((! (IsFault addrdesc)) : Bool)
  then
    (do
      let ns ← (( do (undefined_bitvector_at (← occLabel 2684) 1) ) : SailM (BitVec 1) )
      let ns ← (( do
        if ((BEq.beq ss SS_NonSecure) : Bool)
        then
          (do
            (__UNKNOWN_bit ()))
        else
          (let ns : (BitVec 1) :=
            if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
            then 0#1
            else 1#1
          (pure (ns))) ) : SailM (BitVec 1) )
      let ns : (BitVec 1) :=
        if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
        then 0#1
        else 1#1
      let w__1 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_F w__1 0#1))
      let w__2 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__3 ← (( do (ReportedPARShareability (PAREncodeShareability addrdesc.memattrs)) ) :
        SailM (BitVec 2) )
      (PAR_write (_update_PAR_Type_SH w__2 w__3))
      let w__4 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_NS w__4 ns))
      let w__5 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__6 ← (( do (__IMPDEF_bit "Non-Faulting PAR") ) : SailM (BitVec 1) )
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__5 10 10 w__6)))
      let w__7 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_LPAE w__7 1#1))
      let w__8 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_PA w__8 (Sail.BitVec.extractLsb addrdesc.paddress.address 39 12)))
      let w__9 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__10 ← (( do (EncodePARAttrs addrdesc.memattrs) ) : SailM (BitVec 8) )
      let w__11 ← (( do (ReportedPARAttrs w__10) ) : SailM (BitVec 8) )
      (PAR_write (_update_PAR_Type_ATTR w__9 w__11)))
  else
    (do
      let w__12 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_F w__12 1#1))
      let w__13 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__14 ← (( do (AArch32_PARFaultStatusLD addrdesc.fault) ) : SailM (BitVec 6) )
      (PAR_write (_update_PAR_Type_FST w__13 w__14))
      let w__15 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write
        (_update_PAR_Type_S2WLK w__15
          (if (addrdesc.fault.s2fs1walk : Bool)
          then 1#1
          else 0#1)))
      let w__16 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write
        (_update_PAR_Type_FSTAGE w__16
          (if (addrdesc.fault.secondstage : Bool)
          then 1#1
          else 0#1)))
      let w__17 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_LPAE w__17 1#1))
      let w__18 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__19 ← (( do (__IMPDEF_bits 16 "Faulting PAR") ) : SailM (BitVec 16) )
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__18 63 48 w__19))))


def AArch32_EncodePARSD (addrdesc_in : AddressDescriptor) (supersection : (BitVec 1)) (ss : SecurityState) : SailM Unit := do
  let addrdesc : AddressDescriptor := addrdesc_in
  if ((! (IsFault addrdesc)) : Bool)
  then
    (do
      let addrdesc : AddressDescriptor :=
        if (((BEq.beq addrdesc.memattrs.memtype MemType_Device) || ((addrdesc.memattrs.inner.attrs == MemAttr_NC) && (addrdesc.memattrs.outer.attrs == MemAttr_NC))) : Bool)
        then
          { addrdesc with memattrs := { addrdesc.memattrs with shareability := Shareability_OSH } }
        else addrdesc
      let ns ← (( do (undefined_bitvector_at (← occLabel 2688) 1) ) : SailM (BitVec 1) )
      let ns ← (( do
        if ((BEq.beq ss SS_NonSecure) : Bool)
        then
          (do
            (__UNKNOWN_bit ()))
        else
          (let ns : (BitVec 1) :=
            if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
            then 0#1
            else 1#1
          (pure (ns))) ) : SailM (BitVec 1) )
      let ns : (BitVec 1) :=
        if ((BEq.beq addrdesc.paddress.paspace PAS_Secure) : Bool)
        then 0#1
        else 1#1
      let sh : (BitVec 2) :=
        if ((bne addrdesc.memattrs.shareability Shareability_NSH) : Bool)
        then 0b01#2
        else 0b00#2
      let w__1 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_F w__1 0#1))
      let w__2 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_SS w__2 supersection))
      let w__3 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__4 ← (( do (AArch32_PAROuterAttrs addrdesc.memattrs) ) : SailM (BitVec 2) )
      let w__5 ← (( do (AArch32_ReportedOuterAttrs w__4) ) : SailM (BitVec 2) )
      (PAR_write (_update_PAR_Type_Outer w__3 w__5))
      let w__6 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__7 ← (( do (AArch32_PARInnerAttrs addrdesc.memattrs) ) : SailM (BitVec 3) )
      let w__8 ← (( do (AArch32_ReportedInnerAttrs w__7) ) : SailM (BitVec 3) )
      (PAR_write (_update_PAR_Type_Inner w__6 w__8))
      let w__9 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__10 ← (( do (ReportedPARShareability sh) ) : SailM (BitVec 2) )
      (PAR_write (_update_PAR_Type_SH w__9 w__10))
      let w__11 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__12 ← (( do (__IMPDEF_bit "Non-Faulting PAR") ) : SailM (BitVec 1) )
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__11 8 8 w__12)))
      let w__13 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_NS w__13 ns))
      let w__14 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write
        (_update_PAR_Type_NOS w__14
          (if ((BEq.beq addrdesc.memattrs.shareability Shareability_OSH) : Bool)
          then 0#1
          else 1#1)))
      let w__15 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_LPAE w__15 0#1))
      let w__16 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write
        (_update_PAR_Type_PA w__16 (Sail.BitVec.extractLsb addrdesc.paddress.address 39 12))))
  else
    (do
      let w__17 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_F w__17 1#1))
      let w__18 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__19 ← (( do (AArch32_PARFaultStatusSD addrdesc.fault) ) : SailM (BitVec 6) )
      (PAR_write (_update_PAR_Type_FST w__18 w__19))
      let w__20 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      (PAR_write (_update_PAR_Type_LPAE w__20 0#1))
      let w__21 ← (( do (PAR_read ()) ) : SailM (BitVec 64) )
      let w__22 ← (( do (__IMPDEF_bits 16 "Faulting PAR") ) : SailM (BitVec 16) )
      (PAR_write (Mk_PAR_Type (Sail.BitVec.updateSubrange w__21 31 16 w__22))))


def AArch32_IncrementCycleCounter (_ : Unit) : SailM Unit := do
  let w__6 ← (( do
    if ((← do
         (CountPMUEvents CYCLE_COUNTER_ID)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__1 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                  (pure ((((_get_PMCR_Type_LC w__1) == 1#1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__2 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
                 (pure ((((_get_PMCR_Type_D w__2) == 0#1) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            (HasElapsed64Cycles ())))
    else (pure false) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do (PMCCNTR_read ()) ) : SailM (BitVec 64) )
      let old_value : Int := (BitVec.toNat w__7)
      let new_value : Int := (old_value +i 1)
      (PMCCNTR_write (Mk_PMCCNTR_Type (integer_subrange new_value 63 0)))
      let w__8 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
      let ovflw : Int :=
        if (((_get_PMCR_Type_LC w__8) == 1#1) : Bool)
        then 64
        else 32
      if (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((64 : Int) -i (ovflw : Int)) +i (1 : Int)))) (integer_subrange
             old_value 64 ovflw)) != (Sail.BitVec.castWidth (integer_subrange new_value 64 ovflw))) : Bool)
      then
        (do
          let w__9 ← (( do (PMOVSSET_read ()) ) : SailM (BitVec 32) )
          (PMOVSSET_write (_update_PMOVSSET_Type_C w__9 1#1))
          let w__10 ← (( do (PMOVSR_read ()) ) : SailM (BitVec 32) )
          (PMOVSR_write (_update_PMOVSR_Type_C w__10 1#1)))
      else (pure (())))
  else (pure (()))


def __set_HCPTR (value_name : (BitVec 32)) : SailM Unit := do
  let r : HCPTR_Type := value_name
  let w__0 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (Mk_HCPTR_Type (set_slice 10 w__0 0 (BitVec.slice r 0 10))))
  let w__1 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
  (HCPTR_write (Mk_HCPTR_Type (set_slice 20 w__1 12 (BitVec.slice r 12 20))))
  let w__7 ← (( do
    if ((← do
         if ((← do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL3))
              else (pure false)) : Bool)
         then
           (do
             let w__4 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
             (pure (((! w__4) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__6 ← (( do readReg NSACR ) : SailM (BitVec 32) )
        (pure ((((_get_NSACR_Type_cp10 w__6) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if ((! w__7) : Bool)
  then
    (do
      let w__8 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TCP11 w__8 (_get_HCPTR_Type_TCP11 r))))
  else (pure (()))
  let w__14 ← (( do
    if ((← do
         if ((← do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL3))
              else (pure false)) : Bool)
         then
           (do
             let w__11 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
             (pure (((! w__11) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__13 ← (( do readReg NSACR ) : SailM (BitVec 32) )
        (pure ((((_get_NSACR_Type_cp10 w__13) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if ((! w__14) : Bool)
  then
    (do
      let w__15 ← (( do (HCPTR_read ()) ) : SailM (BitVec 32) )
      (HCPTR_write (_update_HCPTR_Type_TCP10 w__15 (_get_HCPTR_Type_TCP10 r))))
  else (pure (()))


def MAIR0_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR0_Type := value_name
  let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (PRRR_NS_read ()) ) : SailM (BitVec 32) )
      (PRRR_NS_write (Mk_PRRR_Type (set_slice 32 w__1 0 (BitVec.slice r 0 32)))))
  else
    (do
      let w__3 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            (pure (((! w__2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
          writeReg MAIR_EL1 (Sail.BitVec.updateSubrange w__4 31 0 (BitVec.slice r 0 32)))
      else
        (do
          let w__5 ← (( do (PRRR_read ()) ) : SailM (BitVec 32) )
          (PRRR_write (Mk_PRRR_Type (set_slice 32 w__5 0 (BitVec.slice r 0 32))))))
  writeReg _MAIR0_NS r


def __set_CPACR (value_name : (BitVec 32)) : SailM Unit := do
  let r : CPACR_Type := value_name
  let w__0 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (Mk_CPACR_Type (set_slice 20 w__0 0 (BitVec.slice r 0 20))))
  let w__1 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
  (CPACR_write (Mk_CPACR_Type (set_slice 8 w__1 24 (BitVec.slice r 24 8))))
  let w__7 ← (( do
    if ((← do
         if ((← do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL3))
              else (pure false)) : Bool)
         then
           (do
             let w__4 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
             (pure (((! w__4) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__6 ← (( do readReg NSACR ) : SailM (BitVec 32) )
        (pure ((((_get_NSACR_Type_cp10 w__6) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if ((! w__7) : Bool)
  then
    (do
      let w__8 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
      (CPACR_write (_update_CPACR_Type_cp11 w__8 (_get_CPACR_Type_cp11 r))))
  else (pure (()))
  let w__14 ← (( do
    if ((← do
         if ((← do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL3))
              else (pure false)) : Bool)
         then
           (do
             let w__11 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
             (pure (((! w__11) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__13 ← (( do readReg NSACR ) : SailM (BitVec 32) )
        (pure ((((_get_NSACR_Type_cp10 w__13) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if ((! w__14) : Bool)
  then
    (do
      let w__15 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
      (CPACR_write (_update_CPACR_Type_cp10 w__15 (_get_CPACR_Type_cp10 r))))
  else (pure (()))


def MAIR1_NS_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : MAIR1_Type := value_name
  let w__0 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (NMRR_NS_read ()) ) : SailM (BitVec 32) )
      (NMRR_NS_write (Mk_NMRR_Type (set_slice 32 w__1 0 (BitVec.slice r 0 32)))))
  else
    (do
      let w__3 ← (( do
        if (((! (HaveEL EL3)) : Bool) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
            (pure (((! w__2) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do readReg MAIR_EL1 ) : SailM (BitVec 64) )
          writeReg MAIR_EL1 (Sail.BitVec.updateSubrange w__4 63 32 (BitVec.slice r 0 32)))
      else
        (do
          let w__5 ← (( do (NMRR_read ()) ) : SailM (BitVec 32) )
          (NMRR_write (Mk_NMRR_Type (set_slice 32 w__5 0 (BitVec.slice r 0 32))))))
  writeReg _MAIR1_NS r


def __get_HCPTR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : HCPTR_Type := value_name
  let tmp : HCPTR_Type :=
    (Mk_HCPTR_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
          (Sail.BitVec.zeroExtend 0xCCC4000#28 32)))))
  let w__5 ← (( do
    if ((← do
         if ((← do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL3))
              else (pure false)) : Bool)
         then
           (do
             let w__2 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
             (pure (((! w__2) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do readReg NSACR ) : SailM (BitVec 32) )
        (pure ((((_get_NSACR_Type_cp10 w__4) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if (w__5 : Bool)
    then
      (Mk_HCPTR_Type
        ((Sail.BitVec.castWidth (m := 32) (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
              (Sail.BitVec.zeroExtend 0x0#4 32))))) ||| (Sail.BitVec.castWidth (m := 32) (Sail.BitVec.zeroExtend
            0xC00#12 32))))
    else tmp
  (pure (tmp))


def __get_CPACR (value_name : (BitVec 32)) : SailM (BitVec 32) := do
  let tmp : CPACR_Type := value_name
  let tmp : CPACR_Type := (Mk_CPACR_Type (tmp &&& (Complement.complement 0x4C0CFFFF#32)))
  let w__5 ← (( do
    if ((← do
         if ((← do
              if (((HaveEL EL3) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL3))
              else (pure false)) : Bool)
         then
           (do
             let w__2 ← (( do (IsCurrentSecurityState SS_Secure) ) : SailM Bool )
             (pure (((! w__2) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__4 ← (( do readReg NSACR ) : SailM (BitVec 32) )
        (pure ((((_get_NSACR_Type_cp10 w__4) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 32) :=
    if (w__5 : Bool)
    then
      (Mk_CPACR_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 32) (Complement.complement
            (Sail.BitVec.zeroExtend 0xF00000#24 32)))))
    else tmp
  (pure (tmp))


/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegRead_4af9bde7d3ab9efe (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FIQ : (BitVec 1) := (_get_SCR_EL3_Type_FIQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL0 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL0 w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegRead_51434e4b9d244793 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FIQ : (BitVec 1) := (_get_SCR_EL3_Type_FIQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL0 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL0 w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICC_AP0R_EL1_SysRegRead_c718785136d493b9 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FIQ : (BitVec 1) := (_get_SCR_EL3_Type_FIQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL0 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL0 w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_FMO : (BitVec 1) := (_get_HCR_EL2_Type_FMO w__5)
  let w__6 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__6)
  let w__7 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__7)
  sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def ICC_AP1R_EL1_SysRegRead_39371d4468952849 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
  let __EDSCR_SDD : (BitVec 1) := (_get_EDSCR_Type_SDD w__1)
  let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_IRQ : (BitVec 1) := (_get_SCR_EL3_Type_IRQ w__2)
  let w__3 ← (( do (ICC_SRE_EL1_read ()) ) : SailM (BitVec 64) )
  let __ICC_SRE_EL1_SRE : (BitVec 1) := (_get_ICC_SRE_EL1_Type_SRE w__3)
  let w__4 ← (( do readReg ICH_HCR_EL2 ) : SailM (BitVec 64) )
  let __ICH_HCR_EL2_TALL1 : (BitVec 1) := (_get_ICH_HCR_EL2_Type_TALL1 w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_IMO : (BitVec 1) := (_get_HCR_EL2_Type_IMO w__5)
  let w__6 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_NS : (BitVec 1) := (_get_SCR_EL3_Type_NS w__6)
  let w__7 ← (( do readReg ICC_SRE_EL2 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL2_SRE : (BitVec 1) := (_get_ICC_SRE_EL2_Type_SRE w__7)
  let w__8 ← (( do readReg ICC_SRE_EL3 ) : SailM (BitVec 64) )
  let __ICC_SRE_EL3_SRE : (BitVec 1) := (_get_ICC_SRE_EL3_Type_SRE w__8)
  sailThrow ((Error_Undefined ()))


end ArmFull.Functions
