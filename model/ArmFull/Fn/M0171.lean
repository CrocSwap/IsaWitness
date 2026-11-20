module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0018
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0061
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0153
public import ArmFull.Fn.M0155
public import ArmFull.Fn.M0166
public import ArmFull.Fn.M0167
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0170 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: Vb : Int, n : Nat, 0 ≤ n ∧ n < 31 -/
def PMUCountValue (n : Nat) (Vb : Int) : SailM Int := do
  let Vp ← (( do (undefined_bool_at (← occLabel 545) ()) ) : SailM Bool )
  let tc ← (( do (undefined_bitvector_at (← occLabel 546) 2) ) : SailM (BitVec 2) )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HavePMUv3TH ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveAArch64 ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (Vb))
  else
    (do
      let w__3 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
      let T : Int := (BitVec.toNat (_get_PMEVTYPER_EL0_Type_TH (GetElem?.getElem! w__3 n)))
      let Vc ← (( do (undefined_bool_at (← occLabel 547) ()) ) : SailM Bool )
      let w__4 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
      let Vc : Bool :=
        match (BitVec.setWidth 2 (Sail.BitVec.extractLsb
          (_get_PMEVTYPER_EL0_Type_TC (GetElem?.getElem! w__4 n)) 2 1)) with
        | 0b00 => (Vb != T)
        | 0b01 => (Vb == T)
        | 0b10 => (Vb ≥b T)
        | 0b11 => (Vb <b T)
        | _ => Vc
      let Vt ← (( do (undefined_int_at (← occLabel 548) ()) ) : SailM Int )
      let w__5 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
      let Vt : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 (_get_PMEVTYPER_EL0_Type_TC (GetElem?.getElem! w__5 n)) 0)])) == 0#1) : Bool)
        then
          (if (Vc : Bool)
          then Vb
          else 0)
        else
          (if (Vc : Bool)
          then 1
          else 0)
      let Vt : Int := Vt
      let v ← (( do (undefined_int_at (← occLabel 549) ()) ) : SailM Int )
      let w__8 ← (( do
        if ((← do
             (HavePMUv3EDGE ())) : Bool)
        then
          (do
            let w__7 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
            (pure ((((_get_PMEVTYPER_EL0_Type_TE (GetElem?.getElem! w__7 n)) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      let v ← (( do
        if (w__8 : Bool)
        then
          (do
            ArmFull.assert ((0 ≤b n) && (n <b 31)) "sail-inputs/03-v8_base.sail:5457.46-5457.47"
            let w__9 ← (( do readReg PMULastThresholdValue ) : SailM (Vector Bool 31) )
            let Vp : Bool := (GetElem?.getElem! w__9 n)
            let w__10 ← (( do readReg PMEVTYPER_EL0 ) : SailM (Vector (BitVec 64) 32) )
            let tc : (BitVec 2) :=
              ((Sail.BitVec.extractLsb (_get_PMEVTYPER_EL0_Type_TC (GetElem?.getElem! w__10 n)) 1 0) : (BitVec 2))
            let tc ← (( do
              if ((tc == 0b00#2) : Bool)
              then
                (do
                  let c ← (( do (undefined_Constraint (← occLabel 550) ()) ) : SailM Constraint
                    )
                  let w__11 ← (( do (ConstrainUnpredictableBits Unpredictable_RESTC 2) ) : SailM
                    (Constraint × (BitVec 2)) )
                  let (tup__0, tup__1) := (w__11 : (Constraint × (BitVec 2)))
                  let c : Constraint := tup__0
                  let tc : (BitVec 2) := tup__1
                  let tc : (BitVec 2) :=
                    if ((BEq.beq c Constraint_DISABLED) : Bool)
                    then 0b00#2
                    else tc
                  (pure (tc)))
              else (pure (tc)) ) : SailM (BitVec 2) )
            let v : Int :=
              match tc with
              | 0b00 => Vt
              | 0b10 =>
                (if ((neq_bool Vp Vc) : Bool)
                then 1
                else 0)
              | b__0 =>
                (if (((! Vp) && Vc) : Bool)
                then 1
                else 0)
            (pure (v)))
        else (pure (Vt)) ) : SailM Int )
      let v : Int := v
      let w__12 ← (( do readReg PMULastThresholdValue ) : SailM (Vector Bool 31) )
      writeReg PMULastThresholdValue (vectorUpdate w__12 n Vc)
      (pure (v)))


def BRBETimeStamp (_ : Unit) : SailM TimeStamp := SailME.run do
  let TS_el2 ← (( do (undefined_bitvector_at (.site 553) 2) ) : SailME TimeStamp (BitVec 2) )
  let w__0 ← (( do (HaveEL EL2) ) : SailME TimeStamp Bool )
  let TS_el2 ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do readReg BRBCR_EL2 ) : SailME TimeStamp (BitVec 64) )
        let TS_el2 : (BitVec 2) := ((_get_BRBCR_EL2_Type_TS w__1) : (BitVec 2))
        let w__3 ← (( do
          (pure ((← do
                let w__2 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
                (pure (((! w__2) : Bool)))) && ((TS_el2 == 0b10#2) : Bool))) ) : SailME TimeStamp
          Bool )
        let TS_el2 ← (( do
          if (w__3 : Bool)
          then
            (do
              let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_EL2TIMESTAMP 2) )
                : SailME TimeStamp (Constraint × (BitVec 2)) )
              (pure (__tup_1)))
          else (pure (TS_el2)) ) : SailME TimeStamp (BitVec 2) )
        match TS_el2 with
        | 0b00 => (pure (()))
        | 0b01 =>
          (do
            SailME.throw (TimeStamp_Virtual : TimeStamp))
        | 0b10 =>
          (do
            let w__4 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
            ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:5539.33-5539.34"
            SailME.throw (TimeStamp_OffsetPhysical : TimeStamp))
        | _ =>
          (do
            SailME.throw (TimeStamp_Physical : TimeStamp))
        (pure (TS_el2)))
    else (pure (TS_el2)) ) : SailME TimeStamp (BitVec 2) )
  let TS_el2 := TS_el2
  let w__5 ← (( do readReg BRBCR_EL1 ) : SailME TimeStamp (BitVec 64) )
  let TS_el1 : (BitVec 2) := (_get_BRBCR_EL1_Type_TS w__5)
  let w__8 ← (( do
    if (((TS_el1 == 0b00#2) : Bool) : Bool)
    then (pure true)
    else
      (do
        (pure ((← do
              let w__6 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
              (pure (((! w__6) : Bool)))) && ((TS_el1 == 0b10#2) : Bool)))) ) : SailME TimeStamp
    Bool )
  let TS_el1 ← (( do
    if (w__8 : Bool)
    then
      (do
        let (_, __tup_1) ← (( do (ConstrainUnpredictableBits Unpredictable_EL1TIMESTAMP 2) ) :
          SailME TimeStamp (Constraint × (BitVec 2)) )
        (pure (__tup_1)))
    else (pure (TS_el1)) ) : SailME TimeStamp (BitVec 2) )
  match TS_el1 with
  | 0b01 => (pure (TimeStamp_Virtual))
  | 0b10 => (pure (TimeStamp_OffsetPhysical))
  | 0b11 => (pure (TimeStamp_Physical))
  | _ =>
    (do
      (Unreachable ())
      (undefined_TimeStamp (.site 554) ()))


def GetTimestamp (timeStampType : TimeStamp) : SailM (BitVec 64) := do
  match timeStampType with
  | .TimeStamp_Physical =>
    (do
      (PhysicalCountInt ()))
  | .TimeStamp_Virtual =>
    (do
      let w__1 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do readReg CNTVOFF_EL2 ) : SailM (BitVec 64) )
      (pure ((w__1 - w__2))))
  | .TimeStamp_OffsetPhysical =>
    (do
      let w__3 ← (( do (PhysicalOffsetIsValid ()) ) : SailM Bool )
      let physoff ← (( do
        if (w__3 : Bool)
        then
          (do
            readReg CNTPOFF_EL2)
        else (pure ((Zeros (n := 64)))) ) : SailM (BitVec 64) )
      let w__5 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
      (pure ((w__5 - physoff))))
  | .TimeStamp_None => (pure ((Zeros (n := 64))))
  | .TimeStamp_CoreSight =>
    (do
      (__IMPDEF_bits 64 "Coresight timestamp"))


def UsePrimarySpaceEL2 (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
  if (((_get_MPAM3_EL3_Type_ALTSP_HEN w__0) == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      (pure (((_get_MPAM3_EL3_Type_ALTSP_HFC w__1) == 0#1))))
  else
    (do
      if ((← do
           let w__2 ← (( do (MPAMisEnabled ()) ) : SailM Bool )
           (pure (((! w__2) : Bool)))) : Bool)
      then (pure true)
      else
        (do
          let w__3 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          (pure ((((_get_MPAM2_EL2_Type_ALTSP_EL2 w__3) == 0#1) : Bool)))))


/-- Type quantifiers: k_long_format : Bool -/
def AArch32_CommonFaultStatus (fault : FaultRecord) (long_format : Bool) : SailM (BitVec 32) := do
  let target : (BitVec 32) := (Zeros (n := 32))
  let w__2 ← (( do
    if ((← do
         (HaveRASExt ())) : Bool)
    then
      (do
        (IsAsyncAbort__1 fault))
    else (pure false) ) : SailM Bool )
  let target ← (( do
    if (w__2 : Bool)
    then
      (do
        let errstate ← (( do (AArch32_PEErrorState fault) ) : SailM ErrorState )
        let w__3 ← (( do (AArch32_EncodeAsyncErrorSyndrome errstate) ) : SailM (BitVec 2) )
        let target := ((Sail.BitVec.updateSubrange target 15 14 w__3) : (BitVec 32))
        (pure (target)))
    else (pure (target)) ) : SailM (BitVec 32) )
  let w__4 ← (( do (IsExternalAbort__1 fault) ) : SailM Bool )
  let target : (BitVec 32) :=
    if (w__4 : Bool)
    then (BitVec.update target 12 (Bit fault.extflag))
    else target
  let target : (BitVec 32) :=
    (BitVec.update target 9
      (Bit
        (if (long_format : Bool)
        then 1#1
        else 0#1)))
  if (long_format : Bool)
  then
    (do
      let w__5 ← (( do (EncodeLDFSC fault.statuscode fault.level) ) : SailM (BitVec 6) )
      let target := ((Sail.BitVec.updateSubrange target 5 0 w__5) : (BitVec 32))
      (pure (target)))
  else
    (do
      let split_vec ← (( do (EncodeSDFSC fault.statuscode fault.level) ) : SailM (BitVec 5) )
      let target : (BitVec 32) :=
        (Sail.BitVec.updateSubrange target 10 10 (Sail.BitVec.extractLsb split_vec 4 4))
      let target : (BitVec 32) :=
        (Sail.BitVec.updateSubrange target 3 0 (Sail.BitVec.extractLsb split_vec 3 0))
      (pure (target)))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def S1DecodeMemAttrs (attr_in : (BitVec 8)) (sh : (BitVec 2)) (s1aarch64 : Bool) (walkparams : S1TTWParams) : SailM MemoryAttributes := do
  let attr : (BitVec 8) := attr_in
  let w__0 ← (( do (S1ConstrainUnpredictableRESMAIR attr s1aarch64) ) : SailM Bool )
  let attr ← (( do
    if (w__0 : Bool)
    then
      (do
        (C27bMAIR s1aarch64))
    else (pure (attr)) ) : SailM (BitVec 8) )
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1219) ()) ) : SailM
    MemoryAttributes )
  let b__0 := attr
  let memattrs ← (( do
    if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 7 4)) == (0x0#4 : (BitVec 4))) : Bool)
    then
      (do
        let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
        let w__1 ← (( do (DecodeDevice (Sail.BitVec.extractLsb attr 3 2)) ) : SailM DeviceType )
        let memattrs := ({ memattrs with device := w__1 } : MemoryAttributes)
        let memattrs : MemoryAttributes :=
          { memattrs with xs := if (s1aarch64 : Bool)
            then (Complement.complement (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access attr 0)])))
            else 1#1 }
        (pure (memattrs)))
    else
      (do
        match b__0 with
        | 0b01000000 =>
          (do
            let w__3 ← (( do
              if ((s1aarch64 : Bool) : Bool)
              then
                (do
                  (HaveFeatXS ()))
              else (pure false) ) : SailM Bool )
            ArmFull.assert w__3 "sail-inputs/27-armcert_c27b.sail:525.41-525.42"
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let memattrs : MemoryAttributes :=
              { memattrs with outer := { memattrs.outer with attrs := MemAttr_NC } }
            let memattrs : MemoryAttributes :=
              { memattrs with inner := { memattrs.inner with attrs := MemAttr_NC } }
            let memattrs : MemoryAttributes := { memattrs with xs := 0#1 }
            (pure (memattrs)))
        | 0b10100000 =>
          (do
            let w__5 ← (( do
              if ((s1aarch64 : Bool) : Bool)
              then
                (do
                  (HaveFeatXS ()))
              else (pure false) ) : SailM Bool )
            ArmFull.assert w__5 "sail-inputs/27-armcert_c27b.sail:532.41-532.42"
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let memattrs : MemoryAttributes :=
              { memattrs with outer := { memattrs.outer with attrs := MemAttr_WT } }
            let memattrs : MemoryAttributes :=
              { memattrs with outer := { memattrs.outer with hints := MemHint_RA } }
            let memattrs : MemoryAttributes :=
              { memattrs with outer := { memattrs.outer with transient := false } }
            let memattrs : MemoryAttributes :=
              { memattrs with inner := { memattrs.inner with attrs := MemAttr_WT } }
            let memattrs : MemoryAttributes :=
              { memattrs with inner := { memattrs.inner with hints := MemHint_RA } }
            let memattrs : MemoryAttributes :=
              { memattrs with inner := { memattrs.inner with transient := false } }
            let memattrs : MemoryAttributes := { memattrs with xs := 0#1 }
            (pure (memattrs)))
        | 0b11110000 =>
          (do
            let w__7 ← (( do
              if ((s1aarch64 : Bool) : Bool)
              then
                (do
                  (HaveMTE2Ext ()))
              else (pure false) ) : SailM Bool )
            ArmFull.assert w__7 "sail-inputs/27-armcert_c27b.sail:543.42-543.43"
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let memattrs : MemoryAttributes :=
              { memattrs with outer := { memattrs.outer with attrs := MemAttr_WB } }
            let memattrs : MemoryAttributes :=
              { memattrs with outer := { memattrs.outer with hints := MemHint_RWA } }
            let memattrs : MemoryAttributes :=
              { memattrs with outer := { memattrs.outer with transient := false } }
            let memattrs : MemoryAttributes :=
              { memattrs with inner := { memattrs.inner with attrs := MemAttr_WB } }
            let memattrs : MemoryAttributes :=
              { memattrs with inner := { memattrs.inner with hints := MemHint_RWA } }
            let memattrs : MemoryAttributes :=
              { memattrs with inner := { memattrs.inner with transient := false } }
            let memattrs : MemoryAttributes := { memattrs with xs := 0#1 }
            (pure (memattrs)))
        | _ =>
          (do
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let w__8 ← (( do (DecodeLDFAttr (Sail.BitVec.extractLsb attr 7 4)) ) : SailM
              MemAttrHints )
            let memattrs := ({ memattrs with outer := w__8 } : MemoryAttributes)
            let w__9 ← (( do (DecodeLDFAttr (Sail.BitVec.extractLsb attr 3 0)) ) : SailM
              MemAttrHints )
            let memattrs := ({ memattrs with inner := w__9 } : MemoryAttributes)
            let memattrs : MemoryAttributes :=
              if (((memattrs.inner.attrs == MemAttr_WB) && (memattrs.outer.attrs == MemAttr_WB)) : Bool)
              then { memattrs with xs := 0#1 }
              else { memattrs with xs := 1#1 }
            (pure (memattrs)))) ) : SailM MemoryAttributes )
  let memattrs : MemoryAttributes :=
    if ((s1aarch64 && (attr == 0b11110000#8)) : Bool)
    then { memattrs with tags := MemTag_AllocationTagged }
    else
      (if ((s1aarch64 && (walkparams.mtx == 1#1)) : Bool)
      then { memattrs with tags := MemTag_CanonicallyTagged }
      else { memattrs with tags := MemTag_Untagged })
  let memattrs : MemoryAttributes := { memattrs with notagaccess := false }
  let w__10 ← (( do (DecodeShareability sh) ) : SailM Shareability )
  let memattrs := ({ memattrs with shareability := w__10 } : MemoryAttributes)
  (pure (memattrs))


def CreateAddressDescriptor (va : (BitVec 64)) (pa : FullAddress) (memattrs : MemoryAttributes) : SailM AddressDescriptor := do
  let addrdesc ← (( do (undefined_AddressDescriptor (← occLabel 1249) ()) ) : SailM
    AddressDescriptor )
  let addrdesc : AddressDescriptor := { addrdesc with paddress := pa }
  let addrdesc : AddressDescriptor := { addrdesc with vaddress := va }
  let addrdesc : AddressDescriptor := { addrdesc with memattrs := memattrs }
  let w__0 ← (( do (NoFault ()) ) : SailM FaultRecord )
  let addrdesc := ({ addrdesc with fault := w__0 } : AddressDescriptor)
  let addrdesc : AddressDescriptor := { addrdesc with s1assured := false }
  (pure (addrdesc))


def CreateFaultyAddressDescriptor (va : (BitVec 64)) (fault : FaultRecord) : SailM AddressDescriptor := do
  let addrdesc ← (( do (undefined_AddressDescriptor (← occLabel 1250) ()) ) : SailM
    AddressDescriptor )
  let addrdesc : AddressDescriptor := { addrdesc with vaddress := va }
  let addrdesc : AddressDescriptor := { addrdesc with fault := fault }
  (pure (addrdesc))


/-- Type quantifiers: k_N : Nat, 52 < k_N -/
def AArch64_S2NextWalkStateLeaf (currentstate : TTWState) (ss : SecurityState) (walkparams : S2TTWParams) (ipa : AddressDescriptor) (descriptor : (BitVec k_N)) : SailM TTWState := do
  let s2aarch64 ← (( do (undefined_bool_at (← occLabel 1561) ()) ) : SailM Bool )
  let nextstate ← (( do (undefined_TTWState (← occLabel 1562) ()) ) : SailM TTWState )
  let baseaddress ← (( do (undefined_FullAddress (← occLabel 1563) ()) ) : SailM FullAddress )
  let baseaddress ← (( do
    if ((BEq.beq ss SS_Secure) : Bool)
    then
      (let baseaddress : FullAddress :=
        { baseaddress with paspace := (AArch64_SS2OutputPASpace walkparams ipa.paddress.paspace) }
      (pure (baseaddress)))
    else
      (do
        if ((BEq.beq ss SS_Realm) : Bool)
        then
          (do
            let ns ← (( do
              if ((walkparams.d128 == 1#1) : Bool)
              then
                (do
                  ArmFull.assert (127 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26859.39-26859.40"
                  (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 127)])))))
              else
                (do
                  ArmFull.assert (55 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26862.38-26862.39"
                  (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 55)]))))) ) :
              SailM (BitVec 1) )
            let baseaddress : FullAddress :=
              { baseaddress with paspace := if ((ns == 1#1) : Bool)
                then PAS_NonSecure
                else PAS_Realm }
            (pure (baseaddress)))
        else
          (let baseaddress : FullAddress := { baseaddress with paspace := PAS_NonSecure }
          (pure (baseaddress)))) ) : SailM FullAddress )
  let w__0 ← (( do
    (AArch64_LeafBase descriptor walkparams.d128 walkparams.ds walkparams.tgx currentstate.level) )
    : SailM (BitVec 56) )
  let baseaddress := ({ baseaddress with address := w__0 } : FullAddress)
  let nextstate : TTWState := { nextstate with istable := false }
  let nextstate : TTWState := { nextstate with level := currentstate.level }
  let nextstate : TTWState := { nextstate with baseaddress := baseaddress }
  let w__1 ← (( do (AArch64_S2ApplyOutputPerms descriptor walkparams) ) : SailM Permissions )
  let nextstate := ({ nextstate with permissions := w__1 } : TTWState)
  let s2_attr : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 5 2)
  let s2_sh ← (( do
    if ((walkparams.ds == 1#1) : Bool)
    then (pure (walkparams.sh))
    else
      (do
        ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26876.33-26876.34"
        (pure ((Sail.BitVec.extractLsb descriptor 9 8)))) ) : SailM (BitVec 2) )
  let s2_fnxs : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)]))
  let nextstate ← (( do
    if ((walkparams.fwb == 1#1) : Bool)
    then
      (do
        let w__2 ← (( do (AArch64_S2ApplyFWBMemAttrs ipa.memattrs walkparams descriptor) ) : SailM
          MemoryAttributes )
        let nextstate := ({ nextstate with memattrs := w__2 } : TTWState)
        let nextstate : TTWState :=
          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb s2_attr 3 1)) == 0b111#3) : Bool)
          then { nextstate with permissions := { nextstate.permissions with s2tag_na := 1#1 } }
          else { nextstate with permissions := { nextstate.permissions with s2tag_na := 0#1 } }
        (pure (nextstate)))
    else
      (do
        let s2aarch64 : Bool := true
        let w__3 ← (( do (S2DecodeMemAttrs s2_attr s2_sh s2aarch64) ) : SailM MemoryAttributes )
        let nextstate := ({ nextstate with memattrs := w__3 } : TTWState)
        let nextstate : TTWState :=
          { nextstate with memattrs := { nextstate.memattrs with xs := (Complement.complement
                s2_fnxs) } }
        let nextstate : TTWState :=
          if ((s2_attr == 0b0100#4) : Bool)
          then { nextstate with permissions := { nextstate.permissions with s2tag_na := 1#1 } }
          else { nextstate with permissions := { nextstate.permissions with s2tag_na := 0#1 } }
        (pure (nextstate))) ) : SailM TTWState )
  let w__4 ← (( do
    (AArch64_ContiguousBit walkparams.tgx walkparams.d128 currentstate.level descriptor) ) : SailM
    (BitVec 1) )
  let nextstate := ({ nextstate with contiguous := w__4 } : TTWState)
  if ((walkparams.d128 == 1#1) : Bool)
  then
    (do
      ArmFull.assert (114 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26899.35-26899.36"
      let nextstate : TTWState :=
        { nextstate with s2assuredonly := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              descriptor 114)])) }
      (pure (nextstate)))
  else
    (do
      let w__5 ← (( do
        if ((walkparams.assuredonly == 1#1) : Bool)
        then
          (do
            ArmFull.assert (58 <b (Sail.BitVec.length descriptor)) "sail-inputs/03-v8_base.sail:26903.38-26903.39"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 58)])))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let nextstate := ({ nextstate with s2assuredonly := w__5 } : TTWState)
      (pure (nextstate)))


def GetPendingPhysicalSError (_ : Unit) : SailM FaultRecord := do
  let fault ← (( do (__UNKNOWN_FaultRecord ()) ) : SailM FaultRecord )
  let w__0 ← (( do (undefined_bool_at (← occLabel 1918) ()) ) : SailM Bool )
  let w__1 : Fault :=
    if ((w__0 : Bool) : Bool)
    then Fault_AsyncExternal
    else Fault_AsyncParity
  let fault := ({ fault with statuscode := w__1 } : FaultRecord)
  let w__2 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__2 } : FaultRecord)
  let fault : FaultRecord := { fault with level := 0 }
  (pure (fault))


def DebugWriteFault (vaddress : (BitVec 64)) (fault : FaultRecord) : SailM Unit := do
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 2439) 64) ) : SailM (BitVec 64) )
  let syndrome ← (( do
    match fault.access.acctype with
    | .AccessType_SPE =>
      (do
        let w__0 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
        let syndrome := ((Sail.BitVec.extractLsb w__0 63 0) : (BitVec 64))
        (pure (syndrome)))
    | _ =>
      (do
        (Unreachable ())
        (pure (syndrome))) ) : SailM (BitVec 64) )
  let w__1 ← (( do (EncodeLDFSC fault.statuscode fault.level) ) : SailM (BitVec 6) )
  let syndrome :=
    ((Sail.BitVec.updateSubrange syndrome 15 0 ((Zeros (n := 10)) +++ w__1)) : (BitVec 64))
  let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 55 32 (Zeros (n := 24)))
  let ec ← (( do (undefined_bitvector_at (← occLabel 2440) 6) ) : SailM (BitVec 6) )
  let w__4 ← (( do
    (pure ((← do
          (pure ((← do
                (HaveRME ())) && ((bne fault.gpcf.gpf GPCF_None) : Bool)))) && ((bne fault.gpcf.gpf
          GPCF_Fail) : Bool))) ) : SailM Bool )
  let ec : (BitVec 6) :=
    if (w__4 : Bool)
    then 0b011110#6
    else
      (if (fault.secondstage : Bool)
      then 0b100101#6
      else 0b100100#6)
  let syndrome : (BitVec 64) := (Sail.BitVec.updateSubrange syndrome 31 26 ec)
  let syndrome : (BitVec 64) := (BitVec.update syndrome 17 (Bit 1#1))
  let syndrome : (BitVec 64) :=
    if ((BEq.beq fault.statuscode Fault_Permission) : Bool)
    then
      (let syndrome : (BitVec 64) :=
        (BitVec.update syndrome 39
          (Bit
            (if (fault.assuredonly : Bool)
            then 1#1
            else 0#1)))
      let syndrome : (BitVec 64) :=
        (BitVec.update syndrome 38
          (Bit
            (if (fault.overlay : Bool)
            then 1#1
            else 0#1)))
      (BitVec.update syndrome 37
        (Bit
          (if (fault.dirtybit : Bool)
          then 1#1
          else 0#1))))
    else syndrome
  match fault.access.acctype with
  | .AccessType_SPE =>
    (do
      let w__5 ← (( do readReg PMBSR_EL1 ) : SailM (BitVec 64) )
      writeReg PMBSR_EL1 (Sail.BitVec.updateSubrange w__5 63 0 syndrome))
  | _ =>
    (do
      (Unreachable ()))


def AArch64_TLBI_RVA (security : SecurityState) (regime : Regime) (vmid : (BitVec 16)) (shareability : Shareability) (level : TLBILevel) (attr : TLBIMemAttr) (Xt : (BitVec 64)) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure (((w__0.EL == EL3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL2) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__2.EL == EL1) : Bool))))) ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:36307.65-36307.66"
  let r ← (( do (undefined_TLBIRecord (← occLabel 2472) ()) ) : SailM TLBIRecord )
  let r : TLBIRecord := { r with op := TLBIOp_RVA }
  let r : TLBIRecord := { r with from_aarch64 := true }
  let r : TLBIRecord := { r with security := security }
  let r : TLBIRecord := { r with regime := regime }
  let r : TLBIRecord := { r with vmid := vmid }
  let r : TLBIRecord := { r with level := level }
  let r : TLBIRecord := { r with attr := attr }
  let r : TLBIRecord := { r with asid := (Sail.BitVec.extractLsb Xt 63 48) }
  let r : TLBIRecord :=
    { r with ttl := (Sail.BitVec.updateSubrange r.ttl 1 0 (Sail.BitVec.extractLsb Xt 38 37)) }
  let r : TLBIRecord := { r with d64 := true }
  let r : TLBIRecord :=
    { r with d128 := ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb r.ttl 1 0)) == 0b00#2) }
  let valid_name ← (( do (undefined_bool_at (← occLabel 2473) ()) ) : SailM Bool )
  let w__5 ← (( do (TLBIRange regime Xt) ) : SailM
    (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) )
  let (tup__0, tup__1, tup__2, tup__3) :=
    (w__5 : (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)))
  let valid_name : Bool := tup__0
  let r : TLBIRecord := { r with tg := tup__1 }
  let r : TLBIRecord := { r with address := tup__2 }
  let r : TLBIRecord := { r with end_address_name := tup__3 }
  if ((! valid_name) : Bool)
  then (pure (()))
  else
    (do
      (TLBI r shareability)
      let _ : Unit :=
        if ((bne shareability Shareability_NSH) : Bool)
        then (Broadcast shareability r)
        else ()
      (pure (())))


end ArmFull.Functions
