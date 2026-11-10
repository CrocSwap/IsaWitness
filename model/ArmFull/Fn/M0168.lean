import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0038
import ArmFull.Fn.M0039
import ArmFull.Fn.M0042
import ArmFull.Fn.M0043
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050
import ArmFull.Fn.M0062
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0098
import ArmFull.Fn.M0100
import ArmFull.Fn.M0117
import ArmFull.Fn.M0119
import ArmFull.Fn.M0120
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0152
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0156
import ArmFull.Fn.M0158

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

def DecodeGPTTable (pgs : PGSe) (entry : (BitVec 64)) : SailM (GPCF × GPTTable) := do
  ArmFull.assert ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb entry 3 0)) == GPT_Table) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:19665.37-19665.38"
  let result ← (( do (undefined_GPTTable (← occLabel 1230) ()) ) : SailM GPTTable )
  if ((! (IsZero ((Sail.BitVec.extractLsb entry 63 52) +++ (Sail.BitVec.extractLsb entry 11 4)))) : Bool)
  then
    (do
      let w__0 ← (( do (__UNKNOWN_GPTTable ()) ) : SailM GPTTable )
      (pure ((GPCF_Walk, w__0))))
  else
    (do
      let l0sz ← (( do (GPTL0Size ()) ) : SailM Int )
      let p : Int := 12
      let p : Int :=
        match pgs with
        | .PGS_4KB => 12
        | .PGS_16KB => 14
        | .PGS_64KB => 16
      let p : Int := p
      if ((! (is_zero_subrange entry ((l0sz -i p) -i 2) 12)) : Bool)
      then
        (do
          let w__1 ← (( do (__UNKNOWN_GPTTable ()) ) : SailM GPTTable )
          (pure ((GPCF_Walk, w__1))))
      else
        (do
          let result : GPTTable :=
            match pgs with
            | .PGS_4KB =>
              { result with address := ((Sail.BitVec.extractLsb entry 55 17) +++ (Zeros (n := 17))) }
            | .PGS_16KB =>
              { result with address := ((Sail.BitVec.extractLsb entry 55 15) +++ (Zeros (n := 15))) }
            | .PGS_64KB =>
              { result with address := ((Sail.BitVec.extractLsb entry 55 13) +++ (Zeros (n := 13))) }
          let w__2 ← (( do (AbovePPS result.address) ) : SailM Bool )
          if (w__2 : Bool)
          then
            (do
              let w__3 ← (( do (__UNKNOWN_GPTTable ()) ) : SailM GPTTable )
              (pure ((GPCF_AddressSize, w__3))))
          else (pure ((GPCF_None, result)))))


def AlignmentFault (accdesc : AccessDescriptor) : SailM FaultRecord := do
  let fault ← (( do (undefined_FaultRecord (← occLabel 1251) ()) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
  let fault : FaultRecord := { fault with level := 0 }
  let fault : FaultRecord := { fault with access := accdesc }
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let fault : FaultRecord := { fault with write := ((! accdesc.read) && accdesc.write) }
  let fault : FaultRecord := { fault with gpcfs2walk := false }
  let w__0 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__0 } : FaultRecord)
  (pure (fault))


def ExclusiveFault (accdesc : AccessDescriptor) : SailM FaultRecord := do
  let fault ← (( do (undefined_FaultRecord (← occLabel 1252) ()) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := Fault_Exclusive }
  let fault : FaultRecord := { fault with access := accdesc }
  let fault : FaultRecord := { fault with secondstage := false }
  let fault : FaultRecord := { fault with s2fs1walk := false }
  let fault : FaultRecord := { fault with write := ((! accdesc.read) && accdesc.write) }
  let fault : FaultRecord := { fault with gpcfs2walk := false }
  let w__0 ← (( do (GPCNoFault ()) ) : SailM GPCFRecord )
  let fault := ({ fault with gpcf := w__0 } : FaultRecord)
  (pure (fault))


/-- Type quantifiers: k_isgeneric : Bool -/
def ComputePAC (data : (BitVec 64)) (modifier : (BitVec 64)) (key0 : (BitVec 64)) (key1 : (BitVec 64)) (isgeneric : Bool) : SailM (BitVec 64) := do
  let w__0 ← (( do (UsePACIMP isgeneric) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (ComputePACIMPDEF data modifier key0 key1))
  else
    (do
      let w__2 ← (( do (UsePACQARMA3 isgeneric) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let isqarma3 : Bool := true
          (ComputePACQARMA data modifier key0 key1 isqarma3))
      else
        (do
          let w__4 ← (( do (UsePACQARMA5 isgeneric) ) : SailM Bool )
          if (w__4 : Bool)
          then
            (do
              let isqarma3 : Bool := false
              (ComputePACQARMA data modifier key0 key1 isqarma3))
          else
            (do
              (undefined_bitvector_at (← occLabel 1291) 64))))


/-- Type quantifiers: b : Int -/
def NumContextAwareBreakpointsImplemented (b : Int) : SailM Int := do
  (C27cEnsureDebugConfig ())
  let w__0 ← (( do readReg NUM_BREAKPOINTS ) : SailM Int )
  ArmFull.assert (b == w__0) "/home/doug/boss-scratch/armcert-defects/c40-candidate/armcert-c27c.sail:103.31-103.32"
  readReg __num_ctx_breakpoints


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n < 64 -/
def AArch64_WatchpointByteMatch (n : Nat) (vaddress : (BitVec 64)) : SailM Bool := SailME.run do
  let LSB ← (( do (undefined_bitvector_at (← occLabel 1397) 8) ) : SailME Bool (BitVec 8) )
  let MSB ← (( do (undefined_bitvector_at (← occLabel 1398) 8) ) : SailME Bool (BitVec 8) )
  let top ← (( do (DebugAddrTop ()) ) : SailME Bool Int )
  let w__0 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
  let bottom : Nat :=
    (Sail.Int.toNatChecked (if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             (GetElem?.getElem! w__0 n) 2)])) == 1#1) : Bool)
    then 2
    else 3))
  let bottom : Int := bottom
  let w__1 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
  let byte_select_match : Bool :=
    ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          (_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__1 n))
          (BitVec.toNat (Sail.BitVec.extractLsb vaddress (Sail.Int.toNatChecked ((bottom -i 1))) 0)))])) != 0#1)
  let w__2 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
  let mask : Int := (BitVec.toNat (_get_DBGWCR_EL1_Type_MASK (GetElem?.getElem! w__2 n)))
  let w__4 ← (( do
    if (((mask >b 0) : Bool) : Bool)
    then
      (do
        let w__3 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        (pure (((! (IsOnes (_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__3 n)))) : Bool))))
    else (pure false) ) : SailME Bool Bool )
  let (bottom, byte_select_match) ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (ConstrainUnpredictableBool Unpredictable_WPMASKANDBAS) ) : SailME Bool
          Bool )
        let byte_select_match := (w__5 : Bool)
        (pure ((bottom, byte_select_match))))
    else
      (do
        let w__6 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let w__7 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let LSB : (BitVec 8) :=
          ((_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__6 n)) &&& (Complement.complement
              (BitVec.subInt (_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__7 n)) 1)))
        let w__8 ← (( do readReg DBGWCR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let MSB : (BitVec 8) := ((_get_DBGWCR_EL1_Type_BAS (GetElem?.getElem! w__8 n)) + LSB)
        if ((! (IsZero (MSB &&& (BitVec.subInt MSB 1)))) : Bool)
        then
          (do
            let w__9 ← (( do (ConstrainUnpredictableBool Unpredictable_WPBASCONTIGUOUS) ) : SailME
              Bool Bool )
            let byte_select_match := (w__9 : Bool)
            let bottom : Nat := 3
            (pure ((bottom, byte_select_match))))
        else (pure ((bottom, byte_select_match)))) ) : SailME Bool (Int × Bool) )
  let bottom : Int := bottom
  let mask ← (( do
    if (((mask >b 0) && (mask ≤b 2)) : Bool)
    then
      (do
        let c ← (( do (undefined_Constraint (← occLabel 1399) ()) ) : SailME Bool Constraint )
        let w__10 ← (( do (ConstrainUnpredictableInteger 3 31 Unpredictable_RESWPMASK) ) : SailME
          Bool (Constraint × Int) )
        let (tup__0, tup__1) := (w__10 : (Constraint × Int))
        let c : Constraint := tup__0
        let mask : Int := tup__1
        ArmFull.assert ((BEq.beq c Constraint_DISABLED) || ((BEq.beq c Constraint_NONE) || (BEq.beq
              c Constraint_UNKNOWN))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:23732.88-23732.89"
        match c with
        | .Constraint_DISABLED =>
          (do
            SailME.throw (false : Bool)
            (pure (mask)))
        | .Constraint_NONE => (pure (0))
        | _ => (pure (mask)))
    else (pure (mask)) ) : SailME Bool Int )
  let mask : Int := mask
  let w__16 ← (( do
    if ((← do
         if ((← do
              if (((top <b 55) : Bool) : Bool)
              then
                (do
                  let w__11 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
                  (pure (((! (is_ones_subrange (GetElem?.getElem! w__11 n) 63 top)) : Bool))))
              else (pure false)) : Bool)
         then
           (do
             let w__13 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
             (pure (((! (is_zero_subrange (GetElem?.getElem! w__13 n) 63 top)) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_DBGxVR_RESS))
    else (pure false) ) : SailME Bool Bool )
  let top : Int :=
    if (w__16 : Bool)
    then 63
    else top
  let top : Int := top
  let WVR_match ← (( do (undefined_bool_at (← occLabel 1400) ()) ) : SailME Bool Bool )
  let WVR_match ← (( do
    if ((mask >b bottom) : Bool)
    then
      (do
        ArmFull.assert ((0 ≤b mask) && ((mask ≤b top) && (top <b 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:23750.67-23750.68"
        let w__17 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let WVR_match :=
          (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (mask : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
              vaddress (Sail.Int.toNatChecked (top)) (Sail.Int.toNatChecked (mask)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
              (GetElem?.getElem! w__17 n) (Sail.Int.toNatChecked (top))
              (Sail.Int.toNatChecked (mask))))) : Bool)
        let w__19 ← (( do
          if ((WVR_match : Bool) : Bool)
          then
            (do
              let w__18 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
              (pure (((! (is_zero_subrange (GetElem?.getElem! w__18 n) (mask -i 1) bottom)) : Bool))))
          else (pure false) ) : SailME Bool Bool )
        if (w__19 : Bool)
        then
          (do
            (ConstrainUnpredictableBool Unpredictable_WPMASKEDBITS))
        else (pure (WVR_match)))
    else
      (do
        ArmFull.assert ((0 ≤b bottom) && ((bottom ≤b top) && (top <b 64))) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:23757.71-23757.72"
        let w__21 ← (( do readReg DBGWVR_EL1 ) : SailME Bool (Vector (BitVec 64) 64) )
        let WVR_match :=
          (((Sail.BitVec.castWidth (m := (Sail.Int.toNatChecked (((top : Int) -i (bottom : Int)) +i (1 : Int)))) (Sail.BitVec.extractLsb
              vaddress (Sail.Int.toNatChecked (top)) (Sail.Int.toNatChecked (bottom)))) == (Sail.BitVec.castWidth (Sail.BitVec.extractLsb
              (GetElem?.getElem! w__21 n) (Sail.Int.toNatChecked (top))
              (Sail.Int.toNatChecked (bottom))))) : Bool)
        (pure (WVR_match))) ) : SailME Bool Bool )
  (pure ((WVR_match && byte_select_match)))


/-- Type quantifiers: size : Nat, size > 0 -/
def PhysMemWrite (desc : AddressDescriptor) (size : Nat) (accdesc : AccessDescriptor) (translation_info : (Option TranslationInfo)) (data : (BitVec (8 * size))) : SailM PhysMemRetStatus := do
  let paddress := desc.paddress.address
  if (((size == 4) && ((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
           (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
           (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) GIC_BASE)))) : Bool)
  then
    (do
      (__WriteGIC (Sail.BitVec.extractLsb paddress 15 0) (Sail.BitVec.castWidth data))
      (pure ((CreatePhysMemRetStatus Fault_None))))
  else
    (do
      if (((Sail.BitVec.castWidth (m := 40) (Sail.BitVec.extractLsb paddress
             (Sail.Int.toNatChecked (((Sail.BitVec.length paddress) -i 1))) 16)) == (Sail.BitVec.castWidth (m := 40) (ZeroExtend1
             (m := (Sail.Int.toNatChecked ((((56 -i 1) -i 16) +i 1)))) UART_BASE))) : Bool)
      then
        (let _ : Unit :=
          (__WriteUART (Sail.BitVec.extractLsb paddress 15 0) size (Sail.BitVec.castWidth data))
        (pure ((CreatePhysMemRetStatus Fault_None))))
      else
        (do
          let w__0 ← (( do
            (sail_mem_write
              (write_request accdesc translation_info size desc.vaddress desc.paddress.address
                (Sail.BitVec.castWidth data))) ) : SailM (Result (Option Bool) Fault) )
          let w__1 : PhysMemRetStatus :=
            match w__0 with
            | .Ok _ => (CreatePhysMemRetStatus Fault_None)
            | .Err statuscode => (CreatePhysMemRetStatus statuscode)
          (pure (w__1))))


/-- Type quantifiers: k_N : Nat, 11 < k_N -/
def AArch64_S2ApplyFWBMemAttrs (s1_memattrs : MemoryAttributes) (walkparams : S2TTWParams) (descriptor : (BitVec k_N)) : SailM MemoryAttributes := do
  let s2_device ← (( do (undefined_DeviceType (← occLabel 1552) ()) ) : SailM DeviceType )
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1553) ()) ) : SailM
    MemoryAttributes )
  let s2_attr : (BitVec 4) := (Sail.BitVec.extractLsb descriptor 5 2)
  let s2_sh ← (( do
    if ((walkparams.ds == 1#1) : Bool)
    then (pure (walkparams.sh))
    else
      (do
        ArmFull.assert (9 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26640.33-26640.34"
        (pure ((Sail.BitVec.extractLsb descriptor 9 8)))) ) : SailM (BitVec 2) )
  let s2_fnxs : (BitVec 1) := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 11)]))
  let memattrs ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access s2_attr 2)])) == 0#1) : Bool)
    then
      (do
        let s2_device ← (( do (DecodeDevice (Sail.BitVec.extractLsb s2_attr 1 0)) ) : SailM
          DeviceType )
        let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
        let memattrs : MemoryAttributes :=
          if ((BEq.beq s1_memattrs.memtype MemType_Device) : Bool)
          then { memattrs with device := (S2CombineS1Device s1_memattrs.device s2_device) }
          else { memattrs with device := s2_device }
        let memattrs : MemoryAttributes := { memattrs with xs := s1_memattrs.xs }
        (pure (memattrs)))
    else
      (do
        if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb s2_attr 1 0)) == 0b11#2) : Bool)
        then (pure (s1_memattrs))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb s2_attr 1 0)) == 0b10#2) : Bool)
            then
              (let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
              let memattrs : MemoryAttributes :=
                { memattrs with inner := { memattrs.inner with attrs := MemAttr_WB } }
              let memattrs : MemoryAttributes :=
                { memattrs with outer := { memattrs.outer with attrs := MemAttr_WB } }
              let memattrs : MemoryAttributes :=
                if (((BEq.beq s1_memattrs.memtype MemType_Normal) && (s1_memattrs.inner.attrs != MemAttr_NC)) : Bool)
                then
                  (let memattrs : MemoryAttributes :=
                    { memattrs with inner := { memattrs.inner with hints := s1_memattrs.inner.hints } }
                  { memattrs with inner := { memattrs.inner with transient := s1_memattrs.inner.transient } })
                else
                  (let memattrs : MemoryAttributes :=
                    { memattrs with inner := { memattrs.inner with hints := MemHint_RWA } }
                  { memattrs with inner := { memattrs.inner with transient := false } })
              let memattrs : MemoryAttributes :=
                if (((BEq.beq s1_memattrs.memtype MemType_Normal) && (s1_memattrs.outer.attrs != MemAttr_NC)) : Bool)
                then
                  (let memattrs : MemoryAttributes :=
                    { memattrs with outer := { memattrs.outer with hints := s1_memattrs.outer.hints } }
                  { memattrs with outer := { memattrs.outer with transient := s1_memattrs.outer.transient } })
                else
                  (let memattrs : MemoryAttributes :=
                    { memattrs with outer := { memattrs.outer with hints := MemHint_RWA } }
                  { memattrs with outer := { memattrs.outer with transient := false } })
              let memattrs : MemoryAttributes := { memattrs with xs := 0#1 }
              (pure (memattrs)))
            else
              (do
                if ((BEq.beq s1_memattrs.memtype MemType_Device) : Bool)
                then (pure (s1_memattrs))
                else
                  (do
                    let cacheability_attr ← (( do (undefined_MemAttrHints (← occLabel 1554) ())
                      ) : SailM MemAttrHints )
                    let cacheability_attr : MemAttrHints :=
                      { cacheability_attr with attrs := MemAttr_NC }
                    let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
                    let memattrs : MemoryAttributes := { memattrs with inner := cacheability_attr }
                    let memattrs : MemoryAttributes := { memattrs with outer := cacheability_attr }
                    let memattrs : MemoryAttributes := { memattrs with xs := s1_memattrs.xs }
                    (pure (memattrs)))))) ) : SailM MemoryAttributes )
  let s2_shareability ← (( do (DecodeShareability s2_sh) ) : SailM Shareability )
  let memattrs : MemoryAttributes :=
    { memattrs with shareability := (S2CombineS1Shareability s1_memattrs.shareability
        s2_shareability) }
  let w__0 ← (( do (S2MemTagType memattrs s1_memattrs.tags) ) : SailM MemTagType )
  let memattrs := ({ memattrs with tags := w__0 } : MemoryAttributes)
  let memattrs : MemoryAttributes :=
    { memattrs with notagaccess := (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb s2_attr
            3 1)) == 0b111#3) && (BEq.beq memattrs.tags MemTag_AllocationTagged)) }
  let memattrs : MemoryAttributes :=
    if ((s2_fnxs == 1#1) : Bool)
    then { memattrs with xs := 0#1 }
    else memattrs
  let memattrs : MemoryAttributes :=
    { memattrs with shareability := (EffectiveShareability memattrs) }
  (pure (memattrs))


def AArch64_S2InitialTTWState (ss : SecurityState) (walkparams : S2TTWParams) : SailM TTWState := do
  let walkstate ← (( do (undefined_TTWState (← occLabel 1555) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1556) ()) ) : SailM FullAddress )
  let w__0 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
  let ttbr : (BitVec 128) := (Sail.BitVec.zeroExtend w__0 128)
  let tablebase : FullAddress :=
    match ss with
    | .SS_NonSecure => { tablebase with paspace := PAS_NonSecure }
    | .SS_Realm => { tablebase with paspace := PAS_Realm }
    | _ => tablebase
  let w__1 ← (( do (AArch64_S2TTBaseAddress walkparams tablebase.paspace ttbr) ) : SailM
    (BitVec 56) )
  let tablebase := ({ tablebase with address := w__1 } : FullAddress)
  let walkstate : TTWState := { walkstate with baseaddress := tablebase }
  let w__2 ← (( do (AArch64_S2StartLevel walkparams) ) : SailM Int )
  let walkstate := ({ walkstate with level := w__2 } : TTWState)
  let walkstate : TTWState := { walkstate with istable := true }
  let w__3 ← (( do (WalkMemAttrs walkparams.sh walkparams.irgn walkparams.orgn) ) : SailM
    MemoryAttributes )
  let walkstate := ({ walkstate with memattrs := w__3 } : TTWState)
  (pure (walkstate))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_S2NextWalkStateTable (currentstate : TTWState) (walkparams : S2TTWParams) (descriptor : (BitVec k_N)) : SailM TTWState := do
  let skl ← (( do (undefined_bitvector_at (← occLabel 1564) 2) ) : SailM (BitVec 2) )
  let nextstate ← (( do (undefined_TTWState (← occLabel 1565) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1566) ()) ) : SailM FullAddress )
  let w__0 ← (( do (AArch64_NextTableBase descriptor walkparams.d128 walkparams.ds walkparams.tgx)
    ) : SailM (BitVec 56) )
  let tablebase := ({ tablebase with address := w__0 } : FullAddress)
  let tablebase : FullAddress := { tablebase with paspace := currentstate.baseaddress.paspace }
  let nextstate : TTWState := { nextstate with istable := true }
  let nextstate ← (( do
    if ((walkparams.d128 == 1#1) : Bool)
    then
      (do
        ArmFull.assert (110 <b (Sail.BitVec.length descriptor)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:26911.35-26911.36"
        let skl : (BitVec 2) := (Sail.BitVec.extractLsb descriptor 110 109)
        let nextstate : TTWState :=
          { nextstate with level := ((currentstate.level +i (BitVec.toNat skl)) +i 1) }
        (pure (nextstate)))
    else
      (let nextstate : TTWState := { nextstate with level := (currentstate.level +i 1) }
      (pure (nextstate))) ) : SailM TTWState )
  let nextstate : TTWState := { nextstate with baseaddress := tablebase }
  let nextstate : TTWState := { nextstate with memattrs := currentstate.memattrs }
  (pure (nextstate))


def AArch64_SS2InitialTTWState (walkparams : S2TTWParams) (ipaspace : PASpace) : SailM TTWState := do
  let walkstate ← (( do (undefined_TTWState (← occLabel 1568) ()) ) : SailM TTWState )
  let tablebase ← (( do (undefined_FullAddress (← occLabel 1569) ()) ) : SailM FullAddress )
  let ttbr ← (( do (undefined_bitvector_at (← occLabel 1570) 128) ) : SailM (BitVec 128) )
  let ttbr ← (( do
    if ((BEq.beq ipaspace PAS_Secure) : Bool)
    then
      (do
        let w__0 ← (( do readReg VSTTBR_EL2 ) : SailM (BitVec 64) )
        let ttbr := ((Sail.BitVec.zeroExtend w__0 128) : (BitVec 128))
        (pure (ttbr)))
    else
      (do
        let w__1 ← (( do (VTTBR_EL2_read ()) ) : SailM (BitVec 128) )
        let ttbr := ((Sail.BitVec.zeroExtend w__1 128) : (BitVec 128))
        (pure (ttbr))) ) : SailM (BitVec 128) )
  let tablebase : FullAddress :=
    if ((BEq.beq ipaspace PAS_Secure) : Bool)
    then
      (if ((walkparams.sw == 0#1) : Bool)
      then { tablebase with paspace := PAS_Secure }
      else { tablebase with paspace := PAS_NonSecure })
    else
      (if ((walkparams.nsw == 0#1) : Bool)
      then { tablebase with paspace := PAS_Secure }
      else { tablebase with paspace := PAS_NonSecure })
  let w__2 ← (( do (AArch64_S2TTBaseAddress walkparams tablebase.paspace ttbr) ) : SailM
    (BitVec 56) )
  let tablebase := ({ tablebase with address := w__2 } : FullAddress)
  let walkstate : TTWState := { walkstate with baseaddress := tablebase }
  let w__3 ← (( do (AArch64_S2StartLevel walkparams) ) : SailM Int )
  let walkstate := ({ walkstate with level := w__3 } : TTWState)
  let walkstate : TTWState := { walkstate with istable := true }
  let w__4 ← (( do (WalkMemAttrs walkparams.sh walkparams.irgn walkparams.orgn) ) : SailM
    MemoryAttributes )
  let walkstate := ({ walkstate with memattrs := w__4 } : TTWState)
  (pure (walkstate))


def GCSReturnValueCheckEnabled (el : (BitVec 2)) : SailM Bool := do
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (false))
  else
    (do
      let questionMark := el
      if ((questionMark == EL0) : Bool)
      then
        (do
          let w__1 ← (( do readReg GCSCRE0_EL1 ) : SailM (BitVec 64) )
          (pure (((_get_GCSCRE0_EL1_Type_RVCHKEN w__1) == 1#1))))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let w__2 ← (( do readReg GCSCR_EL1 ) : SailM (BitVec 64) )
              (pure (((_get_GCSCR_EL1_Type_RVCHKEN w__2) == 1#1))))
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  let w__3 ← (( do readReg GCSCR_EL2 ) : SailM (BitVec 64) )
                  (pure (((_get_GCSCR_EL2_Type_RVCHKEN w__3) == 1#1))))
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      let w__4 ← (( do readReg GCSCR_EL3 ) : SailM (BitVec 64) )
                      (pure (((_get_GCSCR_EL3_Type_RVCHKEN w__4) == 1#1))))
                  else
                    (do
                      (undefined_bool_at (← occLabel 1758) ()))))))


def TLBIRange (regime : Regime) (Xt : (BitVec 64)) : SailM (Bool × (BitVec 2) × (BitVec 64) × (BitVec 64)) := do
  let valid_name : Bool := true
  let start_address : (BitVec 64) := (Zeros (n := 64))
  let end_address_name : (BitVec 64) := (Zeros (n := 64))
  let tg : (BitVec 2) := (Sail.BitVec.extractLsb Xt 47 46)
  let scale : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 45 44))
  let num : Int := (BitVec.toNat (Sail.BitVec.extractLsb Xt 43 39))
  let tg_bits : Int := 12
  if ((tg == 0b00#2) : Bool)
  then (pure ((false, tg, start_address, end_address_name)))
  else
    (do
      let (start_address, tg_bits) ← (( do
        match tg with
        | 0b01 =>
          (do
            let tg_bits : Int := 12
            let w__0 ← (( do (HasLargeAddress regime) ) : SailM Bool )
            let start_address : (BitVec 64) :=
              if (w__0 : Bool)
              then
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 53
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    11)))
              else
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 48 12 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 49
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    15)))
            (pure ((start_address, tg_bits))))
        | 0b10 =>
          (do
            let tg_bits : Int := 14
            let w__1 ← (( do (HasLargeAddress regime) ) : SailM Bool )
            let start_address : (BitVec 64) :=
              if (w__1 : Bool)
              then
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 53
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    11)))
              else
                (let start_address : (BitVec 64) :=
                  (Sail.BitVec.updateSubrange start_address 50 14 (Sail.BitVec.extractLsb Xt 36 0))
                (Sail.BitVec.updateSubrange start_address 63 51
                  (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)]))
                    13)))
            (pure ((start_address, tg_bits))))
        | 0b11 =>
          (let tg_bits : Int := 16
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 52 16 (Sail.BitVec.extractLsb Xt 36 0))
          let start_address : (BitVec 64) :=
            (Sail.BitVec.updateSubrange start_address 63 53
              (BitVec.replicateBits (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access Xt 36)])) 11))
          (pure ((start_address, tg_bits))))
        | _ =>
          (do
            (Unreachable ())
            (pure ((start_address, tg_bits)))) ) : SailM ((BitVec 64) × Int) )
      let tg_bits : Int := tg_bits
      let range : Int :=
        (Int.shiftl (num +i 1) (Sail.Int.toNatChecked ((((5 *i scale) +i 1) +i tg_bits))))
      let end_address_name : (BitVec 64) :=
        (start_address + (Sail.BitVec.castWidth (m := 64) (integer_subrange range 63 0)))
      let end_address_name : (BitVec 64) :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access end_address_name 52)])) != (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                 start_address 52)]))) : Bool)
        then
          ((BitVec.replicateBits
              (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access start_address 52)]))
              (Sail.Int.toNatChecked ((64 -i 52)))) +++ (Ones (n := 52)))
        else end_address_name
      (pure ((valid_name, tg, start_address, end_address_name))))


def AArch32_S1TTWParamsEL30 (va : (BitVec 32)) : SailM S1TTWParams := do
  let w__0 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  ArmFull.assert ((_get_TTBCR_Type_EAE w__0) == 1#1) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:37244.30-37244.31"
  let walkparams ← (( do (undefined_S1TTWParams (← occLabel 2506) ()) ) : SailM S1TTWParams )
  let w__1 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with t0sz := (_get_TTBCR_Type_T0SZ w__1) } : S1TTWParams)
  let w__2 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with t1sz := (_get_TTBCR_Type_T1SZ w__2) } : S1TTWParams)
  let w__3 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with ee := (_get_SCTLR_Type_EE w__3) } : S1TTWParams)
  let w__4 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with wxn := (_get_SCTLR_Type_WXN w__4) } : S1TTWParams)
  let w__5 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with uwxn := (_get_SCTLR_Type_UWXN w__5) } : S1TTWParams)
  let w__6 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
  let w__8 ← (( do
    if (w__6 : Bool)
    then
      (do
        let w__7 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
        (pure ((_get_SCTLR_Type_nTLSMD w__7))))
    else (pure (1#1)) ) : SailM (BitVec 1) )
  let walkparams := ({ walkparams with ntlsmd := w__8 } : S1TTWParams)
  let w__9 ← (( do (MAIR1_S_read ()) ) : SailM (BitVec 32) )
  let w__10 ← (( do (MAIR0_S_read ()) ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with mair := (Mk_MAIRType (w__9 +++ w__10)) } : S1TTWParams)
  let w__11 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let walkparams := ({ walkparams with sif := (_get_SCR_Type_SIF w__11) } : S1TTWParams)
  let varange ← (( do (AArch32_GetVARange va walkparams.t0sz walkparams.t1sz) ) : SailM VARange )
  if ((BEq.beq varange VARange_LOWER) : Bool)
  then
    (do
      let w__12 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with sh := (_get_TTBCR_Type_SH0 w__12) } : S1TTWParams)
      let w__13 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with irgn := (_get_TTBCR_Type_IRGN0 w__13) } : S1TTWParams)
      let w__14 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with orgn := (_get_TTBCR_Type_ORGN0 w__14) } : S1TTWParams)
      let w__15 ← (( do (AArch32_HaveHPDExt ()) ) : SailM Bool )
      let w__18 ← (( do
        if (w__15 : Bool)
        then
          (do
            let w__16 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
            let w__17 ← (( do readReg TTBCR2_S ) : SailM (BitVec 32) )
            (pure (((_get_TTBCR_Type_T2E w__16) &&& (_get_TTBCR2_Type_HPD0 w__17)))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let walkparams := ({ walkparams with hpd := w__18 } : S1TTWParams)
      (pure (walkparams)))
  else
    (do
      let w__19 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with sh := (_get_TTBCR_Type_SH1 w__19) } : S1TTWParams)
      let w__20 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with irgn := (_get_TTBCR_Type_IRGN1 w__20) } : S1TTWParams)
      let w__21 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
      let walkparams := ({ walkparams with orgn := (_get_TTBCR_Type_ORGN1 w__21) } : S1TTWParams)
      let w__22 ← (( do (AArch32_HaveHPDExt ()) ) : SailM Bool )
      let w__25 ← (( do
        if (w__22 : Bool)
        then
          (do
            let w__23 ← (( do readReg TTBCR_S ) : SailM (BitVec 32) )
            let w__24 ← (( do readReg TTBCR2_S ) : SailM (BitVec 32) )
            (pure (((_get_TTBCR_Type_T2E w__23) &&& (_get_TTBCR2_Type_HPD1 w__24)))))
        else (pure (0#1)) ) : SailM (BitVec 1) )
      let walkparams := ({ walkparams with hpd := w__25 } : S1TTWParams)
      (pure (walkparams)))


end ArmFull.Functions
