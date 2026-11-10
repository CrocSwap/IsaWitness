import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0018
import ArmFull.Fn.M0020
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0034
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0045
import ArmFull.Fn.M0046
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0100
import ArmFull.Fn.M0115
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0153
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167

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

def SecureOnlyImplementation (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "Secure-only implementation")


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
            ArmFull.assert ((0 ≤b n) && (n <b 31)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:5457.46-5457.47"
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
  let TS_el2 ← (( do
    if ((HaveEL EL2) : Bool)
    then
      (do
        let w__0 ← (( do readReg BRBCR_EL2 ) : SailME TimeStamp (BitVec 64) )
        let TS_el2 : (BitVec 2) := ((_get_BRBCR_EL2_Type_TS w__0) : (BitVec 2))
        let w__2 ← (( do
          (pure ((← do
                let w__1 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
                (pure (((! w__1) : Bool)))) && ((TS_el2 == 0b10#2) : Bool))) ) : SailME TimeStamp
          Bool )
        let TS_el2 ← (( do
          if (w__2 : Bool)
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
            let w__3 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
            ArmFull.assert w__3 "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:5539.33-5539.34"
            SailME.throw (TimeStamp_OffsetPhysical : TimeStamp))
        | _ =>
          (do
            SailME.throw (TimeStamp_Physical : TimeStamp))
        (pure (TS_el2)))
    else (pure (TS_el2)) ) : SailME TimeStamp (BitVec 2) )
  let TS_el2 := TS_el2
  let w__4 ← (( do readReg BRBCR_EL1 ) : SailME TimeStamp (BitVec 64) )
  let TS_el1 : (BitVec 2) := (_get_BRBCR_EL1_Type_TS w__4)
  let w__7 ← (( do
    if (((TS_el1 == 0b00#2) : Bool) : Bool)
    then (pure true)
    else
      (do
        (pure ((← do
              let w__5 ← (( do (HaveECVExt ()) ) : SailME TimeStamp Bool )
              (pure (((! w__5) : Bool)))) && ((TS_el1 == 0b10#2) : Bool)))) ) : SailME TimeStamp
    Bool )
  let TS_el1 ← (( do
    if (w__7 : Bool)
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


def NonSecureOnlyImplementation (_ : Unit) : SailM Bool := do
  (__IMPDEF_boolean "Non-secure only implementation")


def InsertIESBBeforeException (el : (BitVec 2)) : SailM Bool := do
  if ((← do
       (HaveIESB ())) : Bool)
  then
    (do
      (__IMPDEF_boolean "Has Implicit Error Synchronization Barrier before Exception"))
  else (pure false)


def ConditionSyndrome (_ : Unit) : SailM (BitVec 5) := do
  let cond ← (( do (undefined_bitvector_at (← occLabel 725) 4) ) : SailM (BitVec 4) )
  let syndrome ← (( do (undefined_bitvector_at (← occLabel 726) 5) ) : SailM (BitVec 5) )
  let w__0 ← (( do (UsingAArch32 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let cond ← (( do (AArch32_CurrentCond ()) ) : SailM (BitVec 4) )
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      if ((w__1.T == 0#1) : Bool)
      then
        (do
          let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
          let w__4 ← (( do
            if ((← do
                 (ConditionHolds cond)) : Bool)
            then
              (do
                (ConstrainUnpredictableBool Unpredictable_ESRCONDPASS))
            else (pure false) ) : SailM Bool )
          let syndrome : (BitVec 5) :=
            if (w__4 : Bool)
            then (Sail.BitVec.updateSubrange syndrome 3 0 0b1110#4)
            else (Sail.BitVec.updateSubrange syndrome 3 0 cond)
          (pure (syndrome)))
      else
        (do
          let w__5 ← (( do (__IMPDEF_boolean "Condition valid for trapped T32") ) : SailM Bool )
          if (w__5 : Bool)
          then
            (let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
            let syndrome : (BitVec 5) := (Sail.BitVec.updateSubrange syndrome 3 0 cond)
            (pure (syndrome)))
          else
            (do
              let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 0#1))
              let w__6 ← (( do (__UNKNOWN_bits 4) ) : SailM (BitVec 4) )
              let syndrome := ((Sail.BitVec.updateSubrange syndrome 3 0 w__6) : (BitVec 5))
              (pure (syndrome)))))
  else
    (let syndrome : (BitVec 5) := (BitVec.update syndrome 4 (Bit 1#1))
    let syndrome : (BitVec 5) := (Sail.BitVec.updateSubrange syndrome 3 0 0b1110#4)
    (pure (syndrome)))


def EL3SDDUndefPriority (_ : Unit) : SailM Bool := do
  if ((← do
       if ((← do
            (Halted ())) : Bool)
       then
         (do
           let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
           (pure ((((_get_EDSCR_Type_SDD w__1) == 1#1) : Bool))))
       else (pure false)) : Bool)
  then
    (do
      (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
  else (pure false)


def ICInstNeedsTranslation (opscope : CacheOpScope) : SailM Bool := do
  (__IMPDEF_boolean "Instruction Cache needs translation")


def DCInstNeedsTranslation (opscope : CacheOpScope) : SailM Bool := do
  if ((BEq.beq opscope CacheOpScope_PoE) : Bool)
  then (pure (false))
  else
    (do
      if ((BEq.beq opscope CacheOpScope_PoPA) : Bool)
      then (pure (false))
      else
        (do
          let w__0 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
          if (((_get_CLIDR_EL1_Type_LoC w__0) == 0b000#3) : Bool)
          then
            (do
              let w__1 ← (( do
                (__IMPDEF_boolean
                  "No fault generated for DC operations if PoC is before any level of cache") ) :
                SailM Bool )
              (pure ((! w__1))))
          else
            (do
              let w__3 ← (( do
                (pure ((← do
                      let w__2 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
                      (pure ((((_get_CLIDR_EL1_Type_LoUU w__2) == 0b000#3) : Bool)))) && ((BEq.beq
                      opscope CacheOpScope_PoU) : Bool))) ) : SailM Bool )
              if (w__3 : Bool)
              then
                (do
                  let w__4 ← (( do
                    (__IMPDEF_boolean
                      "No fault generated for DC operations if PoU is before any level of cache") )
                    : SailM Bool )
                  (pure ((! w__4))))
              else (pure (true)))))


/-- Type quantifiers: k_d_side : Bool -/
def AArch32_FaultSyndrome (d_side : Bool) (fault : FaultRecord) : SailM (BitVec 25) := do
  ArmFull.assert (bne fault.statuscode Fault_None) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:13640.41-13640.42"
  let iss : (BitVec 25) := (Zeros (n := 25))
  let iss2 : (BitVec 24) := (Zeros (n := 24))
  let w__2 ← (( do
    if ((← do
         (HaveRASExt ())) : Bool)
    then
      (do
        (IsAsyncAbort__1 fault))
    else (pure false) ) : SailM Bool )
  let iss ← (( do
    if (w__2 : Bool)
    then
      (do
        let errstate ← (( do (AArch32_PEErrorState fault) ) : SailM ErrorState )
        let w__3 ← (( do (AArch32_EncodeAsyncErrorSyndrome errstate) ) : SailM (BitVec 2) )
        let iss := ((Sail.BitVec.updateSubrange iss 11 10 w__3) : (BitVec 25))
        (pure (iss)))
    else (pure (iss)) ) : SailM (BitVec 25) )
  let iss ← (( do
    if (d_side : Bool)
    then
      (do
        let w__12 ← (( do
          if ((← do
               (pure ((← do
                     (IsSecondStage fault)) && ((! fault.s2fs1walk) : Bool)))) : Bool)
          then
            (do
              if ((← do
                   let w__6 ← (( do (IsExternalSyncAbort__1 fault) ) : SailM Bool )
                   (pure (((! w__6) : Bool)))) : Bool)
              then (pure true)
              else
                (do
                  if ((← do
                       (pure ((← do
                             let w__7 ← (( do (HaveRASExt ()) ) : SailM Bool )
                             (pure (((! w__7) : Bool)))) && ((BEq.beq fault.access.acctype
                             AccessType_TTW) : Bool)))) : Bool)
                  then
                    (do
                      (__IMPDEF_boolean "ISV on second stage translation table walk"))
                  else (pure false)))
          else (pure false) ) : SailM Bool )
        let iss : (BitVec 25) :=
          if (w__12 : Bool)
          then (Sail.BitVec.updateSubrange iss 24 14 (LSInstructionSyndrome ()))
          else iss
        let iss : (BitVec 25) :=
          if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
                   AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
          then (BitVec.update iss 8 (Bit 1#1))
          else iss
        if (((BEq.beq fault.access.acctype AccessType_DC) || ((BEq.beq fault.access.acctype
                 AccessType_IC) || (BEq.beq fault.access.acctype AccessType_AT))) : Bool)
        then
          (let iss : (BitVec 25) := (BitVec.update iss 6 (Bit 1#1))
          (pure (iss)))
        else
          (do
            if (((BEq.beq fault.statuscode Fault_HWUpdateAccessFlag) || (BEq.beq fault.statuscode
                   Fault_Exclusive)) : Bool)
            then
              (do
                let w__13 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                let iss := ((BitVec.update iss 6 (Bit w__13)) : (BitVec 25))
                (pure (iss)))
            else
              (do
                let w__15 ← (( do
                  if ((fault.access.atomicop : Bool) : Bool)
                  then
                    (do
                      (IsExternalAbort__1 fault))
                  else (pure false) ) : SailM Bool )
                if (w__15 : Bool)
                then
                  (do
                    let w__16 ← (( do (__UNKNOWN_bit ()) ) : SailM (BitVec 1) )
                    let iss := ((BitVec.update iss 6 (Bit w__16)) : (BitVec 25))
                    (pure (iss)))
                else
                  (let iss : (BitVec 25) :=
                    (BitVec.update iss 6
                      (Bit
                        (if (fault.write : Bool)
                        then 1#1
                        else 0#1)))
                  (pure (iss))))))
    else (pure (iss)) ) : SailM (BitVec 25) )
  let w__17 ← (( do (IsExternalAbort__1 fault) ) : SailM Bool )
  let iss : (BitVec 25) :=
    if (w__17 : Bool)
    then (BitVec.update iss 9 (Bit fault.extflag))
    else iss
  let iss : (BitVec 25) :=
    (BitVec.update iss 7
      (Bit
        (if (fault.s2fs1walk : Bool)
        then 1#1
        else 0#1)))
  let w__18 ← (( do (EncodeLDFSC fault.statuscode fault.level) ) : SailM (BitVec 6) )
  let iss := ((Sail.BitVec.updateSubrange iss 5 0 w__18) : (BitVec 25))
  (pure (iss))


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


def IsSErrorEdgeTriggered (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveDoubleFaultExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then (pure (true))
  else
    (do
      (__IMPDEF_boolean "Edge-triggered SError"))


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
            ArmFull.assert w__3 "/home/doug/boss-scratch/armcert-defects/c27b-accepted/armcert_c27b.sail:525.41-525.42"
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
            ArmFull.assert w__5 "/home/doug/boss-scratch/armcert-defects/c27b-accepted/armcert_c27b.sail:532.41-532.42"
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
            ArmFull.assert w__7 "/home/doug/boss-scratch/armcert-defects/c27b-accepted/armcert_c27b.sail:543.42-543.43"
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


def AArch64_S1TxSZFaults (regime : Regime) (walkparams : S1TTWParams) : SailM Bool := do
  let mintxsz ← (( do (AArch64_S1MinTxSZ regime walkparams.d128 walkparams.ds walkparams.tgx) ) :
    SailM Int )
  let maxtxsz ← (( do (AArch64_MaxTxSZ walkparams.tgx) ) : SailM Int )
  if (((BitVec.toNat walkparams.txsz) <b mintxsz) : Bool)
  then
    (do
      if ((← do
           (Have52BitVAExt ())) : Bool)
      then (pure true)
      else
        (do
          (__IMPDEF_boolean "Fault on TxSZ value below minimum")))
  else
    (do
      if (((BitVec.toNat walkparams.txsz) >b maxtxsz) : Bool)
      then
        (do
          (__IMPDEF_boolean "Fault on TxSZ value above maximum"))
      else (pure (false)))


end ArmFull.Functions
