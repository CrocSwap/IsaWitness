import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0017
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0043
import ArmFull.Fn.M0044
import ArmFull.Fn.M0046
import ArmFull.Fn.M0087
import ArmFull.Fn.M0097
import ArmFull.Fn.M0099
import ArmFull.Fn.M0100
import ArmFull.Fn.M0113
import ArmFull.Fn.M0115
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146

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

/-- Type quantifiers: k_N : Nat, y : Int, k_N ≥ 0 -/
def IsAligned__1 (x : (BitVec k_N)) (y : Int) : Bool :=
  (x == (Align_bits x y))


def EffectiveSCR_EL3_NSE (_ : Unit) : SailM (BitVec 1) := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (0#1))
  else
    (do
      let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
      (pure ((_get_SCR_EL3_Type_NSE w__1))))


def PLOfEL (el : (BitVec 2)) : SailM PrivilegeLevel := do
  let questionMark := el
  if ((questionMark == EL3) : Bool)
  then
    (do
      let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
      let w__1 : PrivilegeLevel :=
        if ((! w__0) : Bool)
        then PL1
        else PL3
      (pure (w__1)))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then (pure (PL2))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then (pure (PL1))
          else
            (do
              if ((questionMark == EL0) : Bool)
              then (pure (PL0))
              else
                (do
                  (undefined_PrivilegeLevel (← occLabel 668) ())))))


def PFAR_set (regime : (BitVec 2)) (value_name : (BitVec 64)) : SailM Unit := do
  let r : (BitVec 64) := value_name
  let w__3 ← (( do
    if ((← do
         (HavePFAR ())) : Bool)
    then (pure true)
    else
      (do
        (pure ((← do
              (HaveRME ())) && ((regime == EL3) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__3 "sail-arm/v8_base.sail:9300.49-9300.50"
  let questionMark := regime
  if ((questionMark == EL1) : Bool)
  then
    (do
      writeReg PFAR_EL1 (Mk_PFAR_EL1_Type r))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          writeReg PFAR_EL2 (Mk_PFAR_EL2_Type r))
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              writeReg MFAR_EL3 (Mk_MFAR_EL3_Type r))
          else
            (do
              (Unreachable ()))))


def EffectiveEA (_ : Unit) : SailM (BitVec 1) := do
  let w__2 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then
      (do
        let w__1 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
        (pure ((((_get_EDSCR_Type_SDD w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (0#1))
  else
    (do
      let w__3 ← (( do (HaveAArch64 ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
          (pure ((_get_SCR_EL3_Type_EA w__4))))
      else
        (do
          let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
          (pure ((_get_SCR_Type_EA w__5)))))


def ExceptionSyndrome (exceptype : Exception) : SailM ExceptionRecord := do
  let r ← (( do (undefined_ExceptionRecord (← occLabel 721) ()) ) : SailM ExceptionRecord )
  let r : ExceptionRecord := { r with exceptype := exceptype }
  let r : ExceptionRecord := { r with syndrome := (Zeros (n := 25)) }
  let r : ExceptionRecord := { r with syndrome2 := (Zeros (n := 24)) }
  let r : ExceptionRecord := { r with vaddress := (Zeros (n := 64)) }
  let r : ExceptionRecord := { r with ipavalid := false }
  let r : ExceptionRecord := { r with pavalid := false }
  let r : ExceptionRecord := { r with NS := 0#1 }
  let r : ExceptionRecord := { r with ipaddress := (Zeros (n := 56)) }
  let w__0 ← (( do (__UNKNOWN_PASpace ()) ) : SailM PASpace )
  let r := ({ r with paddress := { r.paddress with paspace := w__0 } } : ExceptionRecord)
  let w__1 ← (( do (__UNKNOWN_bits 56) ) : SailM (BitVec 56) )
  let r := ({ r with paddress := { r.paddress with address := w__1 } } : ExceptionRecord)
  let r : ExceptionRecord := { r with trappedsyscallinst := false }
  (pure (r))


def AArch64_ExecutingBROrBLROrRetInstr (_ : Unit) : SailM Bool := do
  let opc ← (( do (undefined_bitvector_at (← occLabel 722) 4) ) : SailM (BitVec 4) )
  let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      (pure (if ((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb instr 31 25)) == 0b1101011#7) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                 instr 20 16)) == 0b11111#5)) : Bool)
        then
          (let opc : (BitVec 4) := (Sail.BitVec.extractLsb instr 24 21)
          (opc != 0b0101#4))
        else false)))


def AArch64_ExecutingBTIInstr (_ : Unit) : SailM Bool := do
  let CRm ← (( do (undefined_bitvector_at (← occLabel 723) 4) ) : SailM (BitVec 4) )
  let op2 ← (( do (undefined_bitvector_at (← occLabel 724) 3) ) : SailM (BitVec 3) )
  let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
      (pure (if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb instr 31 22)) == 0b1101010100#10) && ((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                   instr 21 12)) == 0b0000110010#10)) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                 instr 4 0)) == 0b11111#5)) : Bool)
        then
          (let CRm : (BitVec 4) := (Sail.BitVec.extractLsb instr 11 8)
          let op2 : (BitVec 3) := (Sail.BitVec.extractLsb instr 7 5)
          ((CRm == 0b0100#4) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op2 0)])) == 0#1)))
        else false)))


/-- Type quantifiers: localtimeout : Int -/
def WaitForEvent (localtimeout : Int) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         (IsEventRegisterSet ())) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             (HaveFeatWFxT ())) : Bool)
        then
          (do
            (LocalTimeoutEvent localtimeout))
        else (pure false)) ) : SailM Bool )
  if ((! w__4) : Bool)
  then
    (do
      writeReg IsWFEsleep true
      let w__5 ← (( do readReg _DormantCtlReg ) : SailM (BitVec 32) )
      writeReg _DormantCtlReg (Sail.BitVec.updateSubrange w__5 10 10 1#1)
      (pure ((EnterLowPowerState ()))))
  else (pure (()))


/-- Type quantifiers: localtimeout : Int -/
def WaitForInterrupt (localtimeout : Int) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaveFeatWFxT ())) : Bool)
    then
      (do
        (LocalTimeoutEvent localtimeout))
    else (pure false) ) : SailM Bool )
  if ((! w__2) : Bool)
  then
    (do
      writeReg IsWFIsleep true
      let w__3 ← (( do readReg _DormantCtlReg ) : SailM (BitVec 32) )
      writeReg _DormantCtlReg (Sail.BitVec.updateSubrange w__3 0 0 1#1)
      (pure ((EnterLowPowerState ()))))
  else (pure (()))


def MPAMisEnabled (_ : Unit) : SailM Bool := do
  let el : (BitVec 2) := (HighestEL ())
  let questionMark := el
  if ((questionMark == EL3) : Bool)
  then
    (do
      let w__0 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      (pure (((_get_MPAM3_EL3_Type_MPAMEN w__0) == 1#1))))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          let w__1 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
          (pure (((_get_MPAM2_EL2_Type_MPAMEN w__1) == 1#1))))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              let w__2 ← (( do (MPAM1_EL1_read ()) ) : SailM (BitVec 64) )
              (pure (((_get_MPAM1_EL1_Type_MPAMEN w__2) == 1#1))))
          else
            (do
              (undefined_bool_at (← occLabel 745) ()))))


def MAP_vPARTID (vpartid : (BitVec 16)) : SailM ((BitVec 16) × Bool) := do
  let ret ← (( do (undefined_bitvector_at (← occLabel 759) 16) ) : SailM PARTIDtype )
  let err ← (( do (undefined_bool_at (← occLabel 760) ()) ) : SailM Bool )
  let virt : Int := (BitVec.toNat vpartid)
  let w__0 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  let vpmrmax : Int := (BitVec.toNat (_get_MPAMIDR_EL1_Type_VPMR_MAX w__0))
  let vpartid_max : Int := ((Int.shiftl vpmrmax 2) +i 3)
  let virt : Int :=
    if (((BitVec.toNat vpartid) >b vpartid_max) : Bool)
    then (fmod_int virt (vpartid_max +i 1))
    else virt
  let virt : Int := virt
  ArmFull.assert ((0 ≤b virt) && (virt <b 64)) "sail-arm/v8_base.sail:11606.48-11606.49"
  let w__1 ← (( do readReg MPAMVPMV_EL2 ) : SailM (BitVec 64) )
  let (err, ret) ← (( do
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__1 (Sail.Int.toNatChecked (virt)))])) == 1#1) : Bool)
    then
      (do
        let w__2 ← (( do (mapvpmw virt) ) : SailM (BitVec 16) )
        let ret := (w__2 : (BitVec 16))
        let err : Bool := false
        (pure ((err, ret))))
    else
      (do
        let w__3 ← (( do readReg MPAMVPMV_EL2 ) : SailM (BitVec 64) )
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__3 0)])) == 1#1) : Bool)
        then
          (do
            let w__4 ← (( do readReg MPAMVPM0_EL2 ) : SailM (BitVec 64) )
            let ret := ((BitVec.slice w__4 0 16) : (BitVec 16))
            let err : Bool := false
            (pure ((err, ret))))
        else
          (let ret : PARTIDtype := DefaultPARTID
          let err : Bool := true
          (pure ((err, ret))))) ) : SailM (Bool × (BitVec 16)) )
  let w__5 ← (( do readReg MPAMIDR_EL1 ) : SailM (BitVec 64) )
  let partid_max : Int := (BitVec.toNat (_get_MPAMIDR_EL1_Type_PARTID_MAX w__5))
  let (err, ret) : (Bool × (BitVec 16)) :=
    if (((BitVec.toNat ret) >b partid_max) : Bool)
    then
      (let ret : PARTIDtype := DefaultPARTID
      let err : Bool := true
      (err, ret))
    else (err, ret)
  let err := err
  let ret := ret
  (pure ((ret, err)))


def InStreamingMode (_ : Unit) : SailM Bool := do
  if ((← do
       (HaveSME ())) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (pure (((w__1.SM == 1#1) : Bool))))
  else (pure false)


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def UnsignedRSqrtEstimate (operand : (BitVec k_N)) : SailM (BitVec k_N) := do
  let estimate ← (( do (undefined_int_at (← occLabel 818) ()) ) : SailM Int )
  let increasedprecision_name ← (( do (undefined_bool_at (← occLabel 819) ()) ) : SailM Bool )
  ArmFull.assert ((Sail.BitVec.length operand) == 32) "sail-arm/v8_base.sail:13158.19-13158.20"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 820)
      (Sail.BitVec.length operand))) ) : SailM (BitVec k_N) )
  if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb operand
         (Sail.Int.toNatChecked (((Sail.BitVec.length result) -i 1)))
         (Sail.Int.toNatChecked (((Sail.BitVec.length result) -i 2))))) == 0b00#2) : Bool)
  then
    (let result : (BitVec k_N) := (Sail.BitVec.castWidth (Ones (n := (Sail.BitVec.length result))))
    (pure (result)))
  else
    (do
      let increasedprecision_name : Bool := false
      let estimate ← (( do
        (RecipSqrtEstimate (BitVec.toNat (Sail.BitVec.extractLsb operand 31 23))
          increasedprecision_name) ) : SailM Int )
      let result : (BitVec k_N) :=
        (Sail.BitVec.castWidth ((integer_subrange estimate 8 0) +++ (Zeros
            (n := (Sail.Int.toNatChecked (((Sail.BitVec.length result) -i 9)))))))
      (pure (result)))


/-- Type quantifiers: k_iswrite : Bool, size : Int -/
def HandleExternalTTWAbort (memretstatus : PhysMemRetStatus) (iswrite : Bool) (memaddrdesc : AddressDescriptor) (accdesc : AccessDescriptor) (size : Int) (input_fault : FaultRecord) : SailM FaultRecord := do
  let output_fault : FaultRecord := input_fault
  let output_fault : FaultRecord := { output_fault with extflag := memretstatus.extflag }
  let output_fault : FaultRecord := { output_fault with statuscode := memretstatus.statuscode }
  let w__2 ← (( do
    if ((← do
         (IsExternalSyncAbort__1 output_fault)) : Bool)
    then
      (do
        let w__1 ← (( do
          (IsExternalAbortTakenSynchronously memretstatus iswrite memaddrdesc size accdesc) ) :
          SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  let output_fault : FaultRecord :=
    if (w__2 : Bool)
    then
      (if ((BEq.beq output_fault.statuscode Fault_SyncParity) : Bool)
      then { output_fault with statuscode := Fault_AsyncParity }
      else { output_fault with statuscode := Fault_AsyncExternal })
    else output_fault
  let w__3 ← (( do (IsExternalSyncAbort__1 output_fault) ) : SailM Bool )
  let output_fault : FaultRecord :=
    if (w__3 : Bool)
    then
      (if ((BEq.beq output_fault.statuscode Fault_SyncParity) : Bool)
      then { output_fault with statuscode := Fault_SyncParityOnWalk }
      else { output_fault with statuscode := Fault_SyncExternalOnWalk })
    else output_fault
  let w__4 ← (( do (HaveRASExt ()) ) : SailM Bool )
  let output_fault : FaultRecord :=
    if (w__4 : Bool)
    then { output_fault with merrorstate := memretstatus.merrorstate }
    else output_fault
  let w__5 ← (( do (IsExternalSyncAbort__1 output_fault) ) : SailM Bool )
  let output_fault : FaultRecord :=
    if ((! w__5) : Bool)
    then
      (let _ : Unit := (PendSErrorInterrupt output_fault)
      { output_fault with statuscode := Fault_None })
    else output_fault
  (pure (output_fault))


def ReportAsGPCException (fault : FaultRecord) : SailM Bool := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  ArmFull.assert w__0 "sail-arm/v8_base.sail:15078.20-15078.21"
  ArmFull.assert ((BEq.beq fault.statuscode Fault_GPCFOnWalk) || (BEq.beq fault.statuscode
      Fault_GPCFOnOutput)) "sail-arm/v8_base.sail:15079.88-15079.89"
  ArmFull.assert (bne fault.gpcf.gpf GPCF_None) "sail-arm/v8_base.sail:15080.38-15080.39"
  match fault.gpcf.gpf with
  | .GPCF_Walk => (pure (true))
  | .GPCF_AddressSize => (pure (true))
  | .GPCF_EABT => (pure (true))
  | .GPCF_Fail =>
    (do
      if ((← do
           let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
           (pure ((((_get_SCR_EL3_Type_GPF w__1) == 1#1) : Bool)))) : Bool)
      then
        (do
          let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__2.EL != EL3) : Bool))))
      else (pure false))
  | _ =>
    (do
      (undefined_bool_at (← occLabel 879) ()))


def EncodePARAttrs (memattrs : MemoryAttributes) : SailM (BitVec 8) := SailME.run do
  let result ← (( do (undefined_bitvector_at (← occLabel 1188) 8) ) : SailME (BitVec 8)
    (BitVec 8) )
  let w__1 ← (( do
    (pure ((← do
          (HaveMTEExt ())) && ((BEq.beq memattrs.tags MemTag_AllocationTagged) : Bool))) ) : SailME
    (BitVec 8) Bool )
  if (w__1 : Bool)
  then
    (do
      let w__3 ← (( do
        (pure ((← do
              (HaveMTEPermExt ())) && (memattrs.notagaccess : Bool))) ) : SailME (BitVec 8) Bool )
      let result : (BitVec 8) :=
        if (w__3 : Bool)
        then (Sail.BitVec.updateSubrange result 7 0 0b11100000#8)
        else (Sail.BitVec.updateSubrange result 7 0 0b11110000#8)
      (pure (result)))
  else
    (do
      if ((BEq.beq memattrs.memtype MemType_Device) : Bool)
      then
        (let result : (BitVec 8) := (Sail.BitVec.updateSubrange result 7 4 0b0000#4)
        let result : (BitVec 8) :=
          match memattrs.device with
          | .DeviceType_nGnRnE => (Sail.BitVec.updateSubrange result 3 0 0b0000#4)
          | .DeviceType_nGnRE => (Sail.BitVec.updateSubrange result 3 0 0b0100#4)
          | .DeviceType_nGRE => (Sail.BitVec.updateSubrange result 3 0 0b1000#4)
          | .DeviceType_GRE => (Sail.BitVec.updateSubrange result 3 0 0b1100#4)
        let result : (BitVec 8) :=
          (BitVec.update result 0 (Bit (Complement.complement memattrs.xs)))
        (pure (result)))
      else
        (do
          if ((memattrs.xs == 0#1) : Bool)
          then
            (do
              if (((((memattrs.outer.attrs == MemAttr_WT) && (memattrs.inner.attrs == MemAttr_WT)) && (! memattrs.outer.transient)) && (memattrs.outer.hints == MemHint_RA)) : Bool)
              then
                (do
                  SailME.throw (0b10100000#8 : (BitVec 8)))
              else
                (do
                  if (((memattrs.outer.attrs == MemAttr_NC) && (memattrs.inner.attrs == MemAttr_NC)) : Bool)
                  then
                    (do
                      SailME.throw (0b01000000#8 : (BitVec 8)))
                  else (pure (()))))
          else (pure (()))
          let result : (BitVec 8) :=
            if ((memattrs.outer.attrs == MemAttr_WT) : Bool)
            then
              (let result : (BitVec 8) :=
                (Sail.BitVec.updateSubrange result 7 6
                  (if (memattrs.outer.transient : Bool)
                  then 0b00#2
                  else 0b10#2))
              (Sail.BitVec.updateSubrange result 5 4 memattrs.outer.hints))
            else
              (if ((memattrs.outer.attrs == MemAttr_WB) : Bool)
              then
                (let result : (BitVec 8) :=
                  (Sail.BitVec.updateSubrange result 7 6
                    (if (memattrs.outer.transient : Bool)
                    then 0b01#2
                    else 0b11#2))
                (Sail.BitVec.updateSubrange result 5 4 memattrs.outer.hints))
              else (Sail.BitVec.updateSubrange result 7 4 0b0100#4))
          let result : (BitVec 8) :=
            if ((memattrs.inner.attrs == MemAttr_WT) : Bool)
            then
              (let result : (BitVec 8) :=
                (Sail.BitVec.updateSubrange result 3 2
                  (if (memattrs.inner.transient : Bool)
                  then 0b00#2
                  else 0b10#2))
              (Sail.BitVec.updateSubrange result 1 0 memattrs.inner.hints))
            else
              (if ((memattrs.inner.attrs == MemAttr_WB) : Bool)
              then
                (let result : (BitVec 8) :=
                  (Sail.BitVec.updateSubrange result 3 2
                    (if (memattrs.inner.transient : Bool)
                    then 0b01#2
                    else 0b11#2))
                (Sail.BitVec.updateSubrange result 1 0 memattrs.inner.hints))
              else (Sail.BitVec.updateSubrange result 3 0 0b0100#4))
          (pure (result))))


def WalkMemAttrs (sh : (BitVec 2)) (irgn : (BitVec 2)) (orgn : (BitVec 2)) : SailM MemoryAttributes := do
  let walkmemattrs ← (( do (undefined_MemoryAttributes (← occLabel 1216) ()) ) : SailM
    MemoryAttributes )
  let walkmemattrs : MemoryAttributes := { walkmemattrs with memtype := MemType_Normal }
  let w__0 ← (( do (DecodeShareability sh) ) : SailM Shareability )
  let walkmemattrs := ({ walkmemattrs with shareability := w__0 } : MemoryAttributes)
  let w__1 ← (( do (DecodeSDFAttr irgn) ) : SailM MemAttrHints )
  let walkmemattrs := ({ walkmemattrs with inner := w__1 } : MemoryAttributes)
  let w__2 ← (( do (DecodeSDFAttr orgn) ) : SailM MemAttrHints )
  let walkmemattrs := ({ walkmemattrs with outer := w__2 } : MemoryAttributes)
  let walkmemattrs : MemoryAttributes := { walkmemattrs with tags := MemTag_Untagged }
  let walkmemattrs : MemoryAttributes :=
    if (((walkmemattrs.inner.attrs == MemAttr_WB) && (walkmemattrs.outer.attrs == MemAttr_WB)) : Bool)
    then { walkmemattrs with xs := 0#1 }
    else { walkmemattrs with xs := 1#1 }
  let walkmemattrs : MemoryAttributes := { walkmemattrs with notagaccess := false }
  (pure (walkmemattrs))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def S1ConstrainUnpredictableRESMAIR (attr : (BitVec 8)) (s1aarch64 : Bool) : SailM Bool := do
  let b__0 := attr
  if ((((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 7 4)) == (0x0#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
           b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
  then
    (do
      let w__1 ← (( do
        if ((s1aarch64 : Bool) : Bool)
        then
          (do
            (HaveFeatXS ()))
        else (pure false) ) : SailM Bool )
      (pure ((! w__1))))
  else
    (do
      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 7 4)) == (0x0#4 : (BitVec 4))) : Bool)
      then (pure (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb attr 1 0)) != 0b00#2)))
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
              (pure ((! w__3))))
          | 0b10100000 =>
            (do
              let w__5 ← (( do
                if ((s1aarch64 : Bool) : Bool)
                then
                  (do
                    (HaveFeatXS ()))
                else (pure false) ) : SailM Bool )
              (pure ((! w__5))))
          | 0b11110000 =>
            (do
              let w__7 ← (( do
                if ((s1aarch64 : Bool) : Bool)
                then
                  (do
                    (HaveMTE2Ext ()))
                else (pure false) ) : SailM Bool )
              (pure ((! w__7))))
          | b__0 =>
            (pure (if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 3 0)) == (0x0#4 : (BitVec 4))) : Bool)
              then true
              else false))))


def S2MemTagType (s2_memattrs : MemoryAttributes) (s1_tagtype : MemTagType) : SailM MemTagType := do
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  let w__1 : MemTagType :=
    if ((! w__0) : Bool)
    then MemTag_Untagged
    else
      (if (((((((((BEq.beq s1_tagtype MemTag_AllocationTagged) && (BEq.beq s2_memattrs.memtype
                         MemType_Normal)) && (s2_memattrs.inner.attrs == MemAttr_WB)) && (s2_memattrs.inner.hints == MemHint_RWA)) && (! s2_memattrs.inner.transient)) && (s2_memattrs.outer.attrs == MemAttr_WB)) && (s2_memattrs.outer.hints == MemHint_RWA)) && (! s2_memattrs.outer.transient)) : Bool)
      then MemTag_AllocationTagged
      else
        (if ((bne s1_tagtype MemTag_AllocationTagged) : Bool)
        then s1_tagtype
        else MemTag_Untagged))
  (pure (w__1))


/-- Type quantifiers: k_s2aarch64 : Bool -/
def S2DecodeMemAttrs (attr : (BitVec 4)) (sh : (BitVec 2)) (s2aarch64 : Bool) : SailM MemoryAttributes := do
  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 1220) ()) ) : SailM
    MemoryAttributes )
  let b__0 := attr
  let memattrs ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 3 2)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (do
        let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Device }
        let w__0 ← (( do (DecodeDevice (Sail.BitVec.extractLsb attr 1 0)) ) : SailM DeviceType )
        let memattrs := ({ memattrs with device := w__0 } : MemoryAttributes)
        (pure (memattrs)))
    else
      (do
        match b__0 with
        | 0b0100 =>
          (do
            let w__2 ← (( do
              if ((s2aarch64 : Bool) : Bool)
              then
                (do
                  (HaveMTEPermExt ()))
              else (pure false) ) : SailM Bool )
            if (w__2 : Bool)
            then
              (do
                let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
                let w__3 ← (( do (S2DecodeCacheability 0b11#2) ) : SailM MemAttrHints )
                let memattrs := ({ memattrs with outer := w__3 } : MemoryAttributes)
                let w__4 ← (( do (S2DecodeCacheability 0b11#2) ) : SailM MemAttrHints )
                let memattrs := ({ memattrs with inner := w__4 } : MemoryAttributes)
                (pure (memattrs)))
            else
              (do
                let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
                let w__5 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 3 2)) ) :
                  SailM MemAttrHints )
                let memattrs := ({ memattrs with outer := w__5 } : MemoryAttributes)
                let w__6 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 1 0)) ) :
                  SailM MemAttrHints )
                let memattrs := ({ memattrs with inner := w__6 } : MemoryAttributes)
                (pure (memattrs))))
        | _ =>
          (do
            let memattrs : MemoryAttributes := { memattrs with memtype := MemType_Normal }
            let w__7 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 3 2)) ) : SailM
              MemAttrHints )
            let memattrs := ({ memattrs with outer := w__7 } : MemoryAttributes)
            let w__8 ← (( do (S2DecodeCacheability (Sail.BitVec.extractLsb attr 1 0)) ) : SailM
              MemAttrHints )
            let memattrs := ({ memattrs with inner := w__8 } : MemoryAttributes)
            (pure (memattrs)))) ) : SailM MemoryAttributes )
  let w__9 ← (( do (DecodeShareability sh) ) : SailM Shareability )
  let memattrs := ({ memattrs with shareability := w__9 } : MemoryAttributes)
  let w__11 ← (( do
    if ((s2aarch64 : Bool) : Bool)
    then
      (do
        (HaveMTEPermExt ()))
    else (pure false) ) : SailM Bool )
  let memattrs : MemoryAttributes :=
    if (w__11 : Bool)
    then { memattrs with notagaccess := (attr == 0b0100#4) }
    else { memattrs with notagaccess := false }
  (pure (memattrs))


end ArmFull.Functions
