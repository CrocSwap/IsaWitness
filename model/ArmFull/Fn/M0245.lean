module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0124
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0152
public import ArmFull.Fn.M0169
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0173
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0194
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0203
public import ArmFull.Fn.M0242
public import ArmFull.Fn.M0243
public import ArmFull.Fn.M0244 set_option backward.proofsInPublic true @[expose] public section

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

def CheckPendingResetCatch (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaltingAllowed ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg EDESR ) : SailM (BitVec 32) )
        (pure ((((_get_EDESR_Type_RC w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let is_async : Bool := true
      (Halt__1 DebugHalt_ResetCatch is_async))
  else (pure (()))


def CheckPendingOSUnlockCatch (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaltingAllowed ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg EDESR ) : SailM (BitVec 32) )
        (pure ((((_get_EDESR_Type_OSUC w__1) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let is_async : Bool := true
      (Halt__1 DebugHalt_OSUnlockCatch is_async))
  else (pure (()))


/-- Type quantifiers: k_is_async : Bool -/
def CheckPendingExceptionCatch (is_async : Bool) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              (Havev8p8Debug ())) : Bool)
         then
           (do
             (HaltingAllowed ()))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg EDESR ) : SailM (BitVec 32) )
        (pure ((((_get_EDESR_Type_EC w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      (Halt__1 DebugHalt_ExceptionCatch is_async))
  else (pure (()))


def decode_aarch32_instrs_ADR_A1enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:951.29-951.30"
      let d : Int := (BitVec.toNat Rd)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let add : Bool := true
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_A2enc_A_txt (cond : (BitVec 4)) (Rd : (BitVec 4)) (imm12 : (BitVec 12)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      ArmFull.assert (cond != 0b1111#4) "sail-inputs/14-instrs32.sail:972.29-972.30"
      let d : Int := (BitVec.toNat Rd)
      let imm32 ← (( do (A32ExpandImm imm12) ) : SailM (BitVec 32) )
      let add : Bool := false
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_T1enc_A_txt (Rd : (BitVec 3)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend (imm8 +++ 0b00#2) 32)
      let add : Bool := true
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_T2enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      let add : Bool := false
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def decode_aarch32_instrs_ADR_T3enc_A_txt (i : (BitVec 1)) (imm3 : (BitVec 3)) (Rd : (BitVec 4)) (imm8 : (BitVec 8)) : SailM Unit := do
  let w__0 ← (( do (ConditionPassed ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let d : Int := (BitVec.toNat Rd)
      let imm32 : (BitVec 32) := (Sail.BitVec.zeroExtend ((i +++ imm3) +++ imm8) 32)
      let add : Bool := true
      if ((d == 15) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (()))
      (execute_aarch32_instrs_ADR_Op_A_txt add (Sail.Int.toNatChecked (d)) imm32))
  else (pure (()))


def execute_aarch32_instrs_HLT_Op_A_txt (_ : Unit) : SailM Unit := do
  let is_async : Bool := false
  (Halt__1 DebugHalt_HaltInstruction is_async)


def execute_aarch64_instrs_system_exceptions_debug_halt (_ : Unit) : SailM Unit := do
  let is_async : Bool := false
  (Halt__1 DebugHalt_HaltInstruction is_async)


def CheckForPMUOverflow (_ : Unit) : SailM Unit := do
  let check_cnten : Bool := false
  let check_e : Bool := true
  let check_inten : Bool := true
  let include_lo_name : Bool := true
  let include_hi_name : Bool := true
  let exclude_cyc : Bool := false
  let exclude_sync : Bool := false
  let pmuirq ← (( do
    (PMUOverflowCondition check_e check_cnten check_inten include_hi_name include_lo_name
      exclude_cyc exclude_sync) ) : SailM Bool )
  (SetInterruptRequestLevel InterruptID_PMUIRQ
    (if (pmuirq : Bool)
    then Signal_High
    else Signal_Low))
  let _ : Unit :=
    (CTI_SetEventLevel CrossTriggerIn_PMUOverflow
      (if (pmuirq : Bool)
      then Signal_High
      else Signal_Low))
  let w__2 ← (( do
    if ((← do
         (HavePMUv3p9 ())) : Bool)
    then
      (do
        (Havev8p9Debug ()))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      let w__6 ← (( do
        if ((← if (pmuirq : Bool)
             then
               (do
                 (HaltingAllowed ()))
             else (pure false)) : Bool)
        then
          (do
            let w__5 ← (( do readReg EDECR ) : SailM (BitVec 32) )
            (pure ((((_get_EDECR_Type_PME w__5) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          (Halt DebugHalt_EDBGRQ))
      else (pure (())))
  else (pure (()))
  let w__7 ← (( do (ShouldBRBEFreeze ()) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      (BRBEFreeze ()))
  else (pure (()))


/-- Type quantifiers: k_exception_entry : Bool -/
def CheckExceptionCatch (exception_entry : Bool) : SailM Unit := do
  let ctrl ← (( do (undefined_bitvector_at (← occLabel 701) 2) ) : SailM (BitVec 2) )
  let exception_exit ← (( do (undefined_bool_at (← occLabel 702) ()) ) : SailM Bool )
  let increment_name ← (( do (undefined_int_at (← occLabel 703) ()) ) : SailM Int )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let ss ← (( do (SecurityStateAtEL w__0.EL) ) : SailM SecurityState )
  let base : Int := 0
  let base : Int :=
    match ss with
    | .SS_Secure => 0
    | .SS_NonSecure => 4
    | .SS_Realm => 16
    | .SS_Root => 0
  let base : Int := base
  let w__1 ← (( do (HaltingAllowed ()) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let halt ← (( do (undefined_bool_at (← occLabel 704) ()) ) : SailM Bool )
      let w__2 ← (( do (HaveExtendedECDebugEvents ()) ) : SailM Bool )
      let halt ← (( do
        if (w__2 : Bool)
        then
          (do
            let exception_exit : Bool := (! exception_entry)
            let increment_name : Int :=
              if ((BEq.beq ss SS_Realm) : Bool)
              then 4
              else 8
            let w__3 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
            let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
            let w__5 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
            let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
            let ctrl : (BitVec 2) :=
              ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__3
                    (Sail.Int.toNatChecked ((((BitVec.toNat w__4.EL) +i base) +i increment_name))))])) +++ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                    w__5 (Sail.Int.toNatChecked (((BitVec.toNat w__6.EL) +i base))))])))
            let halt : Bool :=
              match ctrl with
              | 0b00 => false
              | 0b01 => true
              | 0b10 => (exception_exit == true)
              | _ => (exception_entry == true)
            (pure (halt)))
        else
          (do
            let w__7 ← (( do (EDECCR_read ()) ) : SailM (BitVec 32) )
            let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
            let halt :=
              (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__7
                    (Sail.Int.toNatChecked (((BitVec.toNat w__8.EL) +i base))))])) == 1#1) : Bool)
            (pure (halt))) ) : SailM Bool )
      if (halt : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  (Havev8p8Debug ())) && (exception_entry : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              let w__11 ← (( do readReg EDESR ) : SailM (BitVec 32) )
              writeReg EDESR (Sail.BitVec.updateSubrange w__11 3 3 1#1))
          else
            (do
              (Halt DebugHalt_ExceptionCatch)))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: N : Nat, List.elem N [32, 64, 128] -/
def FetchDescriptor (ee : (BitVec 1)) (walkaddress : AddressDescriptor) (walkaccess : AccessDescriptor) (fault_in : FaultRecord) (N : Nat) (translation_info : TranslationInfo) : SailM (FaultRecord × (BitVec N)) := SailME.run do
  ArmFull.assert (((N == 32) || (N == 64)) || (N == 128)) "sail-inputs/03-v8_base.sail:19945.41-19945.42"
  let descriptor ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1244)
      (Sail.Int.toNatChecked (N)))) ) : SailME (FaultRecord × (BitVec N)) (BitVec N) )
  let fault : FaultRecord := fault_in
  let w__0 ← (( do (HaveRME ()) ) : SailME (FaultRecord × (BitVec N)) Bool )
  let fault ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (GranuleProtectionCheck walkaddress walkaccess) ) : SailME
          (FaultRecord × (BitVec N)) GPCFRecord )
        let fault := ({ fault with gpcf := w__1 } : FaultRecord)
        if ((bne fault.gpcf.gpf GPCF_None) : Bool)
        then
          (do
            let fault : FaultRecord := { fault with statuscode := Fault_GPCFOnWalk }
            let fault : FaultRecord := { fault with paddress := walkaddress.paddress }
            let fault : FaultRecord := { fault with gpcfs2walk := fault.secondstage }
            let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
              (FaultRecord × (BitVec N)) (BitVec N) )
            SailME.throw ((fault, w__2) : (FaultRecord × (BitVec N)))
            (pure (fault)))
        else (pure (fault)))
    else (pure (fault)) ) : SailME (FaultRecord × (BitVec N)) FaultRecord )
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1245) ()) ) : SailME
    (FaultRecord × (BitVec N)) PhysMemRetStatus )
  let w__3 ← (( do
    ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead walkaddress
      (Sail.Int.toNatChecked ((Int.ediv N 8))) walkaccess (some translation_info))) ) : SailME
    (FaultRecord × (BitVec N)) (PhysMemRetStatus × (BitVec (8 * (N / 8)))) )
  let (tup__0, tup__1) := (w__3 : (PhysMemRetStatus × (BitVec (8 * (N / 8)))))
  let memstatus : PhysMemRetStatus := tup__0
  let descriptor : (BitVec N) := (Sail.BitVec.castWidth tup__1)
  let fault ← (( do
    if ((IsFault__2 memstatus) : Bool)
    then
      (do
        let iswrite : Bool := false
        let w__4 ← (( do
          (HandleExternalTTWAbort memstatus iswrite walkaddress walkaccess (Int.ediv N 8) fault) ) :
          SailME (FaultRecord × (BitVec N)) FaultRecord )
        let fault := (w__4 : FaultRecord)
        if ((IsFault__1 fault.statuscode) : Bool)
        then
          (do
            let w__5 ← (( do ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits N)) ) : SailME
              (FaultRecord × (BitVec N)) (BitVec N) )
            SailME.throw ((fault, w__5) : (FaultRecord × (BitVec N))))
        else (pure (()))
        (pure (fault)))
    else (pure (fault)) ) : SailME (FaultRecord × (BitVec N)) FaultRecord )
  let descriptor : (BitVec N) :=
    if ((ee == 1#1) : Bool)
    then (reverse_endianness descriptor)
    else descriptor
  let descriptor := descriptor
  (pure ((fault, descriptor)))


/-- Type quantifiers: size : Int -/
def AArch64_CheckBreakpoint (fault_in : FaultRecord) (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) (size : Int) : SailM FaultRecord := do
  let is_mismatch_i ← (( do (undefined_bool_at (← occLabel 1392) ()) ) : SailM Bool )
  let match_i ← (( do (undefined_bool_at (← occLabel 1393) ()) ) : SailM Bool )
  let reason ← (( do (undefined_bitvector_at (← occLabel 1394) 6) ) : SailM (BitVec 6) )
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:23665.61-23665.62"
  let w__4 ← (( do
    (pure ((← do
          (pure ((← do
                (UsingAArch32 ())) && (((size == 2) || (size == 4)) : Bool)))) || ((size == 4) : Bool)))
    ) : SailM Bool )
  ArmFull.assert w__4 "sail-inputs/03-v8_base.sail:23666.63-23666.64"
  let fault : FaultRecord := fault_in
  let val_match : Bool := false
  let mismatch : Bool := true
  let mismatch_bp : Bool := false
  let w__5 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  let (is_mismatch_i, match_i, mismatch, mismatch_bp, val_match) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (w__5 -i 1)
    (do
      let mut loop_vars := (is_mismatch_i, match_i, mismatch, mismatch_bp, val_match)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (is_mismatch_i, match_i, mismatch, mismatch_bp, val_match) := loop_vars
        loop_vars ← do
          ArmFull.assert ((i <b 64) || (! (((size == 2) || (size == 4)) || (size == 4)))) "sail-inputs/03-v8_base.sail:23672.67-23672.68"
          let w__6 ← (( do
            (AArch64_BreakpointMatch (Sail.Int.toNatChecked (i)) vaddress accdesc size) ) : SailM
            (Bool × Bool) )
          let (tup__0, tup__1) := (w__6 : (Bool × Bool))
          let match_i : Bool := tup__0
          let is_mismatch_i : Bool := tup__1
          let (mismatch, mismatch_bp, val_match) : (Bool × Bool × Bool) :=
            if (is_mismatch_i : Bool)
            then
              (let mismatch_bp : Bool := true
              let mismatch : Bool := (mismatch && (! match_i))
              (mismatch, mismatch_bp, val_match))
            else
              (let val_match : Bool := (val_match || match_i)
              (mismatch, mismatch_bp, val_match))
          (pure ((is_mismatch_i, match_i, mismatch, mismatch_bp, val_match)))
      (pure loop_vars)) ) : SailM (Bool × Bool × Bool × Bool × Bool) )
  if ((val_match || (mismatch && mismatch_bp)) : Bool)
  then
    (do
      let fault : FaultRecord := { fault with statuscode := Fault_Debug }
      let w__7 ← (( do (HaltOnBreakpointOrWatchpoint ()) ) : SailM Bool )
      if (w__7 : Bool)
      then
        (do
          let reason : (BitVec 6) := DebugHalt_Breakpoint
          (Halt reason))
      else (pure (()))
      (pure (fault)))
  else (pure (fault))


/-- Type quantifiers: size : Int -/
def AArch64_CheckWatchpoint (fault_in : FaultRecord) (vaddress : (BitVec 64)) (accdesc : AccessDescriptor) (size : Int) : SailM FaultRecord := SailME.run do
  let reason ← (( do (undefined_bitvector_at (← occLabel 1402) 6) ) : SailME FaultRecord
    (BitVec 6) )
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailME FaultRecord (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailME FaultRecord Bool )
  ArmFull.assert (! w__1) "sail-inputs/03-v8_base.sail:23827.61-23827.62"
  let fault : FaultRecord := fault_in
  if ((BEq.beq accdesc.acctype AccessType_DC) : Bool)
  then
    (do
      if ((bne accdesc.cacheop CacheOp_Invalidate) : Bool)
      then
        (do
          SailME.throw (fault : FaultRecord))
      else (pure (())))
  else
    (do
      if ((! (IsDataAccess accdesc.acctype)) : Bool)
      then
        (do
          SailME.throw (fault : FaultRecord))
      else (pure (())))
  let w__2 ← (( do (NumWatchpointsImplemented ()) ) : SailME FaultRecord Int )
  let fault ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (w__2 -i 1)
    (do
      let mut loop_vars := fault
      for i in [loop_i_lower:loop_i_upper:1]i do
        let fault := loop_vars
        loop_vars ← do
          ArmFull.assert (i <b 64) "sail-inputs/03-v8_base.sail:23838.39-23838.40"
          let w__3 ← (( do
            (AArch64_WatchpointMatch (Sail.Int.toNatChecked (i)) vaddress size accdesc) ) : SailME
            FaultRecord Bool )
          if (w__3 : Bool)
          then
            (do
              let fault : FaultRecord := { fault with statuscode := Fault_Debug }
              let w__5 ← (( do
                (pure ((← do
                      let w__4 ← (( do readReg DBGWCR_EL1 ) : SailME FaultRecord
                        (Vector (BitVec 64) 64) )
                      (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                              (_get_DBGWCR_EL1_Type_LSC
                                (GetElem?.getElem! w__4 (Sail.Int.toNatChecked (i)))) 0)])) == 1#1) : Bool)))) && (accdesc.read : Bool)))
                ) : SailME FaultRecord Bool )
              if (w__5 : Bool)
              then
                (let fault : FaultRecord := { fault with write := false }
                (pure (fault)))
              else
                (do
                  let w__7 ← (( do
                    (pure ((← do
                          let w__6 ← (( do readReg DBGWCR_EL1 ) : SailME FaultRecord
                            (Vector (BitVec 64) 64) )
                          (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                  (_get_DBGWCR_EL1_Type_LSC
                                    (GetElem?.getElem! w__6 (Sail.Int.toNatChecked (i)))) 1)])) == 1#1) : Bool)))) && (accdesc.write : Bool)))
                    ) : SailME FaultRecord Bool )
                  let fault : FaultRecord :=
                    if (w__7 : Bool)
                    then { fault with write := true }
                    else fault
                  (pure (fault))))
          else (pure (fault))
      (pure loop_vars)) ) : SailME FaultRecord FaultRecord )
  let w__11 ← (( do
    (pure ((← do
          (pure ((← do
                if (((BEq.beq fault.statuscode Fault_Debug) : Bool) : Bool)
                then
                  (do
                    (HaltOnBreakpointOrWatchpoint ()))
                else (pure false)) && ((! accdesc.nonfault) : Bool)))) && ((! (accdesc.firstfault && (! accdesc.first))) : Bool)))
    ) : SailME FaultRecord Bool )
  if (w__11 : Bool)
  then
    (do
      let reason : (BitVec 6) := DebugHalt_Watchpoint
      writeReg EDWAR vaddress
      (Halt reason))
  else (pure (()))
  (pure (fault))


/-- Type quantifiers: k_N : Nat, List.elem k_N [64, 128] -/
def AArch64_MemSwapTableDesc (fault_in : FaultRecord) (prev_desc : (BitVec k_N)) (new_desc : (BitVec k_N)) (ee : (BitVec 1)) (descaccess : AccessDescriptor) (descpaddr : AddressDescriptor) (translation_info : TranslationInfo) : SailM (FaultRecord × (BitVec k_N)) := SailME.run do
  let ordered_new_desc ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1406)
      (Sail.BitVec.length prev_desc))) ) : SailME (FaultRecord × (BitVec k_N)) (BitVec k_N) )
  let fault : FaultRecord := fault_in
  let iswrite ← (( do (undefined_bool_at (← occLabel 1407) ()) ) : SailME
    (FaultRecord × (BitVec k_N)) Bool )
  let w__0 ← (( do (HaveRME ()) ) : SailME (FaultRecord × (BitVec k_N)) Bool )
  let fault ← (( do
    if (w__0 : Bool)
    then
      (do
        let w__1 ← (( do (GranuleProtectionCheck descpaddr descaccess) ) : SailME
          (FaultRecord × (BitVec k_N)) GPCFRecord )
        let fault := ({ fault with gpcf := w__1 } : FaultRecord)
        if ((bne fault.gpcf.gpf GPCF_None) : Bool)
        then
          (do
            let fault : FaultRecord := { fault with statuscode := Fault_GPCFOnWalk }
            let fault : FaultRecord := { fault with paddress := descpaddr.paddress }
            let fault : FaultRecord := { fault with gpcfs2walk := fault.secondstage }
            let w__2 ← (( do
              ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits (Sail.BitVec.length prev_desc))) ) :
              SailME (FaultRecord × (BitVec k_N)) (BitVec k_N) )
            SailME.throw ((fault, w__2) : (FaultRecord × (BitVec k_N)))
            (pure (fault)))
        else (pure (fault)))
    else (pure (fault)) ) : SailME (FaultRecord × (BitVec k_N)) FaultRecord )
  let mem_desc ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1408)
      (Sail.BitVec.length prev_desc))) ) : SailME (FaultRecord × (BitVec k_N)) (BitVec k_N) )
  let memstatus ← (( do (undefined_PhysMemRetStatus (← occLabel 1409) ()) ) : SailME
    (FaultRecord × (BitVec k_N)) PhysMemRetStatus )
  let w__3 ← (( do
    ((fun (x0, x1) => (x0, (Sail.BitVec.castWidth x1))) <$> (PhysMemRead descpaddr
      (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length prev_desc) 8))) descaccess
      (some translation_info))) ) : SailME (FaultRecord × (BitVec k_N))
    (PhysMemRetStatus × (BitVec (8 * (k_N / 8)))) )
  let (tup__0, tup__1) := (w__3 : (PhysMemRetStatus × (BitVec (8 * (k_N / 8)))))
  let memstatus : PhysMemRetStatus := tup__0
  let mem_desc : (BitVec k_N) := (Sail.BitVec.castWidth tup__1)
  let mem_desc : (BitVec k_N) :=
    if ((ee == 1#1) : Bool)
    then (reverse_endianness mem_desc)
    else mem_desc
  let (fault, iswrite) ← (( do
    if ((IsFault__2 memstatus) : Bool)
    then
      (do
        let iswrite : Bool := false
        let w__4 ← (( do
          (HandleExternalTTWAbort memstatus iswrite descpaddr descaccess
            (Int.ediv (Sail.BitVec.length prev_desc) 8) fault) ) : SailME
          (FaultRecord × (BitVec k_N)) FaultRecord )
        let fault := (w__4 : FaultRecord)
        if ((IsFault__1 fault.statuscode) : Bool)
        then
          (do
            let w__5 ← (( do
              ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits (Sail.BitVec.length prev_desc))) ) :
              SailME (FaultRecord × (BitVec k_N)) (BitVec k_N) )
            SailME.throw ((fault, w__5) : (FaultRecord × (BitVec k_N))))
        else (pure (()))
        (pure ((fault, iswrite))))
    else (pure ((fault, iswrite))) ) : SailME (FaultRecord × (BitVec k_N)) (FaultRecord × Bool) )
  if ((mem_desc == prev_desc) : Bool)
  then
    (do
      let ordered_new_desc : (BitVec k_N) :=
        if ((ee == 1#1) : Bool)
        then (reverse_endianness new_desc)
        else new_desc
      let memstatus ← (( do
        (PhysMemWrite descpaddr
          (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length prev_desc) 8))) descaccess
          (some translation_info) (Sail.BitVec.castWidth ordered_new_desc)) ) : SailME
        (FaultRecord × (BitVec k_N)) PhysMemRetStatus )
      let fault ← (( do
        if ((IsFault__2 memstatus) : Bool)
        then
          (do
            let iswrite : Bool := true
            let w__6 ← (( do
              (HandleExternalTTWAbort memstatus iswrite descpaddr descaccess
                (Int.ediv (Sail.BitVec.length prev_desc) 8) fault) ) : SailME
              (FaultRecord × (BitVec k_N)) FaultRecord )
            let fault := (w__6 : FaultRecord)
            if ((IsFault__1 fault.statuscode) : Bool)
            then
              (do
                let w__7 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (__UNKNOWN_bits (Sail.BitVec.length prev_desc))) ) :
                  SailME (FaultRecord × (BitVec k_N)) (BitVec k_N) )
                SailME.throw ((fault, w__7) : (FaultRecord × (BitVec k_N))))
            else (pure (()))
            (pure (fault)))
        else (pure (fault)) ) : SailME (FaultRecord × (BitVec k_N)) FaultRecord )
      let mem_desc : (BitVec k_N) := new_desc
      (pure ((fault, mem_desc))))
  else (pure ((fault, mem_desc)))


def CheckResetCatch (_ : Unit) : SailM Unit := do
  let w__6 ← (( do
    if ((← do
         if ((← do
              (HaveDoPD ())) : Bool)
         then
           (do
             let w__1 ← (( do readReg CTIDEVCTL ) : SailM (BitVec 32) )
             (pure ((((_get_CTIDEVCTL_Type_RCE w__1) == 1#1) : Bool))))
         else (pure false)) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__3 ← (( do (HaveDoPD ()) ) : SailM Bool )
             (pure (((! w__3) : Bool)))) : Bool)
        then
          (do
            let w__4 ← (( do readReg EDECR ) : SailM (BitVec 32) )
            (pure ((((_get_EDECR_Type_RCE w__4) == 1#1) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__6 : Bool)
  then
    (do
      let w__7 ← (( do readReg EDESR ) : SailM (BitVec 32) )
      writeReg EDESR (Sail.BitVec.updateSubrange w__7 1 1 1#1)
      let w__8 ← (( do (HaltingAllowed ()) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (Halt DebugHalt_ResetCatch))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: size : Int -/
def AArch32_CheckBreakpoint (fault_in : FaultRecord) (vaddress : (BitVec 32)) (accdesc : AccessDescriptor) (size : Int) : SailM FaultRecord := do
  let match_i ← (( do (undefined_bool_at (← occLabel 2663) ()) ) : SailM Bool )
  let mismatch_i ← (( do (undefined_bool_at (← occLabel 2664) ()) ) : SailM Bool )
  let reason ← (( do (undefined_bitvector_at (← occLabel 2665) 6) ) : SailM (BitVec 6) )
  let w__0 ← (( do (S1TranslationRegime__1 ()) ) : SailM (BitVec 2) )
  let w__1 ← (( do (ELUsingAArch32 w__0) ) : SailM Bool )
  ArmFull.assert w__1 "sail-inputs/03-v8_base.sail:40498.51-40498.52"
  ArmFull.assert ((size == 2) || (size == 4)) "sail-inputs/03-v8_base.sail:40499.32-40499.33"
  let fault : FaultRecord := fault_in
  let val_match : Bool := false
  let mismatch : Bool := false
  let w__2 ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  let (match_i, mismatch, mismatch_i, val_match) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Int := (w__2 -i 1)
    (do
      let mut loop_vars := (match_i, mismatch, mismatch_i, val_match)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (match_i, mismatch, mismatch_i, val_match) := loop_vars
        loop_vars ← do
          ArmFull.assert ((i <b 16) || (! ((size == 2) || (size == 4)))) "sail-inputs/03-v8_base.sail:40504.64-40504.65"
          let w__3 ← (( do
            (AArch32_BreakpointMatch (Sail.Int.toNatChecked (i)) vaddress accdesc size) ) : SailM
            (Bool × Bool) )
          let (tup__0, tup__1) := (w__3 : (Bool × Bool))
          let match_i : Bool := tup__0
          let mismatch_i : Bool := tup__1
          let val_match : Bool := (val_match || match_i)
          let mismatch : Bool := (mismatch || mismatch_i)
          (pure ((match_i, mismatch, mismatch_i, val_match)))
      (pure loop_vars)) ) : SailM (Bool × Bool × Bool × Bool) )
  let w__5 ← (( do
    if ((val_match : Bool) : Bool)
    then
      (do
        (HaltOnBreakpointOrWatchpoint ()))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let reason : (BitVec 6) := DebugHalt_Breakpoint
      (Halt reason)
      (pure (fault)))
  else
    (let fault : FaultRecord :=
      if ((val_match || mismatch) : Bool)
      then
        (let fault : FaultRecord := { fault with statuscode := Fault_Debug }
        { fault with debugmoe := DebugException_Breakpoint })
      else fault
    (pure (fault)))


end ArmFull.Functions
