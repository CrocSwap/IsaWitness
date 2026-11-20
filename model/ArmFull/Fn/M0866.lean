module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0048
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0062
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0099
public import ArmFull.Fn.M0112
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0158
public import ArmFull.Fn.M0159
public import ArmFull.Fn.M0166
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0171
public import ArmFull.Fn.M0175
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0197
public import ArmFull.Fn.M0211
public import ArmFull.Fn.M0218
public import ArmFull.Fn.M0238
public import ArmFull.Fn.M0242
public import ArmFull.Fn.M0250
public import ArmFull.Fn.M0251
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0254
public import ArmFull.Fn.M0256
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0604
public import ArmFull.Fn.M0605 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacda_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if (source_is_sp : Bool)
  then
    (do
      let w__0 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
      let w__1 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (AddPACDA w__0 w__1) ) : SailM (BitVec 64) )
      (X_set d 64 w__2))
  else
    (do
      let w__3 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
      let w__4 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
      let w__5 ← (( do (AddPACDA w__3 w__4) ) : SailM (BitVec 64) )
      (X_set d 64 w__5))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacdb_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if (source_is_sp : Bool)
  then
    (do
      let w__0 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
      let w__1 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (AddPACDB w__0 w__1) ) : SailM (BitVec 64) )
      (X_set d 64 w__2))
  else
    (do
      let w__3 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
      let w__4 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
      let w__5 ← (( do (AddPACDB w__3 w__4) ) : SailM (BitVec 64) )
      (X_set d 64 w__5))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacga_dp_2src (d : Nat) (m : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  if (source_is_sp : Bool)
  then
    (do
      let w__0 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
      let w__1 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (AddPACGA w__0 w__1) ) : SailM (BitVec 64) )
      (X_set d 64 w__2))
  else
    (do
      let w__3 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
      let w__4 ← (( do (X_read m 64) ) : SailM (BitVec 64) )
      let w__5 ← (( do (AddPACGA w__3 w__4) ) : SailM (BitVec 64) )
      (X_set d 64 w__5))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacia_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AddPACIA w__1 w__2) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AddPACIA w__4 w__5) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_pacib_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AddPACIB w__1 w__2) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AddPACIB w__4 w__5) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


def execute_ZERO_ZT_I__ (_ : Unit) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (FailTransaction TMFailure_ERR false))
  else (pure (()))
  (ZT0_set 512 (Zeros (n := 512)))


/-- Type quantifiers: offset : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_MOVT_R_ZT__ (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let operand ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let w__0 ← (( do (Elem_read operand offset 64) ) : SailM (BitVec 64) )
  (X_set t 64 w__0)


/-- Type quantifiers: offset : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧ List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_MOVT_ZT_R__ (offset : Nat) (t : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  (CheckSMEZT0Enabled ())
  let result ← (( do (ZT0_read 512) ) : SailM (BitVec 512) )
  let w__0 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
  let w__1 ← (( do (Elem_set result offset 64 w__0) ) : SailM (BitVec 512) )
  let result := (w__1 : (BitVec 512))
  (ZT0_set 512 result)


/-- Type quantifiers: SVL : Nat, d : Nat, imm : Int, 0 ≤ d ∧ d ≤ 31 ∧ (is_VL SVL) -/
def execute_RDSVL_R_I__ (SVL : Nat) (d : Nat) (imm : Int) : SailM Unit := do
  (CheckSMEEnabled ())
  let SVL : Nat := SVL
  let len : Int := (imm *i (Int.ediv SVL 8))
  (X_set d 64 (integer_subrange len 63 0))


/-- Type quantifiers: SVL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL SVL) -/
def execute_ADDSPL_R_RI__ (SVL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  let SVL : Nat := SVL
  let len : Int := (imm *i (Int.ediv SVL 64))
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 len)
  if ((d == 31) : Bool)
  then
    (do
      (SP_set result))
  else
    (do
      (X_set d 64 result))


/-- Type quantifiers: SVL : Nat, d : Nat, imm : Int, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL SVL) -/
def execute_ADDSVL_R_RI__ (SVL : Nat) (d : Nat) (imm : Int) (n : Nat) : SailM Unit := do
  (CheckSMEEnabled ())
  let SVL : Nat := SVL
  let len : Int := (imm *i (Int.ediv SVL 8))
  let operand1 ← (( do
    if ((n == 31) : Bool)
    then
      (do
        (SP_read ()))
    else
      (do
        (X_read n 64)) ) : SailM (BitVec 64) )
  let result : (BitVec 64) := (BitVec.addInt operand1 len)
  if ((d == 31) : Bool)
  then
    (do
      (SP_set result))
  else
    (do
      (X_set d 64 result))


/-- Type quantifiers: k_iswrite : Bool, size : Int -/
def HandleExternalAbort (memretstatus : PhysMemRetStatus) (iswrite : Bool) (memaddrdesc : AddressDescriptor) (size : Int) (accdesc : AccessDescriptor) : SailM Unit := do
  let w__2 ← (( do
    if ((((BEq.beq memretstatus.statuscode Fault_SyncExternal) || (BEq.beq memretstatus.statuscode
           Fault_AsyncExternal)) : Bool) : Bool)
    then (pure true)
    else
      (do
        (pure ((← do
              let w__0 ← (( do (HaveRASExt ()) ) : SailM Bool )
              (pure (((! w__0) : Bool)))) && (((BEq.beq memretstatus.statuscode Fault_SyncParity) || (BEq.beq
                memretstatus.statuscode Fault_AsyncParity)) : Bool)))) ) : SailM Bool )
  ArmFull.assert w__2 "sail-inputs/03-v8_base.sail:15313.227-15313.228"
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let fault : FaultRecord := { fault with statuscode := memretstatus.statuscode }
  let fault : FaultRecord := { fault with write := iswrite }
  let fault : FaultRecord := { fault with extflag := memretstatus.extflag }
  let w__5 ← (( do
    if ((← do
         (IsExternalSyncAbort__1 fault)) : Bool)
    then
      (do
        let w__4 ← (( do
          (IsExternalAbortTakenSynchronously memretstatus iswrite memaddrdesc size accdesc) ) :
          SailM Bool )
        (pure (((! w__4) : Bool))))
    else (pure false) ) : SailM Bool )
  let fault : FaultRecord :=
    if (w__5 : Bool)
    then
      (if ((BEq.beq fault.statuscode Fault_SyncParity) : Bool)
      then { fault with statuscode := Fault_AsyncParity }
      else { fault with statuscode := Fault_AsyncExternal })
    else fault
  let w__6 ← (( do (HaveRASExt ()) ) : SailM Bool )
  let fault : FaultRecord :=
    if (w__6 : Bool)
    then { fault with merrorstate := memretstatus.merrorstate }
    else fault
  let w__7 ← (( do (IsExternalSyncAbort__1 fault) ) : SailM Bool )
  if (w__7 : Bool)
  then
    (do
      let w__8 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          (AArch32_Abort (Sail.BitVec.extractLsb memaddrdesc.vaddress 31 0) fault))
      else
        (do
          (AArch64_Abort memaddrdesc.vaddress fault)))
  else (pure ((PendSErrorInterrupt fault)))


def FPProcessException (except : FPExc) (fpcr : (BitVec 64)) : SailM Unit := do
  let is_ase ← (( do (undefined_bool_at (← occLabel 890) ()) ) : SailM Bool )
  let cumul : Int := 0
  let cumul : Int :=
    match except with
    | .FPExc_InvalidOp => 0
    | .FPExc_DivideByZero => 1
    | .FPExc_Overflow => 2
    | .FPExc_Underflow => 3
    | .FPExc_Inexact => 4
    | .FPExc_InputDenorm => 7
  let cumul : Int := cumul
  let enable : Int := (cumul +i 8)
  let w__5 ← (( do
    if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access fpcr (Sail.Int.toNatChecked (enable)))])) == 1#1) : Bool) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__0 ← (( do (HaveSME ()) ) : SailM Bool )
                  (pure (((! w__0) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__1.SM == 0#1) : Bool))))) : Bool)
        then (pure true)
        else
          (do
            (IsFullA64Enabled ())))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool)
  then
    (do
      let accumulated_exceptions ← (( do (GetAccumulatedFPExceptions ()) ) : SailM (BitVec 8) )
      let accumulated_exceptions : (BitVec 8) :=
        (BitVec.update accumulated_exceptions (Sail.Int.toNatChecked (cumul)) (Bit 1#1))
      let w__6 ← (( do (__IMPDEF_boolean "Support trapping of floating-point exceptions") ) :
        SailM Bool )
      if (w__6 : Bool)
      then
        (do
          let w__7 ← (( do (UsingAArch32 ()) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              (AArch32_FPTrappedException accumulated_exceptions))
          else
            (do
              let is_ase ← (( do (IsASEInstruction ()) ) : SailM Bool )
              (AArch64_FPTrappedException is_ase accumulated_exceptions)))
      else (pure ((SetAccumulatedFPExceptions accumulated_exceptions))))
  else
    (do
      let w__8 ← (( do (UsingAArch32 ()) ) : SailM Bool )
      if (w__8 : Bool)
      then
        (do
          let w__9 ← (( do (FPSCR_read__1 ()) ) : SailM (BitVec 32) )
          (FPSCR_write
            (Mk_FPSCR_Type
              (Sail.BitVec.updateSubrange w__9 (Sail.Int.toNatChecked (cumul))
                (Sail.Int.toNatChecked (cumul)) (Sail.BitVec.castWidth 1#1)))))
      else
        (do
          let w__10 ← (( do readReg FPSR ) : SailM (BitVec 64) )
          writeReg FPSR (BitVec.update w__10 (Sail.Int.toNatChecked (cumul)) (Bit 1#1))))


/-- Type quantifiers: k_aligned : Bool -/
def AArch64_FullTranslate (va : (BitVec 64)) (accdesc : AccessDescriptor) (aligned : Bool) : SailM AddressDescriptor := do
  let s1aarch64 ← (( do (undefined_bool_at (← occLabel 1623) ()) ) : SailM Bool )
  let regime ← (( do (TranslationRegime accdesc.el) ) : SailM Regime )
  let fault ← (( do (NoFault__1 accdesc) ) : SailM FaultRecord )
  let ipa ← (( do (undefined_AddressDescriptor (← occLabel 1624) ()) ) : SailM AddressDescriptor
    )
  let w__0 ← (( do (AArch64_S1Translate fault regime va aligned accdesc) ) : SailM
    (FaultRecord × AddressDescriptor) )
  let (tup__0, tup__1) := (w__0 : (FaultRecord × AddressDescriptor))
  let fault : FaultRecord := tup__0
  let ipa : AddressDescriptor := tup__1
  if ((bne fault.statuscode Fault_None) : Bool)
  then
    (do
      (CreateFaultyAddressDescriptor va fault))
  else
    (do
      let w__2 ← (( do (EL2Enabled ()) ) : SailM Bool )
      ArmFull.assert (implies (BEq.beq accdesc.ss SS_Realm) w__2) "sail-inputs/03-v8_base.sail:27784.54-27784.55"
      let w__4 ← (( do
        if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
        then
          (do
            (EL2Enabled ()))
        else (pure false) ) : SailM Bool )
      if (w__4 : Bool)
      then
        (do
          let s1aarch64 : Bool := true
          let pa ← (( do (undefined_AddressDescriptor (← occLabel 1625) ()) ) : SailM
            AddressDescriptor )
          let w__5 ← (( do (AArch64_S2Translate fault ipa s1aarch64 none aligned accdesc) ) :
            SailM (FaultRecord × AddressDescriptor) )
          let (tup__0, tup__1) := (w__5 : (FaultRecord × AddressDescriptor))
          let fault : FaultRecord := tup__0
          let pa : AddressDescriptor := tup__1
          if ((bne fault.statuscode Fault_None) : Bool)
          then
            (do
              (CreateFaultyAddressDescriptor va fault))
          else (pure (pa)))
      else (pure (ipa)))


def CheckSVEEnabled (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         (HaveSME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.SM == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (CheckSMEEnabled ()))
  else
    (do
      let w__5 ← (( do
        if ((← do
             (HaveSME ())) : Bool)
        then
          (do
            let w__4 ← (( do (HaveSVE ()) ) : SailM Bool )
            (pure (((! w__4) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__5 : Bool)
      then
        (do
          (CheckStreamingSVEEnabled ()))
      else
        (do
          (CheckOriginalSVEEnabled ())))


def CheckStreamingSVEAndZAEnabled (_ : Unit) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.ZA == 0#1) : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      (SMEAccessTrap SMEExceptionType_InactiveZA w__1.EL))
  else (pure (()))


def AArch64_CheckFPAdvSIMDEnabled (_ : Unit) : SailM Unit := do
  (AArch64_CheckFPEnabled ())
  let w__4 ← (( do
    if ((← do
         if ((← do
              (HaveSME ())) : Bool)
         then
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.SM == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do (IsFullA64Enabled ()) ) : SailM Bool )
        (pure (((! w__3) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      (SMEAccessTrap SMEExceptionType_Streaming w__5.EL))
  else (pure (()))


def CheckFPEnabled64 (_ : Unit) : SailM Unit := do
  (AArch64_CheckFPEnabled ())


/-- Type quantifiers: k_aligned : Bool -/
def AArch32_S1TranslateLD (fault_in : FaultRecord) (regime : Regime) (va : (BitVec 32)) (aligned : Bool) (accdesc : AccessDescriptor) : SailM (FaultRecord × AddressDescriptor) := do
  let fault : FaultRecord := fault_in
  let w__0 ← (( do (AArch32_S1Enabled regime accdesc.ss) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (AArch32_S1DisabledOutput fault regime va aligned accdesc))
  else
    (do
      let walkparams ← (( do (AArch32_GetS1TTWParams regime va) ) : SailM S1TTWParams )
      let w__2 ← (( do (AArch32_VAIsOutOfRange regime walkparams va) ) : SailM Bool )
      if (w__2 : Bool)
      then
        (do
          let fault : FaultRecord := { fault with level := 1 }
          let fault : FaultRecord := { fault with statuscode := Fault_Translation }
          let w__3 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
          (pure ((fault, w__3))))
      else
        (do
          let walkstate ← (( do (undefined_TTWState (← occLabel 2576) ()) ) : SailM TTWState )
          let w__4 ← (( do (AArch32_S1WalkLD fault regime walkparams accdesc va) ) : SailM
            (FaultRecord × TTWState) )
          let (tup__0, tup__1) := (w__4 : (FaultRecord × TTWState))
          let fault : FaultRecord := tup__0
          let walkstate : TTWState := tup__1
          if ((bne fault.statuscode Fault_None) : Bool)
          then
            (do
              let w__5 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
              (pure ((fault, w__5))))
          else
            (do
              (SetInGuardedPage false)
              let fault ← (( do
                if ((AArch32_S1HasAlignmentFault accdesc aligned walkparams.ntlsmd
                     walkstate.memattrs) : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
                  (pure (fault)))
                else
                  (do
                    let w__6 ← (( do
                      (AArch32_S1LDHasPermissionsFault regime walkparams walkstate.permissions
                        walkstate.memattrs.memtype walkstate.baseaddress.paspace accdesc) ) : SailM
                      Bool )
                    let fault : FaultRecord :=
                      if (w__6 : Bool)
                      then { fault with statuscode := Fault_Permission }
                      else fault
                    (pure (fault))) ) : SailM FaultRecord )
              if ((bne fault.statuscode Fault_None) : Bool)
              then
                (do
                  let w__7 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
                  (pure ((fault, w__7))))
              else
                (do
                  let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 2577) ()) ) :
                    SailM MemoryAttributes )
                  let w__13 ← (( do
                    if ((← do
                         if (((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool) : Bool)
                         then
                           (do
                             if (((BEq.beq walkstate.memattrs.memtype MemType_Device) : Bool) : Bool)
                             then (pure true)
                             else
                               (do
                                 let w__8 ← (( do (AArch32_S1ICacheEnabled regime) ) : SailM Bool
                                   )
                                 (pure (((! w__8) : Bool)))))
                         else (pure false)) : Bool)
                    then (pure true)
                    else
                      (do
                        if ((((bne accdesc.acctype AccessType_IFETCH) && (BEq.beq
                               walkstate.memattrs.memtype MemType_Normal)) : Bool) : Bool)
                        then
                          (do
                            let w__11 ← (( do (AArch32_S1DCacheEnabled regime) ) : SailM Bool )
                            (pure (((! w__11) : Bool))))
                        else (pure false)) ) : SailM Bool )
                  let memattrs ← (( do
                    if (w__13 : Bool)
                    then
                      (do
                        let w__14 ← (( do (NormalNCMemAttr ()) ) : SailM MemoryAttributes )
                        let memattrs := (w__14 : MemoryAttributes)
                        let memattrs : MemoryAttributes :=
                          { memattrs with xs := walkstate.memattrs.xs }
                        (pure (memattrs)))
                    else
                      (let memattrs : MemoryAttributes := walkstate.memattrs
                      (pure (memattrs))) ) : SailM MemoryAttributes )
                  let w__23 ← (( do
                    if ((← do
                         if ((← do
                              if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                              then
                                (do
                                  (AArch32_EL2Enabled accdesc.ss))
                              else (pure false)) : Bool)
                         then
                           (do
                             let w__17 ← (( do
                               (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) ) : SailM
                               Bool )
                             let w__20 ← (( do
                               if (w__17 : Bool)
                               then
                                 (do
                                   let w__18 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                   (pure ((_get_HCR_Type_VM w__18))))
                               else
                                 (do
                                   let w__19 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                   (pure ((_get_HCR_EL2_Type_VM w__19)))) ) : SailM (BitVec 1) )
                             (pure (((w__20 == 1#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__22 ← (( do
                          (__IMPDEF_boolean "Apply effective shareability at stage 1") ) : SailM
                          Bool )
                        (pure (((! w__22) : Bool))))
                    else (pure false) ) : SailM Bool )
                  let memattrs : MemoryAttributes :=
                    if (w__23 : Bool)
                    then { memattrs with shareability := walkstate.memattrs.shareability }
                    else { memattrs with shareability := (EffectiveShareability memattrs) }
                  let oa ← (( do
                    (StageOA (Sail.BitVec.zeroExtend va 64) walkparams.d128 walkparams.tgx walkstate)
                    ) : SailM FullAddress )
                  let ipa ← (( do
                    (CreateAddressDescriptor (Sail.BitVec.zeroExtend va 64) oa memattrs) ) : SailM
                    AddressDescriptor )
                  (pure ((fault, ipa)))))))


/-- Type quantifiers: k_aligned : Bool -/
def AArch32_S1TranslateSD (fault_in : FaultRecord) (regime : Regime) (va : (BitVec 32)) (aligned : Bool) (accdesc : AccessDescriptor) : SailM (FaultRecord × AddressDescriptor × SDFType) := do
  let ipa ← (( do (undefined_AddressDescriptor (← occLabel 2632) ()) ) : SailM AddressDescriptor
    )
  let fault : FaultRecord := fault_in
  let w__0 ← (( do (AArch32_S1Enabled regime accdesc.ss) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let w__1 ← (( do (undefined_AddressDescriptor (← occLabel 2636) ()) ) : SailM
        AddressDescriptor )
      let ipa : AddressDescriptor := (w__1 : AddressDescriptor)
      let w__2 ← (( do (AArch32_S1DisabledOutput fault regime va aligned accdesc) ) : SailM
        (FaultRecord × AddressDescriptor) )
      let (tup__0, tup__1) := (w__2 : (FaultRecord × AddressDescriptor))
      let fault : FaultRecord := tup__0
      let ipa : AddressDescriptor := tup__1
      let w__3 ← (( do (__UNKNOWN_SDFType ()) ) : SailM SDFType )
      (pure ((fault, ipa, w__3))))
  else
    (do
      let walkstate ← (( do (undefined_TTWState (← occLabel 2633) ()) ) : SailM TTWState )
      let w__4 ← (( do (AArch32_S1WalkSD fault regime accdesc va) ) : SailM
        (FaultRecord × TTWState) )
      let (tup__0, tup__1) := (w__4 : (FaultRecord × TTWState))
      let fault : FaultRecord := tup__0
      let walkstate : TTWState := tup__1
      if ((bne fault.statuscode Fault_None) : Bool)
      then
        (do
          let w__5 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
          let w__6 ← (( do (__UNKNOWN_SDFType ()) ) : SailM SDFType )
          (pure ((fault, w__5, w__6))))
      else
        (do
          let domain ← (( do (AArch32_OutputDomain regime walkstate.domain) ) : SailM (BitVec 2) )
          (SetInGuardedPage false)
          let ntlsmd ← (( do (undefined_bitvector_at (← occLabel 2634) 1) ) : SailM (BitVec 1) )
          let w__7 ← (( do (HaveTrapLoadStoreMultipleDeviceExt ()) ) : SailM Bool )
          let ntlsmd ← (( do
            if (w__7 : Bool)
            then
              (do
                match regime with
                | .Regime_EL30 =>
                  (do
                    let w__8 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
                    let ntlsmd := ((_get_SCTLR_Type_nTLSMD w__8) : (BitVec 1))
                    (pure (ntlsmd)))
                | .Regime_EL10 =>
                  (do
                    let w__9 ← (( do (HaveAArch32EL EL3) ) : SailM Bool )
                    if (w__9 : Bool)
                    then
                      (do
                        let w__10 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
                        (pure ((_get_SCTLR_Type_nTLSMD w__10))))
                    else
                      (do
                        let w__11 ← (( do (SCTLR_read__2 ()) ) : SailM (BitVec 32) )
                        (pure ((_get_SCTLR_Type_nTLSMD w__11)))))
                | _ => (pure (ntlsmd)))
            else (pure (1#1)) ) : SailM (BitVec 1) )
          let fault ← (( do
            if ((AArch32_S1HasAlignmentFault accdesc aligned ntlsmd walkstate.memattrs) : Bool)
            then
              (let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
              (pure (fault)))
            else
              (do
                if (((! ((BEq.beq accdesc.acctype AccessType_IC) || (BEq.beq accdesc.acctype
                           AccessType_DC))) && (domain == Domain_NoAccess)) : Bool)
                then
                  (let fault : FaultRecord := { fault with statuscode := Fault_Domain }
                  (pure (fault)))
                else
                  (do
                    if ((domain == Domain_Client) : Bool)
                    then
                      (do
                        let w__13 ← (( do
                          (AArch32_S1SDHasPermissionsFault regime walkstate.permissions
                            walkstate.memattrs.memtype walkstate.baseaddress.paspace accdesc) ) :
                          SailM Bool )
                        let fault : FaultRecord :=
                          if (w__13 : Bool)
                          then { fault with statuscode := Fault_Permission }
                          else fault
                        (pure (fault)))
                    else (pure (fault)))) ) : SailM FaultRecord )
          if ((bne fault.statuscode Fault_None) : Bool)
          then
            (do
              let fault : FaultRecord := { fault with domain := walkstate.domain }
              let w__14 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
              (pure ((fault, w__14, walkstate.sdftype))))
          else
            (do
              let memattrs ← (( do (undefined_MemoryAttributes (← occLabel 2635) ()) ) : SailM
                MemoryAttributes )
              let w__20 ← (( do
                if ((← do
                     if (((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool) : Bool)
                     then
                       (do
                         if (((BEq.beq walkstate.memattrs.memtype MemType_Device) : Bool) : Bool)
                         then (pure true)
                         else
                           (do
                             let w__15 ← (( do (AArch32_S1ICacheEnabled regime) ) : SailM Bool )
                             (pure (((! w__15) : Bool)))))
                     else (pure false)) : Bool)
                then (pure true)
                else
                  (do
                    if ((((bne accdesc.acctype AccessType_IFETCH) && (BEq.beq
                           walkstate.memattrs.memtype MemType_Normal)) : Bool) : Bool)
                    then
                      (do
                        let w__18 ← (( do (AArch32_S1DCacheEnabled regime) ) : SailM Bool )
                        (pure (((! w__18) : Bool))))
                    else (pure false)) ) : SailM Bool )
              let memattrs ← (( do
                if (w__20 : Bool)
                then
                  (do
                    let w__21 ← (( do (NormalNCMemAttr ()) ) : SailM MemoryAttributes )
                    let memattrs := (w__21 : MemoryAttributes)
                    let memattrs : MemoryAttributes := { memattrs with xs := walkstate.memattrs.xs }
                    (pure (memattrs)))
                else
                  (let memattrs : MemoryAttributes := walkstate.memattrs
                  (pure (memattrs))) ) : SailM MemoryAttributes )
              let w__30 ← (( do
                if ((← do
                     if ((← do
                          if (((BEq.beq regime Regime_EL10) : Bool) : Bool)
                          then
                            (do
                              (AArch32_EL2Enabled accdesc.ss))
                          else (pure false)) : Bool)
                     then
                       (do
                         let w__24 ← (( do
                           (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) ) : SailM Bool )
                         let w__27 ← (( do
                           if (w__24 : Bool)
                           then
                             (do
                               let w__25 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                               (pure ((_get_HCR_Type_VM w__25))))
                           else
                             (do
                               let w__26 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                               (pure ((_get_HCR_EL2_Type_VM w__26)))) ) : SailM (BitVec 1) )
                         (pure (((w__27 == 1#1) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__29 ← (( do (__IMPDEF_boolean "Apply effective shareability at stage 1")
                      ) : SailM Bool )
                    (pure (((! w__29) : Bool))))
                else (pure false) ) : SailM Bool )
              let memattrs : MemoryAttributes :=
                if (w__30 : Bool)
                then { memattrs with shareability := walkstate.memattrs.shareability }
                else { memattrs with shareability := (EffectiveShareability memattrs) }
              let oa ← (( do (AArch32_SDStageOA walkstate.baseaddress va walkstate.sdftype) ) :
                SailM FullAddress )
              let ipa ← (( do (CreateAddressDescriptor (Sail.BitVec.zeroExtend va 64) oa memattrs)
                ) : SailM AddressDescriptor )
              (pure ((fault, ipa, walkstate.sdftype))))))


end ArmFull.Functions
