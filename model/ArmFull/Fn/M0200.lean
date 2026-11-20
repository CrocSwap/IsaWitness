module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0062
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0071
public import ArmFull.Fn.M0079
public import ArmFull.Fn.M0081
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0190 set_option backward.proofsInPublic true @[expose] public section

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

def SPE_PMBIDR_P_Read (_ : Unit) : SailM (BitVec 1) := do
  let owning_ss ← (( do (undefined_SecurityState (← occLabel 2447) ()) ) : SailM SecurityState )
  let owning_el ← (( do (undefined_bitvector_at (← occLabel 2448) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do (ProfilingBufferOwner ()) ) : SailM (SecurityState × (BitVec 2)) )
  let (tup__0, tup__1) := (w__0 : (SecurityState × (BitVec 2)))
  let owning_ss : SecurityState := tup__0
  let owning_el : (BitVec 2) := tup__1
  let w__5 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure ((((BitVec.toNat owning_el) >b (BitVec.toNat w__1.EL)) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((← do
             let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__2.EL != EL3) : Bool)))) : Bool)
        then
          (do
            let w__3 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((bne owning_ss w__3) : Bool))))
        else (pure false)) ) : SailM Bool )
  let w__6 : (BitVec 1) :=
    if (w__5 : Bool)
    then 1#1
    else 0#1
  (pure (w__6))


def DACR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_DACR_Type (← occLabel 2579) ()) ) : SailM DACR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg DACR_S)
  else
    (do
      (DACR_NS_read ()))


def BankedRegisterAccessValid (SYSm : (BitVec 5)) (mode : (BitVec 5)) : SailM Unit := do
  let b__0 := SYSm
  if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 4 2)) == (0b000#3 : (BitVec 3))) : Bool)
  then
    (do
      if ((mode != M32_FIQ) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  else
    (do
      match b__0 with
      | 0b00100 =>
        (do
          if ((mode != M32_FIQ) : Bool)
          then sailThrow ((Error_Unpredictable ()))
          else (pure (())))
      | 0b00101 =>
        (do
          if ((mode == M32_System) : Bool)
          then sailThrow ((Error_Unpredictable ()))
          else (pure (())))
      | 0b00110 =>
        (do
          if (((mode == M32_Hyp) || (mode == M32_System)) : Bool)
          then sailThrow ((Error_Unpredictable ()))
          else (pure (())))
      | b__0 =>
        (do
          if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__0 4 2)) == (0b010#3 : (BitVec 3))) : Bool)
          then
            (do
              if ((mode == M32_FIQ) : Bool)
              then sailThrow ((Error_Unpredictable ()))
              else (pure (())))
          else
            (do
              if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x6#4 : (BitVec 4))) : Bool)
              then
                (do
                  if ((mode == M32_FIQ) : Bool)
                  then sailThrow ((Error_Unpredictable ()))
                  else (pure (())))
              else
                (do
                  match b__0 with
                  | 0b01110 =>
                    (do
                      if ((mode == M32_FIQ) : Bool)
                      then sailThrow ((Error_Unpredictable ()))
                      else (pure (())))
                  | b__0 =>
                    (do
                      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x8#4 : (BitVec 4))) : Bool)
                      then
                        (do
                          if ((mode == M32_IRQ) : Bool)
                          then sailThrow ((Error_Unpredictable ()))
                          else (pure (())))
                      else
                        (do
                          if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0x9#4 : (BitVec 4))) : Bool)
                          then
                            (do
                              if ((mode == M32_Svc) : Bool)
                              then sailThrow ((Error_Unpredictable ()))
                              else (pure (())))
                          else
                            (do
                              if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0 4 1)) == (0xA#4 : (BitVec 4))) : Bool)
                              then
                                (do
                                  if ((mode == M32_Abort) : Bool)
                                  then sailThrow ((Error_Unpredictable ()))
                                  else (pure (())))
                              else
                                (do
                                  if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb b__0
                                         4 1)) == (0xB#4 : (BitVec 4))) : Bool)
                                  then
                                    (do
                                      if ((mode == M32_Undef) : Bool)
                                      then sailThrow ((Error_Unpredictable ()))
                                      else (pure (())))
                                  else
                                    (do
                                      if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                             b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                      then
                                        (do
                                          let w__3 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       let w__0 ← (( do (HaveEL EL3) ) : SailM
                                                         Bool )
                                                       (pure (((! w__0) : Bool)))) : Bool)
                                                  then (pure true)
                                                  else
                                                    (do
                                                      let w__1 ← (( do (CurrentSecurityState ()) )
                                                        : SailM SecurityState )
                                                      (pure (((bne w__1 SS_Secure) : Bool))))) || ((mode == M32_Monitor) : Bool)))
                                            ) : SailM Bool )
                                          if (w__3 : Bool)
                                          then sailThrow ((Error_Unpredictable ()))
                                          else (pure (())))
                                      else
                                        (do
                                          match b__0 with
                                          | 0b11110 =>
                                            (do
                                              let w__5 ← (( do
                                                (pure ((← do
                                                      let w__4 ← (( do (HaveEL EL2) ) : SailM Bool
                                                        )
                                                      (pure (((! w__4) : Bool)))) || ((! ((mode == M32_Monitor) || (mode == M32_Hyp))) : Bool)))
                                                ) : SailM Bool )
                                              if (w__5 : Bool)
                                              then sailThrow ((Error_Unpredictable ()))
                                              else (pure (())))
                                          | 0b11111 =>
                                            (do
                                              let w__7 ← (( do
                                                (pure ((← do
                                                      let w__6 ← (( do (HaveEL EL2) ) : SailM Bool
                                                        )
                                                      (pure (((! w__6) : Bool)))) || ((mode != M32_Monitor) : Bool)))
                                                ) : SailM Bool )
                                              if (w__7 : Bool)
                                              then sailThrow ((Error_Unpredictable ()))
                                              else (pure (())))
                                          | _ => sailThrow ((Error_Unpredictable ()))))))))))))


def CPSRWriteByInstr (value_name : (BitVec 32)) (bytemask : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 3)])) == 1#1) : Bool)
  then
    (do
      let split_vec := (Sail.BitVec.extractLsb value_name 31 27)
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb split_vec 4 4) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb split_vec 3 3) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb split_vec 2 2) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb split_vec 1 1) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Q := (Sail.BitVec.extractLsb split_vec 0 0) })
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 2)])) == 1#1) : Bool)
  then
    (do
      let w__6 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__7 with SSBS := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 23)])) })
      else (pure (()))
      if (privileged : Bool)
      then
        (do
          let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__8 with PAN := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 22)])) })
      else (pure (()))
      let w__9 ← (( do (HaveDITExt ()) ) : SailM Bool )
      if (w__9 : Bool)
      then
        (do
          let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__10 with DIT := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 21)])) })
      else (pure (()))
      let w__11 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__11 with GE := (Sail.BitVec.extractLsb value_name 19 16) })
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 1)])) == 1#1) : Bool)
  then
    (do
      let w__12 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__12 with E := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access value_name
            9)])) }
      if (privileged : Bool)
      then
        (do
          let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__13 with A := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                value_name 8)])) })
      else (pure (())))
  else (pure (()))
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access bytemask 0)])) == 1#1) : Bool)
  then
    (do
      if (privileged : Bool)
      then
        (do
          let split_vec := (Sail.BitVec.extractLsb value_name 7 6)
          let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__14 with I := (Sail.BitVec.extractLsb split_vec 1 1) }
          let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
          writeReg PSTATE { w__15 with F := (Sail.BitVec.extractLsb split_vec 0 0) }
          (AArch32_WriteModeByInstr (Sail.BitVec.extractLsb value_name 4 0)))
      else (pure (())))
  else (pure (()))


def SPSRaccessValid (SYSm : (BitVec 5)) (mode : (BitVec 5)) : SailM Unit := do
  match SYSm with
  | 0b01110 =>
    (do
      if ((mode == M32_FIQ) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10000 =>
    (do
      if ((mode == M32_IRQ) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10010 =>
    (do
      if ((mode == M32_Svc) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10100 =>
    (do
      if ((mode == M32_Abort) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b10110 =>
    (do
      if ((mode == M32_Undef) : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b11100 =>
    (do
      let w__3 ← (( do
        if ((← do
             (pure ((← do
                   let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
                   (pure (((! w__0) : Bool)))) || ((mode == M32_Monitor) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            let w__2 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((bne w__2 SS_Secure) : Bool)))) ) : SailM Bool )
      if (w__3 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | 0b11110 =>
    (do
      let w__5 ← (( do
        (pure ((← do
              let w__4 ← (( do (HaveEL EL2) ) : SailM Bool )
              (pure (((! w__4) : Bool)))) || ((mode != M32_Monitor) : Bool))) ) : SailM Bool )
      if (w__5 : Bool)
      then sailThrow ((Error_Unpredictable ()))
      else (pure (())))
  | _ => sailThrow ((Error_Unpredictable ()))


def AArch32_ClearEventCounters (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (AArch64_ClearEventCounters ()))
  else
    (do
      let counters ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
      if ((counters != 0) : Bool)
      then
        (do
          let loop_idx_lower : Nat := 0
          let loop_idx_upper : Int := (counters -i 1)
          (do
            let mut loop_vars := ()
            for idx in [loop_idx_lower:loop_idx_upper:1]i do
              let () := loop_vars
              loop_vars ← do
                ArmFull.assert (0 ≤b idx) "sail-inputs/03-v8_base.sail:43522.45-43522.46"
                ArmFull.assert (idx <b 31) "sail-inputs/03-v8_base.sail:43523.45-43523.46"
                (PMEVCNTR_set (Sail.Int.toNatChecked (idx)) (Zeros (n := 32)))
            (pure loop_vars)))
      else (pure (())))


/-- Type quantifiers: n : Int -/
def ICC_AP1R_EL1_read (n : Int) : SailM (BitVec 64) := do
  let r ← (( do (undefined_ICC_AP1R_EL1_Type (← occLabel 2815) ()) ) : SailM ICC_AP1R_EL1_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:44777.45-44777.46"
      let w__3 ← (( do readReg ICC_AP1R_EL1_S ) : SailM (Vector (BitVec 64) 4) )
      let r := ((GetElem?.getElem! w__3 (Sail.Int.toNatChecked (n))) : (BitVec 64))
      (pure (r)))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:44780.45-44780.46"
      let w__4 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM (Vector (BitVec 64) 4) )
      let r := ((GetElem?.getElem! w__4 (Sail.Int.toNatChecked (n))) : (BitVec 64))
      (pure (r)))


/-- Type quantifiers: n : Int -/
def ICC_AP1R_EL1_set (n : Int) (value_name : (BitVec 64)) : SailM Unit := do
  let r : ICC_AP1R_EL1_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:44791.45-44791.46"
      let w__3 ← (( do readReg ICC_AP1R_EL1_S ) : SailM (Vector (BitVec 64) 4) )
      writeReg ICC_AP1R_EL1_S (vectorUpdate w__3 (Sail.Int.toNatChecked (n)) r))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:44794.45-44794.46"
      let w__4 ← (( do readReg ICC_AP1R_EL1_NS ) : SailM (Vector (BitVec 64) 4) )
      writeReg ICC_AP1R_EL1_NS (vectorUpdate w__4 (Sail.Int.toNatChecked (n)) r))


def CNTP_CVAL_write (value_name : (BitVec 64)) : SailM Unit := do
  let r : CNTP_CVAL_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg CNTP_CVAL_S r)
  else
    (do
      (CNTP_CVAL_NS_write r))


def AIFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2835) 32) ) : SailM AIFSR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg AIFSR_S)
  else
    (do
      (AIFSR_NS_read ()))


def AIFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : AIFSR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg AIFSR_S r)
  else
    (do
      (AIFSR_NS_write r))


def DACR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : DACR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg DACR_S r)
  else
    (do
      (DACR_NS_write r))


def TPIDRURW_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2836) 32) ) : SailM TPIDRURW_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg TPIDRURW_S)
  else
    (do
      (TPIDRURW_NS_read ()))


def TPIDRURW_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURW_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg TPIDRURW_S r)
  else
    (do
      (TPIDRURW_NS_write r))


def ADFSR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2837) 32) ) : SailM ADFSR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg ADFSR_S)
  else
    (do
      (ADFSR_NS_read ()))


def ADFSR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ADFSR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg ADFSR_S r)
  else
    (do
      (ADFSR_NS_write r))


def TPIDRURO_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2838) 32) ) : SailM TPIDRURO_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg TPIDRURO_S)
  else
    (do
      (TPIDRURO_NS_read ()))


def TPIDRURO_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : TPIDRURO_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg TPIDRURO_S r)
  else
    (do
      (TPIDRURO_NS_write r))


def ACTLR_read (_ : Unit) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2840) 32) ) : SailM ACTLR_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      readReg ACTLR_S)
  else
    (do
      (ACTLR_NS_read ()))


def ACTLR_write (value_name : (BitVec 32)) : SailM Unit := do
  let r : ACTLR_Type := value_name
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      writeReg ACTLR_S r)
  else
    (do
      (ACTLR_NS_write r))


/-- Type quantifiers: n : Int -/
def ICC_AP1R_read (n : Int) : SailM (BitVec 32) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 2843) 32) ) : SailM ICC_AP1R_Type )
  let w__2 ← (( do
    if ((← do
         (ELUsingAArch32 EL3)) : Bool)
    then
      (do
        let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
        (pure (((BEq.beq w__1 SS_Secure) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:49741.45-49741.46"
      (ICC_AP1R_S_read (Sail.Int.toNatChecked (n))))
  else
    (do
      ArmFull.assert ((0 ≤b n) && (n <b 4)) "sail-inputs/03-v8_base.sail:49744.45-49744.46"
      (ICC_AP1R_NS_read (Sail.Int.toNatChecked (n))))


end ArmFull.Functions
