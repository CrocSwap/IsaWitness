module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0008
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0023
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0043
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0097
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0113
public import ArmFull.Fn.M0115
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: i : Int -/
def C27bSimpleAllowed (which : Unpredictable) (i : Int) : SailM Bool := do
  if ((BEq.beq which Unpredictable_EL2TIMESTAMP) : Bool)
  then
    if ((i != 2) : Bool)
    then (pure true)
    else
      (do
        (HaveECVExt ()))
  else
    (do
      if ((BEq.beq which Unpredictable_EL1TIMESTAMP) : Bool)
      then
        if ((i != 0) : Bool)
        then
          if ((i != 2) : Bool)
          then (pure true)
          else
            (do
              (HaveECVExt ()))
        else (pure false)
      else
        (do
          if ((BEq.beq which Unpredictable_RESERVEDNSxB) : Bool)
          then
            if ((i != 4) : Bool)
            then
              if ((i != 5) : Bool)
              then
                (pure ((← do
                      (HaveSecureEL2Ext ())) || (i ≥b 2)))
              else (pure false)
            else (pure false)
          else
            (do
              if ((BEq.beq which Unpredictable_RESTCF) : Bool)
              then
                if ((i != 3) : Bool)
                then (pure true)
                else
                  (do
                    (HaveMTEAsymFaultExt ()))
              else
                (do
                  if ((BEq.beq which Unpredictable_PMSCR_PCT) : Bool)
                  then
                    if ((i != 2) : Bool)
                    then
                      if ((i != 3) : Bool)
                      then (pure true)
                      else
                        (do
                          (HaveECVExt ()))
                    else (pure false)
                  else
                    (pure (if ((BEq.beq which Unpredictable_RESDACR) : Bool)
                      then (i != 2)
                      else
                        (if ((BEq.beq which Unpredictable_RESTEXCB) : Bool)
                        then ((i != 5) && ((i <b 9) || (i ≥b 16)))
                        else
                          (if ((BEq.beq which Unpredictable_RESPRRR) : Bool)
                          then (i != 3)
                          else true))))))))


def EffectiveSCR_EL3_RW (_ : Unit) : SailM (BitVec 1) := SailME.run do
  let w__0 ← (( do (HaveAArch64 ()) ) : SailME (BitVec 1) Bool )
  if ((! w__0) : Bool)
  then (pure (0#1))
  else
    (do
      let w__3 ← (( do
        if ((← do
             let w__1 ← (( do (HaveAArch32EL EL2) ) : SailME (BitVec 1) Bool )
             (pure (((! w__1) : Bool)))) : Bool)
        then
          (do
            let w__2 ← (( do (HaveAArch32EL EL1) ) : SailME (BitVec 1) Bool )
            (pure (((! w__2) : Bool))))
        else (pure false) ) : SailME (BitVec 1) Bool )
      if (w__3 : Bool)
      then (pure (1#1))
      else
        (do
          let w__4 ← (( do (HaveAArch32EL EL1) ) : SailME (BitVec 1) Bool )
          if (w__4 : Bool)
          then
            (do
              let w__7 ← (( do
                if ((← do
                     let w__5 ← (( do (HaveAArch32EL EL2) ) : SailME (BitVec 1) Bool )
                     (pure (((! w__5) : Bool)))) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
                    (pure ((((_get_SCR_EL3_Type_NS w__6) == 1#1) : Bool))))
                else (pure false) ) : SailME (BitVec 1) Bool )
              if (w__7 : Bool)
              then
                (do
                  SailME.throw (1#1 : (BitVec 1)))
              else
                (do
                  let w__12 ← (( do
                    if ((← do
                         if ((← do
                              (HaveSecureEL2Ext ())) : Bool)
                         then
                           (do
                             let w__9 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
                             (pure ((((_get_SCR_EL3_Type_EEL2 w__9) == 1#1) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__11 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
                        (pure ((((_get_SCR_EL3_Type_NS w__11) == 0#1) : Bool))))
                    else (pure false) ) : SailME (BitVec 1) Bool )
                  if (w__12 : Bool)
                  then
                    (do
                      SailME.throw (1#1 : (BitVec 1)))
                  else (pure (()))))
          else (pure (()))
          let w__13 ← (( do readReg SCR_EL3 ) : SailME (BitVec 1) (BitVec 64) )
          (pure ((_get_SCR_EL3_Type_RW w__13)))))


def ExternalRealmInvasiveDebugEnabled (_ : Unit) : SailM Bool := do
  let w__0 ← (( do (HaveRME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      if ((← do
           (ExternalInvasiveDebugEnabled ())) : Bool)
      then
        (do
          let w__2 ← (( do readReg RLPIDEN ) : SailM Signal )
          (pure (((BEq.beq w__2 Signal_High) : Bool))))
      else (pure false))


def BRBEMispredictAllowed (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         (HaveEL EL2)) : Bool)
    then
      (do
        let w__1 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBCR_EL2_Type_MPRED w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__4 : Bool :=
        if (((_get_BRBCR_EL1_Type_MPRED w__3) == 0#1) : Bool)
        then false
        else true
      (pure (w__4)))


def BRBCycleCountingEnabled (_ : Unit) : SailM Bool := do
  let w__2 ← (( do
    if ((← do
         (HaveEL EL2)) : Bool)
    then
      (do
        let w__1 ← (( do readReg BRBCR_EL2 ) : SailM (BitVec 64) )
        (pure ((((_get_BRBCR_EL2_Type_CC w__1) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then (pure (false))
  else
    (do
      let w__3 ← (( do readReg BRBCR_EL1 ) : SailM (BitVec 64) )
      let w__4 : Bool :=
        if (((_get_BRBCR_EL1_Type_CC w__3) == 0#1) : Bool)
        then false
        else true
      (pure (w__4)))


def BadMode (mode : (BitVec 5)) : SailM Bool := do
  let valid_name ← (( do (undefined_bool_at (← occLabel 572) ()) ) : SailM Bool )
  let questionMark := mode
  let valid_name ← (( do
    if ((questionMark == M32_Monitor) : Bool)
    then
      (do
        (HaveAArch32EL EL3))
    else
      (do
        if ((questionMark == M32_Hyp) : Bool)
        then
          (do
            (HaveAArch32EL EL2))
        else
          (do
            if ((questionMark == M32_FIQ) : Bool)
            then
              (do
                (HaveAArch32EL EL1))
            else
              (do
                if ((questionMark == M32_IRQ) : Bool)
                then
                  (do
                    (HaveAArch32EL EL1))
                else
                  (do
                    if ((questionMark == M32_Svc) : Bool)
                    then
                      (do
                        (HaveAArch32EL EL1))
                    else
                      (do
                        if ((questionMark == M32_Abort) : Bool)
                        then
                          (do
                            (HaveAArch32EL EL1))
                        else
                          (do
                            if ((questionMark == M32_Undef) : Bool)
                            then
                              (do
                                (HaveAArch32EL EL1))
                            else
                              (do
                                if ((questionMark == M32_System) : Bool)
                                then
                                  (do
                                    (HaveAArch32EL EL1))
                                else
                                  (do
                                    if ((questionMark == M32_User) : Bool)
                                    then
                                      (do
                                        (HaveAArch32EL EL0))
                                    else (pure (false)))))))))) ) : SailM Bool )
  let valid_name := valid_name
  (pure ((! valid_name)))


/-- Type quantifiers: nbits_in : Int -/
def ImplementedSVEVectorLength (nbits_in : Int) : SailM Int := SailME.run do
  let maxbits ← (( do (MaxImplementedVL ()) ) : SailME Int Int )
  let w__1 ← (( do
    if ((((128 ≤b maxbits) && (maxbits ≤b 2048)) : Bool) : Bool)
    then
      (do
        (IsPow2 maxbits))
    else (pure false) ) : SailME Int Bool )
  ArmFull.assert w__1 "sail-inputs/03-v8_base.sail:6880.63-6880.64"
  let nbits : Int := (Min.min nbits_in maxbits)
  ArmFull.assert (((128 ≤b nbits) && (nbits ≤b 2048)) && ((Align_int nbits 128) == nbits)) "sail-inputs/03-v8_base.sail:6882.70-6882.71"
  let nbits ← (( do
    let loop_vars ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun nbits => (pure (nbits >b 128))) nbits
      fun nbits => do
        let w__2 ← (( do (IsPow2 nbits) ) : SailME Int Bool )
        if (w__2 : Bool)
        then
          (do
            let nbits : Int := nbits
            ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "sail-inputs/03-v8_base.sail:6886.44-6886.45"
            SailME.throw (nbits : Int)
            (pure (nbits)))
        else
          (let nbits : Int := (nbits -i 128)
          (pure (nbits)))
    (pure loop_vars) ) : SailME Int Int )
  let nbits : Int := nbits
  ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "sail-inputs/03-v8_base.sail:6892.36-6892.37"
  (pure (nbits))


/-- Type quantifiers: nbits_in : Int -/
def ImplementedSMEVectorLength (nbits_in : Int) : SailM Int := SailME.run do
  let maxbits ← (( do (MaxImplementedSVL ()) ) : SailME Int Int )
  ArmFull.assert (((((maxbits == 128) || (maxbits == 256)) || (maxbits == 512)) || (maxbits == 1024)) || (maxbits == 2048)) "sail-inputs/03-v8_base.sail:6939.38-6939.39"
  let nbits : Int := (Min.min nbits_in maxbits)
  ArmFull.assert (((128 ≤b nbits) && (nbits ≤b 2048)) && ((Align_int nbits 128) == nbits)) "sail-inputs/03-v8_base.sail:6941.70-6941.71"
  let nbits ← (( do
    let loop_vars ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun nbits => (pure (nbits >b 128))) nbits
      fun nbits => do
        let w__1 ← (( do
          (pure ((← do
                (IsPow2 nbits)) && ((SupportedPowerTwoSVL nbits) : Bool))) ) : SailME Int Bool )
        if (w__1 : Bool)
        then
          (do
            let nbits : Int := nbits
            ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "sail-inputs/03-v8_base.sail:6945.44-6945.45"
            SailME.throw (nbits : Int)
            (pure (nbits)))
        else
          (let nbits : Int := (nbits -i 128)
          (pure (nbits)))
    (pure loop_vars) ) : SailME Int Int )
  let nbits : Int := 128
  let nbits ← (( do
    let loop_vars_1 ← sailWhileFuelM (α := Int) (fuel := 1048576) (fun nbits => (pure (nbits <b maxbits))) nbits
      fun nbits => do
        if ((SupportedPowerTwoSVL nbits) : Bool)
        then
          (do
            let nbits : Int := nbits
            ArmFull.assert (((((nbits == 128) || (nbits == 256)) || (nbits == 512)) || (nbits == 1024)) || (nbits == 2048)) "sail-inputs/03-v8_base.sail:6954.44-6954.45"
            SailME.throw (nbits : Int)
            (pure (nbits)))
        else
          (let nbits : Int := (nbits *i 2)
          (pure (nbits)))
    (pure loop_vars_1) ) : SailME Int Int )
  (pure (maxbits))


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
  ArmFull.assert w__3 "sail-inputs/03-v8_base.sail:9307.49-9307.50"
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
  let opc ← (( do (undefined_bitvector_at (.site 722) 4) ) : SailM (BitVec 4) )
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
  let CRm ← (( do (undefined_bitvector_at (.site 723) 4) ) : SailM (BitVec 4) )
  let op2 ← (( do (undefined_bitvector_at (.site 724) 3) ) : SailM (BitVec 3) )
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


def MPAM1_EL1_read (_ : Unit) : SailM (BitVec 64) := do
  let r ← (( do readReg _MPAM1_EL1 ) : SailM MPAM1_EL1_Type )
  let w__0 ← (( do (HaveEL EL3) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      let w__1 ← (( do (MPAM3_EL3_read ()) ) : SailM (BitVec 64) )
      let r := ((BitVec.update r 63 (Bit (BitVec.slice w__1 63 1))) : (BitVec 64))
      (pure (r)))
  else
    (do
      let w__2 ← (( do readReg MPAM2_EL2 ) : SailM (BitVec 64) )
      let r := ((BitVec.update r 63 (Bit (BitVec.slice w__2 63 1))) : (BitVec 64))
      (pure (r)))


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
  ArmFull.assert ((0 ≤b virt) && (virt <b 64)) "sail-inputs/03-v8_base.sail:11619.48-11619.49"
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
  ArmFull.assert ((Sail.BitVec.length operand) == 32) "sail-inputs/03-v8_base.sail:13171.19-13171.20"
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


end ArmFull.Functions
