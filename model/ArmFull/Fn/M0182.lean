import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0015
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0035
import ArmFull.Fn.M0036
import ArmFull.Fn.M0042
import ArmFull.Fn.M0046
import ArmFull.Fn.M0049
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0108
import ArmFull.Fn.M0117
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0152
import ArmFull.Fn.M0154
import ArmFull.Fn.M0166
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0179
import ArmFull.Fn.M0180
import ArmFull.Fn.M0181

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

def ELFromM32 (mode : (BitVec 5)) : SailM (Bool × (BitVec 2)) := do
  let el ← (( do (undefined_bitvector_at (← occLabel 630) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do (BadMode mode) ) : SailM Bool )
  let valid_name : Bool := (! w__0)
  let w__1 ← (( do (EffectiveSCR_EL3_NSE ()) ) : SailM (BitVec 1) )
  let w__2 ← (( do (EffectiveSCR_EL3_NS ()) ) : SailM (BitVec 1) )
  let effective_nse_ns : (BitVec 2) := (w__1 +++ w__2)
  let questionMark := mode
  let (el, valid_name) ← (( do
    if ((questionMark == M32_Monitor) : Bool)
    then
      (let el : (BitVec 2) := EL3
      (pure ((el, valid_name))))
    else
      (do
        if ((questionMark == M32_Hyp) : Bool)
        then
          (let el : (BitVec 2) := EL2
          (pure ((el, valid_name))))
        else
          (do
            if ((questionMark == M32_FIQ) : Bool)
            then
              (do
                let w__6 ← (( do
                  if ((← do
                       if (((HaveEL EL3) : Bool) : Bool)
                       then
                         (do
                           let w__3 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                           (pure (((! w__3) : Bool))))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
                      (pure ((((_get_SCR_Type_NS w__5) == 0#1) : Bool))))
                  else (pure false) ) : SailM Bool )
                let w__7 : (BitVec 2) :=
                  if (w__6 : Bool)
                  then EL3
                  else EL1
                let el := (w__7 : (BitVec 2))
                (pure ((el, valid_name))))
            else
              (do
                if ((questionMark == M32_IRQ) : Bool)
                then
                  (do
                    let w__11 ← (( do
                      if ((← do
                           if (((HaveEL EL3) : Bool) : Bool)
                           then
                             (do
                               let w__8 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                               (pure (((! w__8) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__10 ← (( do readReg SCR ) : SailM (BitVec 32) )
                          (pure ((((_get_SCR_Type_NS w__10) == 0#1) : Bool))))
                      else (pure false) ) : SailM Bool )
                    let w__12 : (BitVec 2) :=
                      if (w__11 : Bool)
                      then EL3
                      else EL1
                    let el := (w__12 : (BitVec 2))
                    (pure ((el, valid_name))))
                else
                  (do
                    if ((questionMark == M32_Svc) : Bool)
                    then
                      (do
                        let w__16 ← (( do
                          if ((← do
                               if (((HaveEL EL3) : Bool) : Bool)
                               then
                                 (do
                                   let w__13 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                   (pure (((! w__13) : Bool))))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__15 ← (( do readReg SCR ) : SailM (BitVec 32) )
                              (pure ((((_get_SCR_Type_NS w__15) == 0#1) : Bool))))
                          else (pure false) ) : SailM Bool )
                        let w__17 : (BitVec 2) :=
                          if (w__16 : Bool)
                          then EL3
                          else EL1
                        let el := (w__17 : (BitVec 2))
                        (pure ((el, valid_name))))
                    else
                      (do
                        if ((questionMark == M32_Abort) : Bool)
                        then
                          (do
                            let w__21 ← (( do
                              if ((← do
                                   if (((HaveEL EL3) : Bool) : Bool)
                                   then
                                     (do
                                       let w__18 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                       (pure (((! w__18) : Bool))))
                                   else (pure false)) : Bool)
                              then
                                (do
                                  let w__20 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                  (pure ((((_get_SCR_Type_NS w__20) == 0#1) : Bool))))
                              else (pure false) ) : SailM Bool )
                            let w__22 : (BitVec 2) :=
                              if (w__21 : Bool)
                              then EL3
                              else EL1
                            let el := (w__22 : (BitVec 2))
                            (pure ((el, valid_name))))
                        else
                          (do
                            if ((questionMark == M32_Undef) : Bool)
                            then
                              (do
                                let w__26 ← (( do
                                  if ((← do
                                       if (((HaveEL EL3) : Bool) : Bool)
                                       then
                                         (do
                                           let w__23 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                           (pure (((! w__23) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__25 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                      (pure ((((_get_SCR_Type_NS w__25) == 0#1) : Bool))))
                                  else (pure false) ) : SailM Bool )
                                let w__27 : (BitVec 2) :=
                                  if (w__26 : Bool)
                                  then EL3
                                  else EL1
                                let el := (w__27 : (BitVec 2))
                                (pure ((el, valid_name))))
                            else
                              (do
                                if ((questionMark == M32_System) : Bool)
                                then
                                  (do
                                    let w__31 ← (( do
                                      if ((← do
                                           if (((HaveEL EL3) : Bool) : Bool)
                                           then
                                             (do
                                               let w__28 ← (( do (HaveAArch64 ()) ) : SailM Bool )
                                               (pure (((! w__28) : Bool))))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          let w__30 ← (( do readReg SCR ) : SailM (BitVec 32) )
                                          (pure ((((_get_SCR_Type_NS w__30) == 0#1) : Bool))))
                                      else (pure false) ) : SailM Bool )
                                    let w__32 : (BitVec 2) :=
                                      if (w__31 : Bool)
                                      then EL3
                                      else EL1
                                    let el := (w__32 : (BitVec 2))
                                    (pure ((el, valid_name))))
                                else
                                  (let (el, valid_name) : ((BitVec 2) × Bool) :=
                                    if ((questionMark == M32_User) : Bool)
                                    then
                                      (let el : (BitVec 2) := EL0
                                      (el, valid_name))
                                    else
                                      (let valid_name : Bool := false
                                      (el, valid_name))
                                  (pure ((el, valid_name))))))))))) ) : SailM ((BitVec 2) × Bool) )
  let w__34 ← (( do
    if ((((valid_name && (el == EL2)) && (HaveEL EL3)) : Bool) : Bool)
    then
      (do
        let w__33 ← (( do (SCR_GEN_read ()) ) : SailM (BitVec 64) )
        (pure ((((_get_SCRType_NS w__33) == 0#1) : Bool))))
    else (pure false) ) : SailM Bool )
  let valid_name ← (( do
    if (w__34 : Bool)
    then (pure (false))
    else
      (do
        let w__37 ← (( do
          (pure ((← do
                if ((valid_name : Bool) : Bool)
                then
                  (do
                    (HaveRME ()))
                else (pure false)) && ((effective_nse_ns == 0b10#2) : Bool))) ) : SailM Bool )
        let valid_name : Bool :=
          if (w__37 : Bool)
          then false
          else valid_name
        (pure (valid_name))) ) : SailM Bool )
  let el ← (( do
    if ((! valid_name) : Bool)
    then
      (do
        (__UNKNOWN_bits 2))
    else (pure (el)) ) : SailM (BitVec 2) )
  let el := el
  (pure ((valid_name, el)))


def AArch64_GenerateDebugExceptionsFrom (from_el : (BitVec 2)) (from_state : SecurityState) (mask : (BitVec 1)) : SailM Bool := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_OSLSR_EL1_Type_OSLK w__0) == 1#1) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             (DoubleLockStatus ()))) : Bool)
    then (pure true)
    else
      (do
        (Halted ())) ) : SailM Bool )
  if (w__4 : Bool)
  then (pure (false))
  else
    (do
      let route_to_el2 ← (( do
        if ((← do
             if (((HaveEL EL2) : Bool) : Bool)
             then
               (do
                 if (((bne from_state SS_Secure) : Bool) : Bool)
                 then (pure true)
                 else
                   (do
                     (IsSecureEL2Enabled ())))
             else (pure false)) : Bool)
        then
          (do
            if ((← do
                 let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((_get_HCR_EL2_Type_TGE w__8) == 1#1) : Bool)))) : Bool)
            then (pure true)
            else
              (do
                let w__9 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_MDCR_EL2_Type_TDE w__9) == 1#1) : Bool)))))
        else (pure false) ) : SailM Bool )
      let target : (BitVec 2) :=
        if (route_to_el2 : Bool)
        then EL2
        else EL1
      let enabled ← (( do (undefined_bool_at (← occLabel 647) ()) ) : SailM Bool )
      let enabled ← (( do
        if (((HaveEL EL3) && (BEq.beq from_state SS_Secure)) : Bool)
        then
          (do
            let w__11 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
            let enabled := (((_get_MDCR_EL3_Type_SDD w__11) == 0#1) : Bool)
            let w__13 ← (( do
              if (((from_el == EL0) : Bool) : Bool)
              then
                (do
                  (ELUsingAArch32 EL1))
              else (pure false) ) : SailM Bool )
            if (w__13 : Bool)
            then
              (do
                if ((enabled : Bool) : Bool)
                then (pure true)
                else
                  (do
                    let w__14 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
                    (pure ((((_get_SDER32_EL3_Type_SUIDEN w__14) == 1#1) : Bool)))))
            else (pure (enabled)))
        else (pure (true)) ) : SailM Bool )
      if ((from_el == target) : Bool)
      then
        (do
          (pure ((← do
                if ((enabled : Bool) : Bool)
                then
                  (do
                    let w__16 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
                    (pure ((((_get_MDSCR_EL1_Type_KDE w__16) == 1#1) : Bool))))
                else (pure false)) && ((mask == 0#1) : Bool))))
      else
        (let enabled : Bool :=
          (enabled && (((BitVec.toNat target) >b (BitVec.toNat from_el)) : Bool))
        (pure (enabled))))


def GPCRegistersConsistent (_ : Unit) : SailM Bool := do
  let w__3 ← (( do
    if ((← do
         let w__0 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
         (pure ((((_get_GPCCR_EL3_Type_PPS w__0) == 0b111#3) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (DecodePPS ()) ) : SailM Int )
        let w__2 ← (( do (AArch64_PAMax ()) ) : SailM Int )
        (pure (((w__1 >b w__2) : Bool)))) ) : SailM Bool )
  if (w__3 : Bool)
  then (pure (false))
  else
    (do
      let w__4 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
      if (((_get_GPCCR_EL3_Type_PGS w__4) == 0b11#2) : Bool)
      then (pure (false))
      else
        (do
          let w__5 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
          if (((_get_GPCCR_EL3_Type_SH w__5) == 0b01#2) : Bool)
          then (pure (false))
          else
            (do
              let w__9 ← (( do
                if ((← do
                     let w__6 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
                     let w__7 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
                     (pure (((((_get_GPCCR_EL3_Type_ORGN w__6) +++ (_get_GPCCR_EL3_Type_IRGN w__7)) == 0b0000#4) : Bool)))) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg GPCCR_EL3 ) : SailM (BitVec 64) )
                    (pure ((((_get_GPCCR_EL3_Type_SH w__8) != 0b10#2) : Bool))))
                else (pure false) ) : SailM Bool )
              let w__10 : Bool :=
                if (w__9 : Bool)
                then false
                else true
              (pure (w__10)))))


/-- Type quantifiers: k_ex10456194_ : Bool -/
def C27bConstrainControl (isbreakpnt : Bool) : SailM (Constraint × (BitVec 6)) := do
  let disabled ← (( do (undefined_bool_at (← occLabel 1378) ()) ) : SailM Bool )
  if (disabled : Bool)
  then
    (do
      let w__0 ← (( do (undefined_bitvector_at (← occLabel 1379) 6) ) : SailM (BitVec 6) )
      (pure ((Constraint_DISABLED, (w__0 : (BitVec 6))))))
  else
    (do
      let allowed : (BitVec 256) := (Zeros (n := 256))
      let allowed ← (( do
        let loop_i_lower : Nat := 0
        let loop_i_upper : Nat := 63
        (do
          let mut loop_vars := allowed
          for i in [loop_i_lower:loop_i_upper:1]i do
            let allowed := loop_vars
            loop_vars ← do
              let raw : (BitVec 6) := (integer_subrange i 5 0)
              let w__1 ← (( do
                (C27bReservedControl (Sail.BitVec.extractLsb raw 4 3)
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access raw 2)]))
                  (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access raw 5)]))
                  (Sail.BitVec.extractLsb raw 1 0) isbreakpnt) ) : SailM Bool )
              let allowed : (BitVec 256) :=
                if ((! w__1) : Bool)
                then (BitVec.update allowed (Sail.Int.toNatChecked (i)) 1#1)
                else allowed
              (pure (allowed))
          (pure loop_vars)) ) : SailM (BitVec 256) )
      let selected ← (( do (C27bSelect allowed) ) : SailM Int )
      (pure ((Constraint_UNKNOWN, (integer_subrange selected 5 0)))))


def ContextMatchingBreakpointRange (_ : Unit) : SailM (Int × Int) := do
  let b ← (( do (NumBreakpointsImplemented ()) ) : SailM Int )
  let c ← (( do (NumContextAwareBreakpointsImplemented b) ) : SailM Int )
  (pure (if ((b ≤b 16) : Bool)
    then ((b -i c), (b -i 1))
    else
      (if ((c ≤b 16) : Bool)
      then ((16 -i c), 15)
      else (0, (c -i 1)))))


/-- Type quantifiers: k_N : Nat, k_N ≥ 0 -/
def AArch64_BlocknTFaults (d128 : (BitVec 1)) (descriptor : (BitVec k_N)) : SailM Bool := do
  let w__0 ← (( do (HaveBlockBBM ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then (pure (false))
  else
    (do
      let nT ← (( do
        if ((d128 == 1#1) : Bool)
        then
          (do
            ArmFull.assert (6 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:24853.33-24853.34"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 6)])))))
        else
          (do
            ArmFull.assert (16 <b (Sail.BitVec.length descriptor)) "sail-arm/v8_base.sail:24856.34-24856.35"
            (pure ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access descriptor 16)]))))) ) : SailM
        (BitVec 1) )
      let bbm_level ← (( do (AArch64_BlockBBMSupportLevel ()) ) : SailM Int )
      let nT_faults ← (( do
        (__IMPDEF_boolean "BBM level 1 or 2 support nT bit causes Translation Fault") ) : SailM Bool
        )
      (pure (((((bbm_level == 1) || (bbm_level == 2)) && (nT == 1#1)) && nT_faults))))


/-- Type quantifiers: level : Int -/
def AArch64_BlockDescSupported (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) (level : Int) : SailM Bool := SailME.run do
  let w__4 ← (( do
    match tgx with
    | .TGx_4KB =>
      (pure (((((level == 0) && ((ds == 1#1) || (d128 == 1#1))) || (level == 1)) || (level == 2))))
    | .TGx_16KB => (pure ((((level == 1) && ((ds == 1#1) || (d128 == 1#1))) || (level == 2))))
    | .TGx_64KB =>
      (do
        (pure ((← do
              if (((level == 1) : Bool) : Bool)
              then
                (do
                  if (((d128 == 1#1) : Bool) : Bool)
                  then (pure true)
                  else
                    (do
                      let w__0 ← (( do (AArch64_PAMax ()) ) : SailME Bool Int )
                      (pure (((w__0 ≥b 52) : Bool)))))
              else (pure false)) || ((level == 2) : Bool)))) ) : SailME Bool Bool )
  SailME.throw (w__4 : Bool)
  (pure (false))


def AArch64_PhysicalAddressSize (d128 : (BitVec 1)) (encoded_ps : (BitVec 3)) (tgx : TGx) : SailM Int := do
  let ps : Int := 32
  let max_ps ← (( do (undefined_int_at (← occLabel 1478) ()) ) : SailM Int )
  let ps : Int :=
    match encoded_ps with
    | 0b000 => 32
    | 0b001 => 36
    | 0b010 => 40
    | 0b011 => 42
    | 0b100 => 44
    | 0b101 => 48
    | 0b110 => 52
    | _ => 56
  let ps : Int := ps
  let w__1 ← (( do
    (pure ((← do
          let w__0 ← (( do (Have56BitPAExt ()) ) : SailM Bool )
          (pure (((! w__0) : Bool)))) || ((d128 == 0#1) : Bool))) ) : SailM Bool )
  let max_ps ← (( do
    if (w__1 : Bool)
    then
      (do
        let w__3 ← (( do
          if (((bne tgx TGx_64KB) : Bool) : Bool)
          then
            (do
              let w__2 ← (( do (Have52BitIPAAndPASpaceExt ()) ) : SailM Bool )
              (pure (((! w__2) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__3 : Bool)
        then
          (do
            let w__4 ← (( do (AArch64_PAMax ()) ) : SailM Int )
            let max_ps : Int := ((Min.min 48 w__4) : Int)
            (pure (max_ps)))
        else
          (do
            let w__5 ← (( do (Have52BitPAExt ()) ) : SailM Bool )
            if ((! w__5) : Bool)
            then
              (do
                let w__6 ← (( do (AArch64_PAMax ()) ) : SailM Int )
                let max_ps : Int := ((Min.min 48 w__6) : Int)
                (pure (max_ps)))
            else
              (do
                let w__7 ← (( do (AArch64_PAMax ()) ) : SailM Int )
                let max_ps : Int := ((Min.min 52 w__7) : Int)
                (pure (max_ps)))))
    else
      (do
        (AArch64_PAMax ())) ) : SailM Int )
  let max_ps : Int := max_ps
  (pure ((Min.min ps max_ps)))


def AArch64_S2InvalidSL (walkparams : S2TTWParams) : SailM Bool := do
  match walkparams.tgx with
  | .TGx_4KB =>
    (do
      let b__0 := (walkparams.sl2 +++ walkparams.sl0)
      if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 2 2)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
      then (pure (true))
      else
        (do
          if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b11#2 : (BitVec 2))) : Bool)
          then (pure (true))
          else
            (do
              match b__0 with
              | 0b010 =>
                (do
                  let w__0 ← (( do (AArch64_PAMax ()) ) : SailM Int )
                  (pure ((w__0 <b 44))))
              | 0b011 =>
                (do
                  let w__1 ← (( do (HaveSmallTranslationTableExt ()) ) : SailM Bool )
                  (pure ((! w__1))))
              | _ => (pure (false)))))
  | .TGx_16KB =>
    (do
      match walkparams.sl0 with
      | 0b11 => (pure ((walkparams.ds == 0#1)))
      | 0b10 =>
        (do
          let w__5 ← (( do (AArch64_PAMax ()) ) : SailM Int )
          (pure ((w__5 <b 42))))
      | _ => (pure (false)))
  | .TGx_64KB =>
    (do
      match walkparams.sl0 with
      | 0b11 => (pure (true))
      | 0b10 =>
        (do
          let w__7 ← (( do (AArch64_PAMax ()) ) : SailM Int )
          (pure ((w__7 <b 44))))
      | _ => (pure (false)))


/-- Type quantifiers: k_s1aarch64 : Bool -/
def AArch64_S2MinTxSZ (d128 : (BitVec 1)) (ds : (BitVec 1)) (tgx : TGx) (s1aarch64 : Bool) : SailM Int := do
  let ips ← (( do (AArch64_PAMax ()) ) : SailM Int )
  let ips ← (( do
    if ((d128 == 0#1) : Bool)
    then
      (do
        let w__2 ← (( do
          (pure ((← do
                (pure ((← do
                      (Have52BitPAExt ())) && ((bne tgx TGx_64KB) : Bool)))) && ((ds == 0#1) : Bool)))
          ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            let w__3 ← (( do (AArch64_PAMax ()) ) : SailM Int )
            let ips : Int := ((Min.min 48 w__3) : Int)
            (pure (ips)))
        else
          (do
            let w__4 ← (( do (AArch64_PAMax ()) ) : SailM Int )
            let ips : Int := ((Min.min 52 w__4) : Int)
            (pure (ips))))
    else (pure (ips)) ) : SailM Int )
  let ips : Int := ips
  let min_txsz : Int := (64 -i ips)
  let min_txsz : Int :=
    if ((! s1aarch64) : Bool)
    then (Min.min min_txsz 24)
    else min_txsz
  let min_txsz : Int := min_txsz
  (pure (min_txsz))


def BRB_IALL (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (GetBRBENumRecords ()) ) : SailM Int )
  let loop_i_lower : Nat := 0
  let loop_i_upper : Int := (w__0 -i 1)
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        ArmFull.assert (i <b 64) "sail-arm/v8_base.sail:35655.39-35655.40"
        let w__1 ← (( do readReg Records_SRC ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_SRC (vectorUpdate w__1 (Sail.Int.toNatChecked (i))
          (Mk_BRBSRCType (Zeros (n := 64))))
        let w__2 ← (( do readReg Records_TGT ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_TGT (vectorUpdate w__2 (Sail.Int.toNatChecked (i))
          (Mk_BRBTGTType (Zeros (n := 64))))
        let w__3 ← (( do readReg Records_INF ) : SailM (Vector (BitVec 64) 64) )
        writeReg Records_INF (vectorUpdate w__3 (Sail.Int.toNatChecked (i))
          (Mk_BRBINFType (Zeros (n := 64))))
    (pure loop_vars))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV89 (enabled : Bool) : SailM Unit := do
  writeReg v8Ap9_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV88 enabled))
  else (pure (()))


/-- Type quantifiers: k_enabled : Bool -/
def __ConfigureV93 (enabled : Bool) : SailM Unit := do
  writeReg v9Ap3_IMPLEMENTED enabled
  if (enabled : Bool)
  then
    (do
      (__ConfigureV92 enabled)
      (__ConfigureV88 enabled))
  else (pure (()))


def AArch32_GetNumEventCountersAccessible (_ : Unit) : SailM Int := do
  let n ← (( do (undefined_int_at (← occLabel 500) ()) ) : SailM Int )
  let total_counters ← (( do (GetNumEventCounters ()) ) : SailM Int )
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL1) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL0) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  let n ← (( do
    if (w__4 : Bool)
    then
      (do
        let w__5 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
        let w__8 ← (( do
          if ((! w__5) : Bool)
          then
            (do
              let w__6 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
              (pure ((_get_MDCR_EL2_Type_HPMN w__6))))
          else
            (do
              let w__7 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
              (pure ((_get_HDCR_Type_HPMN w__7)))) ) : SailM (BitVec 5) )
        let n : Int := ((BitVec.toNat w__8) : Int)
        let w__11 ← (( do
          if (((n >b total_counters) : Bool) : Bool)
          then (pure true)
          else
            (do
              (pure ((← do
                    let w__9 ← (( do (HaveFeatHPMN0 ()) ) : SailM Bool )
                    (pure (((! w__9) : Bool)))) && ((n == 0) : Bool)))) ) : SailM Bool )
        if (w__11 : Bool)
        then
          (do
            let (_, __tup_1) ← (( do
              (ConstrainUnpredictableInteger 0 total_counters Unpredictable_PMUEVENTCOUNTER) ) :
              SailM (Constraint × Int) )
            (pure (__tup_1)))
        else (pure (n)))
    else (pure (total_counters)) ) : SailM Int )
  let n : Int := n
  (pure (n))


end ArmFull.Functions
