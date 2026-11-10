import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0011
import ArmFull.Fn.M0016
import ArmFull.Fn.M0021
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0041
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0062
import ArmFull.Fn.M0097
import ArmFull.Fn.M0144
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0149
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0167
import ArmFull.Fn.M0171
import ArmFull.Fn.M0172
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0184
import ArmFull.Fn.M0186
import ArmFull.Fn.M0250
import ArmFull.Fn.M0252
import ArmFull.Fn.M0253
import ArmFull.Fn.M0254

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

def CheckLDST64BEnabled (_ : Unit) : SailM Unit := do
  let trap : Bool := false
  let iss : (BitVec 25) := (Sail.BitVec.zeroExtend 0b10#2 25)
  let target_el ← (( do (undefined_bitvector_at (← occLabel 2405) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (target_el, trap) ← (( do
    if ((w__0.EL == EL0) : Bool)
    then
      (do
        let w__1 ← (( do (IsInHost ()) ) : SailM Bool )
        if ((! w__1) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let trap := (((_get_SCTLR_EL1_Type_EnALS w__2) == 0#1) : Bool)
            let w__5 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TGE w__4) == 1#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let w__6 : (BitVec 2) :=
              if (w__5 : Bool)
              then EL2
              else EL1
            let target_el := (w__6 : (BitVec 2))
            (pure ((target_el, trap))))
        else
          (do
            let w__7 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let trap := (((_get_SCTLR_EL2_Type_EnALS w__7) == 0#1) : Bool)
            let target_el : (BitVec 2) := EL2
            (pure ((target_el, trap)))))
    else
      (let target_el : (BitVec 2) := EL1
      (pure ((target_el, trap)))) ) : SailM ((BitVec 2) × Bool) )
  let w__15 ← (( do
    if ((← do
         if (((! trap) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__10.EL == EL0) : Bool)))) : Bool)
             then
               (do
                 let w__11 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__11) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__13.EL == EL1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let (target_el, trap) ← (( do
    if (w__15 : Bool)
    then
      (do
        let w__18 ← (( do
          if ((← do
               let w__16 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
               (pure (((! w__16) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__17 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCRX_EL2_Type_EnALS w__17) == 0#1) : Bool)))) ) : SailM Bool )
        let trap := (w__18 : Bool)
        let target_el : (BitVec 2) := EL2
        (pure ((target_el, trap))))
    else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
  let target_el := target_el
  if (trap : Bool)
  then
    (do
      (LDST64BTrap target_el iss))
  else (pure (()))


def CheckST64BVEnabled (_ : Unit) : SailM Unit := do
  let trap : Bool := false
  let iss : (BitVec 25) := (Zeros (n := 25))
  let target_el ← (( do (undefined_bitvector_at (← occLabel 2406) 2) ) : SailM (BitVec 2) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (target_el, trap) ← (( do
    if ((w__0.EL == EL0) : Bool)
    then
      (do
        let w__1 ← (( do (IsInHost ()) ) : SailM Bool )
        if ((! w__1) : Bool)
        then
          (do
            let w__2 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let trap := (((_get_SCTLR_EL1_Type_EnASR w__2) == 0#1) : Bool)
            let w__5 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__4 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TGE w__4) == 1#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let w__6 : (BitVec 2) :=
              if (w__5 : Bool)
              then EL2
              else EL1
            let target_el := (w__6 : (BitVec 2))
            (pure ((target_el, trap))))
        else
          (do
            let w__7 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let trap := (((_get_SCTLR_EL2_Type_EnASR w__7) == 0#1) : Bool)
            let target_el : (BitVec 2) := EL2
            (pure ((target_el, trap)))))
    else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
  let w__15 ← (( do
    if ((← do
         if (((! trap) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__10 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__10.EL == EL0) : Bool)))) : Bool)
             then
               (do
                 let w__11 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__11) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__13.EL == EL1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let (target_el, trap) ← (( do
    if (w__15 : Bool)
    then
      (do
        let w__18 ← (( do
          if ((← do
               let w__16 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
               (pure (((! w__16) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__17 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCRX_EL2_Type_EnASR w__17) == 0#1) : Bool)))) ) : SailM Bool )
        let trap := (w__18 : Bool)
        let target_el : (BitVec 2) := EL2
        (pure ((target_el, trap))))
    else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
  let target_el := target_el
  if (trap : Bool)
  then
    (do
      (LDST64BTrap target_el iss))
  else (pure (()))


def CheckST64BV0Enabled (_ : Unit) : SailM Unit := do
  let trap : Bool := false
  let iss : (BitVec 25) := (Sail.BitVec.zeroExtend 1#1 25)
  let target_el ← (( do (undefined_bitvector_at (← occLabel 2407) 2) ) : SailM (BitVec 2) )
  let w__5 ← (( do
    if ((← do
         if ((← do
              (pure ((← do
                    let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
                    (pure (((w__0.EL != EL3) : Bool)))) && ((HaveEL EL3) : Bool)))) : Bool)
         then
           (do
             let w__2 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
             (pure ((((_get_SCR_EL3_Type_EnAS0 w__2) == 0#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (EL3SDDUndefPriority ()))
    else (pure false) ) : SailM Bool )
  if (w__5 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
  let (target_el, trap) ← (( do
    if ((w__6.EL == EL0) : Bool)
    then
      (do
        let w__7 ← (( do (IsInHost ()) ) : SailM Bool )
        if ((! w__7) : Bool)
        then
          (do
            let w__8 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            let trap := (((_get_SCTLR_EL1_Type_EnAS0 w__8) == 0#1) : Bool)
            let w__11 ← (( do
              if ((← do
                   (EL2Enabled ())) : Bool)
              then
                (do
                  let w__10 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_HCR_EL2_Type_TGE w__10) == 1#1) : Bool))))
              else (pure false) ) : SailM Bool )
            let w__12 : (BitVec 2) :=
              if (w__11 : Bool)
              then EL2
              else EL1
            let target_el := (w__12 : (BitVec 2))
            (pure ((target_el, trap))))
        else
          (do
            let w__13 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
            let trap := (((_get_SCTLR_EL2_Type_EnAS0 w__13) == 0#1) : Bool)
            let target_el : (BitVec 2) := EL2
            (pure ((target_el, trap)))))
    else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
  let w__21 ← (( do
    if ((← do
         if (((! trap) : Bool) : Bool)
         then
           (do
             (EL2Enabled ()))
         else (pure false)) : Bool)
    then
      (do
        if ((← do
             if ((← do
                  let w__16 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__16.EL == EL0) : Bool)))) : Bool)
             then
               (do
                 let w__17 ← (( do (IsInHost ()) ) : SailM Bool )
                 (pure (((! w__17) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
            (pure (((w__19.EL == EL1) : Bool)))))
    else (pure false) ) : SailM Bool )
  let (target_el, trap) ← (( do
    if (w__21 : Bool)
    then
      (do
        let w__24 ← (( do
          if ((← do
               let w__22 ← (( do (IsHCRXEL2Enabled ()) ) : SailM Bool )
               (pure (((! w__22) : Bool)))) : Bool)
          then (pure true)
          else
            (do
              let w__23 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
              (pure ((((_get_HCRX_EL2_Type_EnAS0 w__23) == 0#1) : Bool)))) ) : SailM Bool )
        let trap := (w__24 : Bool)
        let target_el : (BitVec 2) := EL2
        (pure ((target_el, trap))))
    else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
  let w__26 ← (( do
    if (((! trap) : Bool) : Bool)
    then
      (do
        let w__25 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__25.EL != EL3) : Bool))))
    else (pure false) ) : SailM Bool )
  let (target_el, trap) ← (( do
    if (w__26 : Bool)
    then
      (do
        let w__28 ← (( do
          if (((HaveEL EL3) : Bool) : Bool)
          then
            (do
              let w__27 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
              (pure ((((_get_SCR_EL3_Type_EnAS0 w__27) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        let trap := (w__28 : Bool)
        let target_el : (BitVec 2) := EL3
        (pure ((target_el, trap))))
    else (pure ((target_el, trap))) ) : SailM ((BitVec 2) × Bool) )
  if (trap : Bool)
  then
    (do
      let w__30 ← (( do
        if (((target_el == EL3) : Bool) : Bool)
        then
          (do
            (EL3SDDUndef ()))
        else (pure false) ) : SailM Bool )
      if (w__30 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          (LDST64BTrap target_el iss)))
  else (pure (()))


def AArch64_CheckFPAdvSIMDTrap (_ : Unit) : SailM Unit := do
  let w__3 ← (( do
    if ((← do
         if (((HaveEL EL3) : Bool) : Bool)
         then
           (do
             let w__0 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
             (pure ((((_get_CPTR_EL3_Type_TFP w__0) == 1#1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        (EL3SDDUndefPriority ()))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let w__10 ← (( do
    if ((← do
         if ((← do
              let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__4.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             if ((← do
                  let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
                  (pure (((w__5.EL == EL1) : Bool)))) : Bool)
             then (pure true)
             else
               (do
                 let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__6.EL == EL2) : Bool)))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__10 : Bool)
  then
    (do
      let w__13 ← (( do
        if ((← do
             (HaveVirtHostExt ())) : Bool)
        then
          (do
            let w__12 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_E2H w__12) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__13 : Bool)
      then
        (do
          let disabled ← (( do (undefined_bool_at (← occLabel 2416) ()) ) : SailM Bool )
          let w__14 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          let b__0 := (_get_CPTR_EL2_Type_FPEN w__14)
          let disabled ← (( do
            if (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 0 0)) == (0#1 : (BitVec 1))) : Bool)
            then (pure (true))
            else
              (do
                match b__0 with
                | 0b01 =>
                  (do
                    if ((← do
                         let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
                         (pure (((w__15.EL == EL0) : Bool)))) : Bool)
                    then
                      (do
                        let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__16) == 1#1) : Bool))))
                    else (pure false))
                | _ => (pure (false))) ) : SailM Bool )
          let disabled := disabled
          if (disabled : Bool)
          then
            (do
              (AArch64_AdvSIMDFPAccessTrap EL2))
          else (pure (())))
      else
        (do
          let w__18 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
          if (((_get_CPTR_EL2_Type_TFP w__18) == 1#1) : Bool)
          then
            (do
              (AArch64_AdvSIMDFPAccessTrap EL2))
          else (pure (()))))
  else (pure (()))
  if ((HaveEL EL3) : Bool)
  then
    (do
      let w__19 ← (( do readReg CPTR_EL3 ) : SailM (BitVec 64) )
      if (((_get_CPTR_EL3_Type_TFP w__19) == 1#1) : Bool)
      then
        (do
          let w__20 ← (( do (EL3SDDUndef ()) ) : SailM Bool )
          if (w__20 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              (AArch64_AdvSIMDFPAccessTrap EL3)))
      else (pure (())))
  else (pure (()))


/-- Type quantifiers: CRm : Int, CRn : Int, nreg : Int -/
def AArch64_CheckCP15InstrCoarseTraps (CRn : Int) (nreg : Int) (CRm : Int) : SailM Unit := do
  let major ← (( do (undefined_int_at (← occLabel 2418) ()) ) : SailM Int )
  let trapped_encoding : Bool :=
    ((((CRn == 9) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || (CRm == 8)))))))) || ((CRn == 10) && ((CRm == 0) || ((CRm == 1) || ((CRm == 4) || (CRm == 8)))))) || ((CRn == 11) && ((CRm == 0) || ((CRm == 1) || ((CRm == 2) || ((CRm == 3) || ((CRm == 4) || ((CRm == 5) || ((CRm == 6) || ((CRm == 7) || ((CRm == 8) || (CRm == 15))))))))))))
  let w__9 ← (( do
    (pure ((← do
          if ((← do
               if ((← do
                    if ((← do
                         if ((← do
                              (HaveFeatTIDCP1 ())) : Bool)
                         then
                           (do
                             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
                             (pure (((w__1.EL == EL0) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__3 ← (( do (IsInHost ()) ) : SailM Bool )
                        (pure (((! w__3) : Bool))))
                    else (pure false)) : Bool)
               then
                 (do
                   let w__5 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                   (pure (((! w__5) : Bool))))
               else (pure false)) : Bool)
          then
            (do
              let w__7 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
              (pure ((((_get_SCTLR_EL1_Type_TIDCP w__7) == 1#1) : Bool))))
          else (pure false)) && trapped_encoding)) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let w__12 ← (( do
        if ((← do
             (EL2Enabled ())) : Bool)
        then
          (do
            let w__11 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
            (pure ((((_get_HCR_EL2_Type_TGE w__11) == 1#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__12 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4)))
      else
        (do
          (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x3#4))))
  else (pure (()))
  let w__17 ← (( do
    if ((← do
         if ((← do
              let w__13 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__13.EL == EL0) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__14 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__14.EL == EL1) : Bool))))) : Bool)
    then
      (do
        (EL2Enabled ()))
    else (pure false) ) : SailM Bool )
  if (w__17 : Bool)
  then
    (do
      let w__25 ← (( do
        (pure ((← do
              if ((← do
                   if ((← do
                        if ((← do
                             (HaveFeatTIDCP1 ())) : Bool)
                        then
                          (do
                            let w__19 ← (( do readReg PSTATE ) : SailM ProcState )
                            (pure (((w__19.EL == EL0) : Bool))))
                        else (pure false)) : Bool)
                   then
                     (do
                       (IsInHost ()))
                   else (pure false)) : Bool)
              then
                (do
                  let w__23 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
                  (pure ((((_get_SCTLR_EL2_Type_TIDCP w__23) == 1#1) : Bool))))
              else (pure false)) && trapped_encoding)) ) : SailM Bool )
      if (w__25 : Bool)
      then
        (do
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4)))
      else (pure (()))
      let major : Int :=
        if ((nreg == 1) : Bool)
        then CRn
        else CRm
      ArmFull.assert ((0 ≤b major) && (major <b 64)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:34133.54-34133.55"
      let w__33 ← (( do
        if ((← do
             if ((← do
                  (pure ((← do
                        let w__26 ← (( do (IsInHost ()) ) : SailM Bool )
                        (pure (((! w__26) : Bool)))) && ((! ((major == 4) || (major == 14))) : Bool)))) : Bool)
             then
               (do
                 let w__28 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
                 (pure ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access w__28
                         (Sail.Int.toNatChecked (major)))])) == 1#1) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (pure ((← do
                (pure ((← do
                      let w__30 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure ((((_get_HCR_EL2_Type_TIDCP w__30) == 1#1) : Bool)))) && ((nreg == 1) : Bool)))) && trapped_encoding))
        ) : SailM Bool )
      if (w__33 : Bool)
      then
        (do
          let w__36 ← (( do
            if ((← do
                 let w__34 ← (( do readReg PSTATE ) : SailM ProcState )
                 (pure (((w__34.EL == EL0) : Bool)))) : Bool)
            then
              (do
                (__IMPDEF_boolean "UNDEF unallocated CP15 access at EL0"))
            else (pure false) ) : SailM Bool )
          if (w__36 : Bool)
          then sailThrow ((Error_Undefined ()))
          else (pure (()))
          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x3#4)))
      else (pure (())))
  else (pure (()))


def AArch64_CheckPCAlignment (_ : Unit) : SailM Unit := do
  let pc ← (( do (ThisInstrAddr 64) ) : SailM (BitVec 64) )
  if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb pc 1 0)) != 0b00#2) : Bool)
  then
    (do
      (AArch64_PCAlignmentFault ()))
  else (pure (()))


/-- Type quantifiers: k_aligned : Bool -/
def AArch32_S2Translate (fault_in : FaultRecord) (ipa : AddressDescriptor) (s1level : (Option Int)) (aligned : Bool) (accdesc : AccessDescriptor) : SailM (FaultRecord × AddressDescriptor) := do
  let s1aarch64 ← (( do (undefined_bool_at (← occLabel 2551) ()) ) : SailM Bool )
  let fault : FaultRecord := fault_in
  ArmFull.assert (IsZero (Sail.BitVec.extractLsb ipa.paddress.address 55 40)) "/home/doug/boss-scratch/sail-lean-fork/integ/model/v8_base.sail:37992.49-37992.50"
  let w__0 ← (( do (ELStateUsingAArch32 EL2 (BEq.beq accdesc.ss SS_Secure)) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      let s1aarch64 : Bool := false
      (AArch64_S2Translate fault ipa s1aarch64 none aligned accdesc))
  else
    (do
      let fault : FaultRecord := { fault with statuscode := Fault_None }
      let fault : FaultRecord := { fault with secondstage := true }
      let fault : FaultRecord :=
        { fault with s2fs1walk := (BEq.beq accdesc.acctype AccessType_TTW) }
      let fault : FaultRecord := { fault with ipaddress := ipa.paddress }
      let walkparams ← (( do (AArch32_GetS2TTWParams ()) ) : SailM S2TTWParams )
      if ((walkparams.vm == 0#1) : Bool)
      then (pure ((fault, ipa)))
      else
        (do
          if ((AArch32_IPAIsOutOfRange walkparams (Sail.BitVec.extractLsb ipa.paddress.address 39 0)) : Bool)
          then
            (do
              let fault : FaultRecord := { fault with statuscode := Fault_Translation }
              let fault : FaultRecord := { fault with level := 1 }
              let w__2 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
              (pure ((fault, w__2))))
          else
            (do
              let walkstate ← (( do (undefined_TTWState (← occLabel 2552) ()) ) : SailM TTWState
                )
              let w__3 ← (( do (AArch32_S2Walk fault walkparams s1level accdesc ipa) ) : SailM
                (FaultRecord × TTWState) )
              let (tup__0, tup__1) := (w__3 : (FaultRecord × TTWState))
              let fault : FaultRecord := tup__0
              let walkstate : TTWState := tup__1
              if ((bne fault.statuscode Fault_None) : Bool)
              then
                (do
                  let w__4 ← (( do (__UNKNOWN_AddressDescriptor ()) ) : SailM AddressDescriptor )
                  (pure ((fault, w__4))))
              else
                (do
                  let fault ← (( do
                    if ((AArch32_S2HasAlignmentFault accdesc aligned walkstate.memattrs) : Bool)
                    then
                      (let fault : FaultRecord := { fault with statuscode := Fault_Alignment }
                      (pure (fault)))
                    else
                      (do
                        let w__5 ← (( do
                          (AArch32_S2HasPermissionsFault walkparams walkstate.permissions
                            walkstate.memattrs.memtype accdesc) ) : SailM Bool )
                        let fault : FaultRecord :=
                          if (w__5 : Bool)
                          then { fault with statuscode := Fault_Permission }
                          else fault
                        (pure (fault))) ) : SailM FaultRecord )
                  let s2_memattrs ← (( do (undefined_MemoryAttributes (← occLabel 2553) ()) ) :
                    SailM MemoryAttributes )
                  let w__12 ← (( do
                    if ((← do
                         if ((((BEq.beq accdesc.acctype AccessType_TTW) && (BEq.beq
                                walkstate.memattrs.memtype MemType_Device)) : Bool) : Bool)
                         then (pure true)
                         else
                           (do
                             if (((BEq.beq accdesc.acctype AccessType_IFETCH) : Bool) : Bool)
                             then
                               (do
                                 if (((BEq.beq walkstate.memattrs.memtype MemType_Device) : Bool) : Bool)
                                 then (pure true)
                                 else
                                   (do
                                     let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
                                     (pure ((((_get_HCR2_Type_ID w__6) == 1#1) : Bool)))))
                             else (pure false))) : Bool)
                    then (pure true)
                    else
                      (do
                        if ((((bne accdesc.acctype AccessType_IFETCH) && (BEq.beq
                               walkstate.memattrs.memtype MemType_Normal)) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_HCR2_Type_CD w__10) == 1#1) : Bool))))
                        else (pure false)) ) : SailM Bool )
                  let s2_memattrs ← (( do
                    if (w__12 : Bool)
                    then
                      (do
                        let w__13 ← (( do (NormalNCMemAttr ()) ) : SailM MemoryAttributes )
                        let s2_memattrs := (w__13 : MemoryAttributes)
                        let s2_memattrs : MemoryAttributes :=
                          { s2_memattrs with xs := walkstate.memattrs.xs }
                        (pure (s2_memattrs)))
                    else
                      (let s2_memattrs : MemoryAttributes := walkstate.memattrs
                      (pure (s2_memattrs))) ) : SailM MemoryAttributes )
                  let s2aarch64 : Bool := false
                  let memattrs ← (( do (S2CombineS1MemAttrs ipa.memattrs s2_memattrs s2aarch64) )
                    : SailM MemoryAttributes )
                  let ipa_64 : (BitVec 64) :=
                    (Sail.BitVec.zeroExtend (Sail.BitVec.extractLsb ipa.paddress.address 39 0) 64)
                  let oa ← (( do (StageOA ipa_64 walkparams.d128 walkparams.tgx walkstate) ) :
                    SailM FullAddress )
                  let pa ← (( do (CreateAddressDescriptor ipa.vaddress oa memattrs) ) : SailM
                    AddressDescriptor )
                  (pure ((fault, pa)))))))


end ArmFull.Functions
