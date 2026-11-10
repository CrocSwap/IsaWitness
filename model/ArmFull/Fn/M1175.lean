import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0024
import ArmFull.Fn.M0042
import ArmFull.Fn.M0047
import ArmFull.Fn.M0082
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0145
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203
import ArmFull.Fn.M0244
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255
import ArmFull.Fn.M0260
import ArmFull.Fn.M1142

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

def DBGDTRTXint_LDC_da4baa792b999a1f (coproc : (BitVec 4)) (CRd : (BitVec 4)) (address : (BitVec 32)) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg MDSCR_EL1 ) : SailM (BitVec 64) )
  let __MDSCR_EL1_TDCC : (BitVec 1) := (_get_MDSCR_EL1_Type_TDCC w__1)
  let w__2 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
  let __DBGDSCRext_UDCCdis : (BitVec 1) := (_get_DBGDSCRext_Type_UDCCdis w__2)
  let w__3 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  let __MDCR_EL2_TDCC : (BitVec 1) := (_get_MDCR_EL2_Type_TDCC w__3)
  let w__4 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
  let __HDCR_TDCC : (BitVec 1) := (_get_HDCR_Type_TDCC w__4)
  let w__5 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDCC : (BitVec 1) := (_get_MDCR_EL3_Type_TDCC w__5)
  let w__6 ← (( do readReg SDCR ) : SailM (BitVec 32) )
  let __SDCR_TDCC : (BitVec 1) := (_get_SDCR_Type_TDCC w__6)
  let w__7 ← (( do readReg MDCR_EL3 ) : SailM (BitVec 64) )
  let __MDCR_EL3_TDA : (BitVec 1) := (_get_MDCR_EL3_Type_TDA w__7)
  let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__8.M
  let w__9 ← (( do (Halted ()) ) : SailM Bool )
  if (w__9 : Bool)
  then
    (do
      let w__10 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
      (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__10)))
  else
    (do
      if ((__PSTATE_EL == EL0) : Bool)
      then
        (do
          let w__12 ← (( do
            (pure ((← do
                  let w__11 ← (( do (ELUsingAArch32 EL1) ) : SailM Bool )
                  (pure (((! w__11) : Bool)))) && ((__MDSCR_EL1_TDCC == 1#1) : Bool))) ) : SailM
            Bool )
          if (w__12 : Bool)
          then
            (do
              let w__17 ← (( do
                if ((← do
                     if ((← do
                          (EL2Enabled ())) : Bool)
                     then
                       (do
                         let w__14 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                         (pure (((! w__14) : Bool))))
                     else (pure false)) : Bool)
                then
                  (do
                    let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure ((((_get_HCR_EL2_Type_TGE w__16) == 1#1) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__17 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL1 (BitVec.toNat 0x06#8))))
          else
            (do
              let w__19 ← (( do
                (pure ((← do
                      (ELUsingAArch32 EL1)) && ((__DBGDSCRext_UDCCdis == 1#1) : Bool))) ) : SailM
                Bool )
              if (w__19 : Bool)
              then
                (do
                  let w__24 ← (( do
                    if ((← do
                         if ((← do
                              (EL2Enabled ())) : Bool)
                         then
                           (do
                             let w__21 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                             (pure (((! w__21) : Bool))))
                         else (pure false)) : Bool)
                    then
                      (do
                        let w__23 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                        (pure ((((_get_HCR_EL2_Type_TGE w__23) == 1#1) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__24 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__29 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 (ELUsingAArch32 EL2))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__28 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                            (pure ((((_get_HCR_Type_TGE w__28) == 1#1) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__29 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x00#8)))
                      else sailThrow ((Error_Undefined ()))))
              else
                (do
                  let w__33 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__31 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__31) : Bool))))
                          else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__33 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__37 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__37 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                      else
                        (do
                          let w__45 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__39 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                     (pure (((! w__39) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                if ((← do
                                     let w__41 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure ((((_get_HCR_EL2_Type_TGE w__41) == 1#1) : Bool)))) : Bool)
                                then (pure true)
                                else
                                  (do
                                    let w__42 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                    let w__43 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                                    (pure (((((_get_MDCR_EL2_Type_TDE w__42) +++ (_get_MDCR_EL2_Type_TDA
                                            w__43)) != 0b00#2) : Bool)))))
                            else (pure false) ) : SailM Bool )
                          if (w__45 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__53 ← (( do
                                if ((← do
                                     if ((← do
                                          (EL2Enabled ())) : Bool)
                                     then
                                       (do
                                         (ELUsingAArch32 EL2))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    if ((← do
                                         let w__49 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
                                         (pure ((((_get_HCR_Type_TGE w__49) == 1#1) : Bool)))) : Bool)
                                    then (pure true)
                                    else
                                      (do
                                        let w__50 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                        let w__51 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                        (pure (((((_get_HDCR_Type_TDE w__50) +++ (_get_HDCR_Type_TDA
                                                w__51)) != 0b00#2) : Bool)))))
                                else (pure false) ) : SailM Bool )
                              if (w__53 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                              else
                                (do
                                  let w__56 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              let w__54 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__54) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__56 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                  else
                                    (do
                                      let w__59 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL3))
                                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__59 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeMonitorTrapException ()))
                                      else
                                        (do
                                          let w__62 ← (( do
                                            (pure ((← do
                                                  if (((HaveEL EL3) : Bool) : Bool)
                                                  then
                                                    (do
                                                      let w__60 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__60) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__62 : Bool)
                                          then
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x06#8)))
                                          else
                                            (do
                                              let w__63 ← (( do (MemA_read address 4) ) : SailM
                                                (BitVec (8 * 4)) )
                                              (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__63))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__67 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__65 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__65) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__67 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
              else
                (do
                  let w__71 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__71 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__77 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__73 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__73) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__75 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__76 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__75) +++ (_get_MDCR_EL2_Type_TDA
                                    w__76)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__77 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                      else
                        (do
                          let w__83 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__81 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                let w__82 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                (pure (((((_get_HDCR_Type_TDE w__81) +++ (_get_HDCR_Type_TDA w__82)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__83 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__86 ← (( do
                                (pure ((← do
                                      if (((HaveEL EL3) : Bool) : Bool)
                                      then
                                        (do
                                          let w__84 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__84) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__86 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                              else
                                (do
                                  let w__89 ← (( do
                                    (pure ((← do
                                          if (((HaveEL EL3) : Bool) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__89 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeMonitorTrapException ()))
                                  else
                                    (do
                                      let w__92 ← (( do
                                        (pure ((← do
                                              if (((HaveEL EL3) : Bool) : Bool)
                                              then
                                                (do
                                                  let w__90 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__90) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__92 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                      else
                                        (do
                                          let w__93 ← (( do (MemA_read address 4) ) : SailM
                                            (BitVec (8 * 4)) )
                                          (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__93))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__96 ← (( do
                    (pure ((← do
                          if (((HaveEL EL3) : Bool) : Bool)
                          then
                            (do
                              let w__94 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__94) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__96 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__99 ← (( do
                        (pure ((← do
                              if (((HaveEL EL3) : Bool) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__99 : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
                      else
                        (do
                          let w__102 ← (( do
                            (pure ((← do
                                  if (((HaveEL EL3) : Bool) : Bool)
                                  then
                                    (do
                                      let w__100 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__100) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__102 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__103 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4))
                                )
                              (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__103))))))
              else
                (do
                  if ((__PSTATE_EL == EL3) : Bool)
                  then
                    (do
                      if (((__PSTATE_M != M32_Monitor) && (__SDCR_TDCC == 1#1)) : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
                      else
                        (do
                          let w__104 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
                          (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__104))))
                  else (pure (()))))))


/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDM_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let address ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 14
    (do
      let mut loop_vars := address
      for i in [loop_i_lower:loop_i_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                   (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
          then
            (do
              let w__0 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
              (R_set i w__0)
              let address : (BitVec 32) := (BitVec.addInt address 4)
              (pure (address)))
          else (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool)
  then
    (do
      let w__1 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
      (LoadWritePC w__1))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 0#1)) : Bool)
  then
    (do
      let w__2 ← (( do (R_read n) ) : SailM (BitVec 32) )
      (R_set n (BitVec.addInt w__2 (4 *i (BitCount registers)))))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 1#1)) : Bool)
  then
    (do
      let w__3 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (R_set n w__3))
  else (pure (()))


/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDMDA_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address : (BitVec 32) := (BitVec.addInt (BitVec.subInt w__0 (4 *i (BitCount registers))) 4)
  let address ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 14
    (do
      let mut loop_vars := address
      for i in [loop_i_lower:loop_i_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                   (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
          then
            (do
              let w__1 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
              (R_set i w__1)
              let address : (BitVec 32) := (BitVec.addInt address 4)
              (pure (address)))
          else (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool)
  then
    (do
      let w__2 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
      (LoadWritePC w__2))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 0#1)) : Bool)
  then
    (do
      let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
      (R_set n (BitVec.subInt w__3 (4 *i (BitCount registers)))))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 1#1)) : Bool)
  then
    (do
      let w__4 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (R_set n w__4))
  else (pure (()))


/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDMDB_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address : (BitVec 32) := (BitVec.subInt w__0 (4 *i (BitCount registers)))
  let address ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 14
    (do
      let mut loop_vars := address
      for i in [loop_i_lower:loop_i_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                   (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
          then
            (do
              let w__1 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
              (R_set i w__1)
              let address : (BitVec 32) := (BitVec.addInt address 4)
              (pure (address)))
          else (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool)
  then
    (do
      let w__2 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
      (LoadWritePC w__2))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 0#1)) : Bool)
  then
    (do
      let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
      (R_set n (BitVec.subInt w__3 (4 *i (BitCount registers)))))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 1#1)) : Bool)
  then
    (do
      let w__4 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (R_set n w__4))
  else (pure (()))


/-- Type quantifiers: n : Nat, k_wback : Bool, 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDMIB_Op_A_txt (n : Nat) (registers : (BitVec 16)) (wback : Bool) : SailM Unit := do
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let address : (BitVec 32) := (BitVec.addInt w__0 4)
  let address ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 14
    (do
      let mut loop_vars := address
      for i in [loop_i_lower:loop_i_upper:1]i do
        let address := loop_vars
        loop_vars ← do
          if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers
                   (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
          then
            (do
              let w__1 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
              (R_set i w__1)
              let address : (BitVec 32) := (BitVec.addInt address 4)
              (pure (address)))
          else (pure (address))
      (pure loop_vars)) ) : SailM (BitVec 32) )
  if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers 15)])) == 1#1) : Bool)
  then
    (do
      let w__2 ← (( do (MemS_read address 4) ) : SailM (BitVec (8 * 4)) )
      (LoadWritePC w__2))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 0#1)) : Bool)
  then
    (do
      let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
      (R_set n (BitVec.addInt w__3 (4 *i (BitCount registers)))))
  else (pure (()))
  if ((wback && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access registers n)])) == 1#1)) : Bool)
  then
    (do
      let w__4 ← (( do (__UNKNOWN_bits 32) ) : SailM (BitVec 32) )
      (R_set n w__4))
  else (pure (()))


/-- Type quantifiers: k_add : Bool, k_index : Bool, n : Nat, t : Nat, k_wback : Bool, 0 ≤ t ∧
  t ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 -/
def execute_aarch32_instrs_LDRB_i_OpA_A_txt (add : Bool) (imm32 : (BitVec 32)) (index : Bool) (n : Nat) (t : Nat) (wback : Bool) : SailM Unit := do
  let offset_addr ← (( do
    if (add : Bool)
    then
      (do
        let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__0 + imm32))))
    else
      (do
        let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
        (pure ((w__1 - imm32)))) ) : SailM (BitVec 32) )
  let address ← (( do
    if (index : Bool)
    then (pure (offset_addr))
    else
      (do
        (R_read n)) ) : SailM (BitVec 32) )
  let _ : Unit :=
    if (((! wback) && (t != 15)) : Bool)
    then (AArch32_SetLSInstructionSyndrome 1 false t false)
    else ()
  let w__3 ← (( do (MemU_read address 1) ) : SailM (BitVec (8 * 1)) )
  (R_set t (Sail.BitVec.zeroExtend w__3 32))
  if (wback : Bool)
  then
    (do
      (R_set n offset_addr))
  else (pure (()))


end ArmFull.Functions
