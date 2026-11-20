module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0243
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0258
public import ArmFull.Fn.M1197 set_option backward.proofsInPublic true @[expose] public section

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
                                  let w__57 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__55 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__55) : Bool))))
                                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool)))
                                    ) : SailM Bool )
                                  if (w__57 : Bool)
                                  then
                                    (do
                                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                  else
                                    (do
                                      let w__61 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  (ELUsingAArch32 EL3))
                                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__61 : Bool)
                                      then
                                        (do
                                          (AArch32_TakeMonitorTrapException ()))
                                      else
                                        (do
                                          let w__65 ← (( do
                                            (pure ((← do
                                                  if ((← do
                                                       (HaveEL EL3)) : Bool)
                                                  then
                                                    (do
                                                      let w__63 ← (( do (ELUsingAArch32 EL3) ) :
                                                        SailM Bool )
                                                      (pure (((! w__63) : Bool))))
                                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                            ) : SailM Bool )
                                          if (w__65 : Bool)
                                          then
                                            (do
                                              (AArch64_AArch32SystemAccessTrap EL3
                                                (BitVec.toNat 0x06#8)))
                                          else
                                            (do
                                              let w__66 ← (( do (MemA_read address 4) ) : SailM
                                                (BitVec (8 * 4)) )
                                              (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__66))))))))))))
      else
        (do
          if ((__PSTATE_EL == EL1) : Bool)
          then
            (do
              let w__70 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          let w__68 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                          (pure (((! w__68) : Bool))))
                      else (pure false)) && ((__MDCR_EL2_TDCC == 1#1) : Bool))) ) : SailM Bool )
              if (w__70 : Bool)
              then
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
              else
                (do
                  let w__74 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL2))
                          else (pure false)) && ((__HDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__74 : Bool)
                  then
                    (do
                      (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__80 ← (( do
                        if ((← do
                             if ((← do
                                  (EL2Enabled ())) : Bool)
                             then
                               (do
                                 let w__76 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                 (pure (((! w__76) : Bool))))
                             else (pure false)) : Bool)
                        then
                          (do
                            let w__78 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            let w__79 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
                            (pure (((((_get_MDCR_EL2_Type_TDE w__78) +++ (_get_MDCR_EL2_Type_TDA
                                    w__79)) != 0b00#2) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__80 : Bool)
                      then
                        (do
                          (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x06#8)))
                      else
                        (do
                          let w__86 ← (( do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     (ELUsingAArch32 EL2))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__84 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                let w__85 ← (( do (HDCR_read ()) ) : SailM (BitVec 32) )
                                (pure (((((_get_HDCR_Type_TDE w__84) +++ (_get_HDCR_Type_TDA w__85)) != 0b00#2) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__86 : Bool)
                          then
                            (do
                              (AArch32_TakeHypTrapException (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__90 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (HaveEL EL3)) : Bool)
                                      then
                                        (do
                                          let w__88 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                          (pure (((! w__88) : Bool))))
                                      else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__90 : Bool)
                              then
                                (do
                                  (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                              else
                                (do
                                  let w__94 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              (ELUsingAArch32 EL3))
                                          else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) :
                                    SailM Bool )
                                  if (w__94 : Bool)
                                  then
                                    (do
                                      (AArch32_TakeMonitorTrapException ()))
                                  else
                                    (do
                                      let w__98 ← (( do
                                        (pure ((← do
                                              if ((← do
                                                   (HaveEL EL3)) : Bool)
                                              then
                                                (do
                                                  let w__96 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                    Bool )
                                                  (pure (((! w__96) : Bool))))
                                              else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__98 : Bool)
                                      then
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                                      else
                                        (do
                                          let w__99 ← (( do (MemA_read address 4) ) : SailM
                                            (BitVec (8 * 4)) )
                                          (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__99))))))))))
          else
            (do
              if ((__PSTATE_EL == EL2) : Bool)
              then
                (do
                  let w__103 ← (( do
                    (pure ((← do
                          if ((← do
                               (HaveEL EL3)) : Bool)
                          then
                            (do
                              let w__101 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                              (pure (((! w__101) : Bool))))
                          else (pure false)) && ((__MDCR_EL3_TDCC == 1#1) : Bool))) ) : SailM Bool )
                  if (w__103 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                  else
                    (do
                      let w__107 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL3))
                              else (pure false)) && ((__SDCR_TDCC == 1#1) : Bool))) ) : SailM Bool )
                      if (w__107 : Bool)
                      then
                        (do
                          (AArch32_TakeMonitorTrapException ()))
                      else
                        (do
                          let w__111 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      let w__109 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                      (pure (((! w__109) : Bool))))
                                  else (pure false)) && ((__MDCR_EL3_TDA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__111 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x06#8)))
                          else
                            (do
                              let w__112 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4))
                                )
                              (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__112))))))
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
                          let w__113 ← (( do (MemA_read address 4) ) : SailM (BitVec (8 * 4)) )
                          (DBGDTRTXint_write (Mk_DBGDTRTXint_Type w__113))))
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


end ArmFull.Functions
