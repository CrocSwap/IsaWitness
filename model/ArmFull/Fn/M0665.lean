module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0137
public import ArmFull.Fn.M0140
public import ArmFull.Fn.M0141
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0199
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0253
public import ArmFull.Fn.M0258 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: t : Int -/
def DFAR_SysRegRead32_24eaaed98bd8c8b9 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T6 : (BitVec 1) := (_get_HSTR_EL2_Type_T6 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T6 : (BitVec 1) := (_get_HSTR_Type_T6 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TRVM : (BitVec 1) := (_get_HCR_EL2_Type_TRVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TRVM : (BitVec 1) := (_get_HCR_Type_TRVM w__4)
  let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T6 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T6 == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__15) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TRVM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__24 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__25 ← (( do (DFAR_NS_read ()) ) : SailM (BitVec 32) )
                              (R_set t w__25))
                          else
                            (do
                              let w__26 ← (( do (DFAR_read ()) ) : SailM (BitVec 32) )
                              (R_set t w__26)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__29 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  let w__30 ← (( do (DFAR_NS_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__30))
              else
                (do
                  let w__31 ← (( do (DFAR_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__31)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__32 ← (( do (DFAR_S_read ()) ) : SailM (BitVec 32) )
                      (R_set t w__32))
                  else
                    (do
                      let w__33 ← (( do (DFAR_NS_read ()) ) : SailM (BitVec 32) )
                      (R_set t w__33)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DFSR_SysRegRead32_094c65de67978ba7 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TRVM : (BitVec 1) := (_get_HCR_EL2_Type_TRVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TRVM : (BitVec 1) := (_get_HCR_Type_TRVM w__4)
  let w__5 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__5)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__9 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__7 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__7) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T5 == 1#1) : Bool))) ) : SailM Bool )
          if (w__9 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__13 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T5 == 1#1) : Bool))) ) : SailM Bool )
              if (w__13 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__17 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__15 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__15) : Bool))))
                          else (pure false)) && ((__HCR_EL2_TRVM == 1#1) : Bool))) ) : SailM Bool )
                  if (w__17 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__21 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_TRVM == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__24 ← (( do
                            if ((← do
                                 (HaveEL EL3)) : Bool)
                            then
                              (do
                                (ELUsingAArch32 EL3))
                            else (pure false) ) : SailM Bool )
                          if (w__24 : Bool)
                          then
                            (do
                              let w__25 ← (( do (DFSR_NS_read ()) ) : SailM (BitVec 32) )
                              (R_set t w__25))
                          else
                            (do
                              let w__26 ← (( do (DFSR_read ()) ) : SailM (BitVec 32) )
                              (R_set t w__26)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__29 ← (( do
                if ((← do
                     (HaveEL EL3)) : Bool)
                then
                  (do
                    (ELUsingAArch32 EL3))
                else (pure false) ) : SailM Bool )
              if (w__29 : Bool)
              then
                (do
                  let w__30 ← (( do (DFSR_NS_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__30))
              else
                (do
                  let w__31 ← (( do (DFSR_read ()) ) : SailM (BitVec 32) )
                  (R_set t w__31)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__32 ← (( do readReg DFSR_S ) : SailM (BitVec 32) )
                      (R_set t w__32))
                  else
                    (do
                      let w__33 ← (( do (DFSR_NS_read ()) ) : SailM (BitVec 32) )
                      (R_set t w__33)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DISR_SysRegRead32_9f42ad0cc10a5f19 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T12 : (BitVec 1) := (_get_HSTR_EL2_Type_T12 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T12 : (BitVec 1) := (_get_HSTR_Type_T12 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_AMO : (BitVec 1) := (_get_HCR_EL2_Type_AMO w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_AMO : (BitVec 1) := (_get_HCR_Type_AMO w__4)
  let w__5 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_EA : (BitVec 1) := (_get_SCR_EL3_Type_EA w__5)
  let w__6 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_EA : (BitVec 1) := (_get_SCR_Type_EA w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__10 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__8 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                      (pure (((! w__8) : Bool))))
                  else (pure false)) && ((__HSTR_EL2_T12 == 1#1) : Bool))) ) : SailM Bool )
          if (w__10 : Bool)
          then
            (do
              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
          else
            (do
              let w__14 ← (( do
                (pure ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL2))
                      else (pure false)) && ((__HSTR_T12 == 1#1) : Bool))) ) : SailM Bool )
              if (w__14 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  let w__18 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__16 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__16) : Bool))))
                          else (pure false)) && ((__HCR_EL2_AMO == 1#1) : Bool))) ) : SailM Bool )
                  if (w__18 : Bool)
                  then
                    (do
                      let w__19 ← (( do readReg VDISR_EL2 ) : SailM (BitVec 64) )
                      (R_set t (Sail.BitVec.extractLsb (__get_VDISR_EL2 w__19) 31 0)))
                  else
                    (do
                      let w__23 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HCR_AMO == 1#1) : Bool))) ) : SailM Bool )
                      if (w__23 : Bool)
                      then
                        (do
                          let w__24 ← (( do (VDISR_read ()) ) : SailM (BitVec 32) )
                          (R_set t (__get_VDISR w__24)))
                      else
                        (do
                          let w__30 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            (HaveEL EL3)) : Bool)
                                       then
                                         (do
                                           let w__26 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                           (pure (((! w__26) : Bool))))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      let w__28 ← (( do (Halted ()) ) : SailM Bool )
                                      (pure (((! w__28) : Bool))))
                                  else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__30 : Bool)
                          then
                            (do
                              (R_set t (Zeros (n := 32))))
                          else
                            (do
                              let w__36 ← (( do
                                (pure ((← do
                                      if ((← do
                                           if ((← do
                                                (HaveEL EL3)) : Bool)
                                           then
                                             (do
                                               (ELUsingAArch32 EL3))
                                           else (pure false)) : Bool)
                                      then
                                        (do
                                          let w__34 ← (( do (Halted ()) ) : SailM Bool )
                                          (pure (((! w__34) : Bool))))
                                      else (pure false)) && ((__SCR_EA == 1#1) : Bool))) ) : SailM
                                Bool )
                              if (w__36 : Bool)
                              then
                                (do
                                  (R_set t (Zeros (n := 32))))
                              else
                                (do
                                  let w__37 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
                                  (R_set t (__get_DISR w__37)))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__43 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                (HaveEL EL3)) : Bool)
                           then
                             (do
                               let w__39 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                               (pure (((! w__39) : Bool))))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__41 ← (( do (Halted ()) ) : SailM Bool )
                          (pure (((! w__41) : Bool))))
                      else (pure false)) && ((__SCR_EL3_EA == 1#1) : Bool))) ) : SailM Bool )
              if (w__43 : Bool)
              then
                (do
                  (R_set t (Zeros (n := 32))))
              else
                (do
                  let w__49 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    (HaveEL EL3)) : Bool)
                               then
                                 (do
                                   (ELUsingAArch32 EL3))
                               else (pure false)) : Bool)
                          then
                            (do
                              let w__47 ← (( do (Halted ()) ) : SailM Bool )
                              (pure (((! w__47) : Bool))))
                          else (pure false)) && ((__SCR_EA == 1#1) : Bool))) ) : SailM Bool )
                  if (w__49 : Bool)
                  then
                    (do
                      (R_set t (Zeros (n := 32))))
                  else
                    (do
                      let w__50 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_DISR w__50)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__51 ← (( do (DISR_read ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_DISR w__51)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def ERRIDR_SysRegRead32_98e51b40bf051290 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_TERR : (BitVec 1) := (_get_SCR_EL3_Type_TERR w__1)
  let w__2 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_TERR : (BitVec 1) := (_get_SCR_Type_TERR w__2)
  let w__3 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__3)
  let w__4 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__4)
  let w__5 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TERR : (BitVec 1) := (_get_HCR_EL2_Type_TERR w__5)
  let w__6 ← (( do (HCR2_read ()) ) : SailM (BitVec 32) )
  let __HCR2_TERR : (BitVec 1) := (_get_HCR2_Type_TERR w__6)
  let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_M : (BitVec 5) := w__7.M
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__17 ← (( do
            (pure ((← do
                  if ((← do
                       if ((← do
                            if ((← do
                                 if ((← do
                                      (Halted ())) : Bool)
                                 then
                                   (do
                                     (HaveEL EL3))
                                 else (pure false)) : Bool)
                            then
                              (do
                                let w__11 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__11) == 1#1) : Bool))))
                            else (pure false)) : Bool)
                       then
                         (do
                           (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                       else (pure false)) : Bool)
                  then
                    (do
                      let w__15 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                      (pure (((! w__15) : Bool))))
                  else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
          if (w__17 : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__27 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__21 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__21) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          (ELUsingAArch32 EL3))
                      else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__27 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__29 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                              (pure (((! w__29) : Bool))))
                          else (pure false)) && ((__HSTR_EL2_T5 == 1#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                  else
                    (do
                      let w__35 ← (( do
                        (pure ((← do
                              if ((← do
                                   (EL2Enabled ())) : Bool)
                              then
                                (do
                                  (ELUsingAArch32 EL2))
                              else (pure false)) && ((__HSTR_T5 == 1#1) : Bool))) ) : SailM Bool )
                      if (w__35 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__39 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (EL2Enabled ())) : Bool)
                                  then
                                    (do
                                      let w__37 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
                                      (pure (((! w__37) : Bool))))
                                  else (pure false)) && ((__HCR_EL2_TERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__39 : Bool)
                          then
                            (do
                              (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))
                          else
                            (do
                              let w__43 ← (( do
                                (pure ((← do
                                      if ((← do
                                           (EL2Enabled ())) : Bool)
                                      then
                                        (do
                                          (ELUsingAArch32 EL2))
                                      else (pure false)) && ((__HCR2_TERR == 1#1) : Bool))) ) :
                                SailM Bool )
                              if (w__43 : Bool)
                              then
                                (do
                                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                              else
                                (do
                                  let w__47 ← (( do
                                    (pure ((← do
                                          if ((← do
                                               (HaveEL EL3)) : Bool)
                                          then
                                            (do
                                              let w__45 ← (( do (ELUsingAArch32 EL3) ) : SailM
                                                Bool )
                                              (pure (((! w__45) : Bool))))
                                          else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) )
                                    : SailM Bool )
                                  if (w__47 : Bool)
                                  then
                                    (do
                                      let w__50 ← (( do
                                        if ((← do
                                             (Halted ())) : Bool)
                                        then
                                          (do
                                            let w__49 ← (( do (EDSCR_read ()) ) : SailM
                                              (BitVec 32) )
                                            (pure ((((_get_EDSCR_Type_SDD w__49) == 1#1) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__50 : Bool)
                                      then sailThrow ((Error_Undefined ()))
                                      else
                                        (do
                                          (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                                  else
                                    (do
                                      let w__55 ← (( do
                                        (pure ((← do
                                              (pure ((← do
                                                    if ((← do
                                                         (HaveEL EL3)) : Bool)
                                                    then
                                                      (do
                                                        (ELUsingAArch32 EL3))
                                                    else (pure false)) && ((__PSTATE_M != M32_Monitor) : Bool)))) && ((__SCR_TERR == 1#1) : Bool)))
                                        ) : SailM Bool )
                                      if (w__55 : Bool)
                                      then
                                        (do
                                          let w__58 ← (( do
                                            if ((← do
                                                 (Halted ())) : Bool)
                                            then
                                              (do
                                                let w__57 ← (( do (EDSCR_read ()) ) : SailM
                                                  (BitVec 32) )
                                                (pure ((((_get_EDSCR_Type_SDD w__57) == 1#1) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__58 : Bool)
                                          then sailThrow ((Error_Undefined ()))
                                          else
                                            (do
                                              (AArch32_TakeMonitorTrapException ())))
                                      else
                                        (do
                                          let w__59 ← (( do (ERRIDR_read ()) ) : SailM (BitVec 32)
                                            )
                                          (R_set t (__get_ERRIDR w__59)))))))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__69 ← (( do
                (pure ((← do
                      if ((← do
                           if ((← do
                                if ((← do
                                     if ((← do
                                          (Halted ())) : Bool)
                                     then
                                       (do
                                         (HaveEL EL3))
                                     else (pure false)) : Bool)
                                then
                                  (do
                                    let w__63 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__63) == 1#1) : Bool))))
                                else (pure false)) : Bool)
                           then
                             (do
                               (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                           else (pure false)) : Bool)
                      then
                        (do
                          let w__67 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                          (pure (((! w__67) : Bool))))
                      else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM Bool )
              if (w__69 : Bool)
              then sailThrow ((Error_Undefined ()))
              else
                (do
                  let w__79 ← (( do
                    (pure ((← do
                          if ((← do
                               if ((← do
                                    if ((← do
                                         if ((← do
                                              (Halted ())) : Bool)
                                         then
                                           (do
                                             (HaveEL EL3))
                                         else (pure false)) : Bool)
                                    then
                                      (do
                                        let w__73 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                        (pure ((((_get_EDSCR_Type_SDD w__73) == 1#1) : Bool))))
                                    else (pure false)) : Bool)
                               then
                                 (do
                                   (__IMPDEF_boolean "EL3 trap priority when SDD == '1'"))
                               else (pure false)) : Bool)
                          then
                            (do
                              (ELUsingAArch32 EL3))
                          else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM Bool )
                  if (w__79 : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__83 ← (( do
                        (pure ((← do
                              if ((← do
                                   (HaveEL EL3)) : Bool)
                              then
                                (do
                                  let w__81 ← (( do (ELUsingAArch32 EL3) ) : SailM Bool )
                                  (pure (((! w__81) : Bool))))
                              else (pure false)) && ((__SCR_EL3_TERR == 1#1) : Bool))) ) : SailM
                        Bool )
                      if (w__83 : Bool)
                      then
                        (do
                          let w__86 ← (( do
                            if ((← do
                                 (Halted ())) : Bool)
                            then
                              (do
                                let w__85 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                (pure ((((_get_EDSCR_Type_SDD w__85) == 1#1) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__86 : Bool)
                          then sailThrow ((Error_Undefined ()))
                          else
                            (do
                              (AArch64_AArch32SystemAccessTrap EL3 (BitVec.toNat 0x03#8))))
                      else
                        (do
                          let w__90 ← (( do
                            (pure ((← do
                                  if ((← do
                                       (HaveEL EL3)) : Bool)
                                  then
                                    (do
                                      (ELUsingAArch32 EL3))
                                  else (pure false)) && ((__SCR_TERR == 1#1) : Bool))) ) : SailM
                            Bool )
                          if (w__90 : Bool)
                          then
                            (do
                              let w__93 ← (( do
                                if ((← do
                                     (Halted ())) : Bool)
                                then
                                  (do
                                    let w__92 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
                                    (pure ((((_get_EDSCR_Type_SDD w__92) == 1#1) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__93 : Bool)
                              then sailThrow ((Error_Undefined ()))
                              else
                                (do
                                  (AArch32_TakeMonitorTrapException ())))
                          else
                            (do
                              let w__94 ← (( do (ERRIDR_read ()) ) : SailM (BitVec 32) )
                              (R_set t (__get_ERRIDR w__94)))))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if (((__PSTATE_M != M32_Monitor) && (__SCR_TERR == 1#1)) : Bool)
                  then
                    (do
                      (AArch32_TakeMonitorTrapException ()))
                  else
                    (do
                      let w__95 ← (( do (ERRIDR_read ()) ) : SailM (BitVec 32) )
                      (R_set t (__get_ERRIDR w__95))))
              else (pure (())))))


end ArmFull.Functions
