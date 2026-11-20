module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0044
public import ArmFull.Fn.M0046
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0052
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0059
public import ArmFull.Fn.M0092
public import ArmFull.Fn.M0098
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0148
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0183
public import ArmFull.Fn.M0184
public import ArmFull.Fn.M0196
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0252
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
def DFAR_SysRegWrite32_27a6ae6fd1c0c709 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T6 : (BitVec 1) := (_get_HSTR_EL2_Type_T6 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T6 : (BitVec 1) := (_get_HSTR_Type_T6 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TVM : (BitVec 1) := (_get_HCR_Type_TVM w__4)
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
                          else (pure false)) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCR_TVM == 1#1) : Bool))) ) : SailM Bool )
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
                              let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DFAR_NS_write w__25))
                          else
                            (do
                              let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DFAR_write w__26)))))))
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
                  let w__30 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DFAR_NS_write w__30))
              else
                (do
                  let w__31 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DFAR_write w__31)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__32 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DFAR_S_write w__32))
                  else
                    (do
                      let w__33 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DFAR_NS_write w__33)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DFSR_SysRegWrite32_d19afe00f293902c (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T5 : (BitVec 1) := (_get_HSTR_EL2_Type_T5 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T5 : (BitVec 1) := (_get_HSTR_Type_T5 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TVM : (BitVec 1) := (_get_HCR_EL2_Type_TVM w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TVM : (BitVec 1) := (_get_HCR_Type_TVM w__4)
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
                          else (pure false)) && ((__HCR_EL2_TVM == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCR_TVM == 1#1) : Bool))) ) : SailM Bool )
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
                              let w__25 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DFSR_NS_write (Mk_DFSR_Type w__25)))
                          else
                            (do
                              let w__26 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (DFSR_write (Mk_DFSR_Type w__26))))))))
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
                  let w__30 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DFSR_NS_write (Mk_DFSR_Type w__30)))
              else
                (do
                  let w__31 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DFSR_write (Mk_DFSR_Type w__31))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then
                    (do
                      let w__32 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg DFSR_S (Mk_DFSR_Type w__32))
                  else
                    (do
                      let w__33 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DFSR_NS_write (Mk_DFSR_Type w__33))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DISR_SysRegWrite32_797163d94eb0b6e5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
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
                      let w__19 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      writeReg VDISR_EL2 (Mk_VDISR_EL2_Type (Sail.BitVec.zeroExtend w__19 64)))
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
                          let w__24 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (VDISR_write (Mk_VDISR_Type w__24)))
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
                          then (pure (()))
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
                              then (pure (()))
                              else
                                (do
                                  let w__37 ← (( do (R_read t) ) : SailM (BitVec 32) )
                                  (DISR_write (Mk_DISR_Type w__37)))))))))
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
              then (pure (()))
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
                  then (pure (()))
                  else
                    (do
                      let w__50 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (DISR_write (Mk_DISR_Type w__50)))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__51 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (DISR_write (Mk_DISR_Type w__51)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DTLBIALL_SysRegWrite32_e0269c0064c12331 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TTLB : (BitVec 1) := (_get_HCR_Type_TTLB w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__5)
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
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCR_TTLB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__29 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 (IsFeatureImplemented FEAT_XS)) : Bool)
                                            then
                                              (do
                                                let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                  Bool )
                                                (pure (((! w__23) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (IsFeatureImplemented FEAT_HCX))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (IsHCRXEL2Enabled ()))
                                  else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__29 : Bool)
                          then
                            (do
                              let w__30 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                              (AArch32_DTLBI_ALL w__30 Regime_EL10 Shareability_NSH TLBI_ExcludeXS))
                          else
                            (do
                              let w__31 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                              (AArch32_DTLBI_ALL w__31 Regime_EL10 Shareability_NSH TLBI_AllAttr)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__32 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              (AArch32_DTLBI_ALL w__32 Regime_EL10 Shareability_NSH TLBI_AllAttr))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__33 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  (AArch32_DTLBI_ALL w__33 Regime_EL30 Shareability_NSH TLBI_AllAttr))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DTLBIASID_SysRegWrite32_58b10d925491a590 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg HSTR_EL2 ) : SailM (BitVec 64) )
  let __HSTR_EL2_T8 : (BitVec 1) := (_get_HSTR_EL2_Type_T8 w__1)
  let w__2 ← (( do (HSTR_read ()) ) : SailM (BitVec 32) )
  let __HSTR_T8 : (BitVec 1) := (_get_HSTR_Type_T8 w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TTLB : (BitVec 1) := (_get_HCR_EL2_Type_TTLB w__3)
  let w__4 ← (( do (HCR_read ()) ) : SailM (BitVec 32) )
  let __HCR_TTLB : (BitVec 1) := (_get_HCR_Type_TTLB w__4)
  let w__5 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  let __HCRX_EL2_FnXS : (BitVec 1) := (_get_HCRX_EL2_Type_FnXS w__5)
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
                  else (pure false)) && ((__HSTR_EL2_T8 == 1#1) : Bool))) ) : SailM Bool )
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
                      else (pure false)) && ((__HSTR_T8 == 1#1) : Bool))) ) : SailM Bool )
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
                          else (pure false)) && ((__HCR_EL2_TTLB == 1#1) : Bool))) ) : SailM Bool )
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
                              else (pure false)) && ((__HCR_TTLB == 1#1) : Bool))) ) : SailM Bool )
                      if (w__21 : Bool)
                      then
                        (do
                          (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
                      else
                        (do
                          let w__29 ← (( do
                            (pure ((← do
                                  if ((← do
                                       if ((← do
                                            if ((← do
                                                 (IsFeatureImplemented FEAT_XS)) : Bool)
                                            then
                                              (do
                                                let w__23 ← (( do (ELUsingAArch32 EL2) ) : SailM
                                                  Bool )
                                                (pure (((! w__23) : Bool))))
                                            else (pure false)) : Bool)
                                       then
                                         (do
                                           (IsFeatureImplemented FEAT_HCX))
                                       else (pure false)) : Bool)
                                  then
                                    (do
                                      (IsHCRXEL2Enabled ()))
                                  else (pure false)) && ((__HCRX_EL2_FnXS == 1#1) : Bool))) ) :
                            SailM Bool )
                          if (w__29 : Bool)
                          then
                            (do
                              let w__30 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                              let w__31 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                              let w__32 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (AArch32_DTLBI_ASID w__30 Regime_EL10 w__31 Shareability_NSH
                                TLBI_ExcludeXS w__32))
                          else
                            (do
                              let w__33 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
                              let w__34 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
                              let w__35 ← (( do (R_read t) ) : SailM (BitVec 32) )
                              (AArch32_DTLBI_ASID w__33 Regime_EL10 w__34 Shareability_NSH
                                TLBI_AllAttr w__35)))))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__36 ← (( do (SecurityStateAtEL EL1) ) : SailM SecurityState )
              let w__37 ← (( do (VMID_read ()) ) : SailM (BitVec 16) )
              let w__38 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (AArch32_DTLBI_ASID w__36 Regime_EL10 w__37 Shareability_NSH TLBI_AllAttr w__38))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__39 ← (( do (SecurityStateAtEL EL3) ) : SailM SecurityState )
                  let w__40 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (AArch32_DTLBI_ASID w__39 Regime_EL30 VMID_NONE Shareability_NSH TLBI_AllAttr
                    w__40))
              else (pure (())))))


end ArmFull.Functions
