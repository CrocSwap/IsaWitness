import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0036
import ArmFull.Fn.M0038
import ArmFull.Fn.M0048
import ArmFull.Fn.M0049
import ArmFull.Fn.M0053
import ArmFull.Fn.M0054
import ArmFull.Fn.M0055
import ArmFull.Fn.M0056
import ArmFull.Fn.M0063
import ArmFull.Fn.M0079
import ArmFull.Fn.M0082
import ArmFull.Fn.M0086
import ArmFull.Fn.M0087
import ArmFull.Fn.M0100
import ArmFull.Fn.M0115
import ArmFull.Fn.M0121
import ArmFull.Fn.M0137
import ArmFull.Fn.M0141
import ArmFull.Fn.M0144
import ArmFull.Fn.M0150
import ArmFull.Fn.M0159
import ArmFull.Fn.M0166
import ArmFull.Fn.M0202
import ArmFull.Fn.M0203

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
def CNTKCTL_SysRegRead32_9166ed3878001f60 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__1 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
          (R_set t (__get_CNTKCTL w__1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
              (R_set t (__get_CNTKCTL w__2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__3 ← (( do (CNTKCTL_read__1 ()) ) : SailM (BitVec 32) )
                  (R_set t (__get_CNTKCTL w__3)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DLR_SysRegRead32_8fb9614c85c3b992 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (DLR_read ()) ) : SailM (BitVec 32) )
      (R_set t w__1))


/-- Type quantifiers: t : Int -/
def DSPSR2_SysRegRead32_6da9b04f72c6c3f2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (DSPSR2_read ()) ) : SailM (BitVec 32) )
      (R_set t (__get_DSPSR2 w__1)))


/-- Type quantifiers: t : Int -/
def DSPSR_SysRegRead32_b8ab5544c94609ec (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (DSPSR_read ()) ) : SailM (BitVec 32) )
      (R_set t w__1))


/-- Type quantifiers: t : Int -/
def JMCR_SysRegRead32_f5fe518171c35ee0 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do (__IMPDEF_boolean "JMCR UNDEFINED at EL0") ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__2 ← (( do readReg JMCR ) : SailM (BitVec 32) )
          (R_set t (__get_JMCR w__2))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do readReg JMCR ) : SailM (BitVec 32) )
          (R_set t (__get_JMCR w__3)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do readReg JMCR ) : SailM (BitVec 32) )
              (R_set t (__get_JMCR w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg JMCR ) : SailM (BitVec 32) )
                  (R_set t (__get_JMCR w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def JOSCR_SysRegRead32_64dbf044d539336d (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__1 ← (( do (__IMPDEF_boolean "JOSCR UNDEFINED at EL0") ) : SailM Bool )
      if (w__1 : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          let w__2 ← (( do readReg JOSCR ) : SailM (BitVec 32) )
          (R_set t (__get_JOSCR w__2))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__3 ← (( do readReg JOSCR ) : SailM (BitVec 32) )
          (R_set t (__get_JOSCR w__3)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__4 ← (( do readReg JOSCR ) : SailM (BitVec 32) )
              (R_set t (__get_JOSCR w__4)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__5 ← (( do readReg JOSCR ) : SailM (BitVec 32) )
                  (R_set t (__get_JOSCR w__5)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def RMR_SysRegRead32_43cf65be6b4153a2 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__4 ← (( do
    if ((← do
         if ((← do
              let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
              (pure (((w__0.EL == EL1) : Bool)))) : Bool)
         then (pure true)
         else
           (do
             let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
             (pure (((w__1.EL == EL3) : Bool))))) : Bool)
    then
      (do
        let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((IsHighestEL w__3.EL) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__4 : Bool)
  then
    (do
      let w__5 ← (( do (RMR_read ()) ) : SailM (BitVec 32) )
      (R_set t (__get_RMR w__5)))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int, t2 : Int -/
def CNTHP_CVAL_SysRegRead64_bedb5ea1dc82962f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
              let w__3 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
              let (__tup_0, __tup_1) :=
                ((Sail.BitVec.extractLsb w__2 63 32), (Sail.BitVec.extractLsb w__3 31 0))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__4 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
                      let w__5 ← (( do (CNTHP_CVAL_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__4 63 32), (Sail.BitVec.extractLsb w__5 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure (())))))


/-- Type quantifiers: t : Int, t2 : Int -/
def CNTVOFF_SysRegRead64_66c4d48806fce48e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 4)) (CRm : (BitVec 4)) (t : Int) (t2 : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
              let w__3 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
              let (__tup_0, __tup_1) :=
                ((Sail.BitVec.extractLsb w__2 63 32), (Sail.BitVec.extractLsb w__3 31 0))
              (R_set t2 __tup_0)
              (R_set t __tup_1))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__4 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                      let w__5 ← (( do (CNTVOFF_read ()) ) : SailM (BitVec 64) )
                      let (__tup_0, __tup_1) :=
                        ((Sail.BitVec.extractLsb w__4 63 32), (Sail.BitVec.extractLsb w__5 31 0))
                      (R_set t2 __tup_0)
                      (R_set t __tup_1)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTFRQ_SysRegWrite32_bb1fcec10c61c758 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((IsHighestEL w__0.EL) : Bool)
  then
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (CNTFRQ_write w__1))
  else sailThrow ((Error_Undefined ()))


/-- Type quantifiers: t : Int -/
def CNTHCTL_SysRegWrite32_7d97fc0c6abe59e3 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (CNTHCTL_write (Mk_CNTHCTL_Type w__2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (CNTHCTL_write (Mk_CNTHCTL_Type w__3))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_CTL_SysRegWrite32_ed680b861de2ac5b (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (__set_CNTHP_CTL (Mk_CNTHP_CTL_Type w__2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      (__set_CNTHP_CTL (Mk_CNTHP_CTL_Type w__3))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTHP_TVAL_SysRegWrite32_1a9db618df39c059 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCR ) : SailM (BitVec 32) )
  let __SCR_NS : (BitVec 1) := (_get_SCR_Type_NS w__1)
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then sailThrow ((Error_Undefined ()))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (R_read t) ) : SailM (BitVec 32) )
              let w__3 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
              (CNTHP_CVAL_write
                (Mk_CNTHP_CVAL_Type ((Sail.BitVec.castWidth (m := 64) (sign_extend w__2 64)) + w__3))))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  if ((__SCR_NS == 0#1) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__4 ← (( do (R_read t) ) : SailM (BitVec 32) )
                      let w__5 ← (( do (PhysicalCountInt ()) ) : SailM (BitVec 64) )
                      (CNTHP_CVAL_write
                        (Mk_CNTHP_CVAL_Type
                          ((Sail.BitVec.castWidth (m := 64) (sign_extend w__4 64)) + w__5)))))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def CNTKCTL_SysRegWrite32_e68a84be701ace4f (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
          (CNTKCTL_write (Mk_CNTKCTL_Type w__1)))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__2 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (CNTKCTL_write (Mk_CNTKCTL_Type w__2)))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__3 ← (( do (R_read t) ) : SailM (BitVec 32) )
                  (CNTKCTL_write (Mk_CNTKCTL_Type w__3)))
              else (pure (())))))


/-- Type quantifiers: t : Int -/
def DLR_SysRegWrite32_aff2e156d6e1196e (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (DLR_write w__1))


/-- Type quantifiers: t : Int -/
def DSPSR2_SysRegWrite32_d1d98bc563bc83d5 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (DSPSR2_write (Mk_DSPSR2_Type w__1)))


/-- Type quantifiers: t : Int -/
def DSPSR_SysRegWrite32_eb89215986db3057 (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do (Halted ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
      (DSPSR_write (Mk_DSPSR_Type w__1)))


/-- Type quantifiers: t : Int -/
def RMR_SysRegWrite32_9dfdd4710efdf52a (el : (BitVec 2)) (coproc : (BitVec 4)) (opc1 : (BitVec 3)) (CRn : (BitVec 4)) (opc2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  if ((__PSTATE_EL == EL0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          if ((IsHighestEL EL1) : Bool)
          then
            (do
              let w__1 ← (( do (R_read t) ) : SailM (BitVec 32) )
              (RMR_write (Mk_RMR_Type w__1)))
          else sailThrow ((Error_Undefined ())))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__2 ← (( do readReg CP15SDISABLE ) : SailM Signal )
                  if ((BEq.beq w__2 Signal_High) : Bool)
                  then sailThrow ((Error_Undefined ()))
                  else
                    (do
                      let w__3 ← (( do readReg CP15SDISABLE2 ) : SailM Signal )
                      if ((BEq.beq w__3 Signal_High) : Bool)
                      then sailThrow ((Error_Undefined ()))
                      else
                        (do
                          let w__4 ← (( do (R_read t) ) : SailM (BitVec 32) )
                          (RMR_write (Mk_RMR_Type w__4)))))
              else (pure (())))))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADC_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2918) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2919) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
  let (tup__0, tup__1) := ((AddWithCarry w__3 shifted w__4.C) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__8 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__8 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_setflags : Bool, 0 ≤ n ∧
  n ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_i_OpT_A_txt (d : Nat) (imm32 : (BitVec 32)) (n : Nat) (setflags : Bool) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2922) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2923) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__0 imm32 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__1 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__2 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_ADD_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let nzcv ← (( do (undefined_bitvector_at (← occLabel 2934) 4) ) : SailM (BitVec 4) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2935) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let shifted ← (( do (Shift w__1 shift_t shift_n w__2.C) ) : SailM (BitVec 32) )
  let w__3 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let (tup__0, tup__1) := ((AddWithCarry w__3 shifted 0#1) : ((BitVec 32) × (BitVec 4)))
  let result : (BitVec 32) := tup__0
  let nzcv : (BitVec 4) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (Sail.BitVec.extractLsb nzcv 3 3) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (Sail.BitVec.extractLsb nzcv 2 2) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := (Sail.BitVec.extractLsb nzcv 1 1) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with V := (Sail.BitVec.extractLsb nzcv 0 0) })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, s : Nat, k_setflags : Bool, 0 ≤ s ∧
  s ≤ 15 ∧ 0 ≤ n ∧ n ≤ 15 ∧ 0 ≤ m ∧ m ≤ 15 ∧ 0 ≤ d ∧ d ≤ 15 -/
def execute_aarch32_instrs_AND_rr_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (s : Nat) (setflags : Bool) (shift_t : SRType) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 2960) 1) ) : SailM (BitVec 1) )
  let shifted ← (( do (undefined_bitvector_at (← occLabel 2961) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read s) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 shift_t shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1)) )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let shifted : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  let w__4 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let result : (BitVec 32) := (w__4 &&& shifted)
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with Z := (IsZeroBit result) }
      let w__7 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__7 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, k_setflags : Bool, shift_n : Int, List.elem m
  [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_ASR_i_Op_A_txt (d : Nat) (m : Nat) (setflags : Bool) (shift_n : Int) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 2962) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2963) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__2 ← (( do (Shift_C w__0 SRType_ASR shift_n w__1.C) ) : SailM ((BitVec 32) × (BitVec 1))
    )
  let (tup__0, tup__1) := (w__2 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__3 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with Z := (IsZeroBit result) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with C := carry })
  else (pure (()))


/-- Type quantifiers: d : Nat, m : Nat, n : Nat, k_setflags : Bool, List.elem n
  [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem m [0, 1, 2, 3, 4, 5, 6, 7] ∧ List.elem d [0, 1, 2, 3, 4, 5, 6, 7] -/
def execute_aarch32_instrs_ASR_r_Op_A_txt (d : Nat) (m : Nat) (n : Nat) (setflags : Bool) : SailM Unit := do
  let carry ← (( do (undefined_bitvector_at (← occLabel 2965) 1) ) : SailM (BitVec 1) )
  let result ← (( do (undefined_bitvector_at (← occLabel 2966) 32) ) : SailM (BitVec 32) )
  let w__0 ← (( do (R_read m) ) : SailM (BitVec 32) )
  let shift_n : Int := (BitVec.toNat (Sail.BitVec.extractLsb w__0 7 0))
  let w__1 ← (( do (R_read n) ) : SailM (BitVec 32) )
  let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
  let w__3 ← (( do (Shift_C w__1 SRType_ASR shift_n w__2.C) ) : SailM ((BitVec 32) × (BitVec 1))
    )
  let (tup__0, tup__1) := (w__3 : ((BitVec 32) × (BitVec 1)))
  let result : (BitVec 32) := tup__0
  let carry : (BitVec 1) := tup__1
  (R_set d result)
  if (setflags : Bool)
  then
    (do
      let w__4 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__4 with N := (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access result 31)])) }
      let w__5 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__5 with Z := (IsZeroBit result) }
      let w__6 ← (( do readReg PSTATE ) : SailM ProcState )
      writeReg PSTATE { w__6 with C := carry })
  else (pure (()))


end ArmFull.Functions
