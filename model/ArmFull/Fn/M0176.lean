import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0010
import ArmFull.Fn.M0034
import ArmFull.Fn.M0043
import ArmFull.Fn.M0047
import ArmFull.Fn.M0056
import ArmFull.Fn.M0059
import ArmFull.Fn.M0060
import ArmFull.Fn.M0061
import ArmFull.Fn.M0092
import ArmFull.Fn.M0166

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

def __set_SCTLR_S (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  let w__0 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  writeReg SCTLR_S (Sail.BitVec.updateSubrange w__0 4 0 (BitVec.slice r 0 5))
  let w__1 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  writeReg SCTLR_S (BitVec.update w__1 6 (Bit (BitVec.slice r 6 1)))
  let w__2 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
  writeReg SCTLR_S (Sail.BitVec.updateSubrange w__2 31 8 (BitVec.slice r 8 24))
  let w__3 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  if ((! (! w__3)) : Bool)
  then
    (do
      let w__4 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
      writeReg SCTLR_S (Sail.BitVec.updateSubrange w__4 7 7 (_get_SCTLR_Type_ITD r)))
  else (pure (()))
  let w__5 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  if ((! (! w__5)) : Bool)
  then
    (do
      let w__6 ← (( do readReg SCTLR_S ) : SailM (BitVec 32) )
      writeReg SCTLR_S (Sail.BitVec.updateSubrange w__6 5 5 (_get_SCTLR_Type_CP15BEN r)))
  else (pure (()))


def __set_SCTLR_NS (value_name : (BitVec 32)) : SailM Unit := do
  let r : SCTLR_Type := value_name
  let w__0 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
  (SCTLR_NS_write (Mk_SCTLR_Type (set_slice 5 w__0 0 (BitVec.slice r 0 5))))
  let w__1 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
  (SCTLR_NS_write (Mk_SCTLR_Type (set_slice 1 w__1 6 (BitVec.slice r 6 1))))
  let w__2 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
  (SCTLR_NS_write (Mk_SCTLR_Type (set_slice 24 w__2 8 (BitVec.slice r 8 24))))
  let w__3 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  if ((! (! w__3)) : Bool)
  then
    (do
      let w__4 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
      (SCTLR_NS_write (_update_SCTLR_Type_ITD w__4 (_get_SCTLR_Type_ITD r))))
  else (pure (()))
  let w__5 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  if ((! (! w__5)) : Bool)
  then
    (do
      let w__6 ← (( do (SCTLR_NS_read ()) ) : SailM (BitVec 32) )
      (SCTLR_NS_write (_update_SCTLR_Type_CP15BEN w__6 (_get_SCTLR_Type_CP15BEN r))))
  else (pure (()))


def __get_SCTLR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : SCTLR_EL1_Type := value_name
  let tmp : SCTLR_EL1_Type :=
    (Mk_SCTLR_EL1_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
          (Sail.BitVec.zeroExtend 0x400020000#36 64)))))
  let w__0 ← (( do (__IMPDEF_boolean "IMPLEMENTED_CP15BEN") ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_SCTLR_EL1_Type
        ((Sail.BitVec.castWidth (m := 64) (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
              (Sail.BitVec.zeroExtend 0x0#4 64))))) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
            0x20#8 64))))
    else tmp
  let w__1 ← (( do (__IMPDEF_boolean "IMPLEMENTED_ITD") ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__1) : Bool)
    then
      (Mk_SCTLR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80#8 64)))))
    else tmp
  (pure (tmp))


def __get_FPEXC32_EL2 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : FPEXC32_EL2_Type := value_name
  let w__0 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Invalid Operation floating-point exceptions") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_FPEXC32_EL2_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1#4 64)))))
    else tmp
  let w__1 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Divide by Zero floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 64) :=
    if ((! w__1) : Bool)
    then
      (Mk_FPEXC32_EL2_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x2#4 64)))))
    else tmp
  let w__2 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Overflow floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__2) : Bool)
    then
      (Mk_FPEXC32_EL2_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x4#4 64)))))
    else tmp
  let w__3 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Underflow floating-point exceptions") ) : SailM Bool
    )
  let tmp : (BitVec 64) :=
    if ((! w__3) : Bool)
    then
      (Mk_FPEXC32_EL2_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8#4 64)))))
    else tmp
  let w__4 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of Inexact floating-point exceptions")
    ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__4) : Bool)
    then
      (Mk_FPEXC32_EL2_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else tmp
  let tmp : FPEXC32_EL2_Type :=
    (Mk_FPEXC32_EL2_Type
      ((tmp &&& (Complement.complement 0xFFFFFFFF9BFFF860#64)) ||| (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.zeroExtend
          0x700#12 64))))
  let w__5 ← (( do
    (__IMPDEF_boolean "IMPLEMENTED_trapping of Input Denormal floating-point exceptions") ) : SailM
    Bool )
  let tmp : (BitVec 64) :=
    if ((! w__5) : Bool)
    then
      (Mk_FPEXC32_EL2_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80#8 64)))))
    else tmp
  let w__6 ← (( do (__IMPDEF_boolean "IMPLEMENTED_trapping of floating-point exceptions") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__6) : Bool)
    then
      (Mk_FPEXC32_EL2_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x4000000#28 64)))))
    else tmp
  (pure (tmp))


def __get_PMCR_EL0 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMCR_EL0_Type := value_name
  let tmp : PMCR_EL0_Type :=
    (Mk_PMCR_EL0_Type (tmp &&& (Complement.complement 0xFFFFFFFE00000506#64)))
  let w__0 ← (( do (__IMPDEF_boolean "the implementation includes a PMU event export bus") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_PMCR_EL0_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else tmp
  let w__1 ← (( do (IsFeatureImplemented FEAT_PMUv3p7) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! (! w__1)) : Bool)
    then
      (Mk_PMCR_EL0_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0xFF000000#32 64)))))
    else tmp
  (pure (tmp))


def __get_PMSDSFR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMSDSFR_EL1_Type := value_name
  let w__0 ← (( do (__IMPDEF_boolean "filtering on Data Source [m] is supported") ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then (Mk_PMSDSFR_EL1_Type (tmp &&& (Complement.complement 0xFFFFFFFFFFFFFFFF#64)))
    else tmp
  (pure (tmp))


def __get_PMSEVFR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMSEVFR_EL1_Type := value_name
  let tmp : PMSEVFR_EL1_Type :=
    (Mk_PMSEVFR_EL1_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
          (Sail.BitVec.zeroExtend 0xFFFF00000001#48 64)))))
  let w__2 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then (pure true)
    else
      (do
        (__IMPDEF_boolean "filtering on event 2 is optionally supported")) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__2) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x4#4 64)))))
    else tmp
  let w__5 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then (pure true)
    else
      (do
        (__IMPDEF_boolean "filtering on event 4 is optionally supported")) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__5) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else tmp
  let w__6 ← (( do (IsFeatureImplemented FEAT_SPEv1p2) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__6) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x40#8 64)))))
    else tmp
  let w__11 ← (( do
    if ((← do
         if ((← do
              (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
         then (pure true)
         else
           (do
             (__IMPDEF_boolean "filtering on event 8 is optionally supported"))) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 8 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__11) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100#12 64)))))
    else tmp
  let w__16 ← (( do
    if ((← do
         if ((← do
              (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
         then (pure true)
         else
           (do
             (__IMPDEF_boolean "filtering on event 9 is optionally supported"))) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 9 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__16) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200#12 64)))))
    else tmp
  let w__21 ← (( do
    if ((← do
         if ((← do
              (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
         then (pure true)
         else
           (do
             (__IMPDEF_boolean "filtering on event 10 is optionally supported"))) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 10 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__21) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400#12 64)))))
    else tmp
  let w__22 ← (( do (IsFeatureImplemented FEAT_SPEv1p1) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__22) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800#12 64)))))
    else tmp
  let w__23 ← (( do (IsFeatureImplemented FEAT_TME) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__23) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10000#20 64)))))
    else tmp
  let w__26 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p1)) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_SVE))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__26) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x60000#20 64)))))
    else tmp
  let w__29 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 19 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__29) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80000#20 64)))))
    else tmp
  let w__32 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 20 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__32) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100000#24 64)))))
    else tmp
  let w__35 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 21 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__35) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200000#24 64)))))
    else tmp
  let w__38 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 22 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__38) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400000#24 64)))))
    else tmp
  let w__41 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 23 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__41) : Bool)
    then
      (Mk_PMSEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800000#24 64)))))
    else tmp
  (pure (tmp))


def __get_PMSNEVFR_EL1 (value_name : (BitVec 64)) : SailM (BitVec 64) := do
  let tmp : PMSNEVFR_EL1_Type := value_name
  let tmp : PMSNEVFR_EL1_Type :=
    (Mk_PMSNEVFR_EL1_Type
      (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
          (Sail.BitVec.zeroExtend 0xFFFF00000001#48 64)))))
  let w__0 ← (( do (__IMPDEF_boolean "the PE supports sampling of speculative instructions") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__0) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x2#4 64)))))
    else tmp
  let w__3 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then (pure true)
    else
      (do
        (__IMPDEF_boolean "filtering on event 2 is optionally supported")) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__3) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x4#4 64)))))
    else tmp
  let w__6 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then (pure true)
    else
      (do
        (__IMPDEF_boolean "filtering on event 4 is optionally supported")) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__6) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10#8 64)))))
    else tmp
  let w__11 ← (( do
    if ((← do
         if ((← do
              (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
         then (pure true)
         else
           (do
             (__IMPDEF_boolean "filtering on event 8 is optionally supported"))) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 8 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__11) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100#12 64)))))
    else tmp
  let w__16 ← (( do
    if ((← do
         if ((← do
              (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
         then (pure true)
         else
           (do
             (__IMPDEF_boolean "filtering on event 9 is optionally supported"))) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 9 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__16) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200#12 64)))))
    else tmp
  let w__21 ← (( do
    if ((← do
         if ((← do
              (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
         then (pure true)
         else
           (do
             (__IMPDEF_boolean "filtering on event 10 is optionally supported"))) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 10 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__21) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400#12 64)))))
    else tmp
  let w__22 ← (( do (IsFeatureImplemented FEAT_SPEv1p1) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__22) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800#12 64)))))
    else tmp
  let w__23 ← (( do
    (__IMPDEF_boolean "event 12 is not implemented, or filtering on event 12 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__23 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1000#16 64)))))
    else tmp
  let w__24 ← (( do
    (__IMPDEF_boolean "event 13 is not implemented, or filtering on event 13 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__24 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x2000#16 64)))))
    else tmp
  let w__25 ← (( do
    (__IMPDEF_boolean "event 14 is not implemented, or filtering on event 14 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__25 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x4000#16 64)))))
    else tmp
  let w__26 ← (( do
    (__IMPDEF_boolean "event 15 is not implemented, or filtering on event 15 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__26 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8000#16 64)))))
    else tmp
  let w__27 ← (( do (IsFeatureImplemented FEAT_TME) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__27) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10000#20 64)))))
    else tmp
  let w__30 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SVE)) : Bool)
    then
      (do
        (IsFeatureImplemented FEAT_SPEv1p1))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__30) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x60000#20 64)))))
    else tmp
  let w__33 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 19 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__33) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80000#20 64)))))
    else tmp
  let w__36 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 20 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__36) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100000#24 64)))))
    else tmp
  let w__39 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 21 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__39) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200000#24 64)))))
    else tmp
  let w__42 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 22 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__42) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400000#24 64)))))
    else tmp
  let w__45 ← (( do
    if ((← do
         (IsFeatureImplemented FEAT_SPEv1p4)) : Bool)
    then
      (do
        (__IMPDEF_boolean "event 23 is implemented"))
    else (pure false) ) : SailM Bool )
  let tmp : (BitVec 64) :=
    if ((! w__45) : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800000#24 64)))))
    else tmp
  let w__46 ← (( do
    (__IMPDEF_boolean "event 24 is not implemented, or filtering on event 24 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__46 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1000000#28 64)))))
    else tmp
  let w__47 ← (( do
    (__IMPDEF_boolean "event 25 is not implemented, or filtering on event 25 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__47 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x2000000#28 64)))))
    else tmp
  let w__48 ← (( do
    (__IMPDEF_boolean "event 26 is not implemented, or filtering on event 26 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__48 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x4000000#28 64)))))
    else tmp
  let w__49 ← (( do
    (__IMPDEF_boolean "event 27 is not implemented, or filtering on event 27 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__49 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8000000#28 64)))))
    else tmp
  let w__50 ← (( do
    (__IMPDEF_boolean "event 28 is not implemented, or filtering on event 28 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__50 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10000000#32 64)))))
    else tmp
  let w__51 ← (( do
    (__IMPDEF_boolean "event 29 is not implemented, or filtering on event 29 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__51 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x20000000#32 64)))))
    else tmp
  let w__52 ← (( do
    (__IMPDEF_boolean "event 30 is not implemented, or filtering on event 30 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__52 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x40000000#32 64)))))
    else tmp
  let w__53 ← (( do
    (__IMPDEF_boolean "event 31 is not implemented, or filtering on event 31 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__53 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80000000#32 64)))))
    else tmp
  let w__54 ← (( do
    (__IMPDEF_boolean "event 48 is not implemented, or filtering on event 48 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__54 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x1000000000000#52 64)))))
    else tmp
  let w__55 ← (( do
    (__IMPDEF_boolean "event 49 is not implemented, or filtering on event 49 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__55 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x2000000000000#52 64)))))
    else tmp
  let w__56 ← (( do
    (__IMPDEF_boolean "event 50 is not implemented, or filtering on event 50 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__56 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x4000000000000#52 64)))))
    else tmp
  let w__57 ← (( do
    (__IMPDEF_boolean "event 51 is not implemented, or filtering on event 51 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__57 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x8000000000000#52 64)))))
    else tmp
  let w__58 ← (( do
    (__IMPDEF_boolean "event 52 is not implemented, or filtering on event 52 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__58 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x10000000000000#56 64)))))
    else tmp
  let w__59 ← (( do
    (__IMPDEF_boolean "event 53 is not implemented, or filtering on event 53 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__59 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x20000000000000#56 64)))))
    else tmp
  let w__60 ← (( do
    (__IMPDEF_boolean "event 54 is not implemented, or filtering on event 54 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__60 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x40000000000000#56 64)))))
    else tmp
  let w__61 ← (( do
    (__IMPDEF_boolean "event 55 is not implemented, or filtering on event 55 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__61 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x80000000000000#56 64)))))
    else tmp
  let w__62 ← (( do
    (__IMPDEF_boolean "event 56 is not implemented, or filtering on event 56 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__62 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x100000000000000#60 64)))))
    else tmp
  let w__63 ← (( do
    (__IMPDEF_boolean "event 57 is not implemented, or filtering on event 57 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__63 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x200000000000000#60 64)))))
    else tmp
  let w__64 ← (( do
    (__IMPDEF_boolean "event 58 is not implemented, or filtering on event 58 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__64 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x400000000000000#60 64)))))
    else tmp
  let w__65 ← (( do
    (__IMPDEF_boolean "event 59 is not implemented, or filtering on event 59 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__65 : Bool)
    then
      (Mk_PMSNEVFR_EL1_Type
        (tmp &&& (Sail.BitVec.castWidth (m := 64) (Complement.complement
            (Sail.BitVec.zeroExtend 0x800000000000000#60 64)))))
    else tmp
  let w__66 ← (( do
    (__IMPDEF_boolean "event 60 is not implemented, or filtering on event 60 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__66 : Bool)
    then (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x1000000000000000#64)))
    else tmp
  let w__67 ← (( do
    (__IMPDEF_boolean "event 61 is not implemented, or filtering on event 61 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__67 : Bool)
    then (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x2000000000000000#64)))
    else tmp
  let w__68 ← (( do
    (__IMPDEF_boolean "event 62 is not implemented, or filtering on event 62 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__68 : Bool)
    then (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x4000000000000000#64)))
    else tmp
  let w__69 ← (( do
    (__IMPDEF_boolean "event 63 is not implemented, or filtering on event 63 is not supported") ) :
    SailM Bool )
  let tmp : (BitVec 64) :=
    if (w__69 : Bool)
    then (Mk_PMSNEVFR_EL1_Type (tmp &&& (Complement.complement 0x8000000000000000#64)))
    else tmp
  (pure (tmp))


end ArmFull.Functions
