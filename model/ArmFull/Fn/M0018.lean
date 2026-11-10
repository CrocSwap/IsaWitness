import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork

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

def num_of_Unpredictable (arg_ : Unpredictable) : Int :=
  match arg_ with
  | .Unpredictable_VMSR => 0
  | .Unpredictable_WBOVERLAPLD => 1
  | .Unpredictable_WBOVERLAPST => 2
  | .Unpredictable_LDPOVERLAP => 3
  | .Unpredictable_BASEOVERLAP => 4
  | .Unpredictable_DATAOVERLAP => 5
  | .Unpredictable_DEVPAGE2 => 6
  | .Unpredictable_INSTRDEVICE => 7
  | .Unpredictable_RESCPACR => 8
  | .Unpredictable_RESMAIR => 9
  | .Unpredictable_S1CTAGGED => 10
  | .Unpredictable_S2RESMEMATTR => 11
  | .Unpredictable_RESTEXCB => 12
  | .Unpredictable_RESPRRR => 13
  | .Unpredictable_RESDACR => 14
  | .Unpredictable_RESVTCRS => 15
  | .Unpredictable_RESTnSZ => 16
  | .Unpredictable_RESTCF => 17
  | .Unpredictable_DEVICETAGSTORE => 18
  | .Unpredictable_OORTnSZ => 19
  | .Unpredictable_LARGEIPA => 20
  | .Unpredictable_ESRCONDPASS => 21
  | .Unpredictable_ILZEROIT => 22
  | .Unpredictable_ILZEROT => 23
  | .Unpredictable_BPVECTORCATCHPRI => 24
  | .Unpredictable_VCMATCHHALF => 25
  | .Unpredictable_VCMATCHDAPA => 26
  | .Unpredictable_WPMASKANDBAS => 27
  | .Unpredictable_WPBASCONTIGUOUS => 28
  | .Unpredictable_RESWPMASK => 29
  | .Unpredictable_WPMASKEDBITS => 30
  | .Unpredictable_RESBPWPCTRL => 31
  | .Unpredictable_BPNOTIMPL => 32
  | .Unpredictable_RESBPTYPE => 33
  | .Unpredictable_RESMDSELR => 34
  | .Unpredictable_BPNOTCTXCMP => 35
  | .Unpredictable_BPMATCHHALF => 36
  | .Unpredictable_BPMISMATCHHALF => 37
  | .Unpredictable_BPLINKINGDISABLED => 38
  | .Unpredictable_RESBPMASK => 39
  | .Unpredictable_BPMASK => 40
  | .Unpredictable_BPMASKEDBITS => 41
  | .Unpredictable_BPLINKEDADDRMATCH => 42
  | .Unpredictable_RESTARTALIGNPC => 43
  | .Unpredictable_RESTARTZEROUPPERPC => 44
  | .Unpredictable_ZEROUPPER => 45
  | .Unpredictable_ERETZEROUPPERPC => 46
  | .Unpredictable_A32FORCEALIGNPC => 47
  | .Unpredictable_SMD => 48
  | .Unpredictable_NONFAULT => 49
  | .Unpredictable_SVEZEROUPPER => 50
  | .Unpredictable_SVELDNFDATA => 51
  | .Unpredictable_SVELDNFZERO => 52
  | .Unpredictable_CHECKSPNONEACTIVE => 53
  | .Unpredictable_SMEZEROUPPER => 54
  | .Unpredictable_NVNV1 => 55
  | .Unpredictable_Shareability => 56
  | .Unpredictable_AFUPDATE => 57
  | .Unpredictable_DBUPDATE => 58
  | .Unpredictable_IESBinDebug => 59
  | .Unpredictable_BADPMSFCR => 60
  | .Unpredictable_ZEROBTYPE => 61
  | .Unpredictable_EL2TIMESTAMP => 62
  | .Unpredictable_EL1TIMESTAMP => 63
  | .Unpredictable_RESERVEDNSxB => 64
  | .Unpredictable_WFxTDEBUG => 65
  | .Unpredictable_LS64UNSUPPORTED => 66
  | .Unpredictable_MISALIGNEDATOMIC => 67
  | .Unpredictable_CLEARERRITEZERO => 68
  | .Unpredictable_ALUEXCEPTIONRETURN => 69
  | .Unpredictable_IGNORETRAPINDEBUG => 70
  | .Unpredictable_DBGxVR_RESS => 71
  | .Unpredictable_PMUEVENTCOUNTER => 72
  | .Unpredictable_PMSCR_PCT => 73
  | .Unpredictable_CounterReservedForEL2 => 74
  | .Unpredictable_BRBFILTRATE => 75
  | .Unpredictable_MOPSOVERLAP31 => 76
  | .Unpredictable_STOREONLYTAGCHECKEDCAS => 77
  | .Unpredictable_RESTC => 78


def undefined_Constraint (ℓ : ChoiceLabel) (_ : Unit) : SailM Constraint := do
  (internal_pick_at (ℓ.child 0)
    [Constraint_NONE, Constraint_UNKNOWN, Constraint_UNDEF, Constraint_UNDEFEL0, Constraint_NOP, Constraint_TRUE, Constraint_FALSE, Constraint_DISABLED, Constraint_UNCOND, Constraint_COND, Constraint_ADDITIONAL_DECODE, Constraint_WBSUPPRESS, Constraint_FAULT, Constraint_LIMITED_ATOMICITY, Constraint_NVNV1_00, Constraint_NVNV1_01, Constraint_NVNV1_11, Constraint_EL1TIMESTAMP, Constraint_EL2TIMESTAMP, Constraint_OSH, Constraint_ISH, Constraint_NSH, Constraint_NC, Constraint_WT, Constraint_WB, Constraint_FORCE, Constraint_FORCENOSLCHECK, Constraint_MAPTOALLOCATED, Constraint_PMSCR_PCT_VIRT])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 28 -/
def Constraint_of_num (arg_ : Nat) : Constraint :=
  match arg_ with
  | 0 => Constraint_NONE
  | 1 => Constraint_UNKNOWN
  | 2 => Constraint_UNDEF
  | 3 => Constraint_UNDEFEL0
  | 4 => Constraint_NOP
  | 5 => Constraint_TRUE
  | 6 => Constraint_FALSE
  | 7 => Constraint_DISABLED
  | 8 => Constraint_UNCOND
  | 9 => Constraint_COND
  | 10 => Constraint_ADDITIONAL_DECODE
  | 11 => Constraint_WBSUPPRESS
  | 12 => Constraint_FAULT
  | 13 => Constraint_LIMITED_ATOMICITY
  | 14 => Constraint_NVNV1_00
  | 15 => Constraint_NVNV1_01
  | 16 => Constraint_NVNV1_11
  | 17 => Constraint_EL1TIMESTAMP
  | 18 => Constraint_EL2TIMESTAMP
  | 19 => Constraint_OSH
  | 20 => Constraint_ISH
  | 21 => Constraint_NSH
  | 22 => Constraint_NC
  | 23 => Constraint_WT
  | 24 => Constraint_WB
  | 25 => Constraint_FORCE
  | 26 => Constraint_FORCENOSLCHECK
  | 27 => Constraint_MAPTOALLOCATED
  | _ => Constraint_PMSCR_PCT_VIRT


def num_of_Constraint (arg_ : Constraint) : Int :=
  match arg_ with
  | .Constraint_NONE => 0
  | .Constraint_UNKNOWN => 1
  | .Constraint_UNDEF => 2
  | .Constraint_UNDEFEL0 => 3
  | .Constraint_NOP => 4
  | .Constraint_TRUE => 5
  | .Constraint_FALSE => 6
  | .Constraint_DISABLED => 7
  | .Constraint_UNCOND => 8
  | .Constraint_COND => 9
  | .Constraint_ADDITIONAL_DECODE => 10
  | .Constraint_WBSUPPRESS => 11
  | .Constraint_FAULT => 12
  | .Constraint_LIMITED_ATOMICITY => 13
  | .Constraint_NVNV1_00 => 14
  | .Constraint_NVNV1_01 => 15
  | .Constraint_NVNV1_11 => 16
  | .Constraint_EL1TIMESTAMP => 17
  | .Constraint_EL2TIMESTAMP => 18
  | .Constraint_OSH => 19
  | .Constraint_ISH => 20
  | .Constraint_NSH => 21
  | .Constraint_NC => 22
  | .Constraint_WT => 23
  | .Constraint_WB => 24
  | .Constraint_FORCE => 25
  | .Constraint_FORCENOSLCHECK => 26
  | .Constraint_MAPTOALLOCATED => 27
  | .Constraint_PMSCR_PCT_VIRT => 28


def undefined_RestrictType (ℓ : ChoiceLabel) (_ : Unit) : SailM RestrictType := do
  (internal_pick_at (ℓ.child 0)
    [RestrictType_DataValue, RestrictType_ControlFlow, RestrictType_CachePrefetch, RestrictType_Other])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 3 -/
def RestrictType_of_num (arg_ : Nat) : RestrictType :=
  match arg_ with
  | 0 => RestrictType_DataValue
  | 1 => RestrictType_ControlFlow
  | 2 => RestrictType_CachePrefetch
  | _ => RestrictType_Other


def num_of_RestrictType (arg_ : RestrictType) : Int :=
  match arg_ with
  | .RestrictType_DataValue => 0
  | .RestrictType_ControlFlow => 1
  | .RestrictType_CachePrefetch => 2
  | .RestrictType_Other => 3


def undefined_FPExc (ℓ : ChoiceLabel) (_ : Unit) : SailM FPExc := do
  (internal_pick_at (ℓ.child 0)
    [FPExc_InvalidOp, FPExc_DivideByZero, FPExc_Overflow, FPExc_Underflow, FPExc_Inexact, FPExc_InputDenorm])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def FPExc_of_num (arg_ : Nat) : FPExc :=
  match arg_ with
  | 0 => FPExc_InvalidOp
  | 1 => FPExc_DivideByZero
  | 2 => FPExc_Overflow
  | 3 => FPExc_Underflow
  | 4 => FPExc_Inexact
  | _ => FPExc_InputDenorm


def num_of_FPExc (arg_ : FPExc) : Int :=
  match arg_ with
  | .FPExc_InvalidOp => 0
  | .FPExc_DivideByZero => 1
  | .FPExc_Overflow => 2
  | .FPExc_Underflow => 3
  | .FPExc_Inexact => 4
  | .FPExc_InputDenorm => 5


def undefined_FPRounding (ℓ : ChoiceLabel) (_ : Unit) : SailM FPRounding := do
  (internal_pick_at (ℓ.child 0)
    [FPRounding_TIEEVEN, FPRounding_POSINF, FPRounding_NEGINF, FPRounding_ZERO, FPRounding_TIEAWAY, FPRounding_ODD])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def FPRounding_of_num (arg_ : Nat) : FPRounding :=
  match arg_ with
  | 0 => FPRounding_TIEEVEN
  | 1 => FPRounding_POSINF
  | 2 => FPRounding_NEGINF
  | 3 => FPRounding_ZERO
  | 4 => FPRounding_TIEAWAY
  | _ => FPRounding_ODD


def num_of_FPRounding (arg_ : FPRounding) : Int :=
  match arg_ with
  | .FPRounding_TIEEVEN => 0
  | .FPRounding_POSINF => 1
  | .FPRounding_NEGINF => 2
  | .FPRounding_ZERO => 3
  | .FPRounding_TIEAWAY => 4
  | .FPRounding_ODD => 5


def undefined_FPType (ℓ : ChoiceLabel) (_ : Unit) : SailM FPType := do
  (internal_pick_at (ℓ.child 0)
    [FPType_Zero, FPType_Denormal, FPType_Nonzero, FPType_Infinity, FPType_QNaN, FPType_SNaN])


/-- Type quantifiers: arg_ : Nat, 0 ≤ arg_ ∧ arg_ ≤ 5 -/
def FPType_of_num (arg_ : Nat) : FPType :=
  match arg_ with
  | 0 => FPType_Zero
  | 1 => FPType_Denormal
  | 2 => FPType_Nonzero
  | 3 => FPType_Infinity
  | 4 => FPType_QNaN
  | _ => FPType_SNaN


def num_of_FPType (arg_ : FPType) : Int :=
  match arg_ with
  | .FPType_Zero => 0
  | .FPType_Denormal => 1
  | .FPType_Nonzero => 2
  | .FPType_Infinity => 3
  | .FPType_QNaN => 4
  | .FPType_SNaN => 5


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 30 -/
def read_gpr (n : Nat) : SailM (BitVec 64) := do
  match n with
  | 0 =>
    (do
      readReg R0)
  | 1 =>
    (do
      readReg R1)
  | 2 =>
    (do
      readReg R2)
  | 3 =>
    (do
      readReg R3)
  | 4 =>
    (do
      readReg R4)
  | 5 =>
    (do
      readReg R5)
  | 6 =>
    (do
      readReg R6)
  | 7 =>
    (do
      readReg R7)
  | 8 =>
    (do
      readReg R8)
  | 9 =>
    (do
      readReg R9)
  | 10 =>
    (do
      readReg R10)
  | 11 =>
    (do
      readReg R11)
  | 12 =>
    (do
      readReg R12)
  | 13 =>
    (do
      readReg R13)
  | 14 =>
    (do
      readReg R14)
  | 15 =>
    (do
      readReg R15)
  | 16 =>
    (do
      readReg R16)
  | 17 =>
    (do
      readReg R17)
  | 18 =>
    (do
      readReg R18)
  | 19 =>
    (do
      readReg R19)
  | 20 =>
    (do
      readReg R20)
  | 21 =>
    (do
      readReg R21)
  | 22 =>
    (do
      readReg R22)
  | 23 =>
    (do
      readReg R23)
  | 24 =>
    (do
      readReg R24)
  | 25 =>
    (do
      readReg R25)
  | 26 =>
    (do
      readReg R26)
  | 27 =>
    (do
      readReg R27)
  | 28 =>
    (do
      readReg R28)
  | 29 =>
    (do
      readReg R29)
  | _ =>
    (do
      readReg R30)


/-- Type quantifiers: n : Nat, lo : Nat, hi : Nat, 0 ≤ n ∧ n ≤ 30 ∧
  0 ≤ lo ∧ lo ≤ hi ∧ hi ≤ 63 -/
def write_gpr_bits (n : Nat) (hi : Nat) (lo : Nat) (v : (BitVec (hi - lo + 1))) : SailM Unit := do
  match n with
  | 0 =>
    (do
      let w__0 ← (( do readReg R0 ) : SailM (BitVec 64) )
      writeReg R0 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__0 hi lo
        (Sail.BitVec.castWidth v))))
  | 1 =>
    (do
      let w__1 ← (( do readReg R1 ) : SailM (BitVec 64) )
      writeReg R1 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__1 hi lo
        (Sail.BitVec.castWidth v))))
  | 2 =>
    (do
      let w__2 ← (( do readReg R2 ) : SailM (BitVec 64) )
      writeReg R2 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__2 hi lo
        (Sail.BitVec.castWidth v))))
  | 3 =>
    (do
      let w__3 ← (( do readReg R3 ) : SailM (BitVec 64) )
      writeReg R3 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__3 hi lo
        (Sail.BitVec.castWidth v))))
  | 4 =>
    (do
      let w__4 ← (( do readReg R4 ) : SailM (BitVec 64) )
      writeReg R4 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__4 hi lo
        (Sail.BitVec.castWidth v))))
  | 5 =>
    (do
      let w__5 ← (( do readReg R5 ) : SailM (BitVec 64) )
      writeReg R5 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__5 hi lo
        (Sail.BitVec.castWidth v))))
  | 6 =>
    (do
      let w__6 ← (( do readReg R6 ) : SailM (BitVec 64) )
      writeReg R6 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__6 hi lo
        (Sail.BitVec.castWidth v))))
  | 7 =>
    (do
      let w__7 ← (( do readReg R7 ) : SailM (BitVec 64) )
      writeReg R7 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__7 hi lo
        (Sail.BitVec.castWidth v))))
  | 8 =>
    (do
      let w__8 ← (( do readReg R8 ) : SailM (BitVec 64) )
      writeReg R8 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__8 hi lo
        (Sail.BitVec.castWidth v))))
  | 9 =>
    (do
      let w__9 ← (( do readReg R9 ) : SailM (BitVec 64) )
      writeReg R9 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__9 hi lo
        (Sail.BitVec.castWidth v))))
  | 10 =>
    (do
      let w__10 ← (( do readReg R10 ) : SailM (BitVec 64) )
      writeReg R10 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__10 hi lo
        (Sail.BitVec.castWidth v))))
  | 11 =>
    (do
      let w__11 ← (( do readReg R11 ) : SailM (BitVec 64) )
      writeReg R11 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__11 hi lo
        (Sail.BitVec.castWidth v))))
  | 12 =>
    (do
      let w__12 ← (( do readReg R12 ) : SailM (BitVec 64) )
      writeReg R12 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__12 hi lo
        (Sail.BitVec.castWidth v))))
  | 13 =>
    (do
      let w__13 ← (( do readReg R13 ) : SailM (BitVec 64) )
      writeReg R13 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__13 hi lo
        (Sail.BitVec.castWidth v))))
  | 14 =>
    (do
      let w__14 ← (( do readReg R14 ) : SailM (BitVec 64) )
      writeReg R14 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__14 hi lo
        (Sail.BitVec.castWidth v))))
  | 15 =>
    (do
      let w__15 ← (( do readReg R15 ) : SailM (BitVec 64) )
      writeReg R15 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__15 hi lo
        (Sail.BitVec.castWidth v))))
  | 16 =>
    (do
      let w__16 ← (( do readReg R16 ) : SailM (BitVec 64) )
      writeReg R16 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__16 hi lo
        (Sail.BitVec.castWidth v))))
  | 17 =>
    (do
      let w__17 ← (( do readReg R17 ) : SailM (BitVec 64) )
      writeReg R17 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__17 hi lo
        (Sail.BitVec.castWidth v))))
  | 18 =>
    (do
      let w__18 ← (( do readReg R18 ) : SailM (BitVec 64) )
      writeReg R18 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__18 hi lo
        (Sail.BitVec.castWidth v))))
  | 19 =>
    (do
      let w__19 ← (( do readReg R19 ) : SailM (BitVec 64) )
      writeReg R19 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__19 hi lo
        (Sail.BitVec.castWidth v))))
  | 20 =>
    (do
      let w__20 ← (( do readReg R20 ) : SailM (BitVec 64) )
      writeReg R20 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__20 hi lo
        (Sail.BitVec.castWidth v))))
  | 21 =>
    (do
      let w__21 ← (( do readReg R21 ) : SailM (BitVec 64) )
      writeReg R21 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__21 hi lo
        (Sail.BitVec.castWidth v))))
  | 22 =>
    (do
      let w__22 ← (( do readReg R22 ) : SailM (BitVec 64) )
      writeReg R22 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__22 hi lo
        (Sail.BitVec.castWidth v))))
  | 23 =>
    (do
      let w__23 ← (( do readReg R23 ) : SailM (BitVec 64) )
      writeReg R23 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__23 hi lo
        (Sail.BitVec.castWidth v))))
  | 24 =>
    (do
      let w__24 ← (( do readReg R24 ) : SailM (BitVec 64) )
      writeReg R24 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__24 hi lo
        (Sail.BitVec.castWidth v))))
  | 25 =>
    (do
      let w__25 ← (( do readReg R25 ) : SailM (BitVec 64) )
      writeReg R25 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__25 hi lo
        (Sail.BitVec.castWidth v))))
  | 26 =>
    (do
      let w__26 ← (( do readReg R26 ) : SailM (BitVec 64) )
      writeReg R26 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__26 hi lo
        (Sail.BitVec.castWidth v))))
  | 27 =>
    (do
      let w__27 ← (( do readReg R27 ) : SailM (BitVec 64) )
      writeReg R27 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__27 hi lo
        (Sail.BitVec.castWidth v))))
  | 28 =>
    (do
      let w__28 ← (( do readReg R28 ) : SailM (BitVec 64) )
      writeReg R28 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__28 hi lo
        (Sail.BitVec.castWidth v))))
  | 29 =>
    (do
      let w__29 ← (( do readReg R29 ) : SailM (BitVec 64) )
      writeReg R29 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__29 hi lo
        (Sail.BitVec.castWidth v))))
  | _ =>
    (do
      let w__30 ← (( do readReg R30 ) : SailM (BitVec 64) )
      writeReg R30 (Sail.BitVec.castWidth (m := 64) (Sail.BitVec.updateSubrange w__30 hi lo
        (Sail.BitVec.castWidth v))))


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 30 -/
def write_gpr (n : Nat) (v : (BitVec 64)) : SailM Unit := do
  match n with
  | 0 =>
    (do
      writeReg R0 v)
  | 1 =>
    (do
      writeReg R1 v)
  | 2 =>
    (do
      writeReg R2 v)
  | 3 =>
    (do
      writeReg R3 v)
  | 4 =>
    (do
      writeReg R4 v)
  | 5 =>
    (do
      writeReg R5 v)
  | 6 =>
    (do
      writeReg R6 v)
  | 7 =>
    (do
      writeReg R7 v)
  | 8 =>
    (do
      writeReg R8 v)
  | 9 =>
    (do
      writeReg R9 v)
  | 10 =>
    (do
      writeReg R10 v)
  | 11 =>
    (do
      writeReg R11 v)
  | 12 =>
    (do
      writeReg R12 v)
  | 13 =>
    (do
      writeReg R13 v)
  | 14 =>
    (do
      writeReg R14 v)
  | 15 =>
    (do
      writeReg R15 v)
  | 16 =>
    (do
      writeReg R16 v)
  | 17 =>
    (do
      writeReg R17 v)
  | 18 =>
    (do
      writeReg R18 v)
  | 19 =>
    (do
      writeReg R19 v)
  | 20 =>
    (do
      writeReg R20 v)
  | 21 =>
    (do
      writeReg R21 v)
  | 22 =>
    (do
      writeReg R22 v)
  | 23 =>
    (do
      writeReg R23 v)
  | 24 =>
    (do
      writeReg R24 v)
  | 25 =>
    (do
      writeReg R25 v)
  | 26 =>
    (do
      writeReg R26 v)
  | 27 =>
    (do
      writeReg R27 v)
  | 28 =>
    (do
      writeReg R28 v)
  | 29 =>
    (do
      writeReg R29 v)
  | _ =>
    (do
      writeReg R30 v)


/-- Type quantifiers: n : Nat, 0 ≤ n ∧ n ≤ 30 -/
def register_ref (n : Nat) : (RegisterRef (BitVec 64)) :=
  match n with
  | 0 => Register.R0
  | 1 => Register.R1
  | 2 => Register.R2
  | 3 => Register.R3
  | 4 => Register.R4
  | 5 => Register.R5
  | 6 => Register.R6
  | 7 => Register.R7
  | 8 => Register.R8
  | 9 => Register.R9
  | 10 => Register.R10
  | 11 => Register.R11
  | 12 => Register.R12
  | 13 => Register.R13
  | 14 => Register.R14
  | 15 => Register.R15
  | 16 => Register.R16
  | 17 => Register.R17
  | 18 => Register.R18
  | 19 => Register.R19
  | 20 => Register.R20
  | 21 => Register.R21
  | 22 => Register.R22
  | 23 => Register.R23
  | 24 => Register.R24
  | 25 => Register.R25
  | 26 => Register.R26
  | 27 => Register.R27
  | 28 => Register.R28
  | 29 => Register.R29
  | _ => Register.R30


end ArmFull.Functions
