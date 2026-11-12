import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0016
import ArmFull.Fn.M0024
import ArmFull.Fn.M0044
import ArmFull.Fn.M0049
import ArmFull.Fn.M0050

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

def PACSub (Tinput : (BitVec 64)) : SailM (BitVec 64) := do
  let Toutput ← (( do (undefined_bitvector_at (← occLabel 1284) 64) ) : SailM (BitVec 64) )
  let Toutput ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 15
    (do
      let mut loop_vars := Toutput
      for i in [loop_i_lower:loop_i_upper:1]i do
        let Toutput := loop_vars
        loop_vars :=
          match (BitVec.setWidth 4 (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb Tinput
            (Sail.Int.toNatChecked (((4 *i i) +i 3))) (Sail.Int.toNatChecked ((4 *i i)))))) with
          | 0b0000 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1011#4))
          | 0b0001 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0110#4))
          | 0b0010 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1000#4))
          | 0b0011 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1111#4))
          | 0b0100 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1100#4))
          | 0b0101 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0000#4))
          | 0b0110 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1001#4))
          | 0b0111 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1110#4))
          | 0b1000 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0011#4))
          | 0b1001 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0111#4))
          | 0b1010 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0100#4))
          | 0b1011 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0101#4))
          | 0b1100 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1101#4))
          | 0b1101 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0010#4))
          | 0b1110 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0001#4))
          | 0b1111 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1010#4))
          | _ => Toutput
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (pure (Toutput))


def PACSub1 (Tinput : (BitVec 64)) : SailM (BitVec 64) := do
  let Toutput ← (( do (undefined_bitvector_at (← occLabel 1285) 64) ) : SailM (BitVec 64) )
  let Toutput ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 15
    (do
      let mut loop_vars := Toutput
      for i in [loop_i_lower:loop_i_upper:1]i do
        let Toutput := loop_vars
        loop_vars :=
          match (BitVec.setWidth 4 (Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb Tinput
            (Sail.Int.toNatChecked (((4 *i i) +i 3))) (Sail.Int.toNatChecked ((4 *i i)))))) with
          | 0b0000 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1010#4))
          | 0b0001 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1101#4))
          | 0b0010 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1110#4))
          | 0b0011 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0110#4))
          | 0b0100 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1111#4))
          | 0b0101 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0111#4))
          | 0b0110 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0011#4))
          | 0b0111 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0101#4))
          | 0b1000 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1001#4))
          | 0b1001 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1000#4))
          | 0b1010 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0000#4))
          | 0b1011 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1100#4))
          | 0b1100 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b1011#4))
          | 0b1101 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0001#4))
          | 0b1110 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0010#4))
          | 0b1111 =>
            (Sail.BitVec.updateSubrange Toutput (Sail.Int.toNatChecked (((4 *i i) +i 3)))
              (Sail.Int.toNatChecked ((4 *i i))) (Sail.BitVec.castWidth 0b0100#4))
          | _ => Toutput
      (pure loop_vars)) ) : SailM (BitVec 64) )
  (pure (Toutput))


def TweakCellInvRot (incell_name : (BitVec 4)) : SailM (BitVec 4) := do
  let outcell ← (( do (undefined_bitvector_at (← occLabel 1286) 4) ) : SailM (BitVec 4) )
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 3
      (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 2)]))))
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 2
      (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 1)]))))
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 1
      (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 0)]))))
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 0
      (Bit
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 0)])) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              incell_name 3)])))))
  (pure (outcell))


def TweakCellRot (incell_name : (BitVec 4)) : SailM (BitVec 4) := do
  let outcell ← (( do (undefined_bitvector_at (← occLabel 1288) 4) ) : SailM (BitVec 4) )
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 3
      (Bit
        ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 0)])) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              incell_name 1)])))))
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 2
      (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 3)]))))
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 1
      (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 2)]))))
  let outcell : (BitVec 4) :=
    (BitVec.update outcell 0
      (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access incell_name 1)]))))
  (pure (outcell))


/-- Type quantifiers: n : Int, part : Int, width : Nat, width ≥ 0 -/
def Vpart_read (n : Int) (part : Int) (width : Nat) : SailM (BitVec width) := do
  ArmFull.assert ((n ≥b 0) && (n ≤b 31)) "sail-arm/v8_base.sail:22343.27-22343.28"
  ArmFull.assert ((part == 0) || (part == 1)) "sail-arm/v8_base.sail:22344.32-22344.33"
  if ((part == 0) : Bool)
  then
    (do
      ArmFull.assert (width <b 128) "sail-arm/v8_base.sail:22346.26-22346.27"
      ArmFull.assert (((((width == 8) || (width == 16)) || (width == 32)) || (width == 64)) || (width == 128)) "sail-arm/v8_base.sail:22347.57-22347.58"
      ((Sail.BitVec.castWidth ) <$> (V_read n width)))
  else
    (do
      ArmFull.assert ((width == 32) || (width == 64)) "sail-arm/v8_base.sail:22350.40-22350.41"
      let vreg ← (( do (V_read n 128) ) : SailM (BitVec 128) )
      (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb vreg
          (Sail.Int.toNatChecked (((width *i 2) -i 1))) width)))))


def ELR_read (el : (BitVec 2)) : SailM (BitVec 64) := do
  let r ← (( do (undefined_bitvector_at (← occLabel 1343) 64) ) : SailM (BitVec 64) )
  let questionMark := el
  if ((questionMark == EL1) : Bool)
  then
    (do
      readReg ELR_EL1)
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          readReg ELR_EL2)
      else
        (do
          if ((questionMark == EL3) : Bool)
          then
            (do
              readReg ELR_EL3)
          else
            (do
              (Unreachable ())
              (pure (r)))))


def _set_CNTKCTL_Type_PL0PCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0PCTEN r v)


def _set_CNTKCTL_Type_PL0PTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0PTEN r v)


def _set_CNTKCTL_Type_PL0VCTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0VCTEN r v)


def _set_CNTKCTL_Type_PL0VTEN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_CNTKCTL_Type_PL0VTEN r v)


def AArch64_ExecutingERETInstr (_ : Unit) : SailM Bool := do
  let instr ← (( do (ThisInstr ()) ) : SailM (BitVec 32) )
  (pure (((Sail.BitVec.castWidth (m := 20) (Sail.BitVec.extractLsb instr 31 12)) == 0b11010110100111110000#20)))


def _set_GCR_EL1_Type_Exclude (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCR_EL1_Type_Exclude r v)


def _set_GCR_EL1_Type_RRND (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_GCR_EL1_Type_RRND r v)


def _set_RGSR_EL1_Type_SEED (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 48)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RGSR_EL1_Type_SEED r v)


def _set_RGSR_EL1_Type_TAG (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_RGSR_EL1_Type_TAG r v)


def AArch64_NextRandomTagBit (_ : Unit) : SailM (BitVec 1) := do
  let w__0 ← (( do readReg GCR_EL1 ) : SailM (BitVec 64) )
  ArmFull.assert ((_get_GCR_EL1_Type_RRND w__0) == 0#1) "sail-arm/v8_base.sail:22689.31-22689.32"
  let w__1 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  let lfsr : (BitVec 16) := (Sail.BitVec.extractLsb (_get_RGSR_EL1_Type_SEED w__1) 15 0)
  let top : (BitVec 1) :=
    ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access lfsr 5)])) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
              lfsr 3)]))) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access lfsr 2)]))) ^^^ (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
          lfsr 0)])))
  let w__2 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  let w__3 ← (( do readReg RGSR_EL1 ) : SailM (BitVec 64) )
  writeReg RGSR_EL1 (Sail.BitVec.updateSubrange w__2 55 8
    (Sail.BitVec.updateSubrange (Sail.BitVec.extractLsb w__3 55 8) 15 0
      (top +++ (Sail.BitVec.extractLsb lfsr 15 1))))
  (pure (top))


def SP_read (_ : Unit) : SailM (BitVec 64) := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.SP == 0#1) : Bool)
  then
    (do
      readReg SP_EL0)
  else
    (do
      let w__2 ← (( do readReg PSTATE ) : SailM ProcState )
      let questionMark := w__2.EL
      if ((questionMark == EL0) : Bool)
      then
        (do
          readReg SP_EL0)
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              readReg SP_EL1)
          else
            (do
              if ((questionMark == EL2) : Bool)
              then
                (do
                  readReg SP_EL2)
              else
                (do
                  if ((questionMark == EL3) : Bool)
                  then
                    (do
                      readReg SP_EL3)
                  else
                    (do
                      (undefined_bitvector_at (← occLabel 1351) 64))))))


def _set_TFSRE0_EL1_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSRE0_EL1_Type_TF0 r v)


def _set_TFSR_EL1_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL1_Type_TF0 r v)


def _set_TFSR_EL2_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL2_Type_TF0 r v)


def _set_TFSR_EL3_Type_TF0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL3_Type_TF0 r v)


def _set_TFSRE0_EL1_Type_TF1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSRE0_EL1_Type_TF1 r v)


def _set_TFSR_EL1_Type_TF1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL1_Type_TF1 r v)


def _set_TFSR_EL2_Type_TF1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_TFSR_EL2_Type_TF1 r v)


def AArch64_ReportTagCheckFault (el : (BitVec 2)) (ttbr : (BitVec 1)) : SailM Unit := do
  let questionMark := el
  if ((questionMark == EL3) : Bool)
  then
    (do
      ArmFull.assert (ttbr == 0#1) "sail-arm/v8_base.sail:22983.28-22983.29"
      let w__0 ← (( do readReg TFSR_EL3 ) : SailM (BitVec 64) )
      writeReg TFSR_EL3 (Sail.BitVec.updateSubrange w__0 0 0 1#1))
  else
    (do
      if ((questionMark == EL2) : Bool)
      then
        (do
          if ((ttbr == 0#1) : Bool)
          then
            (do
              let w__1 ← (( do readReg TFSR_EL2 ) : SailM (BitVec 64) )
              writeReg TFSR_EL2 (Sail.BitVec.updateSubrange w__1 0 0 1#1))
          else
            (do
              let w__2 ← (( do readReg TFSR_EL2 ) : SailM (BitVec 64) )
              writeReg TFSR_EL2 (Sail.BitVec.updateSubrange w__2 1 1 1#1)))
      else
        (do
          if ((questionMark == EL1) : Bool)
          then
            (do
              if ((ttbr == 0#1) : Bool)
              then
                (do
                  let w__3 ← (( do readReg TFSR_EL1 ) : SailM (BitVec 64) )
                  writeReg TFSR_EL1 (Sail.BitVec.updateSubrange w__3 0 0 1#1))
              else
                (do
                  let w__4 ← (( do readReg TFSR_EL1 ) : SailM (BitVec 64) )
                  writeReg TFSR_EL1 (Sail.BitVec.updateSubrange w__4 1 1 1#1)))
          else
            (do
              if ((questionMark == EL0) : Bool)
              then
                (do
                  if ((ttbr == 0#1) : Bool)
                  then
                    (do
                      let w__5 ← (( do readReg TFSRE0_EL1 ) : SailM (BitVec 64) )
                      writeReg TFSRE0_EL1 (Sail.BitVec.updateSubrange w__5 0 0 1#1))
                  else
                    (do
                      let w__6 ← (( do readReg TFSRE0_EL1 ) : SailM (BitVec 64) )
                      writeReg TFSRE0_EL1 (Sail.BitVec.updateSubrange w__6 1 1 1#1)))
              else (pure (())))))


def _set_DBGBCR_EL1_Type_BAS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_BAS r v)


def _set_DBGBCR_Type_BAS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBCR_Type_BAS r v)


def _set_DBGWCR_EL1_Type_BAS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_BAS r v)


def _set_DBGWCR_Type_BAS (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_BAS r v)


def _set_DBGBCR_EL1_Type_BT2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_BT2 r v)


def _set_DBGBCR_EL1_Type_HMC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_HMC r v)


def _set_DBGBCR_Type_HMC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBCR_Type_HMC r v)


def _set_DBGWCR_EL1_Type_HMC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_HMC r v)


def _set_DBGWCR_Type_HMC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_HMC r v)


def _set_DBGBCR_EL1_Type_LBN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_LBN r v)


def _set_DBGBCR_Type_LBN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBCR_Type_LBN r v)


def _set_DBGWCR_EL1_Type_LBN (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_LBN r v)


def _set_DBGWCR_Type_LBN (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_LBN r v)


def _set_DBGBCR_EL1_Type_LBNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_LBNX r v)


def _set_DBGWCR_EL1_Type_LBNX (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_LBNX r v)


def _set_DBGBCR_EL1_Type_MASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_MASK r v)


def _set_DBGWCR_EL1_Type_MASK (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_MASK r v)


def _set_DBGWCR_Type_MASK (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 5)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_MASK r v)


def _set_DBGBCR_EL1_Type_PMC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_PMC r v)


def _set_DBGBCR_Type_PMC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBCR_Type_PMC r v)


def _set_DBGBCR_EL1_Type_SSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_SSC r v)


def _set_DBGBCR_Type_SSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBCR_Type_SSC r v)


def _set_DBGWCR_EL1_Type_SSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_SSC r v)


def _set_DBGWCR_Type_SSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_SSC r v)


def _set_DBGBCR_EL1_Type_SSCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBCR_EL1_Type_SSCE r v)


def _set_DBGWCR_EL1_Type_SSCE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_SSCE r v)


def _set_DBGBVR_EL1_Type_ContextID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_ContextID r v)


def _set_DBGBVR_Type_ContextID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBVR_Type_ContextID r v)


def _set_DBGBVR_EL1_Type_ContextID2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_ContextID2 r v)


def _set_DBGBXVR_Type_ContextID2 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 32)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBXVR_Type_ContextID2 r v)


def _set_DBGBVR_EL1_Type_RESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_RESS r v)


def _set_DBGWVR_EL1_Type_RESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 15)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWVR_EL1_Type_RESS r v)


def _set_VNCR_EL2_Type_RESS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 7)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VNCR_EL2_Type_RESS r v)


def _set_DBGBVR_EL1_Type_VMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGBVR_EL1_Type_VMID r v)


def _set_DBGBXVR_Type_VMID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGBXVR_Type_VMID r v)


def _set_EDVIDSR_Type_VMID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_EDVIDSR_Type_VMID r v)


def _set_PMVCIDSR_Type_VMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_PMVCIDSR_Type_VMID r v)


def _set_PMVIDSR_Type_VMID (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_PMVIDSR_Type_VMID r v)


def _set_VTTBR_EL2_Type_VMID (r_ref : (RegisterRef (BitVec 128))) (v : (BitVec 16)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 128) )
  writeRegRef r_ref (_update_VTTBR_EL2_Type_VMID r v)


def _set_VTTBR_Type_VMID (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 8)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTTBR_Type_VMID r v)


def _set_VTCR_EL2_Type_GCSH (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_GCSH r v)


def _set_VTCR_EL2_Type_NSA (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_NSA r v)


def _set_VTCR_EL2_Type_NSW (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_NSW r v)


def _set_VTCR_EL2_Type_S2PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_S2PIE r v)


def _set_ID_AA64MMFR3_EL1_Type_S2PIE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S2PIE r v)


def _set_VTCR_EL2_Type_S2POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_S2POE r v)


def _set_ID_AA64MMFR3_EL1_Type_S2POE (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 4)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_ID_AA64MMFR3_EL1_Type_S2POE r v)


def _set_VTCR_EL2_Type_SL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_SL0 r v)


def _set_VSTCR_EL2_Type_SL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSTCR_EL2_Type_SL0 r v)


def _set_VTCR_Type_SL0 (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_VTCR_Type_SL0 r v)


def _set_VTCR_EL2_Type_SL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_SL2 r v)


def _set_VSTCR_EL2_Type_SL2 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VSTCR_EL2_Type_SL2 r v)


def _set_VTCR_EL2_Type_TL0 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_TL0 r v)


def _set_VTCR_EL2_Type_TL1 (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_TL1 r v)


def _set_VTCR_EL2_Type_VS (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 1)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_VTCR_EL2_Type_VS r v)


def _set_DBGWCR_EL1_Type_LSC (r_ref : (RegisterRef (BitVec 64))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 64) )
  writeRegRef r_ref (_update_DBGWCR_EL1_Type_LSC r v)


def _set_DBGWCR_Type_LSC (r_ref : (RegisterRef (BitVec 32))) (v : (BitVec 2)) : SailM Unit := do
  let r ← (( do (reg_deref r_ref) ) : SailM (BitVec 32) )
  writeRegRef r_ref (_update_DBGWCR_Type_LSC r v)


end ArmFull.Functions
