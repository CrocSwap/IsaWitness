module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0117
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0198
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1248
public import ArmFull.Fn.M1249 set_option backward.proofsInPublic true @[expose] public section

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

def decode_setp_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let d : Int := (BitVec.toNat Rd)
          let s : Int := (BitVec.toNat Rs)
          let n : Int := (BitVec.toNat Rn)
          let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
          let stage ← (( do (undefined_MOPSStage (← occLabel 4769) ()) ) : SailM MOPSStage )
          let stage ← (( do
            match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
            | 0b00 => (pure (MOPSStage_Prologue))
            | 0b01 => (pure (MOPSStage_Main))
            | 0b10 => (pure (MOPSStage_Epilogue))
            | _ =>
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
          let stage := stage
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43117.58-43117.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_setpn_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let d : Int := (BitVec.toNat Rd)
          let s : Int := (BitVec.toNat Rs)
          let n : Int := (BitVec.toNat Rn)
          let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
          let stage ← (( do (undefined_MOPSStage (← occLabel 4770) ()) ) : SailM MOPSStage )
          let stage ← (( do
            match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
            | 0b00 => (pure (MOPSStage_Prologue))
            | 0b01 => (pure (MOPSStage_Main))
            | 0b10 => (pure (MOPSStage_Epilogue))
            | _ =>
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
          let stage := stage
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43173.58-43173.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_setpt_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let d : Int := (BitVec.toNat Rd)
          let s : Int := (BitVec.toNat Rs)
          let n : Int := (BitVec.toNat Rn)
          let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
          let stage ← (( do (undefined_MOPSStage (← occLabel 4771) ()) ) : SailM MOPSStage )
          let stage ← (( do
            match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
            | 0b00 => (pure (MOPSStage_Prologue))
            | 0b01 => (pure (MOPSStage_Main))
            | 0b10 => (pure (MOPSStage_Epilogue))
            | _ =>
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
          let stage := stage
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43229.58-43229.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_setptn_aarch64_instrs_memory_mcpymset_set (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((sz != 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let d : Int := (BitVec.toNat Rd)
          let s : Int := (BitVec.toNat Rs)
          let n : Int := (BitVec.toNat Rn)
          let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
          let stage ← (( do (undefined_MOPSStage (← occLabel 4772) ()) ) : SailM MOPSStage )
          let stage ← (( do
            match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
            | 0b00 => (pure (MOPSStage_Prologue))
            | 0b01 => (pure (MOPSStage_Main))
            | 0b10 => (pure (MOPSStage_Epilogue))
            | _ =>
              (do
                (__ArmCertEndOfDecode ())
                sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
          let stage := stage
          (__ArmCertEndOfDecode ())
          (CheckMOPSEnabled ())
          if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
          then
            (do
              let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                Constraint )
              ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43285.58-43285.59"
              match c with
              | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
              | .Constraint_NOP =>
                (do
                  (EndOfInstruction ()))
              | _ => (pure (())))
          else (pure (()))
          (execute_aarch64_instrs_memory_mcpymset_set (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage)))


def decode_setgp_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          if ((sz != 0b00#2) : Bool)
          then
            (do
              (__ArmCertEndOfDecode ())
              sailThrow ((Error_Undefined ())))
          else
            (do
              let d : Int := (BitVec.toNat Rd)
              let s : Int := (BitVec.toNat Rs)
              let n : Int := (BitVec.toNat Rn)
              let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
              let stage ← (( do (undefined_MOPSStage (← occLabel 4778) ()) ) : SailM MOPSStage )
              let stage ← (( do
                match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
                | 0b00 => (pure (MOPSStage_Prologue))
                | 0b01 => (pure (MOPSStage_Main))
                | 0b10 => (pure (MOPSStage_Epilogue))
                | _ =>
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
              let stage := stage
              (__ArmCertEndOfDecode ())
              (CheckMOPSEnabled ())
              if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
              then
                (do
                  let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                    Constraint )
                  ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43530.58-43530.59"
                  match c with
                  | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
                  | .Constraint_NOP =>
                    (do
                      (EndOfInstruction ()))
                  | _ => (pure (())))
              else (pure (()))
              (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage))))


def decode_setgpn_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          if ((sz != 0b00#2) : Bool)
          then
            (do
              (__ArmCertEndOfDecode ())
              sailThrow ((Error_Undefined ())))
          else
            (do
              let d : Int := (BitVec.toNat Rd)
              let s : Int := (BitVec.toNat Rs)
              let n : Int := (BitVec.toNat Rn)
              let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
              let stage ← (( do (undefined_MOPSStage (← occLabel 4779) ()) ) : SailM MOPSStage )
              let stage ← (( do
                match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
                | 0b00 => (pure (MOPSStage_Prologue))
                | 0b01 => (pure (MOPSStage_Main))
                | 0b10 => (pure (MOPSStage_Epilogue))
                | _ =>
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
              let stage := stage
              (__ArmCertEndOfDecode ())
              (CheckMOPSEnabled ())
              if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
              then
                (do
                  let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                    Constraint )
                  ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43589.58-43589.59"
                  match c with
                  | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
                  | .Constraint_NOP =>
                    (do
                      (EndOfInstruction ()))
                  | _ => (pure (())))
              else (pure (()))
              (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage))))


def decode_setgpt_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          if ((sz != 0b00#2) : Bool)
          then
            (do
              (__ArmCertEndOfDecode ())
              sailThrow ((Error_Undefined ())))
          else
            (do
              let d : Int := (BitVec.toNat Rd)
              let s : Int := (BitVec.toNat Rs)
              let n : Int := (BitVec.toNat Rn)
              let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
              let stage ← (( do (undefined_MOPSStage (← occLabel 4780) ()) ) : SailM MOPSStage )
              let stage ← (( do
                match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
                | 0b00 => (pure (MOPSStage_Prologue))
                | 0b01 => (pure (MOPSStage_Main))
                | 0b10 => (pure (MOPSStage_Epilogue))
                | _ =>
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
              let stage := stage
              (__ArmCertEndOfDecode ())
              (CheckMOPSEnabled ())
              if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
              then
                (do
                  let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                    Constraint )
                  ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43648.58-43648.59"
                  match c with
                  | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
                  | .Constraint_NOP =>
                    (do
                      (EndOfInstruction ()))
                  | _ => (pure (())))
              else (pure (()))
              (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage))))


def decode_setgptn_aarch64_instrs_memory_mcpymset_setg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 4)) (Rs : (BitVec 5)) (sz : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatMOPS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do (HaveMTEExt ()) ) : SailM Bool )
      if ((! w__1) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          if ((sz != 0b00#2) : Bool)
          then
            (do
              (__ArmCertEndOfDecode ())
              sailThrow ((Error_Undefined ())))
          else
            (do
              let d : Int := (BitVec.toNat Rd)
              let s : Int := (BitVec.toNat Rs)
              let n : Int := (BitVec.toNat Rn)
              let options_name : (BitVec 2) := (Sail.BitVec.extractLsb op2 1 0)
              let stage ← (( do (undefined_MOPSStage (← occLabel 4781) ()) ) : SailM MOPSStage )
              let stage ← (( do
                match (BitVec.setWidth 2 (Sail.BitVec.extractLsb op2 3 2)) with
                | 0b00 => (pure (MOPSStage_Prologue))
                | 0b01 => (pure (MOPSStage_Main))
                | 0b10 => (pure (MOPSStage_Epilogue))
                | _ =>
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ()))) ) : SailM MOPSStage )
              let stage := stage
              (__ArmCertEndOfDecode ())
              (CheckMOPSEnabled ())
              if ((((((s == n) || (s == d)) || (n == d)) || (d == 31)) || (n == 31)) : Bool)
              then
                (do
                  let c ← (( do (ConstrainUnpredictable Unpredictable_MOPSOVERLAP31) ) : SailM
                    Constraint )
                  ArmFull.assert ((BEq.beq c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)) "sail-inputs/15-instrs64.sail:43707.58-43707.59"
                  match c with
                  | .Constraint_UNDEF => sailThrow ((Error_Undefined ()))
                  | .Constraint_NOP =>
                    (do
                      (EndOfInstruction ()))
                  | _ => (pure (())))
              else (pure (()))
              (execute_aarch64_instrs_memory_mcpymset_setg (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (n)) options_name (Sail.Int.toNatChecked (s)) stage))))


def decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := true
      let zero_data : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpairpost (Sail.Int.toNatChecked (n)) offset
        postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_st2g_aarch64_instrs_integer_tags_mcsettagpairpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := false
      let zero_data : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpairpost (Sail.Int.toNatChecked (n)) offset
        postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_st2g_aarch64_instrs_integer_tags_mcsettagpair (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := false
      let postindex : Bool := false
      let zero_data : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpairpost (Sail.Int.toNatChecked (n)) offset
        postindex (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stg_aarch64_instrs_integer_tags_mcsettagpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := true
      let zero_data : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpost (Sail.Int.toNatChecked (n)) offset postindex
        (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stg_aarch64_instrs_integer_tags_mcsettagpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := false
      let zero_data : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpost (Sail.Int.toNatChecked (n)) offset postindex
        (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stg_aarch64_instrs_integer_tags_mcsettag (Xt : (BitVec 5)) (Xn : (BitVec 5)) (imm9 : (BitVec 9)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let offset : (BitVec 64) := ((sign_extend imm9 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := false
      let postindex : Bool := false
      let zero_data : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettagpost (Sail.Int.toNatChecked (n)) offset postindex
        (Sail.Int.toNatChecked (t)) writeback zero_data))


def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let t2 : Int := (BitVec.toNat Xt2)
      let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) writeback))


def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapairpre (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let t2 : Int := (BitVec.toNat Xt2)
      let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := true
      let postindex : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) writeback))


def decode_stgp_aarch64_instrs_integer_tags_mcsettaganddatapair (Xt : (BitVec 5)) (Xn : (BitVec 5)) (Xt2 : (BitVec 5)) (simm7 : (BitVec 7)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Xn)
      let t : Int := (BitVec.toNat Xt)
      let t2 : Int := (BitVec.toNat Xt2)
      let offset : (BitVec 64) := ((sign_extend simm7 64) <<< LOG2_TAG_GRANULE)
      let writeback : Bool := false
      let postindex : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsettaganddatapairpost (Sail.Int.toNatChecked (n))
        offset postindex (Sail.Int.toNatChecked (t)) (Sail.Int.toNatChecked (t2)) writeback))


def decode_stilp_aarch64_instrs_memory_ordered_pair_stilp (Rt : (BitVec 5)) (Rn : (BitVec 5)) (opc2 : (BitVec 4)) (Rt2 : (BitVec 5)) (L : (BitVec 1)) (size : (BitVec 2)) : SailM Unit := do
  let postindex : Bool := false
  let wback : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1)
  let offset ← (( do (undefined_int_at (← occLabel 5001) ()) ) : SailM Int )
  let n : Int := (BitVec.toNat Rn)
  let t : Int := (BitVec.toNat Rt)
  let t2 : Int := (BitVec.toNat Rt2)
  let scale : Int :=
    (2 +i (BitVec.toNat (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access size 0)]))))
  let datasize : Int := (Int.shiftl 8 (Sail.Int.toNatChecked (scale)))
  let memop ← (( do (undefined_MemOp (← occLabel 5002) ()) ) : SailM MemOp )
  let (memop, offset) : (MemOp × Int) :=
    if ((L == 1#1) : Bool)
    then
      (let memop : MemOp := MemOp_LOAD
      let offset : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1) : Bool)
        then (Int.shiftl 2 (Sail.Int.toNatChecked (scale)))
        else 0
      (memop, offset))
    else
      (let memop : MemOp := MemOp_STORE
      let offset : Int :=
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access opc2 0)])) == 0#1) : Bool)
        then ((Neg.neg 1) *i (Int.shiftl 2 (Sail.Int.toNatChecked (scale))))
        else 0
      (memop, offset))
  let offset : Int := offset
  let tagchecked : Bool := (wback || (n != 31))
  let rt_unknown : Bool := false
  let wb_unknown : Bool := false
  let (wb_unknown, wback) ← (( do
    if (((((BEq.beq memop MemOp_LOAD) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPLD) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_WBSUPPRESS) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-inputs/15-instrs64.sail:51080.113-51080.114"
        match c with
        | .Constraint_WBSUPPRESS =>
          (let wback : Bool := false
          (pure ((wb_unknown, wback))))
        | .Constraint_UNKNOWN =>
          (let wb_unknown : Bool := true
          (pure ((wb_unknown, wback))))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
            (EndOfInstruction ())
            (pure ((wb_unknown, wback))))
        | _ => (pure ((wb_unknown, wback))))
    else (pure ((wb_unknown, wback))) ) : SailM (Bool × Bool) )
  let rt_unknown ← (( do
    if (((((BEq.beq memop MemOp_STORE) && wback) && ((t == n) || (t2 == n))) && (n != 31)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_WBOVERLAPST) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_NONE) || ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq
                c Constraint_UNDEF) || (BEq.beq c Constraint_NOP)))) "sail-inputs/15-instrs64.sail:51099.107-51099.108"
        match c with
        | .Constraint_NONE => (pure (false))
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  let rt_unknown ← (( do
    if (((BEq.beq memop MemOp_LOAD) && (t == t2)) : Bool)
    then
      (do
        let c ← (( do (ConstrainUnpredictable Unpredictable_LDPOVERLAP) ) : SailM Constraint )
        ArmFull.assert ((BEq.beq c Constraint_UNKNOWN) || ((BEq.beq c Constraint_UNDEF) || (BEq.beq
              c Constraint_NOP))) "sail-inputs/15-instrs64.sail:51118.84-51118.85"
        match c with
        | .Constraint_UNKNOWN => (pure (true))
        | .Constraint_UNDEF =>
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        | .Constraint_NOP =>
          (do
            (__ArmCertEndOfDecode ())
            (EndOfInstruction ())
            (pure (rt_unknown)))
        | _ => (pure (rt_unknown)))
    else (pure (rt_unknown)) ) : SailM Bool )
  ArmFull.assert ((datasize == 32) || (datasize == 64)) "sail-inputs/15-instrs64.sail:51132.44-51132.45"
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_memory_ordered_pair_stilp (Sail.Int.toNatChecked (datasize)) memop
    (Sail.Int.toNatChecked (n)) offset postindex rt_unknown (Sail.Int.toNatChecked (t))
    (Sail.Int.toNatChecked (t2)) tagchecked wb_unknown wback)


end ArmFull.Functions
