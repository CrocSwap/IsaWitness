module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0123
public import ArmFull.Fn.M0143
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0164
public import ArmFull.Fn.M0170
public import ArmFull.Fn.M0242
public import ArmFull.Fn.M0602
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0604 set_option backward.proofsInPublic true @[expose] public section

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

def decode_lsrv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_shift_variable (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    shift_type)


def decode_rorv_aarch64_instrs_integer_shift_variable (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op2 : (BitVec 2)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let shift_type ← (( do (DecodeShift op2) ) : SailM ShiftType )
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_shift_variable (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    shift_type)


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autda_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthDA w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthDA w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autdb_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthDB w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthDB w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autia_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthIA w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthIA w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


/-- Type quantifiers: d : Nat, n : Nat, k_source_is_sp : Bool, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_integer_pac_autib_dp_1src (d : Nat) (n : Nat) (source_is_sp : Bool) : SailM Unit := do
  let auth_then_branch : Bool := false
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      if (source_is_sp : Bool)
      then
        (do
          let w__1 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__2 ← (( do (SP_read ()) ) : SailM (BitVec 64) )
          let w__3 ← (( do (AuthIB w__1 w__2 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__3))
      else
        (do
          let w__4 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
          let w__5 ← (( do (X_read n 64) ) : SailM (BitVec 64) )
          let w__6 ← (( do (AuthIB w__4 w__5 auth_then_branch) ) : SailM (BitVec 64) )
          (X_set d 64 w__6)))
  else (pure (()))


def decode_axflag_aarch64_instrs_integer_flags_axflag (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFlagFormatExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_flags_axflag ()))


def decode_b_cond_aarch64_instrs_branch_conditional_cond (cond : (BitVec 4)) (imm19 : (BitVec 19)) : SailM Unit := do
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  let condition : (BitVec 4) := cond
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_conditional_cond condition offset)


def decode_bc_cond_aarch64_instrs_branch_conditional_hinted (cond : (BitVec 4)) (imm19 : (BitVec 19)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatHBC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
      let condition : (BitVec 4) := cond
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_branch_conditional_hinted condition offset))


def decode_bfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool_at (← occLabel 3977) ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool_at (← occLabel 3978) ()) ) : SailM Bool )
  let wmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3979)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let tmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3980)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let (extend, inzero) ← (( do
    match opc with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure ((extend, inzero))))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure ((extend, inzero))))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure ((extend, inzero))))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && (((N != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immr 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   imms 5)])) != 0#1))) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let r : Int := (BitVec.toNat immr)
          let s : Int := (BitVec.toNat imms)
          let w__0 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
              N imms immr false (Sail.Int.toNatChecked (datasize)))) ) : SailM
            ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
            )
          let (tup__0, tup__1) :=
            (w__0 : ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int)))))
          let wmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__0
          let tmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__1
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_bitfield (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) extend inzero (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (r)) (Sail.Int.toNatChecked (s)) (Sail.BitVec.castWidth tmask)
            (Sail.BitVec.castWidth wmask))))


def decode_sbfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool_at (← occLabel 3981) ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool_at (← occLabel 3982) ()) ) : SailM Bool )
  let wmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3983)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let tmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3984)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let (extend, inzero) ← (( do
    match opc with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure ((extend, inzero))))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure ((extend, inzero))))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure ((extend, inzero))))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && (((N != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immr 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   imms 5)])) != 0#1))) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let r : Int := (BitVec.toNat immr)
          let s : Int := (BitVec.toNat imms)
          let w__0 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
              N imms immr false (Sail.Int.toNatChecked (datasize)))) ) : SailM
            ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
            )
          let (tup__0, tup__1) :=
            (w__0 : ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int)))))
          let wmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__0
          let tmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__1
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_bitfield (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) extend inzero (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (r)) (Sail.Int.toNatChecked (s)) (Sail.BitVec.castWidth tmask)
            (Sail.BitVec.castWidth wmask))))


def decode_ubfm_aarch64_instrs_integer_bitfield (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (immr : (BitVec 6)) (N : (BitVec 1)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let inzero ← (( do (undefined_bool_at (← occLabel 3985) ()) ) : SailM Bool )
  let extend ← (( do (undefined_bool_at (← occLabel 3986) ()) ) : SailM Bool )
  let wmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3987)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let tmask ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 3988)
      (Sail.Int.toNatChecked (datasize)))) ) : SailM
    (BitVec (Sail.Int.toNatChecked (datasize : Int))) )
  let (extend, inzero) ← (( do
    match opc with
    | 0b00 =>
      (let inzero : Bool := true
      let extend : Bool := true
      (pure ((extend, inzero))))
    | 0b01 =>
      (let inzero : Bool := false
      let extend : Bool := false
      (pure ((extend, inzero))))
    | 0b10 =>
      (let inzero : Bool := true
      let extend : Bool := false
      (pure ((extend, inzero))))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM (Bool × Bool) )
  let extend := extend
  let inzero := inzero
  if (((sf == 1#1) && (N != 1#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && (((N != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access immr 5)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                   imms 5)])) != 0#1))) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let r : Int := (BitVec.toNat immr)
          let s : Int := (BitVec.toNat imms)
          let w__0 ← (( do
            ((fun (x0, x1) => ((Sail.BitVec.castWidth x0), (Sail.BitVec.castWidth x1))) <$> (DecodeBitMasks
              N imms immr false (Sail.Int.toNatChecked (datasize)))) ) : SailM
            ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int))))
            )
          let (tup__0, tup__1) :=
            (w__0 : ((BitVec (Sail.Int.toNatChecked (datasize : Int))) × (BitVec (Sail.Int.toNatChecked (datasize : Int)))))
          let wmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__0
          let tmask : (BitVec (Sail.Int.toNatChecked (datasize : Int))) := tup__1
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_bitfield (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) extend inzero (Sail.Int.toNatChecked (n))
            (Sail.Int.toNatChecked (r)) (Sail.Int.toNatChecked (s)) (Sail.BitVec.castWidth tmask)
            (Sail.BitVec.castWidth wmask))))


def decode_brk_aarch64_instrs_system_exceptions_debug_breakpoint (imm16 : (BitVec 16)) : SailM Unit := do
  let comment : (BitVec 16) := imm16
  let w__0 ← (( do (HaveBTIExt ()) ) : SailM Bool )
  if (w__0 : Bool)
  then
    (do
      (SetBTypeCompatible true))
  else (pure (()))
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_system_exceptions_debug_breakpoint comment)


def decode_cbnz_aarch64_instrs_branch_conditional_compare (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let iszero : Bool := (op == 0#1)
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_conditional_compare (Sail.Int.toNatChecked (datasize)) iszero
    offset (Sail.Int.toNatChecked (t)))


def decode_cbz_aarch64_instrs_branch_conditional_compare (Rt : (BitVec 5)) (imm19 : (BitVec 19)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let iszero : Bool := (op == 0#1)
  let offset : (BitVec 64) := (sign_extend (imm19 +++ 0b00#2) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_conditional_compare (Sail.Int.toNatChecked (datasize)) iszero
    offset (Sail.Int.toNatChecked (t)))


def decode_ccmn_reg_aarch64_instrs_integer_conditional_compare_register (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_conditional_compare_register condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_ccmp_reg_aarch64_instrs_integer_conditional_compare_register (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_conditional_compare_register condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_ccmn_imm_aarch64_instrs_integer_conditional_compare_immediate (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm5 (Sail.Int.toNatChecked (datasize))))
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_conditional_compare_immediate condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_ccmp_imm_aarch64_instrs_integer_conditional_compare_immediate (nzcv : (BitVec 4)) (Rn : (BitVec 5)) (cond : (BitVec 4)) (imm5 : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let sub_op : Bool := (op == 1#1)
  let condition : (BitVec 4) := cond
  let flags : (BitVec 4) := nzcv
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (Sail.BitVec.zeroExtend imm5 (Sail.Int.toNatChecked (datasize))))
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_conditional_compare_immediate condition
    (Sail.Int.toNatChecked (datasize)) flags (Sail.BitVec.castWidth imm) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_cfinv_aarch64_instrs_integer_flags_cfinv (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFlagManipulateExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_flags_cfinv ()))


def decode_clrex_aarch64_instrs_system_monitors (CRm : (BitVec 4)) : SailM Unit := do
  (__ArmCertEndOfDecode ())
  (pure ((execute_aarch64_instrs_system_monitors ())))


def decode_cls_int_aarch64_instrs_integer_arithmetic_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let opcode : CountOp :=
    if ((op == 0#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_cnt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)) opcode)


def decode_clz_int_aarch64_instrs_integer_arithmetic_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let opcode : CountOp :=
    if ((op == 0#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_cnt (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n)) opcode)


def decode_cnt_aarch64_instrs_integer_arithmetic_unary_cnt (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCSSC ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let datasize : Int := (Int.shiftl 32 (BitVec.toNat sf))
      let n : Int := (BitVec.toNat Rn)
      let d : Int := (BitVec.toNat Rd)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_unary_cnt (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n))))


def decode_crc32_aarch64_instrs_integer_crc (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCRCExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if (((sf == 1#1) && (sz != 0b11#2)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          if (((sf == 0#1) && (sz == 0b11#2)) : Bool)
          then
            (do
              (__ArmCertEndOfDecode ())
              sailThrow ((Error_Undefined ())))
          else
            (do
              let size : Int := (Int.shiftl 8 (BitVec.toNat sz))
              let crc32c : Bool := (C == 1#1)
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_integer_crc crc32c (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
                (Sail.Int.toNatChecked (size))))))


def decode_crc32c_aarch64_instrs_integer_crc (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sz : (BitVec 2)) (C : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let w__0 ← (( do (HaveCRCExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Rd)
      let n : Int := (BitVec.toNat Rn)
      let m : Int := (BitVec.toNat Rm)
      if (((sf == 1#1) && (sz != 0b11#2)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          if (((sf == 0#1) && (sz == 0b11#2)) : Bool)
          then
            (do
              (__ArmCertEndOfDecode ())
              sailThrow ((Error_Undefined ())))
          else
            (do
              let size : Int := (Int.shiftl 8 (BitVec.toNat sz))
              let crc32c : Bool := (C == 1#1)
              (__ArmCertEndOfDecode ())
              (execute_aarch64_instrs_integer_crc crc32c (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
                (Sail.Int.toNatChecked (size))))))


def decode_csel_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let condition : (BitVec 4) := cond
  let else_inv : Bool := (op == 1#1)
  let else_inc : Bool := (o2 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_conditional_select condition (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) else_inc else_inv (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
