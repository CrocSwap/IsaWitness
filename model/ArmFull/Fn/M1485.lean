module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0019
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M1340
public import ArmFull.Fn.M1354
public import ArmFull.Fn.M1381 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegRead (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  if (((CRd == 0b0101#4) && ((cp_num == (BitVec.toNat 0xE#4)) : Bool)) : Bool)
  then
    (do
      (AArch32_STC (integer_subrange cp_num 3 0) CRd address))
  else (pure (()))


/-- Type quantifiers: cp_num : Int -/
def AArch32_SysRegWriteM (cp_num : Int) (instr : (BitVec 32)) (address : (BitVec 32)) : SailM Unit := do
  let CRd : (BitVec 4) := (Sail.BitVec.extractLsb instr 15 12)
  if (((CRd == 0b0101#4) && ((cp_num == (BitVec.toNat 0xE#4)) : Bool)) : Bool)
  then
    (do
      (AArch32_LDC (integer_subrange cp_num 3 0) CRd address))
  else (pure (()))


def decode_b_uncond_aarch64_instrs_branch_unconditional_immediate (imm26 : (BitVec 26)) (op : (BitVec 1)) : SailM Unit := do
  let branch_type : BranchType :=
    if ((op == 1#1) : Bool)
    then BranchType_DIRCALL
    else BranchType_DIR
  let offset : (BitVec 64) := (sign_extend (imm26 +++ 0b00#2) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)


def decode_bl_aarch64_instrs_branch_unconditional_immediate (imm26 : (BitVec 26)) (op : (BitVec 1)) : SailM Unit := do
  let branch_type : BranchType :=
    if ((op == 1#1) : Bool)
    then BranchType_DIRCALL
    else BranchType_DIR
  let offset : (BitVec 64) := (sign_extend (imm26 +++ 0b00#2) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_immediate branch_type offset)


def decode_blr_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4005) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else
          (do
            if ((BEq.beq branch_type BranchType_RET) : Bool)
            then
              (do
                if ((n != 31) : Bool)
                then
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ())))
                else
                  (let n : Nat := 30
                  let source_is_sp : Bool := true
                  (pure ((n, source_is_sp)))))
            else (pure ((n, source_is_sp)))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


def decode_blra_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4006) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else
          (do
            if ((BEq.beq branch_type BranchType_RET) : Bool)
            then
              (do
                if ((n != 31) : Bool)
                then
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ())))
                else
                  (let n : Nat := 30
                  let source_is_sp : Bool := true
                  (pure ((n, source_is_sp)))))
            else (pure ((n, source_is_sp)))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


def decode_br_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4007) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else
          (do
            if ((BEq.beq branch_type BranchType_RET) : Bool)
            then
              (do
                if ((n != 31) : Bool)
                then
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ())))
                else
                  (let n : Nat := 30
                  let source_is_sp : Bool := true
                  (pure ((n, source_is_sp)))))
            else (pure ((n, source_is_sp)))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


def decode_bra_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4008) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else
          (do
            if ((BEq.beq branch_type BranchType_RET) : Bool)
            then
              (do
                if ((n != 31) : Bool)
                then
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ())))
                else
                  (let n : Nat := 30
                  let source_is_sp : Bool := true
                  (pure ((n, source_is_sp)))))
            else (pure ((n, source_is_sp)))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


def decode_ret_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4009) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else
          (do
            if ((BEq.beq branch_type BranchType_RET) : Bool)
            then
              (do
                if ((n != 31) : Bool)
                then
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ())))
                else
                  (let n : Nat := 30
                  let source_is_sp : Bool := true
                  (pure ((n, source_is_sp)))))
            else (pure ((n, source_is_sp)))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


def decode_reta_aarch64_instrs_branch_unconditional_register (Rm : (BitVec 5)) (Rn : (BitVec 5)) (M : (BitVec 1)) (A : (BitVec 1)) (op : (BitVec 2)) (Z : (BitVec 1)) : SailM Unit := do
  let n : Nat := (BitVec.toNat Rn)
  let branch_type ← (( do (undefined_BranchType (← occLabel 4010) ()) ) : SailM BranchType )
  let m : Int := (BitVec.toNat Rm)
  let pac : Bool := (A == 1#1)
  let use_key_a : Bool := (M == 0#1)
  let source_is_sp : Bool := ((Z == 1#1) && (m == 31))
  if (((! pac) && (m != 0)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__1 ← (( do
        if (pac : Bool)
        then
          (do
            let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
            (pure (((! w__0) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__1 : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else (pure (())))
  let branch_type ← (( do
    match op with
    | 0b00 => (pure (BranchType_INDIR))
    | 0b01 => (pure (BranchType_INDCALL))
    | 0b10 => (pure (BranchType_RET))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM BranchType )
  let branch_type := branch_type
  let (n, source_is_sp) ← (( do
    if (pac : Bool)
    then
      (do
        if (((Z == 0#1) && (m != 31)) : Bool)
        then
          (do
            (__ArmCertEndOfDecode ())
            sailThrow ((Error_Undefined ())))
        else
          (do
            if ((BEq.beq branch_type BranchType_RET) : Bool)
            then
              (do
                if ((n != 31) : Bool)
                then
                  (do
                    (__ArmCertEndOfDecode ())
                    sailThrow ((Error_Undefined ())))
                else
                  (let n : Nat := 30
                  let source_is_sp : Bool := true
                  (pure ((n, source_is_sp)))))
            else (pure ((n, source_is_sp)))))
    else (pure ((n, source_is_sp))) ) : SailM (Nat × Bool) )
  let n : Int := n
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_unconditional_register branch_type (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) pac source_is_sp use_key_a)


def decode_FADDV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDV_V_P_Z__ 128 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDV_V_P_Z__ 256 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDV_V_P_Z__ 512 (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (esize))
                (Sail.Int.toNatChecked (g)) (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDV_V_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FADDV_V_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_FMAXNMV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMV_V_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMV_V_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMV_V_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMV_V_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMAXNMV_V_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


def decode_FMINNMV_V_P_Z__ (size : (BitVec 2)) (Pg : (BitVec 3)) (Zn : (BitVec 5)) (Vd : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then
      (do
        let w__1 ← (( do (HaveSME ()) ) : SailM Bool )
        (pure (((! w__1) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((size == 0b00#2) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
          let g : Int := (BitVec.toNat Pg)
          let n : Int := (BitVec.toNat Zn)
          let d : Int := (BitVec.toNat Vd)
          match VL with
          | 128 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMV_V_P_Z__ 128 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 256 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMV_V_P_Z__ 256 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 512 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMV_V_P_Z__ 512 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 1024 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMV_V_P_Z__ 1024 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | 2048 =>
            (do
              (__ArmCertEndOfDecode ())
              (execute_FMINNMV_V_P_Z__ 2048 (Sail.Int.toNatChecked (d))
                (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (g))
                (Sail.Int.toNatChecked (n))))
          | _ => (pure (()))))


end ArmFull.Functions
