module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0011
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0020
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0022
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0086
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0143
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0164
public import ArmFull.Fn.M0168
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0195
public import ArmFull.Fn.M0235
public import ArmFull.Fn.M0241
public import ArmFull.Fn.M0242
public import ArmFull.Fn.M0244
public import ArmFull.Fn.M0245
public import ArmFull.Fn.M0248
public import ArmFull.Fn.M0251
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0602
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0865 set_option backward.proofsInPublic true @[expose] public section

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

def decode_csinc_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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


def decode_csinv_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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


def decode_csneg_aarch64_instrs_integer_conditional_select (Rd : (BitVec 5)) (Rn : (BitVec 5)) (o2 : (BitVec 1)) (cond : (BitVec 4)) (Rm : (BitVec 5)) (op : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
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


def decode_ctz_aarch64_instrs_integer_arithmetic_unary_ctz (Rd : (BitVec 5)) (Rn : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
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
      (execute_aarch64_instrs_integer_arithmetic_unary_ctz (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (n))))


def decode_dcps1_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__0 ← (( do (Halted ()) ) : SailM Bool )
      if ((! w__0) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_exceptions_debug_exception target_level)))


def decode_dcps2_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__0 ← (( do (Halted ()) ) : SailM Bool )
      if ((! w__0) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_exceptions_debug_exception target_level)))


def decode_dcps3_aarch64_instrs_system_exceptions_debug_exception (LL : (BitVec 2)) (imm16 : (BitVec 16)) : SailM Unit := do
  let target_level : (BitVec 2) := LL
  if ((LL == 0b00#2) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__0 ← (( do (Halted ()) ) : SailM Bool )
      if ((! w__0) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_exceptions_debug_exception target_level)))


def decode_dmb_aarch64_instrs_system_barriers_dmb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  let domain ← (( do (undefined_MBReqDomain (← occLabel 4096) ()) ) : SailM MBReqDomain )
  let types ← (( do (undefined_MBReqTypes (← occLabel 4097) ()) ) : SailM MBReqTypes )
  let domain : MBReqDomain :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb CRm 3 2)) with
    | 0b00 => MBReqDomain_OuterShareable
    | 0b01 => MBReqDomain_Nonshareable
    | 0b10 => MBReqDomain_InnerShareable
    | _ => MBReqDomain_FullSystem
  let (domain, types) : (MBReqDomain × MBReqTypes) :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb CRm 1 0)) with
    | 0b00 =>
      (let types : MBReqTypes := MBReqTypes_All
      let domain : MBReqDomain := MBReqDomain_FullSystem
      (domain, types))
    | 0b01 =>
      (let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b10 =>
      (let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | _ =>
      (let types : MBReqTypes := MBReqTypes_All
      (domain, types))
  let types := types
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_system_barriers_dmb domain types)


def decode_drps_aarch64_instrs_branch_unconditional_dret (_ : Unit) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (Halted ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
        (pure (((w__1.EL == EL0) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_branch_unconditional_dret ()))


def decode_dsb_aarch64_instrs_system_barriers_dsb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  let nXS : Bool := false
  let alias' ← (( do (undefined_DSBAlias (← occLabel 4098) ()) ) : SailM DSBAlias )
  let alias' : DSBAlias :=
    match CRm with
    | 0b0000 => DSBAlias_SSBB
    | 0b0100 => DSBAlias_PSSBB
    | _ => DSBAlias_DSB
  let alias' := alias'
  let domain ← (( do (undefined_MBReqDomain (← occLabel 4099) ()) ) : SailM MBReqDomain )
  let domain : MBReqDomain :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb CRm 3 2)) with
    | 0b00 => MBReqDomain_OuterShareable
    | 0b01 => MBReqDomain_Nonshareable
    | 0b10 => MBReqDomain_InnerShareable
    | _ => MBReqDomain_FullSystem
  let types ← (( do (undefined_MBReqTypes (← occLabel 4100) ()) ) : SailM MBReqTypes )
  let (domain, types) : (MBReqDomain × MBReqTypes) :=
    match (BitVec.setWidth 2 (Sail.BitVec.extractLsb CRm 1 0)) with
    | 0b00 =>
      (let types : MBReqTypes := MBReqTypes_All
      let domain : MBReqDomain := MBReqDomain_FullSystem
      (domain, types))
    | 0b01 =>
      (let types : MBReqTypes := MBReqTypes_Reads
      (domain, types))
    | 0b10 =>
      (let types : MBReqTypes := MBReqTypes_Writes
      (domain, types))
    | _ =>
      (let types : MBReqTypes := MBReqTypes_All
      (domain, types))
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_system_barriers_dsb alias' domain nXS types)


def decode_dsb_aarch64_instrs_system_barriers_dsb_nxs (imm2 : (BitVec 2)) : SailM Unit := do
  let w__0 ← (( do (HaveFeatXS ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let types : MBReqTypes := MBReqTypes_All
      let nXS : Bool := true
      let alias' : DSBAlias := DSBAlias_DSB
      let domain ← (( do (undefined_MBReqDomain (← occLabel 4101) ()) ) : SailM MBReqDomain )
      let domain : MBReqDomain :=
        match imm2 with
        | 0b00 => MBReqDomain_OuterShareable
        | 0b01 => MBReqDomain_Nonshareable
        | 0b10 => MBReqDomain_InnerShareable
        | _ => MBReqDomain_FullSystem
      let domain := domain
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_system_barriers_dsb alias' domain nXS types))


/-- Type quantifiers: k_pac : Bool, k_use_key_a : Bool -/
def execute_aarch64_instrs_branch_unconditional_eret (pac : Bool) (use_key_a : Bool) : SailM Unit := do
  (AArch64_CheckForERetTrap pac use_key_a)
  let target ← (( do (ELR_read__1 ()) ) : SailM (BitVec 64) )
  let modifier ← (( do (SP_read ()) ) : SailM (BitVec 64) )
  let auth_then_branch : Bool := true
  let target ← (( do
    if (pac : Bool)
    then
      (do
        if (use_key_a : Bool)
        then
          (do
            (AuthIA target modifier auth_then_branch))
        else
          (do
            (AuthIB target modifier auth_then_branch)))
    else (pure (target)) ) : SailM (BitVec 64) )
  (return_exception (Sail.BitVec.extractLsb target 55 0))
  let w__2 ← (( do (SPSR_read (N := 64)) ) : SailM (BitVec 64) )
  (AArch64_ExceptionReturn target w__2)


def decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imms : (BitVec 6)) (Rm : (BitVec 5)) (N : (BitVec 1)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  if ((N != sf) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imms 5)])) == 1#1)) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          let lsb : Int := (BitVec.toNat imms)
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_ins_ext_extract_immediate (Sail.Int.toNatChecked (d))
            (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (lsb))
            (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)))))


def decode_gmi_aarch64_instrs_integer_tags_mcinserttagmask (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Xd)
      let n : Int := (BitVec.toNat Xn)
      let m : Int := (BitVec.toNat Xm)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcinserttagmask (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_hlt_aarch64_instrs_system_exceptions_debug_halt (imm16 : (BitVec 16)) : SailM Unit := do
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
         (pure ((((_get_EDSCR_Type_HDE w__0) == 0#1) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaltingAllowed ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let w__3 ← (( do (HaveBTIExt ()) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          (SetBTypeCompatible true))
      else (pure (()))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_system_exceptions_debug_halt ()))


def decode_hvc_aarch64_instrs_system_exceptions_runtime_hvc (imm16 : (BitVec 16)) : SailM Unit := do
  let imm : (BitVec 16) := imm16
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_system_exceptions_runtime_hvc imm)


def decode_irg_aarch64_instrs_integer_tags_mcinsertrandomtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTEExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let d : Int := (BitVec.toNat Xd)
      let n : Int := (BitVec.toNat Xn)
      let m : Int := (BitVec.toNat Xm)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcinsertrandomtag (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_isb_aarch64_instrs_system_barriers_isb (opc : (BitVec 2)) (CRm : (BitVec 4)) : SailM Unit := do
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_system_barriers_isb ())


def decode_madd_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let datasize : Int := destsize
  let sub_op : Bool := (o0 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (destsize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_msub_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Ra : (BitVec 5)) (o0 : (BitVec 1)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let a : Int := (BitVec.toNat Ra)
  let destsize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let datasize : Int := destsize
  let sub_op : Bool := (o0 == 1#1)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_arithmetic_mul_uniform_add_sub (Sail.Int.toNatChecked (a))
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize))
    (Sail.Int.toNatChecked (destsize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))
    sub_op)


def decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let imm : (BitVec 16) := imm16
  let opcode ← (( do (undefined_MoveWideOp (← occLabel 4659) ()) ) : SailM MoveWideOp )
  let opcode ← (( do
    match opc with
    | 0b00 => (pure (MoveWideOp_N))
    | 0b10 => (pure (MoveWideOp_Z))
    | 0b11 => (pure (MoveWideOp_K))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM MoveWideOp )
  let opcode := opcode
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access hw 1)])) == 1#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let pos : Int := (BitVec.toNat (hw +++ 0b0000#4))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) imm opcode (Sail.Int.toNatChecked (pos))))


def decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let imm : (BitVec 16) := imm16
  let opcode ← (( do (undefined_MoveWideOp (← occLabel 4660) ()) ) : SailM MoveWideOp )
  let opcode ← (( do
    match opc with
    | 0b00 => (pure (MoveWideOp_N))
    | 0b10 => (pure (MoveWideOp_Z))
    | 0b11 => (pure (MoveWideOp_K))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM MoveWideOp )
  let opcode := opcode
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access hw 1)])) == 1#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let pos : Int := (BitVec.toNat (hw +++ 0b0000#4))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) imm opcode (Sail.Int.toNatChecked (pos))))


def decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide (Rd : (BitVec 5)) (imm16 : (BitVec 16)) (hw : (BitVec 2)) (opc : (BitVec 2)) (sf : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((sf == 1#1) : Bool)
    then 64
    else 32
  let imm : (BitVec 16) := imm16
  let opcode ← (( do (undefined_MoveWideOp (← occLabel 4661) ()) ) : SailM MoveWideOp )
  let opcode ← (( do
    match opc with
    | 0b00 => (pure (MoveWideOp_N))
    | 0b10 => (pure (MoveWideOp_Z))
    | 0b11 => (pure (MoveWideOp_K))
    | _ =>
      (do
        (__ArmCertEndOfDecode ())
        sailThrow ((Error_Undefined ()))) ) : SailM MoveWideOp )
  let opcode := opcode
  if (((sf == 0#1) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access hw 1)])) == 1#1)) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let pos : Int := (BitVec.toNat (hw +++ 0b0000#4))
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_ins_ext_insert_movewide (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) imm opcode (Sail.Int.toNatChecked (pos))))


def decode_msr_imm_aarch64_instrs_system_register_cpsr (op2 : (BitVec 3)) (CRm : (BitVec 4)) (op1 : (BitVec 3)) : SailM Unit := do
  if (((op1 == 0b000#3) && (op2 == 0b000#3)) : Bool)
  then sailThrow ((Error_See "CFINV"))
  else (pure (()))
  if (((op1 == 0b000#3) && (op2 == 0b001#3)) : Bool)
  then sailThrow ((Error_See "XAFLAG"))
  else (pure (()))
  if (((op1 == 0b000#3) && (op2 == 0b010#3)) : Bool)
  then sailThrow ((Error_See "AXFLAG"))
  else (pure (()))
  (__ArmCertEndOfDecode ())
  (AArch64_CheckSystemAccess 0b00#2 op1 0b0100#4 CRm op2 0b11111#5 0#1)
  let min_EL ← (( do (undefined_bitvector_at (← occLabel 4662) 2) ) : SailM (BitVec 2) )
  let need_secure : Bool := false
  let b__0 := op1
  let (min_EL, need_secure) ← (( do
    if (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 2 1)) == (0b00#2 : (BitVec 2))) : Bool)
    then
      (let min_EL : (BitVec 2) := EL1
      (pure ((min_EL, need_secure))))
    else
      (do
        match b__0 with
        | 0b010 =>
          (let min_EL : (BitVec 2) := EL1
          (pure ((min_EL, need_secure))))
        | 0b011 =>
          (let min_EL : (BitVec 2) := EL0
          (pure ((min_EL, need_secure))))
        | 0b100 =>
          (let min_EL : (BitVec 2) := EL2
          (pure ((min_EL, need_secure))))
        | 0b101 =>
          (do
            let w__0 ← (( do (HaveVirtHostExt ()) ) : SailM Bool )
            if ((! w__0) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            let min_EL : (BitVec 2) := EL2
            (pure ((min_EL, need_secure))))
        | 0b110 =>
          (let min_EL : (BitVec 2) := EL3
          (pure ((min_EL, need_secure))))
        | _ =>
          (let min_EL : (BitVec 2) := EL1
          let need_secure : Bool := true
          (pure ((min_EL, need_secure))))) ) : SailM ((BitVec 2) × Bool) )
  let min_EL := min_EL
  let w__4 ← (( do
    if ((← do
         let w__1 ← (( do readReg PSTATE ) : SailM ProcState )
         (pure ((((BitVec.toNat w__1.EL) <b (BitVec.toNat min_EL)) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        if ((need_secure : Bool) : Bool)
        then
          (do
            let w__2 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
            (pure (((bne w__2 SS_Secure) : Bool))))
        else (pure false)) ) : SailM Bool )
  if (w__4 : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let operand : (BitVec 4) := CRm
  let field ← (( do (undefined_PSTATEField (← occLabel 4663) ()) ) : SailM PSTATEField )
  let field ← (( do
    match (BitVec.setWidth 6 (op1 +++ op2)) with
    | 0b000011 =>
      (do
        let w__5 ← (( do (HaveUAOExt ()) ) : SailM Bool )
        if ((! w__5) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_UAO)))
    | 0b000100 =>
      (do
        let w__6 ← (( do (HavePANExt ()) ) : SailM Bool )
        if ((! w__6) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_PAN)))
    | 0b000101 => (pure (PSTATEField_SP))
    | 0b001000 =>
      (do
        let b__1 := CRm
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b000#3 : (BitVec 3))) : Bool)
        then
          (do
            let w__7 ← (( do (HaveFeatNMI ()) ) : SailM Bool )
            if ((! w__7) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure (PSTATEField_ALLINT)))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__1 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
            then
              (do
                let w__8 ← (( do (HaveFeatEBEP ()) ) : SailM Bool )
                if ((! w__8) : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure (()))
                (pure (PSTATEField_PM)))
            else sailThrow ((Error_Undefined ()))))
    | 0b011010 =>
      (do
        let w__9 ← (( do (HaveDITExt ()) ) : SailM Bool )
        if ((! w__9) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_DIT)))
    | 0b011011 =>
      (do
        let b__3 := CRm
        if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b001#3 : (BitVec 3))) : Bool)
        then
          (do
            let w__10 ← (( do (HaveSME ()) ) : SailM Bool )
            if ((! w__10) : Bool)
            then sailThrow ((Error_Undefined ()))
            else (pure (()))
            (pure (PSTATEField_SVCRSM)))
        else
          (do
            if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b010#3 : (BitVec 3))) : Bool)
            then
              (do
                let w__11 ← (( do (HaveSME ()) ) : SailM Bool )
                if ((! w__11) : Bool)
                then sailThrow ((Error_Undefined ()))
                else (pure (()))
                (pure (PSTATEField_SVCRZA)))
            else
              (do
                if (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb b__3 3 1)) == (0b011#3 : (BitVec 3))) : Bool)
                then
                  (do
                    let w__12 ← (( do (HaveSME ()) ) : SailM Bool )
                    if ((! w__12) : Bool)
                    then sailThrow ((Error_Undefined ()))
                    else (pure (()))
                    (pure (PSTATEField_SVCRSMZA)))
                else sailThrow ((Error_Undefined ())))))
    | 0b011100 =>
      (do
        let w__13 ← (( do (HaveMTEExt ()) ) : SailM Bool )
        if ((! w__13) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_TCO)))
    | 0b011110 => (pure (PSTATEField_DAIFSet))
    | 0b011111 => (pure (PSTATEField_DAIFClr))
    | 0b011001 =>
      (do
        let w__14 ← (( do (HaveSSBSExt ()) ) : SailM Bool )
        if ((! w__14) : Bool)
        then sailThrow ((Error_Undefined ()))
        else (pure (()))
        (pure (PSTATEField_SSBS)))
    | _ => sailThrow ((Error_Undefined ())) ) : SailM PSTATEField )
  let w__16 ← (( do
    (pure ((← do
          let w__15 ← (( do readReg PSTATE ) : SailM ProcState )
          (pure (((w__15.EL == EL0) : Bool)))) && (((BEq.beq field PSTATEField_DAIFSet) || (BEq.beq
            field PSTATEField_DAIFClr)) : Bool))) ) : SailM Bool )
  if (w__16 : Bool)
  then
    (do
      let w__19 ← (( do
        if ((← do
             (IsInHost ())) : Bool)
        then (pure true)
        else
          (do
            let w__18 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
            (pure ((((_get_SCTLR_EL1_Type_UMA w__18) == 0#1) : Bool)))) ) : SailM Bool )
      if (w__19 : Bool)
      then
        (do
          let w__22 ← (( do
            if ((← do
                 (EL2Enabled ())) : Bool)
            then
              (do
                let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                (pure ((((_get_HCR_EL2_Type_TGE w__21) == 1#1) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__22 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else (pure (())))
  else (pure (()))
  (execute_aarch64_instrs_system_register_cpsr field operand)


end ArmFull.Functions
