module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0017
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0100
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0165
public import ArmFull.Fn.M0193
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0226
public import ArmFull.Fn.M0235
public import ArmFull.Fn.M0242
public import ArmFull.Fn.M0243
public import ArmFull.Fn.M0602
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0605 set_option backward.proofsInPublic true @[expose] public section

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

def decode_subg_aarch64_instrs_integer_tags_mcsubtag (Xd : (BitVec 5)) (Xn : (BitVec 5)) (uimm4 : (BitVec 4)) (op3 : (BitVec 2)) (uimm6 : (BitVec 6)) : SailM Unit := do
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
      let tag_offset : (BitVec 4) := uimm4
      let offset : (BitVec 64) := ((Sail.BitVec.zeroExtend uimm6 64) <<< LOG2_TAG_GRANULE)
      let ADD : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_tags_mcsubtag ADD (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (n)) offset tag_offset))


def decode_subp_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
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
      let setflags : Bool := false
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddress
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))


def decode_subps_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags (Xd : (BitVec 5)) (Xn : (BitVec 5)) (Xm : (BitVec 5)) : SailM Unit := do
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
      let setflags : Bool := true
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_pointer_mcsubtracttaggedaddresssetflags
        (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n)) setflags))


def decode_svc_aarch64_instrs_system_exceptions_runtime_svc (imm16 : (BitVec 16)) : SailM Unit := do
  let imm : (BitVec 16) := imm16
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_system_exceptions_runtime_svc imm)


def decode_tbnz_aarch64_instrs_branch_conditional_test (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((b5 == 1#1) : Bool)
    then 64
    else 32
  let bit_pos : Int := (BitVec.toNat (b5 +++ b40))
  let bit_val : (BitVec 1) := op
  let offset : (BitVec 64) := (sign_extend (imm14 +++ 0b00#2) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_conditional_test (Sail.Int.toNatChecked (bit_pos)) bit_val
    (Sail.Int.toNatChecked (datasize)) offset (Sail.Int.toNatChecked (t)))


def decode_tbz_aarch64_instrs_branch_conditional_test (Rt : (BitVec 5)) (imm14 : (BitVec 14)) (b40 : (BitVec 5)) (op : (BitVec 1)) (b5 : (BitVec 1)) : SailM Unit := do
  let t : Int := (BitVec.toNat Rt)
  let datasize : Int :=
    if ((b5 == 1#1) : Bool)
    then 64
    else 32
  let bit_pos : Int := (BitVec.toNat (b5 +++ b40))
  let bit_val : (BitVec 1) := op
  let offset : (BitVec 64) := (sign_extend (imm14 +++ 0b00#2) 64)
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_branch_conditional_test (Sail.Int.toNatChecked (bit_pos)) bit_val
    (Sail.Int.toNatChecked (datasize)) offset (Sail.Int.toNatChecked (t)))


def decode_tcancel_aarch64_instrs_system_tme_tcancel (imm16 : (BitVec 16)) : SailM Unit := do
  let w__0 ← (( do (HaveTME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let retry : Bool := ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access imm16 15)])) == 1#1)
      let reason : (BitVec 15) := (Sail.BitVec.extractLsb imm16 14 0)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_system_tme_tcancel reason retry))


def decode_tcommit_aarch64_instrs_system_tme_tcommit (_ : Unit) : SailM Unit := do
  let w__0 ← (( do (HaveTME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_system_tme_tcommit ()))


def decode_tstart_aarch64_instrs_system_tme_tstart (Rt : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__0 ← (( do (HaveTME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Rt)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_tme_tstart 128 (Sail.Int.toNatChecked (t))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_tme_tstart 256 (Sail.Int.toNatChecked (t))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_tme_tstart 512 (Sail.Int.toNatChecked (t))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_tme_tstart 1024 (Sail.Int.toNatChecked (t))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_system_tme_tstart 2048 (Sail.Int.toNatChecked (t))))
      | _ => (pure (())))


def decode_ttest_aarch64_instrs_system_tme_ttest (Rt : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveTME ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let t : Int := (BitVec.toNat Rt)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_system_tme_ttest (Sail.Int.toNatChecked (t))))


def decode_udf_perm_undef_aarch64_instrs_udf (imm16 : (BitVec 16)) : SailM Unit := do
  (__ArmCertEndOfDecode ())
  sailThrow ((Error_Undefined ()))


def decode_umax_imm_aarch64_instrs_integer_arithmetic_max_min_umax_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
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
      let imm : Int := (BitVec.toNat imm8)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_umax_imm (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n))))


def decode_umax_reg_aarch64_instrs_integer_arithmetic_max_min_umax_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_umax_reg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_umin_reg_aarch64_instrs_integer_arithmetic_max_min_umin_reg (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (sf : (BitVec 1)) : SailM Unit := do
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
      let m : Int := (BitVec.toNat Rm)
      let d : Int := (BitVec.toNat Rd)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_umin_reg (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m)) (Sail.Int.toNatChecked (n))))


def decode_umin_imm_aarch64_instrs_integer_arithmetic_max_min_umin_imm (Rd : (BitVec 5)) (Rn : (BitVec 5)) (imm8 : (BitVec 8)) (sf : (BitVec 1)) : SailM Unit := do
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
      let imm : Int := (BitVec.toNat imm8)
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_arithmetic_max_min_umin_imm (Sail.Int.toNatChecked (d))
        (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (imm)) (Sail.Int.toNatChecked (n))))


/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_system_sysinstwithreg_wfet (d : Nat) : SailM Unit := do
  let w__0 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let localtimeout : Int := (BitVec.toNat w__0)
  let w__3 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_WFxTDEBUG))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  (Hint_WFE localtimeout WFxType_WFET)


/-- Type quantifiers: d : Nat, 0 ≤ d ∧ d ≤ 31 -/
def execute_aarch64_instrs_system_sysinstwithreg_wfit (d : Nat) : SailM Unit := do
  let w__0 ← (( do (X_read d 64) ) : SailM (BitVec 64) )
  let localtimeout : Int := (BitVec.toNat w__0)
  let w__3 ← (( do
    if ((← do
         (Halted ())) : Bool)
    then
      (do
        (ConstrainUnpredictableBool Unpredictable_WFxTDEBUG))
    else (pure false) ) : SailM Bool )
  if (w__3 : Bool)
  then
    (do
      (EndOfInstruction ()))
  else (pure (()))
  (Hint_WFI localtimeout WFxType_WFIT)


def decode_xaflag_aarch64_instrs_integer_flags_xaflag (CRm : (BitVec 4)) : SailM Unit := do
  let w__0 ← (( do (HaveFlagFormatExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      (__ArmCertEndOfDecode ())
      (execute_aarch64_instrs_integer_flags_xaflag ()))


def decode_xpac_aarch64_instrs_integer_pac_strip_dp_1src (Rd : (BitVec 5)) (Rn : (BitVec 5)) (D : (BitVec 1)) : SailM Unit := do
  let data : Bool := (D == 1#1)
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let w__0 ← (( do (HavePACExt ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      if ((n != 31) : Bool)
      then
        (do
          (__ArmCertEndOfDecode ())
          sailThrow ((Error_Undefined ())))
      else
        (do
          (__ArmCertEndOfDecode ())
          (execute_aarch64_instrs_integer_pac_strip_dp_1src (Sail.Int.toNatChecked (d)) data)))


def decode_xpac_aarch64_instrs_integer_pac_strip_hint (_ : Unit) : SailM Unit := do
  let d : Nat := 30
  let data : Bool := false
  (__ArmCertEndOfDecode ())
  (execute_aarch64_instrs_integer_pac_strip_dp_1src d data)


/-- Type quantifiers: SVL : Nat, dim_dim_esize : Nat, esize : Nat, esize = 64 ∧
  (is_VL SVL) ∧ dim_dim_esize = (SVL / esize * (SVL / esize * esize)) -/
def execute_ZERO_ZA_I__ (SVL : Nat) (dim_dim_esize : Nat) (esize : Nat) (mask : (BitVec 8)) : SailM Unit := do
  (CheckSMEAndZAEnabled ())
  let SVL : Nat := SVL
  let dim : Nat := (Sail.Int.toNatChecked ((Int.ediv SVL esize)))
  let result : (BitVec dim_dim_esize) := (Sail.BitVec.castWidth (Zeros (n := dim_dim_esize)))
  let w__2 ← (( do
    if ((← do
         (HaveTME ())) : Bool)
    then
      (do
        let w__1 ← (( do readReg TSTATE ) : SailM TMState )
        (pure (((w__1.depth >b 0) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (FailTransaction TMFailure_ERR false))
  else (pure (()))
  let loop_i_lower : Nat := 0
  let loop_i_upper : Nat := 7
  (do
    let mut loop_vars := ()
    for i in [loop_i_lower:loop_i_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access mask (Sail.Int.toNatChecked (i)))])) == 1#1) : Bool)
        then
          (do
            (ZAtile_set SVL i esize dim_dim_esize (Sail.BitVec.castWidth result)))
        else (pure (()))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7466)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
                let res : Int := (Max.max element1 element2)
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))) ) : SailM
                  (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_MZ_ZZW_2x2 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7467)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
                let res : Int := (Max.max element1 element2)
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))) ) : SailM
                  (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7468)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
                let res : Int := (Max.max element1 element2)
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))) ) : SailM
                  (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg
  = 2 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_SMAX_MZ_ZZV_2x1 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7469)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
                let res : Int := (Max.max element1 element2)
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))) ) : SailM
                  (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, dn : Nat, esize : Nat, k_is_unsigned : Bool, m : Nat, nreg : Nat, nreg
  = 4 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem esize [8, 16, 32, 64] ∧ 0 ≤ dn ∧ dn ≤ 31 ∧ (is_VL VL) -/
def execute_UMAX_MZ_ZZW_4x4 (VL : Nat) (dn : Nat) (esize : Nat) (m : Nat) (nreg : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7470)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let results ← (( do (undefined_vector 4 w__0) ) : SailM (Vector (BitVec VL) 4) )
  let results ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := results
      for r in [loop_r_lower:loop_r_upper:1]i do
        let results := loop_vars
        loop_vars ← do
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (dn +i r) VL)) ) : SailM
            (BitVec VL) )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (m +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let w__1 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand1 e esize)) ) :
                  SailM (BitVec esize) )
                let element1 ← (( do (asl_Int w__1 is_unsigned) ) : SailM Int )
                let w__2 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read operand2 e esize)) ) :
                  SailM (BitVec esize) )
                let element2 ← (( do (asl_Int w__2 is_unsigned) ) : SailM Int )
                let res : Int := (Max.max element1 element2)
                let w__3 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e esize
                    (Sail.BitVec.castWidth (integer_subrange res (esize -i 1) 0))) ) : SailM
                  (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__3) : (Vector (BitVec VL) 4))
                (pure (results))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM (Vector (BitVec VL) 4) )
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        (Z_set (dn +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


end ArmFull.Functions
