module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0009
public import ArmFull.Fn.M0015
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0021
public import ArmFull.Fn.M0024
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0035
public import ArmFull.Fn.M0038
public import ArmFull.Fn.M0040
public import ArmFull.Fn.M0041
public import ArmFull.Fn.M0042
public import ArmFull.Fn.M0047
public import ArmFull.Fn.M0050
public import ArmFull.Fn.M0053
public import ArmFull.Fn.M0054
public import ArmFull.Fn.M0055
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0057
public import ArmFull.Fn.M0063
public import ArmFull.Fn.M0071
public import ArmFull.Fn.M0081
public import ArmFull.Fn.M0082
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0141
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0151
public import ArmFull.Fn.M0159
public import ArmFull.Fn.M0178
public import ArmFull.Fn.M0181
public import ArmFull.Fn.M0182
public import ArmFull.Fn.M0187
public import ArmFull.Fn.M0190
public import ArmFull.Fn.M0200
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0202
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0236
public import ArmFull.Fn.M0243
public import ArmFull.Fn.M0251
public import ArmFull.Fn.M0252
public import ArmFull.Fn.M0257
public import ArmFull.Fn.M0258
public import ArmFull.Fn.M0605
public import ArmFull.Fn.M0606
public import ArmFull.Fn.M0867
public import ArmFull.Fn.M1097
public import ArmFull.Fn.M1122
public import ArmFull.Fn.M1123
public import ArmFull.Fn.M1137
public import ArmFull.Fn.M1138
public import ArmFull.Fn.M1139 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVT_MZ2_Z__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7623)
      (Sail.Int.toNatChecked ((2 *i VL))))) ) : SailM (BitVec (2 * VL)) )
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let element ← (( do (Elem_read operand e 16) ) : SailM (BitVec 16) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res ← (( do (FPConvertSVE__1 element w__0 32) ) : SailM (BitVec 32) )
          (Elem_set result e 32 res)
      (pure loop_vars)) ) : SailM (BitVec (2 * VL)) )
  (Z_set (d +i 0) VL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked ((VL -i 1))) 0)))
  (Z_set (d +i 1) VL
    (Sail.BitVec.castWidth (Sail.BitVec.extractLsb result (Sail.Int.toNatChecked (((2 *i VL) -i 1)))
      VL)))


/-- Type quantifiers: VL : Nat, d : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FCVTL_MZ2_Z__ (VL : Nat) (d : Nat) (n : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let pairs : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 32)))
  let operand ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL) )
  let result0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7624)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7625)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let (result0, result1) ← (( do
    let loop_p_lower : Nat := 0
    let loop_p_upper : Int := (pairs -i 1)
    (do
      let mut loop_vars := (result0, result1)
      for p in [loop_p_lower:loop_p_upper:1]i do
        let (result0, result1) := loop_vars
        loop_vars ← do
          let element1 ← (( do (Elem_read operand ((2 *i p) +i 0) 16) ) : SailM (BitVec 16) )
          let element2 ← (( do (Elem_read operand ((2 *i p) +i 1) 16) ) : SailM (BitVec 16) )
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res1 ← (( do (FPConvertSVE__1 element1 w__0 32) ) : SailM (BitVec 32) )
          let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          let res2 ← (( do (FPConvertSVE__1 element2 w__1 32) ) : SailM (BitVec 32) )
          let w__2 ← (( do (Elem_set result0 p 32 res1) ) : SailM (BitVec VL) )
          let result0 := (w__2 : (BitVec VL))
          let w__3 ← (( do (Elem_set result1 p 32 res2) ) : SailM (BitVec VL) )
          let result1 := (w__3 : (BitVec VL))
          (pure ((result0, result1)))
      (pure loop_vars)) ) : SailM ((BitVec VL) × (BitVec VL)) )
  (Z_set (d +i 0) VL (Sail.BitVec.castWidth result0))
  (Z_set (d +i 1) VL (Sail.BitVec.castWidth result1))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 2 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCLAMP_MZ_ZZ_2 (VL : Nat) (d : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7626)
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
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL)
            )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (d +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
                let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
                let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (BFMaxNum (k_N := 16) element1 element3 w__1) ) : SailM
                  (BitVec 16) )
                let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__4 ← (( do (BFMinNum (k_N := 16) w__2 element2 w__3) ) : SailM (BitVec 16) )
                let w__5 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 16 w__4) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__5) : (Vector (BitVec VL) 4))
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
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, m : Nat, n : Nat, nreg : Nat, nreg = 4 ∧
  0 ≤ n ∧ n ≤ 31 ∧ 0 ≤ m ∧ m ≤ 31 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_BFCLAMP_MZ_ZZ_4 (VL : Nat) (d : Nat) (m : Nat) (n : Nat) (nreg : Nat) : SailM Unit := do
  (CheckStreamingSVEEnabled ())
  let VL : Nat := VL
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 16)))
  let w__0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 7627)
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
          let operand1 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read n VL)) ) : SailM (BitVec VL)
            )
          let operand2 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL)
            )
          let operand3 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read (d +i r) VL)) ) : SailM
            (BitVec VL) )
          let loop_e_lower : Nat := 0
          let loop_e_upper : Int := (elements -i 1)
          (do
            let mut loop_vars_1 := results
            for e in [loop_e_lower:loop_e_upper:1]i do
              let results := loop_vars_1
              loop_vars_1 ← do
                let element1 ← (( do (Elem_read operand1 e 16) ) : SailM (BitVec 16) )
                let element2 ← (( do (Elem_read operand2 e 16) ) : SailM (BitVec 16) )
                let element3 ← (( do (Elem_read operand3 e 16) ) : SailM (BitVec 16) )
                let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__2 ← (( do (BFMaxNum (k_N := 16) element1 element3 w__1) ) : SailM
                  (BitVec 16) )
                let w__3 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                let w__4 ← (( do (BFMinNum (k_N := 16) w__2 element2 w__3) ) : SailM (BitVec 16) )
                let w__5 ← (( do
                  (Elem_set (GetElem?.getElem! results (Sail.Int.toNatChecked (r))) e 16 w__4) ) :
                  SailM (BitVec VL) )
                let results :=
                  ((vectorUpdate results (Sail.Int.toNatChecked (r)) w__5) : (Vector (BitVec VL) 4))
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
        (Z_set (d +i r) VL
          (Sail.BitVec.castWidth (GetElem?.getElem! results (Sail.Int.toNatChecked (r)))))
    (pure loop_vars))


def __FetchInstr (pc : (BitVec 64)) : SailM (__InstrEnc × (BitVec 32)) := do
  let hw1 ← (( do (undefined_bitvector_at (.site 7632) 16) ) : SailM (BitVec 16) )
  let hw2 ← (( do (undefined_bitvector_at (.site 7633) 16) ) : SailM (BitVec 16) )
  let isT16 ← (( do (undefined_bool_at (.site 7634) ()) ) : SailM Bool )
  let enc ← (( do (undefined___InstrEnc (.site 7635) ()) ) : SailM __InstrEnc )
  let instr ← (( do (undefined_bitvector_at (.site 7636) 32) ) : SailM (BitVec 32) )
  let accdesc ← (( do (CreateAccDescIFetch ()) ) : SailM AccessDescriptor )
  (SetBTypeCompatible false)
  (CheckSoftwareStep ())
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  if ((w__0.nRW == 0#1) : Bool)
  then
    (do
      (AArch64_CheckPCAlignment ())
      let enc : __InstrEnc := __A64
      let w__1 ← (( do (PC_read ()) ) : SailM (BitVec 64) )
      let w__2 ← (( do (AArch64_MemSingle_read w__1 4 accdesc true) ) : SailM (BitVec (4 * 8)) )
      let instr := (w__2 : (BitVec 32))
      (AArch64_CheckIllegalState ())
      (pure ((enc, instr))))
  else
    (do
      (AArch32_CheckPCAlignment ())
      let w__3 ← (( do readReg PSTATE ) : SailM ProcState )
      let (enc, instr) ← (( do
        if ((w__3.T == 1#1) : Bool)
        then
          (do
            let hw1 ← (( do
              (AArch32_MemSingle_read (Sail.BitVec.extractLsb pc 31 0) 2 accdesc true) ) : SailM
              (BitVec 16) )
            let isT16 : Bool :=
              ((BitVec.toNat (Sail.BitVec.extractLsb hw1 15 11)) <b (BitVec.toNat 0b11101#5))
            if (isT16 : Bool)
            then
              (let enc : __InstrEnc := __T16
              let instr : (BitVec 32) := ((Zeros (n := 16)) +++ hw1)
              (pure ((enc, instr))))
            else
              (do
                let hw2 ← (( do
                  (AArch32_MemSingle_read (BitVec.addInt (Sail.BitVec.extractLsb pc 31 0) 2) 2
                    accdesc true) ) : SailM (BitVec 16) )
                let enc : __InstrEnc := __T32
                let instr : (BitVec 32) := (hw1 +++ hw2)
                (pure ((enc, instr)))))
        else
          (do
            let enc : __InstrEnc := __A32
            let w__4 ← (( do
              (AArch32_MemSingle_read (Sail.BitVec.extractLsb pc 31 0) 4 accdesc true) ) : SailM
              (BitVec (4 * 8)) )
            let instr := (w__4 : (BitVec 32))
            (pure ((enc, instr)))) ) : SailM (__InstrEnc × (BitVec 32)) )
      (AArch32_CheckIllegalState ())
      (pure ((enc, instr))))


/-- Type quantifiers: size : Nat, (size * 8) ≥ 0 -/
def Mem_read (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) : SailM (BitVec (size * 8)) := do
  let ispair : Bool := false
  let highestAddressfirst : Bool := false
  ArmFull.assert (((((size == 1) || (size == 2)) || (size == 4)) || (size == 8)) || (size == 16)) "sail-inputs/03-v8_base.sail:28178.48-28178.49"
  ((Sail.BitVec.castWidth ) <$> (Mem_read__2 address size accdesc ispair highestAddressfirst))


/-- Type quantifiers: k_ispair : Bool, size : Nat, (size * 8) ≥ 0 -/
def Mem_read__1 (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) : SailM (BitVec (size * 8)) := do
  let highestAddressfirst : Bool := false
  ArmFull.assert (((((size == 1) || (size == 2)) || (size == 4)) || (size == 8)) || (size == 16)) "sail-inputs/03-v8_base.sail:28184.48-28184.49"
  ((Sail.BitVec.castWidth ) <$> (Mem_read__2 address size accdesc ispair highestAddressfirst))


/-- Type quantifiers: size : Nat, (size * 8) ≥ 0 -/
def Mem_set (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let ispair : Bool := false
  let highestAddressfirst : Bool := false
  (Mem_set__2 address size accdesc ispair highestAddressfirst (Sail.BitVec.castWidth value_in_name))


/-- Type quantifiers: k_ispair : Bool, size : Nat, (size * 8) ≥ 0 -/
def Mem_set__1 (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let highestAddressfirst : Bool := false
  (Mem_set__2 address size accdesc ispair highestAddressfirst (Sail.BitVec.castWidth value_in_name))


/-- Type quantifiers: k_N : Nat, esize : Nat, List.elem k_N
  [8, 16, 32, 64, 128, 256, 512, 1024, 2048] ∧ List.elem esize [8, 16, 32, 64] ∧ k_N ≥ esize -/
def Reduce (op : ReduceOp) (input : (BitVec k_N)) (esize : Nat) : SailM (BitVec esize) := do
  let altfp ← (( do
    if ((← do
         if ((← do
              (HaveAltFP ())) : Bool)
         then
           (do
             let w__1 ← (( do (UsingAArch32 ()) ) : SailM Bool )
             (pure (((! w__1) : Bool))))
         else (pure false)) : Bool)
    then
      (do
        let w__3 ← (( do readReg FPCR ) : SailM (BitVec 64) )
        (pure ((((_get_FPCR_Type_AH w__3) == 1#1) : Bool))))
    else (pure false) ) : SailM Bool )
  ((Sail.BitVec.castWidth ) <$> (Reduce__1 op input esize altfp))


/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemA_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_LOAD acqrel tagchecked) ) : SailM
    AccessDescriptor )
  ((Sail.BitVec.castWidth ) <$> (Mem_with_type_read address size accdesc))


/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemA_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let acqrel : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescExLDST MemOp_STORE acqrel tagchecked) ) : SailM
    AccessDescriptor )
  (Mem_with_type_set address size accdesc (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemU_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let nontemporal : Bool := false
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_LOAD nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  ((Sail.BitVec.castWidth ) <$> (Mem_with_type_read address size accdesc))


/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemU_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let nontemporal : Bool := false
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let privileged : Bool := (w__0.EL != EL0)
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_STORE nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  (Mem_with_type_set address size accdesc (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemU_unpriv_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let nontemporal : Bool := false
  let privileged : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_LOAD nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  ((Sail.BitVec.castWidth ) <$> (Mem_with_type_read address size accdesc))


/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemU_unpriv_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let nontemporal : Bool := false
  let privileged : Bool := false
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescGPR MemOp_STORE nontemporal privileged tagchecked) ) : SailM
    AccessDescriptor )
  (Mem_with_type_set address size accdesc (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemO_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescAcqRel MemOp_LOAD tagchecked) ) : SailM AccessDescriptor )
  ((Sail.BitVec.castWidth ) <$> (Mem_with_type_read address size accdesc))


/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemO_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let tagchecked : Bool := false
  let accdesc ← (( do (CreateAccDescAcqRel MemOp_STORE tagchecked) ) : SailM AccessDescriptor )
  (Mem_with_type_set address size accdesc (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def MemS_read (address : (BitVec 32)) (size : Nat) : SailM (BitVec (8 * size)) := do
  let accdesc ← (( do (CreateAccDescA32LSMD MemOp_LOAD) ) : SailM AccessDescriptor )
  ((Sail.BitVec.castWidth ) <$> (Mem_with_type_read address size accdesc))


/-- Type quantifiers: size : Nat, (8 * size) ≥ 0 -/
def MemS_set (address : (BitVec 32)) (size : Nat) (value_name : (BitVec (8 * size))) : SailM Unit := do
  let accdesc ← (( do (CreateAccDescA32LSMD MemOp_STORE) ) : SailM AccessDescriptor )
  (Mem_with_type_set address size accdesc (Sail.BitVec.castWidth value_name))


/-- Type quantifiers: cp_num : Int, t : Int -/
def AArch32_SysRegWrite (cp_num : Int) (instr : (BitVec 32)) (t : Int) : SailM Unit := do
  let el ← (( do (undefined_bitvector_at (← occLabel 2905) 2) ) : SailM (BitVec 2) )
  let temprt ← (( do (R_read t) ) : SailM (BitVec 32) )
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let (_, __tup_1) ← (( do (ELFromM32 w__0.M) ) : SailM (Bool × (BitVec 2)) )
  let el : (BitVec 2) := __tup_1
  let opc1 : (BitVec 3) := (BitVec.slice instr 21 3)
  let CRn : (BitVec 4) := (BitVec.slice instr 16 4)
  let CRm : (BitVec 4) := (BitVec.slice instr 0 4)
  let opc2 : (BitVec 3) := (BitVec.slice instr 5 3)
  let temprt : (BitVec 32) :=
    if (((((cp_num == 14) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (opc2 == 0b101#3)) : Bool)
    then
      (let temprt : (BitVec 32) :=
        (BitVec.update temprt 8 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access temprt 7)]))))
      (BitVec.update temprt 6 (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access temprt 5)])))))
    else temprt
  let temprt ← (( do
    if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b0001#4)) && (CRm == 0b0000#4)) && (opc2 == 0b010#3)) : Bool)
    then
      (do
        let w__7 ← (( do
          if ((← do
               if ((← do
                    if ((← do
                         let w__1 ← (( do (CurrentSecurityState ()) ) : SailM SecurityState )
                         (pure (((BEq.beq w__1 SS_NonSecure) : Bool)))) : Bool)
                    then
                      (do
                        (HaveEL EL3))
                    else (pure false)) : Bool)
               then
                 (do
                   (ELUsingAArch32 EL3))
               else (pure false)) : Bool)
          then
            (do
              let w__6 ← (( do readReg NSACR ) : SailM (BitVec 32) )
              (pure ((((_get_NSACR_Type_cp10 w__6) == 0#1) : Bool))))
          else (pure false) ) : SailM Bool )
        if (w__7 : Bool)
        then
          (do
            let w__8 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
            let temprt :=
              ((Sail.BitVec.updateSubrange temprt 23 22 (_get_CPACR_Type_cp11 w__8)) : (BitVec 32))
            let w__9 ← (( do (CPACR_read__1 ()) ) : SailM (BitVec 32) )
            let temprt :=
              ((Sail.BitVec.updateSubrange temprt 21 20 (_get_CPACR_Type_cp10 w__9)) : (BitVec 32))
            (pure (temprt)))
        else (pure (temprt)))
    else (pure (temprt)) ) : SailM (BitVec 32) )
  let temprt ← (( do
    if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && ((CRm == 0b1100#4) || (CRm == 0b1110#4))) && ((opc2 == 0b001#3) || ((opc2 == 0b010#3) || (opc2 == 0b011#3)))) : Bool)
    then
      (do
        let w__10 ← (( do (PMUCounterMask ()) ) : SailM (BitVec 64) )
        let mask : (BitVec 32) := (Sail.BitVec.extractLsb w__10 31 0)
        let temprt ← (( do
          if (((opc2 == 0b011#3) && (CRm == 0b1100#4)) : Bool)
          then
            (do
              let w__11 ← (( do (PMOVSSET_read ()) ) : SailM (BitVec 32) )
              let temprt := ((w__11 &&& (Complement.complement (temprt &&& mask))) : (BitVec 32))
              (pure (temprt)))
          else (pure (temprt)) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b011#3) && (CRm == 0b1110#4)) : Bool)
          then
            (do
              let w__12 ← (( do (PMOVSSET_read ()) ) : SailM (BitVec 32) )
              let temprt := ((w__12 ||| (temprt &&& mask)) : (BitVec 32))
              (pure (temprt)))
          else (pure (temprt)) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b010#3) && (CRm == 0b1100#4)) : Bool)
          then
            (do
              let w__13 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
              let temprt := ((w__13 &&& (Complement.complement (temprt &&& mask))) : (BitVec 32))
              (pure (temprt)))
          else (pure (temprt)) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b001#3) && (CRm == 0b1100#4)) : Bool)
          then
            (do
              let w__14 ← (( do (PMCNTENSET_read ()) ) : SailM (BitVec 32) )
              let temprt := ((w__14 ||| (temprt &&& mask)) : (BitVec 32))
              (pure (temprt)))
          else (pure (temprt)) ) : SailM (BitVec 32) )
        let temprt ← (( do
          if (((opc2 == 0b010#3) && (CRm == 0b1110#4)) : Bool)
          then
            (do
              let w__15 ← (( do (PMINTENSET_read ()) ) : SailM (BitVec 32) )
              let temprt := ((w__15 &&& (Complement.complement (temprt &&& mask))) : (BitVec 32))
              (pure (temprt)))
          else (pure (temprt)) ) : SailM (BitVec 32) )
        if (((opc2 == 0b001#3) && (CRm == 0b1110#4)) : Bool)
        then
          (do
            let w__16 ← (( do (PMINTENSET_read ()) ) : SailM (BitVec 32) )
            let temprt := ((w__16 ||| (temprt &&& mask)) : (BitVec 32))
            (pure (temprt)))
        else (pure (temprt)))
    else (pure (temprt)) ) : SailM (BitVec 32) )
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then
    (do
      let w__18 ← (( do
        if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access temprt 3)])) == 1#1) : Bool) : Bool)
        then
          (do
            let w__17 ← (( do (PMCR_read ()) ) : SailM (BitVec 32) )
            (pure ((((_get_PMCR_Type_D w__17) == 0#1) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__18 : Bool)
      then
        (do
          writeReg __clock_divider 63)
      else (pure (())))
  else (pure (()))
  if (((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             CRm 3 2)) == 0b10#2) || (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb CRm 3
               2)) == 0b11#2) && ((Sail.BitVec.castWidth (m := 5) ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb
                 opc2 2 0))) != 0b11111#5)))) : Bool)
  then
    (do
      let w__30 ← (( do
        if ((← do
             (pure ((← do
                   let w__19 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                   (pure ((((BitVec.toNat
                         ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__19 -i 1)) : Bool)))) && (((Sail.BitVec.castWidth (m := 5) ((Sail.BitVec.extractLsb
                       CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) != 0b11111#5) : Bool)))) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          if ((← do
                               let w__22 ← (( do readReg PSTATE ) : SailM ProcState )
                               (pure (((w__22.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__23 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__23.EL == EL1) : Bool)))))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__26 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__26) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__28 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                (pure ((((BitVec.toNat
                      ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__28 -i 1)) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__30 : Bool)
      then
        (do
          let w__31 ← (( do (GetNumEventCounters ()) ) : SailM Int )
          if (((BitVec.toNat
                 ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0))) >b (w__31 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__32 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              if (w__32 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
      else (pure (())))
  else (pure (()))
  let w__36 ← (( do
    if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4)) : Bool) : Bool)
    then
      (do
        (pure ((← do
              if (((opc2 == 0b001#3) : Bool) : Bool)
              then
                (do
                  let w__33 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                  (pure ((((_get_PMSELR_Type_SEL w__33) != 0b11111#5) : Bool))))
              else (pure false)) || ((opc2 == 0b010#3) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__36 : Bool)
  then
    (do
      let w__51 ← (( do
        if ((← do
             if ((← do
                  let w__37 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                  let w__38 ← (( do (GetNumEventCounters ()) ) : SailM Int )
                  (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__37)) >b (w__38 -i 1)) : Bool)))) : Bool)
             then
               (do
                 let w__39 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                 (pure ((((_get_PMSELR_Type_SEL w__39) != 0b11111#5) : Bool))))
             else (pure false)) : Bool)
        then (pure true)
        else
          (do
            if ((← do
                 if ((← do
                      if ((← do
                           (EL2Enabled ())) : Bool)
                      then
                        (do
                          if ((← do
                               let w__42 ← (( do readReg PSTATE ) : SailM ProcState )
                               (pure (((w__42.EL == EL0) : Bool)))) : Bool)
                          then (pure true)
                          else
                            (do
                              let w__43 ← (( do readReg PSTATE ) : SailM ProcState )
                              (pure (((w__43.EL == EL1) : Bool)))))
                      else (pure false)) : Bool)
                 then
                   (do
                     let w__46 ← (( do readReg PMUSERENR_EL0 ) : SailM (BitVec 64) )
                     (pure ((((_get_PMUSERENR_EL0_Type_EN w__46) == 1#1) : Bool))))
                 else (pure false)) : Bool)
            then
              (do
                let w__48 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
                let w__49 ← (( do (AArch32_GetNumEventCountersAccessible ()) ) : SailM Int )
                (pure ((((BitVec.toNat (_get_PMSELR_Type_SEL w__48)) >b (w__49 -i 1)) : Bool))))
            else (pure false)) ) : SailM Bool )
      if (w__51 : Bool)
      then
        (do
          let w__52 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
          let w__53 ← (( do (GetNumEventCounters ()) ) : SailM Int )
          if (((BitVec.toNat (_get_PMSELR_Type_SEL w__52)) >b (w__53 -i 1)) : Bool)
          then sailThrow ((Error_Undefined ()))
          else
            (do
              let w__54 ← (( do (ELUsingAArch32 EL2) ) : SailM Bool )
              if (w__54 : Bool)
              then
                (do
                  (AArch32_TakeHypTrapException (BitVec.toNat 0x03#8)))
              else
                (do
                  (AArch64_AArch32SystemAccessTrap EL2 (BitVec.toNat 0x03#8)))))
      else (pure (())))
  else (pure (()))
  let temprt ← (( do
    if (((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b110#3)) && (CRn == 0b0111#4)) : Bool)
    then
      (do
        let temprt ← (( do
          if ((CRm == 0b1000#4) : Bool)
          then
            (do
              let w__55 ← (( do (DBGCLAIMCLR_read ()) ) : SailM (BitVec 32) )
              let temprt :=
                ((Sail.BitVec.updateSubrange temprt 7 0
                  ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__55 7 0)) ||| (Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                      temprt 7 0)))) : (BitVec 32))
              (pure (temprt)))
          else (pure (temprt)) ) : SailM (BitVec 32) )
        if ((CRm == 0b1001#4) : Bool)
        then
          (do
            let w__56 ← (( do (DBGCLAIMCLR_read ()) ) : SailM (BitVec 32) )
            let temprt :=
              ((Sail.BitVec.updateSubrange temprt 7 0
                ((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb w__56 7 0)) &&& (Sail.BitVec.castWidth (m := 8) (Complement.complement
                    (Sail.BitVec.extractLsb temprt 7 0))))) : (BitVec 32))
            (pure (temprt)))
        else (pure (temprt)))
    else (pure (temprt)) ) : SailM (BitVec 32) )
  let temprt2 ← (( do (R_read t) ) : SailM (BitVec 32) )
  (R_set t temprt)
  (AArch32_AutoGen_SysRegWrite32 el (integer_subrange cp_num 3 0) opc1 CRn opc2 CRm t)
  (R_set t temprt2)
  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b110#3)) && (CRn == 0b0111#4)) && (CRm == 0b1000#4)) : Bool)
  then
    (do
      let w__57 ← (( do (DBGCLAIMCLR_read ()) ) : SailM (BitVec 32) )
      (DBGCLAIMCLR_write
        (Mk_DBGCLAIMCLR_Type
          (Sail.BitVec.updateSubrange w__57 7 0 (Sail.BitVec.extractLsb temprt 7 0)))))
  else (pure (()))
  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (opc2 == 0b100#3)) && (CRn == 0b0001#4)) && (CRm == 0b0000#4)) : Bool)
  then
    (do
      if (((BitVec.toNat temprt) == (BitVec.toNat 0xC5ACCE55#32)) : Bool)
      then
        (do
          let w__58 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
          (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK w__58 1#1))
          let w__59 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
          writeReg EDPRSR (Sail.BitVec.updateSubrange w__59 5 5 1#1)
          let w__60 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
          writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__60 1 1 1#1))
      else
        (do
          let w__61 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
          if (((_get_DBGOSLSR_Type_OSLK w__61) == 1#1) : Bool)
          then
            (do
              let w__62 ← (( do (DBGOSLSR_read ()) ) : SailM (BitVec 32) )
              (DBGOSLSR_write (_update_DBGOSLSR_Type_OSLK w__62 0#1))
              let w__63 ← (( do readReg EDPRSR ) : SailM (BitVec 32) )
              writeReg EDPRSR (Sail.BitVec.updateSubrange w__63 5 5 0#1)
              let w__64 ← (( do readReg OSLSR_EL1 ) : SailM (BitVec 64) )
              writeReg OSLSR_EL1 (Sail.BitVec.updateSubrange w__64 1 1 0#1)
              (CheckOSUnlockCatch ()))
          else (pure (()))))
  else (pure (()))
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && ((CRm == 0b1100#4) || (CRm == 0b1110#4))) && ((opc2 == 0b001#3) || ((opc2 == 0b010#3) || (opc2 == 0b011#3)))) : Bool)
  then
    (do
      if (((opc2 == 0b011#3) && (CRm == 0b1100#4)) : Bool)
      then
        (do
          (PMOVSSET_write (Mk_PMOVSSET_Type temprt)))
      else (pure (()))
      if (((opc2 == 0b011#3) && (CRm == 0b1110#4)) : Bool)
      then
        (do
          (PMOVSR_write (Mk_PMOVSR_Type temprt)))
      else (pure (()))
      if (((opc2 == 0b010#3) && (CRm == 0b1100#4)) : Bool)
      then
        (do
          (PMCNTENSET_write (Mk_PMCNTENSET_Type temprt)))
      else (pure (()))
      if (((opc2 == 0b001#3) && (CRm == 0b1100#4)) : Bool)
      then
        (do
          (PMCNTENCLR_write (Mk_PMCNTENCLR_Type temprt)))
      else (pure (()))
      if (((opc2 == 0b010#3) && (CRm == 0b1110#4)) : Bool)
      then
        (do
          (PMINTENSET_write (Mk_PMINTENSET_Type temprt)))
      else (pure (()))
      if (((opc2 == 0b001#3) && (CRm == 0b1110#4)) : Bool)
      then
        (do
          (PMINTENCLR_write (Mk_PMINTENCLR_Type temprt)))
      else (pure (())))
  else (pure (()))
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then
    (do
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access temprt 2)])) == 1#1) : Bool)
      then
        (do
          (PMCCNTR_write (Mk_PMCCNTR_Type (Zeros (n := 64)))))
      else (pure (()))
      if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access temprt 1)])) == 1#1) : Bool)
      then
        (do
          (AArch32_ClearEventCounters ()))
      else (pure (())))
  else (pure (()))
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1001#4)) && (CRm == 0b1101#4)) && ((opc2 == 0b001#3) || (opc2 == 0b010#3))) : Bool)
  then
    (do
      let w__65 ← (( do (PMSELR_read ()) ) : SailM (BitVec 32) )
      let pmselr : Int := (BitVec.toNat (_get_PMSELR_Type_SEL w__65))
      if ((opc2 == 0b001#3) : Bool)
      then
        (do
          if ((pmselr == 31) : Bool)
          then
            (do
              (PMCCFILTR_write (__get_PMCCFILTR (Mk_PMCCFILTR_Type temprt))))
          else
            (do
              (PMEVTYPER_set (Sail.Int.toNatChecked (pmselr))
                (__get_PMEVTYPER (Mk_PMEVTYPER_Type temprt)))))
      else (pure (()))
      if ((opc2 == 0b010#3) : Bool)
      then
        (do
          ArmFull.assert (pmselr <b 31) "sail-inputs/12-sysregs.sail:1330.30-1330.31"
          (PMEVCNTR_set (Sail.Int.toNatChecked (pmselr)) temprt))
      else (pure (())))
  else (pure (()))
  if (((((cp_num == 15) && (opc1 == 0b000#3)) && (CRn == 0b1110#4)) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
           CRm 3 2)) == 0b11#2)) : Bool)
  then
    (do
      let index : Int :=
        (BitVec.toNat ((Sail.BitVec.extractLsb CRm 1 0) +++ (Sail.BitVec.extractLsb opc2 2 0)))
      if ((index == 31) : Bool)
      then
        (do
          (PMCCFILTR_write (__get_PMCCFILTR (Mk_PMCCFILTR_Type temprt))))
      else
        (do
          (PMEVTYPER_set (Sail.Int.toNatChecked (index))
            (__get_PMEVTYPER (Mk_PMEVTYPER_Type temprt)))))
  else (pure (()))
  if ((((((cp_num == 15) && (opc1 == 0b000#3)) && (opc2 == 0b100#3)) && (CRn == 0b1001#4)) && (CRm == 0b1100#4)) : Bool)
  then
    (do
      (AArch32_PMUSwIncrement temprt))
  else (pure (()))
  if (((((((cp_num == 15) && ((opc1 == 0b000#3) || (opc1 == 0b100#3))) && (CRn == 0b1100#4)) && (opc2 == 0b010#3)) && (CRm == 0b0000#4)) && ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
             temprt 1)])) == 1#1)) : Bool)
  then
    (do
      (TakeReset false))
  else
    (do
      if ((((((cp_num == 15) && (opc1 == 0b000#3)) && ((opc2 == 0b100#3) || (opc2 == 0b111#3))) && (CRn == 0b0000#4)) && (CRm == 0b0000#4)) : Bool)
      then
        (do
          (MIDR_write (Mk_MIDR_Type temprt)))
      else (pure (())))
  if ((((((cp_num == 14) && (opc1 == 0b000#3)) && (CRn == 0b0000#4)) && (opc2 == 0b000#3)) && (CRm == 0b0101#4)) : Bool)
  then
    (do
      let w__66 ← (( do (DBGDSCRint_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRint_write (_update_DBGDSCRint_Type_TXfull w__66 1#1))
      let w__67 ← (( do readReg MDCCSR_EL0 ) : SailM (BitVec 64) )
      writeReg MDCCSR_EL0 (Sail.BitVec.updateSubrange w__67 29 29 1#1)
      let w__68 ← (( do (DBGDSCRext_read ()) ) : SailM (BitVec 32) )
      (DBGDSCRext_write (_update_DBGDSCRext_Type_TXfull w__68 1#1))
      let w__69 ← (( do (EDSCR_read ()) ) : SailM (BitVec 32) )
      (EDSCR_write (_update_EDSCR_Type_TXfull w__69 1#1)))
  else (pure (()))


end ArmFull.Functions
