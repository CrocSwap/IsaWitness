module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0034
public import ArmFull.Fn.M0051
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0111
public import ArmFull.Fn.M0116
public import ArmFull.Fn.M0118
public import ArmFull.Fn.M0144
public import ArmFull.Fn.M0145
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0147
public import ArmFull.Fn.M0179
public import ArmFull.Fn.M0201
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0217
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0255
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0882
public import ArmFull.Fn.M1197
public import ArmFull.Fn.M1216
public import ArmFull.Fn.M1217 set_option backward.proofsInPublic true @[expose] public section

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

def decode_FMMLA_Z_ZZZ_D (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveSVEFP64MatMulExt ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let esize : Nat := 64
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMMLA_Z_ZZZ_D 128 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMMLA_Z_ZZZ_D 256 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMMLA_Z_ZZZ_D 512 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMMLA_Z_ZZZ_D 1024 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_FMMLA_Z_ZZZ_D 2048 (Sail.Int.toNatChecked (da)) esize (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


def decode_BFMMLA_Z_ZZZ__ (Zm : (BitVec 5)) (Zn : (BitVec 5)) (Zda : (BitVec 5)) : SailM Unit := do
  let VL ← (( do (CurrentVL_read ()) ) : SailM Int )
  let w__2 ← (( do
    if ((← do
         let w__0 ← (( do (HaveSVE ()) ) : SailM Bool )
         (pure (((! w__0) : Bool)))) : Bool)
    then (pure true)
    else
      (do
        let w__1 ← (( do (HaveBF16Ext ()) ) : SailM Bool )
        (pure (((! w__1) : Bool)))) ) : SailM Bool )
  if (w__2 : Bool)
  then
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))
  else
    (do
      let n : Int := (BitVec.toNat Zn)
      let m : Int := (BitVec.toNat Zm)
      let da : Int := (BitVec.toNat Zda)
      match VL with
      | 128 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMMLA_Z_ZZZ__ 128 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 256 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMMLA_Z_ZZZ__ 256 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 512 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMMLA_Z_ZZZ__ 512 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 1024 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMMLA_Z_ZZZ__ 1024 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | 2048 =>
        (do
          (__ArmCertEndOfDecode ())
          (execute_BFMMLA_Z_ZZZ__ 2048 (Sail.Int.toNatChecked (da)) (Sail.Int.toNatChecked (m))
            (Sail.Int.toNatChecked (n))))
      | _ => (pure (())))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FADDQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:11326.45-11326.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 esize)) ) : SailM (BitVec esize)
    )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← (( do (CeilPow2 (segments *i esize)) ) : SailM Nat )
  let p2elems : Int := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let stmp ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5170)
              (Sail.Int.toNatChecked (p2bits)))) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          let stmp ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (p2elems -i 1)
            (do
              let mut loop_vars_1 := stmp
              for s in [loop_s_lower:loop_s_upper:1]i do
                let stmp := loop_vars_1
                loop_vars_1 ← do
                  let w__3 ← (( do
                    if (((s <b segments) : Bool) : Bool)
                    then
                      (do
                        (ActivePredicateElement mask ((s *i elempersegment) +i e) esize))
                    else (pure false) ) : SailM Bool )
                  if (w__3 : Bool)
                  then
                    (do
                      let w__4 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand
                          ((s *i elempersegment) +i e) esize)) ) : SailM (BitVec esize) )
                      (Elem_set stmp s esize (Sail.BitVec.castWidth w__4)))
                  else
                    (do
                      (Elem_set stmp s esize (Sail.BitVec.castWidth identity)))
              (pure loop_vars_1)) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          ArmFull.assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "sail-inputs/16-instrs64_sve.sail:11340.129-11340.130"
          let dtmp ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce ReduceOp_FADD stmp esize)) ) :
            SailM (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth dtmp)))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXNMQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:11405.45-11405.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN esize)) ) : SailM
    (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← (( do (CeilPow2 (segments *i esize)) ) : SailM Nat )
  let p2elems : Int := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let stmp ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5171)
              (Sail.Int.toNatChecked (p2bits)))) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          let stmp ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (p2elems -i 1)
            (do
              let mut loop_vars_1 := stmp
              for s in [loop_s_lower:loop_s_upper:1]i do
                let stmp := loop_vars_1
                loop_vars_1 ← do
                  let w__3 ← (( do
                    if (((s <b segments) : Bool) : Bool)
                    then
                      (do
                        (ActivePredicateElement mask ((s *i elempersegment) +i e) esize))
                    else (pure false) ) : SailM Bool )
                  if (w__3 : Bool)
                  then
                    (do
                      let w__4 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand
                          ((s *i elempersegment) +i e) esize)) ) : SailM (BitVec esize) )
                      (Elem_set stmp s esize (Sail.BitVec.castWidth w__4)))
                  else
                    (do
                      (Elem_set stmp s esize (Sail.BitVec.castWidth identity)))
              (pure loop_vars_1)) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          ArmFull.assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "sail-inputs/16-instrs64_sve.sail:11419.129-11419.130"
          let dtmp ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce ReduceOp_FMAXNUM stmp esize)) ) :
            SailM (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth dtmp)))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINNMQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:11484.45-11484.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPDefaultNaN esize)) ) : SailM
    (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← (( do (CeilPow2 (segments *i esize)) ) : SailM Nat )
  let p2elems : Int := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let stmp ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5172)
              (Sail.Int.toNatChecked (p2bits)))) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          let stmp ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (p2elems -i 1)
            (do
              let mut loop_vars_1 := stmp
              for s in [loop_s_lower:loop_s_upper:1]i do
                let stmp := loop_vars_1
                loop_vars_1 ← do
                  let w__3 ← (( do
                    if (((s <b segments) : Bool) : Bool)
                    then
                      (do
                        (ActivePredicateElement mask ((s *i elempersegment) +i e) esize))
                    else (pure false) ) : SailM Bool )
                  if (w__3 : Bool)
                  then
                    (do
                      let w__4 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand
                          ((s *i elempersegment) +i e) esize)) ) : SailM (BitVec esize) )
                      (Elem_set stmp s esize (Sail.BitVec.castWidth w__4)))
                  else
                    (do
                      (Elem_set stmp s esize (Sail.BitVec.castWidth identity)))
              (pure loop_vars_1)) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          ArmFull.assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "sail-inputs/16-instrs64_sve.sail:11498.129-11498.130"
          let dtmp ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce ReduceOp_FMINNUM stmp esize)) ) :
            SailM (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth dtmp)))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMAXQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:11563.45-11563.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPInfinity 1#1 esize)) ) : SailM
    (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← (( do (CeilPow2 (segments *i esize)) ) : SailM Nat )
  let p2elems : Int := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let stmp ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5173)
              (Sail.Int.toNatChecked (p2bits)))) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          let stmp ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (p2elems -i 1)
            (do
              let mut loop_vars_1 := stmp
              for s in [loop_s_lower:loop_s_upper:1]i do
                let stmp := loop_vars_1
                loop_vars_1 ← do
                  let w__3 ← (( do
                    if (((s <b segments) : Bool) : Bool)
                    then
                      (do
                        (ActivePredicateElement mask ((s *i elempersegment) +i e) esize))
                    else (pure false) ) : SailM Bool )
                  if (w__3 : Bool)
                  then
                    (do
                      let w__4 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand
                          ((s *i elempersegment) +i e) esize)) ) : SailM (BitVec esize) )
                      (Elem_set stmp s esize (Sail.BitVec.castWidth w__4)))
                  else
                    (do
                      (Elem_set stmp s esize (Sail.BitVec.castWidth identity)))
              (pure loop_vars_1)) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          ArmFull.assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "sail-inputs/16-instrs64_sve.sail:11577.129-11577.130"
          let dtmp ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce ReduceOp_FMAX stmp esize)) ) :
            SailM (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth dtmp)))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, g : Nat, n : Nat, 0 ≤ n ∧
  n ≤ 31 ∧
  List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧
  List.elem esize [8, 16, 32, 64] ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_FMINQV_Z_P_Z__ (VL : Nat) (d : Nat) (esize : Nat) (g : Nat) (n : Nat) : SailM Unit := do
  (CheckSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let segments : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 128)))
  let elempersegment : Nat := (Sail.Int.toNatChecked ((Int.ediv 128 esize)))
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let operand ← (( do
    if (w__0 : Bool)
    then
      (do
        ((Sail.BitVec.castWidth ) <$> (Z_read n VL)))
    else (pure ((Sail.BitVec.castWidth (Zeros (n := VL))))) ) : SailM (BitVec VL) )
  ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-inputs/16-instrs64_sve.sail:11642.45-11642.46"
  let identity ← (( do ((Sail.BitVec.castWidth ) <$> (FPInfinity 0#1 esize)) ) : SailM
    (BitVec esize) )
  let result : (BitVec 128) := (Zeros (n := 128))
  let p2bits ← (( do (CeilPow2 (segments *i esize)) ) : SailM Nat )
  let p2elems : Int := (Int.ediv p2bits esize)
  let result ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elempersegment -i 1)
    (do
      let mut loop_vars := result
      for e in [loop_e_lower:loop_e_upper:1]i do
        let result := loop_vars
        loop_vars ← do
          let stmp ← (( do
            ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5174)
              (Sail.Int.toNatChecked (p2bits)))) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          let stmp ← (( do
            let loop_s_lower : Nat := 0
            let loop_s_upper : Int := (p2elems -i 1)
            (do
              let mut loop_vars_1 := stmp
              for s in [loop_s_lower:loop_s_upper:1]i do
                let stmp := loop_vars_1
                loop_vars_1 ← do
                  let w__3 ← (( do
                    if (((s <b segments) : Bool) : Bool)
                    then
                      (do
                        (ActivePredicateElement mask ((s *i elempersegment) +i e) esize))
                    else (pure false) ) : SailM Bool )
                  if (w__3 : Bool)
                  then
                    (do
                      let w__4 ← (( do
                        ((Sail.BitVec.castWidth ) <$> (Elem_read operand
                          ((s *i elempersegment) +i e) esize)) ) : SailM (BitVec esize) )
                      (Elem_set stmp s esize (Sail.BitVec.castWidth w__4)))
                  else
                    (do
                      (Elem_set stmp s esize (Sail.BitVec.castWidth identity)))
              (pure loop_vars_1)) ) : SailM (BitVec (Sail.Int.toNatChecked p2bits)) )
          ArmFull.assert ((((((((((p2bits == 16) || (p2bits == 32)) || (p2bits == 64)) || (p2bits == 128)) || (p2bits == 256)) || (p2bits == 512)) || (p2bits == 1024)) || (p2bits == 2048)) && (p2bits ≥b esize)) || (! (((esize == 16) || (esize == 32)) || (esize == 64)))) "sail-inputs/16-instrs64_sve.sail:11656.129-11656.130"
          let dtmp ← (( do ((Sail.BitVec.castWidth ) <$> (Reduce ReduceOp_FMIN stmp esize)) ) :
            SailM (BitVec esize) )
          ((Sail.BitVec.castWidth ) <$> (Elem_set result e esize (Sail.BitVec.castWidth dtmp)))
      (pure loop_vars)) ) : SailM (BitVec 128) )
  (V_set d 128 result)


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n
  : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  scale = 0 ∧
  offs_size = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 8 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1B_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 5753) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5754)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5755)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5756)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__6 : (BitVec VL))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, result) := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
                (BitVec esize) )
              let off ← (( do
                (asl_Int (Sail.BitVec.extractLsb w__8 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                  offs_unsigned) ) : SailM Int )
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (msize / 8 * 8)) )
              let data := ((Sail.BitVec.castWidth w__9) : (BitVec msize))
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) :
                SailM (BitVec esize) )
              let w__11 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__10)) ) : SailM
                (BitVec VL) )
              let result := (w__11 : (BitVec VL))
              (pure ((data, result))))
          else
            (do
              let w__12 ← (( do
                (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM
                (BitVec VL) )
              let result := (w__12 : (BitVec VL))
              (pure ((data, result))))
      (pure loop_vars)) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL (Sail.BitVec.castWidth result))


/-- Type quantifiers: VL : Nat, esize : Nat, g : Nat, k_is_unsigned : Bool, m : Nat, msize : Nat, n
  : Nat, offs_size : Nat, k_offs_unsigned : Bool, scale : Nat, t : Nat, 0 ≤ t ∧
  t ≤ 31 ∧
  scale = 0 ∧
  offs_size = 32 ∧
  0 ≤ n ∧
  n ≤ 31 ∧
  msize = 8 ∧
  0 ≤ m ∧ m ≤ 31 ∧ List.elem g [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 32 ∧ (is_VL VL) -/
def execute_LD1SB_Z_P_BZ_S_x32_unscaled (VL : Nat) (esize : Nat) (g : Nat) (m : Nat) (msize : Nat) (n : Nat) (offs_size : Nat) (offs_unsigned : Bool) (scale : Nat) (t : Nat) (is_unsigned : Bool) : SailM Unit := do
  (CheckNonStreamingSVEEnabled ())
  let VL : Nat := VL
  let PL : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let elements : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let base ← (( do (undefined_bitvector_at (← occLabel 5757) 64) ) : SailM (BitVec 64) )
  let mask ← (( do ((Sail.BitVec.castWidth ) <$> (P_read g PL)) ) : SailM
    (BitVec (Sail.Int.toNatChecked PL)) )
  let offset ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5758)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5759)
      (Sail.Int.toNatChecked (VL)))) ) : SailM (BitVec VL) )
  let data ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 5760)
      (Sail.Int.toNatChecked (msize)))) ) : SailM (BitVec msize) )
  let mbytes : Nat := (Sail.Int.toNatChecked ((Int.ediv msize 8)))
  let contiguous : Bool := false
  let nontemporal : Bool := false
  let tagchecked : Bool := true
  let accdesc ← (( do (CreateAccDescSVE MemOp_LOAD nontemporal contiguous tagchecked) ) : SailM
    AccessDescriptor )
  let w__0 ← (( do (AnyActiveElement mask esize) ) : SailM Bool )
  let (base, offset) ← (( do
    if ((! w__0) : Bool)
    then
      (do
        let w__2 ← (( do
          if (((n == 31) : Bool) : Bool)
          then
            (do
              (ConstrainUnpredictableBool Unpredictable_CHECKSPNONEACTIVE))
          else (pure false) ) : SailM Bool )
        if (w__2 : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        (pure ((base, offset))))
    else
      (do
        if ((n == 31) : Bool)
        then
          (do
            (CheckSPAlignment ()))
        else (pure (()))
        let w__5 ← (( do
          if ((n == 31) : Bool)
          then
            (do
              (SP_read ()))
          else
            (do
              (X_read n 64)) ) : SailM (BitVec 64) )
        let base := (w__5 : (BitVec 64))
        let w__6 ← (( do ((Sail.BitVec.castWidth ) <$> (Z_read m VL)) ) : SailM (BitVec VL) )
        let offset := (w__6 : (BitVec VL))
        (pure ((base, offset)))) ) : SailM ((BitVec 64) × (BitVec VL)) )
  let (data, result) ← (( do
    let loop_e_lower : Nat := 0
    let loop_e_upper : Int := (elements -i 1)
    (do
      let mut loop_vars := (data, result)
      for e in [loop_e_lower:loop_e_upper:1]i do
        let (data, result) := loop_vars
        loop_vars ← do
          let w__7 ← (( do (ActivePredicateElement mask e esize) ) : SailM Bool )
          if (w__7 : Bool)
          then
            (do
              let w__8 ← (( do ((Sail.BitVec.castWidth ) <$> (Elem_read offset e esize)) ) : SailM
                (BitVec esize) )
              let off ← (( do
                (asl_Int (Sail.BitVec.extractLsb w__8 (Sail.Int.toNatChecked ((offs_size -i 1))) 0)
                  offs_unsigned) ) : SailM Int )
              let addr : (BitVec 64) := (BitVec.addInt base (Int.shiftl off scale))
              let w__9 ← (( do ((Sail.BitVec.castWidth ) <$> (Mem_read addr mbytes accdesc)) ) :
                SailM (BitVec (msize / 8 * 8)) )
              let data := ((Sail.BitVec.castWidth w__9) : (BitVec msize))
              let w__10 ← (( do ((Sail.BitVec.castWidth ) <$> (Extend data esize is_unsigned)) ) :
                SailM (BitVec esize) )
              let w__11 ← (( do (Elem_set result e esize (Sail.BitVec.castWidth w__10)) ) : SailM
                (BitVec VL) )
              let result := (w__11 : (BitVec VL))
              (pure ((data, result))))
          else
            (do
              let w__12 ← (( do
                (Elem_set result e esize (Sail.BitVec.castWidth (Zeros (n := esize)))) ) : SailM
                (BitVec VL) )
              let result := (w__12 : (BitVec VL))
              (pure ((data, result))))
      (pure loop_vars)) ) : SailM ((BitVec msize) × (BitVec VL)) )
  (Z_set t VL (Sail.BitVec.castWidth result))


end ArmFull.Functions
