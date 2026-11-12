import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0000
import ArmFull.Fn.M0009
import ArmFull.Fn.M0010
import ArmFull.Fn.M0016
import ArmFull.Fn.M0018
import ArmFull.Fn.M0022
import ArmFull.Fn.M0023
import ArmFull.Fn.M0051
import ArmFull.Fn.M0092
import ArmFull.Fn.M0116
import ArmFull.Fn.M0117
import ArmFull.Fn.M0120
import ArmFull.Fn.M0145
import ArmFull.Fn.M0146
import ArmFull.Fn.M0150
import ArmFull.Fn.M0154
import ArmFull.Fn.M0155
import ArmFull.Fn.M0168
import ArmFull.Fn.M0178
import ArmFull.Fn.M0181
import ArmFull.Fn.M0216
import ArmFull.Fn.M0217
import ArmFull.Fn.M0254
import ArmFull.Fn.M0255
import ArmFull.Fn.M1002
import ArmFull.Fn.M1040
import ArmFull.Fn.M1043
import ArmFull.Fn.M1071
import ArmFull.Fn.M1072
import ArmFull.Fn.M1073

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

/-- Type quantifiers: k_highestAddressfirst : Bool, k_ispair : Bool, size : Nat, (size * 8) ≥ 0 -/
def Mem_set__2 (address : (BitVec 64)) (size : Nat) (accdesc : AccessDescriptor) (ispair : Bool) (highestAddressfirst : Bool) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let c ← (( do (undefined_Constraint (← occLabel 1646) ()) ) : SailM Constraint )
  let joinedpair ← (( do (undefined_bool_at (← occLabel 1647) ()) ) : SailM Bool )
  let halfsize : Nat := (Sail.Int.toNatChecked ((Int.ediv size 2)))
  let value_name : (BitVec (size * 8)) := value_in_name
  let alignment : Int :=
    if (ispair : Bool)
    then halfsize
    else size
  let aligned : Bool := (IsAligned__1 address alignment)
  let w__1 ← (( do
    if (((! aligned) : Bool) : Bool)
    then
      (do
        (AArch64_UnalignedAccessFaults accdesc address size))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      let w__2 ← (( do (AlignmentFault accdesc) ) : SailM FaultRecord )
      (AArch64_Abort address w__2))
  else (pure (()))
  let w__3 ← (( do (BigEndian accdesc.acctype) ) : SailM Bool )
  let value_name ← (( do
    if (w__3 : Bool)
    then
      (do
        ArmFull.assert (((size *i 8) == 8) || (((size *i 8) == 16) || (((size *i 8) == 32) || (((size *i 8) == 64) || ((size *i 8) == 128))))) "sail-arm/v8_base.sail:28271.116-28271.117"
        let value_name : (BitVec (size * 8)) := (reverse_endianness value_name)
        (pure (value_name)))
    else (pure (value_name)) ) : SailM (BitVec (size * 8)) )
  if ((((BEq.beq accdesc.acctype AccessType_ASIMD) && (size == 16)) && (IsAligned__1 address 8)) : Bool)
  then
    (do
      ArmFull.assert (halfsize >b 0) "sail-arm/v8_base.sail:28275.27-28275.28"
      let highhalf ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1652)
          (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
        (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
      let lowhalf ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1653)
          (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
        (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
      let highhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name 127 64))
      let lowhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name 63 0))
      (AArch64_MemSingle_set__1 address halfsize accdesc aligned ispair
        (Sail.BitVec.castWidth lowhalf))
      (AArch64_MemSingle_set__1 (BitVec.addInt address halfsize) halfsize accdesc aligned ispair
        (Sail.BitVec.castWidth highhalf)))
  else
    (do
      let w__6 ← (( do
        if ((← do
             (HaveLSE2Ext ())) : Bool)
        then
          (do
            (AllInAlignedQuantity address size 16))
        else (pure false) ) : SailM Bool )
      if (w__6 : Bool)
      then
        (do
          ArmFull.assert (((((size == 1) || (size == 2)) || (size == 4)) || (size == 8)) || (size == 16)) "sail-arm/v8_base.sail:28282.52-28282.53"
          (AArch64_MemSingle_set__1 address size accdesc aligned ispair
            (Sail.BitVec.castWidth value_name)))
      else
        (do
          if ((ispair && aligned) : Bool)
          then
            (do
              let joinedpair : Bool := false
              ArmFull.assert (halfsize >b 0) "sail-arm/v8_base.sail:28286.27-28286.28"
              let highhalf ← (( do
                ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1650)
                  (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
              let lowhalf ← (( do
                ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1651)
                  (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
              ArmFull.assert ((size *i 8) == ((halfsize *i 8) +i (halfsize *i 8))) "sail-arm/v8_base.sail:28289.69-28289.70"
              let highhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
                (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                  (Sail.Int.toNatChecked (((size *i 8) -i 1)))
                  (Sail.Int.toNatChecked (((((size *i 8) -i 1) -i (halfsize *i 8)) +i 1)))))
              let lowhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
                (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                  (Sail.Int.toNatChecked ((((size *i 8) -i 1) -i (halfsize *i 8))))
                  (Sail.Int.toNatChecked ((((((size *i 8) -i 1) -i (halfsize *i 8)) -i (halfsize *i 8)) +i 1)))))
              let w__8 ← (( do
                (pure ((← do
                      (HaveLRCPC3Ext ())) && (highestAddressfirst : Bool))) ) : SailM Bool )
              if (w__8 : Bool)
              then
                (do
                  ArmFull.assert (((((halfsize == 1) || (halfsize == 2)) || (halfsize == 4)) || (halfsize == 8)) || (halfsize == 16)) "sail-arm/v8_base.sail:28292.60-28292.61"
                  (AArch64_MemSingle_set__1 (BitVec.addInt address halfsize) halfsize accdesc
                    aligned joinedpair (Sail.BitVec.castWidth highhalf))
                  (AArch64_MemSingle_set__1 address halfsize accdesc aligned joinedpair
                    (Sail.BitVec.castWidth lowhalf)))
              else
                (do
                  ArmFull.assert (((((halfsize == 1) || (halfsize == 2)) || (halfsize == 4)) || (halfsize == 8)) || (halfsize == 16)) "sail-arm/v8_base.sail:28296.60-28296.61"
                  (AArch64_MemSingle_set__1 address halfsize accdesc aligned joinedpair
                    (Sail.BitVec.castWidth lowhalf))
                  (AArch64_MemSingle_set__1 (BitVec.addInt address halfsize) halfsize accdesc
                    aligned joinedpair (Sail.BitVec.castWidth highhalf))))
          else
            (do
              if (aligned : Bool)
              then
                (do
                  ArmFull.assert (((((size == 1) || (size == 2)) || (size == 4)) || (size == 8)) || (size == 16)) "sail-arm/v8_base.sail:28301.52-28301.53"
                  (AArch64_MemSingle_set__1 address size accdesc aligned ispair
                    (Sail.BitVec.castWidth value_name)))
              else
                (do
                  ArmFull.assert (size >b 1) "sail-arm/v8_base.sail:28304.23-28304.24"
                  let highhalf ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1648)
                      (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                    (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                  let lowhalf ← (( do
                    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1649)
                      (Sail.Int.toNatChecked ((halfsize *i 8))))) ) : SailM
                    (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) )
                  let w__11 ← (( do
                    (pure ((← do
                          (pure ((← do
                                (HaveLRCPC3Ext ())) && (ispair : Bool)))) && (highestAddressfirst : Bool)))
                    ) : SailM Bool )
                  if (w__11 : Bool)
                  then
                    (do
                      ArmFull.assert ((size *i 8) == ((halfsize *i 8) +i (halfsize *i 8))) "sail-arm/v8_base.sail:28308.73-28308.74"
                      let highhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                          (Sail.Int.toNatChecked (((size *i 8) -i 1)))
                          (Sail.Int.toNatChecked (((((size *i 8) -i 1) -i (halfsize *i 8)) +i 1)))))
                      let lowhalf : (BitVec ((Sail.Int.toNatChecked halfsize) * 8)) :=
                        (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                          (Sail.Int.toNatChecked ((((size *i 8) -i 1) -i (halfsize *i 8))))
                          (Sail.Int.toNatChecked ((((((size *i 8) -i 1) -i (halfsize *i 8)) -i (halfsize *i 8)) +i 1)))))
                      let loop_i_lower : Nat := 0
                      let loop_i_upper : Int := (halfsize -i 1)
                      (do
                        let mut loop_vars := ()
                        for i in [loop_i_lower:loop_i_upper:1]i do
                          let () := loop_vars
                          loop_vars ← do
                            (AArch64_MemSingle_set
                              (BitVec.addInt (BitVec.addInt address halfsize) i) 1 accdesc aligned
                              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb highhalf
                                (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                                (Sail.Int.toNatChecked ((8 *i i))))))
                        (pure loop_vars))
                      let loop_i_lower : Nat := 0
                      let loop_i_upper : Int := (halfsize -i 1)
                      (do
                        let mut loop_vars := ()
                        for i in [loop_i_lower:loop_i_upper:1]i do
                          let () := loop_vars
                          loop_vars ← do
                            (AArch64_MemSingle_set (BitVec.addInt address i) 1 accdesc aligned
                              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb lowhalf
                                (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                                (Sail.Int.toNatChecked ((8 *i i))))))
                        (pure loop_vars)))
                  else
                    (do
                      (AArch64_MemSingle_set address 1 accdesc aligned
                        (Sail.BitVec.extractLsb value_name 7 0))
                      let c ← (( do (ConstrainUnpredictable Unpredictable_DEVPAGE2) ) : SailM
                        Constraint )
                      ArmFull.assert ((BEq.beq c Constraint_FAULT) || (BEq.beq c Constraint_NONE)) "sail-arm/v8_base.sail:28319.63-28319.64"
                      let aligned : Bool :=
                        if ((BEq.beq c Constraint_NONE) : Bool)
                        then true
                        else aligned
                      let loop_i_lower : Nat := 1
                      let loop_i_upper : Int := (size -i 1)
                      (do
                        let mut loop_vars := ()
                        for i in [loop_i_lower:loop_i_upper:1]i do
                          let () := loop_vars
                          loop_vars ← do
                            (AArch64_MemSingle_set (BitVec.addInt address i) 1 accdesc aligned
                              (Sail.BitVec.castWidth (Sail.BitVec.extractLsb value_name
                                (Sail.Int.toNatChecked (((8 *i i) +i 7)))
                                (Sail.Int.toNatChecked ((8 *i i))))))
                        (pure loop_vars)))))))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32, 64] -/
def FPTrigSMul (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  let fptype ← (( do (undefined_FPType (← occLabel 1736) ()) ) : SailM FPType )
  let sign ← (( do (undefined_bitvector_at (← occLabel 1737) 1) ) : SailM (BitVec 1) )
  let value_name ← (( do (undefined_real_at (← occLabel 1738) ()) ) : SailM real )
  ArmFull.assert (((Sail.BitVec.length op2) == 16) || (((Sail.BitVec.length op2) == 32) || ((Sail.BitVec.length
          op2) == 64))) "sail-arm/v8_base.sail:30004.41-30004.42"
  let result ← (( do (FPMul op1 op1 fpcr) ) : SailM (BitVec k_N) )
  let fpexc : Bool := false
  let w__0 ← (( do (FPUnpack__1 result fpcr fpexc) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let fptype : FPType := tup__0
  let sign : (BitVec 1) := tup__1
  let value_name : real := tup__2
  let result : (BitVec k_N) :=
    if ((! ((BEq.beq fptype FPType_QNaN) || (BEq.beq fptype FPType_SNaN))) : Bool)
    then
      (BitVec.update result (Sail.Int.toNatChecked (((Sail.BitVec.length result) -i 1)))
        (Bit (BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op2 0)]))))
    else result
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: k_N : Nat, x_in : Int, List.elem k_N [16, 32, 64] -/
def FPTrigMAdd (x_in : Int) (op1 : (BitVec k_N)) (op2_in : (BitVec k_N)) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  ArmFull.assert (((Sail.BitVec.length op2_in) == 16) || (((Sail.BitVec.length op2_in) == 32) || ((Sail.BitVec.length
          op2_in) == 64))) "sail-arm/v8_base.sail:30202.41-30202.42"
  let op2 : (BitVec k_N) := op2_in
  let x : Int := x_in
  ArmFull.assert (x ≥b 0) "sail-arm/v8_base.sail:30205.17-30205.18"
  ArmFull.assert (x <b 8) "sail-arm/v8_base.sail:30206.16-30206.17"
  let x : Int :=
    if (((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access op2
             (Sail.Int.toNatChecked (((Sail.BitVec.length op2_in) -i 1))))])) == 1#1) : Bool)
    then (x +i 8)
    else x
  let x : Int := x
  let coeff ← (( do
    ((Sail.BitVec.castWidth ) <$> (FPTrigMAddCoefficient_read x (Sail.BitVec.length op2_in))) ) :
    SailM (BitVec k_N) )
  let op2 ← (( do (FPAbs op2) ) : SailM (BitVec k_N) )
  (FPMulAdd coeff op1 op2 fpcr)


/-- Type quantifiers: k_ex10456204_ : Bool, k_N : Nat, esize : Nat, List.elem k_N
  [8, 16, 32, 64, 128, 256, 512, 1024, 2048] ∧ List.elem esize [8, 16, 32, 64] ∧ k_N ≥ esize -/
def Reduce__1 (op : ReduceOp) (input : (BitVec k_N)) (esize : Nat) (altfp : Bool) : SailM (BitVec esize) := do
  ArmFull.assert ((esize == 8) || ((esize == 16) || ((esize == 32) || (esize == 64)))) "sail-arm/v8_base.sail:30829.63-30829.64"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1744)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec esize) )
  if (((Sail.BitVec.length input) == esize) : Bool)
  then
    (pure ((Sail.BitVec.castWidth (Sail.BitVec.extractLsb input
        (Sail.Int.toNatChecked ((esize -i 1))) 0))))
  else
    (do
      let half : Nat := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length input) 2)))
      let hi ← (( do
        ((Sail.BitVec.castWidth ) <$> (if _h : (let (op, input, esize, altfp) :=
            (op, (Sail.BitVec.extractLsb input
              (Sail.Int.toNatChecked (((Sail.BitVec.length input) -i 1)))
              (Sail.Int.toNatChecked (half))), (Sail.Int.toNatChecked (esize)), altfp)
          (Sail.BitVec.length input)).toNat < (let (op, input, esize, altfp) :=
            (op, input, (Sail.Int.toNatChecked (esize)), altfp)
          (Sail.BitVec.length input)).toNat then (Reduce__1 op
          (Sail.BitVec.extractLsb input (Sail.Int.toNatChecked (((Sail.BitVec.length input) -i 1)))
            half) esize altfp) else throw (Sail.Error.Assertion "termination measure"))) ) : SailM
        (BitVec esize) )
      let lo ← (( do
        ((Sail.BitVec.castWidth ) <$> (if _h : (let (op, input, esize, altfp) :=
            (op, (Sail.BitVec.extractLsb input (Sail.Int.toNatChecked ((half -i 1))) 0), (Sail.Int.toNatChecked (esize)), altfp)
          (Sail.BitVec.length input)).toNat < (let (op, input, esize, altfp) :=
            (op, input, (Sail.Int.toNatChecked (esize)), altfp)
          (Sail.BitVec.length input)).toNat then (Reduce__1 op
          (Sail.BitVec.extractLsb input (Sail.Int.toNatChecked ((half -i 1))) 0) esize altfp) else throw (Sail.Error.Assertion "termination measure")))
        ) : SailM (BitVec esize) )
      match op with
      | .ReduceOp_FMINNUM =>
        (do
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/v8_base.sail:30839.51-30839.52"
          let w__0 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          (FPMinNum lo hi w__0))
      | .ReduceOp_FMAXNUM =>
        (do
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/v8_base.sail:30843.51-30843.52"
          let w__2 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          (FPMaxNum lo hi w__2))
      | .ReduceOp_FMIN =>
        (do
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/v8_base.sail:30847.51-30847.52"
          let w__4 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          (FPMin__1 lo hi w__4 altfp))
      | .ReduceOp_FMAX =>
        (do
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/v8_base.sail:30851.51-30851.52"
          let w__6 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          (FPMax__1 lo hi w__6 altfp))
      | .ReduceOp_FADD =>
        (do
          ArmFull.assert (((esize == 16) || (esize == 32)) || (esize == 64)) "sail-arm/v8_base.sail:30855.51-30855.52"
          let w__8 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
          (FPAdd lo hi w__8))
      | .ReduceOp_ADD =>
        (let result : (BitVec esize) := (lo + hi)
        (pure (result))))
termination_by (let (op, input, esize, altfp) := (op, input, (Sail.Int.toNatChecked (esize)), altfp)
(Sail.BitVec.length input)).toNat
decreasing_by all_goals first | assumption | (simp_wf; assumption) | simp_all


/-- Type quantifiers: k_N : Nat, k_N = 32 -/
def BFMulAddH_ZA (addend : (BitVec k_N)) (op1 : (BitVec (k_N / 2))) (op2 : (BitVec (k_N / 2))) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length addend) == 32) "sail-arm/v8_base.sail:32200.19-32200.20"
  let value1_name : (BitVec k_N) :=
    (Sail.BitVec.castWidth (op1 +++ (Zeros
        (n := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length addend) 2)))))))
  let value2_name : (BitVec k_N) :=
    (Sail.BitVec.castWidth (op2 +++ (Zeros
        (n := (Sail.Int.toNatChecked ((Int.ediv (Sail.BitVec.length value1_name) 2)))))))
  (FPMulAdd_ZA addend value1_name value2_name fpcr)


/-- Type quantifiers: k_N : Nat, k_N = 128 -/
def BFMatMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length op2) == 128) "sail-arm/v8_base.sail:32417.20-32417.21"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1826)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let sum ← (( do (undefined_bitvector_at (← occLabel 1827) 32) ) : SailM (BitVec 32) )
  let (result, sum) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 1
    (do
      let mut loop_vars := (result, sum)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (result, sum) := loop_vars
        loop_vars ← do
          let loop_j_lower : Nat := 0
          let loop_j_upper : Nat := 1
          (do
            let mut loop_vars_1 := (result, sum)
            for j in [loop_j_lower:loop_j_upper:1]i do
              let (result, sum) := loop_vars_1
              loop_vars_1 ← do
                let w__0 ← (( do (Elem_read addend ((2 *i i) +i j) 32) ) : SailM (BitVec 32) )
                let sum := (w__0 : (BitVec 32))
                let sum ← (( do
                  let loop_k_lower : Nat := 0
                  let loop_k_upper : Nat := 1
                  (do
                    let mut loop_vars_2 := sum
                    for k in [loop_k_lower:loop_k_upper:1]i do
                      let sum := loop_vars_2
                      loop_vars_2 ← do
                        let elt1_a ← (( do (Elem_read op1 (((4 *i i) +i (2 *i k)) +i 0) 16) ) :
                          SailM (BitVec 16) )
                        let elt1_b ← (( do (Elem_read op1 (((4 *i i) +i (2 *i k)) +i 1) 16) ) :
                          SailM (BitVec 16) )
                        let elt2_a ← (( do (Elem_read op2 (((4 *i j) +i (2 *i k)) +i 0) 16) ) :
                          SailM (BitVec 16) )
                        let elt2_b ← (( do (Elem_read op2 (((4 *i j) +i (2 *i k)) +i 1) 16) ) :
                          SailM (BitVec 16) )
                        let w__1 ← (( do (FPCR_read ()) ) : SailM (BitVec 64) )
                        (BFDotAdd (k_N := 32) sum elt1_a elt1_b elt2_a elt2_b w__1)
                    (pure loop_vars_2)) ) : SailM (BitVec 32) )
                let w__3 ← (( do (Elem_set result ((2 *i i) +i j) 32 sum) ) : SailM (BitVec k_N) )
                let result := (w__3 : (BitVec k_N))
                (pure ((result, sum)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM ((BitVec k_N) × (BitVec 32)) )
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: k_N : Nat, esize : Int, k_N ≥ 0 ∧
  (Sail.Int.toNatChecked (esize : Int)) = 16 ∨
  (Sail.Int.toNatChecked (esize : Int)) = 32 ∨
  (Sail.Int.toNatChecked (esize : Int)) = 64 ∨
  (not (k_N = (Sail.Int.toNatChecked (((esize : Int) *i (2 : Int)) *i (2 : Int))))) -/
def FPMatMulAdd (addend : (BitVec k_N)) (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) (esize : Int) (fpcr : (BitVec 64)) : SailM (BitVec k_N) := do
  ArmFull.assert ((Sail.BitVec.length op2) == ((esize *i 2) *i 2)) "sail-arm/v8_base.sail:33003.30-33003.31"
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1914)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let prod0 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1915)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  let prod1 ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1916)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  let sum ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 1917)
      (Sail.Int.toNatChecked (esize)))) ) : SailM (BitVec (Sail.Int.toNatChecked (esize : Int))) )
  let (prod0, prod1, result, sum) ← (( do
    let loop_i_lower : Nat := 0
    let loop_i_upper : Nat := 1
    (do
      let mut loop_vars := (prod0, prod1, result, sum)
      for i in [loop_i_lower:loop_i_upper:1]i do
        let (prod0, prod1, result, sum) := loop_vars
        loop_vars ← do
          let loop_j_lower : Nat := 0
          let loop_j_upper : Nat := 1
          (do
            let mut loop_vars_1 := (prod0, prod1, result, sum)
            for j in [loop_j_lower:loop_j_upper:1]i do
              let (prod0, prod1, result, sum) := loop_vars_1
              loop_vars_1 ← do
                ArmFull.assert (((((2 *i i) +i j) *i esize) ≤b (((((2 *i i) +i j) *i esize) +i esize) -i 1)) || ((! ((((2 *i i) +i j) ≥b 0) && (((((2 *i i) +i j) +i 1) *i esize) ≤b (Sail.BitVec.length
                            result)))) || (! ((Sail.BitVec.length result) == ((esize *i 2) *i 2))))) "sail-arm/v8_base.sail:33010.223-33010.224"
                let w__0 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read addend ((2 *i i) +i j)
                    (Sail.Int.toNatChecked (esize)))) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let sum := (w__0 : (BitVec (Sail.Int.toNatChecked (esize : Int))))
                let w__1 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read op1 ((2 *i i) +i 0)
                    (Sail.Int.toNatChecked (esize)))) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let w__2 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read op2 ((2 *i j) +i 0)
                    (Sail.Int.toNatChecked (esize)))) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let w__3 ← (( do (FPMul w__1 w__2 fpcr) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let prod0 := (w__3 : (BitVec (Sail.Int.toNatChecked (esize : Int))))
                let w__4 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read op1 ((2 *i i) +i 1)
                    (Sail.Int.toNatChecked (esize)))) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let w__5 ← (( do
                  ((Sail.BitVec.castWidth ) <$> (Elem_read op2 ((2 *i j) +i 1)
                    (Sail.Int.toNatChecked (esize)))) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let w__6 ← (( do (FPMul w__4 w__5 fpcr) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let prod1 := (w__6 : (BitVec (Sail.Int.toNatChecked (esize : Int))))
                let w__7 ← (( do (FPAdd prod0 prod1 fpcr) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let w__8 ← (( do (FPAdd sum w__7 fpcr) ) : SailM
                  (BitVec (Sail.Int.toNatChecked (esize : Int))) )
                let sum := (w__8 : (BitVec (Sail.Int.toNatChecked (esize : Int))))
                let w__9 ← (( do
                  (Elem_set result ((2 *i i) +i j) (Sail.Int.toNatChecked (esize))
                    (Sail.BitVec.castWidth sum)) ) : SailM (BitVec k_N) )
                let result := (w__9 : (BitVec k_N))
                (pure ((prod0, prod1, result, sum)))
            (pure loop_vars_1))
      (pure loop_vars)) ) : SailM
    ((BitVec (Sail.Int.toNatChecked (esize : Int))) × (BitVec (Sail.Int.toNatChecked (esize : Int))) × (BitVec k_N) × (BitVec (Sail.Int.toNatChecked (esize : Int))))
    )
  (pure ((Sail.BitVec.castWidth result)))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32] -/
def FPRecipStep (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 2735) ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool_at (← occLabel 2736) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 2737) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2738)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 2739) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 2740) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 2741) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 2742) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 2743) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 2744) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 2745) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 2746) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || ((Sail.BitVec.length result) == 32)) "sail-arm/v8_base.sail:41831.30-41831.31"
  let fpcr ← (( do (StandardFPSCRValue ()) ) : SailM FPCRType )
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs type1 type2 op1 op2 fpcr) ) : SailM (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let product ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2747)
          (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
      let product ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 (Sail.BitVec.length result))))
        else
          (do
            (FPMul op1 op2 fpcr)) ) : SailM (BitVec k_N) )
      let two ← (( do ((Sail.BitVec.castWidth ) <$> (FPTwo 0#1 (Sail.BitVec.length result))) ) :
        SailM (BitVec k_N) )
      (FPSub two product fpcr))
  else (pure (result))


/-- Type quantifiers: k_N : Nat, List.elem k_N [16, 32] -/
def FPRSqrtStep (op1 : (BitVec k_N)) (op2 : (BitVec k_N)) : SailM (BitVec k_N) := do
  let done ← (( do (undefined_bool_at (← occLabel 2748) ()) ) : SailM Bool )
  let inf1 ← (( do (undefined_bool_at (← occLabel 2749) ()) ) : SailM Bool )
  let inf2 ← (( do (undefined_bool_at (← occLabel 2750) ()) ) : SailM Bool )
  let result ← (( do
    ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2751)
      (Sail.BitVec.length op2))) ) : SailM (BitVec k_N) )
  let sign1 ← (( do (undefined_bitvector_at (← occLabel 2752) 1) ) : SailM (BitVec 1) )
  let sign2 ← (( do (undefined_bitvector_at (← occLabel 2753) 1) ) : SailM (BitVec 1) )
  let type1 ← (( do (undefined_FPType (← occLabel 2754) ()) ) : SailM FPType )
  let type2 ← (( do (undefined_FPType (← occLabel 2755) ()) ) : SailM FPType )
  let value1_name ← (( do (undefined_real_at (← occLabel 2756) ()) ) : SailM real )
  let value2_name ← (( do (undefined_real_at (← occLabel 2757) ()) ) : SailM real )
  let zero1 ← (( do (undefined_bool_at (← occLabel 2758) ()) ) : SailM Bool )
  let zero2 ← (( do (undefined_bool_at (← occLabel 2759) ()) ) : SailM Bool )
  ArmFull.assert (((Sail.BitVec.length result) == 16) || ((Sail.BitVec.length result) == 32)) "sail-arm/v8_base.sail:41868.30-41868.31"
  let fpcr ← (( do (StandardFPSCRValue ()) ) : SailM FPCRType )
  let w__0 ← (( do (FPUnpack op1 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__0 : (FPType × (BitVec 1) × real))
  let type1 : FPType := tup__0
  let sign1 : (BitVec 1) := tup__1
  let value1_name : real := tup__2
  let w__1 ← (( do (FPUnpack op2 fpcr) ) : SailM (FPType × (BitVec 1) × real) )
  let (tup__0, tup__1, tup__2) := (w__1 : (FPType × (BitVec 1) × real))
  let type2 : FPType := tup__0
  let sign2 : (BitVec 1) := tup__1
  let value2_name : real := tup__2
  let w__2 ← (( do (FPProcessNaNs type1 type2 op1 op2 fpcr) ) : SailM (Bool × (BitVec k_N)) )
  let (tup__0, tup__1) := (w__2 : (Bool × (BitVec k_N)))
  let done : Bool := tup__0
  let result : (BitVec k_N) := tup__1
  if ((! done) : Bool)
  then
    (do
      let inf1 : Bool := (BEq.beq type1 FPType_Infinity)
      let inf2 : Bool := (BEq.beq type2 FPType_Infinity)
      let zero1 : Bool := (BEq.beq type1 FPType_Zero)
      let zero2 : Bool := (BEq.beq type2 FPType_Zero)
      let product ← (( do
        ((Sail.BitVec.castWidth ) <$> (undefined_bitvector_at (← occLabel 2760)
          (Sail.BitVec.length result))) ) : SailM (BitVec k_N) )
      let product ← (( do
        if (((inf1 && zero2) || (zero1 && inf2)) : Bool)
        then
          (do
            ((Sail.BitVec.castWidth ) <$> (FPZero 0#1 (Sail.BitVec.length result))))
        else
          (do
            (FPMul op1 op2 fpcr)) ) : SailM (BitVec k_N) )
      let three ← (( do ((Sail.BitVec.castWidth ) <$> (FPThree 0#1 (Sail.BitVec.length result))) )
        : SailM (BitVec k_N) )
      (FPHalvedSub three product fpcr))
  else (pure (result))


/-- Type quantifiers: size : Nat, List.elem size [1, 2, 4, 8, 16] -/
def Mem_with_type_read (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) : SailM (BitVec (size * 8)) := do
  let ispair : Bool := false
  ((Sail.BitVec.castWidth ) <$> (Mem_with_type_read__1 address size accdesc ispair))


/-- Type quantifiers: size : Nat, (size * 8) ≥ 0 -/
def Mem_with_type_set (address : (BitVec 32)) (size : Nat) (accdesc : AccessDescriptor) (value_in_name : (BitVec (size * 8))) : SailM Unit := do
  let ispair : Bool := false
  (Mem_with_type_set__1 address size accdesc ispair (Sail.BitVec.castWidth value_in_name))


/-- Type quantifiers: t : Int -/
def DC_GVA_SysOpsWrite_26c60f1734aa9835 (el : (BitVec 2)) (op0 : (BitVec 2)) (op1 : (BitVec 3)) (CRn : (BitVec 4)) (op2 : (BitVec 3)) (CRm : (BitVec 4)) (t : Int) : SailM Unit := do
  let w__0 ← (( do readReg PSTATE ) : SailM ProcState )
  let __PSTATE_EL : (BitVec 2) := w__0.EL
  let w__1 ← (( do readReg SCTLR_EL1 ) : SailM (BitVec 64) )
  let __SCTLR_EL1_DZE : (BitVec 1) := (_get_SCTLR_EL1_Type_DZE w__1)
  let w__2 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TGE : (BitVec 1) := (_get_HCR_EL2_Type_TGE w__2)
  let w__3 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
  let __HCR_EL2_TDZ : (BitVec 1) := (_get_HCR_EL2_Type_TDZ w__3)
  let w__4 ← (( do readReg SCR_EL3 ) : SailM (BitVec 64) )
  let __SCR_EL3_FGTEn : (BitVec 1) := (_get_SCR_EL3_Type_FGTEn w__4)
  let w__5 ← (( do readReg HFGITR_EL2 ) : SailM (BitVec 64) )
  let __HFGITR_EL2_DCZVA : (BitVec 1) := (_get_HFGITR_EL2_Type_DCZVA w__5)
  let w__6 ← (( do readReg SCTLR_EL2 ) : SailM (BitVec 64) )
  let __SCTLR_EL2_DZE : (BitVec 1) := (_get_SCTLR_EL2_Type_DZE w__6)
  if ((__PSTATE_EL == EL0) : Bool)
  then
    (do
      let w__11 ← (( do
        (pure ((← do
              let w__10 ← (( do
                if ((← do
                     (EL2Enabled ())) : Bool)
                then
                  (do
                    let w__8 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    let w__9 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                    (pure (((((_get_HCR_EL2_Type_E2H w__8) +++ (_get_HCR_EL2_Type_TGE w__9)) == 0b11#2) : Bool))))
                else (pure false) ) : SailM Bool )
              (pure (((! w__10) : Bool)))) && ((__SCTLR_EL1_DZE == 0#1) : Bool))) ) : SailM Bool )
      if (w__11 : Bool)
      then
        (do
          let w__13 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TGE == 1#1) : Bool))) ) : SailM Bool )
          if (w__13 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              (AArch64_SystemAccessTrap EL1 (BitVec.toNat 0x18#8))))
      else
        (do
          let w__18 ← (( do
            (pure ((← do
                  if ((← do
                       (EL2Enabled ())) : Bool)
                  then
                    (do
                      let w__15 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      let w__16 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                      (pure (((((_get_HCR_EL2_Type_E2H w__15) +++ (_get_HCR_EL2_Type_TGE w__16)) != 0b11#2) : Bool))))
                  else (pure false)) && ((__HCR_EL2_TDZ == 1#1) : Bool))) ) : SailM Bool )
          if (w__18 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__26 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 if ((← do
                                      (EL2Enabled ())) : Bool)
                                 then
                                   (do
                                     let w__20 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     let w__21 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                                     (pure (((((_get_HCR_EL2_Type_E2H w__20) +++ (_get_HCR_EL2_Type_TGE
                                             w__21)) != 0b11#2) : Bool))))
                                 else (pure false)) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCZVA == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__26 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__31 ← (( do
                    (pure ((← do
                          if ((← do
                               (EL2Enabled ())) : Bool)
                          then
                            (do
                              let w__28 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              let w__29 ← (( do readReg HCR_EL2 ) : SailM (BitVec 64) )
                              (pure (((((_get_HCR_EL2_Type_E2H w__28) +++ (_get_HCR_EL2_Type_TGE
                                      w__29)) == 0b11#2) : Bool))))
                          else (pure false)) && ((__SCTLR_EL2_DZE == 0#1) : Bool))) ) : SailM Bool )
                  if (w__31 : Bool)
                  then
                    (do
                      (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
                  else
                    (do
                      let w__32 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                      (AArch64_MemZero w__32 CacheType_Tag))))))
  else
    (do
      if ((__PSTATE_EL == EL1) : Bool)
      then
        (do
          let w__34 ← (( do
            (pure ((← do
                  (EL2Enabled ())) && ((__HCR_EL2_TDZ == 1#1) : Bool))) ) : SailM Bool )
          if (w__34 : Bool)
          then
            (do
              (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
          else
            (do
              let w__39 ← (( do
                (pure ((← do
                      (pure ((← do
                            if ((← do
                                 (EL2Enabled ())) : Bool)
                            then
                              (do
                                (IsFeatureImplemented FEAT_FGT))
                            else (pure false)) && (((! (HaveEL EL3)) || (__SCR_EL3_FGTEn == 1#1)) : Bool)))) && ((__HFGITR_EL2_DCZVA == 1#1) : Bool)))
                ) : SailM Bool )
              if (w__39 : Bool)
              then
                (do
                  (AArch64_SystemAccessTrap EL2 (BitVec.toNat 0x18#8)))
              else
                (do
                  let w__40 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_MemZero w__40 CacheType_Tag))))
      else
        (do
          if ((__PSTATE_EL == EL2) : Bool)
          then
            (do
              let w__41 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
              (AArch64_MemZero w__41 CacheType_Tag))
          else
            (do
              if ((__PSTATE_EL == EL3) : Bool)
              then
                (do
                  let w__42 ← (( do (X_read t 64) ) : SailM (BitVec 64) )
                  (AArch64_MemZero w__42 CacheType_Tag))
              else (pure (())))))


end ArmFull.Functions
