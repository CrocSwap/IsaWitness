module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0146
public import ArmFull.Fn.M0204
public import ArmFull.Fn.M0214
public import ArmFull.Fn.M0237
public import ArmFull.Fn.M0603
public import ArmFull.Fn.M0866
public import ArmFull.Fn.M0868
public import ArmFull.Fn.M0869
public import ArmFull.Fn.M0870
public import ArmFull.Fn.M0871
public import ArmFull.Fn.M0872
public import ArmFull.Fn.M0873 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧
  nreg = 4 ∧ List.elem n [0, 1] ∧ esize = 16 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_H1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  nreg = 4 ∧ List.elem n [0, 1, 2, 3] ∧ esize = 32 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_W1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, esize : Nat, n : Nat, nreg : Nat, offset : Nat, s : Nat, k_vertical
  : Bool, 0 ≤ s ∧
  s ≤ 31 ∧
  offset = 0 ∧
  nreg = 4 ∧
  List.elem n [0, 1, 2, 3, 4, 5, 6, 7] ∧ esize = 64 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ4_ZA_D1 (VL : Nat) (d : Nat) (esize : Nat) (n : Nat) (nreg : Nat) (offset : Nat) (s : Nat) (vertical : Bool) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  if ((((nreg == 4) && (esize == 64)) && (VL == 128)) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let slices : Nat := (Sail.Int.toNatChecked ((Int.ediv VL esize)))
  let index ← (( do (X_read s 32) ) : SailM (BitVec 32) )
  let slice_name : Int :=
    (fmod_int (((BitVec.toNat index) -i (Nat.mod (BitVec.toNat index) nreg)) +i offset) slices)
  let loop_r_lower : Nat := 0
  let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
  (do
    let mut loop_vars := ()
    for r in [loop_r_lower:loop_r_upper:1]i do
      let () := loop_vars
      loop_vars ← do
        let result ← (( do
          ((Sail.BitVec.castWidth ) <$> (ZAslice_read n esize vertical (slice_name +i r) VL)) ) :
          SailM (BitVec VL) )
        (ZAslice_set n esize vertical (slice_name +i r) VL (Sail.BitVec.castWidth (Zeros (n := VL))))
        (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
    (pure loop_vars))


/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 2 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ_ZA2_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth (Zeros (n := VL))))
          (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: VL : Nat, d : Nat, nreg : Nat, offset : Nat, v : Nat, 0 ≤ v ∧
  v ≤ 31 ∧
  List.elem offset [0, 1, 2, 3, 4, 5, 6, 7] ∧ nreg = 4 ∧ 0 ≤ d ∧ d ≤ 31 ∧ (is_VL VL) -/
def execute_MOVAZ_MZ_ZA4_1 (VL : Nat) (d : Nat) (nreg : Nat) (offset : Nat) (v : Nat) : SailM Unit := do
  (CheckStreamingSVEAndZAEnabled ())
  let VL : Nat := VL
  let vectors_name : Nat := (Sail.Int.toNatChecked ((Int.ediv VL 8)))
  let vstride : Int := (Int.ediv vectors_name nreg)
  let vbase ← (( do (X_read v 32) ) : SailM (BitVec 32) )
  let vec : Int :=
    (Nat.mod (Sail.Int.toNatChecked (((BitVec.toNat vbase) +i offset)))
      (Sail.Int.toNatChecked (vstride)))
  let vec ← (( do
    let loop_r_lower : Nat := 0
    let loop_r_upper : Nat := (Sail.Int.toNatChecked ((nreg -i 1)))
    (do
      let mut loop_vars := vec
      for r in [loop_r_lower:loop_r_upper:1]i do
        let vec := loop_vars
        loop_vars ← do
          let vec : Int := vec
          let result ← (( do ((Sail.BitVec.castWidth ) <$> (ZAvector_read vec VL)) ) : SailM
            (BitVec VL) )
          let vec : Int := vec
          (ZAvector_set vec VL (Sail.BitVec.castWidth (Zeros (n := VL))))
          (Z_set (d +i r) VL (Sail.BitVec.castWidth result))
          let vec : Int := (vec +i vstride)
          (pure (vec))
      (pure loop_vars)) ) : SailM Int )
  (pure (()))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_Reserved (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1 ← (( do
    if ((((Sail.BitVec.castWidth (m := 16) (Sail.BitVec.extractLsb __opcode 31 16)) == (0x0000#16 : (BitVec 16))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 1017) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 1017
      let imm16 := (BitVec.slice __opcode 0 16)
      (decode_udf_perm_undef_aarch64_instrs_udf imm16))
  else
    (do
      (__ArmCertEndOfDecode ())
      sailThrow ((Error_Undefined ())))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_DataProcImm (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__1 ← (( do
    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0x22#8 : (BitVec 8))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 18) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 18
      let Rd := (BitVec.slice __opcode 0 5)
      let Rn := (BitVec.slice __opcode 5 5)
      let imm12 := (BitVec.slice __opcode 10 12)
      let sh := (BitVec.slice __opcode 22 1)
      let S := (BitVec.slice __opcode 29 1)
      let op := (BitVec.slice __opcode 30 1)
      let sf := (BitVec.slice __opcode 31 1)
      (decode_add_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh S op
        sf))
  else
    (do
      let w__3 ← (( do
        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0x62#8 : (BitVec 8))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 19) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 19
          let Rd := (BitVec.slice __opcode 0 5)
          let Rn := (BitVec.slice __opcode 5 5)
          let imm12 := (BitVec.slice __opcode 10 12)
          let sh := (BitVec.slice __opcode 22 1)
          let S := (BitVec.slice __opcode 29 1)
          let op := (BitVec.slice __opcode 30 1)
          let sf := (BitVec.slice __opcode 31 1)
          (decode_adds_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12 sh
            S op sf))
      else
        (do
          let w__5 ← (( do
            if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0xA2#8 : (BitVec 8))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 20) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 20
              let Rd := (BitVec.slice __opcode 0 5)
              let Rn := (BitVec.slice __opcode 5 5)
              let imm12 := (BitVec.slice __opcode 10 12)
              let sh := (BitVec.slice __opcode 22 1)
              let S := (BitVec.slice __opcode 29 1)
              let op := (BitVec.slice __opcode 30 1)
              let sf := (BitVec.slice __opcode 31 1)
              (decode_sub_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn imm12
                sh S op sf))
          else
            (do
              let w__7 ← (( do
                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 30 23)) == (0xE2#8 : (BitVec 8))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 21) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 21
                  let Rd := (BitVec.slice __opcode 0 5)
                  let Rn := (BitVec.slice __opcode 5 5)
                  let imm12 := (BitVec.slice __opcode 10 12)
                  let sh := (BitVec.slice __opcode 22 1)
                  let S := (BitVec.slice __opcode 29 1)
                  let op := (BitVec.slice __opcode 30 1)
                  let sf := (BitVec.slice __opcode 31 1)
                  (decode_subs_addsub_imm_aarch64_instrs_integer_arithmetic_add_sub_immediate Rd Rn
                    imm12 sh S op sf))
              else
                (do
                  let w__9 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb __opcode 31 22)) == (0b1001000110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             __opcode 15 14)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 26) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 26
                      let Xd := (BitVec.slice __opcode 0 5)
                      let Xn := (BitVec.slice __opcode 5 5)
                      let uimm4 := (BitVec.slice __opcode 10 4)
                      let op3 := (BitVec.slice __opcode 14 2)
                      let uimm6 := (BitVec.slice __opcode 16 6)
                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 14)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 15)])) != 0#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_addg_aarch64_instrs_integer_tags_mcaddtag Xd Xn uimm4 op3 uimm6)))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode 31
                                 31)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                 __opcode 28 24)) == (0b10000#5 : (BitVec 5)))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 34) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 34
                          let Rd := (BitVec.slice __opcode 0 5)
                          let immhi := (BitVec.slice __opcode 5 19)
                          let immlo := (BitVec.slice __opcode 29 2)
                          let op := (BitVec.slice __opcode 31 1)
                          (decode_adr_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi
                            immlo op))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb __opcode
                                     31 31)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                     __opcode 28 24)) == (0b10000#5 : (BitVec 5)))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 35) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 35
                              let Rd := (BitVec.slice __opcode 0 5)
                              let immhi := (BitVec.slice __opcode 5 19)
                              let immlo := (BitVec.slice __opcode 29 2)
                              let op := (BitVec.slice __opcode 31 1)
                              (decode_adrp_aarch64_instrs_integer_arithmetic_address_pc_rel Rd immhi
                                immlo op))
                          else
                            (do
                              let w__15 ← (( do
                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                       __opcode 30 23)) == (0x24#8 : (BitVec 8))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 40) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 40
                                  let Rd := (BitVec.slice __opcode 0 5)
                                  let Rn := (BitVec.slice __opcode 5 5)
                                  let imms := (BitVec.slice __opcode 10 6)
                                  let immr := (BitVec.slice __opcode 16 6)
                                  let N := (BitVec.slice __opcode 22 1)
                                  let opc := (BitVec.slice __opcode 29 2)
                                  let sf := (BitVec.slice __opcode 31 1)
                                  (decode_and_log_imm_aarch64_instrs_integer_logical_immediate Rd Rn
                                    imms immr N opc sf))
                              else
                                (do
                                  let w__17 ← (( do
                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                           __opcode 30 23)) == (0xE4#8 : (BitVec 8))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 41) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 41
                                      let Rd := (BitVec.slice __opcode 0 5)
                                      let Rn := (BitVec.slice __opcode 5 5)
                                      let imms := (BitVec.slice __opcode 10 6)
                                      let immr := (BitVec.slice __opcode 16 6)
                                      let N := (BitVec.slice __opcode 22 1)
                                      let opc := (BitVec.slice __opcode 29 2)
                                      let sf := (BitVec.slice __opcode 31 1)
                                      (decode_ands_log_imm_aarch64_instrs_integer_logical_immediate
                                        Rd Rn imms immr N opc sf))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                               __opcode 30 23)) == (0xA4#8 : (BitVec 8))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 42) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 42
                                          let Rd := (BitVec.slice __opcode 0 5)
                                          let Rn := (BitVec.slice __opcode 5 5)
                                          let imms := (BitVec.slice __opcode 10 6)
                                          let immr := (BitVec.slice __opcode 16 6)
                                          let N := (BitVec.slice __opcode 22 1)
                                          let opc := (BitVec.slice __opcode 29 2)
                                          let sf := (BitVec.slice __opcode 31 1)
                                          (decode_eor_log_imm_aarch64_instrs_integer_logical_immediate
                                            Rd Rn imms immr N opc sf))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                   __opcode 30 23)) == (0x64#8 : (BitVec 8))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 43) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 43
                                              let Rd := (BitVec.slice __opcode 0 5)
                                              let Rn := (BitVec.slice __opcode 5 5)
                                              let imms := (BitVec.slice __opcode 10 6)
                                              let immr := (BitVec.slice __opcode 16 6)
                                              let N := (BitVec.slice __opcode 22 1)
                                              let opc := (BitVec.slice __opcode 29 2)
                                              let sf := (BitVec.slice __opcode 31 1)
                                              (decode_orr_log_imm_aarch64_instrs_integer_logical_immediate
                                                Rd Rn imms immr N opc sf))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                       __opcode 30 23)) == (0x66#8 : (BitVec 8))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 76) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 76
                                                  let Rd := (BitVec.slice __opcode 0 5)
                                                  let Rn := (BitVec.slice __opcode 5 5)
                                                  let imms := (BitVec.slice __opcode 10 6)
                                                  let immr := (BitVec.slice __opcode 16 6)
                                                  let N := (BitVec.slice __opcode 22 1)
                                                  let opc := (BitVec.slice __opcode 29 2)
                                                  let sf := (BitVec.slice __opcode 31 1)
                                                  (decode_bfm_aarch64_instrs_integer_bitfield Rd Rn
                                                    imms immr N opc sf))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                           __opcode 30 23)) == (0x26#8 : (BitVec 8))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 77) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 77
                                                      let Rd := (BitVec.slice __opcode 0 5)
                                                      let Rn := (BitVec.slice __opcode 5 5)
                                                      let imms := (BitVec.slice __opcode 10 6)
                                                      let immr := (BitVec.slice __opcode 16 6)
                                                      let N := (BitVec.slice __opcode 22 1)
                                                      let opc := (BitVec.slice __opcode 29 2)
                                                      let sf := (BitVec.slice __opcode 31 1)
                                                      (decode_sbfm_aarch64_instrs_integer_bitfield
                                                        Rd Rn imms immr N opc sf))
                                                  else
                                                    (do
                                                      let w__27 ← (( do
                                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                               __opcode 30 23)) == (0xA6#8 : (BitVec 8))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__26 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__26 <b 78) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__27 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 78
                                                          let Rd := (BitVec.slice __opcode 0 5)
                                                          let Rn := (BitVec.slice __opcode 5 5)
                                                          let imms := (BitVec.slice __opcode 10 6)
                                                          let immr := (BitVec.slice __opcode 16 6)
                                                          let N := (BitVec.slice __opcode 22 1)
                                                          let opc := (BitVec.slice __opcode 29 2)
                                                          let sf := (BitVec.slice __opcode 31 1)
                                                          (decode_ubfm_aarch64_instrs_integer_bitfield
                                                            Rd Rn imms immr N opc sf))
                                                      else
                                                        (do
                                                          let w__29 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 30 23)) == (0x27#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 21 21)) == (0#1 : (BitVec 1)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__28 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__28 <b 206) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__29 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 206
                                                              let Rd := (BitVec.slice __opcode 0 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let imms :=
                                                                (BitVec.slice __opcode 10 6)
                                                              let Rm := (BitVec.slice __opcode 16 5)
                                                              let N := (BitVec.slice __opcode 22 1)
                                                              let sf := (BitVec.slice __opcode 31 1)
                                                              (decode_extr_aarch64_instrs_integer_ins_ext_extract_immediate
                                                                Rd Rn imms Rm N sf))
                                                          else
                                                            (do
                                                              let w__31 ← (( do
                                                                if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                       __opcode 30 23)) == (0xE5#8 : (BitVec 8))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__30 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__30 <b 696) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__31 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 696
                                                                  let Rd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  let imm16 :=
                                                                    (BitVec.slice __opcode 5 16)
                                                                  let hw :=
                                                                    (BitVec.slice __opcode 21 2)
                                                                  let opc :=
                                                                    (BitVec.slice __opcode 29 2)
                                                                  let sf :=
                                                                    (BitVec.slice __opcode 31 1)
                                                                  (decode_movk_aarch64_instrs_integer_ins_ext_insert_movewide
                                                                    Rd imm16 hw opc sf))
                                                              else
                                                                (do
                                                                  let w__33 ← (( do
                                                                    if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                           __opcode 30 23)) == (0x25#8 : (BitVec 8))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__32 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__32 <b 697) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__33 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 697
                                                                      let Rd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      let imm16 :=
                                                                        (BitVec.slice __opcode 5 16)
                                                                      let hw :=
                                                                        (BitVec.slice __opcode 21 2)
                                                                      let opc :=
                                                                        (BitVec.slice __opcode 29 2)
                                                                      let sf :=
                                                                        (BitVec.slice __opcode 31 1)
                                                                      (decode_movn_aarch64_instrs_integer_ins_ext_insert_movewide
                                                                        Rd imm16 hw opc sf))
                                                                  else
                                                                    (do
                                                                      let w__35 ← (( do
                                                                        if ((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                               __opcode 30 23)) == (0xA5#8 : (BitVec 8))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__34 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__34 <b 698) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__35 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 698
                                                                          let Rd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          let imm16 :=
                                                                            (BitVec.slice __opcode 5
                                                                              16)
                                                                          let hw :=
                                                                            (BitVec.slice __opcode
                                                                              21 2)
                                                                          let opc :=
                                                                            (BitVec.slice __opcode
                                                                              29 2)
                                                                          let sf :=
                                                                            (BitVec.slice __opcode
                                                                              31 1)
                                                                          (decode_movz_aarch64_instrs_integer_ins_ext_insert_movewide
                                                                            Rd imm16 hw opc sf))
                                                                      else
                                                                        (do
                                                                          let w__37 ← (( do
                                                                            if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                   __opcode 30 18)) == (0b0010001110000#13 : (BitVec 13))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__36 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__36 <b 832) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__37 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 832
                                                                              let Rd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let imm8 :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 8)
                                                                              let sf :=
                                                                                (BitVec.slice
                                                                                  __opcode 31 1)
                                                                              (decode_smax_imm_aarch64_instrs_integer_arithmetic_max_min_smax_imm
                                                                                Rd Rn imm8 sf))
                                                                          else
                                                                            (do
                                                                              let w__39 ← (( do
                                                                                if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                       __opcode 30
                                                                                       18)) == (0b0010001110010#13 : (BitVec 13))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__38 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__38 <b 847) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__39 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 847
                                                                                  let Rd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let imm8 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 8)
                                                                                  let sf :=
                                                                                    (BitVec.slice
                                                                                      __opcode 31 1)
                                                                                  (decode_smin_imm_aarch64_instrs_integer_arithmetic_max_min_smin_imm
                                                                                    Rd Rn imm8 sf))
                                                                              else
                                                                                (do
                                                                                  let w__41 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 10) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 22)) == (0b1101000110#10 : (BitVec 10))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 14)) == (0b00#2 : (BitVec 2)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__40 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__40 <b 990) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__41 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 990
                                                                                      let Xd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      let Xn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let uimm4 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 4)
                                                                                      let op3 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          14 2)
                                                                                      let uimm6 :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 6)
                                                                                      if ((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 14)])) != 0#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                 __opcode
                                                                                                 15)])) != 0#1)) : Bool)
                                                                                      then
                                                                                        sailThrow ((Error_ConstrainedUnpredictable
                                                                                          ()))
                                                                                      else
                                                                                        (do
                                                                                          (decode_subg_aarch64_instrs_integer_tags_mcsubtag
                                                                                            Xd Xn
                                                                                            uimm4
                                                                                            op3
                                                                                            uimm6)))
                                                                                  else
                                                                                    (do
                                                                                      let w__43 ← (( do
                                                                                        if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               30 18)) == (0b0010001110001#13 : (BitVec 13))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__42 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__42 <b 1018) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__43 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1018
                                                                                          let Rd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let imm8 :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 8)
                                                                                          let sf :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              31 1)
                                                                                          (decode_umax_imm_aarch64_instrs_integer_arithmetic_max_min_umax_imm
                                                                                            Rd Rn
                                                                                            imm8 sf))
                                                                                      else
                                                                                        (do
                                                                                          let w__45 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   30
                                                                                                   18)) == (0b0010001110011#13 : (BitVec 13))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__44 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__44 <b 1021) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__45 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1021
                                                                                              let Rd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let imm8 :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  8)
                                                                                              let sf :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  31
                                                                                                  1)
                                                                                              (decode_umin_imm_aarch64_instrs_integer_arithmetic_max_min_umin_imm
                                                                                                Rd
                                                                                                Rn
                                                                                                imm8
                                                                                                sf))
                                                                                          else
                                                                                            (do
                                                                                              (__ArmCertEndOfDecode
                                                                                                ())
                                                                                              sailThrow ((Error_Undefined
                                                                                                ())))))))))))))))))))))))))


end ArmFull.Functions
