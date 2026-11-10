import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0021
import ArmFull.Fn.M0167
import ArmFull.Fn.M0928
import ArmFull.Fn.M0932

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

def decode_bic_advsimd_imm_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp (← occLabel 3993) ()) ) : SailM ImmediateOp )
  let b__0 := (cmode +++ op)
  let operation ← (( do
    if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure (ImmediateOp_MOVI))
    else
      (do
        if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure (ImmediateOp_MVNI))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure (ImmediateOp_ORR))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure (ImmediateOp_BIC))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure (ImmediateOp_MOVI))
                    else
                      (do
                        if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure (ImmediateOp_MVNI))
                        else
                          (do
                            if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure (ImmediateOp_ORR))
                            else
                              (do
                                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4
                                         3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure (ImmediateOp_BIC))
                                else
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure (ImmediateOp_MOVI))
                                    else
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure (ImmediateOp_MVNI))
                                        else
                                          (do
                                            if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure (ImmediateOp_MOVI))
                                            else
                                              (do
                                                match b__0 with
                                                | 0b11110 => (pure (ImmediateOp_MOVI))
                                                | _ =>
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then sailThrow ((Error_Undefined ()))
                                                    else (pure (()))
                                                    (pure (ImmediateOp_MOVI)))))))))))))) ) : SailM
    ImmediateOp )
  let operation := operation
  let imm64 ← (( do
    (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM
    (BitVec 64) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits imm64
      (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 64)))))
  (execute_aarch64_instrs_vector_logical (Sail.Int.toNatChecked (datasize))
    (Sail.BitVec.castWidth imm) operation (Sail.Int.toNatChecked (rd)))


def decode_movi_advsimd_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp (← occLabel 3994) ()) ) : SailM ImmediateOp )
  let b__0 := (cmode +++ op)
  let operation ← (( do
    if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure (ImmediateOp_MOVI))
    else
      (do
        if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure (ImmediateOp_MVNI))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure (ImmediateOp_ORR))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure (ImmediateOp_BIC))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure (ImmediateOp_MOVI))
                    else
                      (do
                        if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure (ImmediateOp_MVNI))
                        else
                          (do
                            if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure (ImmediateOp_ORR))
                            else
                              (do
                                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4
                                         3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure (ImmediateOp_BIC))
                                else
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure (ImmediateOp_MOVI))
                                    else
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure (ImmediateOp_MVNI))
                                        else
                                          (do
                                            if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure (ImmediateOp_MOVI))
                                            else
                                              (do
                                                match b__0 with
                                                | 0b11110 => (pure (ImmediateOp_MOVI))
                                                | _ =>
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then sailThrow ((Error_Undefined ()))
                                                    else (pure (()))
                                                    (pure (ImmediateOp_MOVI)))))))))))))) ) : SailM
    ImmediateOp )
  let operation := operation
  let imm64 ← (( do
    (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM
    (BitVec 64) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits imm64
      (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 64)))))
  (execute_aarch64_instrs_vector_logical (Sail.Int.toNatChecked (datasize))
    (Sail.BitVec.castWidth imm) operation (Sail.Int.toNatChecked (rd)))


def decode_mvni_advsimd_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp (← occLabel 3995) ()) ) : SailM ImmediateOp )
  let b__0 := (cmode +++ op)
  let operation ← (( do
    if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure (ImmediateOp_MOVI))
    else
      (do
        if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure (ImmediateOp_MVNI))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure (ImmediateOp_ORR))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure (ImmediateOp_BIC))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure (ImmediateOp_MOVI))
                    else
                      (do
                        if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure (ImmediateOp_MVNI))
                        else
                          (do
                            if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure (ImmediateOp_ORR))
                            else
                              (do
                                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4
                                         3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure (ImmediateOp_BIC))
                                else
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure (ImmediateOp_MOVI))
                                    else
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure (ImmediateOp_MVNI))
                                        else
                                          (do
                                            if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure (ImmediateOp_MOVI))
                                            else
                                              (do
                                                match b__0 with
                                                | 0b11110 => (pure (ImmediateOp_MOVI))
                                                | _ =>
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then sailThrow ((Error_Undefined ()))
                                                    else (pure (()))
                                                    (pure (ImmediateOp_MOVI)))))))))))))) ) : SailM
    ImmediateOp )
  let operation := operation
  let imm64 ← (( do
    (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM
    (BitVec 64) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits imm64
      (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 64)))))
  (execute_aarch64_instrs_vector_logical (Sail.Int.toNatChecked (datasize))
    (Sail.BitVec.castWidth imm) operation (Sail.Int.toNatChecked (rd)))


def decode_orr_advsimd_imm_aarch64_instrs_vector_logical (Rd : (BitVec 5)) (h : (BitVec 1)) (g : (BitVec 1)) (f : (BitVec 1)) (e : (BitVec 1)) (d : (BitVec 1)) (cmode : (BitVec 4)) (c : (BitVec 1)) (b : (BitVec 1)) (a : (BitVec 1)) (op : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let rd : Int := (BitVec.toNat Rd)
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let operation ← (( do (undefined_ImmediateOp (← occLabel 3996) ()) ) : SailM ImmediateOp )
  let b__0 := (cmode +++ op)
  let operation ← (( do
    if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
    then (pure (ImmediateOp_MOVI))
    else
      (do
        if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
        then (pure (ImmediateOp_MVNI))
        else
          (do
            if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
            then (pure (ImmediateOp_ORR))
            else
              (do
                if ((((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb b__0 4 4)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                then (pure (ImmediateOp_BIC))
                else
                  (do
                    if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                             b__0 1 0)) == (0b00#2 : (BitVec 2)))) : Bool)
                    then (pure (ImmediateOp_MOVI))
                    else
                      (do
                        if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                 b__0 1 0)) == (0b01#2 : (BitVec 2)))) : Bool)
                        then (pure (ImmediateOp_MVNI))
                        else
                          (do
                            if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4 3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                     b__0 1 0)) == (0b10#2 : (BitVec 2)))) : Bool)
                            then (pure (ImmediateOp_ORR))
                            else
                              (do
                                if ((((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb b__0 4
                                         3)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                         b__0 1 0)) == (0b11#2 : (BitVec 2)))) : Bool)
                                then (pure (ImmediateOp_BIC))
                                else
                                  (do
                                    if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                             b__0 0 0)) == (0#1 : (BitVec 1)))) : Bool)
                                    then (pure (ImmediateOp_MOVI))
                                    else
                                      (do
                                        if ((((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 b__0 4 2)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                 b__0 0 0)) == (1#1 : (BitVec 1)))) : Bool)
                                        then (pure (ImmediateOp_MVNI))
                                        else
                                          (do
                                            if (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                   b__0 4 1)) == (0xE#4 : (BitVec 4))) : Bool)
                                            then (pure (ImmediateOp_MOVI))
                                            else
                                              (do
                                                match b__0 with
                                                | 0b11110 => (pure (ImmediateOp_MOVI))
                                                | _ =>
                                                  (do
                                                    if ((Q == 0#1) : Bool)
                                                    then sailThrow ((Error_Undefined ()))
                                                    else (pure (()))
                                                    (pure (ImmediateOp_MOVI)))))))))))))) ) : SailM
    ImmediateOp )
  let operation := operation
  let imm64 ← (( do
    (AdvSIMDExpandImm op cmode (((((((a +++ b) +++ c) +++ d) +++ e) +++ f) +++ g) +++ h)) ) : SailM
    (BitVec 64) )
  let imm : (BitVec (Sail.Int.toNatChecked (datasize : Int))) :=
    (Sail.BitVec.castWidth (BitVec.replicateBits imm64
      (Sail.Int.toNatChecked ((Int.ediv (Sail.Int.toNatChecked (datasize)) 64)))))
  (execute_aarch64_instrs_vector_logical (Sail.Int.toNatChecked (datasize))
    (Sail.BitVec.castWidth imm) operation (Sail.Int.toNatChecked (rd)))


def decode_bif_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let op ← (( do (undefined_VBitOp (← occLabel 4000) ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match opc2 with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op)


def decode_bit_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let op ← (( do (undefined_VBitOp (← occLabel 4001) ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match opc2 with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op)


def decode_bsl_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let op ← (( do (undefined_VBitOp (← occLabel 4002) ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match opc2 with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op)


def decode_eor_advsimd_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor (Rd : (BitVec 5)) (Rn : (BitVec 5)) (Rm : (BitVec 5)) (opc2 : (BitVec 2)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  let m : Int := (BitVec.toNat Rm)
  let esize : Nat := 8
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int := (Int.ediv (Sail.Int.toNatChecked (datasize)) esize)
  let op ← (( do (undefined_VBitOp (← occLabel 4003) ()) ) : SailM VBitOp )
  let op : VBitOp :=
    match opc2 with
    | 0b00 => VBitOp_VEOR
    | 0b01 => VBitOp_VBSL
    | 0b10 => VBitOp_VBIT
    | _ => VBitOp_VBIF
  let op := op
  (execute_aarch64_instrs_vector_arithmetic_binary_uniform_logical_bsl_eor
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (m))
    (Sail.Int.toNatChecked (n)) op)


def decode_cls_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let countop : CountOp :=
    if ((U == 1#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_vector_arithmetic_unary_clsz countop (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)))


def decode_clz_advsimd_aarch64_instrs_vector_arithmetic_unary_clsz (Rd : (BitVec 5)) (Rn : (BitVec 5)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size == 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let countop : CountOp :=
    if ((U == 1#1) : Bool)
    then CountOp_CLZ
    else CountOp_CLS
  (execute_aarch64_instrs_vector_arithmetic_unary_clsz countop (Sail.Int.toNatChecked (d))
    (Sail.Int.toNatChecked (datasize)) elements (Sail.Int.toNatChecked (esize))
    (Sail.Int.toNatChecked (n)))


def decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4035) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmeq_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison ← (( do (undefined_CompareOp (← occLabel 4036) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4037) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmge_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison ← (( do (undefined_CompareOp (← occLabel 4038) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if ((size != 0b11#2) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int := esize
  let elements : Nat := 1
  let comparison ← (( do (undefined_CompareOp (← occLabel 4039) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


def decode_cmgt_advsimd_zero_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_simd (Rd : (BitVec 5)) (Rn : (BitVec 5)) (op : (BitVec 1)) (size : (BitVec 2)) (U : (BitVec 1)) (Q : (BitVec 1)) : SailM Unit := do
  let d : Int := (BitVec.toNat Rd)
  let n : Int := (BitVec.toNat Rn)
  if (((size +++ Q) == 0b110#3) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let esize : Int := (Int.shiftl 8 (BitVec.toNat size))
  let datasize : Int :=
    if ((Q == 1#1) : Bool)
    then 128
    else 64
  let elements : Int :=
    (Int.ediv (Sail.Int.toNatChecked (datasize)) (Sail.Int.toNatChecked (esize)))
  let comparison ← (( do (undefined_CompareOp (← occLabel 4040) ()) ) : SailM CompareOp )
  let comparison : CompareOp :=
    match (BitVec.setWidth 2 (op +++ U)) with
    | 0b00 => CompareOp_GT
    | 0b01 => CompareOp_GE
    | 0b10 => CompareOp_EQ
    | _ => CompareOp_LE
  let comparison := comparison
  (execute_aarch64_instrs_vector_arithmetic_unary_cmp_int_bulk_sisd comparison
    (Sail.Int.toNatChecked (d)) (Sail.Int.toNatChecked (datasize)) elements
    (Sail.Int.toNatChecked (esize)) (Sail.Int.toNatChecked (n)))


end ArmFull.Functions
