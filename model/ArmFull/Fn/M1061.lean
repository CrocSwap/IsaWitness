import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0145
import ArmFull.Fn.M0948
import ArmFull.Fn.M0949
import ArmFull.Fn.M0950
import ArmFull.Fn.M0951
import ArmFull.Fn.M1017
import ArmFull.Fn.M1023
import ArmFull.Fn.M1024

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

def decode_ldgm_aarch64_instrs_integer_tags_mcgettagarray (Xt : (BitVec 5)) (Xn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Xt)
  let n : Int := (BitVec.toNat Xn)
  (execute_aarch64_instrs_integer_tags_mcgettagarray (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (t)))


def decode_stgm_aarch64_instrs_integer_tags_mcsettagarray (Xt : (BitVec 5)) (Xn : (BitVec 5)) : SailM Unit := do
  let w__0 ← (( do (HaveMTE2Ext ()) ) : SailM Bool )
  if ((! w__0) : Bool)
  then sailThrow ((Error_Undefined ()))
  else (pure (()))
  let t : Int := (BitVec.toNat Xt)
  let n : Int := (BitVec.toNat Xn)
  (execute_aarch64_instrs_integer_tags_mcsettagarray (Sail.Int.toNatChecked (n))
    (Sail.Int.toNatChecked (t)))


/-- Type quantifiers: pc : Int -/
def __DecodeA64_SVE__seg8 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__685 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
             __opcode 21 13)) == (0b010000101#9 : (BitVec 9)))) : Bool) : Bool)
    then
      (do
        let w__684 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__684 <b 1379) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__685 : Bool)
  then
    (do
      writeReg SEE 1379
      let size := (BitVec.slice __opcode 22 2)
      let U := (BitVec.slice __opcode 16 1)
      let Pg := (BitVec.slice __opcode 10 3)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_SXTB_Z_P_Z__ size U Pg Zn Zd)
      (pure false))
  else
    (do
      let w__687 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                 __opcode 21 13)) == (0b010010101#9 : (BitVec 9)))) : Bool) : Bool)
        then
          (do
            let w__686 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__686 <b 1380) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__687 : Bool)
      then
        (do
          writeReg SEE 1380
          let size := (BitVec.slice __opcode 22 2)
          let U := (BitVec.slice __opcode 16 1)
          let Pg := (BitVec.slice __opcode 10 3)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_SXTH_Z_P_Z__ size U Pg Zn Zd)
          (pure false))
      else
        (do
          let w__689 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                     __opcode 21 13)) == (0b010100101#9 : (BitVec 9)))) : Bool) : Bool)
            then
              (do
                let w__688 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__688 <b 1381) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__689 : Bool)
          then
            (do
              writeReg SEE 1381
              let size := (BitVec.slice __opcode 22 2)
              let U := (BitVec.slice __opcode 16 1)
              let Pg := (BitVec.slice __opcode 10 3)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zd := (BitVec.slice __opcode 0 5)
              (decode_SXTW_Z_P_Z__ size U Pg Zn Zd)
              (pure false))
          else
            (do
              let w__691 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                         __opcode 21 13)) == (0b011010001#9 : (BitVec 9)))) : Bool) : Bool)
                then
                  (do
                    let w__690 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__690 <b 1382) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__691 : Bool)
              then
                (do
                  writeReg SEE 1382
                  let size := (BitVec.slice __opcode 22 2)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Vd := (BitVec.slice __opcode 0 5)
                  (decode_ANDV_R_P_Z__ size Pg Zn Vd)
                  (pure false))
              else
                (do
                  let w__693 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                             __opcode 21 13)) == (0b011001001#9 : (BitVec 9)))) : Bool) : Bool)
                    then
                      (do
                        let w__692 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__692 <b 1383) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__693 : Bool)
                  then
                    (do
                      writeReg SEE 1383
                      let size := (BitVec.slice __opcode 22 2)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Vd := (BitVec.slice __opcode 0 5)
                      (decode_EORV_R_P_Z__ size Pg Zn Vd)
                      (pure false))
                  else
                    (do
                      let w__695 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                 __opcode 21 13)) == (0b011000001#9 : (BitVec 9)))) : Bool) : Bool)
                        then
                          (do
                            let w__694 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__694 <b 1384) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__695 : Bool)
                      then
                        (do
                          writeReg SEE 1384
                          let size := (BitVec.slice __opcode 22 2)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Vd := (BitVec.slice __opcode 0 5)
                          (decode_ORV_R_P_Z__ size Pg Zn Vd)
                          (pure false))
                      else
                        (do
                          let w__697 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                     __opcode 21 13)) == (0b000000001#9 : (BitVec 9)))) : Bool) : Bool)
                            then
                              (do
                                let w__696 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__696 <b 1385) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__697 : Bool)
                          then
                            (do
                              writeReg SEE 1385
                              let size := (BitVec.slice __opcode 22 2)
                              let U := (BitVec.slice __opcode 16 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Vd := (BitVec.slice __opcode 0 5)
                              (decode_SADDV_R_P_Z__ size U Pg Zn Vd)
                              (pure false))
                          else
                            (do
                              let w__699 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 21 13)) == (0b000001001#9 : (BitVec 9)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__698 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__698 <b 1386) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__699 : Bool)
                              then
                                (do
                                  writeReg SEE 1386
                                  let size := (BitVec.slice __opcode 22 2)
                                  let U := (BitVec.slice __opcode 16 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Vd := (BitVec.slice __opcode 0 5)
                                  (decode_UADDV_R_P_Z__ size U Pg Zn Vd)
                                  (pure false))
                              else
                                (do
                                  let w__701 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 21 13)) == (0b001001001#9 : (BitVec 9)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__700 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__700 <b 1387) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__701 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1387
                                      let size := (BitVec.slice __opcode 22 2)
                                      let U := (BitVec.slice __opcode 16 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Vd := (BitVec.slice __opcode 0 5)
                                      (decode_UMAXV_R_P_Z__ size U Pg Zn Vd)
                                      (pure false))
                                  else
                                    (do
                                      let w__703 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 21 13)) == (0b001000001#9 : (BitVec 9)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__702 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__702 <b 1388) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__703 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1388
                                          let size := (BitVec.slice __opcode 22 2)
                                          let U := (BitVec.slice __opcode 16 1)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Vd := (BitVec.slice __opcode 0 5)
                                          (decode_SMAXV_R_P_Z__ size U Pg Zn Vd)
                                          (pure false))
                                      else
                                        (do
                                          let w__705 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                     __opcode 21 13)) == (0b001011001#9 : (BitVec 9)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__704 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__704 <b 1389) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__705 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1389
                                              let size := (BitVec.slice __opcode 22 2)
                                              let U := (BitVec.slice __opcode 16 1)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Vd := (BitVec.slice __opcode 0 5)
                                              (decode_UMINV_R_P_Z__ size U Pg Zn Vd)
                                              (pure false))
                                          else
                                            (do
                                              let w__707 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 21 13)) == (0b001010001#9 : (BitVec 9)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__706 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__706 <b 1390) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__707 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1390
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let U := (BitVec.slice __opcode 16 1)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Vd := (BitVec.slice __opcode 0 5)
                                                  (decode_SMINV_R_P_Z__ size U Pg Zn Vd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__709 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b010000#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__708 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__708 <b 1391) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__709 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1391
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let imm5b := (BitVec.slice __opcode 16 5)
                                                      let imm5 := (BitVec.slice __opcode 5 5)
                                                      let Zd := (BitVec.slice __opcode 0 5)
                                                      (decode_INDEX_Z_II__ size imm5b imm5 Zd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__711 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b010010#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__710 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__710 <b 1392) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__711 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1392
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let Rm := (BitVec.slice __opcode 16 5)
                                                          let imm5 := (BitVec.slice __opcode 5 5)
                                                          let Zd := (BitVec.slice __opcode 0 5)
                                                          (decode_INDEX_Z_IR__ size Rm imm5 Zd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__713 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                       __opcode 15 10)) == (0b010001#6 : (BitVec 6))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__712 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__712 <b 1393) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__713 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1393
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let imm5 :=
                                                                (BitVec.slice __opcode 16 5)
                                                              let Rn := (BitVec.slice __opcode 5 5)
                                                              let Zd := (BitVec.slice __opcode 0 5)
                                                              (decode_INDEX_Z_RI__ size imm5 Rn Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__715 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                         __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                           __opcode 15 10)) == (0b010011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__714 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__714 <b 1394) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__715 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1394
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let Rm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_INDEX_Z_RR__ size Rm Rn Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__717 ← (( do
                                                                    if ((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                           __opcode 31 18)) == (0b00000101100000#14 : (BitVec 14))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__716 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__716 <b 1395) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__717 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1395
                                                                      let imm13 :=
                                                                        (BitVec.slice __opcode 5 13)
                                                                      let Zdn :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_AND_Z_ZI__ imm13 Zdn)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__719 ← (( do
                                                                        if ((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                               __opcode 31 18)) == (0b00000101010000#14 : (BitVec 14))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__718 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__718 <b 1396) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__719 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1396
                                                                          let imm13 :=
                                                                            (BitVec.slice __opcode 5
                                                                              13)
                                                                          let Zdn :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_EOR_Z_ZI__ imm13
                                                                            Zdn)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__721 ← (( do
                                                                            if ((((Sail.BitVec.castWidth (m := 14) (Sail.BitVec.extractLsb
                                                                                   __opcode 31 18)) == (0b00000101000000#14 : (BitVec 14))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__720 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__720 <b 1397) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__721 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1397
                                                                              let imm13 :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 13)
                                                                              let Zdn :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_ORR_Z_ZI__
                                                                                imm13 Zdn)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__723 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           15 13)) == (0b110#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__722 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__722 <b 1398) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__723 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1398
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 1)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Za :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zdn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_MAD_Z_P_ZZZ__
                                                                                    size Zm op Pg Za
                                                                                    Zdn)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__725 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               15 13)) == (0b111#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__724 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__724 <b 1399) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__725 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1399
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let op :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 1)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Za :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zdn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_MSB_Z_P_ZZZ__
                                                                                        size Zm op
                                                                                        Pg Za Zdn)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__727 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   15
                                                                                                   13)) == (0b010#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__726 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__726 <b 1400) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__727 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1400
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let op :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 1)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zda :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_MLA_Z_P_ZZZ__
                                                                                            size Zm
                                                                                            op Pg Zn
                                                                                            Zda)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__729 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       15
                                                                                                       13)) == (0b011#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__728 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__728 <b 1401) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__729 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1401
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let op :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  1)
                                                                                              let Pg :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  3)
                                                                                              let Zn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let Zda :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_MLS_Z_P_ZZZ__
                                                                                                size
                                                                                                Zm
                                                                                                op
                                                                                                Pg
                                                                                                Zn
                                                                                                Zda)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__731 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 22) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       31
                                                                                                       10)) == (0b0000010000100000101111#22 : (BitVec 22))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__730 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__730 <b 1402) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__731 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1402
                                                                                                  let Zn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Zd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_MOVPRFX_Z_Z__
                                                                                                    Zn
                                                                                                    Zd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__733 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               17)) == (0b01000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               15
                                                                                                               13)) == (0b001#3 : (BitVec 3))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__732 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__732 <b 1403) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__733 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1403
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let M :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          1)
                                                                                                      let Pg :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          3)
                                                                                                      let Zn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Zd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_MOVPRFX_Z_P_Z__
                                                                                                        size
                                                                                                        M
                                                                                                        Pg
                                                                                                        Zn
                                                                                                        Zd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__735 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 24)) == (0x25#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   14)) == (0x82#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   9
                                                                                                                   9)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__734 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__734 <b 1404) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__735 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1404
                                                                                                          let size :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              2)
                                                                                                          let Pg :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              4)
                                                                                                          let Pn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              4)
                                                                                                          let Rd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_CNTP_R_P_P__
                                                                                                            size
                                                                                                            Pg
                                                                                                            Pn
                                                                                                            Rd)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__737 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 13) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       21
                                                                                                                       9)) == (0b1101000100000#13 : (BitVec 13))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       4
                                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__736 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__736 <b 1405) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__737 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1405
                                                                                                              let size :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  2)
                                                                                                              let Pn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  4)
                                                                                                              let Pd :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  4)
                                                                                                              (decode_REV_P_P__
                                                                                                                size
                                                                                                                Pn
                                                                                                                Pd)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__739 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           21
                                                                                                                           20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             9)) == (0b0101000#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             4
                                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__738 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__738 <b 1406) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__739 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1406
                                                                                                                  let size :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      2)
                                                                                                                  let Pm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      4)
                                                                                                                  let H :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      1)
                                                                                                                  let Pn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      4)
                                                                                                                  let Pd :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      4)
                                                                                                                  (decode_TRN1_P_PP__
                                                                                                                    size
                                                                                                                    Pm
                                                                                                                    H
                                                                                                                    Pn
                                                                                                                    Pd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__741 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               21
                                                                                                                               20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 15
                                                                                                                                 9)) == (0b0101010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 4
                                                                                                                                 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__740 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__740 <b 1407) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__741 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1407
                                                                                                                      let size :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          2)
                                                                                                                      let Pm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          4)
                                                                                                                      let H :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          1)
                                                                                                                      let Pn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          4)
                                                                                                                      let Pd :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          4)
                                                                                                                      (decode_TRN2_P_PP__
                                                                                                                        size
                                                                                                                        Pm
                                                                                                                        H
                                                                                                                        Pn
                                                                                                                        Pd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__743 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   21
                                                                                                                                   20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     15
                                                                                                                                     9)) == (0b0100100#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     4
                                                                                                                                     4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__742 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__742 <b 1408) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__743 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1408
                                                                                                                          let size :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              2)
                                                                                                                          let Pm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              4)
                                                                                                                          let H :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              1)
                                                                                                                          let Pn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              4)
                                                                                                                          let Pd :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_UZP1_P_PP__
                                                                                                                            size
                                                                                                                            Pm
                                                                                                                            H
                                                                                                                            Pn
                                                                                                                            Pd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__745 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       21
                                                                                                                                       20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         15
                                                                                                                                         9)) == (0b0100110#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         4
                                                                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__744 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__744 <b 1409) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__745 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1409
                                                                                                                              let size :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  2)
                                                                                                                              let Pm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  4)
                                                                                                                              let H :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  1)
                                                                                                                              let Pn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  4)
                                                                                                                              let Pd :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_UZP2_P_PP__
                                                                                                                                size
                                                                                                                                Pm
                                                                                                                                H
                                                                                                                                Pn
                                                                                                                                Pd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__747 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           21
                                                                                                                                           20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             15
                                                                                                                                             9)) == (0b0100000#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             4
                                                                                                                                             4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__746 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__746 <b 1410) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__747 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1410
                                                                                                                                  let size :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      2)
                                                                                                                                  let Pm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      4)
                                                                                                                                  let H :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
                                                                                                                                  let Pn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      4)
                                                                                                                                  let Pd :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_ZIP1_P_PP__
                                                                                                                                    size
                                                                                                                                    Pm
                                                                                                                                    H
                                                                                                                                    Pn
                                                                                                                                    Pd)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__749 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               21
                                                                                                                                               20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 9)) == (0b0100010#7 : (BitVec 7))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 4
                                                                                                                                                 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__748 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__748 <b 1411) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__749 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1411
                                                                                                                                      let size :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          2)
                                                                                                                                      let Pm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          4)
                                                                                                                                      let H :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          1)
                                                                                                                                      let Pn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          4)
                                                                                                                                      let Pd :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      (decode_ZIP2_P_PP__
                                                                                                                                        size
                                                                                                                                        Pm
                                                                                                                                        H
                                                                                                                                        Pn
                                                                                                                                        Pd)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__751 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 24)) == (0x05#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 21
                                                                                                                                                 10)) == (0xE0E#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__750 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__750 <b 1412) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__751 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1412
                                                                                                                                          let size :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              2)
                                                                                                                                          let Zn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zd :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_REV_Z_Z__
                                                                                                                                            size
                                                                                                                                            Zn
                                                                                                                                            Zd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__753 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       21
                                                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       15
                                                                                                                                                       10)) == (0b001100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__752 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__752 <b 1413) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__753 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1413
                                                                                                                                              let size :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  2)
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let Zn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zd :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_TBL_Z_ZZ_1
                                                                                                                                                size
                                                                                                                                                Zm
                                                                                                                                                Zn
                                                                                                                                                Zd)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__755 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           21
                                                                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           15
                                                                                                                                                           10)) == (0b001010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__754 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__754 <b 1414) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__755 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1414
                                                                                                                                                  let size :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      2)
                                                                                                                                                  let Zm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let Zn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Zd :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_TBL_Z_ZZ_2
                                                                                                                                                    size
                                                                                                                                                    Zm
                                                                                                                                                    Zn
                                                                                                                                                    Zd)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__757 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               21
                                                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               15
                                                                                                                                                               10)) == (0b011100#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__756 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__756 <b 1415) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__757 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1415
                                                                                                                                                      let size :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          2)
                                                                                                                                                      let Zm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let H :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          1)
                                                                                                                                                      let Zn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Zd :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_TRN1_Z_ZZ__
                                                                                                                                                        size
                                                                                                                                                        Zm
                                                                                                                                                        H
                                                                                                                                                        Zn
                                                                                                                                                        Zd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__759 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   21
                                                                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   10)) == (0b011101#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__758 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__758 <b 1416) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__759 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1416
                                                                                                                                                          let size :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              2)
                                                                                                                                                          let Zm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              5)
                                                                                                                                                          let H :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              1)
                                                                                                                                                          let Zn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Zd :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_TRN2_Z_ZZ__
                                                                                                                                                            size
                                                                                                                                                            Zm
                                                                                                                                                            H
                                                                                                                                                            Zn
                                                                                                                                                            Zd)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__761 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       21
                                                                                                                                                                       21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       15
                                                                                                                                                                       10)) == (0b011010#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__760 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__760 <b 1417) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__761 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1417
                                                                                                                                                              let size :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  2)
                                                                                                                                                              let Zm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  5)
                                                                                                                                                              let H :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  1)
                                                                                                                                                              let Zn :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  5
                                                                                                                                                                  5)
                                                                                                                                                              let Zd :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  0
                                                                                                                                                                  5)
                                                                                                                                                              (decode_UZP1_Z_ZZ__
                                                                                                                                                                size
                                                                                                                                                                Zm
                                                                                                                                                                H
                                                                                                                                                                Zn
                                                                                                                                                                Zd)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__763 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           21
                                                                                                                                                                           21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           15
                                                                                                                                                                           10)) == (0b011011#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__762 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__762 <b 1418) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__763 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1418
                                                                                                                                                                  let size :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      2)
                                                                                                                                                                  let Zm :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      5)
                                                                                                                                                                  let H :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      1)
                                                                                                                                                                  let Zn :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      5
                                                                                                                                                                      5)
                                                                                                                                                                  let Zd :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      0
                                                                                                                                                                      5)
                                                                                                                                                                  (decode_UZP2_Z_ZZ__
                                                                                                                                                                    size
                                                                                                                                                                    Zm
                                                                                                                                                                    H
                                                                                                                                                                    Zn
                                                                                                                                                                    Zd)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__765 ← (( do
                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                             __opcode
                                                                                                                                                                             31
                                                                                                                                                                             24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               21
                                                                                                                                                                               21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                               __opcode
                                                                                                                                                                               15
                                                                                                                                                                               10)) == (0b011000#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__764 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__764 <b 1419) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__765 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 1419
                                                                                                                                                                      let size :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          22
                                                                                                                                                                          2)
                                                                                                                                                                      let Zm :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          16
                                                                                                                                                                          5)
                                                                                                                                                                      let H :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          10
                                                                                                                                                                          1)
                                                                                                                                                                      let Zn :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          5
                                                                                                                                                                          5)
                                                                                                                                                                      let Zd :=
                                                                                                                                                                        (BitVec.slice
                                                                                                                                                                          __opcode
                                                                                                                                                                          0
                                                                                                                                                                          5)
                                                                                                                                                                      (decode_ZIP1_Z_ZZ__
                                                                                                                                                                        size
                                                                                                                                                                        Zm
                                                                                                                                                                        H
                                                                                                                                                                        Zn
                                                                                                                                                                        Zd)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__767 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 24)) == (0x05#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   21
                                                                                                                                                                                   21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                   __opcode
                                                                                                                                                                                   15
                                                                                                                                                                                   10)) == (0b011001#6 : (BitVec 6))))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__766 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__766 <b 1420) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__767 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 1420
                                                                                                                                                                          let size :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              22
                                                                                                                                                                              2)
                                                                                                                                                                          let Zm :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              16
                                                                                                                                                                              5)
                                                                                                                                                                          let H :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              10
                                                                                                                                                                              1)
                                                                                                                                                                          let Zn :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              5
                                                                                                                                                                              5)
                                                                                                                                                                          let Zd :=
                                                                                                                                                                            (BitVec.slice
                                                                                                                                                                              __opcode
                                                                                                                                                                              0
                                                                                                                                                                              5)
                                                                                                                                                                          (decode_ZIP2_Z_ZZ__
                                                                                                                                                                            size
                                                                                                                                                                            Zm
                                                                                                                                                                            H
                                                                                                                                                                            Zn
                                                                                                                                                                            Zd)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__769 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     21)) == (0b00000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     15
                                                                                                                                                                                     10)) == (0b000110#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__768 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__768 <b 1421) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__769 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 1421
                                                                                                                                                                              let Zm :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  16
                                                                                                                                                                                  5)
                                                                                                                                                                              let H :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  10
                                                                                                                                                                                  1)
                                                                                                                                                                              let Zn :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  5
                                                                                                                                                                                  5)
                                                                                                                                                                              let Zd :=
                                                                                                                                                                                (BitVec.slice
                                                                                                                                                                                  __opcode
                                                                                                                                                                                  0
                                                                                                                                                                                  5)
                                                                                                                                                                              (decode_TRN1_Z_ZZ_Q
                                                                                                                                                                                Zm
                                                                                                                                                                                H
                                                                                                                                                                                Zn
                                                                                                                                                                                Zd)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__771 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         21)) == (0b00000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         15
                                                                                                                                                                                         10)) == (0b000111#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__770 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__770 <b 1422) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__771 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 1422
                                                                                                                                                                                  let Zm :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      16
                                                                                                                                                                                      5)
                                                                                                                                                                                  let H :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      10
                                                                                                                                                                                      1)
                                                                                                                                                                                  let Zn :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      5
                                                                                                                                                                                      5)
                                                                                                                                                                                  let Zd :=
                                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                                      __opcode
                                                                                                                                                                                      0
                                                                                                                                                                                      5)
                                                                                                                                                                                  (decode_TRN2_Z_ZZ_Q
                                                                                                                                                                                    Zm
                                                                                                                                                                                    H
                                                                                                                                                                                    Zn
                                                                                                                                                                                    Zd)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
