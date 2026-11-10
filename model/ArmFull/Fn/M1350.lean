import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M0164
import ArmFull.Fn.M0179
import ArmFull.Fn.M0928
import ArmFull.Fn.M1060
import ArmFull.Fn.M1095
import ArmFull.Fn.M1147
import ArmFull.Fn.M1148
import ArmFull.Fn.M1182

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

/-- Type quantifiers: pc : Int -/
def __DecodeT32__seg14 (pc : Int) (__opcode : (BitVec 32)) : SailM Unit := do
  let w__974 ← (( do
    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 21 16)) == (0b110110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                 __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
    then
      (do
        let w__973 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__973 <b 3885) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__974 : Bool)
  then
    (do
      writeReg SEE 3885
      let D := (BitVec.slice __opcode 22 1)
      let Vd := (BitVec.slice __opcode 12 4)
      let size := (BitVec.slice __opcode 8 2)
      let op := (BitVec.slice __opcode 7 1)
      let M := (BitVec.slice __opcode 5 1)
      let Vm := (BitVec.slice __opcode 0 4)
      (decode_aarch32_instrs_VRINTZ_vfp_T1enc_A_txt D Vd size op M Vm))
  else
    (do
      let w__976 ← (( do
        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb __opcode 31 23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                   __opcode 11 10)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 6 6)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
        then
          (do
            let w__975 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__975 <b 3887) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__976 : Bool)
      then
        (do
          writeReg SEE 3887
          let D := (BitVec.slice __opcode 22 1)
          let cc := (BitVec.slice __opcode 20 2)
          let Vn := (BitVec.slice __opcode 16 4)
          let Vd := (BitVec.slice __opcode 12 4)
          let size := (BitVec.slice __opcode 8 2)
          let N := (BitVec.slice __opcode 7 1)
          let M := (BitVec.slice __opcode 5 1)
          let Vm := (BitVec.slice __opcode 0 4)
          (decode_aarch32_instrs_VSEL_T1enc_A_txt D cc Vn Vd size N M Vm))
      else
        (do
          let w__978 ← (( do
            if (((__opcode == 0b11110011101011111000000000010000#32) : Bool) : Bool)
            then
              (do
                let w__977 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__977 <b 3891) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__978 : Bool)
          then
            (do
              writeReg SEE 3891
              if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 28)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 29)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 30)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 31)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                           __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                         __opcode 4)])) != 0#1)) : Bool)
              then sailThrow ((Error_ConstrainedUnpredictable ()))
              else
                (do
                  (decode_aarch32_instrs_ESB_T1enc_A_txt ())))
          else
            (do
              let w__980 ← (( do
                if (((__opcode == 0b11110011101011111000000000010010#32) : Bool) : Bool)
                then
                  (do
                    let w__979 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__979 <b 3893) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__980 : Bool)
              then
                (do
                  writeReg SEE 3893
                  if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 28)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 29)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 30)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 31)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                               __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                             __opcode 4)])) != 0#1)) : Bool)
                  then sailThrow ((Error_ConstrainedUnpredictable ()))
                  else
                    (do
                      (decode_aarch32_instrs_TSB_T1enc_A_txt ())))
              else
                (do
                  let w__982 ← (( do
                    if (((__opcode == 0b11110011101011111000000000010100#32) : Bool) : Bool)
                    then
                      (do
                        let w__981 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__981 <b 3895) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__982 : Bool)
                  then
                    (do
                      writeReg SEE 3895
                      if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 28)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 29)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 30)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 31)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                   __opcode 2)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                 __opcode 4)])) != 0#1)) : Bool)
                      then sailThrow ((Error_ConstrainedUnpredictable ()))
                      else
                        (do
                          (decode_aarch32_instrs_CSDB_T1enc_A_txt ())))
                  else
                    (do
                      let w__984 ← (( do
                        if (((__opcode == 0b11110011101111111000111101000000#32) : Bool) : Bool)
                        then
                          (do
                            let w__983 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__983 <b 3897) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__984 : Bool)
                      then
                        (do
                          writeReg SEE 3897
                          if (((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                       __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                     __opcode 11)])) != 1#1)) : Bool)
                          then sailThrow ((Error_ConstrainedUnpredictable ()))
                          else
                            (do
                              (decode_aarch32_instrs_SSBB_T1enc_A_txt ())))
                      else
                        (do
                          let w__986 ← (( do
                            if (((__opcode == 0b11110011101111111000111101000100#32) : Bool) : Bool)
                            then
                              (do
                                let w__985 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__985 <b 3899) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__986 : Bool)
                          then
                            (do
                              writeReg SEE 3899
                              if (((((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access __opcode
                                                       16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                       __opcode 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                     __opcode 18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                   __opcode 19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                 __opcode 13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                               __opcode 8)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                             __opcode 9)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                           __opcode 10)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                         __opcode 11)])) != 1#1)) : Bool)
                              then sailThrow ((Error_ConstrainedUnpredictable ()))
                              else
                                (do
                                  (decode_aarch32_instrs_PSSBB_T1enc_A_txt ())))
                          else
                            (do
                              let w__988 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                         __opcode 31 23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                           __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 11 8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__987 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__987 <b 3901) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__988 : Bool)
                              then
                                (do
                                  writeReg SEE 3901
                                  let D := (BitVec.slice __opcode 22 1)
                                  let Vn := (BitVec.slice __opcode 16 4)
                                  let Vd := (BitVec.slice __opcode 12 4)
                                  let N := (BitVec.slice __opcode 7 1)
                                  let Q := (BitVec.slice __opcode 6 1)
                                  let M := (BitVec.slice __opcode 5 1)
                                  let U := (BitVec.slice __opcode 4 1)
                                  let Vm := (BitVec.slice __opcode 0 4)
                                  (decode_aarch32_instrs_VDOT_T1enc_A_txt D Vn Vd N Q M U Vm))
                              else
                                (do
                                  let w__990 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                             __opcode 31 23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                               __opcode 21 20)) == (0b10#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                               __opcode 11 8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__989 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__989 <b 3903) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__990 : Bool)
                                  then
                                    (do
                                      writeReg SEE 3903
                                      let op1 := (BitVec.slice __opcode 23 1)
                                      let D := (BitVec.slice __opcode 22 1)
                                      let op2 := (BitVec.slice __opcode 20 2)
                                      let Vn := (BitVec.slice __opcode 16 4)
                                      let Vd := (BitVec.slice __opcode 12 4)
                                      let N := (BitVec.slice __opcode 7 1)
                                      let Q := (BitVec.slice __opcode 6 1)
                                      let M := (BitVec.slice __opcode 5 1)
                                      let U := (BitVec.slice __opcode 4 1)
                                      let Vm := (BitVec.slice __opcode 0 4)
                                      (decode_aarch32_instrs_VDOT_s_T1enc_A_txt op1 D op2 Vn Vd N Q
                                        M U Vm))
                                  else
                                    (do
                                      let w__992 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                 __opcode 31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                   __opcode 21 16)) == (0b111001#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                     __opcode 11 6)) == (0b101111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                     __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__991 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__991 <b 3905) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__992 : Bool)
                                      then
                                        (do
                                          writeReg SEE 3905
                                          let D := (BitVec.slice __opcode 22 1)
                                          let Vd := (BitVec.slice __opcode 12 4)
                                          let M := (BitVec.slice __opcode 5 1)
                                          let Vm := (BitVec.slice __opcode 0 4)
                                          (decode_aarch32_instrs_VJCVT_T1enc_A_txt D Vd M Vm))
                                      else
                                        (do
                                          let w__994 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                     __opcode 31 25)) == (0b1111110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 21 21)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                         __opcode 11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                         __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__993 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__993 <b 3907) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__994 : Bool)
                                          then
                                            (do
                                              writeReg SEE 3907
                                              let rot := (BitVec.slice __opcode 23 2)
                                              let D := (BitVec.slice __opcode 22 1)
                                              let S := (BitVec.slice __opcode 20 1)
                                              let Vn := (BitVec.slice __opcode 16 4)
                                              let Vd := (BitVec.slice __opcode 12 4)
                                              let N := (BitVec.slice __opcode 7 1)
                                              let Q := (BitVec.slice __opcode 6 1)
                                              let M := (BitVec.slice __opcode 5 1)
                                              let Vm := (BitVec.slice __opcode 0 4)
                                              (decode_aarch32_instrs_VCMLA_T1enc_A_txt rot D S Vn Vd
                                                N Q M Vm))
                                          else
                                            (do
                                              let w__996 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0xFE#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                           __opcode 11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__995 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__995 <b 3909) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__996 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 3909
                                                  let S := (BitVec.slice __opcode 23 1)
                                                  let D := (BitVec.slice __opcode 22 1)
                                                  let rot := (BitVec.slice __opcode 20 2)
                                                  let Vn := (BitVec.slice __opcode 16 4)
                                                  let Vd := (BitVec.slice __opcode 12 4)
                                                  let N := (BitVec.slice __opcode 7 1)
                                                  let Q := (BitVec.slice __opcode 6 1)
                                                  let M := (BitVec.slice __opcode 5 1)
                                                  let Vm := (BitVec.slice __opcode 0 4)
                                                  (decode_aarch32_instrs_VCMLA_idx_T1enc_A_txt S D
                                                    rot Vn Vd N Q M Vm))
                                              else
                                                (do
                                                  let w__998 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 7) (Sail.BitVec.extractLsb
                                                             __opcode 31 25)) == (0b1111110#7 : (BitVec 7))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 23 23)) == (1#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                 __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                   __opcode 11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__997 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__997 <b 3911) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__998 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 3911
                                                      let rot := (BitVec.slice __opcode 24 1)
                                                      let D := (BitVec.slice __opcode 22 1)
                                                      let S := (BitVec.slice __opcode 20 1)
                                                      let Vn := (BitVec.slice __opcode 16 4)
                                                      let Vd := (BitVec.slice __opcode 12 4)
                                                      let N := (BitVec.slice __opcode 7 1)
                                                      let Q := (BitVec.slice __opcode 6 1)
                                                      let M := (BitVec.slice __opcode 5 1)
                                                      let Vm := (BitVec.slice __opcode 0 4)
                                                      (decode_aarch32_instrs_VCADD_T1enc_A_txt rot D
                                                        S Vn Vd N Q M Vm))
                                                  else
                                                    (do
                                                      let w__1000 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0xFC#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                   __opcode 21 20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                     __opcode 11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                     __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__999 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__999 <b 3913) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__1000 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 3913
                                                          let S := (BitVec.slice __opcode 23 1)
                                                          let D := (BitVec.slice __opcode 22 1)
                                                          let Vn := (BitVec.slice __opcode 16 4)
                                                          let Vd := (BitVec.slice __opcode 12 4)
                                                          let N := (BitVec.slice __opcode 7 1)
                                                          let Q := (BitVec.slice __opcode 6 1)
                                                          let M := (BitVec.slice __opcode 5 1)
                                                          let Vm := (BitVec.slice __opcode 0 4)
                                                          (decode_aarch32_instrs_VFMAL_T1enc_A_txt S
                                                            D Vn Vd N Q M Vm))
                                                      else
                                                        (do
                                                          let w__1002 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 31 23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                       __opcode 21 21)) == (0#1 : (BitVec 1))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                         __opcode 11 8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                         __opcode 4 4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__1001 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__1001 <b 3915) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__1002 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 3915
                                                              let D := (BitVec.slice __opcode 22 1)
                                                              let S := (BitVec.slice __opcode 20 1)
                                                              let Vn := (BitVec.slice __opcode 16 4)
                                                              let Vd := (BitVec.slice __opcode 12 4)
                                                              let N := (BitVec.slice __opcode 7 1)
                                                              let Q := (BitVec.slice __opcode 6 1)
                                                              let M := (BitVec.slice __opcode 5 1)
                                                              let Vm := (BitVec.slice __opcode 0 4)
                                                              (decode_aarch32_instrs_VFMAL_i_T1enc_A_txt
                                                                D S Vn Vd N Q M Vm))
                                                          else
                                                            (do
                                                              let w__1004 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                         __opcode 31 23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                           __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                             __opcode 11 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                             __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__1003 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__1003 <b 3917) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__1004 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 3917
                                                                  let D :=
                                                                    (BitVec.slice __opcode 22 1)
                                                                  let Vn :=
                                                                    (BitVec.slice __opcode 16 4)
                                                                  let Vd :=
                                                                    (BitVec.slice __opcode 12 4)
                                                                  let N :=
                                                                    (BitVec.slice __opcode 7 1)
                                                                  let Q :=
                                                                    (BitVec.slice __opcode 6 1)
                                                                  let M :=
                                                                    (BitVec.slice __opcode 5 1)
                                                                  let Vm :=
                                                                    (BitVec.slice __opcode 0 4)
                                                                  (decode_aarch32_instrs_VDOT_bf16_T1enc_A_txt
                                                                    D Vn Vd N Q M Vm))
                                                              else
                                                                (do
                                                                  let w__1006 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                             __opcode 31 23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                               __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                 __opcode 11 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                 __opcode 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__1005 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__1005 <b 3919) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__1006 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 3919
                                                                      let D :=
                                                                        (BitVec.slice __opcode 22 1)
                                                                      let Vn :=
                                                                        (BitVec.slice __opcode 16 4)
                                                                      let Vd :=
                                                                        (BitVec.slice __opcode 12 4)
                                                                      let N :=
                                                                        (BitVec.slice __opcode 7 1)
                                                                      let Q :=
                                                                        (BitVec.slice __opcode 6 1)
                                                                      let M :=
                                                                        (BitVec.slice __opcode 5 1)
                                                                      let Vm :=
                                                                        (BitVec.slice __opcode 0 4)
                                                                      (decode_aarch32_instrs_VDOT_bf16_i_T1enc_A_txt
                                                                        D Vn Vd N Q M Vm))
                                                                  else
                                                                    (do
                                                                      let w__1008 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                   __opcode 21 20)) == (0b00#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                     __opcode 11 8)) == (0xC#4 : (BitVec 4))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 6 6)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__1007 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__1007 <b 3921) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__1008 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 3921
                                                                          let D :=
                                                                            (BitVec.slice __opcode
                                                                              22 1)
                                                                          let Vn :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Vd :=
                                                                            (BitVec.slice __opcode
                                                                              12 4)
                                                                          let N :=
                                                                            (BitVec.slice __opcode 7
                                                                              1)
                                                                          let M :=
                                                                            (BitVec.slice __opcode 5
                                                                              1)
                                                                          let Vm :=
                                                                            (BitVec.slice __opcode 0
                                                                              4)
                                                                          (decode_aarch32_instrs_VMMLA_T1enc_A_txt
                                                                            D Vn Vd N M Vm))
                                                                      else
                                                                        (do
                                                                          let w__1010 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 23)) == (0b111111111#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                       __opcode 21
                                                                                       16)) == (0b110110#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 11
                                                                                         6)) == (0b011001#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                         __opcode 4
                                                                                         4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__1009 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__1009 <b 3923) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__1010 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 3923
                                                                              let D :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 1)
                                                                              let Vd :=
                                                                                (BitVec.slice
                                                                                  __opcode 12 4)
                                                                              let M :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 1)
                                                                              let Vm :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 4)
                                                                              (decode_aarch32_instrs_VCVT_T1enc_A_txt
                                                                                D Vd M Vm))
                                                                          else
                                                                            (do
                                                                              let w__1012 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           21 16)) == (0b110011#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             11 6)) == (0b100101#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__1011 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__1011 <b 3925) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__1012 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 3925
                                                                                  let D :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 1)
                                                                                  let Vd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 12 4)
                                                                                  let M :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 1)
                                                                                  let Vm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 4)
                                                                                  (decode_aarch32_instrs_VCVTB_bf16_T1enc_A_txt
                                                                                    D Vd M Vm))
                                                                              else
                                                                                (do
                                                                                  let w__1014 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 23)) == (0b111011101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               21 16)) == (0b110011#6 : (BitVec 6))) && (((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 11
                                                                                                 6)) == (0b100111#6 : (BitVec 6))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 4 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__1013 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__1013 <b 3927) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__1014 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 3927
                                                                                      let D :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 1)
                                                                                      let Vd :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          12 4)
                                                                                      let M :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          1)
                                                                                      let Vm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          4)
                                                                                      (decode_aarch32_instrs_VCVTT_T1enc_A_txt
                                                                                        D Vd M Vm))
                                                                                  else
                                                                                    (do
                                                                                      let w__1016 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 23)) == (0b111111000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   21
                                                                                                   20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     11
                                                                                                     8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     4
                                                                                                     4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__1015 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__1015 <b 3929) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__1016 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 3929
                                                                                          let D :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 1)
                                                                                          let Vn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 4)
                                                                                          let Vd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              12 4)
                                                                                          let N :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              7 1)
                                                                                          let Q :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              6 1)
                                                                                          let M :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 1)
                                                                                          let Vm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 4)
                                                                                          (decode_aarch32_instrs_VFMA_bf_T1enc_A_txt
                                                                                            D Vn Vd
                                                                                            N Q M Vm))
                                                                                      else
                                                                                        (do
                                                                                          let w__1018 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     23)) == (0b111111100#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       21
                                                                                                       20)) == (0b11#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         11
                                                                                                         8)) == (0x8#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         4
                                                                                                         4)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__1017 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__1017 <b 3931) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__1018 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 3931
                                                                                              let D :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  1)
                                                                                              let Vn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  4)
                                                                                              let Vd :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  12
                                                                                                  4)
                                                                                              let N :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  7
                                                                                                  1)
                                                                                              let Q :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  6
                                                                                                  1)
                                                                                              let M :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  1)
                                                                                              let Vm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  4)
                                                                                              (decode_aarch32_instrs_VFMA_bfs_T1enc_A_txt
                                                                                                D Vn
                                                                                                Vd N
                                                                                                Q M
                                                                                                Vm))
                                                                                          else
                                                                                            (do
                                                                                              let w__1020 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0xFC#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           21
                                                                                                           20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             11
                                                                                                             8)) == (0xC#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             6
                                                                                                             6)) == (1#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__1019 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__1019 <b 3933) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__1020 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 3933
                                                                                                  let B :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      23
                                                                                                      1)
                                                                                                  let D :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      1)
                                                                                                  let Vn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      4)
                                                                                                  let Vd :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      12
                                                                                                      4)
                                                                                                  let N :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      7
                                                                                                      1)
                                                                                                  let M :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      1)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      4
                                                                                                      1)
                                                                                                  let Vm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      4)
                                                                                                  (decode_aarch32_instrs_MMLA_T1enc_A_txt
                                                                                                    B
                                                                                                    D
                                                                                                    Vn
                                                                                                    Vd
                                                                                                    N
                                                                                                    M
                                                                                                    U
                                                                                                    Vm))
                                                                                              else
                                                                                                (do
                                                                                                  let w__1022 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             23)) == (0b111111001#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               21
                                                                                                               20)) == (0b10#2 : (BitVec 2))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 11
                                                                                                                 8)) == (0xD#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 4
                                                                                                                 4)) == (0#1 : (BitVec 1)))))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__1021 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__1021 <b 3935) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__1022 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 3935
                                                                                                      let D :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          1)
                                                                                                      let Vn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          4)
                                                                                                      let Vd :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          12
                                                                                                          4)
                                                                                                      let N :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          7
                                                                                                          1)
                                                                                                      let Q :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          6
                                                                                                          1)
                                                                                                      let M :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          1)
                                                                                                      let Vm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          4)
                                                                                                      (decode_aarch32_instrs_VUSDOT_T1enc_A_txt
                                                                                                        D
                                                                                                        Vn
                                                                                                        Vd
                                                                                                        N
                                                                                                        Q
                                                                                                        M
                                                                                                        Vm))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__1024 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 23)) == (0b111111101#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 2) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   21
                                                                                                                   20)) == (0b00#2 : (BitVec 2))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   11
                                                                                                                   8)) == (0xD#4 : (BitVec 4))))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__1023 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__1023 <b 3937) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__1024 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 3937
                                                                                                          let D :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
                                                                                                          let Vn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              4)
                                                                                                          let Vd :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              12
                                                                                                              4)
                                                                                                          let N :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              7
                                                                                                              1)
                                                                                                          let Q :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              6
                                                                                                              1)
                                                                                                          let M :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              1)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              4
                                                                                                              1)
                                                                                                          let Vm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              4)
                                                                                                          (decode_aarch32_instrs_DOT_T1enc_A_txt
                                                                                                            D
                                                                                                            Vn
                                                                                                            Vd
                                                                                                            N
                                                                                                            Q
                                                                                                            M
                                                                                                            U
                                                                                                            Vm))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__1026 ← (( do
                                                                                                            if (((__opcode == 0b11110011101011111000000000010110#32) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__1025 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__1025 <b 3939) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__1026 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 3939
                                                                                                              if ((((((((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 16)])) != 1#1) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                                 __opcode
                                                                                                                                 17)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                               __opcode
                                                                                                                               18)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                             __opcode
                                                                                                                             19)])) != 1#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                           __opcode
                                                                                                                           13)])) != 0#1)) || ((BitVec.setWidth 1 (BitVec.join1 [(BitVec.access
                                                                                                                         __opcode
                                                                                                                         11)])) != 0#1)) : Bool)
                                                                                                              then
                                                                                                                sailThrow ((Error_ConstrainedUnpredictable
                                                                                                                  ()))
                                                                                                              else
                                                                                                                (do
                                                                                                                  (decode_aarch32_instrs_CLRBHB_T1enc_A_txt
                                                                                                                    ())))
                                                                                                          else
                                                                                                            sailThrow ((Error_Undefined
                                                                                                              ()))))))))))))))))))))))))))))


end ArmFull.Functions
