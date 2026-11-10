import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1024
import ArmFull.Fn.M1155
import ArmFull.Fn.M1156
import ArmFull.Fn.M1157
import ArmFull.Fn.M1188

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
def __DecodeA64_SVE__seg2 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__191 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
               __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
    then
      (do
        let w__190 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__190 <b 1132) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__191 : Bool)
  then
    (do
      writeReg SEE 1132
      let size := (BitVec.slice __opcode 22 2)
      let Zm := (BitVec.slice __opcode 16 5)
      let Zn := (BitVec.slice __opcode 5 5)
      let Zd := (BitVec.slice __opcode 0 5)
      (decode_FSUB_Z_ZZ__ size Zm Zn Zd)
      (pure false))
  else
    (do
      let w__193 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                   __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                   __opcode 15 10)) == (0b000011#6 : (BitVec 6))))) : Bool) : Bool)
        then
          (do
            let w__192 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__192 <b 1133) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__193 : Bool)
      then
        (do
          writeReg SEE 1133
          let size := (BitVec.slice __opcode 22 2)
          let Zm := (BitVec.slice __opcode 16 5)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zd := (BitVec.slice __opcode 0 5)
          (decode_FTSMUL_Z_ZZ__ size Zm Zn Zd)
          (pure false))
      else
        (do
          let w__195 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                       __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                       __opcode 15 10)) == (0b000110#6 : (BitVec 6))))) : Bool) : Bool)
            then
              (do
                let w__194 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__194 <b 1134) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__195 : Bool)
          then
            (do
              writeReg SEE 1134
              let size := (BitVec.slice __opcode 22 2)
              let Zm := (BitVec.slice __opcode 16 5)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zd := (BitVec.slice __opcode 0 5)
              (decode_FRECPS_Z_ZZ__ size Zm Zn Zd)
              (pure false))
          else
            (do
              let w__197 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                           __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                           __opcode 15 10)) == (0b000111#6 : (BitVec 6))))) : Bool) : Bool)
                then
                  (do
                    let w__196 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__196 <b 1135) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__197 : Bool)
              then
                (do
                  writeReg SEE 1135
                  let size := (BitVec.slice __opcode 22 2)
                  let Zm := (BitVec.slice __opcode 16 5)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zd := (BitVec.slice __opcode 0 5)
                  (decode_FRSQRTS_Z_ZZ__ size Zm Zn Zd)
                  (pure false))
              else
                (do
                  let w__199 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x04#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                               __opcode 15 10)) == (0b101100#6 : (BitVec 6))))) : Bool) : Bool)
                    then
                      (do
                        let w__198 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__198 <b 1136) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__199 : Bool)
                  then
                    (do
                      writeReg SEE 1136
                      let size := (BitVec.slice __opcode 22 2)
                      let Zm := (BitVec.slice __opcode 16 5)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zd := (BitVec.slice __opcode 0 5)
                      (decode_FTSSEL_Z_ZZ__ size Zm Zn Zd)
                      (pure false))
                  else
                    (do
                      let w__201 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x04#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                 __opcode 21 10)) == (0x82E#12 : (BitVec 12)))) : Bool) : Bool)
                        then
                          (do
                            let w__200 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__200 <b 1137) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__201 : Bool)
                      then
                        (do
                          writeReg SEE 1137
                          let size := (BitVec.slice __opcode 22 2)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zd := (BitVec.slice __opcode 0 5)
                          (decode_FEXPA_Z_Z__ size Zn Zd)
                          (pure false))
                      else
                        (do
                          let w__203 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                       __opcode 21 19)) == (0b010#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                       __opcode 15 10)) == (0b100000#6 : (BitVec 6))))) : Bool) : Bool)
                            then
                              (do
                                let w__202 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__202 <b 1138) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__203 : Bool)
                          then
                            (do
                              writeReg SEE 1138
                              let size := (BitVec.slice __opcode 22 2)
                              let imm3 := (BitVec.slice __opcode 16 3)
                              let Zm := (BitVec.slice __opcode 5 5)
                              let Zdn := (BitVec.slice __opcode 0 5)
                              (decode_FTMAD_Z_ZZI__ size imm3 Zm Zdn)
                              (pure false))
                          else
                            (do
                              let w__205 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x64#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 5) (Sail.BitVec.extractLsb
                                           __opcode 21 17)) == (0b00000#5 : (BitVec 5))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                           __opcode 15 13)) == (0b100#3 : (BitVec 3))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__204 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__204 <b 1139) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__205 : Bool)
                              then
                                (do
                                  writeReg SEE 1139
                                  let size := (BitVec.slice __opcode 22 2)
                                  let rot := (BitVec.slice __opcode 16 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zm := (BitVec.slice __opcode 5 5)
                                  let Zdn := (BitVec.slice __opcode 0 5)
                                  (decode_FCADD_Z_P_ZZ__ size rot Pg Zm Zdn)
                                  (pure false))
                              else
                                (do
                                  let w__207 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x64#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 21 21)) == (0#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 15 15)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__206 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__206 <b 1140) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__207 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1140
                                      let size := (BitVec.slice __opcode 22 2)
                                      let Zm := (BitVec.slice __opcode 16 5)
                                      let rot := (BitVec.slice __opcode 13 2)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zda := (BitVec.slice __opcode 0 5)
                                      (decode_FCMLA_Z_P_ZZZ__ size Zm rot Pg Zn Zda)
                                      (pure false))
                                  else
                                    (do
                                      let w__209 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                 __opcode 15 12)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__208 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__208 <b 1141) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__209 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1141
                                          let size := (BitVec.slice __opcode 22 2)
                                          let i2 := (BitVec.slice __opcode 19 2)
                                          let Zm := (BitVec.slice __opcode 16 3)
                                          let rot := (BitVec.slice __opcode 10 2)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zda := (BitVec.slice __opcode 0 5)
                                          (decode_FCMLA_Z_ZZZi_H size i2 Zm rot Zn Zda)
                                          (pure false))
                                      else
                                        (do
                                          let w__211 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                     __opcode 15 12)) == (0x1#4 : (BitVec 4)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__210 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__210 <b 1142) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__211 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1142
                                              let size := (BitVec.slice __opcode 22 2)
                                              let i1 := (BitVec.slice __opcode 20 1)
                                              let Zm := (BitVec.slice __opcode 16 4)
                                              let rot := (BitVec.slice __opcode 10 2)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zda := (BitVec.slice __opcode 0 5)
                                              (decode_FCMLA_Z_ZZZi_S size i1 Zm rot Zn Zda)
                                              (pure false))
                                          else
                                            (do
                                              let w__213 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                         __opcode 31 23)) == (0b011001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                           __opcode 15 10)) == (0b001000#6 : (BitVec 6))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__212 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__212 <b 1143) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__213 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1143
                                                  let i3h := (BitVec.slice __opcode 22 1)
                                                  let i3l := (BitVec.slice __opcode 19 2)
                                                  let Zm := (BitVec.slice __opcode 16 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zd := (BitVec.slice __opcode 0 5)
                                                  (decode_FMUL_Z_ZZi_H i3h i3l Zm Zn Zd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__215 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                             __opcode 31 23)) == (0b011001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                               __opcode 15 10)) == (0b000000#6 : (BitVec 6))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__214 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__214 <b 1144) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__215 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1144
                                                      let i3h := (BitVec.slice __opcode 22 1)
                                                      let i3l := (BitVec.slice __opcode 19 2)
                                                      let Zm := (BitVec.slice __opcode 16 3)
                                                      let op := (BitVec.slice __opcode 10 1)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zda := (BitVec.slice __opcode 0 5)
                                                      (decode_FMLA_Z_ZZZi_H i3h i3l Zm op Zn Zda)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__217 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                 __opcode 31 23)) == (0b011001000#9 : (BitVec 9))) && (((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 21 21)) == (1#1 : (BitVec 1))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                   __opcode 15 10)) == (0b000001#6 : (BitVec 6))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__216 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__216 <b 1145) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__217 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1145
                                                          let i3h := (BitVec.slice __opcode 22 1)
                                                          let i3l := (BitVec.slice __opcode 19 2)
                                                          let Zm := (BitVec.slice __opcode 16 3)
                                                          let op := (BitVec.slice __opcode 10 1)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zda := (BitVec.slice __opcode 0 5)
                                                          (decode_FMLS_Z_ZZZi_H i3h i3l Zm op Zn Zda)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__219 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                     __opcode 15 10)) == (0b001000#6 : (BitVec 6)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__218 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__218 <b 1146) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__219 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1146
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let i2 := (BitVec.slice __opcode 19 2)
                                                              let Zm := (BitVec.slice __opcode 16 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zd := (BitVec.slice __opcode 0 5)
                                                              (decode_FMUL_Z_ZZi_S size i2 Zm Zn Zd)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__221 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                         __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__220 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__220 <b 1147) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__221 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1147
                                                                  let size :=
                                                                    (BitVec.slice __opcode 22 2)
                                                                  let i2 :=
                                                                    (BitVec.slice __opcode 19 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 3)
                                                                  let op :=
                                                                    (BitVec.slice __opcode 10 1)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zda :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_FMLA_Z_ZZZi_S size i2 Zm
                                                                    op Zn Zda)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__223 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                             __opcode 15 10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__222 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__222 <b 1148) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__223 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1148
                                                                      let size :=
                                                                        (BitVec.slice __opcode 22 2)
                                                                      let i2 :=
                                                                        (BitVec.slice __opcode 19 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 3)
                                                                      let op :=
                                                                        (BitVec.slice __opcode 10 1)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zda :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_FMLS_Z_ZZZi_S size i2
                                                                        Zm op Zn Zda)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__225 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 10)) == (0b001000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__224 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__224 <b 1149) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__225 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1149
                                                                          let size :=
                                                                            (BitVec.slice __opcode
                                                                              22 2)
                                                                          let i1 :=
                                                                            (BitVec.slice __opcode
                                                                              20 1)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 4)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_FMUL_Z_ZZi_D size
                                                                            i1 Zm Zn Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__227 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 10)) == (0b000000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__226 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__226 <b 1150) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__227 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1150
                                                                              let size :=
                                                                                (BitVec.slice
                                                                                  __opcode 22 2)
                                                                              let i1 :=
                                                                                (BitVec.slice
                                                                                  __opcode 20 1)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 4)
                                                                              let op :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 1)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zda :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_FMLA_Z_ZZZi_D
                                                                                size i1 Zm op Zn Zda)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__229 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         10)) == (0b000001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__228 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__228 <b 1151) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__229 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1151
                                                                                  let size :=
                                                                                    (BitVec.slice
                                                                                      __opcode 22 2)
                                                                                  let i1 :=
                                                                                    (BitVec.slice
                                                                                      __opcode 20 1)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 4)
                                                                                  let op :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 1)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zda :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_FMLS_Z_ZZZi_D
                                                                                    size i1 Zm op Zn
                                                                                    Zda)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__231 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 24)) == (0x64#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             21 13)) == (0b010000100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__230 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__230 <b 1152) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__231 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1152
                                                                                      let size :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          22 2)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zdn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_FADDP_Z_P_ZZ__
                                                                                        size Pg Zm
                                                                                        Zdn)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__233 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 24)) == (0x64#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 21
                                                                                                 13)) == (0b010100100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__232 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__232 <b 1153) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__233 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1153
                                                                                          let size :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              22 2)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zdn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_FMAXNMP_Z_P_ZZ__
                                                                                            size Pg
                                                                                            Zm Zdn)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__235 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     24)) == (0x64#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     21
                                                                                                     13)) == (0b010110100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__234 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__234 <b 1154) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__235 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1154
                                                                                              let size :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  22
                                                                                                  2)
                                                                                              let Pg :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  3)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let Zdn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_FMAXP_Z_P_ZZ__
                                                                                                size
                                                                                                Pg
                                                                                                Zm
                                                                                                Zdn)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__237 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         24)) == (0x64#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         21
                                                                                                         13)) == (0b010101100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__236 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__236 <b 1155) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__237 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1155
                                                                                                  let size :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      22
                                                                                                      2)
                                                                                                  let Pg :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      3)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Zdn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_FMINNMP_Z_P_ZZ__
                                                                                                    size
                                                                                                    Pg
                                                                                                    Zm
                                                                                                    Zdn)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__239 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             24)) == (0x64#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             21
                                                                                                             13)) == (0b010111100#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__238 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__238 <b 1156) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__239 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1156
                                                                                                      let size :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          22
                                                                                                          2)
                                                                                                      let Pg :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          3)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Zdn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_FMINP_Z_P_ZZ__
                                                                                                        size
                                                                                                        Pg
                                                                                                        Zm
                                                                                                        Zdn)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__241 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 10)) == (0b100000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__240 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__240 <b 1157) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__241 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1157
                                                                                                          let o2 :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              22
                                                                                                              1)
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
                                                                                                          let T :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              1)
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
                                                                                                          (decode_FMLALB_Z_ZZZ__
                                                                                                            o2
                                                                                                            Zm
                                                                                                            op
                                                                                                            T
                                                                                                            Zn
                                                                                                            Zda)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__243 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     10)) == (0b100001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__242 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__242 <b 1158) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__243 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1158
                                                                                                              let o2 :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  22
                                                                                                                  1)
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
                                                                                                              let T :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  1)
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
                                                                                                              (decode_FMLALT_Z_ZZZ__
                                                                                                                o2
                                                                                                                Zm
                                                                                                                op
                                                                                                                T
                                                                                                                Zn
                                                                                                                Zda)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__245 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         10)) == (0b101000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__244 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__244 <b 1159) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__245 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1159
                                                                                                                  let o2 :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      22
                                                                                                                      1)
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
                                                                                                                  let T :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      1)
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
                                                                                                                  (decode_FMLSLB_Z_ZZZ__
                                                                                                                    o2
                                                                                                                    Zm
                                                                                                                    op
                                                                                                                    T
                                                                                                                    Zn
                                                                                                                    Zda)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__247 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b01100100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             10)) == (0b101001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__246 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__246 <b 1160) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__247 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1160
                                                                                                                      let o2 :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          22
                                                                                                                          1)
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
                                                                                                                      let T :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          1)
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
                                                                                                                      (decode_FMLSLT_Z_ZZZ__
                                                                                                                        o2
                                                                                                                        Zm
                                                                                                                        op
                                                                                                                        T
                                                                                                                        Zn
                                                                                                                        Zda)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__249 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b01100100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   12)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   10
                                                                                                                                   10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__248 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__248 <b 1161) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__249 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1161
                                                                                                                          let o2 :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              22
                                                                                                                              1)
                                                                                                                          let i3h :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              19
                                                                                                                              2)
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              3)
                                                                                                                          let op :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              1)
                                                                                                                          let i3l :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              11
                                                                                                                              1)
                                                                                                                          let T :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              1)
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
                                                                                                                          (decode_FMLALB_Z_ZZZi_S
                                                                                                                            o2
                                                                                                                            i3h
                                                                                                                            Zm
                                                                                                                            op
                                                                                                                            i3l
                                                                                                                            T
                                                                                                                            Zn
                                                                                                                            Zda)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__251 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b01100100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       12)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       10
                                                                                                                                       10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__250 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__250 <b 1162) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__251 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1162
                                                                                                                              let o2 :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  22
                                                                                                                                  1)
                                                                                                                              let i3h :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  19
                                                                                                                                  2)
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  3)
                                                                                                                              let op :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  1)
                                                                                                                              let i3l :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  11
                                                                                                                                  1)
                                                                                                                              let T :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  1)
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
                                                                                                                              (decode_FMLALT_Z_ZZZi_S
                                                                                                                                o2
                                                                                                                                i3h
                                                                                                                                Zm
                                                                                                                                op
                                                                                                                                i3l
                                                                                                                                T
                                                                                                                                Zn
                                                                                                                                Zda)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__253 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b01100100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           12)) == (0x6#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           10
                                                                                                                                           10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__252 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__252 <b 1163) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__253 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1163
                                                                                                                                  let o2 :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      22
                                                                                                                                      1)
                                                                                                                                  let i3h :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      19
                                                                                                                                      2)
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      3)
                                                                                                                                  let op :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      1)
                                                                                                                                  let i3l :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      11
                                                                                                                                      1)
                                                                                                                                  let T :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      1)
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
                                                                                                                                  (decode_FMLSLB_Z_ZZZi_S
                                                                                                                                    o2
                                                                                                                                    i3h
                                                                                                                                    Zm
                                                                                                                                    op
                                                                                                                                    i3l
                                                                                                                                    T
                                                                                                                                    Zn
                                                                                                                                    Zda)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__255 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b01100100101#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               12)) == (0x6#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               10
                                                                                                                                               10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__254 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__254 <b 1164) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__255 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1164
                                                                                                                                      let o2 :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          22
                                                                                                                                          1)
                                                                                                                                      let i3h :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          19
                                                                                                                                          2)
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          3)
                                                                                                                                      let op :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          1)
                                                                                                                                      let i3l :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          11
                                                                                                                                          1)
                                                                                                                                      let T :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          1)
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
                                                                                                                                      (decode_FMLSLT_Z_ZZZi_S
                                                                                                                                        o2
                                                                                                                                        i3h
                                                                                                                                        Zm
                                                                                                                                        op
                                                                                                                                        i3l
                                                                                                                                        T
                                                                                                                                        Zn
                                                                                                                                        Zda)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__257 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 10)) == (0b100000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__256 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__256 <b 1165) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__257 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1165
                                                                                                                                          let o2 :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              22
                                                                                                                                              1)
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
                                                                                                                                          let T :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              1)
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
                                                                                                                                          (decode_BFMLALB_Z_ZZZ__
                                                                                                                                            o2
                                                                                                                                            Zm
                                                                                                                                            op
                                                                                                                                            T
                                                                                                                                            Zn
                                                                                                                                            Zda)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__259 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     10)) == (0b100001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__258 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__258 <b 1166) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__259 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1166
                                                                                                                                              let o2 :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  22
                                                                                                                                                  1)
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
                                                                                                                                              let T :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  1)
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
                                                                                                                                              (decode_BFMLALT_Z_ZZZ__
                                                                                                                                                o2
                                                                                                                                                Zm
                                                                                                                                                op
                                                                                                                                                T
                                                                                                                                                Zn
                                                                                                                                                Zda)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__261 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         10)) == (0b101000#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__260 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__260 <b 1167) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__261 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1167
                                                                                                                                                  let o2 :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      22
                                                                                                                                                      1)
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
                                                                                                                                                  let T :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      1)
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
                                                                                                                                                  (decode_BFMLSLB_Z_ZZZ__
                                                                                                                                                    o2
                                                                                                                                                    Zm
                                                                                                                                                    op
                                                                                                                                                    T
                                                                                                                                                    Zn
                                                                                                                                                    Zda)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__263 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b01100100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 6) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             10)) == (0b101001#6 : (BitVec 6)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__262 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__262 <b 1168) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__263 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1168
                                                                                                                                                      let o2 :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          22
                                                                                                                                                          1)
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
                                                                                                                                                      let T :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          1)
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
                                                                                                                                                      (decode_BFMLSLT_Z_ZZZ__
                                                                                                                                                        o2
                                                                                                                                                        Zm
                                                                                                                                                        op
                                                                                                                                                        T
                                                                                                                                                        Zn
                                                                                                                                                        Zda)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__265 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 21)) == (0b01100100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   15
                                                                                                                                                                   12)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   10
                                                                                                                                                                   10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__264 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__264 <b 1169) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__265 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1169
                                                                                                                                                          let o2 :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              22
                                                                                                                                                              1)
                                                                                                                                                          let i3h :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              19
                                                                                                                                                              2)
                                                                                                                                                          let Zm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              3)
                                                                                                                                                          let op :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              1)
                                                                                                                                                          let i3l :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              11
                                                                                                                                                              1)
                                                                                                                                                          let T :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              1)
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
                                                                                                                                                          (decode_BFMLALB_Z_ZZZi__
                                                                                                                                                            o2
                                                                                                                                                            i3h
                                                                                                                                                            Zm
                                                                                                                                                            op
                                                                                                                                                            i3l
                                                                                                                                                            T
                                                                                                                                                            Zn
                                                                                                                                                            Zda)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__267 ← (( do
                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                     __opcode
                                                                                                                                                                     31
                                                                                                                                                                     21)) == (0b01100100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       15
                                                                                                                                                                       12)) == (0x4#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       10
                                                                                                                                                                       10)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__266 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__266 <b 1170) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__267 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1170
                                                                                                                                                              let o2 :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  22
                                                                                                                                                                  1)
                                                                                                                                                              let i3h :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  19
                                                                                                                                                                  2)
                                                                                                                                                              let Zm :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  16
                                                                                                                                                                  3)
                                                                                                                                                              let op :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  13
                                                                                                                                                                  1)
                                                                                                                                                              let i3l :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  11
                                                                                                                                                                  1)
                                                                                                                                                              let T :=
                                                                                                                                                                (BitVec.slice
                                                                                                                                                                  __opcode
                                                                                                                                                                  10
                                                                                                                                                                  1)
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
                                                                                                                                                              (decode_BFMLALT_Z_ZZZi__
                                                                                                                                                                o2
                                                                                                                                                                i3h
                                                                                                                                                                Zm
                                                                                                                                                                op
                                                                                                                                                                i3l
                                                                                                                                                                T
                                                                                                                                                                Zn
                                                                                                                                                                Zda)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__269 ← (( do
                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                         __opcode
                                                                                                                                                                         31
                                                                                                                                                                         21)) == (0b01100100111#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           15
                                                                                                                                                                           12)) == (0x6#4 : (BitVec 4))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           10
                                                                                                                                                                           10)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__268 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__268 <b 1171) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__269 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1171
                                                                                                                                                                  let o2 :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      22
                                                                                                                                                                      1)
                                                                                                                                                                  let i3h :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      19
                                                                                                                                                                      2)
                                                                                                                                                                  let Zm :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      16
                                                                                                                                                                      3)
                                                                                                                                                                  let op :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      13
                                                                                                                                                                      1)
                                                                                                                                                                  let i3l :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      11
                                                                                                                                                                      1)
                                                                                                                                                                  let T :=
                                                                                                                                                                    (BitVec.slice
                                                                                                                                                                      __opcode
                                                                                                                                                                      10
                                                                                                                                                                      1)
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
                                                                                                                                                                  (decode_BFMLSLB_Z_ZZZi__
                                                                                                                                                                    o2
                                                                                                                                                                    i3h
                                                                                                                                                                    Zm
                                                                                                                                                                    op
                                                                                                                                                                    i3l
                                                                                                                                                                    T
                                                                                                                                                                    Zn
                                                                                                                                                                    Zda)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (pure true))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
