import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1111
import ArmFull.Fn.M1112
import ArmFull.Fn.M1113
import ArmFull.Fn.M1114
import ArmFull.Fn.M1152
import ArmFull.Fn.M1153

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
def __DecodeA64_SVE__seg0 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__1 ← (( do
    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
               __opcode 21 13)) == (0b011000100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
               __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
    then
      (do
        let w__0 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__0 <b 1037) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1 : Bool)
  then
    (do
      writeReg SEE 1037
      let size := (BitVec.slice __opcode 22 2)
      let Pg := (BitVec.slice __opcode 10 3)
      let i1 := (BitVec.slice __opcode 5 1)
      let Zdn := (BitVec.slice __opcode 0 5)
      (decode_FADD_Z_P_ZS__ size Pg i1 Zdn)
      (pure false))
  else
    (do
      let w__3 ← (( do
        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                   __opcode 21 13)) == (0b011001100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                   __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
        then
          (do
            let w__2 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2 <b 1038) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__3 : Bool)
      then
        (do
          writeReg SEE 1038
          let size := (BitVec.slice __opcode 22 2)
          let Pg := (BitVec.slice __opcode 10 3)
          let i1 := (BitVec.slice __opcode 5 1)
          let Zdn := (BitVec.slice __opcode 0 5)
          (decode_FSUB_Z_P_ZS__ size Pg i1 Zdn)
          (pure false))
      else
        (do
          let w__5 ← (( do
            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                       __opcode 21 13)) == (0b011010100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                       __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
            then
              (do
                let w__4 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__4 <b 1039) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__5 : Bool)
          then
            (do
              writeReg SEE 1039
              let size := (BitVec.slice __opcode 22 2)
              let Pg := (BitVec.slice __opcode 10 3)
              let i1 := (BitVec.slice __opcode 5 1)
              let Zdn := (BitVec.slice __opcode 0 5)
              (decode_FMUL_Z_P_ZS__ size Pg i1 Zdn)
              (pure false))
          else
            (do
              let w__7 ← (( do
                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                           __opcode 21 13)) == (0b011011100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                           __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                then
                  (do
                    let w__6 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__6 <b 1040) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__7 : Bool)
              then
                (do
                  writeReg SEE 1040
                  let size := (BitVec.slice __opcode 22 2)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let i1 := (BitVec.slice __opcode 5 1)
                  let Zdn := (BitVec.slice __opcode 0 5)
                  (decode_FSUBR_Z_P_ZS__ size Pg i1 Zdn)
                  (pure false))
              else
                (do
                  let w__9 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                               __opcode 21 13)) == (0b011100100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                               __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                    then
                      (do
                        let w__8 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__8 <b 1041) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__9 : Bool)
                  then
                    (do
                      writeReg SEE 1041
                      let size := (BitVec.slice __opcode 22 2)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let i1 := (BitVec.slice __opcode 5 1)
                      let Zdn := (BitVec.slice __opcode 0 5)
                      (decode_FMAXNM_Z_P_ZS__ size Pg i1 Zdn)
                      (pure false))
                  else
                    (do
                      let w__11 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode 31
                                 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                   __opcode 21 13)) == (0b011101100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                   __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                        then
                          (do
                            let w__10 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__10 <b 1042) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__11 : Bool)
                      then
                        (do
                          writeReg SEE 1042
                          let size := (BitVec.slice __opcode 22 2)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let i1 := (BitVec.slice __opcode 5 1)
                          let Zdn := (BitVec.slice __opcode 0 5)
                          (decode_FMINNM_Z_P_ZS__ size Pg i1 Zdn)
                          (pure false))
                      else
                        (do
                          let w__13 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb __opcode
                                     31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                       __opcode 21 13)) == (0b011110100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                       __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                            then
                              (do
                                let w__12 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__12 <b 1043) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__13 : Bool)
                          then
                            (do
                              writeReg SEE 1043
                              let size := (BitVec.slice __opcode 22 2)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let i1 := (BitVec.slice __opcode 5 1)
                              let Zdn := (BitVec.slice __opcode 0 5)
                              (decode_FMAX_Z_P_ZS__ size Pg i1 Zdn)
                              (pure false))
                          else
                            (do
                              let w__15 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                         __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                           __opcode 21 13)) == (0b011111100#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 4) (Sail.BitVec.extractLsb
                                           __opcode 9 6)) == (0x0#4 : (BitVec 4))))) : Bool) : Bool)
                                then
                                  (do
                                    let w__14 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__14 <b 1044) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__15 : Bool)
                              then
                                (do
                                  writeReg SEE 1044
                                  let size := (BitVec.slice __opcode 22 2)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let i1 := (BitVec.slice __opcode 5 1)
                                  let Zdn := (BitVec.slice __opcode 0 5)
                                  (decode_FMIN_Z_P_ZS__ size Pg i1 Zdn)
                                  (pure false))
                              else
                                (do
                                  let w__17 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                             __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                               __opcode 21 13)) == (0b010000001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                               __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__16 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__16 <b 1045) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__17 : Bool)
                                  then
                                    (do
                                      writeReg SEE 1045
                                      let size := (BitVec.slice __opcode 22 2)
                                      let eq := (BitVec.slice __opcode 17 1)
                                      let lt := (BitVec.slice __opcode 16 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let ne := (BitVec.slice __opcode 4 1)
                                      let Pd := (BitVec.slice __opcode 0 4)
                                      (decode_FCMGE_P_P_Z0__ size eq lt Pg Zn ne Pd)
                                      (pure false))
                                  else
                                    (do
                                      let w__19 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                 __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                   __opcode 21 13)) == (0b010000001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                   __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__18 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__18 <b 1046) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__19 : Bool)
                                      then
                                        (do
                                          writeReg SEE 1046
                                          let size := (BitVec.slice __opcode 22 2)
                                          let eq := (BitVec.slice __opcode 17 1)
                                          let lt := (BitVec.slice __opcode 16 1)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let ne := (BitVec.slice __opcode 4 1)
                                          let Pd := (BitVec.slice __opcode 0 4)
                                          (decode_FCMGT_P_P_Z0__ size eq lt Pg Zn ne Pd)
                                          (pure false))
                                      else
                                        (do
                                          let w__21 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                     __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                       __opcode 21 13)) == (0b010001001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                       __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__20 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__20 <b 1047) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__21 : Bool)
                                          then
                                            (do
                                              writeReg SEE 1047
                                              let size := (BitVec.slice __opcode 22 2)
                                              let eq := (BitVec.slice __opcode 17 1)
                                              let lt := (BitVec.slice __opcode 16 1)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let ne := (BitVec.slice __opcode 4 1)
                                              let Pd := (BitVec.slice __opcode 0 4)
                                              (decode_FCMLT_P_P_Z0__ size eq lt Pg Zn ne Pd)
                                              (pure false))
                                          else
                                            (do
                                              let w__23 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                         __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                           __opcode 21 13)) == (0b010001001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                           __opcode 4 4)) == (1#1 : (BitVec 1))))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__22 ← (( do readReg SEE ) : SailM Int )
                                                    (pure (((w__22 <b 1048) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__23 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 1048
                                                  let size := (BitVec.slice __opcode 22 2)
                                                  let eq := (BitVec.slice __opcode 17 1)
                                                  let lt := (BitVec.slice __opcode 16 1)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let ne := (BitVec.slice __opcode 4 1)
                                                  let Pd := (BitVec.slice __opcode 0 4)
                                                  (decode_FCMLE_P_P_Z0__ size eq lt Pg Zn ne Pd)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__25 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                             __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                               __opcode 21 13)) == (0b010010001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                               __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__24 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__24 <b 1049) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__25 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 1049
                                                      let size := (BitVec.slice __opcode 22 2)
                                                      let eq := (BitVec.slice __opcode 17 1)
                                                      let lt := (BitVec.slice __opcode 16 1)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let ne := (BitVec.slice __opcode 4 1)
                                                      let Pd := (BitVec.slice __opcode 0 4)
                                                      (decode_FCMEQ_P_P_Z0__ size eq lt Pg Zn ne Pd)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__27 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                 __opcode 31 24)) == (0x65#8 : (BitVec 8))) && (((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                   __opcode 21 13)) == (0b010011001#9 : (BitVec 9))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                   __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__26 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__26 <b 1050) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__27 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 1050
                                                          let size := (BitVec.slice __opcode 22 2)
                                                          let eq := (BitVec.slice __opcode 17 1)
                                                          let lt := (BitVec.slice __opcode 16 1)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let ne := (BitVec.slice __opcode 4 1)
                                                          let Pd := (BitVec.slice __opcode 0 4)
                                                          (decode_FCMNE_P_P_Z0__ size eq lt Pg Zn ne
                                                            Pd)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__29 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                     __opcode 31 24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                     __opcode 21 13)) == (0b011000001#9 : (BitVec 9)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__28 ← (( do readReg SEE ) :
                                                                  SailM Int )
                                                                (pure (((w__28 <b 1051) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__29 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 1051
                                                              let size :=
                                                                (BitVec.slice __opcode 22 2)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zm := (BitVec.slice __opcode 5 5)
                                                              let Vdn := (BitVec.slice __opcode 0 5)
                                                              (decode_FADDA_V_P_Z__ size Pg Zm Vdn)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__31 ← (( do
                                                                if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                       __opcode 31 13)) == (0b0110010111011111101#19 : (BitVec 19))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__30 ← (( do readReg SEE
                                                                      ) : SailM Int )
                                                                    (pure (((w__30 <b 1052) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__31 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 1052
                                                                  let int_U :=
                                                                    (BitVec.slice __opcode 16 1)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Zn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zd :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_FCVTZU_Z_P_Z_D2X int_U Pg
                                                                    Zn Zd)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__33 ← (( do
                                                                    if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                           __opcode 31 13)) == (0b0110010111011001101#19 : (BitVec 19))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__32 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__32 <b 1053) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__33 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 1053
                                                                      let int_U :=
                                                                        (BitVec.slice __opcode 16 1)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Zn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zd :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_FCVTZU_Z_P_Z_D2W int_U
                                                                        Pg Zn Zd)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__35 ← (( do
                                                                        if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                               __opcode 31 13)) == (0b0110010110011101101#19 : (BitVec 19))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__34 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__34 <b 1054) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__35 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 1054
                                                                          let int_U :=
                                                                            (BitVec.slice __opcode
                                                                              16 1)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Zn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zd :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_FCVTZU_Z_P_Z_S2W
                                                                            int_U Pg Zn Zd)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__37 ← (( do
                                                                            if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                   __opcode 31 13)) == (0b0110010111011101101#19 : (BitVec 19))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__36 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__36 <b 1055) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__37 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 1055
                                                                              let int_U :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 1)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Zn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zd :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_FCVTZU_Z_P_Z_S2X
                                                                                int_U Pg Zn Zd)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__39 ← (( do
                                                                                if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                       __opcode 31
                                                                                       13)) == (0b0110010111011110101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__38 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__38 <b 1056) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__39 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 1056
                                                                                  let int_U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 1)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Zn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zd :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_FCVTZS_Z_P_Z_D2X
                                                                                    int_U Pg Zn Zd)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__41 ← (( do
                                                                                    if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                           __opcode
                                                                                           31 13)) == (0b0110010111011000101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__40 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__40 <b 1057) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__41 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 1057
                                                                                      let int_U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 1)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Zn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zd :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_FCVTZS_Z_P_Z_D2W
                                                                                        int_U Pg Zn
                                                                                        Zd)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__43 ← (( do
                                                                                        if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                               __opcode
                                                                                               31 13)) == (0b0110010110011100101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__42 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__42 <b 1058) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__43 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 1058
                                                                                          let int_U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 1)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Zn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zd :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_FCVTZS_Z_P_Z_S2W
                                                                                            int_U Pg
                                                                                            Zn Zd)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__45 ← (( do
                                                                                            if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                   __opcode
                                                                                                   31
                                                                                                   13)) == (0b0110010111011100101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__44 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__44 <b 1059) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__45 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 1059
                                                                                              let int_U :=
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
                                                                                              (decode_FCVTZS_Z_P_Z_S2X
                                                                                                int_U
                                                                                                Pg
                                                                                                Zn
                                                                                                Zd)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__47 ← (( do
                                                                                                if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                       __opcode
                                                                                                       31
                                                                                                       13)) == (0b0110010101011010101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__46 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__46 <b 1060) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__47 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 1060
                                                                                                  let int_U :=
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
                                                                                                  (decode_FCVTZS_Z_P_Z_FP162H
                                                                                                    int_U
                                                                                                    Pg
                                                                                                    Zn
                                                                                                    Zd)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__49 ← (( do
                                                                                                    if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                           __opcode
                                                                                                           31
                                                                                                           13)) == (0b0110010101011100101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__48 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__48 <b 1061) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__49 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 1061
                                                                                                      let int_U :=
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
                                                                                                      (decode_FCVTZS_Z_P_Z_FP162W
                                                                                                        int_U
                                                                                                        Pg
                                                                                                        Zn
                                                                                                        Zd)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__51 ← (( do
                                                                                                        if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                               __opcode
                                                                                                               31
                                                                                                               13)) == (0b0110010101011110101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__50 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__50 <b 1062) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__51 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 1062
                                                                                                          let int_U :=
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
                                                                                                          (decode_FCVTZS_Z_P_Z_FP162X
                                                                                                            int_U
                                                                                                            Pg
                                                                                                            Zn
                                                                                                            Zd)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__53 ← (( do
                                                                                                            if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                   __opcode
                                                                                                                   31
                                                                                                                   13)) == (0b0110010101011011101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__52 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__52 <b 1063) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__53 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 1063
                                                                                                              let int_U :=
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
                                                                                                              (decode_FCVTZU_Z_P_Z_FP162H
                                                                                                                int_U
                                                                                                                Pg
                                                                                                                Zn
                                                                                                                Zd)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__55 ← (( do
                                                                                                                if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                       __opcode
                                                                                                                       31
                                                                                                                       13)) == (0b0110010101011101101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__54 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__54 <b 1064) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__55 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 1064
                                                                                                                  let int_U :=
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
                                                                                                                  (decode_FCVTZU_Z_P_Z_FP162W
                                                                                                                    int_U
                                                                                                                    Pg
                                                                                                                    Zn
                                                                                                                    Zd)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__57 ← (( do
                                                                                                                    if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                           __opcode
                                                                                                                           31
                                                                                                                           13)) == (0b0110010101011111101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__56 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__56 <b 1065) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__57 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 1065
                                                                                                                      let int_U :=
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
                                                                                                                      (decode_FCVTZU_Z_P_Z_FP162X
                                                                                                                        int_U
                                                                                                                        Pg
                                                                                                                        Zn
                                                                                                                        Zd)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__59 ← (( do
                                                                                                                        if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                               __opcode
                                                                                                                               31
                                                                                                                               13)) == (0b0110010101010010101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__58 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__58 <b 1066) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__59 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 1066
                                                                                                                          let int_U :=
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
                                                                                                                          (decode_SCVTF_Z_P_Z_H2FP16
                                                                                                                            int_U
                                                                                                                            Pg
                                                                                                                            Zn
                                                                                                                            Zd)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__61 ← (( do
                                                                                                                            if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   31
                                                                                                                                   13)) == (0b0110010101010100101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__60 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__60 <b 1067) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__61 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 1067
                                                                                                                              let int_U :=
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
                                                                                                                              (decode_SCVTF_Z_P_Z_W2FP16
                                                                                                                                int_U
                                                                                                                                Pg
                                                                                                                                Zn
                                                                                                                                Zd)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__63 ← (( do
                                                                                                                                if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       31
                                                                                                                                       13)) == (0b0110010101010110101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__62 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__62 <b 1068) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__63 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 1068
                                                                                                                                  let int_U :=
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
                                                                                                                                  (decode_SCVTF_Z_P_Z_X2FP16
                                                                                                                                    int_U
                                                                                                                                    Pg
                                                                                                                                    Zn
                                                                                                                                    Zd)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__65 ← (( do
                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           31
                                                                                                                                           13)) == (0b0110010101010011101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__64 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__64 <b 1069) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__65 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 1069
                                                                                                                                      let int_U :=
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
                                                                                                                                      (decode_UCVTF_Z_P_Z_H2FP16
                                                                                                                                        int_U
                                                                                                                                        Pg
                                                                                                                                        Zn
                                                                                                                                        Zd)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__67 ← (( do
                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               31
                                                                                                                                               13)) == (0b0110010101010101101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__66 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__66 <b 1070) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__67 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 1070
                                                                                                                                          let int_U :=
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
                                                                                                                                          (decode_UCVTF_Z_P_Z_W2FP16
                                                                                                                                            int_U
                                                                                                                                            Pg
                                                                                                                                            Zn
                                                                                                                                            Zd)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__69 ← (( do
                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                                   __opcode
                                                                                                                                                   31
                                                                                                                                                   13)) == (0b0110010101010111101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__68 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__68 <b 1071) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__69 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 1071
                                                                                                                                              let int_U :=
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
                                                                                                                                              (decode_UCVTF_Z_P_Z_X2FP16
                                                                                                                                                int_U
                                                                                                                                                Pg
                                                                                                                                                Zn
                                                                                                                                                Zd)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__71 ← (( do
                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                                       __opcode
                                                                                                                                                       31
                                                                                                                                                       13)) == (0b0110010111001010101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__70 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__70 <b 1072) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__71 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 1072
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
                                                                                                                                                  (decode_FCVT_Z_P_Z_D2S
                                                                                                                                                    Pg
                                                                                                                                                    Zn
                                                                                                                                                    Zd)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__73 ← (( do
                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                                           __opcode
                                                                                                                                                           31
                                                                                                                                                           13)) == (0b0110010111001000101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__72 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__72 <b 1073) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__73 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 1073
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
                                                                                                                                                      (decode_FCVT_Z_P_Z_D2H
                                                                                                                                                        Pg
                                                                                                                                                        Zn
                                                                                                                                                        Zd)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__75 ← (( do
                                                                                                                                                        if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                                               __opcode
                                                                                                                                                               31
                                                                                                                                                               13)) == (0b0110010111001011101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__74 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__74 <b 1074) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__75 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 1074
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
                                                                                                                                                          (decode_FCVT_Z_P_Z_S2D
                                                                                                                                                            Pg
                                                                                                                                                            Zn
                                                                                                                                                            Zd)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (do
                                                                                                                                                          let w__77 ← (( do
                                                                                                                                                            if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                                                   __opcode
                                                                                                                                                                   31
                                                                                                                                                                   13)) == (0b0110010111001001101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                                            then
                                                                                                                                                              (do
                                                                                                                                                                let w__76 ← (( do
                                                                                                                                                                  readReg SEE
                                                                                                                                                                  )
                                                                                                                                                                  :
                                                                                                                                                                  SailM
                                                                                                                                                                  Int
                                                                                                                                                                  )
                                                                                                                                                                (pure (((w__76 <b 1075) : Bool))))
                                                                                                                                                            else
                                                                                                                                                              (pure false)
                                                                                                                                                            )
                                                                                                                                                            :
                                                                                                                                                            SailM
                                                                                                                                                            Bool
                                                                                                                                                            )
                                                                                                                                                          if (w__77 : Bool)
                                                                                                                                                          then
                                                                                                                                                            (do
                                                                                                                                                              writeReg SEE 1075
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
                                                                                                                                                              (decode_FCVT_Z_P_Z_H2D
                                                                                                                                                                Pg
                                                                                                                                                                Zn
                                                                                                                                                                Zd)
                                                                                                                                                              (pure false))
                                                                                                                                                          else
                                                                                                                                                            (do
                                                                                                                                                              let w__79 ← (( do
                                                                                                                                                                if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                                                       __opcode
                                                                                                                                                                       31
                                                                                                                                                                       13)) == (0b0110010110001001101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                                                then
                                                                                                                                                                  (do
                                                                                                                                                                    let w__78 ← (( do
                                                                                                                                                                      readReg SEE
                                                                                                                                                                      )
                                                                                                                                                                      :
                                                                                                                                                                      SailM
                                                                                                                                                                      Int
                                                                                                                                                                      )
                                                                                                                                                                    (pure (((w__78 <b 1076) : Bool))))
                                                                                                                                                                else
                                                                                                                                                                  (pure false)
                                                                                                                                                                )
                                                                                                                                                                :
                                                                                                                                                                SailM
                                                                                                                                                                Bool
                                                                                                                                                                )
                                                                                                                                                              if (w__79 : Bool)
                                                                                                                                                              then
                                                                                                                                                                (do
                                                                                                                                                                  writeReg SEE 1076
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
                                                                                                                                                                  (decode_FCVT_Z_P_Z_H2S
                                                                                                                                                                    Pg
                                                                                                                                                                    Zn
                                                                                                                                                                    Zd)
                                                                                                                                                                  (pure false))
                                                                                                                                                              else
                                                                                                                                                                (do
                                                                                                                                                                  let w__81 ← (( do
                                                                                                                                                                    if ((((Sail.BitVec.castWidth (m := 19) (Sail.BitVec.extractLsb
                                                                                                                                                                           __opcode
                                                                                                                                                                           31
                                                                                                                                                                           13)) == (0b0110010110001000101#19 : (BitVec 19))) : Bool) : Bool)
                                                                                                                                                                    then
                                                                                                                                                                      (do
                                                                                                                                                                        let w__80 ← (( do
                                                                                                                                                                          readReg SEE
                                                                                                                                                                          )
                                                                                                                                                                          :
                                                                                                                                                                          SailM
                                                                                                                                                                          Int
                                                                                                                                                                          )
                                                                                                                                                                        (pure (((w__80 <b 1077) : Bool))))
                                                                                                                                                                    else
                                                                                                                                                                      (pure false)
                                                                                                                                                                    )
                                                                                                                                                                    :
                                                                                                                                                                    SailM
                                                                                                                                                                    Bool
                                                                                                                                                                    )
                                                                                                                                                                  if (w__81 : Bool)
                                                                                                                                                                  then
                                                                                                                                                                    (do
                                                                                                                                                                      writeReg SEE 1077
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
                                                                                                                                                                      (decode_FCVT_Z_P_Z_S2H
                                                                                                                                                                        Pg
                                                                                                                                                                        Zn
                                                                                                                                                                        Zd)
                                                                                                                                                                      (pure false))
                                                                                                                                                                  else
                                                                                                                                                                    (do
                                                                                                                                                                      let w__83 ← (( do
                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 31
                                                                                                                                                                                 24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                 __opcode
                                                                                                                                                                                 21
                                                                                                                                                                                 10)) == (0x38C#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                        then
                                                                                                                                                                          (do
                                                                                                                                                                            let w__82 ← (( do
                                                                                                                                                                              readReg SEE
                                                                                                                                                                              )
                                                                                                                                                                              :
                                                                                                                                                                              SailM
                                                                                                                                                                              Int
                                                                                                                                                                              )
                                                                                                                                                                            (pure (((w__82 <b 1078) : Bool))))
                                                                                                                                                                        else
                                                                                                                                                                          (pure false)
                                                                                                                                                                        )
                                                                                                                                                                        :
                                                                                                                                                                        SailM
                                                                                                                                                                        Bool
                                                                                                                                                                        )
                                                                                                                                                                      if (w__83 : Bool)
                                                                                                                                                                      then
                                                                                                                                                                        (do
                                                                                                                                                                          writeReg SEE 1078
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
                                                                                                                                                                          (decode_FRECPE_Z_Z__
                                                                                                                                                                            size
                                                                                                                                                                            Zn
                                                                                                                                                                            Zd)
                                                                                                                                                                          (pure false))
                                                                                                                                                                      else
                                                                                                                                                                        (do
                                                                                                                                                                          let w__85 ← (( do
                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     31
                                                                                                                                                                                     24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 12) (Sail.BitVec.extractLsb
                                                                                                                                                                                     __opcode
                                                                                                                                                                                     21
                                                                                                                                                                                     10)) == (0x3CC#12 : (BitVec 12)))) : Bool) : Bool)
                                                                                                                                                                            then
                                                                                                                                                                              (do
                                                                                                                                                                                let w__84 ← (( do
                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                  )
                                                                                                                                                                                  :
                                                                                                                                                                                  SailM
                                                                                                                                                                                  Int
                                                                                                                                                                                  )
                                                                                                                                                                                (pure (((w__84 <b 1079) : Bool))))
                                                                                                                                                                            else
                                                                                                                                                                              (pure false)
                                                                                                                                                                            )
                                                                                                                                                                            :
                                                                                                                                                                            SailM
                                                                                                                                                                            Bool
                                                                                                                                                                            )
                                                                                                                                                                          if (w__85 : Bool)
                                                                                                                                                                          then
                                                                                                                                                                            (do
                                                                                                                                                                              writeReg SEE 1079
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
                                                                                                                                                                              (decode_FRSQRTE_Z_Z__
                                                                                                                                                                                size
                                                                                                                                                                                Zn
                                                                                                                                                                                Zd)
                                                                                                                                                                              (pure false))
                                                                                                                                                                          else
                                                                                                                                                                            (do
                                                                                                                                                                              let w__87 ← (( do
                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         31
                                                                                                                                                                                         24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                         __opcode
                                                                                                                                                                                         21
                                                                                                                                                                                         13)) == (0b001100101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                then
                                                                                                                                                                                  (do
                                                                                                                                                                                    let w__86 ← (( do
                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                      )
                                                                                                                                                                                      :
                                                                                                                                                                                      SailM
                                                                                                                                                                                      Int
                                                                                                                                                                                      )
                                                                                                                                                                                    (pure (((w__86 <b 1080) : Bool))))
                                                                                                                                                                                else
                                                                                                                                                                                  (pure false)
                                                                                                                                                                                )
                                                                                                                                                                                :
                                                                                                                                                                                SailM
                                                                                                                                                                                Bool
                                                                                                                                                                                )
                                                                                                                                                                              if (w__87 : Bool)
                                                                                                                                                                              then
                                                                                                                                                                                (do
                                                                                                                                                                                  writeReg SEE 1080
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
                                                                                                                                                                                  (decode_FRECPX_Z_P_Z__
                                                                                                                                                                                    size
                                                                                                                                                                                    Pg
                                                                                                                                                                                    Zn
                                                                                                                                                                                    Zd)
                                                                                                                                                                                  (pure false))
                                                                                                                                                                              else
                                                                                                                                                                                (do
                                                                                                                                                                                  let w__89 ← (( do
                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             31
                                                                                                                                                                                             24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                             __opcode
                                                                                                                                                                                             21
                                                                                                                                                                                             13)) == (0b001101101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                    then
                                                                                                                                                                                      (do
                                                                                                                                                                                        let w__88 ← (( do
                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                          )
                                                                                                                                                                                          :
                                                                                                                                                                                          SailM
                                                                                                                                                                                          Int
                                                                                                                                                                                          )
                                                                                                                                                                                        (pure (((w__88 <b 1081) : Bool))))
                                                                                                                                                                                    else
                                                                                                                                                                                      (pure false)
                                                                                                                                                                                    )
                                                                                                                                                                                    :
                                                                                                                                                                                    SailM
                                                                                                                                                                                    Bool
                                                                                                                                                                                    )
                                                                                                                                                                                  if (w__89 : Bool)
                                                                                                                                                                                  then
                                                                                                                                                                                    (do
                                                                                                                                                                                      writeReg SEE 1081
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
                                                                                                                                                                                      (decode_FSQRT_Z_P_Z__
                                                                                                                                                                                        size
                                                                                                                                                                                        Pg
                                                                                                                                                                                        Zn
                                                                                                                                                                                        Zd)
                                                                                                                                                                                      (pure false))
                                                                                                                                                                                  else
                                                                                                                                                                                    (do
                                                                                                                                                                                      let w__91 ← (( do
                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 31
                                                                                                                                                                                                 24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                 21
                                                                                                                                                                                                 13)) == (0b000100101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                        then
                                                                                                                                                                                          (do
                                                                                                                                                                                            let w__90 ← (( do
                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                              )
                                                                                                                                                                                              :
                                                                                                                                                                                              SailM
                                                                                                                                                                                              Int
                                                                                                                                                                                              )
                                                                                                                                                                                            (pure (((w__90 <b 1082) : Bool))))
                                                                                                                                                                                        else
                                                                                                                                                                                          (pure false)
                                                                                                                                                                                        )
                                                                                                                                                                                        :
                                                                                                                                                                                        SailM
                                                                                                                                                                                        Bool
                                                                                                                                                                                        )
                                                                                                                                                                                      if (w__91 : Bool)
                                                                                                                                                                                      then
                                                                                                                                                                                        (do
                                                                                                                                                                                          writeReg SEE 1082
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
                                                                                                                                                                                          (decode_FRINTA_Z_P_Z__
                                                                                                                                                                                            size
                                                                                                                                                                                            Pg
                                                                                                                                                                                            Zn
                                                                                                                                                                                            Zd)
                                                                                                                                                                                          (pure false))
                                                                                                                                                                                      else
                                                                                                                                                                                        (do
                                                                                                                                                                                          let w__93 ← (( do
                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     31
                                                                                                                                                                                                     24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                     21
                                                                                                                                                                                                     13)) == (0b000111101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                            then
                                                                                                                                                                                              (do
                                                                                                                                                                                                let w__92 ← (( do
                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                  )
                                                                                                                                                                                                  :
                                                                                                                                                                                                  SailM
                                                                                                                                                                                                  Int
                                                                                                                                                                                                  )
                                                                                                                                                                                                (pure (((w__92 <b 1083) : Bool))))
                                                                                                                                                                                            else
                                                                                                                                                                                              (pure false)
                                                                                                                                                                                            )
                                                                                                                                                                                            :
                                                                                                                                                                                            SailM
                                                                                                                                                                                            Bool
                                                                                                                                                                                            )
                                                                                                                                                                                          if (w__93 : Bool)
                                                                                                                                                                                          then
                                                                                                                                                                                            (do
                                                                                                                                                                                              writeReg SEE 1083
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
                                                                                                                                                                                              (decode_FRINTI_Z_P_Z__
                                                                                                                                                                                                size
                                                                                                                                                                                                Pg
                                                                                                                                                                                                Zn
                                                                                                                                                                                                Zd)
                                                                                                                                                                                              (pure false))
                                                                                                                                                                                          else
                                                                                                                                                                                            (do
                                                                                                                                                                                              let w__95 ← (( do
                                                                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         31
                                                                                                                                                                                                         24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                         __opcode
                                                                                                                                                                                                         21
                                                                                                                                                                                                         13)) == (0b000010101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                                then
                                                                                                                                                                                                  (do
                                                                                                                                                                                                    let w__94 ← (( do
                                                                                                                                                                                                      readReg SEE
                                                                                                                                                                                                      )
                                                                                                                                                                                                      :
                                                                                                                                                                                                      SailM
                                                                                                                                                                                                      Int
                                                                                                                                                                                                      )
                                                                                                                                                                                                    (pure (((w__94 <b 1084) : Bool))))
                                                                                                                                                                                                else
                                                                                                                                                                                                  (pure false)
                                                                                                                                                                                                )
                                                                                                                                                                                                :
                                                                                                                                                                                                SailM
                                                                                                                                                                                                Bool
                                                                                                                                                                                                )
                                                                                                                                                                                              if (w__95 : Bool)
                                                                                                                                                                                              then
                                                                                                                                                                                                (do
                                                                                                                                                                                                  writeReg SEE 1084
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
                                                                                                                                                                                                  (decode_FRINTM_Z_P_Z__
                                                                                                                                                                                                    size
                                                                                                                                                                                                    Pg
                                                                                                                                                                                                    Zn
                                                                                                                                                                                                    Zd)
                                                                                                                                                                                                  (pure false))
                                                                                                                                                                                              else
                                                                                                                                                                                                (do
                                                                                                                                                                                                  let w__97 ← (( do
                                                                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             31
                                                                                                                                                                                                             24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                             __opcode
                                                                                                                                                                                                             21
                                                                                                                                                                                                             13)) == (0b000000101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                                    then
                                                                                                                                                                                                      (do
                                                                                                                                                                                                        let w__96 ← (( do
                                                                                                                                                                                                          readReg SEE
                                                                                                                                                                                                          )
                                                                                                                                                                                                          :
                                                                                                                                                                                                          SailM
                                                                                                                                                                                                          Int
                                                                                                                                                                                                          )
                                                                                                                                                                                                        (pure (((w__96 <b 1085) : Bool))))
                                                                                                                                                                                                    else
                                                                                                                                                                                                      (pure false)
                                                                                                                                                                                                    )
                                                                                                                                                                                                    :
                                                                                                                                                                                                    SailM
                                                                                                                                                                                                    Bool
                                                                                                                                                                                                    )
                                                                                                                                                                                                  if (w__97 : Bool)
                                                                                                                                                                                                  then
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      writeReg SEE 1085
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
                                                                                                                                                                                                      (decode_FRINTN_Z_P_Z__
                                                                                                                                                                                                        size
                                                                                                                                                                                                        Pg
                                                                                                                                                                                                        Zn
                                                                                                                                                                                                        Zd)
                                                                                                                                                                                                      (pure false))
                                                                                                                                                                                                  else
                                                                                                                                                                                                    (do
                                                                                                                                                                                                      let w__99 ← (( do
                                                                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 31
                                                                                                                                                                                                                 24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                 __opcode
                                                                                                                                                                                                                 21
                                                                                                                                                                                                                 13)) == (0b000001101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                                        then
                                                                                                                                                                                                          (do
                                                                                                                                                                                                            let w__98 ← (( do
                                                                                                                                                                                                              readReg SEE
                                                                                                                                                                                                              )
                                                                                                                                                                                                              :
                                                                                                                                                                                                              SailM
                                                                                                                                                                                                              Int
                                                                                                                                                                                                              )
                                                                                                                                                                                                            (pure (((w__98 <b 1086) : Bool))))
                                                                                                                                                                                                        else
                                                                                                                                                                                                          (pure false)
                                                                                                                                                                                                        )
                                                                                                                                                                                                        :
                                                                                                                                                                                                        SailM
                                                                                                                                                                                                        Bool
                                                                                                                                                                                                        )
                                                                                                                                                                                                      if (w__99 : Bool)
                                                                                                                                                                                                      then
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          writeReg SEE 1086
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
                                                                                                                                                                                                          (decode_FRINTP_Z_P_Z__
                                                                                                                                                                                                            size
                                                                                                                                                                                                            Pg
                                                                                                                                                                                                            Zn
                                                                                                                                                                                                            Zd)
                                                                                                                                                                                                          (pure false))
                                                                                                                                                                                                      else
                                                                                                                                                                                                        (do
                                                                                                                                                                                                          let w__101 ← (( do
                                                                                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 8) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     31
                                                                                                                                                                                                                     24)) == (0x65#8 : (BitVec 8))) && ((Sail.BitVec.castWidth (m := 9) (Sail.BitVec.extractLsb
                                                                                                                                                                                                                     __opcode
                                                                                                                                                                                                                     21
                                                                                                                                                                                                                     13)) == (0b000110101#9 : (BitVec 9)))) : Bool) : Bool)
                                                                                                                                                                                                            then
                                                                                                                                                                                                              (do
                                                                                                                                                                                                                let w__100 ← (( do
                                                                                                                                                                                                                  readReg SEE
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                  :
                                                                                                                                                                                                                  SailM
                                                                                                                                                                                                                  Int
                                                                                                                                                                                                                  )
                                                                                                                                                                                                                (pure (((w__100 <b 1087) : Bool))))
                                                                                                                                                                                                            else
                                                                                                                                                                                                              (pure false)
                                                                                                                                                                                                            )
                                                                                                                                                                                                            :
                                                                                                                                                                                                            SailM
                                                                                                                                                                                                            Bool
                                                                                                                                                                                                            )
                                                                                                                                                                                                          if (w__101 : Bool)
                                                                                                                                                                                                          then
                                                                                                                                                                                                            (do
                                                                                                                                                                                                              writeReg SEE 1087
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
                                                                                                                                                                                                              (decode_FRINTX_Z_P_Z__
                                                                                                                                                                                                                size
                                                                                                                                                                                                                Pg
                                                                                                                                                                                                                Zn
                                                                                                                                                                                                                Zd)
                                                                                                                                                                                                              (pure false))
                                                                                                                                                                                                          else
                                                                                                                                                                                                            (pure true)))))))))))))))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
