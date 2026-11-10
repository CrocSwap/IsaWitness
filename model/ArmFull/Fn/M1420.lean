import Sail
import ArmFull.Defs
import ArmFull.SpecializationV1
import ArmFull.AbstractReal
import ArmFull.ArmExtrasFork
import ArmFull.Fn.M1027
import ArmFull.Fn.M1327
import ArmFull.Fn.M1328
import ArmFull.Fn.M1329

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
def __DecodeA64_SVE__seg25 (pc : Int) (__opcode : (BitVec 32)) : SailM Bool := do
  let w__2031 ← (( do
    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000101100#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
               __opcode 15 13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
               __opcode 4 4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
    then
      (do
        let w__2030 ← (( do readReg SEE ) : SailM Int )
        (pure (((w__2030 <b 2052) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__2031 : Bool)
  then
    (do
      writeReg SEE 2052
      let msz := (BitVec.slice __opcode 23 2)
      let imm5 := (BitVec.slice __opcode 16 5)
      let Pg := (BitVec.slice __opcode 10 3)
      let Zn := (BitVec.slice __opcode 5 5)
      let prfop := (BitVec.slice __opcode 0 4)
      (decode_PRFD_I_P_AI_D msz imm5 Pg Zn prfop)
      (pure false))
  else
    (do
      let w__2033 ← (( do
        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                 __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
        then
          (do
            let w__2032 ← (( do readReg SEE ) : SailM Int )
            (pure (((w__2032 <b 2053) : Bool))))
        else (pure false) ) : SailM Bool )
      if (w__2033 : Bool)
      then
        (do
          writeReg SEE 2053
          let msz := (BitVec.slice __opcode 23 2)
          let imm5 := (BitVec.slice __opcode 16 5)
          let U := (BitVec.slice __opcode 14 1)
          let ff := (BitVec.slice __opcode 13 1)
          let Pg := (BitVec.slice __opcode 10 3)
          let Zn := (BitVec.slice __opcode 5 5)
          let Zt := (BitVec.slice __opcode 0 5)
          (decode_LD1B_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
          (pure false))
      else
        (do
          let w__2035 ← (( do
            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                     __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
            then
              (do
                let w__2034 ← (( do readReg SEE ) : SailM Int )
                (pure (((w__2034 <b 2054) : Bool))))
            else (pure false) ) : SailM Bool )
          if (w__2035 : Bool)
          then
            (do
              writeReg SEE 2054
              let msz := (BitVec.slice __opcode 23 2)
              let imm5 := (BitVec.slice __opcode 16 5)
              let U := (BitVec.slice __opcode 14 1)
              let ff := (BitVec.slice __opcode 13 1)
              let Pg := (BitVec.slice __opcode 10 3)
              let Zn := (BitVec.slice __opcode 5 5)
              let Zt := (BitVec.slice __opcode 0 5)
              (decode_LD1SB_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
              (pure false))
          else
            (do
              let w__2037 ← (( do
                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                         __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                then
                  (do
                    let w__2036 ← (( do readReg SEE ) : SailM Int )
                    (pure (((w__2036 <b 2055) : Bool))))
                else (pure false) ) : SailM Bool )
              if (w__2037 : Bool)
              then
                (do
                  writeReg SEE 2055
                  let msz := (BitVec.slice __opcode 23 2)
                  let imm5 := (BitVec.slice __opcode 16 5)
                  let U := (BitVec.slice __opcode 14 1)
                  let ff := (BitVec.slice __opcode 13 1)
                  let Pg := (BitVec.slice __opcode 10 3)
                  let Zn := (BitVec.slice __opcode 5 5)
                  let Zt := (BitVec.slice __opcode 0 5)
                  (decode_LDFF1B_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                  (pure false))
              else
                (do
                  let w__2039 ← (( do
                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31 21)) == (0b11000100001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                             __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                    then
                      (do
                        let w__2038 ← (( do readReg SEE ) : SailM Int )
                        (pure (((w__2038 <b 2056) : Bool))))
                    else (pure false) ) : SailM Bool )
                  if (w__2039 : Bool)
                  then
                    (do
                      writeReg SEE 2056
                      let msz := (BitVec.slice __opcode 23 2)
                      let imm5 := (BitVec.slice __opcode 16 5)
                      let U := (BitVec.slice __opcode 14 1)
                      let ff := (BitVec.slice __opcode 13 1)
                      let Pg := (BitVec.slice __opcode 10 3)
                      let Zn := (BitVec.slice __opcode 5 5)
                      let Zt := (BitVec.slice __opcode 0 5)
                      (decode_LDFF1SB_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                      (pure false))
                  else
                    (do
                      let w__2041 ← (( do
                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode 31
                                 21)) == (0b11000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                 __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                        then
                          (do
                            let w__2040 ← (( do readReg SEE ) : SailM Int )
                            (pure (((w__2040 <b 2057) : Bool))))
                        else (pure false) ) : SailM Bool )
                      if (w__2041 : Bool)
                      then
                        (do
                          writeReg SEE 2057
                          let msz := (BitVec.slice __opcode 23 2)
                          let imm5 := (BitVec.slice __opcode 16 5)
                          let U := (BitVec.slice __opcode 14 1)
                          let ff := (BitVec.slice __opcode 13 1)
                          let Pg := (BitVec.slice __opcode 10 3)
                          let Zn := (BitVec.slice __opcode 5 5)
                          let Zt := (BitVec.slice __opcode 0 5)
                          (decode_LD1H_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                          (pure false))
                      else
                        (do
                          let w__2043 ← (( do
                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb __opcode
                                     31 21)) == (0b11000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                     __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                            then
                              (do
                                let w__2042 ← (( do readReg SEE ) : SailM Int )
                                (pure (((w__2042 <b 2058) : Bool))))
                            else (pure false) ) : SailM Bool )
                          if (w__2043 : Bool)
                          then
                            (do
                              writeReg SEE 2058
                              let msz := (BitVec.slice __opcode 23 2)
                              let imm5 := (BitVec.slice __opcode 16 5)
                              let U := (BitVec.slice __opcode 14 1)
                              let ff := (BitVec.slice __opcode 13 1)
                              let Pg := (BitVec.slice __opcode 10 3)
                              let Zn := (BitVec.slice __opcode 5 5)
                              let Zt := (BitVec.slice __opcode 0 5)
                              (decode_LD1SH_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                              (pure false))
                          else
                            (do
                              let w__2045 ← (( do
                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                         __opcode 31 21)) == (0b11000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                         __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                then
                                  (do
                                    let w__2044 ← (( do readReg SEE ) : SailM Int )
                                    (pure (((w__2044 <b 2059) : Bool))))
                                else (pure false) ) : SailM Bool )
                              if (w__2045 : Bool)
                              then
                                (do
                                  writeReg SEE 2059
                                  let msz := (BitVec.slice __opcode 23 2)
                                  let imm5 := (BitVec.slice __opcode 16 5)
                                  let U := (BitVec.slice __opcode 14 1)
                                  let ff := (BitVec.slice __opcode 13 1)
                                  let Pg := (BitVec.slice __opcode 10 3)
                                  let Zn := (BitVec.slice __opcode 5 5)
                                  let Zt := (BitVec.slice __opcode 0 5)
                                  (decode_LDFF1H_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                                  (pure false))
                              else
                                (do
                                  let w__2047 ← (( do
                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                             __opcode 31 21)) == (0b11000100101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                             __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                    then
                                      (do
                                        let w__2046 ← (( do readReg SEE ) : SailM Int )
                                        (pure (((w__2046 <b 2060) : Bool))))
                                    else (pure false) ) : SailM Bool )
                                  if (w__2047 : Bool)
                                  then
                                    (do
                                      writeReg SEE 2060
                                      let msz := (BitVec.slice __opcode 23 2)
                                      let imm5 := (BitVec.slice __opcode 16 5)
                                      let U := (BitVec.slice __opcode 14 1)
                                      let ff := (BitVec.slice __opcode 13 1)
                                      let Pg := (BitVec.slice __opcode 10 3)
                                      let Zn := (BitVec.slice __opcode 5 5)
                                      let Zt := (BitVec.slice __opcode 0 5)
                                      (decode_LDFF1SH_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                                      (pure false))
                                  else
                                    (do
                                      let w__2049 ← (( do
                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                 __opcode 31 21)) == (0b11000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                 __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                        then
                                          (do
                                            let w__2048 ← (( do readReg SEE ) : SailM Int )
                                            (pure (((w__2048 <b 2061) : Bool))))
                                        else (pure false) ) : SailM Bool )
                                      if (w__2049 : Bool)
                                      then
                                        (do
                                          writeReg SEE 2061
                                          let msz := (BitVec.slice __opcode 23 2)
                                          let imm5 := (BitVec.slice __opcode 16 5)
                                          let U := (BitVec.slice __opcode 14 1)
                                          let ff := (BitVec.slice __opcode 13 1)
                                          let Pg := (BitVec.slice __opcode 10 3)
                                          let Zn := (BitVec.slice __opcode 5 5)
                                          let Zt := (BitVec.slice __opcode 0 5)
                                          (decode_LD1W_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                                          (pure false))
                                      else
                                        (do
                                          let w__2051 ← (( do
                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                     __opcode 31 21)) == (0b11000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                     __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                            then
                                              (do
                                                let w__2050 ← (( do readReg SEE ) : SailM Int )
                                                (pure (((w__2050 <b 2062) : Bool))))
                                            else (pure false) ) : SailM Bool )
                                          if (w__2051 : Bool)
                                          then
                                            (do
                                              writeReg SEE 2062
                                              let msz := (BitVec.slice __opcode 23 2)
                                              let imm5 := (BitVec.slice __opcode 16 5)
                                              let U := (BitVec.slice __opcode 14 1)
                                              let ff := (BitVec.slice __opcode 13 1)
                                              let Pg := (BitVec.slice __opcode 10 3)
                                              let Zn := (BitVec.slice __opcode 5 5)
                                              let Zt := (BitVec.slice __opcode 0 5)
                                              (decode_LD1SW_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                                              (pure false))
                                          else
                                            (do
                                              let w__2053 ← (( do
                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                         __opcode 31 21)) == (0b11000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                         __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                then
                                                  (do
                                                    let w__2052 ← (( do readReg SEE ) : SailM Int
                                                      )
                                                    (pure (((w__2052 <b 2063) : Bool))))
                                                else (pure false) ) : SailM Bool )
                                              if (w__2053 : Bool)
                                              then
                                                (do
                                                  writeReg SEE 2063
                                                  let msz := (BitVec.slice __opcode 23 2)
                                                  let imm5 := (BitVec.slice __opcode 16 5)
                                                  let U := (BitVec.slice __opcode 14 1)
                                                  let ff := (BitVec.slice __opcode 13 1)
                                                  let Pg := (BitVec.slice __opcode 10 3)
                                                  let Zn := (BitVec.slice __opcode 5 5)
                                                  let Zt := (BitVec.slice __opcode 0 5)
                                                  (decode_LDFF1W_Z_P_AI_D msz imm5 U ff Pg Zn Zt)
                                                  (pure false))
                                              else
                                                (do
                                                  let w__2055 ← (( do
                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                             __opcode 31 21)) == (0b11000101001#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                             __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                    then
                                                      (do
                                                        let w__2054 ← (( do readReg SEE ) : SailM
                                                          Int )
                                                        (pure (((w__2054 <b 2064) : Bool))))
                                                    else (pure false) ) : SailM Bool )
                                                  if (w__2055 : Bool)
                                                  then
                                                    (do
                                                      writeReg SEE 2064
                                                      let msz := (BitVec.slice __opcode 23 2)
                                                      let imm5 := (BitVec.slice __opcode 16 5)
                                                      let U := (BitVec.slice __opcode 14 1)
                                                      let ff := (BitVec.slice __opcode 13 1)
                                                      let Pg := (BitVec.slice __opcode 10 3)
                                                      let Zn := (BitVec.slice __opcode 5 5)
                                                      let Zt := (BitVec.slice __opcode 0 5)
                                                      (decode_LDFF1SW_Z_P_AI_D msz imm5 U ff Pg Zn
                                                        Zt)
                                                      (pure false))
                                                  else
                                                    (do
                                                      let w__2057 ← (( do
                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                 __opcode 31 21)) == (0b11000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                 __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                        then
                                                          (do
                                                            let w__2056 ← (( do readReg SEE ) :
                                                              SailM Int )
                                                            (pure (((w__2056 <b 2065) : Bool))))
                                                        else (pure false) ) : SailM Bool )
                                                      if (w__2057 : Bool)
                                                      then
                                                        (do
                                                          writeReg SEE 2065
                                                          let msz := (BitVec.slice __opcode 23 2)
                                                          let imm5 := (BitVec.slice __opcode 16 5)
                                                          let U := (BitVec.slice __opcode 14 1)
                                                          let ff := (BitVec.slice __opcode 13 1)
                                                          let Pg := (BitVec.slice __opcode 10 3)
                                                          let Zn := (BitVec.slice __opcode 5 5)
                                                          let Zt := (BitVec.slice __opcode 0 5)
                                                          (decode_LD1D_Z_P_AI_D msz imm5 U ff Pg Zn
                                                            Zt)
                                                          (pure false))
                                                      else
                                                        (do
                                                          let w__2059 ← (( do
                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                     __opcode 31 21)) == (0b11000101101#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                     __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                            then
                                                              (do
                                                                let w__2058 ← (( do readReg SEE )
                                                                  : SailM Int )
                                                                (pure (((w__2058 <b 2066) : Bool))))
                                                            else (pure false) ) : SailM Bool )
                                                          if (w__2059 : Bool)
                                                          then
                                                            (do
                                                              writeReg SEE 2066
                                                              let msz :=
                                                                (BitVec.slice __opcode 23 2)
                                                              let imm5 :=
                                                                (BitVec.slice __opcode 16 5)
                                                              let U := (BitVec.slice __opcode 14 1)
                                                              let ff := (BitVec.slice __opcode 13 1)
                                                              let Pg := (BitVec.slice __opcode 10 3)
                                                              let Zn := (BitVec.slice __opcode 5 5)
                                                              let Zt := (BitVec.slice __opcode 0 5)
                                                              (decode_LDFF1D_Z_P_AI_D msz imm5 U ff
                                                                Pg Zn Zt)
                                                              (pure false))
                                                          else
                                                            (do
                                                              let w__2061 ← (( do
                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                         __opcode 31 21)) == (0b11000100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                         __opcode 15 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                then
                                                                  (do
                                                                    let w__2060 ← (( do
                                                                      readReg SEE ) : SailM Int )
                                                                    (pure (((w__2060 <b 2067) : Bool))))
                                                                else (pure false) ) : SailM Bool )
                                                              if (w__2061 : Bool)
                                                              then
                                                                (do
                                                                  writeReg SEE 2067
                                                                  let msz :=
                                                                    (BitVec.slice __opcode 23 2)
                                                                  let Zm :=
                                                                    (BitVec.slice __opcode 16 5)
                                                                  let U :=
                                                                    (BitVec.slice __opcode 14 1)
                                                                  let ff :=
                                                                    (BitVec.slice __opcode 13 1)
                                                                  let Pg :=
                                                                    (BitVec.slice __opcode 10 3)
                                                                  let Rn :=
                                                                    (BitVec.slice __opcode 5 5)
                                                                  let Zt :=
                                                                    (BitVec.slice __opcode 0 5)
                                                                  (decode_LD1B_Z_P_BZ_D_64_unscaled
                                                                    msz Zm U ff Pg Rn Zt)
                                                                  (pure false))
                                                              else
                                                                (do
                                                                  let w__2063 ← (( do
                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                             __opcode 31 21)) == (0b11000100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                             __opcode 15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                    then
                                                                      (do
                                                                        let w__2062 ← (( do
                                                                          readReg SEE ) : SailM Int
                                                                          )
                                                                        (pure (((w__2062 <b 2068) : Bool))))
                                                                    else (pure false) ) : SailM Bool
                                                                    )
                                                                  if (w__2063 : Bool)
                                                                  then
                                                                    (do
                                                                      writeReg SEE 2068
                                                                      let msz :=
                                                                        (BitVec.slice __opcode 23 2)
                                                                      let Zm :=
                                                                        (BitVec.slice __opcode 16 5)
                                                                      let U :=
                                                                        (BitVec.slice __opcode 14 1)
                                                                      let ff :=
                                                                        (BitVec.slice __opcode 13 1)
                                                                      let Pg :=
                                                                        (BitVec.slice __opcode 10 3)
                                                                      let Rn :=
                                                                        (BitVec.slice __opcode 5 5)
                                                                      let Zt :=
                                                                        (BitVec.slice __opcode 0 5)
                                                                      (decode_LD1SB_Z_P_BZ_D_64_unscaled
                                                                        msz Zm U ff Pg Rn Zt)
                                                                      (pure false))
                                                                  else
                                                                    (do
                                                                      let w__2065 ← (( do
                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                 __opcode 31 21)) == (0b11000100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                 __opcode 15 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                        then
                                                                          (do
                                                                            let w__2064 ← (( do
                                                                              readReg SEE ) : SailM
                                                                              Int )
                                                                            (pure (((w__2064 <b 2069) : Bool))))
                                                                        else (pure false) ) : SailM
                                                                        Bool )
                                                                      if (w__2065 : Bool)
                                                                      then
                                                                        (do
                                                                          writeReg SEE 2069
                                                                          let msz :=
                                                                            (BitVec.slice __opcode
                                                                              23 2)
                                                                          let Zm :=
                                                                            (BitVec.slice __opcode
                                                                              16 5)
                                                                          let U :=
                                                                            (BitVec.slice __opcode
                                                                              14 1)
                                                                          let ff :=
                                                                            (BitVec.slice __opcode
                                                                              13 1)
                                                                          let Pg :=
                                                                            (BitVec.slice __opcode
                                                                              10 3)
                                                                          let Rn :=
                                                                            (BitVec.slice __opcode 5
                                                                              5)
                                                                          let Zt :=
                                                                            (BitVec.slice __opcode 0
                                                                              5)
                                                                          (decode_LDFF1B_Z_P_BZ_D_64_unscaled
                                                                            msz Zm U ff Pg Rn Zt)
                                                                          (pure false))
                                                                      else
                                                                        (do
                                                                          let w__2067 ← (( do
                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                     __opcode 31 21)) == (0b11000100010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                     __opcode 15 13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                            then
                                                                              (do
                                                                                let w__2066 ← (( do
                                                                                  readReg SEE ) :
                                                                                  SailM Int )
                                                                                (pure (((w__2066 <b 2070) : Bool))))
                                                                            else (pure false) ) :
                                                                            SailM Bool )
                                                                          if (w__2067 : Bool)
                                                                          then
                                                                            (do
                                                                              writeReg SEE 2070
                                                                              let msz :=
                                                                                (BitVec.slice
                                                                                  __opcode 23 2)
                                                                              let Zm :=
                                                                                (BitVec.slice
                                                                                  __opcode 16 5)
                                                                              let U :=
                                                                                (BitVec.slice
                                                                                  __opcode 14 1)
                                                                              let ff :=
                                                                                (BitVec.slice
                                                                                  __opcode 13 1)
                                                                              let Pg :=
                                                                                (BitVec.slice
                                                                                  __opcode 10 3)
                                                                              let Rn :=
                                                                                (BitVec.slice
                                                                                  __opcode 5 5)
                                                                              let Zt :=
                                                                                (BitVec.slice
                                                                                  __opcode 0 5)
                                                                              (decode_LDFF1SB_Z_P_BZ_D_64_unscaled
                                                                                msz Zm U ff Pg Rn Zt)
                                                                              (pure false))
                                                                          else
                                                                            (do
                                                                              let w__2069 ← (( do
                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                         __opcode 31
                                                                                         21)) == (0b11000100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                         __opcode 15
                                                                                         13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                then
                                                                                  (do
                                                                                    let w__2068 ← (( do
                                                                                      readReg SEE )
                                                                                      : SailM Int )
                                                                                    (pure (((w__2068 <b 2071) : Bool))))
                                                                                else (pure false) )
                                                                                : SailM Bool )
                                                                              if (w__2069 : Bool)
                                                                              then
                                                                                (do
                                                                                  writeReg SEE 2071
                                                                                  let msz :=
                                                                                    (BitVec.slice
                                                                                      __opcode 23 2)
                                                                                  let Zm :=
                                                                                    (BitVec.slice
                                                                                      __opcode 16 5)
                                                                                  let U :=
                                                                                    (BitVec.slice
                                                                                      __opcode 14 1)
                                                                                  let ff :=
                                                                                    (BitVec.slice
                                                                                      __opcode 13 1)
                                                                                  let Pg :=
                                                                                    (BitVec.slice
                                                                                      __opcode 10 3)
                                                                                  let Rn :=
                                                                                    (BitVec.slice
                                                                                      __opcode 5 5)
                                                                                  let Zt :=
                                                                                    (BitVec.slice
                                                                                      __opcode 0 5)
                                                                                  (decode_LD1H_Z_P_BZ_D_64_unscaled
                                                                                    msz Zm U ff Pg
                                                                                    Rn Zt)
                                                                                  (pure false))
                                                                              else
                                                                                (do
                                                                                  let w__2071 ← (( do
                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             31 21)) == (0b11000100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                             __opcode
                                                                                             15 13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                    then
                                                                                      (do
                                                                                        let w__2070 ← (( do
                                                                                          readReg SEE
                                                                                          ) : SailM
                                                                                          Int )
                                                                                        (pure (((w__2070 <b 2072) : Bool))))
                                                                                    else
                                                                                      (pure false) )
                                                                                    : SailM Bool )
                                                                                  if (w__2071 : Bool)
                                                                                  then
                                                                                    (do
                                                                                      writeReg SEE 2072
                                                                                      let msz :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          23 2)
                                                                                      let Zm :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          16 5)
                                                                                      let U :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          14 1)
                                                                                      let ff :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          13 1)
                                                                                      let Pg :=
                                                                                        (BitVec.slice
                                                                                          __opcode
                                                                                          10 3)
                                                                                      let Rn :=
                                                                                        (BitVec.slice
                                                                                          __opcode 5
                                                                                          5)
                                                                                      let Zt :=
                                                                                        (BitVec.slice
                                                                                          __opcode 0
                                                                                          5)
                                                                                      (decode_LD1SH_Z_P_BZ_D_64_unscaled
                                                                                        msz Zm U ff
                                                                                        Pg Rn Zt)
                                                                                      (pure false))
                                                                                  else
                                                                                    (do
                                                                                      let w__2073 ← (( do
                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 31
                                                                                                 21)) == (0b11000100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                 __opcode
                                                                                                 15
                                                                                                 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                        then
                                                                                          (do
                                                                                            let w__2072 ← (( do
                                                                                              readReg SEE
                                                                                              ) :
                                                                                              SailM
                                                                                              Int )
                                                                                            (pure (((w__2072 <b 2073) : Bool))))
                                                                                        else
                                                                                          (pure false)
                                                                                        ) : SailM
                                                                                        Bool )
                                                                                      if (w__2073 : Bool)
                                                                                      then
                                                                                        (do
                                                                                          writeReg SEE 2073
                                                                                          let msz :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              23 2)
                                                                                          let Zm :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              16 5)
                                                                                          let U :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              14 1)
                                                                                          let ff :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              13 1)
                                                                                          let Pg :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              10 3)
                                                                                          let Rn :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              5 5)
                                                                                          let Zt :=
                                                                                            (BitVec.slice
                                                                                              __opcode
                                                                                              0 5)
                                                                                          (decode_LDFF1H_Z_P_BZ_D_64_unscaled
                                                                                            msz Zm U
                                                                                            ff Pg Rn
                                                                                            Zt)
                                                                                          (pure false))
                                                                                      else
                                                                                        (do
                                                                                          let w__2075 ← (( do
                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     31
                                                                                                     21)) == (0b11000100110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                     __opcode
                                                                                                     15
                                                                                                     13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                            then
                                                                                              (do
                                                                                                let w__2074 ← (( do
                                                                                                  readReg SEE
                                                                                                  )
                                                                                                  :
                                                                                                  SailM
                                                                                                  Int
                                                                                                  )
                                                                                                (pure (((w__2074 <b 2074) : Bool))))
                                                                                            else
                                                                                              (pure false)
                                                                                            ) :
                                                                                            SailM
                                                                                            Bool )
                                                                                          if (w__2075 : Bool)
                                                                                          then
                                                                                            (do
                                                                                              writeReg SEE 2074
                                                                                              let msz :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  23
                                                                                                  2)
                                                                                              let Zm :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  16
                                                                                                  5)
                                                                                              let U :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  14
                                                                                                  1)
                                                                                              let ff :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  13
                                                                                                  1)
                                                                                              let Pg :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  10
                                                                                                  3)
                                                                                              let Rn :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  5
                                                                                                  5)
                                                                                              let Zt :=
                                                                                                (BitVec.slice
                                                                                                  __opcode
                                                                                                  0
                                                                                                  5)
                                                                                              (decode_LDFF1SH_Z_P_BZ_D_64_unscaled
                                                                                                msz
                                                                                                Zm U
                                                                                                ff
                                                                                                Pg
                                                                                                Rn
                                                                                                Zt)
                                                                                              (pure false))
                                                                                          else
                                                                                            (do
                                                                                              let w__2077 ← (( do
                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         31
                                                                                                         21)) == (0b11000101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                         __opcode
                                                                                                         15
                                                                                                         13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                then
                                                                                                  (do
                                                                                                    let w__2076 ← (( do
                                                                                                      readReg SEE
                                                                                                      )
                                                                                                      :
                                                                                                      SailM
                                                                                                      Int
                                                                                                      )
                                                                                                    (pure (((w__2076 <b 2075) : Bool))))
                                                                                                else
                                                                                                  (pure false)
                                                                                                ) :
                                                                                                SailM
                                                                                                Bool
                                                                                                )
                                                                                              if (w__2077 : Bool)
                                                                                              then
                                                                                                (do
                                                                                                  writeReg SEE 2075
                                                                                                  let msz :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      23
                                                                                                      2)
                                                                                                  let Zm :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      16
                                                                                                      5)
                                                                                                  let U :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      14
                                                                                                      1)
                                                                                                  let ff :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      13
                                                                                                      1)
                                                                                                  let Pg :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      10
                                                                                                      3)
                                                                                                  let Rn :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      5
                                                                                                      5)
                                                                                                  let Zt :=
                                                                                                    (BitVec.slice
                                                                                                      __opcode
                                                                                                      0
                                                                                                      5)
                                                                                                  (decode_LD1W_Z_P_BZ_D_64_unscaled
                                                                                                    msz
                                                                                                    Zm
                                                                                                    U
                                                                                                    ff
                                                                                                    Pg
                                                                                                    Rn
                                                                                                    Zt)
                                                                                                  (pure false))
                                                                                              else
                                                                                                (do
                                                                                                  let w__2079 ← (( do
                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             31
                                                                                                             21)) == (0b11000101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                             __opcode
                                                                                                             15
                                                                                                             13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                    then
                                                                                                      (do
                                                                                                        let w__2078 ← (( do
                                                                                                          readReg SEE
                                                                                                          )
                                                                                                          :
                                                                                                          SailM
                                                                                                          Int
                                                                                                          )
                                                                                                        (pure (((w__2078 <b 2076) : Bool))))
                                                                                                    else
                                                                                                      (pure false)
                                                                                                    )
                                                                                                    :
                                                                                                    SailM
                                                                                                    Bool
                                                                                                    )
                                                                                                  if (w__2079 : Bool)
                                                                                                  then
                                                                                                    (do
                                                                                                      writeReg SEE 2076
                                                                                                      let msz :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          23
                                                                                                          2)
                                                                                                      let Zm :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          16
                                                                                                          5)
                                                                                                      let U :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          14
                                                                                                          1)
                                                                                                      let ff :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          13
                                                                                                          1)
                                                                                                      let Pg :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          10
                                                                                                          3)
                                                                                                      let Rn :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          5
                                                                                                          5)
                                                                                                      let Zt :=
                                                                                                        (BitVec.slice
                                                                                                          __opcode
                                                                                                          0
                                                                                                          5)
                                                                                                      (decode_LD1SW_Z_P_BZ_D_64_unscaled
                                                                                                        msz
                                                                                                        Zm
                                                                                                        U
                                                                                                        ff
                                                                                                        Pg
                                                                                                        Rn
                                                                                                        Zt)
                                                                                                      (pure false))
                                                                                                  else
                                                                                                    (do
                                                                                                      let w__2081 ← (( do
                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 31
                                                                                                                 21)) == (0b11000101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                 __opcode
                                                                                                                 15
                                                                                                                 13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                        then
                                                                                                          (do
                                                                                                            let w__2080 ← (( do
                                                                                                              readReg SEE
                                                                                                              )
                                                                                                              :
                                                                                                              SailM
                                                                                                              Int
                                                                                                              )
                                                                                                            (pure (((w__2080 <b 2077) : Bool))))
                                                                                                        else
                                                                                                          (pure false)
                                                                                                        )
                                                                                                        :
                                                                                                        SailM
                                                                                                        Bool
                                                                                                        )
                                                                                                      if (w__2081 : Bool)
                                                                                                      then
                                                                                                        (do
                                                                                                          writeReg SEE 2077
                                                                                                          let msz :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              23
                                                                                                              2)
                                                                                                          let Zm :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              16
                                                                                                              5)
                                                                                                          let U :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              14
                                                                                                              1)
                                                                                                          let ff :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              13
                                                                                                              1)
                                                                                                          let Pg :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              10
                                                                                                              3)
                                                                                                          let Rn :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              5
                                                                                                              5)
                                                                                                          let Zt :=
                                                                                                            (BitVec.slice
                                                                                                              __opcode
                                                                                                              0
                                                                                                              5)
                                                                                                          (decode_LDFF1W_Z_P_BZ_D_64_unscaled
                                                                                                            msz
                                                                                                            Zm
                                                                                                            U
                                                                                                            ff
                                                                                                            Pg
                                                                                                            Rn
                                                                                                            Zt)
                                                                                                          (pure false))
                                                                                                      else
                                                                                                        (do
                                                                                                          let w__2083 ← (( do
                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     31
                                                                                                                     21)) == (0b11000101010#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                     __opcode
                                                                                                                     15
                                                                                                                     13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                            then
                                                                                                              (do
                                                                                                                let w__2082 ← (( do
                                                                                                                  readReg SEE
                                                                                                                  )
                                                                                                                  :
                                                                                                                  SailM
                                                                                                                  Int
                                                                                                                  )
                                                                                                                (pure (((w__2082 <b 2078) : Bool))))
                                                                                                            else
                                                                                                              (pure false)
                                                                                                            )
                                                                                                            :
                                                                                                            SailM
                                                                                                            Bool
                                                                                                            )
                                                                                                          if (w__2083 : Bool)
                                                                                                          then
                                                                                                            (do
                                                                                                              writeReg SEE 2078
                                                                                                              let msz :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  23
                                                                                                                  2)
                                                                                                              let Zm :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  16
                                                                                                                  5)
                                                                                                              let U :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  14
                                                                                                                  1)
                                                                                                              let ff :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  13
                                                                                                                  1)
                                                                                                              let Pg :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  10
                                                                                                                  3)
                                                                                                              let Rn :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  5
                                                                                                                  5)
                                                                                                              let Zt :=
                                                                                                                (BitVec.slice
                                                                                                                  __opcode
                                                                                                                  0
                                                                                                                  5)
                                                                                                              (decode_LDFF1SW_Z_P_BZ_D_64_unscaled
                                                                                                                msz
                                                                                                                Zm
                                                                                                                U
                                                                                                                ff
                                                                                                                Pg
                                                                                                                Rn
                                                                                                                Zt)
                                                                                                              (pure false))
                                                                                                          else
                                                                                                            (do
                                                                                                              let w__2085 ← (( do
                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         31
                                                                                                                         21)) == (0b11000101110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                         __opcode
                                                                                                                         15
                                                                                                                         13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                then
                                                                                                                  (do
                                                                                                                    let w__2084 ← (( do
                                                                                                                      readReg SEE
                                                                                                                      )
                                                                                                                      :
                                                                                                                      SailM
                                                                                                                      Int
                                                                                                                      )
                                                                                                                    (pure (((w__2084 <b 2079) : Bool))))
                                                                                                                else
                                                                                                                  (pure false)
                                                                                                                )
                                                                                                                :
                                                                                                                SailM
                                                                                                                Bool
                                                                                                                )
                                                                                                              if (w__2085 : Bool)
                                                                                                              then
                                                                                                                (do
                                                                                                                  writeReg SEE 2079
                                                                                                                  let msz :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      23
                                                                                                                      2)
                                                                                                                  let Zm :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      16
                                                                                                                      5)
                                                                                                                  let U :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      14
                                                                                                                      1)
                                                                                                                  let ff :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      13
                                                                                                                      1)
                                                                                                                  let Pg :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      10
                                                                                                                      3)
                                                                                                                  let Rn :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      5
                                                                                                                      5)
                                                                                                                  let Zt :=
                                                                                                                    (BitVec.slice
                                                                                                                      __opcode
                                                                                                                      0
                                                                                                                      5)
                                                                                                                  (decode_LD1D_Z_P_BZ_D_64_unscaled
                                                                                                                    msz
                                                                                                                    Zm
                                                                                                                    U
                                                                                                                    ff
                                                                                                                    Pg
                                                                                                                    Rn
                                                                                                                    Zt)
                                                                                                                  (pure false))
                                                                                                              else
                                                                                                                (do
                                                                                                                  let w__2087 ← (( do
                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             31
                                                                                                                             21)) == (0b11000101110#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                             __opcode
                                                                                                                             15
                                                                                                                             13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                    then
                                                                                                                      (do
                                                                                                                        let w__2086 ← (( do
                                                                                                                          readReg SEE
                                                                                                                          )
                                                                                                                          :
                                                                                                                          SailM
                                                                                                                          Int
                                                                                                                          )
                                                                                                                        (pure (((w__2086 <b 2080) : Bool))))
                                                                                                                    else
                                                                                                                      (pure false)
                                                                                                                    )
                                                                                                                    :
                                                                                                                    SailM
                                                                                                                    Bool
                                                                                                                    )
                                                                                                                  if (w__2087 : Bool)
                                                                                                                  then
                                                                                                                    (do
                                                                                                                      writeReg SEE 2080
                                                                                                                      let msz :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          23
                                                                                                                          2)
                                                                                                                      let Zm :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          16
                                                                                                                          5)
                                                                                                                      let U :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          14
                                                                                                                          1)
                                                                                                                      let ff :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          13
                                                                                                                          1)
                                                                                                                      let Pg :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          10
                                                                                                                          3)
                                                                                                                      let Rn :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          5
                                                                                                                          5)
                                                                                                                      let Zt :=
                                                                                                                        (BitVec.slice
                                                                                                                          __opcode
                                                                                                                          0
                                                                                                                          5)
                                                                                                                      (decode_LDFF1D_Z_P_BZ_D_64_unscaled
                                                                                                                        msz
                                                                                                                        Zm
                                                                                                                        U
                                                                                                                        ff
                                                                                                                        Pg
                                                                                                                        Rn
                                                                                                                        Zt)
                                                                                                                      (pure false))
                                                                                                                  else
                                                                                                                    (do
                                                                                                                      let w__2089 ← (( do
                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                 __opcode
                                                                                                                                 31
                                                                                                                                 21)) == (0b11000100011#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   15
                                                                                                                                   13)) == (0b100#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                   __opcode
                                                                                                                                   4
                                                                                                                                   4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                        then
                                                                                                                          (do
                                                                                                                            let w__2088 ← (( do
                                                                                                                              readReg SEE
                                                                                                                              )
                                                                                                                              :
                                                                                                                              SailM
                                                                                                                              Int
                                                                                                                              )
                                                                                                                            (pure (((w__2088 <b 2081) : Bool))))
                                                                                                                        else
                                                                                                                          (pure false)
                                                                                                                        )
                                                                                                                        :
                                                                                                                        SailM
                                                                                                                        Bool
                                                                                                                        )
                                                                                                                      if (w__2089 : Bool)
                                                                                                                      then
                                                                                                                        (do
                                                                                                                          writeReg SEE 2081
                                                                                                                          let Zm :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              16
                                                                                                                              5)
                                                                                                                          let msz :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              13
                                                                                                                              2)
                                                                                                                          let Pg :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              10
                                                                                                                              3)
                                                                                                                          let Rn :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              5
                                                                                                                              5)
                                                                                                                          let prfop :=
                                                                                                                            (BitVec.slice
                                                                                                                              __opcode
                                                                                                                              0
                                                                                                                              4)
                                                                                                                          (decode_PRFB_I_P_BZ_D_64_scaled
                                                                                                                            Zm
                                                                                                                            msz
                                                                                                                            Pg
                                                                                                                            Rn
                                                                                                                            prfop)
                                                                                                                          (pure false))
                                                                                                                      else
                                                                                                                        (do
                                                                                                                          let w__2091 ← (( do
                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                     __opcode
                                                                                                                                     31
                                                                                                                                     21)) == (0b11000100011#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       15
                                                                                                                                       13)) == (0b101#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                       __opcode
                                                                                                                                       4
                                                                                                                                       4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                            then
                                                                                                                              (do
                                                                                                                                let w__2090 ← (( do
                                                                                                                                  readReg SEE
                                                                                                                                  )
                                                                                                                                  :
                                                                                                                                  SailM
                                                                                                                                  Int
                                                                                                                                  )
                                                                                                                                (pure (((w__2090 <b 2082) : Bool))))
                                                                                                                            else
                                                                                                                              (pure false)
                                                                                                                            )
                                                                                                                            :
                                                                                                                            SailM
                                                                                                                            Bool
                                                                                                                            )
                                                                                                                          if (w__2091 : Bool)
                                                                                                                          then
                                                                                                                            (do
                                                                                                                              writeReg SEE 2082
                                                                                                                              let Zm :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  16
                                                                                                                                  5)
                                                                                                                              let msz :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  13
                                                                                                                                  2)
                                                                                                                              let Pg :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  10
                                                                                                                                  3)
                                                                                                                              let Rn :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  5
                                                                                                                                  5)
                                                                                                                              let prfop :=
                                                                                                                                (BitVec.slice
                                                                                                                                  __opcode
                                                                                                                                  0
                                                                                                                                  4)
                                                                                                                              (decode_PRFH_I_P_BZ_D_64_scaled
                                                                                                                                Zm
                                                                                                                                msz
                                                                                                                                Pg
                                                                                                                                Rn
                                                                                                                                prfop)
                                                                                                                              (pure false))
                                                                                                                          else
                                                                                                                            (do
                                                                                                                              let w__2093 ← (( do
                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                         __opcode
                                                                                                                                         31
                                                                                                                                         21)) == (0b11000100011#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           15
                                                                                                                                           13)) == (0b110#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                           __opcode
                                                                                                                                           4
                                                                                                                                           4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                then
                                                                                                                                  (do
                                                                                                                                    let w__2092 ← (( do
                                                                                                                                      readReg SEE
                                                                                                                                      )
                                                                                                                                      :
                                                                                                                                      SailM
                                                                                                                                      Int
                                                                                                                                      )
                                                                                                                                    (pure (((w__2092 <b 2083) : Bool))))
                                                                                                                                else
                                                                                                                                  (pure false)
                                                                                                                                )
                                                                                                                                :
                                                                                                                                SailM
                                                                                                                                Bool
                                                                                                                                )
                                                                                                                              if (w__2093 : Bool)
                                                                                                                              then
                                                                                                                                (do
                                                                                                                                  writeReg SEE 2083
                                                                                                                                  let Zm :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      16
                                                                                                                                      5)
                                                                                                                                  let msz :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      13
                                                                                                                                      2)
                                                                                                                                  let Pg :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      10
                                                                                                                                      3)
                                                                                                                                  let Rn :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      5
                                                                                                                                      5)
                                                                                                                                  let prfop :=
                                                                                                                                    (BitVec.slice
                                                                                                                                      __opcode
                                                                                                                                      0
                                                                                                                                      4)
                                                                                                                                  (decode_PRFW_I_P_BZ_D_64_scaled
                                                                                                                                    Zm
                                                                                                                                    msz
                                                                                                                                    Pg
                                                                                                                                    Rn
                                                                                                                                    prfop)
                                                                                                                                  (pure false))
                                                                                                                              else
                                                                                                                                (do
                                                                                                                                  let w__2095 ← (( do
                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                             __opcode
                                                                                                                                             31
                                                                                                                                             21)) == (0b11000100011#11 : (BitVec 11))) && (((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               15
                                                                                                                                               13)) == (0b111#3 : (BitVec 3))) && ((Sail.BitVec.castWidth (m := 1) (Sail.BitVec.extractLsb
                                                                                                                                               __opcode
                                                                                                                                               4
                                                                                                                                               4)) == (0#1 : (BitVec 1))))) : Bool) : Bool)
                                                                                                                                    then
                                                                                                                                      (do
                                                                                                                                        let w__2094 ← (( do
                                                                                                                                          readReg SEE
                                                                                                                                          )
                                                                                                                                          :
                                                                                                                                          SailM
                                                                                                                                          Int
                                                                                                                                          )
                                                                                                                                        (pure (((w__2094 <b 2084) : Bool))))
                                                                                                                                    else
                                                                                                                                      (pure false)
                                                                                                                                    )
                                                                                                                                    :
                                                                                                                                    SailM
                                                                                                                                    Bool
                                                                                                                                    )
                                                                                                                                  if (w__2095 : Bool)
                                                                                                                                  then
                                                                                                                                    (do
                                                                                                                                      writeReg SEE 2084
                                                                                                                                      let Zm :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          16
                                                                                                                                          5)
                                                                                                                                      let msz :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          13
                                                                                                                                          2)
                                                                                                                                      let Pg :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          10
                                                                                                                                          3)
                                                                                                                                      let Rn :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          5
                                                                                                                                          5)
                                                                                                                                      let prfop :=
                                                                                                                                        (BitVec.slice
                                                                                                                                          __opcode
                                                                                                                                          0
                                                                                                                                          4)
                                                                                                                                      (decode_PRFD_I_P_BZ_D_64_scaled
                                                                                                                                        Zm
                                                                                                                                        msz
                                                                                                                                        Pg
                                                                                                                                        Rn
                                                                                                                                        prfop)
                                                                                                                                      (pure false))
                                                                                                                                  else
                                                                                                                                    (do
                                                                                                                                      let w__2097 ← (( do
                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 31
                                                                                                                                                 21)) == (0b11000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                 __opcode
                                                                                                                                                 15
                                                                                                                                                 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                        then
                                                                                                                                          (do
                                                                                                                                            let w__2096 ← (( do
                                                                                                                                              readReg SEE
                                                                                                                                              )
                                                                                                                                              :
                                                                                                                                              SailM
                                                                                                                                              Int
                                                                                                                                              )
                                                                                                                                            (pure (((w__2096 <b 2085) : Bool))))
                                                                                                                                        else
                                                                                                                                          (pure false)
                                                                                                                                        )
                                                                                                                                        :
                                                                                                                                        SailM
                                                                                                                                        Bool
                                                                                                                                        )
                                                                                                                                      if (w__2097 : Bool)
                                                                                                                                      then
                                                                                                                                        (do
                                                                                                                                          writeReg SEE 2085
                                                                                                                                          let Zm :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              16
                                                                                                                                              5)
                                                                                                                                          let U :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              14
                                                                                                                                              1)
                                                                                                                                          let ff :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              13
                                                                                                                                              1)
                                                                                                                                          let Pg :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              10
                                                                                                                                              3)
                                                                                                                                          let Rn :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              5
                                                                                                                                              5)
                                                                                                                                          let Zt :=
                                                                                                                                            (BitVec.slice
                                                                                                                                              __opcode
                                                                                                                                              0
                                                                                                                                              5)
                                                                                                                                          (decode_LD1H_Z_P_BZ_D_64_scaled
                                                                                                                                            Zm
                                                                                                                                            U
                                                                                                                                            ff
                                                                                                                                            Pg
                                                                                                                                            Rn
                                                                                                                                            Zt)
                                                                                                                                          (pure false))
                                                                                                                                      else
                                                                                                                                        (do
                                                                                                                                          let w__2099 ← (( do
                                                                                                                                            if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     31
                                                                                                                                                     21)) == (0b11000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                     __opcode
                                                                                                                                                     15
                                                                                                                                                     13)) == (0b100#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                            then
                                                                                                                                              (do
                                                                                                                                                let w__2098 ← (( do
                                                                                                                                                  readReg SEE
                                                                                                                                                  )
                                                                                                                                                  :
                                                                                                                                                  SailM
                                                                                                                                                  Int
                                                                                                                                                  )
                                                                                                                                                (pure (((w__2098 <b 2086) : Bool))))
                                                                                                                                            else
                                                                                                                                              (pure false)
                                                                                                                                            )
                                                                                                                                            :
                                                                                                                                            SailM
                                                                                                                                            Bool
                                                                                                                                            )
                                                                                                                                          if (w__2099 : Bool)
                                                                                                                                          then
                                                                                                                                            (do
                                                                                                                                              writeReg SEE 2086
                                                                                                                                              let Zm :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  16
                                                                                                                                                  5)
                                                                                                                                              let U :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  14
                                                                                                                                                  1)
                                                                                                                                              let ff :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  13
                                                                                                                                                  1)
                                                                                                                                              let Pg :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  10
                                                                                                                                                  3)
                                                                                                                                              let Rn :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  5
                                                                                                                                                  5)
                                                                                                                                              let Zt :=
                                                                                                                                                (BitVec.slice
                                                                                                                                                  __opcode
                                                                                                                                                  0
                                                                                                                                                  5)
                                                                                                                                              (decode_LD1SH_Z_P_BZ_D_64_scaled
                                                                                                                                                Zm
                                                                                                                                                U
                                                                                                                                                ff
                                                                                                                                                Pg
                                                                                                                                                Rn
                                                                                                                                                Zt)
                                                                                                                                              (pure false))
                                                                                                                                          else
                                                                                                                                            (do
                                                                                                                                              let w__2101 ← (( do
                                                                                                                                                if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         31
                                                                                                                                                         21)) == (0b11000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                         __opcode
                                                                                                                                                         15
                                                                                                                                                         13)) == (0b111#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                then
                                                                                                                                                  (do
                                                                                                                                                    let w__2100 ← (( do
                                                                                                                                                      readReg SEE
                                                                                                                                                      )
                                                                                                                                                      :
                                                                                                                                                      SailM
                                                                                                                                                      Int
                                                                                                                                                      )
                                                                                                                                                    (pure (((w__2100 <b 2087) : Bool))))
                                                                                                                                                else
                                                                                                                                                  (pure false)
                                                                                                                                                )
                                                                                                                                                :
                                                                                                                                                SailM
                                                                                                                                                Bool
                                                                                                                                                )
                                                                                                                                              if (w__2101 : Bool)
                                                                                                                                              then
                                                                                                                                                (do
                                                                                                                                                  writeReg SEE 2087
                                                                                                                                                  let Zm :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      16
                                                                                                                                                      5)
                                                                                                                                                  let U :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      14
                                                                                                                                                      1)
                                                                                                                                                  let ff :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      13
                                                                                                                                                      1)
                                                                                                                                                  let Pg :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      10
                                                                                                                                                      3)
                                                                                                                                                  let Rn :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      5
                                                                                                                                                      5)
                                                                                                                                                  let Zt :=
                                                                                                                                                    (BitVec.slice
                                                                                                                                                      __opcode
                                                                                                                                                      0
                                                                                                                                                      5)
                                                                                                                                                  (decode_LDFF1H_Z_P_BZ_D_64_scaled
                                                                                                                                                    Zm
                                                                                                                                                    U
                                                                                                                                                    ff
                                                                                                                                                    Pg
                                                                                                                                                    Rn
                                                                                                                                                    Zt)
                                                                                                                                                  (pure false))
                                                                                                                                              else
                                                                                                                                                (do
                                                                                                                                                  let w__2103 ← (( do
                                                                                                                                                    if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             31
                                                                                                                                                             21)) == (0b11000100111#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                             __opcode
                                                                                                                                                             15
                                                                                                                                                             13)) == (0b101#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                    then
                                                                                                                                                      (do
                                                                                                                                                        let w__2102 ← (( do
                                                                                                                                                          readReg SEE
                                                                                                                                                          )
                                                                                                                                                          :
                                                                                                                                                          SailM
                                                                                                                                                          Int
                                                                                                                                                          )
                                                                                                                                                        (pure (((w__2102 <b 2088) : Bool))))
                                                                                                                                                    else
                                                                                                                                                      (pure false)
                                                                                                                                                    )
                                                                                                                                                    :
                                                                                                                                                    SailM
                                                                                                                                                    Bool
                                                                                                                                                    )
                                                                                                                                                  if (w__2103 : Bool)
                                                                                                                                                  then
                                                                                                                                                    (do
                                                                                                                                                      writeReg SEE 2088
                                                                                                                                                      let Zm :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          16
                                                                                                                                                          5)
                                                                                                                                                      let U :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          14
                                                                                                                                                          1)
                                                                                                                                                      let ff :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          13
                                                                                                                                                          1)
                                                                                                                                                      let Pg :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          10
                                                                                                                                                          3)
                                                                                                                                                      let Rn :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          5
                                                                                                                                                          5)
                                                                                                                                                      let Zt :=
                                                                                                                                                        (BitVec.slice
                                                                                                                                                          __opcode
                                                                                                                                                          0
                                                                                                                                                          5)
                                                                                                                                                      (decode_LDFF1SH_Z_P_BZ_D_64_scaled
                                                                                                                                                        Zm
                                                                                                                                                        U
                                                                                                                                                        ff
                                                                                                                                                        Pg
                                                                                                                                                        Rn
                                                                                                                                                        Zt)
                                                                                                                                                      (pure false))
                                                                                                                                                  else
                                                                                                                                                    (do
                                                                                                                                                      let w__2105 ← (( do
                                                                                                                                                        if (((((Sail.BitVec.castWidth (m := 11) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 31
                                                                                                                                                                 21)) == (0b11000101011#11 : (BitVec 11))) && ((Sail.BitVec.castWidth (m := 3) (Sail.BitVec.extractLsb
                                                                                                                                                                 __opcode
                                                                                                                                                                 15
                                                                                                                                                                 13)) == (0b110#3 : (BitVec 3)))) : Bool) : Bool)
                                                                                                                                                        then
                                                                                                                                                          (do
                                                                                                                                                            let w__2104 ← (( do
                                                                                                                                                              readReg SEE
                                                                                                                                                              )
                                                                                                                                                              :
                                                                                                                                                              SailM
                                                                                                                                                              Int
                                                                                                                                                              )
                                                                                                                                                            (pure (((w__2104 <b 2089) : Bool))))
                                                                                                                                                        else
                                                                                                                                                          (pure false)
                                                                                                                                                        )
                                                                                                                                                        :
                                                                                                                                                        SailM
                                                                                                                                                        Bool
                                                                                                                                                        )
                                                                                                                                                      if (w__2105 : Bool)
                                                                                                                                                      then
                                                                                                                                                        (do
                                                                                                                                                          writeReg SEE 2089
                                                                                                                                                          let Zm :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              16
                                                                                                                                                              5)
                                                                                                                                                          let U :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              14
                                                                                                                                                              1)
                                                                                                                                                          let ff :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              13
                                                                                                                                                              1)
                                                                                                                                                          let Pg :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              10
                                                                                                                                                              3)
                                                                                                                                                          let Rn :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              5
                                                                                                                                                              5)
                                                                                                                                                          let Zt :=
                                                                                                                                                            (BitVec.slice
                                                                                                                                                              __opcode
                                                                                                                                                              0
                                                                                                                                                              5)
                                                                                                                                                          (decode_LD1W_Z_P_BZ_D_64_scaled
                                                                                                                                                            Zm
                                                                                                                                                            U
                                                                                                                                                            ff
                                                                                                                                                            Pg
                                                                                                                                                            Rn
                                                                                                                                                            Zt)
                                                                                                                                                          (pure false))
                                                                                                                                                      else
                                                                                                                                                        (pure true))))))))))))))))))))))))))))))))))))))


end ArmFull.Functions
