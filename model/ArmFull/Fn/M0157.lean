module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1
public import ArmFull.AbstractReal
public import ArmFull.ArmExtrasFork
public import ArmFull.Fn.M0000
public import ArmFull.Fn.M0016
public import ArmFull.Fn.M0036
public import ArmFull.Fn.M0056
public import ArmFull.Fn.M0087
public import ArmFull.Fn.M0144 set_option backward.proofsInPublic true @[expose] public section

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

/-- Type quantifiers: k_cold : Bool -/
def AArch64_AutoGen_ArchitectureReset__seg3 (cold : Bool) : SailM Bool := do
  let w__1094 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1093 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1093) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1094 : Bool)
  then
    (do
      let w__1095 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1095 14 14 0#1))
  else
    (do
      let w__1096 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1097 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1096 14 14 w__1097))
  let w__1099 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1098 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1098) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1099 : Bool)
  then
    (do
      let w__1100 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1100 13 13 0#1))
  else
    (do
      let w__1101 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1102 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1101 13 13 w__1102))
  let w__1104 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1103 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1103) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1104 : Bool)
  then
    (do
      let w__1105 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1105 12 12 0#1))
  else
    (do
      let w__1106 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1107 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1106 12 12 w__1107))
  let w__1109 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1108 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1108) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1109 : Bool)
  then
    (do
      let w__1110 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1110 11 11 0#1))
  else
    (do
      let w__1111 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1112 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1111 11 11 w__1112))
  let w__1114 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1113 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1113) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1114 : Bool)
  then
    (do
      let w__1115 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1115 10 10 0#1))
  else
    (do
      let w__1116 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1117 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1116 10 10 w__1117))
  let w__1119 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1118 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1118) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1119 : Bool)
  then
    (do
      let w__1120 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1120 9 9 0#1))
  else
    (do
      let w__1121 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1122 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1121 9 9 w__1122))
  let w__1124 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1123 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1123) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1124 : Bool)
  then
    (do
      let w__1125 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1125 8 8 0#1))
  else
    (do
      let w__1126 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1127 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1126 8 8 w__1127))
  let w__1129 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1128 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1128) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1129 : Bool)
  then
    (do
      let w__1130 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1130 7 7 0#1))
  else
    (do
      let w__1131 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1132 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1131 7 7 w__1132))
  let w__1134 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1133 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1133) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1134 : Bool)
  then
    (do
      let w__1135 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1135 6 6 0#1))
  else
    (do
      let w__1136 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1137 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1136 6 6 w__1137))
  let w__1139 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1138 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1138) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1139 : Bool)
  then
    (do
      let w__1140 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1140 5 5 0#1))
  else
    (do
      let w__1141 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1142 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1141 5 5 w__1142))
  let w__1144 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1143 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1143) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1144 : Bool)
  then
    (do
      let w__1145 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1145 4 4 0#1))
  else
    (do
      let w__1146 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1147 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1146 4 4 w__1147))
  let w__1149 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1148 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1148) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1149 : Bool)
  then
    (do
      let w__1150 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1150 3 3 0#1))
  else
    (do
      let w__1151 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1152 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1151 3 3 w__1152))
  let w__1154 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1153 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1153) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1154 : Bool)
  then
    (do
      let w__1155 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1155 2 2 0#1))
  else
    (do
      let w__1156 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1157 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1156 2 2 w__1157))
  let w__1159 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1158 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1158) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1159 : Bool)
  then
    (do
      let w__1160 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1160 1 1 0#1))
  else
    (do
      let w__1161 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1162 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1161 1 1 w__1162))
  let w__1164 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1163 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1163) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1164 : Bool)
  then
    (do
      let w__1165 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1165 0 0 0#1))
  else
    (do
      let w__1166 ← (( do readReg HDFGRTR2_EL2 ) : SailM (BitVec 64) )
      let w__1167 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HDFGRTR2_EL2 (Sail.BitVec.updateSubrange w__1166 0 0 w__1167))
  let w__1168 ← (( do readReg DBGPRCR_EL1 ) : SailM (BitVec 64) )
  writeReg DBGPRCR_EL1 (Sail.BitVec.updateSubrange w__1168 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1169 ← (( do readReg PMCNTENCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENCLR_EL0 (Sail.BitVec.updateSubrange w__1169 63 33
    0b0000000000000000000000000000000#31)
  let w__1170 ← (( do readReg PMCNTENCLR_EL0 ) : SailM (BitVec 64) )
  writeReg PMCNTENCLR_EL0 (BitVec.update w__1170 32 (Bit 0#1))
  let w__1171 ← (( do (SDER32_EL3_read ()) ) : SailM (BitVec 64) )
  (SDER32_EL3_write
    (Mk_SDER32_EL3_Type
      (set_slice 62 w__1171 2 0b00000000000000000000000000000000000000000000000000000000000000#62)))
  let w__1172 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
  writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__1172 62 48 0b000000000000000#15)
  let w__1173 ← (( do readReg HPFAR_EL2 ) : SailM (BitVec 64) )
  writeReg HPFAR_EL2 (Sail.BitVec.updateSubrange w__1173 3 0 0b0000#4)
  let w__1174 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__1174 63 40 0b000000000000000000000000#24)
  let w__1175 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (BitVec.update w__1175 31 (Bit 1#1))
  let w__1176 ← (( do readReg VMPIDR_EL2 ) : SailM (BitVec 64) )
  writeReg VMPIDR_EL2 (Sail.BitVec.updateSubrange w__1176 29 25 0b00000#5)
  let w__1177 ← (( do readReg ID_AA64MMFR3_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AA64MMFR3_EL1 (Sail.BitVec.updateSubrange w__1177 51 48 0b0000#4)
  let w__1178 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__1178 63 32
    0b00000000000000000000000000000000#32)
  let w__1179 ← (( do readReg ICH_VTR_EL2 ) : SailM (BitVec 64) )
  writeReg ICH_VTR_EL2 (Sail.BitVec.updateSubrange w__1179 17 5 0b0000000000000#13)
  let w__1180 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__1180 63 32
    0b00000000000000000000000000000000#32)
  let w__1181 ← (( do readReg ID_PFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_PFR1_EL1 (Sail.BitVec.updateSubrange w__1181 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1182 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange w__1182 63 6
    0b0000000000000000000000000000000000000000000000000000000000#58)
  let w__1183 ← (( do readReg MDSELR_EL1 ) : SailM (BitVec 64) )
  writeReg MDSELR_EL1 (Sail.BitVec.updateSubrange w__1183 3 0 0b0000#4)
  let w__1184 ← (( do readReg ICV_EOIR0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_EOIR0_EL1 (Sail.BitVec.updateSubrange w__1184 63 24
    0b0000000000000000000000000000000000000000#40)
  let w__1185 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__1185 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1186 ← (( do readReg ID_DFR1_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR1_EL1 (Sail.BitVec.updateSubrange w__1186 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1187 ← (( do readReg VBAR_EL3 ) : SailM (BitVec 64) )
  writeReg VBAR_EL3 (Sail.BitVec.updateSubrange w__1187 10 0 0b00000000000#11)
  let w__1188 ← (( do readReg ID_AFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AFR0_EL1 (Sail.BitVec.updateSubrange w__1188 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1189 ← (( do readReg ID_AFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_AFR0_EL1 (Sail.BitVec.updateSubrange w__1189 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1190 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1190 63 44 0b00000000000000000000#20)
  let w__1192 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1191 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1191) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1192 : Bool)
  then
    (do
      let w__1193 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1193 43 43 0#1))
  else
    (do
      let w__1194 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      let w__1195 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1194 43 43 w__1195))
  let w__1196 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (BitVec.update w__1196 42 (Bit 0#1))
  let w__1197 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1197 39 37 0b000#3)
  let w__1198 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1198 35 32 0b0000#4)
  let w__1200 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1199 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1199) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1200 : Bool)
  then
    (do
      let w__1201 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1201 31 30 0b00#2))
  else
    (do
      let w__1202 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      let w__1203 ← (( do (__UNKNOWN_bits 2) ) : SailM (BitVec 2) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1202 31 30 w__1203))
  if (cold : Bool)
  then
    (do
      let w__1204 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
      writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1204 28 28 1#1))
  else (pure (()))
  let w__1205 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1205 25 24 0b00#2)
  let w__1206 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1206 23 23 0#1)
  let w__1207 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1207 22 20 0b000#3)
  let w__1208 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (BitVec.update w__1208 18 (Bit 0#1))
  let w__1209 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (Sail.BitVec.updateSubrange w__1209 17 17 0#1)
  let w__1210 ← (( do readReg MDCR_EL2 ) : SailM (BitVec 64) )
  writeReg MDCR_EL2 (BitVec.update w__1210 16 (Bit 0#1))
  let w__1211 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTKCTL_EL1 (Sail.BitVec.updateSubrange w__1211 63 18
    0b0000000000000000000000000000000000000000000000#46)
  let w__1212 ← (( do readReg CNTKCTL_EL1 ) : SailM (BitVec 64) )
  writeReg CNTKCTL_EL1 (Sail.BitVec.updateSubrange w__1212 16 10 0b0000000#7)
  let w__1213 ← (( do readReg LORN_EL1 ) : SailM (BitVec 64) )
  writeReg LORN_EL1 (Sail.BitVec.updateSubrange w__1213 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1214 ← (( do readReg ICV_IGRPEN0_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN0_EL1 (Sail.BitVec.updateSubrange w__1214 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1215 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__1215 63 34 0b000000000000000000000000000000#30)
  let w__1216 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (BitVec.update w__1216 32 (Bit 0#1))
  let w__1217 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__1217 63 35 0b00000000000000000000000000000#29)
  let w__1218 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__1218 27 26 0b00#2)
  let w__1219 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (Sail.BitVec.updateSubrange w__1219 19 14 0b000000#6)
  let w__1220 ← (( do readReg SPSR_EL3 ) : SailM (BitVec 64) )
  writeReg SPSR_EL3 (BitVec.update w__1220 5 (Bit 0#1))
  let w__1221 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__1221 63 56 0b00000000#8)
  let w__1222 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__1222 31 24 0b00000000#8)
  let w__1223 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__1223 63 32
    0b00000000000000000000000000000000#32)
  let w__1224 ← (( do readReg CCSIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CCSIDR_EL1 (Sail.BitVec.updateSubrange w__1224 31 28 0b0000#4)
  let w__1225 ← (( do readReg VMECID_P_EL2 ) : SailM (BitVec 64) )
  writeReg VMECID_P_EL2 (Sail.BitVec.updateSubrange w__1225 63 16
    0b000000000000000000000000000000000000000000000000#48)
  let w__1226 ← (( do readReg OSECCR_EL1 ) : SailM (BitVec 64) )
  writeReg OSECCR_EL1 (Sail.BitVec.updateSubrange w__1226 63 32
    0b00000000000000000000000000000000#32)
  let w__1227 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange w__1227 63 32
    0b00000000000000000000000000000000#32)
  let w__1228 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__1228 29 (Bit 0#1))
  let w__1229 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange w__1229 24 8 0b00000000000000000#17)
  let w__1230 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__1230 5 (Bit 0#1))
  let w__1231 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__1231 0 (Bit 0#1))
  let w__1232 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (Sail.BitVec.updateSubrange w__1232 63 8
    0b00000000000000000000000000000000000000000000000000000000#56)
  let w__1233 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__1233 5 (Bit 0#1))
  let w__1234 ← (( do readReg DBGVCR32_EL2 ) : SailM (BitVec 64) )
  writeReg DBGVCR32_EL2 (BitVec.update w__1234 0 (Bit 0#1))
  let w__1235 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1235 63 63 0#1)
  let w__1236 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1236 62 62 0#1)
  let w__1237 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1237 61 61 0#1)
  let w__1238 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1238 60 60 0#1)
  let w__1239 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1239 59 59 0#1)
  let w__1240 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1240 58 58 0#1)
  let w__1241 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1241 57 57 0#1)
  let w__1242 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1242 56 56 0#1)
  let w__1243 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1243 55 55 0#1)
  let w__1244 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1244 54 54 0#1)
  let w__1245 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1245 53 53 0#1)
  let w__1246 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1246 52 52 0#1)
  let w__1247 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (BitVec.update w__1247 51 (Bit 0#1))
  let w__1248 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1248 50 50 0#1)
  let w__1250 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1249 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1249) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1250 : Bool)
  then
    (do
      let w__1251 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1251 49 49 0#1))
  else
    (do
      let w__1252 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1253 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1252 49 49 w__1253))
  let w__1255 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1254 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1254) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1255 : Bool)
  then
    (do
      let w__1256 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1256 48 48 0#1))
  else
    (do
      let w__1257 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1258 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1257 48 48 w__1258))
  let w__1260 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1259 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1259) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1260 : Bool)
  then
    (do
      let w__1261 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1261 47 47 0#1))
  else
    (do
      let w__1262 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1263 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1262 47 47 w__1263))
  let w__1265 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1264 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1264) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1265 : Bool)
  then
    (do
      let w__1266 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1266 46 46 0#1))
  else
    (do
      let w__1267 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1268 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1267 46 46 w__1268))
  let w__1270 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1269 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1269) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1270 : Bool)
  then
    (do
      let w__1271 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1271 45 45 0#1))
  else
    (do
      let w__1272 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1273 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1272 45 45 w__1273))
  let w__1275 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1274 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1274) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1275 : Bool)
  then
    (do
      let w__1276 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1276 44 44 0#1))
  else
    (do
      let w__1277 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1278 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1277 44 44 w__1278))
  let w__1280 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1279 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1279) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1280 : Bool)
  then
    (do
      let w__1281 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1281 43 43 0#1))
  else
    (do
      let w__1282 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1283 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1282 43 43 w__1283))
  let w__1285 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1284 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1284) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1285 : Bool)
  then
    (do
      let w__1286 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1286 42 42 0#1))
  else
    (do
      let w__1287 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1288 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1287 42 42 w__1288))
  let w__1290 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1289 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1289) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1290 : Bool)
  then
    (do
      let w__1291 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1291 41 41 0#1))
  else
    (do
      let w__1292 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1293 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1292 41 41 w__1293))
  let w__1295 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1294 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1294) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1295 : Bool)
  then
    (do
      let w__1296 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1296 40 40 0#1))
  else
    (do
      let w__1297 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
      let w__1298 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1297 40 40 w__1298))
  let w__1299 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1299 39 39 0#1)
  let w__1300 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1300 38 38 0#1)
  let w__1301 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1301 37 37 0#1)
  let w__1302 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1302 36 36 0#1)
  let w__1303 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1303 35 35 0#1)
  let w__1304 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1304 34 34 0#1)
  let w__1305 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1305 33 33 0#1)
  let w__1306 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1306 32 32 0#1)
  let w__1307 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1307 31 31 0#1)
  let w__1308 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1308 30 30 0#1)
  let w__1309 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1309 29 29 0#1)
  let w__1310 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1310 28 28 0#1)
  let w__1311 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1311 27 27 0#1)
  let w__1312 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1312 26 26 0#1)
  let w__1313 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1313 25 25 0#1)
  let w__1314 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1314 24 24 0#1)
  let w__1315 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1315 23 23 0#1)
  let w__1316 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1316 22 22 0#1)
  let w__1317 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1317 21 21 0#1)
  let w__1318 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1318 20 20 0#1)
  let w__1319 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1319 19 19 0#1)
  let w__1320 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1320 18 18 0#1)
  let w__1321 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1321 17 17 0#1)
  let w__1322 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1322 16 16 0#1)
  let w__1323 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1323 15 15 0#1)
  let w__1324 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1324 14 14 0#1)
  let w__1325 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1325 13 13 0#1)
  let w__1326 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1326 12 12 0#1)
  let w__1327 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1327 11 11 0#1)
  let w__1328 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1328 10 10 0#1)
  let w__1329 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1329 9 9 0#1)
  let w__1330 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1330 8 8 0#1)
  let w__1331 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1331 7 7 0#1)
  let w__1332 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1332 6 6 0#1)
  let w__1333 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1333 5 5 0#1)
  let w__1334 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1334 4 4 0#1)
  let w__1335 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1335 3 3 0#1)
  let w__1336 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1336 2 2 0#1)
  let w__1337 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1337 1 1 0#1)
  let w__1338 ← (( do readReg HFGRTR_EL2 ) : SailM (BitVec 64) )
  writeReg HFGRTR_EL2 (Sail.BitVec.updateSubrange w__1338 0 0 0#1)
  let w__1339 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__1339 63 32
    0b00000000000000000000000000000000#32)
  let w__1340 ← (( do readReg ID_DFR0_EL1 ) : SailM (BitVec 64) )
  writeReg ID_DFR0_EL1 (Sail.BitVec.updateSubrange w__1340 63 0
    0b0000000000000000000000000000000000000000000000000000000000000000#64)
  let w__1341 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1341 63 32 0b00000000000000000000000000000000#32)
  let w__1342 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1342 27 26 0b00#2)
  let w__1343 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1343 23 22 0b00#2)
  let w__1344 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1344 19 18 0b00#2)
  let w__1345 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1345 15 0 0b0000000000000000#16)
  let w__1346 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1346 63 32 0b00000000000000000000000000000000#32)
  let w__1347 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1347 29 21 0b000000000#9)
  let w__1348 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1348 19 14 0b000000#6)
  let w__1349 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (BitVec.update w__1349 13 (Bit 1#1))
  let w__1350 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (BitVec.update w__1350 11 (Bit 0#1))
  let w__1351 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (BitVec.update w__1351 9 (Bit 1#1))
  let w__1352 ← (( do readReg CPTR_EL2 ) : SailM (BitVec 64) )
  writeReg CPTR_EL2 (Sail.BitVec.updateSubrange w__1352 7 0 0b11111111#8)
  let w__1353 ← (( do readReg CLIDR_EL1 ) : SailM (BitVec 64) )
  writeReg CLIDR_EL1 (Sail.BitVec.updateSubrange w__1353 63 47 0b00000000000000000#17)
  let w__1354 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1354 63 23
    0b00000000000000000000000000000000000000000#41)
  let w__1356 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1355 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1355) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1356 : Bool)
  then
    (do
      let w__1357 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1357 22 22 0#1))
  else
    (do
      let w__1358 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1359 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1358 22 22 w__1359))
  let w__1361 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1360 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1360) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1361 : Bool)
  then
    (do
      let w__1362 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1362 20 20 0#1))
  else
    (do
      let w__1363 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1364 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1363 20 20 w__1364))
  let w__1366 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1365 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1365) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1366 : Bool)
  then
    (do
      let w__1367 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1367 19 19 0#1))
  else
    (do
      let w__1368 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1369 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1368 19 19 w__1369))
  let w__1371 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1370 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1370) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1371 : Bool)
  then
    (do
      let w__1372 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1372 18 18 0#1))
  else
    (do
      let w__1373 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1374 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1373 18 18 w__1374))
  let w__1376 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1375 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1375) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1376 : Bool)
  then
    (do
      let w__1377 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1377 17 17 0#1))
  else
    (do
      let w__1378 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1379 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1378 17 17 w__1379))
  let w__1381 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1380 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1380) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1381 : Bool)
  then
    (do
      let w__1382 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1382 15 15 0#1))
  else
    (do
      let w__1383 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1384 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1383 15 15 w__1384))
  let w__1386 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1385 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1385) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1386 : Bool)
  then
    (do
      let w__1387 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1387 14 14 0#1))
  else
    (do
      let w__1388 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1389 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1388 14 14 w__1389))
  let w__1390 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
  writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1390 13 12 0b00#2)
  let w__1392 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1391 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1391) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1392 : Bool)
  then
    (do
      let w__1393 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1393 11 11 0#1))
  else
    (do
      let w__1394 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1395 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1394 11 11 w__1395))
  let w__1397 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1396 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1396) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1397 : Bool)
  then
    (do
      let w__1398 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1398 10 10 0#1))
  else
    (do
      let w__1399 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1400 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1399 10 10 w__1400))
  let w__1402 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1401 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1401) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1402 : Bool)
  then
    (do
      let w__1403 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1403 9 9 0#1))
  else
    (do
      let w__1404 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1405 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1404 9 9 w__1405))
  let w__1407 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1406 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1406) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1407 : Bool)
  then
    (do
      let w__1408 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1408 8 8 0#1))
  else
    (do
      let w__1409 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1410 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1409 8 8 w__1410))
  let w__1412 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1411 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1411) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1412 : Bool)
  then
    (do
      let w__1413 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1413 7 7 0#1))
  else
    (do
      let w__1414 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1415 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1414 7 7 w__1415))
  let w__1417 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1416 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1416) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1417 : Bool)
  then
    (do
      let w__1418 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1418 6 6 0#1))
  else
    (do
      let w__1419 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1420 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1419 6 6 w__1420))
  let w__1422 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1421 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1421) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1422 : Bool)
  then
    (do
      let w__1423 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1423 5 5 0#1))
  else
    (do
      let w__1424 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1425 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1424 5 5 w__1425))
  let w__1427 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1426 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1426) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1427 : Bool)
  then
    (do
      let w__1428 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1428 4 4 0#1))
  else
    (do
      let w__1429 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1430 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1429 4 4 w__1430))
  let w__1432 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1431 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1431) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1432 : Bool)
  then
    (do
      let w__1433 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1433 3 3 0#1))
  else
    (do
      let w__1434 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1435 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1434 3 3 w__1435))
  let w__1437 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1436 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1436) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1437 : Bool)
  then
    (do
      let w__1438 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1438 2 2 0#1))
  else
    (do
      let w__1439 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1440 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1439 2 2 w__1440))
  let w__1442 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1441 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1441) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1442 : Bool)
  then
    (do
      let w__1443 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1443 1 1 0#1))
  else
    (do
      let w__1444 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1445 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1444 1 1 w__1445))
  let w__1447 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1446 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1446) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1447 : Bool)
  then
    (do
      let w__1448 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1448 0 0 0#1))
  else
    (do
      let w__1449 ← (( do readReg HCRX_EL2 ) : SailM (BitVec 64) )
      let w__1450 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HCRX_EL2 (Sail.BitVec.updateSubrange w__1449 0 0 w__1450))
  let w__1451 ← (( do readReg ICV_IGRPEN1_EL1 ) : SailM (BitVec 64) )
  writeReg ICV_IGRPEN1_EL1 (Sail.BitVec.updateSubrange w__1451 63 1
    0b000000000000000000000000000000000000000000000000000000000000000#63)
  let w__1452 ← (( do readReg PMXEVCNTR_EL0 ) : SailM (BitVec 64) )
  writeReg PMXEVCNTR_EL0 (Sail.BitVec.updateSubrange w__1452 63 32
    0b00000000000000000000000000000000#32)
  let w__1453 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1453 63 3
    0b0000000000000000000000000000000000000000000000000000000000000#61)
  let w__1455 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1454 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1454) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1455 : Bool)
  then
    (do
      let w__1456 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1456 2 2 0#1))
  else
    (do
      let w__1457 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__1458 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1457 2 2 w__1458))
  let w__1459 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
  writeReg HFGWTR2_EL2 (BitVec.update w__1459 1 (Bit 0#1))
  let w__1461 ← (( do
    if (((! cold) : Bool) : Bool)
    then
      (do
        let w__1460 ← (( do (HaveEL EL3) ) : SailM Bool )
        (pure (((! w__1460) : Bool))))
    else (pure false) ) : SailM Bool )
  if (w__1461 : Bool)
  then
    (do
      let w__1462 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1462 0 0 0#1))
  else
    (do
      let w__1463 ← (( do readReg HFGWTR2_EL2 ) : SailM (BitVec 64) )
      let w__1464 ← (( do (__UNKNOWN_bits 1) ) : SailM (BitVec 1) )
      writeReg HFGWTR2_EL2 (Sail.BitVec.updateSubrange w__1463 0 0 w__1464))
  (pure true)


end ArmFull.Functions
