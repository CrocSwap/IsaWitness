module public import Sail
public import ArmFull.Defs
public import ArmFull.SpecializationV1 set_option backward.proofsInPublic true @[expose] public section

open Sail ArmFull

abbrev sign_extend {w : Nat} (x : BitVec w) (w' : Nat) := Sail.BitVec.signExtend x w'

def dec_str (x : Int) := x.repr
def hex_str (x : Int) := x.toHex

def putchar (_ : Int) : Unit := ()

def sleep_request (_ : Unit) : SailM Unit := pure ()
def wakeup_request (_ : Unit) : SailM Unit := pure ()
meta section
macro_rules | `(tactic| decreasing_trivial) => `(tactic|
  first
  | grind
  | decide)
