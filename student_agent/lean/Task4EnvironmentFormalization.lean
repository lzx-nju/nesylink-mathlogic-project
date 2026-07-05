/-
  Environment formalization for `mathematical_logic/task_4`.

  This file models the task-4 environment layer that is most useful for the
  course report:

  * room-level navigation;
  * the rotating bridge in the center room;
  * the locked east exit that requires a key but does not consume it;
  * the north chest that grants a key;
  * the east chest that grants a sword;
  * the south guardian whose defeat reveals the final chest;
  * the final chest as the task completion condition.

  It intentionally abstracts away pixel motion, monster AI, knockback and HUD
  rendering. Those details exist in the Python engine, but the report's
  environment-formalization section only needs the symbolic transition layer that
  the planner and proofs rely on.

  Python correspondence:
  * `nesylink/core/mechanics/movement.py`
  * `nesylink/core/mechanics/interactions.py`
  * `nesylink/core/mechanics/combat.py`
  * `nesylink/map_data/mathematical_logic/task_4/*.json`
-/

namespace Task4EnvironmentFormalization

inductive Room where
  | west
  | center
  | north
  | east
  | south
  deriving DecidableEq, Repr

inductive BridgeState where
  | westToNorth
  | westToEast
  | westToSouth
  deriving DecidableEq, Repr

inductive Action where
  | toggleBridge
  | goCenter
  | goWest
  | goNorth
  | goEast
  | goSouth
  | openChest
  | attack
  | openFinalChest
  | wait
  deriving DecidableEq, Repr

structure EnvState where
  room : Room
  bridge : BridgeState
  keys : Nat
  hasShield : Bool
  hasSword : Bool
  northChestOpened : Bool
  eastChestOpened : Bool
  guardianAlive : Bool
  finalChestVisible : Bool
  finalChestOpened : Bool
  deriving DecidableEq, Repr

def initialState : EnvState :=
  {
    room := Room.west
    bridge := BridgeState.westToNorth
    keys := 0
    hasShield := true
    hasSword := false
    northChestOpened := false
    eastChestOpened := false
    guardianAlive := true
    finalChestVisible := false
    finalChestOpened := false
  }

def rotateBridge : BridgeState → BridgeState
  | BridgeState.westToNorth => BridgeState.westToEast
  | BridgeState.westToEast => BridgeState.westToSouth
  | BridgeState.westToSouth => BridgeState.westToNorth

def bridgeAllowsNorth (b : BridgeState) : Prop :=
  b = BridgeState.westToNorth

def bridgeAllowsEast (b : BridgeState) : Prop :=
  b = BridgeState.westToEast

def bridgeAllowsSouth (b : BridgeState) : Prop :=
  b = BridgeState.westToSouth

def hasKey (s : EnvState) : Prop :=
  s.keys > 0

instance (b : BridgeState) : Decidable (bridgeAllowsNorth b) :=
  inferInstanceAs (Decidable (b = BridgeState.westToNorth))

instance (b : BridgeState) : Decidable (bridgeAllowsEast b) :=
  inferInstanceAs (Decidable (b = BridgeState.westToEast))

instance (b : BridgeState) : Decidable (bridgeAllowsSouth b) :=
  inferInstanceAs (Decidable (b = BridgeState.westToSouth))

instance (s : EnvState) : Decidable (hasKey s) :=
  inferInstanceAs (Decidable (s.keys > 0))

def GoalReached (s : EnvState) : Prop :=
  s.finalChestOpened = true

def step (s : EnvState) : Action → EnvState
  | Action.toggleBridge =>
      if s.room = Room.west then
        { s with bridge := rotateBridge s.bridge }
      else
        s
  | Action.goCenter =>
      if s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south then
        { s with room := Room.center }
      else
        s
  | Action.goWest =>
      if s.room = Room.center then
        { s with room := Room.west }
      else
        s
  | Action.goNorth =>
      if s.room = Room.center ∧ bridgeAllowsNorth s.bridge then
        { s with room := Room.north }
      else
        s
  | Action.goEast =>
      if s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s then
        { s with room := Room.east }
      else
        s
  | Action.goSouth =>
      if s.room = Room.center ∧ bridgeAllowsSouth s.bridge then
        { s with room := Room.south }
      else
        s
  | Action.openChest =>
      if s.room = Room.north ∧ s.northChestOpened = false then
        { s with northChestOpened := true, keys := s.keys + 1 }
      else if s.room = Room.east ∧ s.eastChestOpened = false then
        { s with eastChestOpened := true, hasSword := true }
      else
        s
  | Action.attack =>
      if s.room = Room.south ∧ s.guardianAlive = true ∧ s.hasSword = true then
        { s with guardianAlive := false, finalChestVisible := true }
      else
        s
  | Action.openFinalChest =>
      if s.room = Room.center ∧ s.finalChestVisible = true then
        { s with finalChestOpened := true }
      else
        s
  | Action.wait => s

def run : EnvState → List Action → EnvState
  | s, [] => s
  | s, a :: rest => run (step s a) rest

theorem rotateBridge_three_cycle :
    rotateBridge (rotateBridge (rotateBridge BridgeState.westToNorth)) =
      BridgeState.westToNorth := by
  rfl

theorem goEast_blocked_without_key
    {s : EnvState}
    (hRoom : s.room = Room.center)
    (hBridge : s.bridge = BridgeState.westToEast)
    (hKeys : s.keys = 0) :
    step s Action.goEast = s := by
  simp [step, hRoom, hBridge, bridgeAllowsEast, hasKey, hKeys]

theorem goEast_succeeds_with_key
    {s : EnvState}
    (hRoom : s.room = Room.center)
    (hBridge : s.bridge = BridgeState.westToEast)
    (hKeys : s.keys > 0) :
    (step s Action.goEast).room = Room.east := by
  simp [step, hRoom, hBridge, bridgeAllowsEast, hasKey, hKeys]

theorem attack_without_sword_has_no_effect
    {s : EnvState}
    (hRoom : s.room = Room.south)
    (hGuardian : s.guardianAlive = true)
    (hSword : s.hasSword = false) :
    step s Action.attack = s := by
  simp [step, hRoom, hGuardian, hSword]

theorem attack_with_sword_reveals_final_chest
    {s : EnvState}
    (hRoom : s.room = Room.south)
    (hGuardian : s.guardianAlive = true)
    (hSword : s.hasSword = true) :
    let t := step s Action.attack
    t.guardianAlive = false ∧ t.finalChestVisible = true := by
  simp [step, hRoom, hGuardian, hSword]

theorem openFinalChest_requires_visibility
    {s : EnvState}
    (hRoom : s.room = Room.center)
    (hVisible : s.finalChestVisible = false) :
    step s Action.openFinalChest = s := by
  simp [step, hRoom, hVisible]

def witnessPlan : List Action :=
  [
    Action.goCenter,
    Action.goNorth,
    Action.openChest,
    Action.goCenter,
    Action.goWest,
    Action.toggleBridge,
    Action.goCenter,
    Action.goEast,
    Action.openChest,
    Action.goCenter,
    Action.goWest,
    Action.toggleBridge,
    Action.goCenter,
    Action.goSouth,
    Action.attack,
    Action.goCenter,
    Action.openFinalChest
  ]

def finalState : EnvState :=
  {
    room := Room.center
    bridge := BridgeState.westToSouth
    keys := 1
    hasShield := true
    hasSword := true
    northChestOpened := true
    eastChestOpened := true
    guardianAlive := false
    finalChestVisible := true
    finalChestOpened := true
  }

theorem witnessPlan_executes_to_finalState :
    run initialState witnessPlan = finalState := by
  rfl

theorem witnessPlan_reaches_goal :
    GoalReached (run initialState witnessPlan) := by
  simp [GoalReached, witnessPlan_executes_to_finalState, finalState]

theorem task4_completable :
    ∃ plan, GoalReached (run initialState plan) := by
  exact ⟨witnessPlan, witnessPlan_reaches_goal⟩

end Task4EnvironmentFormalization
