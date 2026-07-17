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

namespace Task4Formalization

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

theorem openFinalChest_blocked_not_in_center
    {s : EnvState} (hRoom : s.room ≠ Room.center) :
    step s Action.openFinalChest = s := by
  simp [step, hRoom]

theorem openFinalChest_succeeds_when_visible
    {s : EnvState}
    (hRoom : s.room = Room.center)
    (hVisible : s.finalChestVisible = true) :
    (step s Action.openFinalChest).finalChestOpened = true := by
  simp [step, hRoom, hVisible]

/-! ### toggleBridge lemmas -/

theorem toggleBridge_only_in_west
    {s : EnvState} (hRoom : s.room ≠ Room.west) :
    step s Action.toggleBridge = s := by
  simp [step, hRoom]

/-! ### Navigation lemmas -/

/-- `goEast` does NOT consume keys (Python conditional exit behavior).
    This is an explicit invariant per project convention. -/
theorem goEast_preserves_keys
    {s : EnvState} : (step s Action.goEast).keys = s.keys := by
  by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
  · simp [step, h1]
  · simp [step, h1]

/-! ### Chest lemmas (north and east independent) -/

theorem openChest_north_only
    {s : EnvState}
    (hRoom : s.room ≠ Room.north)
    (hRoom' : s.room ≠ Room.east) :
    step s Action.openChest = s := by
  show (if s.room = Room.north ∧ s.northChestOpened = false then
        { s with northChestOpened := true, keys := s.keys + 1 }
       else if s.room = Room.east ∧ s.eastChestOpened = false then
        { s with eastChestOpened := true, hasSword := true }
       else s) = s
  by_cases h1 : s.room = Room.north ∧ s.northChestOpened = false
  · exact absurd h1.1 hRoom
  · by_cases h2 : s.room = Room.east ∧ s.eastChestOpened = false
    · exact absurd h2.1 hRoom'
    · simp [h1, h2]

theorem openChest_north_increases_keys
    {s : EnvState}
    (hRoom : s.room = Room.north)
    (hChest : s.northChestOpened = false) :
    (step s Action.openChest).keys = s.keys + 1 := by
  simp [step, hRoom, hChest]

theorem openChest_north_marks_opened
    {s : EnvState}
    (hRoom : s.room = Room.north)
    (hChest : s.northChestOpened = false) :
    (step s Action.openChest).northChestOpened = true := by
  simp [step, hRoom, hChest]

theorem openChest_north_already_opened
    {s : EnvState}
    (hRoom : s.room = Room.north)
    (hChest : s.northChestOpened = true) :
    step s Action.openChest = s := by
  simp [step, hRoom, hChest]

theorem openChest_east_grants_sword
    {s : EnvState}
    (hRoom : s.room = Room.east)
    (hChest : s.eastChestOpened = false) :
    (step s Action.openChest).hasSword = true := by
  have hNorth : ¬(s.room = Room.north ∧ s.northChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom, hChest]

theorem openChest_east_marks_opened
    {s : EnvState}
    (hRoom : s.room = Room.east)
    (hChest : s.eastChestOpened = false) :
    (step s Action.openChest).eastChestOpened = true := by
  have hNorth : ¬(s.room = Room.north ∧ s.northChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom, hChest]

theorem openChest_east_already_opened
    {s : EnvState}
    (hRoom : s.room = Room.east)
    (hChest : s.eastChestOpened = true) :
    step s Action.openChest = s := by
  have hNorth : ¬(s.room = Room.north ∧ s.northChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom, hChest]

/-! ### openFinalChest preserves lemmas -/

theorem openFinalChest_preserves_guardianAlive
    {s : EnvState} : (step s Action.openFinalChest).guardianAlive = s.guardianAlive := by
  by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
  · simp [step, h1]
  · simp [step, h1]

/-! ### Necessity lemmas -/

/-- Non-openFinalChest actions preserve the `finalChestOpened` field. -/
theorem non_openFinalChest_preserves_finalChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openFinalChest) :
    (step s a).finalChestOpened = s.finalChestOpened := by
  cases a with
  | toggleBridge =>
    by_cases h1 : s.room = Room.west
    · simp [step, h1]
    · simp [step, h1]
  | goCenter =>
    by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
    · simp [step, h1]
    · simp [step, h1]
  | goWest =>
    by_cases h1 : s.room = Room.center
    · simp [step, h1]
    · simp [step, h1]
  | goNorth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | goEast =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
    · simp [step, h1]
    · simp [step, h1]
  | goSouth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | openChest =>
    by_cases h1 : s.room = Room.north ∧ s.northChestOpened = false
    · simp [step, h1]
    · by_cases h2 : s.room = Room.east ∧ s.eastChestOpened = false
      · simp [step, h2]
      · simp [step, h1, h2]
  | attack =>
    by_cases h1 : s.room = Room.south ∧ s.guardianAlive = true ∧ s.hasSword = true
    · simp [step, h1]
    · simp [step, h1]
  | openFinalChest => exact absurd rfl ha
  | wait => simp [step]

/-- `openFinalChest` is the only action that can flip `finalChestOpened` from
    `false` to `true`. -/
theorem only_openFinalChest_sets_finalChestOpened
    {s : EnvState} (hs : s.finalChestOpened = false) (a : Action)
    (h : (step s a).finalChestOpened = true) : a = Action.openFinalChest := by
  by_cases ha : a = Action.openFinalChest
  · exact ha
  · have := non_openFinalChest_preserves_finalChestOpened (s := s) a ha
    rw [this, hs] at h
    simp at h

/-! ### Action-wise invariant lemmas -/

/-- `attack` is the only action that can change `guardianAlive`. -/
theorem only_attack_changes_guardianAlive
    {s : EnvState} (a : Action) (ha : a ≠ Action.attack) :
    (step s a).guardianAlive = s.guardianAlive := by
  cases a with
  | toggleBridge =>
    by_cases h1 : s.room = Room.west
    · simp [step, h1]
    · simp [step, h1]
  | goCenter =>
    by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
    · simp [step, h1]
    · simp [step, h1]
  | goWest =>
    by_cases h1 : s.room = Room.center
    · simp [step, h1]
    · simp [step, h1]
  | goNorth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | goEast =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
    · simp [step, h1]
    · simp [step, h1]
  | goSouth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | openChest =>
    by_cases h1 : s.room = Room.north ∧ s.northChestOpened = false
    · simp [step, h1]
    · by_cases h2 : s.room = Room.east ∧ s.eastChestOpened = false
      · simp [step, h2]
      · simp [step, h1, h2]
  | attack => exact absurd rfl ha
  | openFinalChest =>
    by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- `attack` is the only action that can change `finalChestVisible` (it reveals
    the final chest when the guardian is defeated). -/
theorem only_attack_changes_finalChestVisible
    {s : EnvState} (a : Action) (ha : a ≠ Action.attack) :
    (step s a).finalChestVisible = s.finalChestVisible := by
  cases a with
  | toggleBridge =>
    by_cases h1 : s.room = Room.west
    · simp [step, h1]
    · simp [step, h1]
  | goCenter =>
    by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
    · simp [step, h1]
    · simp [step, h1]
  | goWest =>
    by_cases h1 : s.room = Room.center
    · simp [step, h1]
    · simp [step, h1]
  | goNorth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | goEast =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
    · simp [step, h1]
    · simp [step, h1]
  | goSouth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | openChest =>
    by_cases h1 : s.room = Room.north ∧ s.northChestOpened = false
    · simp [step, h1]
    · by_cases h2 : s.room = Room.east ∧ s.eastChestOpened = false
      · simp [step, h2]
      · simp [step, h1, h2]
  | attack => exact absurd rfl ha
  | openFinalChest =>
    by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- `openChest` is the only action that can change `northChestOpened`. -/
theorem only_openChest_changes_northChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).northChestOpened = s.northChestOpened := by
  cases a with
  | toggleBridge =>
    by_cases h1 : s.room = Room.west
    · simp [step, h1]
    · simp [step, h1]
  | goCenter =>
    by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
    · simp [step, h1]
    · simp [step, h1]
  | goWest =>
    by_cases h1 : s.room = Room.center
    · simp [step, h1]
    · simp [step, h1]
  | goNorth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | goEast =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
    · simp [step, h1]
    · simp [step, h1]
  | goSouth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | openChest => exact absurd rfl ha
  | attack =>
    by_cases h1 : s.room = Room.south ∧ s.guardianAlive = true ∧ s.hasSword = true
    · simp [step, h1]
    · simp [step, h1]
  | openFinalChest =>
    by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- `openChest` is the only action that can change `eastChestOpened`. -/
theorem only_openChest_changes_eastChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).eastChestOpened = s.eastChestOpened := by
  cases a with
  | toggleBridge =>
    by_cases h1 : s.room = Room.west
    · simp [step, h1]
    · simp [step, h1]
  | goCenter =>
    by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
    · simp [step, h1]
    · simp [step, h1]
  | goWest =>
    by_cases h1 : s.room = Room.center
    · simp [step, h1]
    · simp [step, h1]
  | goNorth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | goEast =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
    · simp [step, h1]
    · simp [step, h1]
  | goSouth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | openChest => exact absurd rfl ha
  | attack =>
    by_cases h1 : s.room = Room.south ∧ s.guardianAlive = true ∧ s.hasSword = true
    · simp [step, h1]
    · simp [step, h1]
  | openFinalChest =>
    by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- Only `openChest` (north branch) can change `keys`. -/
theorem only_openChest_changes_keys
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).keys = s.keys := by
  cases a with
  | toggleBridge =>
    by_cases h1 : s.room = Room.west
    · simp [step, h1]
    · simp [step, h1]
  | goCenter =>
    by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
    · simp [step, h1]
    · simp [step, h1]
  | goWest =>
    by_cases h1 : s.room = Room.center
    · simp [step, h1]
    · simp [step, h1]
  | goNorth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | goEast =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
    · simp [step, h1]
    · simp [step, h1]
  | goSouth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | openChest => exact absurd rfl ha
  | attack =>
    by_cases h1 : s.room = Room.south ∧ s.guardianAlive = true ∧ s.hasSword = true
    · simp [step, h1]
    · simp [step, h1]
  | openFinalChest =>
    by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- `hasShield` never changes (shield is in initial state and never modified). -/
theorem hasShield_never_changes
    {s : EnvState} (a : Action) : (step s a).hasShield = s.hasShield := by
  cases a with
  | toggleBridge =>
    by_cases h1 : s.room = Room.west
    · simp [step, h1]
    · simp [step, h1]
  | goCenter =>
    by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
    · simp [step, h1]
    · simp [step, h1]
  | goWest =>
    by_cases h1 : s.room = Room.center
    · simp [step, h1]
    · simp [step, h1]
  | goNorth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | goEast =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
    · simp [step, h1]
    · simp [step, h1]
  | goSouth =>
    by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
    · simp [step, h1]
    · simp [step, h1]
  | openChest =>
    by_cases h1 : s.room = Room.north ∧ s.northChestOpened = false
    · simp [step, h1]
    · by_cases h2 : s.room = Room.east ∧ s.eastChestOpened = false
      · simp [step, h2]
      · simp [step, h1, h2]
  | attack =>
    by_cases h1 : s.room = Room.south ∧ s.guardianAlive = true ∧ s.hasSword = true
    · simp [step, h1]
    · simp [step, h1]
  | openFinalChest =>
    by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-! ### Reachable states and invariants -/

/-- Reachability: states reachable from `initialState` via arbitrary actions. -/
inductive Reachable : EnvState → Prop where
  | init : Reachable initialState
  | step (s : EnvState) (a : Action) : Reachable s → Reachable (step s a)

/-- Invariant: if the north chest is not opened then no keys have been collected. -/
theorem northChestOpened_or_keys_zero {s : EnvState} (hr : Reachable s) :
    s.northChestOpened = true ∨ s.keys = 0 := by
  induction hr with
  | init => simp [initialState]
  | step s a hr ih =>
    cases a with
    | toggleBridge =>
      by_cases h1 : s.room = Room.west
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | goCenter =>
      by_cases h1 : s.room = Room.west ∨ s.room = Room.north ∨ s.room = Room.east ∨ s.room = Room.south
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | goWest =>
      by_cases h1 : s.room = Room.center
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | goNorth =>
      by_cases h1 : s.room = Room.center ∧ bridgeAllowsNorth s.bridge
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | goEast =>
      by_cases h1 : s.room = Room.center ∧ bridgeAllowsEast s.bridge ∧ hasKey s
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | goSouth =>
      by_cases h1 : s.room = Room.center ∧ bridgeAllowsSouth s.bridge
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | openChest =>
      by_cases h1 : s.room = Room.north ∧ s.northChestOpened = false
      · left; simp [step, h1]
      · by_cases h2 : s.room = Room.east ∧ s.eastChestOpened = false
        · simp [step, h2]; exact ih
        · simp [step, h1, h2]; exact ih
    | attack =>
      by_cases h1 : s.room = Room.south ∧ s.guardianAlive = true ∧ s.hasSword = true
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | openFinalChest =>
      by_cases h1 : s.room = Room.center ∧ s.finalChestVisible = true
      · simp [step, h1]; exact ih
      · simp [step, h1]; exact ih
    | wait => simp [step]; exact ih

/-- Safety invariant: `keys` never decreases below zero (trivially true for
    `Nat`, but stated for documentation). -/
theorem keys_non_negative {s : EnvState} (_ : Reachable s) : s.keys ≥ 0 := by
  omega

/-- Helper invariant: if `finalChestVisible = true` then `guardianAlive = false`
    (the final chest is only revealed when the guardian is defeated by attack). -/
theorem finalChestVisible_implies_guardianDead {s : EnvState} (hr : Reachable s)
    (hv : s.finalChestVisible = true) : s.guardianAlive = false := by
  induction hr with
  | init => simp [initialState] at hv
  | step s' a hr ih =>
    by_cases hs : s'.finalChestVisible = true
    · have hguard' : (step s' a).guardianAlive = s'.guardianAlive := by
        by_cases ha : a = Action.attack
        · subst ha
          have hcond : ¬(s'.room = Room.south ∧ s'.guardianAlive = true ∧ s'.hasSword = true) := by
            intro h; have := ih hs; rw [this] at h; simp at h
          simp [step, hcond]
        · exact only_attack_changes_guardianAlive a ha
      rw [hguard']
      exact ih hs
    · have hf : s'.finalChestVisible = false := by
        cases h : s'.finalChestVisible with
        | true => exact absurd h hs
        | false => rfl
      have ha : a = Action.attack := by
        by_cases h' : a = Action.attack
        · exact h'
        · have := only_attack_changes_finalChestVisible (s := s') a h'
          rw [this, hf] at hv
          simp at hv
      subst ha
      by_cases hcond : s'.room = Room.south ∧ s'.guardianAlive = true ∧ s'.hasSword = true
      · simp [step, hcond]
      · have hstep : step s' Action.attack = s' := by simp [step, hcond]
        rw [hstep, hf] at hv
        simp at hv

/-- If a reachable state has `finalChestOpened = true`, then the guardian has
    been defeated. (Room position is not part of the postcondition because the
    player may move after opening the final chest.) -/
theorem completion_postcondition {s : EnvState} (hr : Reachable s)
    (hc : s.finalChestOpened = true) :
    s.guardianAlive = false := by
  induction hr with
  | init => simp [initialState] at hc
  | step s' a hr ih =>
    by_cases hs : s'.finalChestOpened = true
    · have hguard' : (step s' a).guardianAlive = s'.guardianAlive := by
        by_cases ha : a = Action.attack
        · subst ha
          have hcond : ¬(s'.room = Room.south ∧ s'.guardianAlive = true ∧ s'.hasSword = true) := by
            intro h; have := ih hs; rw [this] at h; simp at h
          simp [step, hcond]
        · exact only_attack_changes_guardianAlive a ha
      rw [hguard']
      exact ih hs
    · have hf : s'.finalChestOpened = false := by
        cases h : s'.finalChestOpened with
        | true => exact absurd h hs
        | false => rfl
      have ha : a = Action.openFinalChest := only_openFinalChest_sets_finalChestOpened hf a hc
      subst ha
      by_cases hcond : s'.room = Room.center ∧ s'.finalChestVisible = true
      · have hguardDead : s'.guardianAlive = false :=
          finalChestVisible_implies_guardianDead hr hcond.2
        have hguard' : (step s' Action.openFinalChest).guardianAlive = s'.guardianAlive :=
          openFinalChest_preserves_guardianAlive
        rw [hguard']; exact hguardDead
      · have hstep : step s' Action.openFinalChest = s' := by simp [step, hcond]
        rw [hstep, hf] at hc
        simp at hc

/-! ### Action-mask/safety layer -/

/-- Legal-action predicate for the symbolic transition layer (Bool version
    for computable checking via `native_decide`). -/
def actionEnabled (s : EnvState) : Action → Bool
  | Action.toggleBridge => s.room = Room.west
  | Action.goCenter =>
      s.room = Room.west || s.room = Room.north ||
      s.room = Room.east || s.room = Room.south
  | Action.goWest => s.room = Room.center
  | Action.goNorth => s.room = Room.center && decide (bridgeAllowsNorth s.bridge)
  | Action.goEast => s.room = Room.center && decide (bridgeAllowsEast s.bridge) && s.keys > 0
  | Action.goSouth => s.room = Room.center && decide (bridgeAllowsSouth s.bridge)
  | Action.openChest =>
      (s.room = Room.north && s.northChestOpened = false) ||
      (s.room = Room.east && s.eastChestOpened = false)
  | Action.attack =>
      s.room = Room.south && s.guardianAlive = true && s.hasSword = true
  | Action.openFinalChest =>
      s.room = Room.center && s.finalChestVisible = true
  | Action.wait => true

def actionsEnabledAlong : EnvState → List Action → Bool
  | _, [] => true
  | s, a :: rest => actionEnabled s a && actionsEnabledAlong (step s a) rest

/-! ### Interaction preserves lemmas (for BFS certificate proofs) -/

theorem openChest_north_preserves_guardianAlive
    {s : EnvState} (hRoom : s.room = Room.north) (hChest : s.northChestOpened = false) :
    (step s Action.openChest).guardianAlive = s.guardianAlive := by
  simp [step, hRoom, hChest]

theorem openChest_north_preserves_eastChestOpened
    {s : EnvState} (hRoom : s.room = Room.north) (hChest : s.northChestOpened = false) :
    (step s Action.openChest).eastChestOpened = s.eastChestOpened := by
  simp [step, hRoom, hChest]

theorem openChest_east_preserves_guardianAlive
    {s : EnvState} (hRoom : s.room = Room.east) (hChest : s.eastChestOpened = false) :
    (step s Action.openChest).guardianAlive = s.guardianAlive := by
  simp [step, hRoom, hChest]

/-! ### Baseline-aligned symbolic policy (BFS certificate mode) -/

/--
A symbolic BFS action provider.  In Python this is implemented by
`bfs_path(...)` plus `follow_bfs_aligned(...)`, which returns one movement
action toward the first tile of the current shortest path, or the supplied
`final_action` when already at a goal room.
-/
abbrev BfsAction := EnvState → Room → Action

/--
Policy shape matching `decide_task4`.

1. If north chest not opened: if at north, openChest; else BFS to north.
2. Else if east chest not opened: if at east, openChest; else BFS to east.
3. Else if guardian alive: if at south, attack; else BFS to south.
4. Else: if at center, openFinalChest; else BFS to center.

This definition is parameterized by `bfsAction`: Lean verifies the stage logic
and the BFS contract separately, instead of hardcoding a route.
-/
def symbolicPolicy (bfsAction : BfsAction) (s : EnvState) : Action :=
  if s.finalChestOpened then Action.wait
  else if s.northChestOpened = false then
    if s.room = Room.north then Action.openChest
    else bfsAction s Room.north
  else if s.eastChestOpened = false then
    if s.room = Room.east then Action.openChest
    else bfsAction s Room.east
  else if s.guardianAlive = true then
    if s.room = Room.south then Action.attack
    else bfsAction s Room.south
  else
    if s.room = Room.center then Action.openFinalChest
    else bfsAction s Room.center

/-! ### BFS route certificates -/

/--
Soundness certificate for a room-approach BFS phase.  The plan must end at the
target room while preserving all interaction-relevant state (keys, sword,
chests, guardian, visibility, completion).
-/
structure ApproachCertificate (target : Room) (start : EnvState) where
  plan : List Action
  enabled : actionsEnabledAlong start plan = true
  endsAtRoom : (run start plan).room = target
  keysPreserved : (run start plan).keys = start.keys
  hasShieldPreserved : (run start plan).hasShield = start.hasShield
  hasSwordPreserved : (run start plan).hasSword = start.hasSword
  northChestOpenedPreserved : (run start plan).northChestOpened = start.northChestOpened
  eastChestOpenedPreserved : (run start plan).eastChestOpened = start.eastChestOpened
  guardianAlivePreserved : (run start plan).guardianAlive = start.guardianAlive
  finalChestVisiblePreserved : (run start plan).finalChestVisible = start.finalChestVisible
  finalChestOpenedPreserved : (run start plan).finalChestOpened = start.finalChestOpened

abbrev NorthApproachCertificate (start : EnvState) := ApproachCertificate Room.north start
abbrev EastApproachCertificate (start : EnvState) := ApproachCertificate Room.east start
abbrev SouthApproachCertificate (start : EnvState) := ApproachCertificate Room.south start
abbrev CenterApproachCertificate (start : EnvState) := ApproachCertificate Room.center start

/-! ### Main non-fixed-route Task 4 theorem -/

/--
Task 4 completion theorem aligned with the BFS policy.

The policy structure is:
1. BFS to north → openChest (gains one key)
2. BFS to east → openChest (gains sword)
3. BFS to south → attack (defeats guardian, reveals final chest)
4. BFS to center → openFinalChest (completes task)

This theorem chains the BFS certificates and the interaction actions.
-/
theorem task4_bfs_certificate_completes
    (northRoute : NorthApproachCertificate initialState)
    (eastRoute : EastApproachCertificate
      (step (run initialState northRoute.plan) Action.openChest))
    (southRoute : SouthApproachCertificate
      (step (run (step (run initialState northRoute.plan) Action.openChest) eastRoute.plan) Action.openChest))
    (centerRoute : CenterApproachCertificate
      (step (run (step (run (step (run initialState northRoute.plan) Action.openChest) eastRoute.plan) Action.openChest) southRoute.plan) Action.attack)) :
    GoalReached
      (step
        (run
          (step
            (run
              (step
                (run
                  (step (run initialState northRoute.plan) Action.openChest)
                  eastRoute.plan)
                Action.openChest)
              southRoute.plan)
            Action.attack)
          centerRoute.plan)
        Action.openFinalChest) := by
  let sN := run initialState northRoute.plan
  let sNK := step sN Action.openChest
  let sE := run sNK eastRoute.plan
  let sEK := step sE Action.openChest
  let sS := run sEK southRoute.plan
  let sSK := step sS Action.attack
  let sC := run sSK centerRoute.plan
  -- North-approach BFS: ends at north, northChestOpened still false, guardian alive.
  have hRoomN : sN.room = Room.north := northRoute.endsAtRoom
  have hNChestClosed : sN.northChestOpened = false := by
    have h := northRoute.northChestOpenedPreserved; rw [h]; simp [initialState]
  have hNGuardian : sN.guardianAlive = true := by
    have h := northRoute.guardianAlivePreserved; rw [h]; simp [initialState]
  have hNEastChest : sN.eastChestOpened = false := by
    have h := northRoute.eastChestOpenedPreserved; rw [h]; simp [initialState]
  -- Open chest (north): guardian/eastChest preserved.
  have hNKGuardian : sNK.guardianAlive = sN.guardianAlive :=
    openChest_north_preserves_guardianAlive hRoomN hNChestClosed
  have hNKEastChest : sNK.eastChestOpened = sN.eastChestOpened :=
    openChest_north_preserves_eastChestOpened hRoomN hNChestClosed
  -- East-approach BFS: ends at east, eastChestOpened still false, guardian preserved.
  have hRoomE : sE.room = Room.east := eastRoute.endsAtRoom
  have hEEastChest : sE.eastChestOpened = false := by
    have h1 : sE.eastChestOpened = sNK.eastChestOpened := eastRoute.eastChestOpenedPreserved
    rw [h1, hNKEastChest, hNEastChest]
  have hEGuardian : sE.guardianAlive = true := by
    have h1 : sE.guardianAlive = sNK.guardianAlive := eastRoute.guardianAlivePreserved
    rw [h1, hNKGuardian, hNGuardian]
  -- Open chest (east): guardian preserved.
  have hEKGuardian : sEK.guardianAlive = sE.guardianAlive :=
    openChest_east_preserves_guardianAlive hRoomE hEEastChest
  -- South-approach BFS: ends at south, guardian preserved, hasSword preserved.
  have hRoomS : sS.room = Room.south := southRoute.endsAtRoom
  have hSGuardian : sS.guardianAlive = true := by
    have h1 : sS.guardianAlive = sEK.guardianAlive := southRoute.guardianAlivePreserved
    rw [h1, hEKGuardian, hEGuardian]
  have hSSword : sS.hasSword = true := by
    have h1 : sS.hasSword = sEK.hasSword := southRoute.hasSwordPreserved
    have h2 : sEK.hasSword = true := openChest_east_grants_sword hRoomE hEEastChest
    rw [h1]; exact h2
  -- Attack: guardian defeated, final chest visible.
  have hAttack := attack_with_sword_reveals_final_chest hRoomS hSGuardian hSSword
  have hSKVisible : sSK.finalChestVisible = true := hAttack.2
  -- Center-approach BFS: ends at center, finalChestVisible preserved.
  have hRoomC : sC.room = Room.center := centerRoute.endsAtRoom
  have hCVisible : sC.finalChestVisible = true := by
    have h1 : sC.finalChestVisible = sSK.finalChestVisible := centerRoute.finalChestVisiblePreserved
    rw [h1]; exact hSKVisible
  -- openFinalChest on center with visibility → finalChestOpened.
  have hDone : (step sC Action.openFinalChest).finalChestOpened = true :=
    openFinalChest_succeeds_when_visible hRoomC hCVisible
  simpa [GoalReached, sN, sNK, sE, sEK, sS, sSK, sC] using hDone

/-! ### Public map regression instance -/

-- Room-level BFS plans for the public Task-4 layout.
def publicNorthPlan : List Action :=
  [Action.goCenter, Action.goNorth]
def publicEastPlan : List Action :=
  [Action.goCenter, Action.goWest, Action.toggleBridge, Action.goCenter, Action.goEast]
def publicSouthPlan : List Action :=
  [Action.goCenter, Action.goWest, Action.toggleBridge, Action.goCenter, Action.goSouth]
def publicCenterPlan : List Action :=
  [Action.goCenter]

def publicNorthRoute : NorthApproachCertificate initialState :=
  { plan := publicNorthPlan
    enabled := by native_decide
    endsAtRoom := by native_decide
    keysPreserved := by native_decide
    hasShieldPreserved := by native_decide
    hasSwordPreserved := by native_decide
    northChestOpenedPreserved := by native_decide
    eastChestOpenedPreserved := by native_decide
    guardianAlivePreserved := by native_decide
    finalChestVisiblePreserved := by native_decide
    finalChestOpenedPreserved := by native_decide }

def publicEastRoute : EastApproachCertificate
      (step (run initialState publicNorthPlan) Action.openChest) :=
  { plan := publicEastPlan
    enabled := by native_decide
    endsAtRoom := by native_decide
    keysPreserved := by native_decide
    hasShieldPreserved := by native_decide
    hasSwordPreserved := by native_decide
    northChestOpenedPreserved := by native_decide
    eastChestOpenedPreserved := by native_decide
    guardianAlivePreserved := by native_decide
    finalChestVisiblePreserved := by native_decide
    finalChestOpenedPreserved := by native_decide }

def publicSouthRoute : SouthApproachCertificate
      (step (run (step (run initialState publicNorthPlan) Action.openChest) publicEastPlan) Action.openChest) :=
  { plan := publicSouthPlan
    enabled := by native_decide
    endsAtRoom := by native_decide
    keysPreserved := by native_decide
    hasShieldPreserved := by native_decide
    hasSwordPreserved := by native_decide
    northChestOpenedPreserved := by native_decide
    eastChestOpenedPreserved := by native_decide
    guardianAlivePreserved := by native_decide
    finalChestVisiblePreserved := by native_decide
    finalChestOpenedPreserved := by native_decide }

def publicCenterRoute : CenterApproachCertificate
      (step (run (step (run (step (run initialState publicNorthPlan) Action.openChest) publicEastPlan) Action.openChest) publicSouthPlan) Action.attack) :=
  { plan := publicCenterPlan
    enabled := by native_decide
    endsAtRoom := by native_decide
    keysPreserved := by native_decide
    hasShieldPreserved := by native_decide
    hasSwordPreserved := by native_decide
    northChestOpenedPreserved := by native_decide
    eastChestOpenedPreserved := by native_decide
    guardianAlivePreserved := by native_decide
    finalChestVisiblePreserved := by native_decide
    finalChestOpenedPreserved := by native_decide }

theorem public_task4_bfs_certificate_completes :
    GoalReached
      (step
        (run
          (step
            (run
              (step
                (run
                  (step (run initialState publicNorthPlan) Action.openChest)
                  publicEastPlan)
                Action.openChest)
              publicSouthPlan)
            Action.attack)
          publicCenterPlan)
        Action.openFinalChest) := by
  exact task4_bfs_certificate_completes publicNorthRoute publicEastRoute
    publicSouthRoute publicCenterRoute

end Task4Formalization
