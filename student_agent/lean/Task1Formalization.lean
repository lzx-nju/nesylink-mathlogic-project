/-
  Environment formalization for `mathematical_logic/task_1`.

  This is the simplest built-in task: open the left chest to get one key, then
  use the north locked exit. The formalization models the room at the tile
  level (8 rows × 10 columns), including wall collision, chest interaction at
  the correct tile, and the locked north exit.

  Python correspondence:
  * `nesylink/map_data/mathematical_logic/task_1/room_001.json`
  * `nesylink/core/mechanics/interactions.py`
  * `nesylink/core/mechanics/movement.py`

  Key parameters verified against the Python implementation:
  * Room layout: `room_001.json` (8 rows × 10 columns).
  * Spawn: `spawns.default = [4, 6]`.
  * Chest: `pos = [0, 3]`, loot = key.
  * North exit tiles: `EXIT_DIRECTION_TILES["north"] = ((4, 0), (5, 0))`
    (see `nesylink/core/world/schema.py:30-35`). We pick `(4, 0)` as the
    witness exit tile; it is consistent with the spawn column.
  * Chest interaction uses Manhattan adjacency (`is_adjacent`,
    `state.py:142-143`, distance ≤ 1). To match this semantics we model
    `openChest` as triggering whenever the player stands on any tile at
    Manhattan distance ≤ 1 from the chest tile `(0, 3)`. The witness plan
    keeps the player on `(0, 3)` itself, which is a valid adjacent tile
    (distance 0).
-/

namespace Task1Formalization

/-! ### Tile-level room grid -/

-- Room layout (8 rows × 10 columns):
--   row 2: "##..######"   → cols 0-1 wall, cols 2-3 floor, cols 4-9 wall
--   row 5: "#######..."   → cols 0-6 wall, cols 7-9 floor
--   all other rows: floor
def isWalkable (x y : Nat) : Bool :=
  if y < 8 ∧ x < 10 then
    match y, x with
    | 2, 0 | 2, 1 => false
    | 2, 4 | 2, 5 | 2, 6 | 2, 7 | 2, 8 | 2, 9 => false
    | 5, 0 | 5, 1 | 5, 2 | 5, 3 | 5, 4 | 5, 5 | 5, 6 => false
    | _, _ => true
  else false

-- Manhattan distance between two tiles.
def manhattan (x1 y1 x2 y2 : Nat) : Nat :=
  (if x1 ≤ x2 then x2 - x1 else x1 - x2) + (if y1 ≤ y2 then y2 - y1 else y1 - y2)

-- Chest tile from `room_001.json`.
def chestTile : Nat × Nat := (0, 3)

-- Adjacency as in `state.py:is_adjacent` (Manhattan distance ≤ 1, including
-- the tile itself, since `manhattan_distance <= 1` covers distance 0).
def isAdjacentToChest (x y : Nat) : Bool :=
  manhattan x y chestTile.1 chestTile.2 ≤ 1

/-! ### Actions -/

inductive Action where
  | up | down | left | right
  | openChest | goNorth
  deriving DecidableEq, Repr

/-! ### Environment state -/

structure EnvState where
  x : Nat
  y : Nat
  keys : Nat
  chestOpened : Bool
  completed : Bool
  deriving DecidableEq, Repr

-- Spawn at tile (4, 6) per room_001.json
def initialState : EnvState :=
  { x := 4, y := 6, keys := 0, chestOpened := false, completed := false }

def GoalReached (s : EnvState) : Prop :=
  s.completed = true

/-! ### Transition function -/

def step (s : EnvState) : Action → EnvState
  | Action.up =>
      let ny := s.y - 1
      if isWalkable s.x ny then { s with y := ny } else s
  | Action.down =>
      let ny := s.y + 1
      if isWalkable s.x ny then { s with y := ny } else s
  | Action.left =>
      let nx := s.x - 1
      if isWalkable nx s.y then { s with x := nx } else s
  | Action.right =>
      let nx := s.x + 1
      if isWalkable nx s.y then { s with x := nx } else s
  | Action.openChest =>
      -- Trigger on any tile at Manhattan distance ≤ 1 from the chest, matching
      -- `interactions.py` + `state.py:is_adjacent`.
      if isAdjacentToChest s.x s.y ∧ ¬s.chestOpened then
        { s with chestOpened := true, keys := s.keys + 1 }
      else
        s
  | Action.goNorth =>
      if s.x = 4 ∧ s.y = 0 ∧ s.keys > 0 then
        { s with keys := s.keys - 1, completed := true }
      else
        s

def run : EnvState → List Action → EnvState
  | s, [] => s
  | s, a :: rest => run (step s a) rest

/-! ### Safety invariants -/

theorem step_preserves_walkable
    {s : EnvState} (hw : isWalkable s.x s.y = true) (a : Action) :
    isWalkable (step s a).x (step s a).y = true := by
  cases a
  · unfold step; simp; split <;> assumption
  · unfold step; simp; split <;> assumption
  · unfold step; simp; split <;> assumption
  · unfold step; simp; split <;> assumption
  · -- openChest never moves the player.
    unfold step; simp; split <;> assumption
  · -- goNorth never moves the player.
    unfold step; simp; split <;> assumption

theorem initialState_walkable : isWalkable initialState.x initialState.y = true := by
  decide

theorem run_preserves_walkable
    {s : EnvState} (hw : isWalkable s.x s.y = true) (plan : List Action) :
    isWalkable (run s plan).x (run s plan).y = true := by
  induction plan generalizing s with
  | nil => exact hw
  | cons a rest ih =>
    apply ih
    exact step_preserves_walkable hw a

theorem walkable_implies_bounds {x y : Nat} (h : isWalkable x y = true) : x < 10 ∧ y < 8 := by
  unfold isWalkable at h
  by_cases hb : y < 8 ∧ x < 10
  · exact ⟨hb.2, hb.1⟩
  · simp [hb] at h

/-! ### Wall documentation -/

example : isWalkable 4 2 = false := by decide

example : isWalkable 0 5 = false := by decide

/-! ### Chest adjacency lemmas -/

theorem chest_at_tile_zero_three : chestTile = (0, 3) := rfl

theorem adjacent_tiles_walkable :
    isWalkable 0 3 = true ∧ isWalkable 1 3 = true ∧ isWalkable 0 4 = true := by
  decide

theorem chest_tile_walkable : isWalkable chestTile.1 chestTile.2 = true := by
  decide

/-- The chest-adjacent tile used in the witness plan is walkable. -/
theorem witness_chest_tile_walkable : isWalkable 0 3 = true := by decide

/-! ### Interaction preconditions -/

theorem openChest_only_at_chest
    {s : EnvState} (h : ¬isAdjacentToChest s.x s.y) :
    step s Action.openChest = s := by
  dsimp [step]
  simp [h]

theorem openChest_already_opened
    {s : EnvState} (hc : s.chestOpened = true) :
    step s Action.openChest = s := by
  dsimp [step]
  simp [hc]

theorem openChest_at_chest_increases_keys
    {s : EnvState} (hadj : isAdjacentToChest s.x s.y = true) (hc : ¬s.chestOpened) :
    (step s Action.openChest).keys = s.keys + 1 := by
  dsimp [step]
  simp [hadj, hc]

theorem openChest_at_chest_marks_opened
    {s : EnvState} (hadj : isAdjacentToChest s.x s.y = true) (hc : ¬s.chestOpened) :
    (step s Action.openChest).chestOpened = true := by
  dsimp [step]
  simp [hadj, hc]

theorem openChest_preserves_position
    {s : EnvState} (hadj : isAdjacentToChest s.x s.y = true) (hc : ¬s.chestOpened) :
    (step s Action.openChest).x = s.x ∧ (step s Action.openChest).y = s.y := by
  dsimp [step]
  simp [hadj, hc]

theorem goNorth_only_at_exit
    {s : EnvState} (h : s.x ≠ 4 ∨ s.y ≠ 0) :
    step s Action.goNorth = s := by
  rcases h with hx | hy
  · simp [step, hx]
  · simp [step, hy]

theorem goNorth_without_key
    {s : EnvState} (hx : s.x = 4) (hy : s.y = 0) (hk : s.keys = 0) :
    step s Action.goNorth = s := by
  dsimp [step]
  simp [hx, hy, hk]

theorem goNorth_at_exit_with_key_completes
    {s : EnvState} (hx : s.x = 4) (hy : s.y = 0) (hk : s.keys > 0) :
    (step s Action.goNorth).completed = true := by
  dsimp [step]
  simp [hx, hy, hk]

theorem goNorth_at_exit_consumes_key
    {s : EnvState} (hx : s.x = 4) (hy : s.y = 0) (hk : s.keys > 0) :
    (step s Action.goNorth).keys = s.keys - 1 := by
  dsimp [step]
  simp [hx, hy, hk]

/-! ### Necessity lemmas -/

/-- Non-goNorth actions preserve the `completed` field. -/
theorem non_goNorth_preserves_completed
    {s : EnvState} (a : Action) (ha : a ≠ Action.goNorth) :
    (step s a).completed = s.completed := by
  cases a with
  | up =>
    by_cases h : isWalkable s.x (s.y - 1) = true
    · simp [step, h]
    · simp [step, h]
  | down =>
    by_cases h : isWalkable s.x (s.y + 1) = true
    · simp [step, h]
    · simp [step, h]
  | left =>
    by_cases h : isWalkable (s.x - 1) s.y = true
    · simp [step, h]
    · simp [step, h]
  | right =>
    by_cases h : isWalkable (s.x + 1) s.y = true
    · simp [step, h]
    · simp [step, h]
  | openChest =>
    by_cases h1 : isAdjacentToChest s.x s.y = true
    · by_cases h2 : s.chestOpened = true
      · simp [step, h1, h2]
      · simp [step, h1, h2]
    · simp [step, h1]
  | goNorth => exact absurd rfl ha

/-- `goNorth` is the only action that can flip `completed` from `false` to
    `true`. All other actions leave `completed` unchanged. -/
theorem only_goNorth_sets_completed
    {s : EnvState} (hs : s.completed = false) (a : Action)
    (h : (step s a).completed = true) : a = Action.goNorth := by
  by_cases ha : a = Action.goNorth
  · exact ha
  · have := non_goNorth_preserves_completed (s := s) a ha
    rw [this, hs] at h
    simp at h

/-- Moving actions preserve the `chestOpened` flag. (`openChest` is excluded
    because it can set the flag to `true`.) -/
theorem move_preserves_chestOpened
    {s : EnvState} (a : Action)
    (ha : a = Action.up ∨ a = Action.down ∨ a = Action.left ∨ a = Action.right) :
    (step s a).chestOpened = s.chestOpened := by
  rcases ha with rfl | rfl | rfl | rfl
  · unfold step; simp; split <;> rfl
  · unfold step; simp; split <;> rfl
  · unfold step; simp; split <;> rfl
  · unfold step; simp; split <;> rfl

/-- Moving actions preserve the `keys` field. -/
theorem move_preserves_keys
    {s : EnvState} (a : Action)
    (ha : a = Action.up ∨ a = Action.down ∨ a = Action.left ∨ a = Action.right) :
    (step s a).keys = s.keys := by
  rcases ha with rfl | rfl | rfl | rfl
  · unfold step; simp; split <;> rfl
  · unfold step; simp; split <;> rfl
  · unfold step; simp; split <;> rfl
  · unfold step; simp; split <;> rfl

/-- `goNorth` preserves the `chestOpened` flag (it only modifies `keys` and
    `completed`). -/
theorem goNorth_preserves_chestOpened
    {s : EnvState} : (step s Action.goNorth).chestOpened = s.chestOpened := by
  unfold step; simp; split <;> rfl

/-! ### Witness plan -/

-- Tile-level route:
--   (4,6) → right×3 → (7,6) → up×3 → (7,3) → left×7 → (0,3)
--   openChest (adjacent, distance 0) → right×3 → (3,3) → up×3 → (3,0) → right×1 → (4,0)
--   goNorth
def witnessPlan : List Action := [
  Action.right, Action.right, Action.right,
  Action.up, Action.up, Action.up,
  Action.left, Action.left, Action.left, Action.left, Action.left, Action.left, Action.left,
  Action.openChest,
  Action.right, Action.right, Action.right,
  Action.up, Action.up, Action.up,
  Action.right,
  Action.goNorth
]

def finalState : EnvState :=
  { x := 4, y := 0, keys := 0, chestOpened := true, completed := true }

theorem witnessPlan_executes_to_finalState :
    run initialState witnessPlan = finalState := by
  native_decide

theorem witnessPlan_reaches_goal :
    GoalReached (run initialState witnessPlan) := by
  rw [witnessPlan_executes_to_finalState]
  simp [GoalReached, finalState]

theorem task1_completable :
    ∃ plan : List Action, GoalReached (run initialState plan) := by
  exact ⟨witnessPlan, witnessPlan_reaches_goal⟩

/-! ### Symbolic policy formalization -/

/--
The abstract stage machine behind the task 1 baseline. This is the symbolic
counterpart of the Python `build_task1_plan` routine: it ignores pixel-level
frame counts and keeps only the high-level subgoal ordering that matters for
the environment proof.
-/
inductive PolicyStage where
  | openChest
  | goNorth
  | done
  deriving DecidableEq, Repr

def policyStage (s : EnvState) : PolicyStage :=
  if s.chestOpened = false then PolicyStage.openChest
  else if s.completed = false then PolicyStage.goNorth
  else PolicyStage.done

/--
State-driven tile-level policy. It maps the current symbolic state to the next
movement action, routing around walls to reach the chest tile `(0, 3)` first,
then the north exit tile `(4, 0)`.

Route to chest (stage `openChest`):
  `(4,6) → right×3 → (7,6) → up×3 → (7,3) → left×7 → (0,3)`
The detour to column 7 bypasses the wall on row 5 (cols 0–6). Row 3 is fully
walkable, so the player proceeds left to the chest tile.

Route to exit (stage `goNorth`):
  `(0,3) → right×3 → (3,3) → up×3 → (3,0) → right×1 → (4,0)`
The player ascends through column 3 (one of only two floor columns on row 2),
then moves right to the exit tile.
-/
def symbolicPolicy (s : EnvState) : Action :=
  match policyStage s with
  | PolicyStage.openChest =>
      if s.x = 0 ∧ s.y = 3 ∧ !s.chestOpened then
        Action.openChest
      else if s.y = 6 then
        if s.x < 7 then Action.right else Action.up
      else if s.x = 7 ∧ s.y > 3 then
        Action.up
      else if s.y = 3 ∧ s.x > 0 then
        Action.left
      else
        Action.up
  | PolicyStage.goNorth =>
      if s.x = 4 ∧ s.y = 0 ∧ s.keys > 0 then
        Action.goNorth
      else if s.y = 3 ∧ s.x < 3 then
        Action.right
      else if s.x = 3 ∧ s.y > 0 then
        Action.up
      else if s.y = 0 ∧ s.x < 4 then
        Action.right
      else
        Action.up
  | PolicyStage.done => Action.up

def policyStep (s : EnvState) : EnvState :=
  step s (symbolicPolicy s)

def runPolicy : Nat → EnvState → EnvState
  | 0, s => s
  | n + 1, s => runPolicy n (policyStep s)

def policyTrace : Nat → EnvState → List Action
  | 0, _ => []
  | n + 1, s =>
      let a := symbolicPolicy s
      a :: policyTrace n (step s a)

/-- Legal-action predicate for the symbolic transition layer (Bool version
    for computable checking via `native_decide`). -/
def actionEnabled (s : EnvState) : Action → Bool
  | Action.up => isWalkable s.x (s.y - 1)
  | Action.down => isWalkable s.x (s.y + 1)
  | Action.left => isWalkable (s.x - 1) s.y
  | Action.right => isWalkable (s.x + 1) s.y
  | Action.openChest => isAdjacentToChest s.x s.y && !s.chestOpened
  | Action.goNorth => s.x = 4 && s.y = 0 && s.keys > 0

def actionsEnabledAlong : EnvState → List Action → Bool
  | _, [] => true
  | s, a :: rest => actionEnabled s a && actionsEnabledAlong (step s a) rest

theorem policyTrace_22_matches_witnessPlan :
    policyTrace 22 initialState = witnessPlan := by
  native_decide

theorem policyTrace_22_actions_enabled :
    actionsEnabledAlong initialState (policyTrace 22 initialState) = true := by
  native_decide

theorem symbolicPolicy_run_22_finalState :
    runPolicy 22 initialState = finalState := by
  native_decide

theorem symbolicPolicy_reaches_goal :
    GoalReached (runPolicy 22 initialState) := by
  rw [symbolicPolicy_run_22_finalState]
  simp [GoalReached, finalState]

theorem task1_symbolicPolicy_completes :
    ∃ n, GoalReached (runPolicy n initialState) := by
  exact ⟨22, symbolicPolicy_reaches_goal⟩

end Task1Formalization
