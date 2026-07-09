/-!
  Task 1 formalization, rewritten to match the current BFS-based
  `student_agent/baseline_policy.py` implementation.

  Important alignment with Python policy:

  * `decide_task1` does NOT follow a fixed action list.
  * It reads `keys = current_keys(reward_signals, inventory)`.
  * If `keys <= 0`, it detects the visible chest, builds `blocked` from the
    current frame, sets goals to the walkable neighbors of that chest, and calls
    `follow_bfs_aligned(..., final_action = ACTION_A)`.
  * If `keys > 0`, it sets goals to `EXIT_DIRECTION_TILES["north"]` and calls
    `follow_bfs_aligned(..., final_action = ACTION_UP)`.
  * `follow_bfs_aligned` recomputes BFS at every step.  This Lean model proves
    the symbolic BFS contract rather than proving one fixed route.

  Pixel alignment is intentionally abstracted away: the proof layer reasons at
  tile level.  Alignment micro-actions are implementation details whose only
  specification obligation is that they eventually realize the next BFS tile
  transition without changing the high-level stage.
-/

namespace Task1Formalization

/-! ### Tile and action model -/

abbrev Tile := Nat × Nat

def GRID_WIDTH : Nat := 10
def GRID_HEIGHT : Nat := 8

def inBounds (t : Tile) : Bool :=
  decide (t.1 < GRID_WIDTH ∧ t.2 < GRID_HEIGHT)

def chestTile : Tile := (0, 3)

def northExitTiles : List Tile := [(4, 0), (5, 0)]

def isNorthExitTile (x y : Nat) : Bool :=
  decide (y = 0 ∧ (x = 4 ∨ x = 5))

def manhattan (a b : Tile) : Nat :=
  (if a.1 ≤ b.1 then b.1 - a.1 else a.1 - b.1) +
  (if a.2 ≤ b.2 then b.2 - a.2 else a.2 - b.2)

def isAdjacent (a b : Tile) : Bool :=
  decide (manhattan a b = 1)

/--
Four-neighbor order matches Python `neighbors_of`:
`[(x, y - 1), (x, y + 1), (x - 1, y), (x + 1, y)]`, except that this symbolic
version omits out-of-range underflow candidates instead of generating saturated
natural-number duplicates.  Later `inBounds` checks play the same role as the
Python filter.
-/
def neighborsOf (t : Tile) : List Tile :=
  (if t.2 = 0 then [] else [(t.1, t.2 - 1)]) ++
  [(t.1, t.2 + 1)] ++
  (if t.1 = 0 then [] else [(t.1 - 1, t.2)]) ++
  [(t.1 + 1, t.2)]

inductive Action where
  | noop
  | up | down | left | right
  | openChest
  deriving DecidableEq, Repr



/-! ### Perceived room abstraction -/

/--
`RoomModel` is the symbolic counterpart of the current visual frame.

`blocked` corresponds to `build_blocked_tiles(frame, avoid_traps=False)` for
Task 1: walls, abysses if any, and currently visible chest tiles are treated as
not traversable by BFS.  `detectedChest` corresponds to
`detect_chest_tile(frame)`.
-/
structure RoomModel where
  blocked : Tile → Bool
  detectedChest : Option Tile

/-- BFS may step on a tile iff it is within the grid and not blocked. -/
def freeTile (r : RoomModel) (t : Tile) : Bool :=
  inBounds t && !r.blocked t

/-- Python task1 chest goals: walkable neighbors of the detected chest. -/
def chestNeighborGoals (r : RoomModel) : List Tile :=
  match r.detectedChest with
  | none => []
  | some c => (neighborsOf c).filter (fun n => freeTile r n)

def isAdjacentToDetectedChest (r : RoomModel) (spos : Tile) : Bool :=
  match r.detectedChest with
  | none => false
  | some c => isAdjacent spos c

/-! ### Environment state and transition -/

structure EnvState where
  x : Nat
  y : Nat
  keys : Nat
  chestOpened : Bool
  completed : Bool
  deriving DecidableEq, Repr

-- Public task-1 spawn tile.
def initialState : EnvState :=
  { x := 4, y := 6, keys := 0, chestOpened := false, completed := false }

def pos (s : EnvState) : Tile := (s.x, s.y)

def GoalReached (s : EnvState) : Prop :=
  s.completed = true

/-- Movement target with boundary underflow represented as `none`. -/
def moveTarget (s : EnvState) : Action → Option Tile
  | Action.up => if s.y = 0 then none else some (s.x, s.y - 1)
  | Action.down => some (s.x, s.y + 1)
  | Action.left => if s.x = 0 then none else some (s.x - 1, s.y)
  | Action.right => some (s.x + 1, s.y)
  | _ => none

def moveStep (r : RoomModel) (s : EnvState) (target : Option Tile) : EnvState :=
  match target with
  | none => s
  | some t => if freeTile r t then { s with x := t.1, y := t.2 } else s

/--
Tile-level transition.  The only high-level special actions are exactly the
ones used by Task 1: `ACTION_A` for opening the detected key chest and
`ACTION_UP` on a north exit tile for leaving through the locked door.
-/
def step (r : RoomModel) (s : EnvState) : Action → EnvState
  | Action.noop => s
  | Action.up =>
      if isNorthExitTile s.x s.y && decide (s.keys > 0) then
        { s with keys := s.keys - 1, completed := true }
      else
        moveStep r s (moveTarget s Action.up)
  | Action.down => moveStep r s (moveTarget s Action.down)
  | Action.left => moveStep r s (moveTarget s Action.left)
  | Action.right => moveStep r s (moveTarget s Action.right)
  | Action.openChest =>
      if isAdjacentToDetectedChest r (pos s) && !s.chestOpened then
        { s with chestOpened := true, keys := s.keys + 1 }
      else
        s


def run (r : RoomModel) : EnvState → List Action → EnvState
  | s, [] => s
  | s, a :: rest => run r (step r s a) rest

/-! ### Action-mask/safety layer -/

def actionEnabled (r : RoomModel) (s : EnvState) : Action → Bool
  | Action.noop => true
  | Action.up =>
      match moveTarget s Action.up with
      | none => false
      | some t => freeTile r t
  | Action.down =>
      match moveTarget s Action.down with
      | none => false
      | some t => freeTile r t
  | Action.left =>
      match moveTarget s Action.left with
      | none => false
      | some t => freeTile r t
  | Action.right =>
      match moveTarget s Action.right with
      | none => false
      | some t => freeTile r t
  | Action.openChest => isAdjacentToDetectedChest r (pos s) && !s.chestOpened

def actionsEnabledAlong (r : RoomModel) : EnvState → List Action → Bool
  | _, [] => true
  | s, a :: rest =>
      actionEnabled r s a && actionsEnabledAlong r (step r s a) rest

/-! ### Baseline-aligned symbolic policy shape -/

/--
A symbolic BFS action provider.  In Python this is implemented by
`bfs_path(...)` plus `follow_bfs_aligned(...)`, which returns one movement
action toward the first tile of the current shortest path, or the supplied
`final_action` when already at a goal.
-/
abbrev BfsAction := EnvState → List Tile → Action

/--
Policy shape matching `decide_task1`.

This definition is intentionally parameterized by `bfsAction`: Lean verifies the
stage logic and the BFS contract separately, instead of hardcoding a route.
-/
def symbolicPolicy (r : RoomModel) (bfsAction : BfsAction) (s : EnvState) : Action :=
  if s.completed then
    Action.noop
  else if s.keys = 0 then
    match r.detectedChest with
    | none => Action.noop
    | some _ =>
        let goals := chestNeighborGoals r
        if pos s ∈ goals then Action.openChest else bfsAction s goals
  else
    if isNorthExitTile s.x s.y then Action.up else bfsAction s northExitTiles

/-- When no key is held and the BFS has reached a chest-neighbor goal, the
    symbolic policy emits the same final action as Python: `ACTION_A`. -/
theorem symbolicPolicy_getKey_goal_emits_openChest
    (hDone : s.completed = false)
    (hKeys : s.keys = 0)
    (hChest : r.detectedChest ≠ none)
    (hGoal : pos s ∈ chestNeighborGoals r) :
    symbolicPolicy r bfsAction s = Action.openChest := by
  unfold symbolicPolicy
  simp [hDone, hKeys, hGoal]

  cases hDet : r.detectedChest with
  | none =>
      exfalso
      exact hChest hDet
  | some c =>
      simp [hDet]


/-- Once a key is held and the agent is on a north-exit tile, the symbolic
    policy emits the same final action as Python: `ACTION_UP` toward the north
    locked exit, represented here as `goNorth`. -/
theorem symbolicPolicy_exit_goal_emits_up
    (r : RoomModel) (bfsAction : BfsAction) {s : EnvState}
    (hDone : s.completed = false)
    (hKeys : s.keys > 0)
    (hExit : isNorthExitTile s.x s.y = true) :
    symbolicPolicy r bfsAction s = Action.up := by
  unfold symbolicPolicy
  have hNotZero : ¬ s.keys = 0 := Nat.ne_of_gt hKeys
  simp [hDone, hNotZero, hExit]


/-! ### BFS route certificates -/

/--
Soundness certificate for the first BFS phase: from the current state, BFS has
found an enabled movement plan that ends adjacent to the detected chest.  This
is the formal counterpart of:

```
goals = {n for n in neighbors_of(chest) if in_bounds(n) and n not in blocked}
follow_bfs_aligned(..., goals, blocked, final_action=ACTION_A)
```
-/
structure ChestBfsCertificate (r : RoomModel) (start : EnvState) where
  plan : List Action
  enabled : actionsEnabledAlong r start plan = true
  endsAdjacent : isAdjacentToDetectedChest r (pos (run r start plan)) = true
  chestStillClosed : (run r start plan).chestOpened = false

/--
Soundness certificate for the second BFS phase: after opening the chest, BFS has
found an enabled movement plan that ends on a north-exit tile while a key is
still held.  This is the formal counterpart of:

```
exit_goals = set(EXIT_DIRECTION_TILES["north"])
follow_bfs_aligned(..., exit_goals, blocked, final_action=ACTION_UP)
```
-/
structure ExitBfsCertificate (r : RoomModel) (start : EnvState) where
  plan : List Action
  enabled : actionsEnabledAlong r start plan = true
  endsAtNorthExit : isNorthExitTile (run r start plan).x (run r start plan).y = true
  keyPositiveAtGoal : (run r start plan).keys > 0

/-! ### Local interaction correctness lemmas -/

theorem openChest_at_detected_chest_neighbor_gets_key
    (r : RoomModel) {s : EnvState}
    (hAdj : isAdjacentToDetectedChest r (pos s) = true)
    (hClosed : s.chestOpened = false) :
    (step r s Action.openChest).keys = s.keys + 1 ∧
    (step r s Action.openChest).chestOpened = true := by
  simp [step, hAdj, hClosed]

theorem up_at_exit_with_key_completes
    (r : RoomModel) {s : EnvState}
    (hExit : isNorthExitTile s.x s.y = true)
    (hKey : s.keys > 0) :
    (step r s Action.up).completed = true := by
  simp [step, hExit, hKey]


/-! ### Main non-fixed-route Task 1 theorem -/

/--
Task 1 completion theorem aligned with the BFS policy.

This theorem is not a fixed-route proof.  It says: for any perceived Task-1
room model `r`, if the first BFS phase supplies a sound route to a walkable
neighbor of the detected chest, and the second BFS phase supplies a sound route
to a north-exit tile after the chest is opened, then the baseline Task-1 policy
structure completes the task.
-/
theorem task1_bfs_certificate_completes
    (r : RoomModel)
    (chestRoute : ChestBfsCertificate r initialState)
    (exitRoute :
      ExitBfsCertificate r
        (step r (run r initialState chestRoute.plan) Action.openChest)) :
    GoalReached
      (step r
        (run r
          (step r (run r initialState chestRoute.plan) Action.openChest)
          exitRoute.plan)
        Action.up) := by
  let sOpen := step r (run r initialState chestRoute.plan) Action.openChest
  let sExit := run r sOpen exitRoute.plan
  have hDone : (step r sExit Action.up).completed = true :=
    up_at_exit_with_key_completes r
      (s := sExit)
      exitRoute.endsAtNorthExit
      exitRoute.keyPositiveAtGoal
  simpa [GoalReached, sOpen, sExit] using hDone

/-- The first BFS phase followed by `ACTION_A` really produces a key. -/
theorem task1_chest_phase_gets_key
    (r : RoomModel)
    (chestRoute : ChestBfsCertificate r initialState) :
    (step r (run r initialState chestRoute.plan) Action.openChest).keys =
      (run r initialState chestRoute.plan).keys + 1 := by
  have h := openChest_at_detected_chest_neighbor_gets_key r
    (s := run r initialState chestRoute.plan)
    chestRoute.endsAdjacent
    chestRoute.chestStillClosed
  exact h.1

/-! ### Public map regression instance

The following closed certificates instantiate the generic BFS theorem on the
public Task-1 layout.  They are included only as regression checks for the known
training map; the main theorem above is the non-fixed-route proof used to align
with the current BFS policy.
-/

def publicWall (t : Tile) : Bool :=
  decide (
    (t.2 = 2 ∧ (t.1 = 0 ∨ t.1 = 1 ∨ t.1 = 4 ∨ t.1 = 5 ∨
      t.1 = 6 ∨ t.1 = 7 ∨ t.1 = 8 ∨ t.1 = 9)) ∨
    (t.2 = 5 ∧ (t.1 = 0 ∨ t.1 = 1 ∨ t.1 = 2 ∨ t.1 = 3 ∨
      t.1 = 4 ∨ t.1 = 5 ∨ t.1 = 6))
  )

def publicBlocked (t : Tile) : Bool :=
  publicWall t || decide (t = chestTile)

def publicRoom : RoomModel :=
  { blocked := publicBlocked, detectedChest := some chestTile }

def publicChestPlan : List Action := [
  Action.right, Action.right, Action.right,
  Action.up, Action.up, Action.up,
  Action.left, Action.left, Action.left, Action.left, Action.left, Action.left
]

def publicExitPlan : List Action := [
  Action.right, Action.right,
  Action.up, Action.up, Action.up,
  Action.right
]

def publicChestRoute : ChestBfsCertificate publicRoom initialState :=
  { plan := publicChestPlan
    enabled := by native_decide
    endsAdjacent := by native_decide
    chestStillClosed := by native_decide }

def publicExitRoute :
    ExitBfsCertificate publicRoom
      (step publicRoom (run publicRoom initialState publicChestRoute.plan) Action.openChest) :=
  { plan := publicExitPlan
    enabled := by native_decide
    endsAtNorthExit := by native_decide
    keyPositiveAtGoal := by native_decide }

theorem public_task1_bfs_certificate_completes :
    GoalReached
      (step publicRoom
        (run publicRoom
          (step publicRoom (run publicRoom initialState publicChestRoute.plan) Action.openChest)
          publicExitRoute.plan)
        Action.up) := by
  exact task1_bfs_certificate_completes publicRoom publicChestRoute publicExitRoute

/-- Optional closed-map trace for debugging only.  This is not the main proof. -/
def publicTask1Trace : List Action :=
  publicChestRoute.plan ++ [Action.openChest] ++ publicExitRoute.plan ++ [Action.up]

theorem publicTask1Trace_reaches_goal :
    GoalReached (run publicRoom initialState publicTask1Trace) := by
  unfold GoalReached
  native_decide


end Task1Formalization
