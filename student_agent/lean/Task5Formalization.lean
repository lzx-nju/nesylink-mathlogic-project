/-
  Environment formalization for `mathematical_logic/task_5`.

  Task 5 is a four-room exploration task with mixed mechanics:

  * press the start-room button to unlock the south conditional exit;
  * go south and open the key chest;
  * return to the start room and use the east locked exit (consumes key);
  * explore west and east rooms;
  * open every visible chest in the dungeon.

  In the Python engine, world completion is triggered when all visible chests are
  open and the map does not use an explicit `complete_task` exit. This file
  formalizes that room-level logic (see `progress.py:all_chests_opened` and
  `engine.py:106`).

  It intentionally abstracts away monster AI, trap collision geometry and the
  reward-side periodic HP drain. The focus is the symbolic environment layer that
  the planner must satisfy: button gating, key gating, chest opening and global
  completion.

  Python correspondence:
  * `nesylink/map_data/mathematical_logic/task_5/*.json`
  * `nesylink/core/mechanics/interactions.py`
  * `nesylink/core/mechanics/movement.py`
  * `nesylink/core/mechanics/progress.py`
  * `nesylink/core/mechanics/engine.py`
-/

namespace Task5Formalization

/-! ### Rooms, actions, state -/

inductive Room where
  | startRoom
  | southRoom
  | eastRoom
  | westRoom
  deriving DecidableEq, Repr

inductive Action where
  | pressButton
  | goSouth
  | goNorth
  | goEast
  | goWest
  | openChest
  | wait
  deriving DecidableEq, Repr

structure EnvState where
  room : Room
  buttonPressed : Bool
  keys : Nat
  hp : Nat
  startChestOpened : Bool
  southChestOpened : Bool
  eastChestOpened : Bool
  westChestOpened : Bool
  deriving DecidableEq, Repr

-- Spawn in room_0_0 (startRoom) per dungeon.json + room_0_0.json:default_spawn.
def initialState : EnvState :=
  {
    room := Room.startRoom
    buttonPressed := false
    keys := 0
    hp := 5
    startChestOpened := false
    southChestOpened := false
    eastChestOpened := false
    westChestOpened := false
  }

/-- World completion predicate: every visible chest has been opened.
    Aligns with `progress.py:all_chests_opened` (no hidden chests in task_5). -/
def allChestsOpened (s : EnvState) : Prop :=
  s.startChestOpened = true ∧
  s.southChestOpened = true ∧
  s.eastChestOpened = true ∧
  s.westChestOpened = true

def GoalReached (s : EnvState) : Prop :=
  allChestsOpened s

/-! ### Transition function -/

def step (s : EnvState) : Action → EnvState
  | Action.pressButton =>
      if s.room = Room.startRoom then
        { s with buttonPressed := true }
      else
        s
  | Action.goSouth =>
      -- room_0_0 south_exit: type=conditional, requires button_pressed=button_1.
      if s.room = Room.startRoom ∧ s.buttonPressed = true then
        { s with room := Room.southRoom }
      else
        s
  | Action.goNorth =>
      -- room_0_1 north_exit: type=normal.
      if s.room = Room.southRoom then
        { s with room := Room.startRoom }
      else
        s
  | Action.goEast =>
      -- startRoom east_exit: locked_key, consume_key=true.
      -- eastRoom west_exit: normal (returns to startRoom).
      if s.room = Room.startRoom ∧ s.keys > 0 then
        { s with room := Room.eastRoom, keys := s.keys - 1 }
      else if s.room = Room.westRoom then
        { s with room := Room.startRoom }
      else
        s
  | Action.goWest =>
      -- startRoom west_exit: normal.
      -- eastRoom west_exit: normal (returns to startRoom).
      if s.room = Room.startRoom then
        { s with room := Room.westRoom }
      else if s.room = Room.eastRoom then
        { s with room := Room.startRoom }
      else
        s
  | Action.openChest =>
      -- Each room has exactly one chest with distinct loot:
      --   startRoom: gold (no side effect)
      --   southRoom: key  (keys + 1)
      --   eastRoom:  heal (hp + 1)
      --   westRoom:  gold (no side effect)
      if s.room = Room.startRoom ∧ s.startChestOpened = false then
        { s with startChestOpened := true }
      else if s.room = Room.southRoom ∧ s.southChestOpened = false then
        { s with southChestOpened := true, keys := s.keys + 1 }
      else if s.room = Room.eastRoom ∧ s.eastChestOpened = false then
        { s with eastChestOpened := true, hp := s.hp + 1 }
      else if s.room = Room.westRoom ∧ s.westChestOpened = false then
        { s with westChestOpened := true }
      else
        s
  | Action.wait => s

def run : EnvState → List Action → EnvState
  | s, [] => s
  | s, a :: rest => run (step s a) rest

/-! ### Navigation lemmas -/

theorem pressButton_only_in_startRoom
    {s : EnvState} (hRoom : s.room ≠ Room.startRoom) :
    step s Action.pressButton = s := by
  simp [step, hRoom]

theorem pressButton_marks_pressed
    {s : EnvState} (hRoom : s.room = Room.startRoom) :
    (step s Action.pressButton).buttonPressed = true := by
  simp [step, hRoom]

theorem pressButton_preserves_room
    {s : EnvState} : (step s Action.pressButton).room = s.room := by
  by_cases h : s.room = Room.startRoom
  · simp [step, h]
  · simp [step, h]

theorem pressButton_preserves_keys
    {s : EnvState} : (step s Action.pressButton).keys = s.keys := by
  by_cases h : s.room = Room.startRoom
  · simp [step, h]
  · simp [step, h]

theorem pressButton_preserves_chests
    {s : EnvState} :
    (step s Action.pressButton).startChestOpened = s.startChestOpened ∧
    (step s Action.pressButton).southChestOpened = s.southChestOpened ∧
    (step s Action.pressButton).eastChestOpened = s.eastChestOpened ∧
    (step s Action.pressButton).westChestOpened = s.westChestOpened := by
  by_cases h : s.room = Room.startRoom
  · simp [step, h]
  · simp [step, h]

theorem goSouth_blocked_without_button
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hButton : s.buttonPressed = false) :
    step s Action.goSouth = s := by
  simp [step, hRoom, hButton]

theorem goSouth_succeeds_after_button
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hButton : s.buttonPressed = true) :
    (step s Action.goSouth).room = Room.southRoom := by
  simp [step, hRoom, hButton]

theorem goSouth_preserves_buttonPressed
    {s : EnvState} : (step s Action.goSouth).buttonPressed = s.buttonPressed := by
  by_cases h : s.room = Room.startRoom ∧ s.buttonPressed = true
  · simp [step, h]
  · simp [step, h]

theorem goSouth_preserves_keys
    {s : EnvState} : (step s Action.goSouth).keys = s.keys := by
  by_cases h : s.room = Room.startRoom ∧ s.buttonPressed = true
  · simp [step, h]
  · simp [step, h]

theorem goSouth_preserves_chests
    {s : EnvState} :
    (step s Action.goSouth).startChestOpened = s.startChestOpened ∧
    (step s Action.goSouth).southChestOpened = s.southChestOpened ∧
    (step s Action.goSouth).eastChestOpened = s.eastChestOpened ∧
    (step s Action.goSouth).westChestOpened = s.westChestOpened := by
  by_cases h : s.room = Room.startRoom ∧ s.buttonPressed = true
  · simp [step, h]
  · simp [step, h]

theorem goNorth_only_in_southRoom
    {s : EnvState} (hRoom : s.room ≠ Room.southRoom) :
    step s Action.goNorth = s := by
  simp [step, hRoom]

theorem goNorth_succeeds_in_southRoom
    {s : EnvState} (hRoom : s.room = Room.southRoom) :
    (step s Action.goNorth).room = Room.startRoom := by
  simp [step, hRoom]

theorem goNorth_preserves_buttonPressed
    {s : EnvState} : (step s Action.goNorth).buttonPressed = s.buttonPressed := by
  by_cases h : s.room = Room.southRoom
  · simp [step, h]
  · simp [step, h]

theorem goNorth_preserves_keys
    {s : EnvState} : (step s Action.goNorth).keys = s.keys := by
  by_cases h : s.room = Room.southRoom
  · simp [step, h]
  · simp [step, h]

theorem goNorth_preserves_chests
    {s : EnvState} :
    (step s Action.goNorth).startChestOpened = s.startChestOpened ∧
    (step s Action.goNorth).southChestOpened = s.southChestOpened ∧
    (step s Action.goNorth).eastChestOpened = s.eastChestOpened ∧
    (step s Action.goNorth).westChestOpened = s.westChestOpened := by
  by_cases h : s.room = Room.southRoom
  · simp [step, h]
  · simp [step, h]

theorem goEast_blocked_without_key
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hKeys : s.keys = 0) :
    step s Action.goEast = s := by
  simp [step, hRoom, hKeys]

theorem goEast_from_start_consumes_key
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hKeys : s.keys > 0) :
    (step s Action.goEast).room = Room.eastRoom ∧
    (step s Action.goEast).keys = s.keys - 1 := by
  simp [step, hRoom, hKeys]

theorem goEast_from_west_returns_to_start
    {s : EnvState}
    (hRoom : s.room = Room.westRoom) :
    (step s Action.goEast).room = Room.startRoom ∧
    (step s Action.goEast).keys = s.keys := by
  have h : ¬(s.room = Room.startRoom ∧ s.keys > 0) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom]

theorem goEast_preserves_buttonPressed
    {s : EnvState} : (step s Action.goEast).buttonPressed = s.buttonPressed := by
  by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
  · simp [step, h1]
  · by_cases h2 : s.room = Room.westRoom
    · simp [step, h2]
    · simp [step, h1, h2]

theorem goEast_preserves_chests
    {s : EnvState} :
    (step s Action.goEast).startChestOpened = s.startChestOpened ∧
    (step s Action.goEast).southChestOpened = s.southChestOpened ∧
    (step s Action.goEast).eastChestOpened = s.eastChestOpened ∧
    (step s Action.goEast).westChestOpened = s.westChestOpened := by
  by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
  · simp [step, h1]
  · by_cases h2 : s.room = Room.westRoom
    · simp [step, h2]
    · simp [step, h1, h2]

theorem goWest_from_start_to_west
    {s : EnvState}
    (hRoom : s.room = Room.startRoom) :
    (step s Action.goWest).room = Room.westRoom ∧
    (step s Action.goWest).keys = s.keys := by
  simp [step, hRoom]

theorem goWest_from_east_returns_to_start
    {s : EnvState}
    (hRoom : s.room = Room.eastRoom) :
    (step s Action.goWest).room = Room.startRoom ∧
    (step s Action.goWest).keys = s.keys := by
  have h : ¬s.room = Room.startRoom := by
    intro hh; rw [hh] at hRoom; simp at hRoom
  simp [step, hRoom]

theorem goWest_preserves_buttonPressed
    {s : EnvState} : (step s Action.goWest).buttonPressed = s.buttonPressed := by
  by_cases h1 : s.room = Room.startRoom
  · simp [step, h1]
  · by_cases h2 : s.room = Room.eastRoom
    · simp [step, h2]
    · simp [step, h1, h2]

theorem goWest_preserves_keys
    {s : EnvState} : (step s Action.goWest).keys = s.keys := by
  by_cases h1 : s.room = Room.startRoom
  · simp [step, h1]
  · by_cases h2 : s.room = Room.eastRoom
    · simp [step, h2]
    · simp [step, h1, h2]

theorem goWest_preserves_chests
    {s : EnvState} :
    (step s Action.goWest).startChestOpened = s.startChestOpened ∧
    (step s Action.goWest).southChestOpened = s.southChestOpened ∧
    (step s Action.goWest).eastChestOpened = s.eastChestOpened ∧
    (step s Action.goWest).westChestOpened = s.westChestOpened := by
  by_cases h1 : s.room = Room.startRoom
  · simp [step, h1]
  · by_cases h2 : s.room = Room.eastRoom
    · simp [step, h2]
    · simp [step, h1, h2]

/-! ### Chest lemmas -/

theorem openChest_start_marks_opened
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hChest : s.startChestOpened = false) :
    (step s Action.openChest).startChestOpened = true ∧
    (step s Action.openChest).room = Room.startRoom ∧
    (step s Action.openChest).keys = s.keys ∧
    (step s Action.openChest).hp = s.hp := by
  have h2 : ¬(s.room = Room.southRoom ∧ s.southChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h3 : ¬(s.room = Room.eastRoom ∧ s.eastChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h4 : ¬(s.room = Room.westRoom ∧ s.westChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom, hChest]

theorem openChest_start_already_opened
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hChest : s.startChestOpened = true) :
    step s Action.openChest = s := by
  have h1 : ¬(s.room = Room.startRoom ∧ s.startChestOpened = false) := by
    intro h; rw [hChest] at h; simp at h
  have h2 : ¬(s.room = Room.southRoom ∧ s.southChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h3 : ¬(s.room = Room.eastRoom ∧ s.eastChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h4 : ¬(s.room = Room.westRoom ∧ s.westChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, h1, h2, h3, h4]

theorem openChest_south_grants_key
    {s : EnvState}
    (hRoom : s.room = Room.southRoom)
    (hChest : s.southChestOpened = false) :
    (step s Action.openChest).southChestOpened = true ∧
    (step s Action.openChest).keys = s.keys + 1 ∧
    (step s Action.openChest).room = Room.southRoom := by
  have h1 : ¬(s.room = Room.startRoom ∧ s.startChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h3 : ¬(s.room = Room.eastRoom ∧ s.eastChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h4 : ¬(s.room = Room.westRoom ∧ s.westChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom, hChest]

theorem openChest_south_already_opened
    {s : EnvState}
    (hRoom : s.room = Room.southRoom)
    (hChest : s.southChestOpened = true) :
    step s Action.openChest = s := by
  have h1 : ¬(s.room = Room.startRoom ∧ s.startChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h2 : ¬(s.room = Room.southRoom ∧ s.southChestOpened = false) := by
    intro h; rw [hChest] at h; simp at h
  have h3 : ¬(s.room = Room.eastRoom ∧ s.eastChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h4 : ¬(s.room = Room.westRoom ∧ s.westChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, h1, h2, h3, h4]

theorem openChest_east_heals
    {s : EnvState}
    (hRoom : s.room = Room.eastRoom)
    (hChest : s.eastChestOpened = false) :
    (step s Action.openChest).eastChestOpened = true ∧
    (step s Action.openChest).hp = s.hp + 1 ∧
    (step s Action.openChest).room = Room.eastRoom ∧
    (step s Action.openChest).keys = s.keys := by
  have h1 : ¬(s.room = Room.startRoom ∧ s.startChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h2 : ¬(s.room = Room.southRoom ∧ s.southChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h4 : ¬(s.room = Room.westRoom ∧ s.westChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom, hChest]

theorem openChest_east_already_opened
    {s : EnvState}
    (hRoom : s.room = Room.eastRoom)
    (hChest : s.eastChestOpened = true) :
    step s Action.openChest = s := by
  have h1 : ¬(s.room = Room.startRoom ∧ s.startChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h2 : ¬(s.room = Room.southRoom ∧ s.southChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h3 : ¬(s.room = Room.eastRoom ∧ s.eastChestOpened = false) := by
    intro h; rw [hChest] at h; simp at h
  have h4 : ¬(s.room = Room.westRoom ∧ s.westChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, h1, h2, h3, h4]

theorem openChest_west_marks_opened
    {s : EnvState}
    (hRoom : s.room = Room.westRoom)
    (hChest : s.westChestOpened = false) :
    (step s Action.openChest).westChestOpened = true ∧
    (step s Action.openChest).room = Room.westRoom ∧
    (step s Action.openChest).keys = s.keys ∧
    (step s Action.openChest).hp = s.hp := by
  have h1 : ¬(s.room = Room.startRoom ∧ s.startChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h2 : ¬(s.room = Room.southRoom ∧ s.southChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h3 : ¬(s.room = Room.eastRoom ∧ s.eastChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  simp [step, hRoom, hChest]

theorem openChest_west_already_opened
    {s : EnvState}
    (hRoom : s.room = Room.westRoom)
    (hChest : s.westChestOpened = true) :
    step s Action.openChest = s := by
  have h1 : ¬(s.room = Room.startRoom ∧ s.startChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h2 : ¬(s.room = Room.southRoom ∧ s.southChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h3 : ¬(s.room = Room.eastRoom ∧ s.eastChestOpened = false) := by
    intro h; rw [hRoom] at h; simp at h
  have h4 : ¬(s.room = Room.westRoom ∧ s.westChestOpened = false) := by
    intro h; rw [hChest] at h; simp at h
  simp [step, h1, h2, h3, h4]

theorem openChest_preserves_buttonPressed
    {s : EnvState} :
    (step s Action.openChest).buttonPressed = s.buttonPressed := by
  by_cases h1 : s.room = Room.startRoom ∧ s.startChestOpened = false
  · simp [step, h1]
  · by_cases h2 : s.room = Room.southRoom ∧ s.southChestOpened = false
    · simp [step, h2]
    · by_cases h3 : s.room = Room.eastRoom ∧ s.eastChestOpened = false
      · simp [step, h3]
      · by_cases h4 : s.room = Room.westRoom ∧ s.westChestOpened = false
        · simp [step, h4]
        · simp [step, h1, h2, h3, h4]

theorem openChest_preserves_room
    {s : EnvState} : (step s Action.openChest).room = s.room := by
  by_cases h1 : s.room = Room.startRoom ∧ s.startChestOpened = false
  · simp [step, h1]
  · by_cases h2 : s.room = Room.southRoom ∧ s.southChestOpened = false
    · simp [step, h2]
    · by_cases h3 : s.room = Room.eastRoom ∧ s.eastChestOpened = false
      · simp [step, h3]
      · by_cases h4 : s.room = Room.westRoom ∧ s.westChestOpened = false
        · simp [step, h4]
        · simp [step, h1, h2, h3, h4]

/-! ### Necessity lemmas (action-wise invariants) -/

/-- Only `pressButton` can change `buttonPressed`. -/
theorem only_pressButton_changes_buttonPressed
    {s : EnvState} (a : Action) (ha : a ≠ Action.pressButton) :
    (step s a).buttonPressed = s.buttonPressed := by
  cases a with
  | pressButton => exact absurd rfl ha
  | goSouth => exact goSouth_preserves_buttonPressed
  | goNorth => exact goNorth_preserves_buttonPressed
  | goEast => exact goEast_preserves_buttonPressed
  | goWest => exact goWest_preserves_buttonPressed
  | openChest => exact openChest_preserves_buttonPressed
  | wait => simp [step]

/-- Only `openChest` can change `startChestOpened`. -/
theorem only_openChest_changes_startChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).startChestOpened = s.startChestOpened := by
  cases a with
  | pressButton =>
    have := pressButton_preserves_chests (s := s)
    rcases this with ⟨h, _, _, _⟩; exact h
  | goSouth =>
    have := goSouth_preserves_chests (s := s)
    rcases this with ⟨h, _, _, _⟩; exact h
  | goNorth =>
    have := goNorth_preserves_chests (s := s)
    rcases this with ⟨h, _, _, _⟩; exact h
  | goEast =>
    have := goEast_preserves_chests (s := s)
    rcases this with ⟨h, _, _, _⟩; exact h
  | goWest =>
    have := goWest_preserves_chests (s := s)
    rcases this with ⟨h, _, _, _⟩; exact h
  | openChest => exact absurd rfl ha
  | wait => simp [step]

/-- Only `openChest` can change `southChestOpened`. -/
theorem only_openChest_changes_southChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).southChestOpened = s.southChestOpened := by
  cases a with
  | pressButton =>
    have := pressButton_preserves_chests (s := s)
    rcases this with ⟨_, h, _, _⟩; exact h
  | goSouth =>
    have := goSouth_preserves_chests (s := s)
    rcases this with ⟨_, h, _, _⟩; exact h
  | goNorth =>
    have := goNorth_preserves_chests (s := s)
    rcases this with ⟨_, h, _, _⟩; exact h
  | goEast =>
    have := goEast_preserves_chests (s := s)
    rcases this with ⟨_, h, _, _⟩; exact h
  | goWest =>
    have := goWest_preserves_chests (s := s)
    rcases this with ⟨_, h, _, _⟩; exact h
  | openChest => exact absurd rfl ha
  | wait => simp [step]

/-- Only `openChest` can change `eastChestOpened`. -/
theorem only_openChest_changes_eastChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).eastChestOpened = s.eastChestOpened := by
  cases a with
  | pressButton =>
    have := pressButton_preserves_chests (s := s)
    rcases this with ⟨_, _, h, _⟩; exact h
  | goSouth =>
    have := goSouth_preserves_chests (s := s)
    rcases this with ⟨_, _, h, _⟩; exact h
  | goNorth =>
    have := goNorth_preserves_chests (s := s)
    rcases this with ⟨_, _, h, _⟩; exact h
  | goEast =>
    have := goEast_preserves_chests (s := s)
    rcases this with ⟨_, _, h, _⟩; exact h
  | goWest =>
    have := goWest_preserves_chests (s := s)
    rcases this with ⟨_, _, h, _⟩; exact h
  | openChest => exact absurd rfl ha
  | wait => simp [step]

/-- Only `openChest` can change `westChestOpened`. -/
theorem only_openChest_changes_westChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).westChestOpened = s.westChestOpened := by
  cases a with
  | pressButton =>
    have := pressButton_preserves_chests (s := s)
    rcases this with ⟨_, _, _, h⟩; exact h
  | goSouth =>
    have := goSouth_preserves_chests (s := s)
    rcases this with ⟨_, _, _, h⟩; exact h
  | goNorth =>
    have := goNorth_preserves_chests (s := s)
    rcases this with ⟨_, _, _, h⟩; exact h
  | goEast =>
    have := goEast_preserves_chests (s := s)
    rcases this with ⟨_, _, _, h⟩; exact h
  | goWest =>
    have := goWest_preserves_chests (s := s)
    rcases this with ⟨_, _, _, h⟩; exact h
  | openChest => exact absurd rfl ha
  | wait => simp [step]

/-- Only `goEast` (from startRoom) and `openChest` (in southRoom) can change `keys`. -/
theorem non_goEast_non_openChest_preserves_keys
    {s : EnvState} (a : Action)
    (ha : a ≠ Action.goEast) (ha' : a ≠ Action.openChest) :
    (step s a).keys = s.keys := by
  cases a with
  | pressButton => exact pressButton_preserves_keys
  | goSouth => exact goSouth_preserves_keys
  | goNorth => exact goNorth_preserves_keys
  | goEast => exact absurd rfl ha
  | goWest => exact goWest_preserves_keys
  | openChest => exact absurd rfl ha'
  | wait => simp [step]

/-- Only `openChest` (in eastRoom) can change `hp`. -/
theorem non_openChest_preserves_hp
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).hp = s.hp := by
  cases a with
  | pressButton =>
    by_cases h : s.room = Room.startRoom
    · simp [step, h]
    · simp [step, h]
  | goSouth =>
    by_cases h : s.room = Room.startRoom ∧ s.buttonPressed = true
    · simp [step, h]
    · simp [step, h]
  | goNorth =>
    by_cases h : s.room = Room.southRoom
    · simp [step, h]
    · simp [step, h]
  | goEast =>
    by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
    · simp [step, h1]
    · by_cases h2 : s.room = Room.westRoom
      · simp [step, h2]
      · simp [step, h1, h2]
  | goWest =>
    by_cases h1 : s.room = Room.startRoom
    · simp [step, h1]
    · by_cases h2 : s.room = Room.eastRoom
      · simp [step, h2]
      · simp [step, h1, h2]
  | openChest => exact absurd rfl ha
  | wait => simp [step]

/-! ### Reachable states and invariants -/

/-- Reachability: states reachable from `initialState` via arbitrary actions. -/
inductive Reachable : EnvState → Prop where
  | init : Reachable initialState
  | step (s : EnvState) (a : Action) : Reachable s → Reachable (step s a)

/-- Invariant: if `buttonPressed = false`, then the player is not in southRoom
    and the south chest has not been opened. Equivalently (contrapositive):
    being in southRoom or having opened the south chest implies the button was
    pressed. This captures the gating effect of the conditional south exit. -/
theorem buttonPressed_false_implies_not_in_south_and_chest_closed
    {s : EnvState} (hr : Reachable s) :
    s.buttonPressed = false →
    s.room ≠ Room.southRoom ∧ s.southChestOpened = false := by
  induction hr with
  | init => simp [initialState]
  | step s a hr ih =>
    intro hb
    cases a with
    | pressButton =>
      by_cases h : s.room = Room.startRoom
      · simp [step, h] at hb
      · have hstep : step s Action.pressButton = s := by simp [step, h]
        rw [hstep] at hb ⊢; exact ih hb
    | goSouth =>
      by_cases h : s.room = Room.startRoom ∧ s.buttonPressed = true
      · simp [step, h] at hb
      · have hstep : step s Action.goSouth = s := by simp [step, h]
        rw [hstep] at hb ⊢; exact ih hb
    | goNorth =>
      by_cases h : s.room = Room.southRoom
      · have hp := goNorth_preserves_buttonPressed (s := s)
        rw [hp] at hb
        have ⟨hnot, _⟩ := ih hb
        exact absurd h hnot
      · have hstep : step s Action.goNorth = s := by simp [step, h]
        rw [hstep] at hb ⊢; exact ih hb
    | goEast =>
      have hp := goEast_preserves_buttonPressed (s := s)
      rw [hp] at hb
      have ⟨hnot, hchest⟩ := ih hb
      by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
      · constructor
        · simp [step, h1];
        · have hp2 := goEast_preserves_chests (s := s)
          rcases hp2 with ⟨_, hsc, _, _⟩
          rw [hsc]; exact hchest
      · by_cases h2 : s.room = Room.westRoom
        · constructor
          · simp [step, h2];
          · have hp2 := goEast_preserves_chests (s := s)
            rcases hp2 with ⟨_, hsc, _, _⟩
            rw [hsc]; exact hchest
        · have hstep : step s Action.goEast = s := by simp [step, h1, h2]
          rw [hstep]; exact ⟨hnot, hchest⟩
    | goWest =>
      have hp := goWest_preserves_buttonPressed (s := s)
      rw [hp] at hb
      have ⟨hnot, hchest⟩ := ih hb
      by_cases h1 : s.room = Room.startRoom
      · constructor
        · simp [step, h1];
        · have hp2 := goWest_preserves_chests (s := s)
          rcases hp2 with ⟨_, hsc, _, _⟩
          rw [hsc]; exact hchest
      · by_cases h2 : s.room = Room.eastRoom
        · constructor
          · simp [step, h2];
          · have hp2 := goWest_preserves_chests (s := s)
            rcases hp2 with ⟨_, hsc, _, _⟩
            rw [hsc]; exact hchest
        · have hstep : step s Action.goWest = s := by simp [step, h1, h2]
          rw [hstep]; exact ⟨hnot, hchest⟩
    | openChest =>
      have hp := openChest_preserves_buttonPressed (s := s)
      rw [hp] at hb
      have ⟨hnot, hchest⟩ := ih hb
      constructor
      · have hp2 := openChest_preserves_room (s := s)
        rw [hp2]; exact hnot
      · by_cases hs : s.room = Room.southRoom ∧ s.southChestOpened = false
        · exact absurd hs.1 hnot
        · have hp2 : (step s Action.openChest).southChestOpened = s.southChestOpened := by
            by_cases h1 : s.room = Room.startRoom ∧ s.startChestOpened = false
            · simp [step, h1]
            · by_cases h2 : s.room = Room.southRoom ∧ s.southChestOpened = false
              · exact absurd h2 hs
              · by_cases h3 : s.room = Room.eastRoom ∧ s.eastChestOpened = false
                · simp [step, h3]
                · by_cases h4 : s.room = Room.westRoom ∧ s.westChestOpened = false
                  · simp [step, h4]
                  · simp [step, h1, h2, h3, h4]
          rw [hp2]; exact hchest
    | wait =>
      simp [step] at hb ⊢; exact ih hb

/-- If a reachable state has `southChestOpened = true`, then `buttonPressed = true`. -/
theorem southChestOpened_implies_buttonPressed
    {s : EnvState} (hr : Reachable s) :
    s.southChestOpened = true → s.buttonPressed = true := by
  intro hc
  by_cases hb : s.buttonPressed = false
  · have := buttonPressed_false_implies_not_in_south_and_chest_closed hr hb
    rcases this with ⟨_, hchest⟩
    rw [hc] at hchest; simp at hchest
  · simp [hb]

/-- Invariant: if `southChestOpened = false`, then `keys = 0`.
    The south chest is the only source of keys, and `goEast` (the only key
    consumer) requires `keys > 0` to fire, so before the chest is opened no
    key can exist. -/
theorem southChestClosed_implies_keys_zero
    {s : EnvState} (hr : Reachable s) :
    s.southChestOpened = false → s.keys = 0 := by
  induction hr with
  | init => simp [initialState]
  | step s a hr ih =>
    intro hc
    cases a with
    | pressButton =>
      have hpres : (step s Action.pressButton).southChestOpened = s.southChestOpened := by
        have := pressButton_preserves_chests (s := s)
        rcases this with ⟨_, h, _, _⟩; exact h
      rw [hpres] at hc
      have hpresk : (step s Action.pressButton).keys = s.keys := pressButton_preserves_keys
      rw [hpresk]
      exact ih hc
    | goSouth =>
      have hpres : (step s Action.goSouth).southChestOpened = s.southChestOpened := by
        have := goSouth_preserves_chests (s := s)
        rcases this with ⟨_, h, _, _⟩; exact h
      rw [hpres] at hc
      have hpresk : (step s Action.goSouth).keys = s.keys := goSouth_preserves_keys
      rw [hpresk]
      exact ih hc
    | goNorth =>
      have hpres : (step s Action.goNorth).southChestOpened = s.southChestOpened := by
        have := goNorth_preserves_chests (s := s)
        rcases this with ⟨_, h, _, _⟩; exact h
      rw [hpres] at hc
      have hpresk : (step s Action.goNorth).keys = s.keys := goNorth_preserves_keys
      rw [hpresk]
      exact ih hc
    | goEast =>
      have hpres : (step s Action.goEast).southChestOpened = s.southChestOpened := by
        have := goEast_preserves_chests (s := s)
        rcases this with ⟨_, h, _, _⟩; exact h
      rw [hpres] at hc
      -- goEast changes keys only when fired from startRoom with keys>0.
      -- If fired, then s.keys > 0, so by ih s.southChestOpened = true,
      -- contradicting hc.
      by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
      · have hkey : s.keys > 0 := h1.2
        have hsc : s.southChestOpened = true := by
          by_cases hclosed : s.southChestOpened = false
          · have hzero := ih hclosed
            rw [hzero] at hkey; simp at hkey
          · simp [hclosed]
        rw [hsc] at hc; simp at hc
      · -- goEast was a no-op or westRoom→startRoom; keys unchanged.
        have hpresk : (step s Action.goEast).keys = s.keys := by
          by_cases h2 : s.room = Room.westRoom
          · have := goEast_from_west_returns_to_start (hRoom := h2)
            rcases this with ⟨_, hk⟩; exact hk
          · simp [step, h1, h2]
        rw [hpresk]
        exact ih hc
    | goWest =>
      have hpres : (step s Action.goWest).southChestOpened = s.southChestOpened := by
        have := goWest_preserves_chests (s := s)
        rcases this with ⟨_, h, _, _⟩; exact h
      rw [hpres] at hc
      have hpresk : (step s Action.goWest).keys = s.keys := goWest_preserves_keys
      rw [hpresk]
      exact ih hc
    | openChest =>
      by_cases hs : s.room = Room.southRoom ∧ s.southChestOpened = false
      · -- south branch fires: southChestOpened becomes true, contradicting hc.
        have hfires : (step s Action.openChest).southChestOpened = true := by
          by_cases h1 : s.room = Room.startRoom ∧ s.startChestOpened = false
          · rw [hs.1] at h1; simp at h1
          · simp [step, hs]
        rw [hfires] at hc; simp at hc
      · -- non-south branch: southChestOpened and keys both unchanged.
        have hpres_sc : (step s Action.openChest).southChestOpened = s.southChestOpened := by
          by_cases h1 : s.room = Room.startRoom ∧ s.startChestOpened = false
          · simp [step, h1]
          · by_cases h2 : s.room = Room.southRoom ∧ s.southChestOpened = false
            · exact absurd h2 hs
            · by_cases h3 : s.room = Room.eastRoom ∧ s.eastChestOpened = false
              · simp [step, h3]
              · by_cases h4 : s.room = Room.westRoom ∧ s.westChestOpened = false
                · simp [step, h4]
                · simp [step, h1, h2, h3, h4]
        have hpres_k : (step s Action.openChest).keys = s.keys := by
          by_cases h1 : s.room = Room.startRoom ∧ s.startChestOpened = false
          · simp [step, h1]
          · by_cases h2 : s.room = Room.southRoom ∧ s.southChestOpened = false
            · exact absurd h2 hs
            · by_cases h3 : s.room = Room.eastRoom ∧ s.eastChestOpened = false
              · simp [step, h3]
              · by_cases h4 : s.room = Room.westRoom ∧ s.westChestOpened = false
                · simp [step, h4]
                · simp [step, h1, h2, h3, h4]
        rw [hpres_sc] at hc
        rw [hpres_k]
        exact ih hc
    | wait =>
      simp [step] at hc
      simp [step]
      exact ih hc

/-- If a reachable state has `GoalReached`, then the button was pressed. -/
theorem completion_postcondition
    {s : EnvState} (hr : Reachable s) (hc : GoalReached s) :
    s.buttonPressed = true := by
  unfold GoalReached allChestsOpened at hc
  rcases hc with ⟨_, hsc, _, _⟩
  exact southChestOpened_implies_buttonPressed hr hsc

/-! ### Witness plan -/

-- Room-level route:
--   startRoom: openChest (start chest)
--   → pressButton
--   → goSouth (button gating)
--   southRoom: openChest (key chest, keys + 1)
--   → goNorth
--   startRoom: goEast (locked_key, consume_key=true, keys - 1)
--   eastRoom: openChest (heal chest, hp + 1)
--   → goWest (back to startRoom)
--   startRoom: goWest (normal exit to westRoom)
--   westRoom: openChest (gold chest)
def witnessPlan : List Action :=
  [
    Action.openChest,
    Action.pressButton,
    Action.goSouth,
    Action.openChest,
    Action.goNorth,
    Action.goEast,
    Action.openChest,
    Action.goWest,
    Action.goWest,
    Action.openChest
  ]

def finalState : EnvState :=
  {
    room := Room.westRoom
    buttonPressed := true
    keys := 0
    hp := 6
    startChestOpened := true
    southChestOpened := true
    eastChestOpened := true
    westChestOpened := true
  }

theorem witnessPlan_executes_to_finalState :
    run initialState witnessPlan = finalState := by
  rfl

theorem witnessPlan_reaches_goal :
    GoalReached (run initialState witnessPlan) := by
  rw [witnessPlan_executes_to_finalState]
  simp [GoalReached, allChestsOpened, finalState]

theorem task5_completable :
    ∃ plan, GoalReached (run initialState plan) := by
  exact ⟨witnessPlan, witnessPlan_reaches_goal⟩

/-! ### Symbolic policy formalization -/

/--
The abstract stage machine behind the task 5 baseline. This is the symbolic
counterpart of the Python `task5_stage` routine: it ignores pixel-level
waypoints and keeps only the high-level subgoal ordering that matters for the
environment proof.
-/
inductive PolicyStage where
  | openStartChest
  | pressStartButton
  | openSouthChest
  | openEastChest
  | openWestChest
  | done
  deriving DecidableEq, Repr

def policyStage (s : EnvState) : PolicyStage :=
  if s.startChestOpened = false then
    PolicyStage.openStartChest
  else if s.buttonPressed = false then
    PolicyStage.pressStartButton
  else if s.southChestOpened = false then
    PolicyStage.openSouthChest
  else if s.eastChestOpened = false then
    PolicyStage.openEastChest
  else if s.westChestOpened = false then
    PolicyStage.openWestChest
  else
    PolicyStage.done

/--
State-driven room-level policy. It maps the current symbolic state to the next
high-level action, including navigation actions that return to the start room
when the current stage needs a different room.
-/
def symbolicPolicy (s : EnvState) : Action :=
  match policyStage s with
  | PolicyStage.openStartChest =>
      match s.room with
      | Room.startRoom => Action.openChest
      | Room.southRoom => Action.goNorth
      | Room.eastRoom => Action.goWest
      | Room.westRoom => Action.goEast
  | PolicyStage.pressStartButton =>
      match s.room with
      | Room.startRoom => Action.pressButton
      | Room.southRoom => Action.goNorth
      | Room.eastRoom => Action.goWest
      | Room.westRoom => Action.goEast
  | PolicyStage.openSouthChest =>
      match s.room with
      | Room.startRoom =>
          if s.buttonPressed = true then Action.goSouth else Action.pressButton
      | Room.southRoom => Action.openChest
      | Room.eastRoom => Action.goWest
      | Room.westRoom => Action.goEast
  | PolicyStage.openEastChest =>
      match s.room with
      | Room.startRoom =>
          if s.keys > 0 then Action.goEast else Action.wait
      | Room.southRoom => Action.goNorth
      | Room.eastRoom => Action.openChest
      | Room.westRoom => Action.goEast
  | PolicyStage.openWestChest =>
      match s.room with
      | Room.startRoom => Action.goWest
      | Room.southRoom => Action.goNorth
      | Room.eastRoom => Action.goWest
      | Room.westRoom => Action.openChest
  | PolicyStage.done => Action.wait

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

/-- Legal-action predicate for the symbolic transition layer. -/
def ActionEnabled (s : EnvState) : Action → Prop
  | Action.pressButton => s.room = Room.startRoom
  | Action.goSouth => s.room = Room.startRoom ∧ s.buttonPressed = true
  | Action.goNorth => s.room = Room.southRoom
  | Action.goEast =>
      (s.room = Room.startRoom ∧ s.keys > 0) ∨ s.room = Room.westRoom
  | Action.goWest => s.room = Room.startRoom ∨ s.room = Room.eastRoom
  | Action.openChest =>
      (s.room = Room.startRoom ∧ s.startChestOpened = false) ∨
      (s.room = Room.southRoom ∧ s.southChestOpened = false) ∨
      (s.room = Room.eastRoom ∧ s.eastChestOpened = false) ∨
      (s.room = Room.westRoom ∧ s.westChestOpened = false)
  | Action.wait => True

def actionsEnabledAlong : EnvState → List Action → Prop
  | _, [] => True
  | s, a :: rest => ActionEnabled s a ∧ actionsEnabledAlong (step s a) rest

theorem policyTrace_10_matches_witnessPlan :
    policyTrace 10 initialState = witnessPlan := by
  native_decide

theorem policyTrace_10_actions_enabled :
    actionsEnabledAlong initialState (policyTrace 10 initialState) := by
  simp [policyTrace, symbolicPolicy, policyStage, actionsEnabledAlong,
    ActionEnabled, initialState, step]

theorem symbolicPolicy_run_10_finalState :
    runPolicy 10 initialState = finalState := by
  native_decide

theorem symbolicPolicy_reaches_goal :
    GoalReached (runPolicy 10 initialState) := by
  rw [symbolicPolicy_run_10_finalState]
  simp [GoalReached, allChestsOpened, finalState]

theorem task5_symbolicPolicy_completes :
    ∃ n, GoalReached (runPolicy n initialState) := by
  exact ⟨10, symbolicPolicy_reaches_goal⟩

end Task5Formalization
