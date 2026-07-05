/-
  Environment formalization for `mathematical_logic/task_5`.

  Task 5 is a four-room exploration task with mixed mechanics:

  * press the start-room button to unlock the south conditional exit;
  * go south and open the key chest;
  * return to the start room and use the east locked exit;
  * explore west and east rooms;
  * open every visible chest in the dungeon.

  In the Python engine, world completion is triggered when all visible chests are
  open and the map does not use an explicit `complete_task` exit. This file
  formalizes that room-level logic.

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

namespace Task5EnvironmentFormalization

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

def allChestsOpened (s : EnvState) : Prop :=
  s.startChestOpened = true ∧
  s.southChestOpened = true ∧
  s.eastChestOpened = true ∧
  s.westChestOpened = true

def GoalReached (s : EnvState) : Prop :=
  allChestsOpened s

def step (s : EnvState) : Action → EnvState
  | Action.pressButton =>
      if s.room = Room.startRoom then
        { s with buttonPressed := true }
      else
        s
  | Action.goSouth =>
      if s.room = Room.startRoom ∧ s.buttonPressed = true then
        { s with room := Room.southRoom }
      else
        s
  | Action.goNorth =>
      if s.room = Room.southRoom then
        { s with room := Room.startRoom }
      else
        s
  | Action.goEast =>
      if s.room = Room.startRoom ∧ s.keys > 0 then
        { s with room := Room.eastRoom, keys := s.keys - 1 }
      else if s.room = Room.westRoom then
        { s with room := Room.startRoom }
      else
        s
  | Action.goWest =>
      if s.room = Room.startRoom then
        { s with room := Room.westRoom }
      else if s.room = Room.eastRoom then
        { s with room := Room.startRoom }
      else
        s
  | Action.openChest =>
      match s.room with
      | Room.startRoom =>
          if s.startChestOpened = false then
            { s with startChestOpened := true }
          else
            s
      | Room.southRoom =>
          if s.southChestOpened = false then
            { s with southChestOpened := true, keys := s.keys + 1 }
          else
            s
      | Room.eastRoom =>
          if s.eastChestOpened = false then
            { s with eastChestOpened := true, hp := s.hp + 1 }
          else
            s
      | Room.westRoom =>
          if s.westChestOpened = false then
            { s with westChestOpened := true }
          else
            s
  | Action.wait => s

def run : EnvState → List Action → EnvState
  | s, [] => s
  | s, a :: rest => run (step s a) rest

theorem south_exit_blocked_without_button
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hButton : s.buttonPressed = false) :
    step s Action.goSouth = s := by
  simp [step, hRoom, hButton]

theorem pressButton_enables_south_progress
    {s : EnvState}
    (hRoom : s.room = Room.startRoom) :
    (step s Action.pressButton).buttonPressed = true := by
  simp [step, hRoom]

theorem south_chest_grants_key
    {s : EnvState}
    (hRoom : s.room = Room.southRoom)
    (hChest : s.southChestOpened = false) :
    (step s Action.openChest).keys = s.keys + 1 := by
  simp [step, hRoom, hChest]

theorem east_exit_consumes_key
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hKeys : s.keys > 0) :
    let t := step s Action.goEast
    t.room = Room.eastRoom ∧ t.keys = s.keys - 1 := by
  simp [step, hRoom, hKeys]

theorem goal_equals_all_chests_opened
    {s : EnvState} :
    GoalReached s ↔
      s.startChestOpened = true ∧
      s.southChestOpened = true ∧
      s.eastChestOpened = true ∧
      s.westChestOpened = true := by
  rfl

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
  simp [GoalReached, allChestsOpened, witnessPlan_executes_to_finalState, finalState]

theorem task5_completable :
    ∃ plan, GoalReached (run initialState plan) := by
  exact ⟨witnessPlan, witnessPlan_reaches_goal⟩

end Task5EnvironmentFormalization
