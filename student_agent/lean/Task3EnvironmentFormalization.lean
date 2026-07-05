/-
  Environment formalization for `mathematical_logic/task_3`.

  Task 3 is the first multi-room return task:

  * start in `start_room`;
  * move west through `monster_hall`;
  * reach `key_room` and open the chest;
  * return east to `start_room`;
  * use the locked east exit with the collected key.

  The Python engine contains a chaser monster in `monster_hall`, but the task's
  high-level requirement is a room-to-room subgoal chain rather than monster
  elimination. This Lean model therefore keeps the monster as part of the state
  but abstracts away combat and continuous motion.

  Python correspondence:
  * `nesylink/map_data/mathematical_logic/task_3/*.json`
  * `nesylink/core/mechanics/interactions.py`
  * `nesylink/core/mechanics/movement.py`
-/

namespace Task3EnvironmentFormalization

inductive Room where
  | startRoom
  | monsterHall
  | keyRoom
  deriving DecidableEq, Repr

inductive Action where
  | goWest
  | goEast
  | openChest
  | openLockedExit
  | wait
  deriving DecidableEq, Repr

structure EnvState where
  room : Room
  keys : Nat
  keyChestOpened : Bool
  hallMonsterAlive : Bool
  completed : Bool
  deriving DecidableEq, Repr

def initialState : EnvState :=
  {
    room := Room.startRoom
    keys := 0
    keyChestOpened := false
    hallMonsterAlive := true
    completed := false
  }

def GoalReached (s : EnvState) : Prop :=
  s.completed = true

def step (s : EnvState) : Action → EnvState
  | Action.goWest =>
      match s.room with
      | Room.startRoom => { s with room := Room.monsterHall }
      | Room.monsterHall => { s with room := Room.keyRoom }
      | Room.keyRoom => s
  | Action.goEast =>
      match s.room with
      | Room.keyRoom => { s with room := Room.monsterHall }
      | Room.monsterHall => { s with room := Room.startRoom }
      | Room.startRoom => s
  | Action.openChest =>
      if s.room = Room.keyRoom ∧ s.keyChestOpened = false then
        { s with keyChestOpened := true, keys := s.keys + 1 }
      else
        s
  | Action.openLockedExit =>
      if s.room = Room.startRoom ∧ s.keys > 0 then
        { s with keys := s.keys - 1, completed := true }
      else
        s
  | Action.wait => s

def run : EnvState → List Action → EnvState
  | s, [] => s
  | s, a :: rest => run (step s a) rest

theorem west_then_west_reaches_keyRoom :
    (run initialState [Action.goWest, Action.goWest]).room = Room.keyRoom := by
  rfl

theorem openChest_in_keyRoom_increases_keys
    {s : EnvState}
    (hRoom : s.room = Room.keyRoom)
    (hChest : s.keyChestOpened = false) :
    (step s Action.openChest).keys = s.keys + 1 := by
  simp [step, hRoom, hChest]

theorem openLockedExit_blocked_without_key
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hKeys : s.keys = 0) :
    step s Action.openLockedExit = s := by
  simp [step, hRoom, hKeys]

theorem openLockedExit_consumes_key_and_completes
    {s : EnvState}
    (hRoom : s.room = Room.startRoom)
    (hKeys : s.keys > 0) :
    let t := step s Action.openLockedExit
    t.keys = s.keys - 1 ∧ t.completed = true := by
  simp [step, hRoom, hKeys]

theorem navigation_preserves_hallMonsterAlive
    {s : EnvState} {a : Action}
    (ha : a = Action.goWest ∨ a = Action.goEast) :
    (step s a).hallMonsterAlive = s.hallMonsterAlive := by
  rcases ha with rfl | rfl
  · dsimp [step]
    split <;> rfl
  · dsimp [step]
    split <;> rfl

def witnessPlan : List Action :=
  [
    Action.goWest,
    Action.goWest,
    Action.openChest,
    Action.goEast,
    Action.goEast,
    Action.openLockedExit
  ]

def finalState : EnvState :=
  {
    room := Room.startRoom
    keys := 0
    keyChestOpened := true
    hallMonsterAlive := true
    completed := true
  }

theorem witnessPlan_executes_to_finalState :
    run initialState witnessPlan = finalState := by
  rfl

theorem witnessPlan_reaches_goal :
    GoalReached (run initialState witnessPlan) := by
  simp [GoalReached, witnessPlan_executes_to_finalState, finalState]

theorem task3_completable :
    ∃ plan, GoalReached (run initialState plan) := by
  exact ⟨witnessPlan, witnessPlan_reaches_goal⟩

end Task3EnvironmentFormalization
