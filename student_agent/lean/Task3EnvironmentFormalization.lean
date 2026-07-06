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

/-! ### Chest lemmas -/

theorem openChest_only_in_keyRoom
    {s : EnvState} (hRoom : s.room ≠ Room.keyRoom) :
    step s Action.openChest = s := by
  simp [step, hRoom]

theorem openChest_already_opened
    {s : EnvState} (hChest : s.keyChestOpened = true) :
    step s Action.openChest = s := by
  simp [step, hChest]

theorem openChest_in_keyRoom_marks_opened
    {s : EnvState}
    (hRoom : s.room = Room.keyRoom)
    (hChest : s.keyChestOpened = false) :
    (step s Action.openChest).keyChestOpened = true := by
  simp [step, hRoom, hChest]

/-! ### Locked exit lemmas -/

theorem openLockedExit_blocked_not_in_startRoom
    {s : EnvState} (hRoom : s.room ≠ Room.startRoom) :
    step s Action.openLockedExit = s := by
  simp [step, hRoom]

theorem openLockedExit_preserves_room
    {s : EnvState} : (step s Action.openLockedExit).room = s.room := by
  by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
  · simp [step, h1]
  · simp [step, h1]

theorem openLockedExit_preserves_keyChestOpened
    {s : EnvState} : (step s Action.openLockedExit).keyChestOpened = s.keyChestOpened := by
  by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
  · simp [step, h1]
  · simp [step, h1]

/-! ### Necessity lemmas -/

/-- Non-openLockedExit actions preserve the `completed` field. -/
theorem non_openLockedExit_preserves_completed
    {s : EnvState} (a : Action) (ha : a ≠ Action.openLockedExit) :
    (step s a).completed = s.completed := by
  cases a with
  | goWest => unfold step; cases s.room <;> rfl
  | goEast => unfold step; cases s.room <;> rfl
  | openChest =>
    by_cases h1 : s.room = Room.keyRoom ∧ s.keyChestOpened = false
    · simp [step, h1]
    · simp [step, h1]
  | openLockedExit => exact absurd rfl ha
  | wait => simp [step]

/-- `openLockedExit` is the only action that can flip `completed` from `false`
    to `true`. -/
theorem only_openLockedExit_sets_completed
    {s : EnvState} (hs : s.completed = false) (a : Action)
    (h : (step s a).completed = true) : a = Action.openLockedExit := by
  by_cases ha : a = Action.openLockedExit
  · exact ha
  · have := non_openLockedExit_preserves_completed (s := s) a ha
    rw [this, hs] at h
    simp at h

/-! ### Action-wise invariant lemmas -/

/-- `hallMonsterAlive` never changes (no attack action in Task 3). -/
theorem hallMonsterAlive_never_changes
    {s : EnvState} (a : Action) :
    (step s a).hallMonsterAlive = s.hallMonsterAlive := by
  cases a with
  | goWest => unfold step; cases s.room <;> rfl
  | goEast => unfold step; cases s.room <;> rfl
  | openChest =>
    by_cases h1 : s.room = Room.keyRoom ∧ s.keyChestOpened = false
    · simp [step, h1]
    · simp [step, h1]
  | openLockedExit =>
    by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- `openChest` is the only action that can change `keyChestOpened`. -/
theorem only_openChest_changes_keyChestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).keyChestOpened = s.keyChestOpened := by
  cases a with
  | goWest => unfold step; cases s.room <;> rfl
  | goEast => unfold step; cases s.room <;> rfl
  | openChest => exact absurd rfl ha
  | openLockedExit =>
    by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- Only `openChest` (gains) and `openLockedExit` (consumes) can change `keys`. -/
theorem only_openChest_or_openLockedExit_changes_keys
    {s : EnvState} (a : Action)
    (ha : a ≠ Action.openChest) (ha' : a ≠ Action.openLockedExit) :
    (step s a).keys = s.keys := by
  cases a with
  | goWest => unfold step; cases s.room <;> rfl
  | goEast => unfold step; cases s.room <;> rfl
  | openChest => exact absurd rfl ha
  | openLockedExit => exact absurd rfl ha'
  | wait => simp [step]

/-! ### Reachable states and invariants -/

/-- Reachability: states reachable from `initialState` via arbitrary actions. -/
inductive Reachable : EnvState → Prop where
  | init : Reachable initialState
  | step (s : EnvState) (a : Action) : Reachable s → Reachable (step s a)

/-- Invariant: if the key chest is not opened then no keys have been collected. -/
theorem keyChestOpened_or_keys_zero {s : EnvState} (hr : Reachable s) :
    s.keyChestOpened = true ∨ s.keys = 0 := by
  induction hr with
  | init => simp [initialState]
  | step s a hr ih =>
    cases a with
    | goWest => unfold step; cases s.room <;> simp <;> exact ih
    | goEast => unfold step; cases s.room <;> simp <;> exact ih
    | openChest =>
      by_cases h1 : s.room = Room.keyRoom ∧ s.keyChestOpened = false
      · left; simp [step, h1]
      · simp [step, h1]; exact ih
    | openLockedExit =>
      by_cases h1 : s.room = Room.startRoom ∧ s.keys > 0
      · rcases ih with (h | h)
        · left; simp [step, h1, h]
        · right; omega
      · simp [step, h1]; exact ih
    | wait => simp [step]; exact ih

/-- If a reachable state has `completed = true`, then the key chest has been
    opened. (We cannot conclude `room = startRoom` because the player may
    navigate away after completing the task.) -/
theorem completion_postcondition {s : EnvState} (hr : Reachable s) (hc : s.completed = true) :
    s.keyChestOpened = true := by
  induction hr with
  | init => simp [initialState] at hc
  | step s' a hr ih =>
    by_cases hs : s'.completed = true
    · have hch := ih hs
      have hch' : (step s' a).keyChestOpened = s'.keyChestOpened := by
        by_cases ha : a = Action.openChest
        · subst ha
          have hstep : step s' Action.openChest = s' := openChest_already_opened hch
          simp [hstep, hch]
        · exact only_openChest_changes_keyChestOpened a ha
      simp [hch', hch]
    · have hf : s'.completed = false := by
        cases h : s'.completed with
        | true => exact absurd h hs
        | false => rfl
      have ha : a = Action.openLockedExit := only_openLockedExit_sets_completed hf a hc
      subst ha
      by_cases hcond : s'.room = Room.startRoom ∧ s'.keys > 0
      · have hchest : s'.keyChestOpened = true := by
          have h_cases := keyChestOpened_or_keys_zero hr
          rcases h_cases with (h | h)
          · exact h
          · rw [h] at hcond; simp at hcond
        have hch' : (step s' Action.openLockedExit).keyChestOpened = s'.keyChestOpened :=
          openLockedExit_preserves_keyChestOpened
        simp [hch', hchest]
      · have hstep : step s' Action.openLockedExit = s' := by simp [step, hcond]
        rw [hstep, hf] at hc
        simp at hc

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

/-! ### Symbolic policy formalization -/

/--
The abstract stage machine behind the task 3 baseline. This is the symbolic
counterpart of the Python `decide_task3` routine: it ignores pixel-level
waypoints and keeps only the high-level subgoal ordering that matters for the
environment proof.
-/
inductive PolicyStage where
  | getKey
  | useExit
  | done
  deriving DecidableEq, Repr

def policyStage (s : EnvState) : PolicyStage :=
  if s.keyChestOpened = false then PolicyStage.getKey
  else if s.completed = false then PolicyStage.useExit
  else PolicyStage.done

/--
State-driven room-level policy. It maps the current symbolic state to the next
high-level action, including navigation actions that move between rooms to reach
the subgoal required by the current stage.
-/
def symbolicPolicy (s : EnvState) : Action :=
  match policyStage s with
  | PolicyStage.getKey =>
      match s.room with
      | Room.startRoom => Action.goWest
      | Room.monsterHall => Action.goWest
      | Room.keyRoom => Action.openChest
  | PolicyStage.useExit =>
      match s.room with
      | Room.keyRoom => Action.goEast
      | Room.monsterHall => Action.goEast
      | Room.startRoom => Action.openLockedExit
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

/-- Legal-action predicate for the symbolic transition layer (Bool version
    for computable checking via `native_decide`). -/
def actionEnabled (s : EnvState) : Action → Bool
  | Action.goWest => s.room = Room.startRoom || s.room = Room.monsterHall
  | Action.goEast => s.room = Room.keyRoom || s.room = Room.monsterHall
  | Action.openChest => s.room = Room.keyRoom && !s.keyChestOpened
  | Action.openLockedExit => s.room = Room.startRoom && s.keys > 0
  | Action.wait => true

def actionsEnabledAlong : EnvState → List Action → Bool
  | _, [] => true
  | s, a :: rest => actionEnabled s a && actionsEnabledAlong (step s a) rest

theorem policyTrace_6_matches_witnessPlan :
    policyTrace 6 initialState = witnessPlan := by
  native_decide

theorem policyTrace_6_actions_enabled :
    actionsEnabledAlong initialState (policyTrace 6 initialState) = true := by
  native_decide

theorem symbolicPolicy_run_6_finalState :
    runPolicy 6 initialState = finalState := by
  native_decide

theorem symbolicPolicy_reaches_goal :
    GoalReached (runPolicy 6 initialState) := by
  rw [symbolicPolicy_run_6_finalState]
  simp [GoalReached, finalState]

theorem task3_symbolicPolicy_completes :
    ∃ n, GoalReached (runPolicy n initialState) := by
  exact ⟨6, symbolicPolicy_reaches_goal⟩

end Task3EnvironmentFormalization
