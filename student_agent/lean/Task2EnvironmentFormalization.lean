/-
  Environment formalization for `mathematical_logic/task_2`.

  Task 2 is a single-room combat-and-exit task:

  * defeat the chaser monster;
  * open the chest to get one key;
  * leave through the west conditional exit.

  The real engine also contains trap rows on the top and bottom boundaries. This
  Lean model keeps a minimal trap effect by letting a "move into trap zone"
  action reduce HP and send the player back to the safe center zone.

  Python correspondence:
  * `nesylink/map_data/mathematical_logic/task_2/room_001.json`
  * `nesylink/core/mechanics/interactions.py`
  * `nesylink/core/mechanics/movement.py`
  * `nesylink/core/mechanics/combat.py`
-/

namespace Task2EnvironmentFormalization

/-! ### Zones and actions -/

inductive Zone where
  | safeCenter
  | nearMonster
  | nearChest
  | westExit
  | topTrap
  | bottomTrap
  deriving DecidableEq, Repr

inductive Action where
  | moveTo (z : Zone)
  | attack
  | openChest
  | useExit
  | wait
  deriving DecidableEq, Repr

/-! ### Environment state -/

structure EnvState where
  zone : Zone
  hp : Nat
  monsterAlive : Bool
  monsterHp : Nat
  chestOpened : Bool
  keys : Nat
  completed : Bool
  deriving DecidableEq, Repr

-- Spawn at tile (7, 3) per room_001.json, modelled as safeCenter.
def initialState : EnvState :=
  {
    zone := Zone.safeCenter
    hp := 5
    monsterAlive := true
    monsterHp := 2
    chestOpened := false
    keys := 0
    completed := false
  }

def GoalReached (s : EnvState) : Prop :=
  s.completed = true

/-! ### Transition function -/

def step (s : EnvState) : Action → EnvState
  | Action.moveTo z =>
      match z with
      | Zone.topTrap =>
          { s with zone := Zone.safeCenter, hp := s.hp - 1 }
      | Zone.bottomTrap =>
          { s with zone := Zone.safeCenter, hp := s.hp - 1 }
      | _ =>
          { s with zone := z }
  | Action.attack =>
      if s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1 then
        if s.monsterHp = 1 then
          { s with monsterAlive := false, monsterHp := 0 }
        else
          { s with monsterHp := s.monsterHp - 1 }
      else
        s
  | Action.openChest =>
      if s.zone = Zone.nearChest ∧ s.chestOpened = false then
        { s with chestOpened := true, keys := s.keys + 1 }
      else
        s
  | Action.useExit =>
      if s.zone = Zone.westExit ∧ s.monsterAlive = false ∧ s.keys > 0 then
        { s with completed := true }
      else
        s
  | Action.wait => s

def run : EnvState → List Action → EnvState
  | s, [] => s
  | s, a :: rest => run (step s a) rest

/-! ### Basic move lemmas -/

theorem move_to_zone
    {s : EnvState} {z : Zone}
    (hz : z ≠ Zone.topTrap) (hz' : z ≠ Zone.bottomTrap) :
    (step s (Action.moveTo z)).zone = z := by
  simp [step]

theorem move_to_zone_not_trap
    {s : EnvState} (z : Zone) : (step s (Action.moveTo z)).zone =
      match z with
      | Zone.topTrap => Zone.safeCenter
      | Zone.bottomTrap => Zone.safeCenter
      | _ => z := by
  cases z <;> simp [step]

/-! ### Trap lemmas -/

theorem trap_move_reduces_hp
    {s : EnvState} (_ : s.hp > 0) :
    (step s (Action.moveTo Zone.topTrap)).hp = s.hp - 1 := by
  simp [step]

theorem trap_move_resets_to_safe_center
    {s : EnvState} :
    (step s (Action.moveTo Zone.bottomTrap)).zone = Zone.safeCenter := by
  simp [step]

theorem trap_move_preserves_monster
    {s : EnvState} :
    (step s (Action.moveTo Zone.topTrap)).monsterAlive = s.monsterAlive := by
  simp [step]

theorem trap_move_preserves_chestOpened
    {s : EnvState} :
    (step s (Action.moveTo Zone.bottomTrap)).chestOpened = s.chestOpened := by
  simp [step]

theorem trap_move_preserves_keys
    {s : EnvState} :
    (step s (Action.moveTo Zone.topTrap)).keys = s.keys := by
  simp [step]

theorem trap_move_preserves_completed
    {s : EnvState} :
    (step s (Action.moveTo Zone.bottomTrap)).completed = s.completed := by
  simp [step]

theorem trap_move_preserves_monsterHp
    {s : EnvState} :
    (step s (Action.moveTo Zone.topTrap)).monsterHp = s.monsterHp := by
  simp [step]

/-! ### Safe move lemmas (non-trap) -/

theorem safe_move_preserves_hp
    {s : EnvState} {z : Zone}
    (hz : z ≠ Zone.topTrap) (hz' : z ≠ Zone.bottomTrap) :
    (step s (Action.moveTo z)).hp = s.hp := by
  simp [step]

theorem safe_move_preserves_monsterAlive
    {s : EnvState} {z : Zone}
    (hz : z ≠ Zone.topTrap) (hz' : z ≠ Zone.bottomTrap) :
    (step s (Action.moveTo z)).monsterAlive = s.monsterAlive := by
  simp [step]

theorem safe_move_preserves_chestOpened
    {s : EnvState} {z : Zone}
    (hz : z ≠ Zone.topTrap) (hz' : z ≠ Zone.bottomTrap) :
    (step s (Action.moveTo z)).chestOpened = s.chestOpened := by
  simp [step]

theorem safe_move_preserves_keys
    {s : EnvState} {z : Zone}
    (hz : z ≠ Zone.topTrap) (hz' : z ≠ Zone.bottomTrap) :
    (step s (Action.moveTo z)).keys = s.keys := by
  simp [step]

theorem safe_move_preserves_completed
    {s : EnvState} {z : Zone}
    (hz : z ≠ Zone.topTrap) (hz' : z ≠ Zone.bottomTrap) :
    (step s (Action.moveTo z)).completed = s.completed := by
  simp [step]

theorem safe_move_preserves_monsterHp
    {s : EnvState} {z : Zone}
    (hz : z ≠ Zone.topTrap) (hz' : z ≠ Zone.bottomTrap) :
    (step s (Action.moveTo z)).monsterHp = s.monsterHp := by
  simp [step]

/-! ### Attack lemmas -/

theorem attack_reduces_monsterHp_when_adjacent
    {s : EnvState}
    (hZone : s.zone = Zone.nearMonster)
    (hMonster : s.monsterAlive = true)
    (hHp : s.hp > 1) :
    (step s Action.attack).monsterHp = s.monsterHp - 1 := by
  by_cases hMhp : s.monsterHp = 1
  · simp [step, hZone, hMonster, hHp, hMhp]
  · simp [step, hZone, hMonster, hHp, hMhp]

theorem attack_kills_monster_when_monsterHp_one
    {s : EnvState}
    (hZone : s.zone = Zone.nearMonster)
    (hMonster : s.monsterAlive = true)
    (hHp : s.hp > 1)
    (hMonsterHp : s.monsterHp = 1) :
    (step s Action.attack).monsterAlive = false := by
  simp [step, hZone, hMonster, hHp, hMonsterHp]

theorem attack_preserves_monsterAlive_when_monsterHp_gt_one
    {s : EnvState}
    (hZone : s.zone = Zone.nearMonster)
    (hMonster : s.monsterAlive = true)
    (hHp : s.hp > 1)
    (hMonsterHp : s.monsterHp > 1) :
    (step s Action.attack).monsterAlive = true := by
  simp [step, hZone, hMonster, hHp]
  split
  · omega
  · rfl

theorem attack_no_effect_without_monster
    {s : EnvState} (hMonster : s.monsterAlive = false) :
    step s Action.attack = s := by
  simp [step, hMonster]

theorem attack_no_effect_not_adjacent
    {s : EnvState} (hZone : s.zone ≠ Zone.nearMonster) :
    step s Action.attack = s := by
  simp [step, hZone]

theorem attack_no_effect_low_hp
    {s : EnvState} (hHp : s.hp ≤ 1) :
    step s Action.attack = s := by
  by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
  · omega
  · simp [step, h1]

theorem attack_preserves_zone
    {s : EnvState} : (step s Action.attack).zone = s.zone := by
  by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
  · simp [step, h1]
    by_cases h2 : s.monsterHp = 1 <;> simp [h2]
  · simp [step, h1]

theorem attack_preserves_chestOpened
    {s : EnvState} : (step s Action.attack).chestOpened = s.chestOpened := by
  by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
  · simp [step, h1]
    by_cases h2 : s.monsterHp = 1 <;> simp [h2]
  · simp [step, h1]

theorem attack_preserves_keys
    {s : EnvState} : (step s Action.attack).keys = s.keys := by
  by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
  · simp [step, h1]
    by_cases h2 : s.monsterHp = 1 <;> simp [h2]
  · simp [step, h1]

theorem attack_preserves_hp
    {s : EnvState} : (step s Action.attack).hp = s.hp := by
  by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
  · simp [step, h1]
    by_cases h2 : s.monsterHp = 1 <;> simp [h2]
  · simp [step, h1]

theorem attack_preserves_completed
    {s : EnvState} : (step s Action.attack).completed = s.completed := by
  by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
  · simp [step, h1]
    by_cases h2 : s.monsterHp = 1 <;> simp [h2]
  · simp [step, h1]

/-! ### Chest lemmas -/

theorem chest_open_only_at_chest
    {s : EnvState} (hZone : s.zone ≠ Zone.nearChest) :
    step s Action.openChest = s := by
  simp [step, hZone]

theorem chest_open_already_opened
    {s : EnvState} (hChest : s.chestOpened = true) :
    step s Action.openChest = s := by
  simp [step, hChest]

theorem chest_open_increases_keys
    {s : EnvState}
    (hZone : s.zone = Zone.nearChest)
    (hChest : s.chestOpened = false) :
    (step s Action.openChest).keys = s.keys + 1 := by
  simp [step, hZone, hChest]

theorem chest_open_marks_opened
    {s : EnvState}
    (hZone : s.zone = Zone.nearChest)
    (hChest : s.chestOpened = false) :
    (step s Action.openChest).chestOpened = true := by
  simp [step, hZone, hChest]

theorem chest_open_preserves_zone
    {s : EnvState} : (step s Action.openChest).zone = s.zone := by
  simp [step]; split <;> rfl

theorem chest_open_preserves_monsterAlive
    {s : EnvState} : (step s Action.openChest).monsterAlive = s.monsterAlive := by
  simp [step]; split <;> rfl

theorem chest_open_preserves_hp
    {s : EnvState} : (step s Action.openChest).hp = s.hp := by
  simp [step]; split <;> rfl

theorem chest_open_preserves_completed
    {s : EnvState} : (step s Action.openChest).completed = s.completed := by
  simp [step]; split <;> rfl

theorem chest_open_preserves_monsterHp
    {s : EnvState} : (step s Action.openChest).monsterHp = s.monsterHp := by
  simp [step]; split <;> rfl

/-! ### Exit lemmas -/

theorem use_exit_only_at_exit
    {s : EnvState} (hZone : s.zone ≠ Zone.westExit) :
    step s Action.useExit = s := by
  simp [step, hZone]

theorem exit_blocked_if_monster_alive
    {s : EnvState}
    (hZone : s.zone = Zone.westExit)
    (hMonster : s.monsterAlive = true) :
    step s Action.useExit = s := by
  simp [step, hZone, hMonster]

theorem exit_blocked_without_key
    {s : EnvState}
    (hZone : s.zone = Zone.westExit)
    (hMonster : s.monsterAlive = false)
    (hKeys : s.keys = 0) :
    step s Action.useExit = s := by
  simp [step, hZone, hMonster, hKeys]

theorem exit_succeeds_after_requirements
    {s : EnvState}
    (hZone : s.zone = Zone.westExit)
    (hMonster : s.monsterAlive = false)
    (hKeys : s.keys > 0) :
    (step s Action.useExit).completed = true := by
  simp [step, hZone, hMonster, hKeys]

theorem use_exit_preserves_zone
    {s : EnvState} : (step s Action.useExit).zone = s.zone := by
  simp [step]; split <;> rfl

theorem use_exit_preserves_monsterAlive
    {s : EnvState} : (step s Action.useExit).monsterAlive = s.monsterAlive := by
  simp [step]; split <;> rfl

theorem use_exit_preserves_chestOpened
    {s : EnvState} : (step s Action.useExit).chestOpened = s.chestOpened := by
  simp [step]; split <;> rfl

theorem use_exit_preserves_keys
    {s : EnvState} : (step s Action.useExit).keys = s.keys := by
  simp [step]; split <;> rfl

theorem use_exit_preserves_monsterHp
    {s : EnvState} : (step s Action.useExit).monsterHp = s.monsterHp := by
  simp [step]; split <;> rfl

/-! ### Necessity lemmas -/

/-- Non-useExit actions preserve the `completed` field. -/
theorem non_useExit_preserves_completed
    {s : EnvState} (a : Action) (ha : a ≠ Action.useExit) :
    (step s a).completed = s.completed := by
  cases a with
  | moveTo z => cases z <;> simp [step]
  | attack =>
    by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
    · simp [step, h1]
      by_cases h2 : s.monsterHp = 1
      · simp [h2]
      · simp [h2]
    · simp [step, h1]
  | openChest =>
    by_cases h1 : s.zone = Zone.nearChest ∧ s.chestOpened = false
    · simp [step, h1]
    · simp [step, h1]
  | useExit => exact absurd rfl ha
  | wait => simp [step]

/-- `useExit` is the only action that can flip `completed` from `false` to
    `true`. All other actions leave `completed` unchanged. -/
theorem only_useExit_sets_completed
    {s : EnvState} (hs : s.completed = false) (a : Action)
    (h : (step s a).completed = true) : a = Action.useExit := by
  by_cases ha : a = Action.useExit
  · exact ha
  · have := non_useExit_preserves_completed (s := s) a ha
    rw [this, hs] at h
    simp at h

/-! ### Action-wise invariant lemmas -/

/-- Attack is the only action that can change `monsterAlive`. -/
theorem only_attack_changes_monsterAlive
    {s : EnvState} (a : Action) (ha : a ≠ Action.attack) :
    (step s a).monsterAlive = s.monsterAlive := by
  cases a with
  | moveTo z => cases z <;> simp [step]
  | attack => exact absurd rfl ha
  | openChest =>
    by_cases h1 : s.zone = Zone.nearChest ∧ s.chestOpened = false
    · simp [step, h1]
    · simp [step, h1]
  | useExit =>
    by_cases h1 : s.zone = Zone.westExit ∧ s.monsterAlive = false ∧ s.keys > 0
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- `openChest` is the only action that can change `chestOpened`. -/
theorem only_openChest_changes_chestOpened
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) :
    (step s a).chestOpened = s.chestOpened := by
  cases a with
  | moveTo z => cases z <;> simp [step]
  | attack =>
    by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
    · simp [step, h1]
      by_cases h2 : s.monsterHp = 1
      · simp [h2]
      · simp [h2]
    · simp [step, h1]
  | openChest => exact absurd rfl ha
  | useExit =>
    by_cases h1 : s.zone = Zone.westExit ∧ s.monsterAlive = false ∧ s.keys > 0
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- Attack is the only action that can change `monsterHp`. -/
theorem only_attack_changes_monsterHp
    {s : EnvState} (a : Action) (ha : a ≠ Action.attack) :
    (step s a).monsterHp = s.monsterHp := by
  cases a with
  | moveTo z => cases z <;> simp [step]
  | attack => exact absurd rfl ha
  | openChest =>
    by_cases h1 : s.zone = Zone.nearChest ∧ s.chestOpened = false
    · simp [step, h1]
    · simp [step, h1]
  | useExit =>
    by_cases h1 : s.zone = Zone.westExit ∧ s.monsterAlive = false ∧ s.keys > 0
    · simp [step, h1]
    · simp [step, h1]
  | wait => simp [step]

/-- Only `openChest` and `useExit` can change `keys`. -/
theorem only_openChest_or_useExit_changes_keys
    {s : EnvState} (a : Action) (ha : a ≠ Action.openChest) (ha' : a ≠ Action.useExit) :
    (step s a).keys = s.keys := by
  cases a with
  | moveTo z => cases z <;> simp [step]
  | attack =>
    by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
    · simp [step, h1]
      by_cases h2 : s.monsterHp = 1
      · simp [h2]
      · simp [h2]
    · simp [step, h1]
  | openChest => exact absurd rfl ha
  | useExit => exact absurd rfl ha'
  | wait => simp [step]

/-- Reachability: states reachable from `initialState` via arbitrary actions. -/
inductive Reachable : EnvState → Prop where
  | init : Reachable initialState
  | step (s : EnvState) (a : Action) : Reachable s → Reachable (step s a)

/-- Invariant: if the chest is not opened then no keys have been collected. -/
theorem chestOpened_or_keys_zero {s : EnvState} (hr : Reachable s) :
    s.chestOpened = true ∨ s.keys = 0 := by
  induction hr with
  | init => simp [initialState]
  | step s a hr ih =>
      cases a with
      | moveTo z => cases z <;> simp [step] <;> exact ih
      | attack =>
          by_cases h1 : s.zone = Zone.nearMonster ∧ s.monsterAlive = true ∧ s.hp > 1
          · simp [step, h1]
            by_cases h2 : s.monsterHp = 1 <;> simp [h2] <;> exact ih
          · simp [step, h1]; exact ih
      | openChest =>
          by_cases h1 : s.zone = Zone.nearChest ∧ s.chestOpened = false
          · simp [step, h1];
          · simp [step, h1]; exact ih
      | useExit =>
          by_cases h1 : s.zone = Zone.westExit ∧ s.monsterAlive = false ∧ s.keys > 0
          · simp [step, h1]; exact ih
          · simp [step, h1]; exact ih
      | wait => simp [step]; exact ih

/-- If a reachable state has `completed = true`, then the monster is defeated and
    the chest has been opened. -/
theorem completion_postcondition {s : EnvState} (hr : Reachable s) (hc : s.completed = true) :
    s.monsterAlive = false ∧ s.chestOpened = true := by
  induction hr with
  | init => simp [initialState] at hc
  | step s' a hr ih =>
      by_cases hs : s'.completed = true
      · -- s' already completed: use ih, then show step preserves both fields
        rcases ih hs with ⟨hm, hch⟩
        have hm' : (step s' a).monsterAlive = s'.monsterAlive := by
          by_cases ha : a = Action.attack
          · subst ha
            have : step s' Action.attack = s' := attack_no_effect_without_monster hm
            simp [this, hm]
          · exact only_attack_changes_monsterAlive a ha
        have hc' : (step s' a).chestOpened = s'.chestOpened := by
          by_cases ha : a = Action.openChest
          · subst ha
            have : step s' Action.openChest = s' := chest_open_already_opened hch
            simp [this, hch]
          · exact only_openChest_changes_chestOpened a ha
        simp [hm', hc', hm, hch]
      · -- s'.completed ≠ true ⇒ s'.completed = false (Bool exhaust)
        have hf : s'.completed = false := by
          cases h : s'.completed with
          | true => exact absurd h hs
          | false => rfl
        have ha : a = Action.useExit := only_useExit_sets_completed hf a hc
        subst ha
        by_cases hcond : s'.zone = Zone.westExit ∧ s'.monsterAlive = false ∧ s'.keys > 0
        · have hchest : s'.chestOpened = true := by
            have h_cases := chestOpened_or_keys_zero hr
            rcases h_cases with (h | h)
            · exact h
            · rw [h] at hcond; simp at hcond
          have hm' : (step s' Action.useExit).monsterAlive = s'.monsterAlive :=
            use_exit_preserves_monsterAlive
          have hc' : (step s' Action.useExit).chestOpened = s'.chestOpened :=
            use_exit_preserves_chestOpened
          simp [hm', hc', hcond.2.1, hchest]
        · have hstep : step s' Action.useExit = s' := by simp [step, hcond]
          rw [hstep, hf] at hc
          simp at hc

/-- HP never increases after any single step. -/
theorem hp_non_increasing
    {s : EnvState} (a : Action) : (step s a).hp ≤ s.hp := by
  cases a with
  | moveTo z =>
    cases z <;> simp [step] <;> (first | apply Nat.le_refl | apply Nat.sub_le_self)
  | attack =>
    have hph : (step s Action.attack).hp = s.hp := by
      simp [step]
      split
      · split <;> rfl
      · rfl
    calc
      (step s Action.attack).hp = s.hp := hph
      _ ≤ s.hp := Nat.le_refl _
  | openChest =>
    have hph : (step s Action.openChest).hp = s.hp := by
      simp [step]; split <;> rfl
    rw [hph]; apply Nat.le_refl
  | useExit =>
    have hph : (step s Action.useExit).hp = s.hp := by
      simp [step]; split <;> rfl
    rw [hph]; apply Nat.le_refl
  | wait => simp [step];

/-! ### Witness plan -/

-- Zone-level route:
--   safeCenter → moveTo nearMonster → attack × 2 → moveTo nearChest
--   → openChest → moveTo westExit → useExit
def witnessPlan : List Action :=
  [
    Action.moveTo Zone.nearMonster,
    Action.attack,
    Action.attack,
    Action.moveTo Zone.nearChest,
    Action.openChest,
    Action.moveTo Zone.westExit,
    Action.useExit
  ]

def finalState : EnvState :=
  {
    zone := Zone.westExit
    hp := 5
    monsterAlive := false
    monsterHp := 0
    chestOpened := true
    keys := 1
    completed := true
  }

theorem witnessPlan_executes_to_finalState :
    run initialState witnessPlan = finalState := by
  native_decide

theorem witnessPlan_reaches_goal :
    GoalReached (run initialState witnessPlan) := by
  rw [witnessPlan_executes_to_finalState]
  simp [GoalReached, finalState]

theorem task2_completable :
    ∃ plan, GoalReached (run initialState plan) := by
  exact ⟨witnessPlan, witnessPlan_reaches_goal⟩

end Task2EnvironmentFormalization
