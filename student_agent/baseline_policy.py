from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

from nesylink.core.constants import ACTION_A, ACTION_LEFT, ACTION_NOOP, ACTION_RIGHT, ACTION_UP, ACTION_DOWN


def repeat(action: int, count: int) -> list[int]:
    return [action] * count


def build_task1_plan() -> list[int]:
    plan: list[int] = []
    plan += repeat(ACTION_RIGHT, 48)
    plan += repeat(ACTION_UP, 48)
    plan += repeat(ACTION_LEFT, 96)
    plan.append(ACTION_A)
    plan += repeat(ACTION_RIGHT, 32)
    plan += repeat(ACTION_UP, 48)
    plan += repeat(ACTION_RIGHT, 16)
    plan += repeat(ACTION_UP, 20)
    return plan


def build_task2_plan() -> list[int]:
    """
    This initial task_2 baseline is a scripted pixel-action plan extracted from
    the successful reference execution trace.
    """
    plan: list[int] = []
    plan += repeat(ACTION_UP, 16)
    plan += repeat(ACTION_LEFT, 64)
    plan += repeat(ACTION_A, 2)
    plan += repeat(ACTION_DOWN, 19)
    plan += repeat(ACTION_LEFT, 32)
    plan += repeat(ACTION_A, 1)
    plan += repeat(ACTION_DOWN, 16)
    plan += repeat(ACTION_LEFT, 32)
    return plan


@dataclass
class AgentHistory:
    task_id: str | None = None
    plan_index: int = 0
    last_inventory: dict[str, Any] = field(default_factory=dict)
    notes: dict[str, Any] = field(default_factory=dict)


class Policy:
    """
    Group baseline policy skeleton.

    The evaluator still calls `act(obs, info)`, but the long-term goal is to keep
    the real decision logic isolated from hidden debug state in `info`.
    """

    def __init__(self) -> None:
        self.history = AgentHistory()
        self.task_plans = {
            "mathematical_logic/task_1": build_task1_plan(),
            "mathematical_logic/task_2": build_task2_plan(),
        }

    def reset(self, seed: int | None = None, task_id: str | None = None) -> None:
        del seed
        self.history = AgentHistory(task_id=task_id)

    def extract_inventory(self, info: dict[str, Any]) -> dict[str, Any]:
        inventory = info.get("inventory", {})
        if isinstance(inventory, dict):
            return dict(inventory)
        return {}

    def infer_task_id(self, info: dict[str, Any]) -> str | None:
        task_id = self.history.task_id
        if task_id:
            return task_id
        env_info = info.get("env", {})
        if isinstance(env_info, dict):
            maybe_task_id = env_info.get("map_id")
            if isinstance(maybe_task_id, str):
                self.history.task_id = maybe_task_id
                return maybe_task_id
        return None

    def next_planned_action(self, task_id: str) -> int:
        plan = self.task_plans.get(task_id)
        if not plan:
            return ACTION_NOOP
        if self.history.plan_index >= len(plan):
            return ACTION_NOOP
        action = plan[self.history.plan_index]
        self.history.plan_index += 1
        return action

    def decide(self, frame, inventory: dict[str, Any], info: dict[str, Any]) -> int:
        del frame, inventory
        task_id = self.infer_task_id(info)
        if task_id in self.task_plans:
            return self.next_planned_action(task_id)

        # TODO: add room-level stage machine for task_3.
        # TODO: add dynamic-bridge state tracking for task_4.
        # TODO: add generic exploration policy for task_5.
        return ACTION_NOOP

    def act(self, obs, info: dict[str, Any]) -> int:
        inventory = self.extract_inventory(info)
        self.history.last_inventory = inventory
        return self.decide(obs, inventory, info)


def make_policy() -> Policy:
    return Policy()
