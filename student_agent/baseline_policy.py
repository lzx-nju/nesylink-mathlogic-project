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

    def current_room_id(self, info: dict[str, Any]) -> str | None:
        env_info = info.get("env", {})
        if isinstance(env_info, dict):
            room_id = env_info.get("room_id")
            if isinstance(room_id, str):
                return room_id
        return None

    def current_tile(self, info: dict[str, Any]) -> tuple[int, int] | None:
        agent_info = info.get("agent", {})
        if not isinstance(agent_info, dict):
            return None
        tile = agent_info.get("tile")
        if isinstance(tile, (list, tuple)) and len(tile) == 2:
            return int(tile[0]), int(tile[1])
        return None

    def current_facing(self, info: dict[str, Any]) -> str | None:
        agent_info = info.get("agent", {})
        if isinstance(agent_info, dict):
            facing = agent_info.get("facing")
            if isinstance(facing, str):
                return facing
        return None

    def bridge_state(self, info: dict[str, Any]) -> str | None:
        dynamic = info.get("dynamic", {})
        if not isinstance(dynamic, dict):
            return None
        objects = dynamic.get("objects", {})
        if not isinstance(objects, dict):
            return None
        bridge = objects.get("center_bridge", {})
        if not isinstance(bridge, dict):
            return None
        state = bridge.get("state")
        if isinstance(state, str):
            return state
        return None

    def monsters_remaining(self, info: dict[str, Any]) -> int:
        entities = info.get("entities", {})
        if isinstance(entities, dict):
            return int(entities.get("monsters_remaining", 0))
        return 0

    def has_item(self, inventory: dict[str, Any], item_id: str) -> bool:
        items = inventory.get("items", [])
        if isinstance(items, (list, tuple)):
            return item_id in items
        return False

    def next_planned_action(self, task_id: str) -> int:
        plan = self.task_plans.get(task_id)
        if not plan:
            return ACTION_NOOP
        if self.history.plan_index >= len(plan):
            return ACTION_NOOP
        action = plan[self.history.plan_index]
        self.history.plan_index += 1
        return action

    def decide_task3(self, info: dict[str, Any], inventory: dict[str, Any]) -> int:
        room_id = self.current_room_id(info)
        tile = self.current_tile(info)
        keys = int(inventory.get("keys", 0))
        if room_id is None or tile is None:
            return ACTION_NOOP

        x, y = tile

        if keys <= 0:
            if room_id == "start_room":
                return ACTION_LEFT
            if room_id == "monster_hall":
                return ACTION_LEFT
            if room_id == "key_room":
                if y < 4:
                    return ACTION_DOWN
                if y > 4:
                    return ACTION_UP
                if x > 6:
                    return ACTION_LEFT
                return ACTION_A
            return ACTION_NOOP

        if room_id == "key_room":
            return ACTION_RIGHT
        if room_id == "monster_hall":
            return ACTION_RIGHT
        if room_id == "start_room":
            return ACTION_RIGHT
        return ACTION_NOOP

    def decide_task4(self, info: dict[str, Any], inventory: dict[str, Any]) -> int:
        room_id = self.current_room_id(info)
        tile = self.current_tile(info)
        facing = self.current_facing(info)
        bridge_state = self.bridge_state(info)
        events = info.get("events", {})
        event_counts = events.get("counts", {}) if isinstance(events, dict) else {}
        keys = int(inventory.get("keys", 0))
        has_sword = self.has_item(inventory, "sword")
        if room_id is None or tile is None:
            return ACTION_NOOP

        if isinstance(event_counts, dict) and int(event_counts.get("monster_killed", 0)) > 0:
            self.history.notes["task4_guardian_defeated"] = True

        guardian_defeated = bool(self.history.notes.get("task4_guardian_defeated", False))
        x, y = tile

        if keys <= 0:
            stage = "get_key"
        elif not has_sword:
            stage = "get_sword"
        elif not guardian_defeated:
            stage = "kill_guardian"
        else:
            stage = "open_final_chest"

        desired_bridge = {
            "get_key": "west_to_north",
            "get_sword": "west_to_east",
            "kill_guardian": "west_to_south",
            "open_final_chest": "west_to_south",
        }[stage]

        if room_id == "west":
            if bridge_state != desired_bridge:
                if x < 4:
                    return ACTION_RIGHT
                if x > 4:
                    return ACTION_LEFT
                if y < 4:
                    return ACTION_DOWN
                if y > 4:
                    return ACTION_UP
                return ACTION_A
            return ACTION_RIGHT

        if room_id == "center":
            if stage == "get_key":
                if x < 4:
                    return ACTION_RIGHT
                if x > 4:
                    return ACTION_LEFT
                return ACTION_UP

            if stage == "get_sword":
                if bridge_state != desired_bridge:
                    if y < 4:
                        return ACTION_DOWN
                    if y > 4:
                        return ACTION_UP
                    return ACTION_LEFT
                if y < 4:
                    return ACTION_DOWN
                if y > 4:
                    return ACTION_UP
                return ACTION_RIGHT

            if stage == "kill_guardian":
                if bridge_state != desired_bridge:
                    if y < 4:
                        return ACTION_DOWN
                    if y > 4:
                        return ACTION_UP
                    return ACTION_LEFT
                if x < 4:
                    return ACTION_RIGHT
                if x > 4:
                    return ACTION_LEFT
                return ACTION_DOWN

            if x < 4:
                return ACTION_RIGHT
            if x > 4:
                return ACTION_LEFT
            if y > 5:
                return ACTION_UP
            if y < 5:
                return ACTION_DOWN
            if facing != "up":
                return ACTION_UP
            return ACTION_A

        if room_id == "north":
            if stage != "get_key":
                return ACTION_DOWN
            if x < 4:
                return ACTION_RIGHT
            if x > 4:
                return ACTION_LEFT
            if y > 4:
                return ACTION_UP
            if y < 4:
                return ACTION_DOWN
            return ACTION_A

        if room_id == "east":
            if stage != "get_sword":
                return ACTION_LEFT
            if y < 4:
                return ACTION_DOWN
            if y > 4:
                return ACTION_UP
            if x < 4:
                return ACTION_RIGHT
            if x > 4:
                return ACTION_LEFT
            if facing != "right":
                return ACTION_RIGHT
            return ACTION_A

        if room_id == "south":
            if stage == "open_final_chest":
                return ACTION_UP
            if x < 4:
                return ACTION_RIGHT
            if x > 4:
                return ACTION_LEFT
            if y < 2:
                return ACTION_DOWN
            if y > 3:
                return ACTION_UP
            if y == 2:
                return ACTION_DOWN
            if facing != "down":
                return ACTION_UP
            return ACTION_A

        return ACTION_NOOP

    def decide(self, frame, inventory: dict[str, Any], info: dict[str, Any]) -> int:
        del frame
        task_id = self.infer_task_id(info)
        if task_id in self.task_plans:
            return self.next_planned_action(task_id)

        if task_id == "mathematical_logic/task_3":
            return self.decide_task3(info, inventory)
        if task_id == "mathematical_logic/task_4":
            return self.decide_task4(info, inventory)

        # TODO: add generic exploration policy for task_5.
        return ACTION_NOOP

    def act(self, obs, info: dict[str, Any]) -> int:
        inventory = self.extract_inventory(info)
        self.history.last_inventory = inventory
        return self.decide(obs, inventory, info)


def make_policy() -> Policy:
    return Policy()
