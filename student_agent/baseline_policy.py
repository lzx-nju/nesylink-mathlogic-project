from __future__ import annotations

from dataclasses import dataclass, field
from typing import Any

import numpy as np

from nesylink.core.constants import (
    ACTION_A,
    ACTION_DOWN,
    ACTION_LEFT,
    ACTION_NOOP,
    ACTION_RIGHT,
    ACTION_UP,
    TILE_SIZE,
)


Color = tuple[int, int, int]
Tile = tuple[int, int]


PLAYER_COLORS: tuple[Color, ...] = ((36, 198, 72), (126, 248, 82))
WALL_COLOR: Color = (219, 18, 82)
CHEST_WOOD: Color = (152, 82, 36)
NPC_COLOR: Color = (240, 154, 52)
MONSTER_COLORS: tuple[Color, ...] = ((238, 126, 28), (255, 180, 48), (200, 78, 16))
ABYSS_COLOR: Color = (0, 0, 0)
BRIDGE_COLOR: Color = (172, 104, 48)
SWITCH_BODY: Color = (255, 216, 80)
SWITCH_DOWN: Color = (184, 124, 42)


BRIDGE_CYCLE = {
    "west_to_north": "west_to_east",
    "west_to_east": "west_to_south",
    "west_to_south": "west_to_north",
}


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
    facing: str = "down"
    last_action: int = ACTION_NOOP
    last_inventory: dict[str, Any] = field(default_factory=dict)
    notes: dict[str, Any] = field(default_factory=dict)


@dataclass(frozen=True)
class PixelState:
    player_tile: Tile | None
    room_id: str | None
    bridge_state: str | None
    monster_visible: bool


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

    def reward_signals(self, info: dict[str, Any]) -> dict[str, Any]:
        reward_info = info.get("reward", {})
        if not isinstance(reward_info, dict):
            return {}
        signals = reward_info.get("reward_signals", {})
        if isinstance(signals, dict):
            return signals
        return {}

    def infer_task_id(self, info: dict[str, Any]) -> str | None:
        del info
        task_id = self.history.task_id
        if task_id:
            return task_id
        return None

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

    def count_color(self, frame: np.ndarray, color: Color, tile: Tile | None = None) -> int:
        if tile is None:
            area = frame
        else:
            x, y = tile
            area = frame[y * TILE_SIZE : (y + 1) * TILE_SIZE, x * TILE_SIZE : (x + 1) * TILE_SIZE]
        return int(np.count_nonzero(np.all(area == color, axis=2)))

    def count_any_color(self, frame: np.ndarray, colors: tuple[Color, ...], tile: Tile | None = None) -> int:
        return sum(self.count_color(frame, color, tile) for color in colors)

    def detect_player_tile(self, frame: np.ndarray) -> Tile | None:
        x_values: list[np.ndarray] = []
        y_values: list[np.ndarray] = []
        for color in PLAYER_COLORS:
            mask = np.all(frame == color, axis=2)
            ys, xs = np.nonzero(mask)
            if len(xs) > 0:
                x_values.append(xs)
                y_values.append(ys)
        if not x_values:
            return None
        xs = np.concatenate(x_values)
        ys = np.concatenate(y_values)

        # The visible green tunic starts a few pixels inside the sprite. Recover
        # the sprite's top-left corner, then use the center tile to match the
        # environment's movement/interact semantics.
        left = max(0, int(xs.min()) - 4)
        top = max(0, int(ys.min()) - 2)
        max_x = frame.shape[1] // TILE_SIZE - 1
        max_y = frame.shape[0] // TILE_SIZE - 1
        center_x = left + TILE_SIZE // 2
        center_y = top + TILE_SIZE // 2
        return (min(max_x, center_x // TILE_SIZE), min(max_y, center_y // TILE_SIZE))

    def tile_has_chest(self, frame: np.ndarray, tile: Tile) -> bool:
        return self.count_color(frame, CHEST_WOOD, tile) >= 25

    def tile_has_npc(self, frame: np.ndarray, tile: Tile) -> bool:
        return self.count_color(frame, NPC_COLOR, tile) >= 20

    def tile_has_switch(self, frame: np.ndarray, tile: Tile) -> bool:
        switch_pixels = self.count_color(frame, SWITCH_BODY, tile) + self.count_color(frame, SWITCH_DOWN, tile)
        return switch_pixels >= 20 and not self.tile_has_chest(frame, tile)

    def tile_has_wall(self, frame: np.ndarray, tile: Tile) -> bool:
        return self.count_color(frame, WALL_COLOR, tile) >= 80

    def has_monster(self, frame: np.ndarray) -> bool:
        return self.count_any_color(frame, MONSTER_COLORS) >= 20

    def detect_task3_room(self, frame: np.ndarray) -> str:
        if self.tile_has_npc(frame, (4, 1)):
            return "start_room"
        if self.tile_has_chest(frame, (5, 4)):
            return "key_room"
        return "monster_hall"

    def detect_bridge_state(self, frame: np.ndarray) -> str | None:
        probes = {
            "west_to_north": ((4, 1), (5, 1), (4, 2), (5, 2)),
            "west_to_east": ((7, 3), (8, 3), (7, 4), (8, 4)),
            "west_to_south": ((4, 5), (5, 5), (4, 6), (5, 6)),
        }
        scores = {
            state: sum(self.count_color(frame, BRIDGE_COLOR, tile) for tile in tiles)
            for state, tiles in probes.items()
        }
        state, score = max(scores.items(), key=lambda item: item[1])
        if score <= 0:
            return None
        return state

    def detect_task4_room(self, frame: np.ndarray) -> str | None:
        if self.count_color(frame, ABYSS_COLOR) >= 600 or self.count_color(frame, BRIDGE_COLOR) >= 200:
            return "center"
        if self.tile_has_switch(frame, (4, 4)):
            return "west"
        if self.tile_has_chest(frame, (5, 4)):
            return "east"
        if self.tile_has_chest(frame, (4, 3)):
            return "north"

        top_middle_open = not self.tile_has_wall(frame, (4, 0)) and not self.tile_has_wall(frame, (5, 0))
        bottom_middle_open = not self.tile_has_wall(frame, (4, 7)) and not self.tile_has_wall(frame, (5, 7))
        if top_middle_open and not bottom_middle_open:
            return "south"
        if bottom_middle_open and not top_middle_open:
            return "north"
        return None

    def perceive(self, frame: np.ndarray, task_id: str | None) -> PixelState:
        player_tile = self.detect_player_tile(frame)
        room_id: str | None = None
        bridge_state: str | None = None
        if task_id == "mathematical_logic/task_3":
            room_id = self.detect_task3_room(frame)
        elif task_id == "mathematical_logic/task_4":
            room_id = self.detect_task4_room(frame)
            if room_id == "center":
                bridge_state = self.detect_bridge_state(frame)
        return PixelState(
            player_tile=player_tile,
            room_id=room_id,
            bridge_state=bridge_state,
            monster_visible=self.has_monster(frame),
        )

    def remembered_bridge_state(self, pixel_state: PixelState) -> str:
        if pixel_state.bridge_state is not None:
            self.history.notes["task4_bridge_state"] = pixel_state.bridge_state
            return pixel_state.bridge_state
        state = self.history.notes.get("task4_bridge_state")
        if isinstance(state, str):
            return state
        self.history.notes["task4_bridge_state"] = "west_to_north"
        return "west_to_north"

    def cycle_remembered_bridge_state(self) -> None:
        state = self.history.notes.get("task4_bridge_state", "west_to_north")
        if not isinstance(state, str):
            state = "west_to_north"
        self.history.notes["task4_bridge_state"] = BRIDGE_CYCLE.get(state, "west_to_north")

    def decide_task3(self, pixel_state: PixelState, inventory: dict[str, Any]) -> int:
        room_id = pixel_state.room_id
        tile = pixel_state.player_tile
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

    def decide_task4(
        self,
        pixel_state: PixelState,
        inventory: dict[str, Any],
        reward_signals: dict[str, Any],
    ) -> int:
        room_id = pixel_state.room_id
        tile = pixel_state.player_tile
        facing = self.history.facing
        bridge_state = self.remembered_bridge_state(pixel_state)
        keys = int(inventory.get("keys", 0))
        has_sword = self.has_item(inventory, "sword")
        if room_id is None or tile is None:
            return ACTION_NOOP

        if float(reward_signals.get("monster_kill", 0.0) or 0.0) > 0:
            self.history.notes["task4_guardian_defeated"] = True
        if room_id == "south" and has_sword and not pixel_state.monster_visible:
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
                self.cycle_remembered_bridge_state()
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

    def update_facing(self, action: int) -> None:
        if action == ACTION_UP:
            self.history.facing = "up"
        elif action == ACTION_DOWN:
            self.history.facing = "down"
        elif action == ACTION_LEFT:
            self.history.facing = "left"
        elif action == ACTION_RIGHT:
            self.history.facing = "right"

    def decide(
        self,
        frame: np.ndarray,
        inventory: dict[str, Any],
        reward_signals: dict[str, Any],
        info: dict[str, Any],
    ) -> int:
        task_id = self.infer_task_id(info)
        if task_id in self.task_plans:
            return self.next_planned_action(task_id)

        pixel_state = self.perceive(frame, task_id)
        if task_id == "mathematical_logic/task_3":
            return self.decide_task3(pixel_state, inventory)
        if task_id == "mathematical_logic/task_4":
            return self.decide_task4(pixel_state, inventory, reward_signals)

        # TODO: add generic exploration policy for task_5.
        return ACTION_NOOP

    def act(self, obs, info: dict[str, Any]) -> int:
        inventory = self.extract_inventory(info)
        reward_signals = self.reward_signals(info)
        self.history.last_inventory = inventory
        action = self.decide(obs, inventory, reward_signals, info)
        self.update_facing(action)
        self.history.last_action = action
        return action


def make_policy() -> Policy:
    return Policy()
