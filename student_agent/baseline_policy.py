from __future__ import annotations

from collections import deque
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
    GRID_HEIGHT,
    GRID_WIDTH,
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
BUTTON_UP: Color = (40, 190, 74)
BUTTON_DOWN_COLOR: Color = (28, 112, 52)

# Trap spike pixels (sprites.py:39-41). Distinctive against floor/wall colors.
TRAP_SPIKE_METAL: Color = (238, 238, 236)
TRAP_SPIKE_SHADE: Color = (112, 112, 126)

# Exit tile positions per direction (schema.py:30-35) and the action that
# triggers the exit once standing on one of its tiles.
EXIT_DIRECTION_TILES: dict[str, tuple[Tile, Tile]] = {
    "north": ((4, 0), (5, 0)),
    "south": ((4, GRID_HEIGHT - 1), (5, GRID_HEIGHT - 1)),
    "west": ((0, 3), (0, 4)),
    "east": ((GRID_WIDTH - 1, 3), (GRID_WIDTH - 1, 4)),
}
EXIT_DIRECTION_ACTION: dict[str, int] = {
    "north": ACTION_UP,
    "south": ACTION_DOWN,
    "west": ACTION_LEFT,
    "east": ACTION_RIGHT,
}


BRIDGE_CYCLE = {
    "west_to_north": "west_to_east",
    "west_to_east": "west_to_south",
    "west_to_south": "west_to_north",
}


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

    def reset(self) -> None:
        # 新版评测脚本无参数调用 reset()。task_id 改由 info["task_id"] 在
        # act() 中获取（仅 --task-policy 模式提供）。
        self.history = AgentHistory()

    def extract_inventory(self, info: dict[str, Any]) -> dict[str, Any]:
        inventory = info.get("inventory", {})
        if isinstance(inventory, dict):
            return dict(inventory)
        return {}

    def extract_last_reward(self, info: dict[str, Any]) -> float:
        # safe 模式下 info["last_reward"] 为上一步标量奖励，reset 后首次为 0.0。
        return float(info.get("last_reward", 0.0) or 0.0)

    def update_memory_from_safe(
        self,
        inventory: dict[str, Any],
        last_reward: float,
        frame: np.ndarray,
    ) -> None:
        # safe 模式下没有 reward_signals，改为基于 inventory diff + last_reward
        # 推断事件。图像感知由各 task 的 decide 函数自行处理。
        notes = self.history.notes
        prev = self.history.last_inventory or {}
        if int(inventory.get("keys", 0)) > int(prev.get("keys", 0) or 0):
            notes["mem_keys_collected"] = int(notes.get("mem_keys_collected", 0) or 0) + 1
            notes["mem_key_collected"] = True
        if int(inventory.get("gold", 0)) > int(prev.get("gold", 0) or 0):
            notes["mem_gold_collected"] = True
        prev_items = set(prev.get("items", []) or [])
        curr_items = set(inventory.get("items", []) or [])
        if curr_items - prev_items:
            notes["mem_item_collected"] = True
        notes["mem_last_reward"] = last_reward
        notes["mem_reward_positive"] = last_reward > 0

    def current_keys(self, inventory: dict[str, Any]) -> int:
        # safe 模式下 reward_signals 不可用，直接用 inventory.keys。
        return int(inventory.get("keys", 0))

    def infer_task_id(self, info: dict[str, Any]) -> str | None:
        # safe 模式下 task_id 通过 info["task_id"] 传入（--task-policy 模式）。
        task_id = info.get("task_id")
        if task_id:
            self.history.task_id = task_id
            return task_id
        return self.history.task_id

    def has_item(self, inventory: dict[str, Any], item_id: str) -> bool:
        items = inventory.get("items", [])
        if isinstance(items, (list, tuple)):
            return item_id in items
        return False

    def in_bounds(self, tile: Tile) -> bool:
        x, y = tile
        return 0 <= x < GRID_WIDTH and 0 <= y < GRID_HEIGHT

    def detect_monster_tile(self, frame: np.ndarray) -> Tile | None:
        if not self.has_monster(frame):
            return None
        x_values: list[np.ndarray] = []
        y_values: list[np.ndarray] = []
        for color in MONSTER_COLORS:
            mask = np.all(frame == color, axis=2)
            ys, xs = np.nonzero(mask)
            if len(xs) > 0:
                x_values.append(xs)
                y_values.append(ys)
        if not x_values:
            return None
        xs = np.concatenate(x_values)
        ys = np.concatenate(y_values)
        max_x = GRID_WIDTH - 1
        max_y = GRID_HEIGHT - 1
        center_x = int(xs.mean())
        center_y = int(ys.mean())
        return (min(max_x, center_x // TILE_SIZE), min(max_y, center_y // TILE_SIZE))

    def detect_all_monster_tiles(self, frame: np.ndarray) -> list[Tile]:
        # Detect all distinct monster tiles by clustering pixels.
        if not self.has_monster(frame):
            return []
        tiles: set[Tile] = set()
        for color in MONSTER_COLORS:
            mask = np.all(frame == color, axis=2)
            ys, xs = np.nonzero(mask)
            for x, y in zip(xs, ys):
                tile = (min(GRID_WIDTH - 1, x // TILE_SIZE), min(GRID_HEIGHT - 1, y // TILE_SIZE))
                tiles.add(tile)
        return list(tiles)

    def detect_closest_monster_tile(self, frame: np.ndarray, agent_tile: Tile) -> Tile | None:
        monsters = self.detect_all_monster_tiles(frame)
        if not monsters:
            return None
        ax, ay = agent_tile
        best = None
        best_dist = 999
        for mx, my in monsters:
            dist = abs(mx - ax) + abs(my - ay)
            if dist < best_dist:
                best = (mx, my)
                best_dist = dist
        return best

    def facing_toward(self, dx: int, dy: int) -> str:
        if dx > 0:
            return "right"
        if dx < 0:
            return "left"
        if dy > 0:
            return "down"
        if dy < 0:
            return "up"
        return self.history.facing

    def attack_monster(self, tile: Tile, monster_tile: Tile, blocked: set[Tile] | None = None, player_px: tuple[float, float] | None = None) -> int:
        # Attack a monster at monster_tile. When adjacent (distance=1), face the
        # monster and press A. When farther away, BFS to the closest adjacent
        # tile using the provided blocked set (if available) or an empty set.
        px, py = tile
        mx, my = monster_tile
        dx = mx - px
        dy = my - py
        manhattan = abs(dx) + abs(dy)
        if manhattan <= 0:
            return ACTION_NOOP

        if manhattan == 1:
            desired = self.facing_toward(dx, dy)
            if self.history.facing == desired:
                return ACTION_A
            # Wrong facing: back off along the monster axis (away from monster)
            # to re-approach on a straight line that sets the correct facing.
            if desired == "right":
                return ACTION_LEFT
            if desired == "left":
                return ACTION_RIGHT
            if desired == "down":
                return ACTION_UP
            return ACTION_DOWN

        # manhattan >= 2: BFS to the closest valid adjacent tile.
        candidates = (
            ((mx - 1, my), False),
            ((mx + 1, my), False),
            ((mx, my - 1), True),
            ((mx, my + 1), True),
        )
        valid = [c for c in candidates if self.in_bounds(c[0])]
        if not valid:
            return ACTION_NOOP

        def dist_to(c: tuple[Tile, bool]) -> int:
            ax, ay = c[0]
            return abs(ax - px) + abs(ay - py)

        target, x_first = min(valid, key=dist_to)
        # Use BFS with pixel alignment if blocked set is provided.
        if blocked is not None and player_px is not None:
            return self.follow_bfs_aligned(player_px, tile, {target}, blocked, final_action=ACTION_A)
        if blocked is not None:
            return self.follow_bfs(tile, {target}, blocked, x_first=x_first, final_action=ACTION_A)
        # Fallback to simple move_towards when no blocked set is provided.
        return self.move_towards(tile, target, x_first=x_first)

    def count_color(self, frame: np.ndarray, color: Color, tile: Tile | None = None) -> int:
        if tile is None:
            area = frame
        else:
            x, y = tile
            area = frame[y * TILE_SIZE : (y + 1) * TILE_SIZE, x * TILE_SIZE : (x + 1) * TILE_SIZE]
        return int(np.count_nonzero(np.all(area == color, axis=2)))

    def count_any_color(self, frame: np.ndarray, colors: tuple[Color, ...], tile: Tile | None = None) -> int:
        return sum(self.count_color(frame, color, tile) for color in colors)

    def detect_player_px(self, frame: np.ndarray) -> tuple[int, int] | None:
        # The visible green tunic starts a few pixels inside the sprite. Recover
        # the sprite's true top-left pixel position so pixel-aligned navigation
        # can avoid clipping walls when squeezing through 1-tile gaps.
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
        left = max(0, int(xs.min()) - 4)
        top = max(0, int(ys.min()) - 2)
        return (left, top)

    def detect_player_tile(self, frame: np.ndarray) -> Tile | None:
        pos = self.detect_player_px(frame)
        if pos is None:
            return None
        left, top = pos
        max_x = frame.shape[1] // TILE_SIZE - 1
        max_y = frame.shape[0] // TILE_SIZE - 1
        # Use the sprite center to match the engine's tile semantics.
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

    def tile_has_button(self, frame: np.ndarray, tile: Tile) -> bool:
        button_pixels = self.count_color(frame, BUTTON_UP, tile) + self.count_color(frame, BUTTON_DOWN_COLOR, tile)
        return button_pixels >= 20 and not self.tile_has_chest(frame, tile)

    def tile_has_wall(self, frame: np.ndarray, tile: Tile) -> bool:
        return self.count_color(frame, WALL_COLOR, tile) >= 80

    def tile_has_trap(self, frame: np.ndarray, tile: Tile) -> bool:
        metal = self.count_color(frame, TRAP_SPIKE_METAL, tile)
        shade = self.count_color(frame, TRAP_SPIKE_SHADE, tile)
        return metal + shade >= 15

    def tile_has_abyss(self, frame: np.ndarray, tile: Tile) -> bool:
        # Abyss tiles are rendered as (0,0,0). A tile is an unwalkable abyss
        # if it is mostly black AND does not have bridge pixels on top.
        black = self.count_color(frame, (0, 0, 0), tile)
        bridge = self.count_color(frame, BRIDGE_COLOR, tile)
        return black >= 180 and bridge < 25

    def has_monster(self, frame: np.ndarray) -> bool:
        return self.count_any_color(frame, MONSTER_COLORS) >= 20

    def detect_chest_tile(self, frame: np.ndarray) -> Tile | None:
        for y in range(GRID_HEIGHT):
            for x in range(GRID_WIDTH):
                if self.tile_has_chest(frame, (x, y)):
                    return (x, y)
        return None

    def detect_button_tile(self, frame: np.ndarray) -> Tile | None:
        for y in range(GRID_HEIGHT):
            for x in range(GRID_WIDTH):
                if self.tile_has_button(frame, (x, y)):
                    return (x, y)
        return None

    def detect_switch_tile(self, frame: np.ndarray) -> Tile | None:
        for y in range(GRID_HEIGHT):
            for x in range(GRID_WIDTH):
                if self.tile_has_switch(frame, (x, y)):
                    return (x, y)
        return None

    def neighbors_of(self, tile: Tile) -> list[Tile]:
        x, y = tile
        return [(x, y - 1), (x, y + 1), (x - 1, y), (x + 1, y)]

    def build_blocked_tiles(self, frame: np.ndarray, *, avoid_traps: bool) -> set[Tile]:
        # Scan the visible grid for non-walkable tiles: walls, abyss (always
        # blocked — bridge tiles overlay the abyss so they are NOT flagged),
        # spike traps (when requested), and chests (always blocking).
        blocked: set[Tile] = set()
        for y in range(GRID_HEIGHT):
            for x in range(GRID_WIDTH):
                tile = (x, y)
                if self.tile_has_wall(frame, tile):
                    blocked.add(tile)
                elif self.tile_has_abyss(frame, tile):
                    blocked.add(tile)
                elif avoid_traps and self.tile_has_trap(frame, tile):
                    blocked.add(tile)
                elif self.tile_has_chest(frame, tile):
                    blocked.add(tile)
        return blocked

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
        top_middle_open = not self.tile_has_wall(frame, (4, 0)) and not self.tile_has_wall(frame, (5, 0))
        bottom_middle_open = not self.tile_has_wall(frame, (4, 7)) and not self.tile_has_wall(frame, (5, 7))
        if top_middle_open and not bottom_middle_open:
            return "south"
        if bottom_middle_open and not top_middle_open:
            return "north"
        if self.detect_switch_tile(frame) is not None:
            return "west"
        return "east"

    def detect_task5_room(self, frame: np.ndarray) -> str | None:
        # South room has a distinctive wall pattern at y=2 (x=2-7) and y=6 (x=4).
        # Detect this pattern first as it's more reliable than chest pixels on
        # entry. The key chest is at (8,5) which may not render immediately.
        south_walls = [(2, 2), (3, 2), (4, 2), (5, 2), (6, 2), (7, 2), (4, 6)]
        if all(self.tile_has_wall(frame, t) for t in south_walls):
            return "task5_south"
        # East room has walls at (5,1), (6,1), (5,2), (6,2).
        east_walls = [(5, 1), (6, 1), (5, 2), (6, 2)]
        if all(self.tile_has_wall(frame, t) for t in east_walls):
            return "task5_east"
        # West room has walls at (6,1), (5,2), (5,3), (3,5), (4,5).
        west_walls = [(6, 1), (5, 2), (5, 3), (3, 5), (4, 5)]
        if all(self.tile_has_wall(frame, t) for t in west_walls):
            return "task5_west"
        # Start room fallback: chest at (4,2) or button at (2,6).
        if self.tile_has_chest(frame, (4, 2)) or self.tile_has_button(frame, (2, 6)):
            return "task5_start"
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
        elif task_id == "mathematical_logic/task_5":
            room_id = self.detect_task5_room(frame)
            # Fallback: if detection failed, use the last known room from history.
            if room_id is None:
                room_id = self.history.notes.get("task5_last_room")
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

    def decide_task1(self, pixel_state: PixelState, inventory: dict[str, Any], frame: np.ndarray) -> int:
        # Task 1: navigate to the key chest, then to the north exit. Walls are
        # perceived from the frame; BFS finds the shortest tile path through the
        # detected gaps. A pixel-alignment guard ensures the sprite clears 1-tile
        # wall gaps instead of straddling them. No hardcoded waypoints.
        tile = pixel_state.player_tile
        if tile is None:
            return ACTION_NOOP
        player_px = self.detect_player_px(frame)
        if player_px is None:
            return ACTION_NOOP
        keys = self.current_keys(inventory)
        blocked = self.build_blocked_tiles(frame, avoid_traps=False)
        if keys <= 0:
            chest = self.detect_chest_tile(frame)
            if chest is None:
                return ACTION_NOOP
            goals = {n for n in self.neighbors_of(chest) if self.in_bounds(n) and n not in blocked}
            return self.follow_bfs_aligned(
                player_px,
                tile,
                goals,
                blocked,
                final_action=ACTION_A,
            )
        exit_goals = set(EXIT_DIRECTION_TILES["north"])
        return self.follow_bfs_aligned(
            player_px,
            tile,
            exit_goals,
            blocked,
            final_action=EXIT_DIRECTION_ACTION["north"],
        )

    def decide_task2(
        self,
        pixel_state: PixelState,
        inventory: dict[str, Any],
        frame: np.ndarray,
    ) -> int:
        # Task 2: defeat the chaser monster, then navigate to the key chest,
        # then to the west exit. Traps (border rows) are perceived from the
        # frame and treated as blocked; BFS finds the shortest safe tile path.
        # Pixel-alignment prevents the sprite from colliding with the chest on
        # an adjacent row when moving horizontally past it. No hardcoded waypoints.
        tile = pixel_state.player_tile
        if tile is None:
            return ACTION_NOOP
        player_px = self.detect_player_px(frame)
        if player_px is None:
            return ACTION_NOOP
        monster_tile = self.detect_monster_tile(frame)
        if monster_tile is not None:
            return self.attack_monster(tile, monster_tile)
        keys = self.current_keys(inventory)
        blocked = self.build_blocked_tiles(frame, avoid_traps=True)
        if keys <= 0:
            chest = self.detect_chest_tile(frame)
            if chest is None:
                return ACTION_NOOP
            goals = {n for n in self.neighbors_of(chest) if self.in_bounds(n) and n not in blocked}
            return self.follow_bfs_aligned(
                player_px,
                tile,
                goals,
                blocked,
                final_action=ACTION_A,
            )
        exit_goals = set(EXIT_DIRECTION_TILES["west"])
        return self.follow_bfs_aligned(
            player_px,
            tile,
            exit_goals,
            blocked,
            final_action=EXIT_DIRECTION_ACTION["west"],
        )

    def decide_task3(self, pixel_state: PixelState, inventory: dict[str, Any], frame: np.ndarray) -> int:
        # Task 3: three rooms connected west→east: key_room ↔ monster_hall ↔ start_room.
        # No keys → navigate to the key chest (in key_room). Has keys → navigate
        # to the east exit (in start_room, locked_key). BFS handles within-room
        # wall avoidance automatically.
        room_id = pixel_state.room_id
        tile = pixel_state.player_tile
        keys = self.current_keys(inventory)
        if room_id is None or tile is None:
            return ACTION_NOOP

        player_px = self.detect_player_px(frame)
        blocked = self.build_blocked_tiles(frame, avoid_traps=False)

        if keys <= 0:
            if room_id == "key_room":
                chest = self.detect_chest_tile(frame)
                if chest is not None:
                    return self.navigate_to_goal(tile, chest, blocked, player_px=player_px, final_action=ACTION_A)
            # In start_room or monster_hall: head west toward key_room.
            return self.navigate_to_exit(tile, "west", blocked, player_px=player_px)

        # Has keys: head east toward the locked exit in start_room.
        return self.navigate_to_exit(tile, "east", blocked, player_px=player_px)

    def decide_task4(
        self,
        pixel_state: PixelState,
        inventory: dict[str, Any],
        frame: np.ndarray,
    ) -> int:
        # Task 4: five rooms around a center hub with a rotating bridge.
        # Stage management (get_key → get_sword → kill_guardian → open_final_chest)
        # and bridge-cycling logic are preserved; within-room navigation is
        # replaced by BFS so the agent doesn't need hardcoded direction logic.
        room_id = pixel_state.room_id
        tile = pixel_state.player_tile
        facing = self.history.facing
        bridge_state = self.remembered_bridge_state(pixel_state)
        keys = int(inventory.get("keys", 0))
        has_sword = self.has_item(inventory, "sword")
        if room_id is None or tile is None:
            return ACTION_NOOP

        # safe 模式下无 reward_signals，用图像感知判断 guardian 是否被击杀：
        # 在 south 房间有剑且怪物不可见则视为已击败。
        if room_id == "south" and has_sword and not pixel_state.monster_visible:
            self.history.notes["task4_guardian_defeated"] = True

        guardian_defeated = bool(self.history.notes.get("task4_guardian_defeated", False))

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

        blocked = self.build_blocked_tiles(frame, avoid_traps=False)
        player_px = self.detect_player_px(frame)

        if room_id == "west":
            if bridge_state != desired_bridge:
                switch = self.detect_switch_tile(frame)
                if switch is not None:
                    # Walk to a tile adjacent to the switch, face it, interact.
                    face_action = self.adjacent_goal_action(tile, switch)
                    if face_action is not None:
                        if self.history.facing != {
                            ACTION_RIGHT: "right",
                            ACTION_LEFT: "left",
                            ACTION_DOWN: "down",
                            ACTION_UP: "up",
                        }.get(face_action):
                            return face_action
                        # Facing the switch: interact once, then update bridge memory.
                        self.cycle_remembered_bridge_state()
                        return ACTION_A
                    goals = {n for n in self.neighbors_of(switch) if self.in_bounds(n) and n not in blocked}
                    if player_px is not None:
                        return self.follow_bfs_aligned(player_px, tile, goals, blocked, final_action=ACTION_A)
                    return self.follow_bfs(tile, goals, blocked, x_first=True, final_action=ACTION_A)
            # Bridge is correct: exit east.
            return self.navigate_to_exit(tile, "east", blocked, player_px=player_px)

        if room_id == "center":
            if stage == "get_key":
                return self.navigate_to_exit(tile, "north", blocked, player_px=player_px)
            if stage == "get_sword":
                if bridge_state != desired_bridge:
                    return self.navigate_to_exit(tile, "west", blocked, player_px=player_px)
                return self.navigate_to_exit(tile, "east", blocked, player_px=player_px)
            if stage == "kill_guardian":
                if bridge_state != desired_bridge:
                    return self.navigate_to_exit(tile, "west", blocked, player_px=player_px)
                return self.navigate_to_exit(tile, "south", blocked, player_px=player_px)
            # open_final_chest: guardian defeated, chest should be visible.
            chest = self.detect_chest_tile(frame)
            if chest is not None:
                return self.navigate_to_goal(tile, chest, blocked, player_px=player_px, final_action=ACTION_A)
            return self.navigate_to_exit(tile, "south", blocked, player_px=player_px)

        if room_id == "north":
            if stage != "get_key":
                return self.navigate_to_exit(tile, "south", blocked, player_px=player_px)
            chest = self.detect_chest_tile(frame)
            if chest is not None:
                return self.navigate_to_goal(tile, chest, blocked, player_px=player_px, final_action=ACTION_A)
            return self.navigate_to_exit(tile, "south", blocked, player_px=player_px)

        if room_id == "east":
            if stage != "get_sword":
                return self.navigate_to_exit(tile, "west", blocked, player_px=player_px)
            chest = self.detect_chest_tile(frame)
            if chest is not None:
                # Need to face right to pick up the sword from the chest.
                face_action = self.adjacent_goal_action(tile, chest)
                if face_action is not None:
                    if self.history.facing != "right":
                        return ACTION_RIGHT
                    return ACTION_A
                goals = {n for n in self.neighbors_of(chest) if self.in_bounds(n) and n not in blocked}
                if player_px is not None:
                    return self.follow_bfs_aligned(player_px, tile, goals, blocked, final_action=ACTION_A)
                return self.follow_bfs(tile, goals, blocked, x_first=True, final_action=ACTION_A)
            return self.navigate_to_exit(tile, "west", blocked, player_px=player_px)

        if room_id == "south":
            if stage == "open_final_chest":
                return self.navigate_to_exit(tile, "north", blocked, player_px=player_px)
            # Kill the guardian monster.
            monster_tile = self.detect_monster_tile(frame)
            if monster_tile is not None:
                return self.attack_monster(tile, monster_tile)
            return self.navigate_to_exit(tile, "north", blocked, player_px=player_px)

        return ACTION_NOOP

    def move_towards(self, tile: Tile, target: Tile, *, x_first: bool = True) -> int:
        x, y = tile
        target_x, target_y = target
        if x_first:
            if x < target_x:
                return ACTION_RIGHT
            if x > target_x:
                return ACTION_LEFT
            if y < target_y:
                return ACTION_DOWN
            if y > target_y:
                return ACTION_UP
        else:
            if y < target_y:
                return ACTION_DOWN
            if y > target_y:
                return ACTION_UP
            if x < target_x:
                return ACTION_RIGHT
            if x > target_x:
                return ACTION_LEFT
        return ACTION_NOOP

    def follow_waypoints(
        self,
        tile: Tile,
        waypoints: tuple[Tile, ...],
        *,
        x_first: bool = True,
        final_action: int = ACTION_NOOP,
    ) -> int:
        for waypoint in waypoints:
            if tile != waypoint:
                return self.move_towards(tile, waypoint, x_first=x_first)
        return final_action

    def follow_route(
        self,
        route_key: str,
        tile: Tile,
        waypoints: tuple[Tile, ...],
        *,
        x_first: bool = True,
        final_action: int = ACTION_NOOP,
    ) -> int:
        index_key = f"{route_key}_waypoint_index"
        index = int(self.history.notes.get(index_key, 0) or 0)
        while index < len(waypoints) and tile == waypoints[index]:
            index += 1
        self.history.notes[index_key] = index
        if index >= len(waypoints):
            return final_action
        return self.move_towards(tile, waypoints[index], x_first=x_first)

    def move_towards_aligned(
        self,
        player_px: tuple[float, float],
        tile: Tile,
        target: Tile,
        *,
        x_first: bool = True,
    ) -> int:
        # Perception-driven move with a pixel-alignment guard. When the
        # primary axis matches the target, align pixels before moving on the
        # secondary axis to avoid straddling tile boundaries.
        px, py = player_px
        x, y = tile
        target_x, target_y = target
        if x_first:
            if x < target_x:
                return ACTION_RIGHT
            if x > target_x:
                return ACTION_LEFT
            col_left = x * TILE_SIZE
            if px < col_left:
                return ACTION_RIGHT
            if px > col_left + 1:
                return ACTION_LEFT
            if y < target_y:
                return ACTION_DOWN
            if y > target_y:
                return ACTION_UP
        else:
            if y < target_y:
                return ACTION_DOWN
            if y > target_y:
                return ACTION_UP
            row_top = y * TILE_SIZE
            if py < row_top:
                return ACTION_DOWN
            if py > row_top + 1:
                return ACTION_UP
            if x < target_x:
                return ACTION_RIGHT
            if x > target_x:
                return ACTION_LEFT
        return ACTION_NOOP

    def follow_route_aligned(
        self,
        route_key: str,
        player_px: tuple[float, float],
        tile: Tile,
        waypoints: tuple[Tile, ...],
        *,
        x_first: bool = True,
        final_action: int = ACTION_NOOP,
    ) -> int:
        if tile is None:
            return ACTION_NOOP
        index_key = f"{route_key}_waypoint_index"
        index = int(self.history.notes.get(index_key, 0) or 0)
        while index < len(waypoints) and tile == waypoints[index]:
            index += 1
        self.history.notes[index_key] = index
        if index >= len(waypoints):
            return final_action
        return self.move_towards_aligned(player_px, tile, waypoints[index], x_first=x_first)

    def bfs_path(
        self,
        start: Tile,
        goals: set[Tile],
        blocked: set[Tile],
    ) -> list[Tile] | None:
        # Breadth-first search over the 4-connected tile grid. ``blocked`` tiles
        # are not traversed unless they are also goals (e.g. exit tiles that sit
        # on the border). The path includes ``start`` as the first element.
        if start in goals:
            return [start]
        queue: deque[Tile] = deque([start])
        parent: dict[Tile, Tile | None] = {start: None}
        while queue:
            current = queue.popleft()
            for nxt in self.neighbors_of(current):
                if not self.in_bounds(nxt):
                    continue
                if nxt in parent:
                    continue
                if nxt in blocked and nxt not in goals:
                    continue
                parent[nxt] = current
                if nxt in goals:
                    path: list[Tile] = []
                    node: Tile | None = nxt
                    while node is not None:
                        path.append(node)
                        node = parent[node]
                    path.reverse()
                    return path
                queue.append(nxt)
        return None

    def follow_bfs(
        self,
        tile: Tile,
        goals: set[Tile],
        blocked: set[Tile],
        *,
        x_first: bool = True,
        final_action: int = ACTION_NOOP,
    ) -> int:
        # Perception-driven navigation: recompute the BFS path every step from
        # the current tile, then issue a single-tile move toward the next tile
        # in the path. No waypoint indices or hardcoded sequences.
        path = self.bfs_path(tile, goals, blocked)
        if path is None or len(path) <= 1:
            return final_action
        return self.move_towards(tile, path[1], x_first=x_first)

    def follow_bfs_aligned(
        self,
        player_px: tuple[float, float],
        tile: Tile,
        goals: set[Tile],
        blocked: set[Tile],
        *,
        final_action: int = ACTION_NOOP,
    ) -> int:
        # Same as follow_bfs but with a pixel-alignment guard so the sprite
        # clears 1-tile wall gaps and avoids pixel-level overlap with chests on
        # adjacent rows. The alignment axis is chosen automatically: before a
        # horizontal move the sprite is vertically aligned (so it doesn't
        # collide with blocked tiles on an adjacent row), and before a vertical
        # move the sprite is horizontally aligned (so it clears 1-tile wall
        # gaps).
        path = self.bfs_path(tile, goals, blocked)
        if path is None or len(path) <= 1:
            return final_action
        next_tile = path[1]
        dx = next_tile[0] - tile[0]
        dy = next_tile[1] - tile[1]
        # Vertical move → align x first (x_first=True); horizontal move → align y first (x_first=False).
        x_first = dy != 0
        return self.move_towards_aligned(player_px, tile, next_tile, x_first=x_first)

    def adjacent_goal_action(
        self,
        tile: Tile,
        goal: Tile,
    ) -> int | None:
        # If tile is adjacent to goal (not on goal), return the action that
        # faces toward the goal.  Returns None if not adjacent.
        dx = goal[0] - tile[0]
        dy = goal[1] - tile[1]
        if abs(dx) + abs(dy) != 1:
            return None
        if dx == 1:
            return ACTION_RIGHT
        if dx == -1:
            return ACTION_LEFT
        if dy == 1:
            return ACTION_DOWN
        return ACTION_UP

    def navigate_to_goal(
        self,
        tile: Tile,
        goal: Tile,
        blocked: set[Tile],
        *,
        player_px: tuple[float, float] | None = None,
        final_action: int = ACTION_A,
        walk_onto: bool = False,
    ) -> int:
        # Navigate to a goal tile and interact. Two modes:
        #  walk_onto=False (default): goal tile is blocking (chest, switch), so
        #    navigate to an adjacent tile, face the goal, then interact.
        #  walk_onto=True: goal tile is walkable (button), so navigate onto the
        #    goal tile itself, then interact.
        if walk_onto:
            if tile == goal:
                return final_action
            if player_px is not None:
                return self.follow_bfs_aligned(player_px, tile, {goal}, blocked, final_action=final_action)
            return self.follow_bfs(tile, {goal}, blocked, x_first=True, final_action=final_action)
        face_action = self.adjacent_goal_action(tile, goal)
        if face_action is not None:
            # Already adjacent: face the goal, then interact on the next step.
            if self.history.facing != {
                ACTION_RIGHT: "right",
                ACTION_LEFT: "left",
                ACTION_DOWN: "down",
                ACTION_UP: "up",
            }.get(face_action):
                return face_action
            return final_action
        # Not adjacent yet: BFS to any walkable neighbor of the goal.
        goals = {n for n in self.neighbors_of(goal) if self.in_bounds(n) and n not in blocked}
        if player_px is not None:
            return self.follow_bfs_aligned(player_px, tile, goals, blocked, final_action=final_action)
        return self.follow_bfs(tile, goals, blocked, x_first=True, final_action=final_action)

    def navigate_to_exit(
        self,
        tile: Tile,
        direction: str,
        blocked: set[Tile],
        *,
        player_px: tuple[float, float] | None = None,
    ) -> int:
        # BFS to the exit tiles for the given direction, then issue the
        # direction action to transition. Uses pixel-alignment when available.
        exit_goals = set(EXIT_DIRECTION_TILES[direction])
        if player_px is not None:
            return self.follow_bfs_aligned(player_px, tile, exit_goals, blocked, final_action=EXIT_DIRECTION_ACTION[direction])
        return self.follow_bfs(tile, exit_goals, blocked, x_first=True, final_action=EXIT_DIRECTION_ACTION[direction])

    def update_task5_memory(
        self,
        pixel_state: PixelState,
        inventory: dict[str, Any],
        last_reward: float,
        frame: np.ndarray,
    ) -> None:
        # safe 模式下无 reward_signals，基于 inventory diff + last_reward + 图像感知推断事件。
        room_id = pixel_state.room_id
        notes = self.history.notes
        if room_id is not None:
            notes["task5_last_room"] = room_id
        else:
            room_id = notes.get("task5_last_room")

        # key_collected: inventory.keys 增加
        prev = self.history.last_inventory or {}
        if int(inventory.get("keys", 0)) > int(prev.get("keys", 0) or 0):
            notes["task5_key_collected"] = True

        # 上一步按了 A 且 last_reward > 0：可能是 chest_opened / button_pressed / monster_kill
        last_action = self.history.last_action
        reward_positive = last_reward > 0
        if last_action == ACTION_A and reward_positive:
            # chest_opened：当前房间标记
            if room_id == "task5_start" and not notes.get("task5_start_chest_opened"):
                notes["task5_start_chest_opened"] = True
            elif room_id == "task5_south" and not notes.get("task5_south_chest_opened"):
                notes["task5_south_chest_opened"] = True
            elif room_id == "task5_east" and not notes.get("task5_east_chest_opened"):
                notes["task5_east_chest_opened"] = True
            elif room_id == "task5_west" and not notes.get("task5_west_chest_opened"):
                notes["task5_west_chest_opened"] = True
            # button_pressed：上一步在按钮附近按 A 且有奖励
            if not notes.get("task5_button_pressed"):
                notes["task5_button_pressed"] = True
            # door_opened：上一步在出口按方向键且 last_reward > 0（此处 action==A 不覆盖）

        # monster_kill：上步有怪物 + 本步无怪物 + last_reward > 0
        prev_monster = notes.get("task5_prev_monster_visible", False)
        curr_monster = pixel_state.monster_visible
        if prev_monster and not curr_monster and reward_positive:
            notes["task5_start_monster_cleared"] = True
        notes["task5_prev_monster_visible"] = curr_monster

        # monster_hit：last_reward > 0 且怪物仍可见
        if reward_positive and curr_monster:
            hits = int(notes.get("task5_start_monster_hits", 0) or 0)
            notes["task5_start_monster_hits"] = hits + 1

        # door_opened / east_gate：last_reward > 0 且房间发生变化时标记
        prev_room = notes.get("task5_prev_room")
        if prev_room is not None and room_id is not None and prev_room != room_id and reward_positive:
            notes["task5_east_gate_opened"] = True
        if room_id is not None:
            notes["task5_prev_room"] = room_id

    def task5_stage(self, inventory: dict[str, Any]) -> str:
        keys = int(inventory.get("keys", 0))
        notes = self.history.notes
        if not bool(notes.get("task5_start_chest_opened", False)):
            return "open_start_chest"
        if not bool(notes.get("task5_button_pressed", False)):
            return "press_button"
        if not bool(notes.get("task5_south_chest_opened", False)):
            return "open_south_chest"
        if not bool(notes.get("task5_east_chest_opened", False)):
            return "open_east_chest" if keys > 0 or bool(notes.get("task5_east_gate_opened", False)) else "open_south_chest"
        if not bool(notes.get("task5_west_chest_opened", False)):
            return "open_west_chest"
        return "done"

    def decide_task5(
        self,
        pixel_state: PixelState,
        inventory: dict[str, Any],
        last_reward: float,
        frame: np.ndarray,
    ) -> int:
        # Task 5: four rooms with chests, button, locked gate, and monsters.
        # Stage management (which chest to open next) is preserved; within-room
        # navigation uses BFS with pixel alignment so hardcoded waypoints and
        # manual alignment ticks are eliminated.
        self.update_task5_memory(pixel_state, inventory, last_reward, frame)
        room_id = pixel_state.room_id
        tile = pixel_state.player_tile
        if room_id is None or tile is None:
            return ACTION_NOOP

        stage = self.task5_stage(inventory)
        if stage == "done":
            return ACTION_NOOP

        blocked = self.build_blocked_tiles(frame, avoid_traps=True)
        player_px = self.detect_player_px(frame)

        if room_id == "task5_start":
            if stage == "open_start_chest":
                chest = self.detect_chest_tile(frame)
                if chest is not None:
                    return self.navigate_to_goal(tile, chest, blocked, player_px=player_px, final_action=ACTION_A)

            if stage in {"press_button", "open_south_chest"}:
                if stage == "press_button":
                    button = self.detect_button_tile(frame)
                    if button is not None:
                        return self.navigate_to_goal(tile, button, blocked, player_px=player_px, final_action=ACTION_A, walk_onto=True)
                return self.navigate_to_exit(tile, "south", blocked, player_px=player_px)

            if stage == "open_east_chest":
                if not bool(self.history.notes.get("task5_start_monster_cleared", False)):
                    monster_tile = self.detect_monster_tile(frame)
                    if monster_tile is not None:
                        return self.attack_monster(tile, monster_tile)
                    self.history.notes["task5_start_monster_cleared"] = True
                return self.navigate_to_exit(tile, "east", blocked, player_px=player_px)

            if stage == "open_west_chest":
                return self.navigate_to_exit(tile, "west", blocked, player_px=player_px)

        if room_id == "task5_south":
            if stage == "open_south_chest":
                # South room's patroller is passive; ignore it and navigate to chest directly.
                chest = self.detect_chest_tile(frame)
                # Fallback: if chest detection failed, use the known chest position (8,5).
                if chest is None:
                    chest = (8, 5)
                return self.navigate_to_goal(tile, chest, blocked, player_px=player_px, final_action=ACTION_A)
            return self.navigate_to_exit(tile, "north", blocked, player_px=player_px)

        if room_id == "task5_east":
            if stage == "open_east_chest":
                if not bool(self.history.notes.get("task5_east_monster_cleared", False)):
                    monster_tile = self.detect_monster_tile(frame)
                    if monster_tile is not None:
                        return self.attack_monster(tile, monster_tile)
                    self.history.notes["task5_east_monster_cleared"] = True
                chest = self.detect_chest_tile(frame)
                if chest is not None:
                    return self.navigate_to_goal(tile, chest, blocked, player_px=player_px, final_action=ACTION_A)
            return self.navigate_to_exit(tile, "west", blocked, player_px=player_px)

        if room_id == "task5_west":
            if stage == "open_west_chest":
                if not bool(self.history.notes.get("task5_west_monster_cleared", False)):
                    monster_tile = self.detect_monster_tile(frame)
                    if monster_tile is not None:
                        return self.attack_monster(tile, monster_tile)
                    self.history.notes["task5_west_monster_cleared"] = True
                chest = self.detect_chest_tile(frame)
                if chest is not None:
                    return self.navigate_to_goal(tile, chest, blocked, player_px=player_px, final_action=ACTION_A)
            return self.navigate_to_exit(tile, "east", blocked, player_px=player_px)

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
        last_reward: float,
        info: dict[str, Any],
    ) -> int:
        task_id = self.infer_task_id(info)
        pixel_state = self.perceive(frame, task_id)
        if task_id == "mathematical_logic/task_1":
            return self.decide_task1(pixel_state, inventory, frame)
        if task_id == "mathematical_logic/task_2":
            return self.decide_task2(pixel_state, inventory, frame)
        if task_id == "mathematical_logic/task_3":
            return self.decide_task3(pixel_state, inventory, frame)
        if task_id == "mathematical_logic/task_4":
            return self.decide_task4(pixel_state, inventory, frame)
        if task_id == "mathematical_logic/task_5":
            return self.decide_task5(pixel_state, inventory, last_reward, frame)

        return ACTION_NOOP

    def act(self, obs, info: dict[str, Any]) -> int:
        inventory = self.extract_inventory(info)
        last_reward = self.extract_last_reward(info)
        self.update_memory_from_safe(inventory, last_reward, obs)
        action = self.decide(obs, inventory, last_reward, info)
        self.history.last_inventory = dict(inventory)
        self.update_facing(action)
        self.history.last_action = action
        return action


def make_policy() -> Policy:
    return Policy()
