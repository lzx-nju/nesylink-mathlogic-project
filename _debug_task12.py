from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

PROJECT_ROOT = Path(__file__).resolve().parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from nesylink.env import make_env
from nesylink.core.constants import ACTION_LABELS
from student_agent.baseline_policy import Policy


def run(task_id: str, seed: int = 0, max_steps: int = 1000):
    env = make_env(task_id=task_id, observation_mode="pixels")
    obs, info = env.reset(seed=seed)
    policy = Policy()
    policy.reset(seed=seed, task_id=task_id)
    print(f"=== {task_id} seed={seed} ===")
    prev_tile = None
    for step in range(1, max_steps + 1):
        action = policy.act(obs, info)
        tile = policy.history.facing if False else None
        # detect player tile from obs
        pt = policy.detect_player_tile(obs)
        keys = int(info.get("inventory", {}).get("keys", 0))
        label = ACTION_LABELS[action] if action < len(ACTION_LABELS) else str(action)
        monster = policy.detect_monster_tile(obs) if task_id.endswith("task_2") else None
        agent = info.get("agent", {})
        pos = agent.get("position_px", None)
        det_px = policy.detect_player_px(obs)
        last_msg = info.get("engine", {}).get("last_message") if "engine" in info else None
        events = [r.get("name") for r in info.get("events", {}).get("records", [])]
        prev_action = getattr(run, "_pa", None)
        prev_pos = getattr(run, "_pp", None)
        meaningful = (
            pt != prev_tile
            or action != prev_action
            or events
            or "blocked" in str(events)
            or pos != prev_pos and (pos is None or prev_pos is None or abs(pos[0] - prev_pos[0]) + abs(pos[1] - prev_pos[1]) > 15)
        )
        marker = ""
        if pt == prev_tile and action in (1, 2, 3, 4) and "blocked" in str(events):
            marker = " <-- BLOCKED"
        prev_tile = pt
        run._pa = action
        run._pp = pos
        if meaningful or marker:
            print(
                f"step {step:3d} tile={pt} engpos={pos} detpx={det_px} keys={keys} facing={policy.history.facing} "
                f"action={label} events={events} monster={monster}{marker}"
            )
        obs, reward, terminated, truncated, info = env.step(action)
        if terminated or truncated:
            print(f"  -> terminated={terminated} truncated={truncated} reason={info.get('terminal_reason')}")
            break
    env.close()


if __name__ == "__main__":
    task = sys.argv[1] if len(sys.argv) > 1 else "mathematical_logic/task_1"
    run(task)
