from __future__ import annotations

import sys
from pathlib import Path

import numpy as np

PROJECT_ROOT = Path(__file__).resolve().parent
if str(PROJECT_ROOT) not in sys.path:
    sys.path.insert(0, str(PROJECT_ROOT))

from nesylink.env import make_env
from nesylink.core.constants import ACTION_LABELS, ACTION_LEFT, ACTION_RIGHT, ACTION_UP, ACTION_DOWN
from student_agent.baseline_policy import PLAYER_COLORS


def green_bounds(frame):
    xs, ys = [], []
    for color in PLAYER_COLORS:
        mask = np.all(frame == color, axis=2)
        yy, xx = np.nonzero(mask)
        if len(xx) > 0:
            xs.append(xx); ys.append(yy)
    xs = np.concatenate(xs); ys = np.concatenate(ys)
    return int(xs.min()), int(xs.max()), int(ys.min()), int(ys.max()), int(xs.mean()), int(ys.mean())


def run():
    env = make_env(task_id="mathematical_logic/task_1", observation_mode="pixels")
    obs, info = env.reset(seed=0)
    # move right a few ticks, then left, then up, then down - observe green bounds vs engpos
    plan = [("right", 3), ("left", 6), ("up", 3), ("down", 6)]
    action_map = {"right": ACTION_RIGHT, "left": ACTION_LEFT, "up": ACTION_UP, "down": ACTION_DOWN}
    pos = info["agent"]["position_px"]
    xmin, xmax, ymin, ymax, xmean, ymean = green_bounds(obs)
    print(f"init engpos={pos} green xmin={xmin} xmax={xmax} ymin={ymin} ymax={ymax} mean=({xmean},{ymean}) left_min={xmin-4} left_mean={xmean-8}")
    for direction, ticks in plan:
        a = action_map[direction]
        for _ in range(ticks):
            obs, r, term, trunc, info = env.step(a)
            pos = info["agent"]["position_px"]
            xmin, xmax, ymin, ymax, xmean, ymean = green_bounds(obs)
            print(f"{direction} engpos=({pos[0]:.0f},{pos[1]:.0f}) green x[{xmin},{xmax}] y[{ymin},{ymax}] mean=({xmean},{ymean}) left_min={xmin-4} left_mean={xmean-8}")
    env.close()


if __name__ == "__main__":
    run()
