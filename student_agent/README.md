# 小组基线 Agent 骨架

本目录用于放置你们小组自己的 Agent 代码，而不是继续直接修改课程示例文件。

## 当前状态

- 已提供统一 `Policy` 类骨架。
- 已兼容当前仓库的评测入口：`act(obs, info) -> int`
- 已将“最终可提交的决策逻辑”和“当前评测兼容层”分开。
- 当前已实现 `task_1`、`task_2`、`task_3` 和 `task_4` 的最小 baseline。
- 其中 `task_2` 当前采用从参考成功执行轨迹中提取的脚本化 debug 版本。
- `task_3` 当前采用房间级规则状态机，基于 `room_id`、`tile` 和 `keys` 做决策。
- `task_4` 当前采用显式阶段机，维护“桥状态 + 关键事件记忆”，依次完成拿钥匙、拿剑、击杀守卫和开最终宝箱。

## 文件说明

- `baseline_policy.py`：当前可运行的基线策略入口。
- `__init__.py`：导出 `Policy` 和 `make_policy`。

## 设计原则

- 不把课程提供的示例文件当作最终项目主代码。
- 对外兼容现有评测脚本，对内逐步改造成符合最终测试限制的结构。
- 先保证有统一骨架，再逐步往里面填 `task_2` 到 `task_5` 的逻辑。

## 当前建议的扩展顺序

1. 完善 `task_1` / `task_2` / `task_3` / `task_4` 的结果记录与截图。
2. 把 `task_2` 从脚本化轨迹替换为更通用的规则策略。
3. 将 `task_3` 从调试版状态机逐步过渡到更符合最终限制的版本。
4. 将 `task_4` 从调试版阶段机逐步过渡到更符合最终限制的版本。
5. 最后为 `task_5` 补通用探索逻辑。

## 运行方式

```bash
python utils/evaluate_policy.py --policy student_agent/baseline_policy.py --tasks mathematical_logic/task_1 --num-envs 1
```

也可以写成：

```bash
python utils/evaluate_policy.py --policy student_agent.baseline_policy:make_policy --tasks mathematical_logic/task_1 --num-envs 1
```
