# 数理逻辑大作业进度跟踪

## 1. 项目状态总览

- 项目名称：数理逻辑课程大作业
- 仓库：`nesylink-mathlogic-project`
- 当前阶段：完整 5 任务 robustness suite 验证
- 更新时间：2026-07-13
- 当前目标：task_1-4 original+spatial 100%，color 66.7%，task_5 修复后仍 0% 但里程碑全面改善

## 2. 当前里程碑

| 里程碑 | 状态 | 截止时间 | 说明 |
|---|---|---|---|
| 阅读课程要求与仓库结构 | 已完成 | Day 1 | 已确认任务要求、评分细则和测试限制 |
| 建立项目管理文档 | 已完成 | Day 1 | 已创建总计划、进度跟踪、记忆清单 |
| 建立实验报告框架 | 已完成 | Day 1 | 已创建 TeX 报告骨架 |
| 跑通环境与示例策略 | 已完成 | Day 1 | 已安装依赖、跑通示例并在自有 baseline 中覆盖前四关 |
| 冻结统一 Agent 接口 | 进行中 | Day 2 | 已有接口草案和 baseline 骨架 |
| 完成最小可用视觉/策略链路 | 已完成 | Day 3 | `task_3` / `task_4` / `task_5` 已接入像素感知 baseline |
| 完成第一批 Lean 定义与证明 | 进行中 | Day 4 | 当前 Lean 文件已通过逐文件编译检查 |
| 统一实验结果并写报告主体 | 未开始 | Day 6 | 待推进 |
| 最终封版与交叉检查 | 未开始 | Day 7 | 待推进 |

## 3. 工作流状态

| 工作流 | 当前状态 | 负责人 | 下一步 |
|---|---|---|---|
| 环境与评测 | 进行中 | 待定 | 补截图并整理 `task_1`-`task_5` 的最终评测记录 |
| 视觉与状态抽取 | 进行中 | 待定 | 已覆盖玩家、房间、宝箱、开关、桥和怪物的基础像素识别 |
| 策略与规划 | 进行中 | 待定 | 基于已跑通 baseline 整理报告叙述并检查提交接口 |
| Lean 形式化与证明 | 进行中 | 待定 | 继续明确证明边界与定理目标 |
| 实验与报告 | 进行中 | 组长 | 累积实验记录与截图 |

## 4. 今日重点

- [x] 阅读课程说明和项目文档
- [x] 规划一周项目步骤
- [x] 创建进度与记忆文档
- [x] 创建实验报告 TeX 骨架
- [ ] 确认小组成员方向选择
- [x] 跑通本地环境与示例 Agent
- [x] 记录第一批实验结果
- [ ] 补第一批截图和任务分析表

## 5. 待办清单

### 高优先级

- 确认五人分工并记录负责人
- 补充记录 `task_1` / `task_2` / `task_3` / `task_4` 的结果细节与截图
- 明确最终提交 Agent 的接口
- 整理 `task_5` baseline 的路线、阶段记忆和像素对齐说明
- 选定 Lean 首批证明目标

### 中优先级

- 梳理五个任务的机制差异
- 设计视觉模块输出格式
- 建立实验截图和结果文件夹规范

### 低优先级

- 统一命名规范与报告图表风格
- 提前整理参考文献

## 6. 风险与阻塞

| 编号 | 风险/阻塞 | 当前状态 | 应对策略 |
|---|---|---|---|
| R1 | 最终测试不能直接用 `info`，但训练可能会依赖 `info` | 已识别 | 明确区分调试版与提交版接口 |
| R2 | 只有一周，串行推进风险高 | 已识别 | 强制按并行工作流推进 |
| R3 | Lean 证明对象选得过大 | 已识别 | 先选可验证层，避免全系统证明 |
| R4 | 报告材料后补会丢失细节 | 已识别 | 每天同步记录截图、日志和结论 |

## 7. 更新日志

### 2026-07-03

- 已通读课程说明、README 与环境说明。
- 已确认最关键约束：测试阶段不能直接依赖 `info`。
- 已建立项目总计划文档。
- 已建立本进度文档，用于后续持续更新。
- 已建立报告 TeX 骨架，用于边做边写。
- 已完成一次基础校验，`report/main.tex` 当前无编辑器诊断报错。
- 已在本地确认 `xelatex` 可用，版本为 `TeX Live 2026`。
- 已成功编译 `docs/Mathematical_logic/report/main.tex`，生成 `main.pdf`。
- 已执行 `python -m pip install -e .`，完成仓库依赖安装。
- 已通过 `utils/evaluate_policy.py` 跑通 `docs/Mathematical_logic/examples/agent.py` 在 `task_1` 上的单轮评测：
  - success_rate = 1.000
  - avg_steps = 290.0
  - avg_reward = 127.050
- 已运行 `docs/Mathematical_logic/examples/task2_reference.py`，得到首批参考结果：
  - task_id = `task_2`
  - steps = 14
  - total_reward = 126.18
  - terminal_reason = `world_completed`
  - world_completed = `True`
- 已新增 `AGENT_INTERFACE_DRAFT.md`，用于统一调试版与提交版策略接口边界。
- 已新增 `TASK_ANALYSIS.md`，完成五关的目标链、关键机制和 baseline 思路整理。
- 已创建 `student_agent/` 目录，作为小组自有 Agent 代码入口。
- 已实现 `student_agent/baseline_policy.py` 的统一 `Policy` 骨架。
- 已通过评测入口验证 `student_agent/baseline_policy.py` 在 `task_1` 上可成功运行：
  - success_rate = 1.000
  - avg_steps = 290.0
  - avg_reward = 127.050
- 已将 `task_2` 接入自有 baseline，并完成单轮评测：
  - success_rate = 1.000
  - avg_steps = 182.0
  - avg_reward = 126.180
  - 当前实现方式：从参考成功执行轨迹中提取的脚本化 debug baseline
- 已将 `task_3` 接入自有 baseline，并完成单轮评测：
  - success_rate = 1.000
  - avg_steps = 523.0
  - avg_reward = 159.770
  - 当前实现方式：房间级规则状态机，使用 `room_id`、`tile` 和 `keys` 做决策
- 已将 `task_4` 接入自有 baseline，并完成单轮评测：
  - success_rate = 1.000
  - avg_steps = 1085.0
  - avg_reward = 249.150
  - 当前实现方式：显式阶段机，维护桥状态与 `monster_killed` 事件记忆

### 2026-07-05

- 已将 `task_3` / `task_4` 的 baseline 改造为像素感知版本，策略主体不再直接读取 `info["env"]`、`info["agent"]`、`info["dynamic"]` 或 `info["events"]`。
- 已修正玩家格子识别：从玩家精灵绿色像素反推出精灵位置，并按玩家中心点计算 tile，与环境交互语义保持一致。
- 已补充 `task_4` 中开关按下后的像素识别，避免按下开关后 west 房间无法识别。
- 已完成 `task_1` 到 `task_4` 的 3 个 seed 回归：
  - `task_1`：success_rate = 1.000，avg_steps = 290.0，avg_reward = 127.050
  - `task_2`：success_rate = 1.000，avg_steps = 182.0，avg_reward = 126.180
  - `task_3`：success_rate = 1.000，avg_steps = 525.0，avg_reward = 159.750
  - `task_4`：success_rate = 1.000，avg_steps = 1089.0，avg_reward = 249.110
- 已逐文件检查 `student_agent/lean/` 下 6 个 Lean 文件，均通过本地 `lean` 编译检查。
- 已将 `task_5` 接入 `student_agent/baseline_policy.py`，采用显式阶段机推进：起始宝箱 -> 按钮 -> 南房间钥匙 -> 起始房间杀怪 -> 东门与治疗宝箱 -> 西房间金币宝箱。
- `task_5` 路线实现中记录了多处像素碰撞对齐点：进入东门前需要在第 4 行对齐，东房间需要在第 1 行/第 1 列对齐，起始房间去西门与西房间底边也需要额外对齐，避免 tile 已到位但角色碰撞箱仍擦到墙或 NPC。
- 已完成 `student_agent/baseline_policy.py` 的全任务单 seed 回归：
  - `task_1`：success_rate = 1.000，avg_steps = 290.0，avg_reward = 127.050
  - `task_2`：success_rate = 1.000，avg_steps = 182.0，avg_reward = 126.180
  - `task_3`：success_rate = 1.000，avg_steps = 525.0，avg_reward = 159.750
  - `task_4`：success_rate = 1.000，avg_steps = 1089.0，avg_reward = 249.110
  - `task_5`：success_rate = 1.000，avg_steps = 1112.0，avg_reward = 155.730

## 8. 首批实验记录

| 日期 | 入口 | 任务 | 结果 | 备注 |
|---|---|---|---|---|
| 2026-07-03 | `utils/evaluate_policy.py` + `examples/agent.py` | `task_1` | 成功 | 1 轮评测成功，reward = 127.050 |
| 2026-07-03 | `examples/task2_reference.py` | `task_2` | 成功 | 14 步完成，终止原因为 `world_completed` |
| 2026-07-03 | `utils/evaluate_policy.py` + `student_agent/baseline_policy.py` | `task_1` | 成功 | 自有 baseline 骨架已跑通 |
| 2026-07-03 | `utils/evaluate_policy.py` + `student_agent/baseline_policy.py` | `task_2` | 成功 | 自有 baseline 已覆盖前两关 |
| 2026-07-03 | `utils/evaluate_policy.py` + `student_agent/baseline_policy.py` | `task_3` | 成功 | 自有 baseline 已覆盖前三关 |
| 2026-07-03 | `utils/evaluate_policy.py` + `student_agent/baseline_policy.py` | `task_4` | 成功 | 自有 baseline 已覆盖前四关 |
| 2026-07-05 | `utils/evaluate_policy.py` + `student_agent/baseline_policy.py` | `task_1`-`task_4` | 成功 | 3 个 seed 全部成功；`task_3` / `task_4` 已改为像素感知基线 |
| 2026-07-05 | `utils/evaluate_policy.py` + `student_agent/baseline_policy.py` | `task_1`-`task_5` | 成功 | 单 seed 全任务通过，`task_5` 用 1112 步完成 |
| 2026-07-05 | `lean` | `student_agent/lean/*.lean` | 成功 | 6 个 Lean 文件逐文件编译通过 |
| 2026-07-10 | `utils/evaluate_policy.py` + `--info-mode safe` | `task_1`-`task_5` | task_1-4 成功，task_5 失败 | safe 模式 10 seed 评测，task_5 agent_dead |
| 2026-07-11 | `utils/evaluate_policy.py` + `--robustness-suite --num-envs 30` | `task_1`-`task_4` | 成功 | original 72/72 + spatial 36/36 全通过，color 0/12 预期失败 |
| 2026-07-13 | `utils/evaluate_policy.py` + `--robustness-suite --num-envs 30` | `task_1`-`task_5` | task_1-4 成功，task_5 失败 | 完整 5 任务评测，task_1-4 original+spatial 100%，color 66.7%（dark/bright 通过），task_5 全部 agent_dead |

### 2026-07-10

- 合并 upstream 评测脚本更新（`--info-mode safe`、`--task-policy`、spatial 变体扩展到 task_4/5）。
- 全面适配 `safe` 信息模式：`update_memory` 与 `update_task5_memory` 重构为基于 `inventory` diff、`last_reward` 和像素感知的事件推断。
- 在 `safe` 模式下运行 10 seed 评测：task_1-4 全部成功，task_5 事件推断正常但导航执行层仍有 bug（agent_dead）。
- 同步更新 `Task1Formalization.lean` 注释与报告实验章节。

### 2026-07-11

- 修复 spatial 布局变体失败。
- 根因一：`move_towards_aligned` 像素对齐阈值 `+1` 过松，在 1-tile 间隙处 sprite rect 覆盖相邻 blocking tile 导致卡住。修复为精确对齐 `+0` 并添加卡住检测（`mem_last_action_blocked` 追踪 reward ≤ -0.05）。
- 根因二：`detect_task3_room` 硬编码 NPC/chest 位置，spatial 变体下 room 检测失败。修复为全网格扫描。
- 修复前 spatial 通过率：task_1 1/3、task_2 1/3、task_3 0/3；修复后全部 3/3。
- 运行 robustness suite（`--num-envs 30`）：task_1-4 的 original + spatial 共 108 个 episode 全部通过，color 变体预期失败（策略基于精确 RGB 匹配）。
- 更新 `eval_results.json` 与报告实验章节。

### 2026-07-13

- 合并组员推送的 color 变体适配（`normalize_obs` 预处理模块，对 dark/bright/inverted 施加逆变换）和 task_2-4 Lean 策略形式化改为 BFS 模式。
- 运行完整 5 任务 robustness suite（`--num-envs 30`，共 150 个 episode）。
- 评测结果：
  - task_1-4 original 72/72 + spatial 36/36 = 108/108 全通过（100%）。
  - task_1-4 color 8/12 通过（66.7%）：dark/bright 全通过，grayscale 有损不可逆仍失败。
  - task_5 全部失败（original 0/18、spatial 0/9、color 0/3）：agent_dead。
- 尝试修复 task_5 导航执行层（7 个 bug）：
  - Bug 1：`navigate_to_exit` 像素对齐方向检查——south/north 只处理 dx==0 的相邻 tile，east/west 只处理 dy==0，避免地图边界卡死。
  - Bug 2：`task5_button_pressed` 误标——只在 agent 在 button tile 上按 A 时标记。
  - Bug 3：button 自动触发检测——button 踩上即触发（不需 A），在 `decide_task5` 中检测 button 不可见时自动标记。
  - Bug 4：`task5_start_monster_cleared` 误标——添加 `room_id == "task5_start"` 条件。
  - Bug 5：`detect_task5_room` east/west 墙体模式错误——更新为与实际房间布局匹配的独特墙位置。
  - Bug 6：`task5_east_chest_opened` 误标——用 `chest_adjacent and not monster_adjacent` 区分开 chest 和攻击怪物。
  - Bug 7：`attack_monster` 缺少 `blocked`/`player_px` 参数——task5_east/west 分支的 attack_monster 调用未传参，导致用简单 move_towards 被墙挡住。
- 修复后 task_5 original 评测：success_rate 仍为 0.000，但 agent 平均存活 1083 步（修复前 400 步），累计正奖励 95.020（修复前 -21.650），全部里程碑 1.000（chest_opened/key_collected/gold_collected/agent_healed/button_pressed/room_changed/door_opened/monster_killed/exit_reached）。agent 成功完成 start→south→east 三个房间的完整任务链，仅在 west 房间因 hp 耗尽死亡。
- 验证 task_1-4 不回归：robustness suite n=30 全部通过，original+spatial 100%，color 66.7%，与修复前完全一致。
- 更新 `eval_results.json` 为完整 5 任务结果（含 task_5 修复后数据），更新 `main.tex` 实验章节。

## 9. 每日更新模板

复制下面模板追加到本文件末尾：

```text
### YYYY-MM-DD

- 今日完成：
- 当前结果：
- 遇到问题：
- 解决方案 / 下一步：
- 需要组长协调的事项：
```

## 10. 集成前检查项

- [ ] 每个方向都有明确负责人
- [ ] 统一接口已经写成文档
- [ ] 调试信息和最终提交信息来源已明确区分
- [ ] Lean 证明对象与代码实现已对齐
- [ ] 报告中每个结论都能对应代码或实验结果
