# 数理逻辑大作业进度跟踪

## 1. 项目状态总览

- 项目名称：数理逻辑课程大作业
- 仓库：`nesylink-mathlogic-project`
- 当前阶段：baseline 改造与验证
- 更新时间：2026-07-05
- 当前目标：将前四关 baseline 从调试状态依赖逐步过渡到像素感知，并推进 `task_5` 与报告材料

## 2. 当前里程碑

| 里程碑 | 状态 | 截止时间 | 说明 |
|---|---|---|---|
| 阅读课程要求与仓库结构 | 已完成 | Day 1 | 已确认任务要求、评分细则和测试限制 |
| 建立项目管理文档 | 已完成 | Day 1 | 已创建总计划、进度跟踪、记忆清单 |
| 建立实验报告框架 | 已完成 | Day 1 | 已创建 TeX 报告骨架 |
| 跑通环境与示例策略 | 已完成 | Day 1 | 已安装依赖、跑通示例并在自有 baseline 中覆盖前四关 |
| 冻结统一 Agent 接口 | 进行中 | Day 2 | 已有接口草案和 baseline 骨架 |
| 完成最小可用视觉/策略链路 | 进行中 | Day 3 | `task_3` / `task_4` 已接入像素感知 baseline |
| 完成第一批 Lean 定义与证明 | 进行中 | Day 4 | 当前 Lean 文件已通过逐文件编译检查 |
| 统一实验结果并写报告主体 | 未开始 | Day 6 | 待推进 |
| 最终封版与交叉检查 | 未开始 | Day 7 | 待推进 |

## 3. 工作流状态

| 工作流 | 当前状态 | 负责人 | 下一步 |
|---|---|---|---|
| 环境与评测 | 进行中 | 待定 | 补截图并扩展到 `task_5` |
| 视觉与状态抽取 | 进行中 | 待定 | 已覆盖玩家、房间、宝箱、开关、桥和怪物的基础像素识别 |
| 策略与规划 | 进行中 | 待定 | 在自有骨架上继续扩展 `task_5` |
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
- 在 `student_agent/` 中设计 `task_5` baseline
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
- 已逐文件检查 `student_agent/lean/` 下 6 个 Lean 文件，均通过 `lake env lean`。

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
| 2026-07-05 | `lake env lean` | `student_agent/lean/*.lean` | 成功 | 6 个 Lean 文件逐文件编译通过 |

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
