# Agent 接口草案

## 1. 目的

本文件用于统一小组内部对 Agent 输入输出的理解，避免后续出现：

- 调试版和提交版混在一起；
- 某些成员默认直接依赖 `info`；
- 视觉模块、策略模块和评测入口接口不一致。

本草案基于当前仓库现状与课程说明整理，后续可继续修订。

## 2. 已知事实

- 当前仓库的 `utils/evaluate_policy.py` 期望策略接口是 `act(obs, info) -> int` 或等价形式。
- 当前课程说明明确要求：最终测试阶段，Agent 不能直接依赖环境内部 `info`。
- 老师目前尚未完全确定最终提交格式，因此小组内部需要提前设计“兼容当前评测脚本，同时满足最终限制”的中间方案。

## 3. 建议采用的双层接口

### 3.1 外层兼容接口

为了兼容当前仓库中的评测脚本，建议保留：

```python
def act(self, obs, info) -> int:
    ...
```

但这里的 `info` 只作为“兼容层输入”，不能默认被策略主体直接消费。

### 3.2 内层真实决策接口

建议策略内部统一转为如下语义：

```python
def decide(self, frame, reward, inventory, history) -> int:
    ...
```

其中：

- `frame`：像素观测，是最终测试阶段允许使用的核心输入。
- `reward`：当前或上一时刻 reward，可作为历史反馈。
- `inventory`：显式提供的物品栏信息。
- `history`：Agent 自己维护的内部记忆，如阶段、目标、最近轨迹。

## 4. 调试版与提交版的边界

### 4.1 调试版允许内容

调试阶段可以为了分析或监督，读取：

- `info["agent"]`
- `info["events"]`
- `info["entities"]`
- `info["dynamic"]`
- 其他环境内部字段

但这些信息只能用于：

- 日志
- 状态对齐
- 监督标注
- 结果分析
- 训练辅助

### 4.2 提交版禁止内容

提交版策略在推理阶段不应直接读取：

- 玩家精确坐标
- 怪物精确坐标
- 地图真值
- 墙体/陷阱真值
- 门和按钮的隐藏状态
- 任意 `info` 中的内部符号状态

## 5. 推荐代码组织方式

建议拆成四层：

1. `perception/`
   - 输入：像素
   - 输出：对象、位置、风险区、可交互点等中间表示
2. `planner/`
   - 输入：感知结果、任务阶段、记忆
   - 输出：子目标或动作建议
3. `controller/`
   - 输入：子目标或期望移动方向
   - 输出：环境动作编号
4. `debug_tools/`
   - 输入：`info`
   - 用途：训练期调试、监督、分析

这样可以把“最终可提交部分”和“训练期辅助部分”分离。

## 6. 当前建议的 Policy 类结构

```python
class Policy:
    def __init__(self):
        self.history = {}
        self.last_reward = 0.0

    def reset(self, seed=None, task_id=None):
        self.history = {
            "task_id": task_id,
            "phase": "init",
            "trace": [],
        }
        self.last_reward = 0.0

    def act(self, obs, info):
        # 兼容当前评测脚本，但不要把 info 直接当作最终决策输入
        inventory = self.extract_inventory(info)
        action = self.decide(
            frame=obs,
            reward=self.last_reward,
            inventory=inventory,
            history=self.history,
        )
        return action

    def extract_inventory(self, info):
        # 后续可替换成真正的评测接口来源
        return info.get("inventory", {})

    def decide(self, frame, reward, inventory, history):
        raise NotImplementedError
```

## 7. 当前最值得优先统一的约定

建议小组尽快统一以下问题：

1. `inventory` 的内部表示格式是什么？
2. 视觉模块输出是否统一成 tile 坐标级别的对象表？
3. 策略层是否采用“阶段机 + 搜索”的形式？
4. Lean 证明对象是规划器、动作筛选器，还是目标判定器？

## 8. 当前结论

当前阶段最合理的策略不是“所有人直接围着 `act(obs, info)` 写逻辑”，而是：

- 对外兼容当前仓库；
- 对内严格按最终测试限制设计；
- 把调试信息使用限制在辅助模块；
- 把真正提交的决策链路尽量做成可解释、可验证结构。
