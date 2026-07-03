# 实验报告 TeX 项目说明

本目录提供数理逻辑大作业的实验报告骨架，建议在整个项目周期中边做边填，而不是最后一天集中补写。

## 文件说明

- `main.tex`：主报告文件，已包含适合本课程作业的章节框架。
- `references.bib`：参考文献数据库，已放入仓库信息示例。
- `figures/`：存放实验截图、结构图、结果图表。

## 推荐写作方式

建议填写顺序：

1. 先写“任务概述”和“总体方法”。
2. 每完成一个模块，就补“环境建模 / 策略设计 / 形式化证明 / 实验结果”。
3. 每天把 `project_management/PROJECT_PROGRESS.md` 中的更新摘要转化为报告草稿内容。
4. 封版前统一润色格式、图表标题和引用。

## 编译方式

优先使用 `XeLaTeX` 编译中文文档。

如果本地安装了 `latexmk`：

```bash
latexmk -xelatex main.tex
```

如果没有安装 `latexmk`，可手动编译：

```bash
xelatex main.tex
bibtex main
xelatex main.tex
xelatex main.tex
```

## 建议同步规则

- 每完成一项实验，就把结果图、截图和关键结论放进 `figures/` 和进度文档。
- 每形成一个明确决策，就同步更新 `PROJECT_MEMORY.md`。
- 报告中的每个结论都应能追溯到代码、实验或证明。
