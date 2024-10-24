import copy
import requests
from itertools import product
from matplotlib import pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from mpl_toolkits import mplot3d
from mpl_toolkits.mplot3d.art3d import Poly3DCollection
from concurrent.futures import ThreadPoolExecutor
import threading
import numpy as np
import sys
import pyodbc  # For SQL Server connection
import tkinter as tk
from tkinter import simpledialog, messagebox

# 调整后的参数，兼顾装箱效率和计算效率
MIN_FILL_RATE = 0.8    # 降低最小填充率
MIN_AREA_RATE = 0.8    # 降低最小面积比
MAX_TIMES = 4          # 增加复合块复杂度
MAX_DEPTH =  4         # 增加搜索深度
MAX_BRANCH =  4        # 增加节点分支数

# 临时的最优放置方案
tmp_best_ps = None
root = None
canvas = None  # 用于保存 FigureCanvasTkAgg 对象的引用
figure_window = None  # 用于保存弹出窗口的引用

# 添加全局变量用于存储单位信息
dimension_unit = 'in'  # 默认尺寸单位为英寸
weight_unit = 'lb'     # 默认重量单位为磅

# 栈数据结构，用于存储剩余空间
class Stack:
    def __init__(self):
        self.data = []

    def empty(self):
        return len(self.data) == 0

    def not_empty(self):
        return len(self.data) > 0

    def pop(self):
        return self.data.pop() if len(self.data) > 0 else None

    def push(self, *items):
        for item in items:
            self.data.append(item)

    def top(self):
        return self.data[-1] if len(self.data) > 0 else None

    def clear(self):
        self.data.clear()

    def size(self):
        return len(self.data)

# 箱子类
class Box:
    def __init__(self, lx, ly, lz, type=0, weight=0.0):
        # 长
        self.lx = lx
        # 宽
        self.ly = ly
        # 高
        self.lz = lz
        # 类型
        self.type = type
        # 重
        self.weight = weight

    def __str__(self):
        return f"lx: {self.lx}, ly: {self.ly}, lz: {self.lz}, type: {self.type}, weight: {self.weight}"

# 剩余空间类
class Space:
    def __init__(self, x, y, z, lx, ly, lz, origin=None):
        # 坐标
        self.x = x
        self.y = y
        self.z = z
        # 长
        self.lx = lx
        # 宽
        self.ly = ly
        # 高
        self.lz = lz
        # 表示从哪个剩余空间切割而来
        self.origin = origin

    def __str__(self):
        return f"x:{self.x},y:{self.y},z:{self.z},lx:{self.lx},ly:{self.ly},lz:{self.lz}"

    def __eq__(self, other):
        return (self.x == other.x and self.y == other.y and self.z == other.z and
                self.lx == other.lx and self.ly == other.ly and self.lz == other.lz)

# 装箱问题类
class Problem:
    def __init__(self, container: Space, box_list=[], num_list=[], weight_limit=sys.maxsize):
        # 容器
        self.container = container
        # 箱子列表
        self.box_list = box_list
        # 箱子对应的数量
        self.num_list = num_list
        # 限重
        self.weight_limit = weight_limit

# 块类
class Block:
    def __init__(self, lx, ly, lz, require_list=[], children=[], direction=None, weight=0.0):
        # 长
        self.lx = lx
        # 宽
        self.ly = ly
        # 高
        self.lz = lz
        # 需要的物品数量
        self.require_list = require_list
        # 体积
        self.volume = 0
        # 子块列表，简单块的子块列表为空
        self.children = children
        # 复合块子块的合并方向
        self.direction = direction
        # 需要的物品重量
        self.weight = weight
        # 顶部可放置矩形尺寸
        self.ax = 0
        self.ay = 0
        # 复杂度，复合次数
        self.times = 0
        # 适应度，块选择时使用
        self.fitness = 0

    def __str__(self):
        return (f"lx: {self.lx}, ly: {self.ly}, lz: {self.lz}, volume: {self.volume}, "
                f"ax: {self.ax}, ay: {self.ay}, times: {self.times}, fitness: {self.fitness}, "
                f"require: {self.require_list}, direction: {self.direction}")

    def __eq__(self, other):
        if not isinstance(other, Block):
            return False
        # 比较lx, ly, lz, ax, ay
        if (self.lx != other.lx or self.ly != other.ly or self.lz != other.lz or
                self.ax != other.ax or self.ay != other.ay):
            return False
        # 比较require_list
        if len(self.require_list) != len(other.require_list):
            return False
        return np.array_equal(np.array(self.require_list), np.array(other.require_list))

    def __hash__(self):
        return hash(",".join([str(self.lx), str(self.ly), str(self.lz), str(self.ax), str(self.ay),
                              ",".join([str(r) for r in self.require_list])]))

# 放置类
class Place:
    def __init__(self, space: Space, block: Block):
        # 空间
        self.space = space
        # 块
        self.block = block

    def __eq__(self, other):
        return self.space == other.space and self.block == other.block

# 装箱状态类
class PackingState:
    def __init__(self, plan_list=None, space_stack=None, avail_list=None, weight=0.0):
        # 已生成的装箱方案列表
        self.plan_list = plan_list if plan_list is not None else []
        # 剩余空间堆栈
        self.space_stack = space_stack if space_stack is not None else Stack()
        # 剩余可用箱体数量
        self.avail_list = avail_list if avail_list is not None else []
        # 当前排样重量
        self.weight = weight
        # 已装载物品总体积
        self.volume = 0
        # 最终装载物品的总体积的评估值
        self.volume_complete = 0

# 合并块时通用校验项目
def combine_common_check(combine: Block, container: Space, num_list, max_weight=sys.maxsize):
    # 合共块尺寸不得大于容器尺寸
    if combine.lx > container.lx or combine.ly > container.ly or combine.lz > container.lz:
        return False
    # 合共块需要的箱子数量不得大于箱子总的数量
    if (np.array(combine.require_list) > np.array(num_list)).any():
        return False
    # 合并块的填充体积不得小于最小填充率
    if combine.volume / (combine.lx * combine.ly * combine.lz) < MIN_FILL_RATE:
        return False
    # 合并块的顶部可放置矩形必须足够大
    if (combine.ax * combine.ay) / (combine.lx * combine.ly) < MIN_AREA_RATE:
        return False
    # 合并块的复杂度不得超过最大复杂度
    if combine.times > MAX_TIMES:
        return False
    # 合并块的重量不得超过最大重量
    if combine.weight > max_weight:
        return False
    return True

# 合并块时通用合并项目
def combine_common(a: Block, b: Block, combine: Block):
    # 合并块的需求箱子数量
    combine.require_list = (np.array(a.require_list) + np.array(b.require_list)).tolist()
    # 合并填充体积
    combine.volume = a.volume + b.volume
    # 构建父子关系
    combine.children = [a, b]
    # 合并后的复杂度
    combine.times = max(a.times, b.times) + 1
    # 重量相加
    combine.weight = a.weight + b.weight

# 生成简单块
def gen_simple_block(container, box_list, num_list, max_weight=sys.maxsize):
    block_table = []
    for box in box_list:
        max_nx = int(container.lx // box.lx)
        max_ny = int(container.ly // box.ly)
        max_nz = int(container.lz // box.lz)
        max_quantity = num_list[box.type]
        for nx in range(1, max_nx + 1):
            for ny in range(1, max_ny + 1):
                for nz in range(1, max_nz + 1):
                    total_boxes = nx * ny * nz
                    if total_boxes > max_quantity:
                        continue
                    lx = box.lx * nx
                    ly = box.ly * ny
                    lz = box.lz * nz
                    weight = total_boxes * box.weight
                    if lx <= container.lx and ly <= container.ly and lz <= container.lz and weight <= max_weight:
                        requires = [0] * len(num_list)
                        requires[box.type] = total_boxes
                        block = Block(lx, ly, lz, requires)
                        block.ax = lx
                        block.ay = ly
                        block.volume = lx * ly * lz
                        block.weight = weight
                        block.times = 0
                        block_table.append(block)
    return sorted(block_table, key=lambda x: x.volume, reverse=True)

# 生成复合块
def gen_complex_block(container, box_list, num_list, max_weight=sys.maxsize):
    # 先生成简单块
    block_table = gen_simple_block(container, box_list, num_list, max_weight)
    block_set = set(block_table)  # 使用集合来存储块
    for times in range(MAX_TIMES):
        new_block_set = set()
        # 循环所有简单块，两两配对
        for a in block_set:
            for b in block_set:
                if a.times == times or b.times == times:
                    c = Block(0, 0, 0)
                    # 按x轴方向复合
                    if a.ax == a.lx and b.ax == b.lx and a.lz == b.lz:
                        c.direction = "x"
                        c.ax = a.ax + b.ax
                        c.ay = min(a.ay, b.ay)
                        c.lx = a.lx + b.lx
                        c.ly = max(a.ly, b.ly)
                        c.lz = a.lz
                        combine_common(a, b, c)
                        if combine_common_check(c, container, num_list, max_weight):
                            new_block_set.add(c)
                            continue
                    # 按y轴方向复合
                    if a.ay == a.ly and b.ay == b.ly and a.lz == b.lz:
                        c.direction = "y"
                        c.ax = min(a.ax, b.ax)
                        c.ay = a.ay + b.ay
                        c.lx = max(a.lx, b.lx)
                        c.ly = a.ly + b.ly
                        c.lz = a.lz
                        combine_common(a, b, c)
                        if combine_common_check(c, container, num_list, max_weight):
                            new_block_set.add(c)
                            continue
                    # 按z轴方向复合
                    if a.ax >= b.lx and a.ay >= b.ly:
                        c.direction = "z"
                        c.ax = b.ax
                        c.ay = b.ay
                        c.lx = a.lx
                        c.ly = a.ly
                        c.lz = a.lz + b.lz
                        combine_common(a, b, c)
                        if combine_common_check(c, container, num_list, max_weight):
                            new_block_set.add(c)
                            continue
        # 更新块集合
        block_set.update(new_block_set)
    # 将集合转换为列表，并按填充体积排序
    return sorted(list(block_set), key=lambda x: x.volume, reverse=True)

# 生成可行块列表
def gen_block_list(space: Space, avail, block_table, avail_weight=sys.maxsize):
    block_list = []
    for block in block_table:
        if ((np.array(block.require_list) <= np.array(avail)).all() and
                block.lx <= space.lx and block.ly <= space.ly and
                block.lz <= space.lz and block.weight <= avail_weight):
            block_list.append(block)
    return block_list

# 裁切出新的剩余空间（有稳定性约束）
def gen_residual_space(space: Space, block: Block):
    # 三个维度的剩余尺寸
    rmx = space.lx - block.lx
    rmy = space.ly - block.ly
    rmz = space.lz - block.lz
    # 三个新裁切出的剩余空间（按入栈顺序依次返回）
    if rmx >= rmy:
        # 可转移空间归属于x轴切割空间
        drs_x = Space(space.x + block.lx, space.y, space.z, rmx, space.ly, space.lz, space)
        drs_y = Space(space.x, space.y + block.ly, space.z, block.lx, rmy, space.lz, space)
        drs_z = Space(space.x, space.y, space.z + block.lz, block.ax, block.ay, rmz, None)
        return drs_z, drs_y, drs_x
    else:
        # 可转移空间归属于y轴切割空间
        drs_x = Space(space.x + block.lx, space.y, space.z, rmx, block.ly, space.lz, space)
        drs_y = Space(space.x, space.y + block.ly, space.z, space.lx, rmy, space.lz, space)
        drs_z = Space(space.x, space.y, space.z + block.lz, block.ax, block.ay, rmz, None)
        return drs_z, drs_x, drs_y

# 空间转移
def transfer_space(space: Space, space_stack: Stack):
    # 仅剩一个空间的话，直接弹出
    if space_stack.size() <= 1:
        space_stack.pop()
        return None
    # 待转移空间的原始空间
    discard = space
    # 目标空间
    space_stack.pop()
    target = space_stack.top()
    # 将可转移的空间转移给目标空间
    if (discard.origin is not None and target.origin is not None and
            discard.origin == target.origin):
        new_target = copy.deepcopy(target)
        # 可转移空间原先归属于y轴切割空间的情况
        if discard.lx == discard.origin.lx:
            new_target.ly = discard.origin.ly
        # 可转移空间原来归属于x轴切割空间的情况
        elif discard.ly == discard.origin.ly:
            new_target.lx = discard.origin.lx
        else:
            return None
        space_stack.pop()
        space_stack.push(new_target)
        # 返回未发生转移之前的目标空间
        return target
    return None

# 还原空间转移
def transfer_space_back(space: Space, space_stack: Stack, revert_space: Space):
    space_stack.pop()
    space_stack.push(revert_space)
    space_stack.push(space)

# 块放置算法
def place_block(ps: PackingState, block: Block):
    # 栈顶剩余空间
    space = ps.space_stack.pop()
    # 更新可用箱体数目
    ps.avail_list = (np.array(ps.avail_list) - np.array(block.require_list)).tolist()
    # 更新放置计划
    place = Place(space, block)
    ps.plan_list.append(place)
    # 更新体积利用率
    ps.volume += block.volume
    # 更新排样重量
    ps.weight += block.weight
    # 压入新的剩余空间
    cuboid1, cuboid2, cuboid3 = gen_residual_space(space, block)
    ps.space_stack.push(cuboid1, cuboid2, cuboid3)
    # 返回临时生成的放置
    return place

# 块移除算法
def remove_block(ps: PackingState, block: Block, place: Place, space: Space):
    # 还原可用箱体数目
    ps.avail_list = (np.array(ps.avail_list) + np.array(block.require_list)).tolist()
    # 还原排样计划
    ps.plan_list.remove(place)
    # 还原体积利用率
    ps.volume -= block.volume
    # 还原排样重量
    ps.weight -= block.weight
    # 移除在此之前裁切出的新空间
    for _ in range(3):
        ps.space_stack.pop()
    # 还原之前的空间
    ps.space_stack.push(space)

# 补全放置方案
def complete(ps: PackingState, block_table, max_weight=sys.maxsize):
    # 不对当前的放置状态进行修改
    tmp = copy.deepcopy(ps)
    while tmp.space_stack.not_empty():
        # 栈顶空间
        space = tmp.space_stack.top()
        # 可用块列表
        block_list = gen_block_list(space, tmp.avail_list, block_table, max_weight - tmp.weight)
        if len(block_list) > 0:
            # 放置块
            place_block(tmp, block_list[0])
        else:
            # 空间转移
            transfer_space(space, tmp.space_stack)
    # 补全后的使用体积
    ps.volume_complete = tmp.volume

# 带深度限制的深度优先搜索算法
def depth_first_search(ps: PackingState, depth, branch, block_table, max_weight=sys.maxsize):
    global tmp_best_ps
    if depth != 0:
        space = ps.space_stack.top()
        block_list = gen_block_list(space, ps.avail_list, block_table, max_weight - ps.weight)
        if len(block_list) > 0:
            # 遍历所有分支
            for i in range(min(branch, len(block_list))):
                # 放置块
                place = place_block(ps, block_list[i])
                # 放置下一个块
                depth_first_search(ps, depth - 1, branch, block_table, max_weight)
                # 移除刚才添加的块
                remove_block(ps, block_list[i], place, space)
        else:
            # 转移空间
            old_target = transfer_space(space, ps.space_stack)
            if old_target:
                # 放置下一个块
                depth_first_search(ps, depth, branch, block_table, max_weight)
                # 还原转移空间
                transfer_space_back(space, ps.space_stack, old_target)
    else:
        # 补全该方案
        complete(ps, block_table, max_weight)
        # 更新最优解
        if ps.volume_complete > tmp_best_ps.volume_complete:
            tmp_best_ps = copy.deepcopy(ps)

# 评价某个块
def estimate(ps: PackingState, block_table, search_params, max_weight=sys.maxsize):
    global tmp_best_ps
    tmp_best_ps = PackingState([], Stack(), [])
    depth_first_search(ps, MAX_DEPTH, MAX_BRANCH, block_table, max_weight)
    return tmp_best_ps.volume_complete

# 查找下一个可行块
# 修改 find_next_block 函数，使用并行处理
def find_next_block(ps: PackingState, block_list, block_table, search_params, max_weight=sys.maxsize):
    # 初始化最优块为第一个块（填充体积最大的块）
    best_block = block_list[0]
    best_fitness = 0

    # 定义一个内部函数，用于评估块的适应度
    def evaluate_block(block):
        # 复制当前状态，避免修改原始状态
        ps_copy = copy.deepcopy(ps)
        # 栈顶空间
        space = ps_copy.space_stack.top()
        # 放置块
        place = place_block(ps_copy, block)
        # 评价值
        fitness = estimate(ps_copy, block_table, search_params, max_weight)
        # 移除刚才添加的块
        remove_block(ps_copy, block, place, space)
        return (fitness, block)

    # 使用线程池并行评估块
    with ThreadPoolExecutor() as executor:
        futures = [executor.submit(evaluate_block, block) for block in block_list]
        for future in futures:
            fitness, block = future.result()
            if fitness > best_fitness:
                best_fitness = fitness
                best_block = block

    return best_block

# 递归构建箱体坐标，用于绘图
def build_box_position(block, init_pos, box_list):
    # 遇到简单块时进行坐标计算
    if len(block.children) <= 0 and block.times == 0:
        # 获取需要的箱子类型索引
        require_list_bool = (np.array(block.require_list) > 0).tolist()
        if True in require_list_bool:
            box_idx = require_list_bool.index(True)
        else:
            return []
        if box_idx >= len(box_list):
            print(f"错误: box_idx ({box_idx}) 超出了 box_list 的范围 ({len(box_list)}).")
            return []
        box = box_list[box_idx]
        # 箱体的相对坐标
        nx = int(block.lx / box.lx)
        ny = int(block.ly / box.ly)
        nz = int(block.lz / box.lz)
        x_list = [i * box.lx for i in range(nx)]
        y_list = [i * box.ly for i in range(ny)]
        z_list = [i * box.lz for i in range(nz)]
        if not x_list or not y_list or not z_list:
            return []
        dimensions = [list(map(sum, zip(d, init_pos))) for d in product(x_list, y_list, z_list)]
        return sorted([d + [box.lx, box.ly, box.lz, box.type] for d in dimensions], key=lambda x: (x[0], x[1], x[2]))
    pos = []
    for child in block.children:
        pos += build_box_position(child, (init_pos[0], init_pos[1], init_pos[2]), box_list)
        # 根据子块的复合方向，确定下一个子块的左后下角坐标
        if block.direction == "x":
            init_pos = (init_pos[0] + child.lx, init_pos[1], init_pos[2])
        elif block.direction == "y":
            init_pos = (init_pos[0], init_pos[1] + child.ly, init_pos[2])
        elif block.direction == "z":
            init_pos = (init_pos[0], init_pos[1], init_pos[2] + child.lz)
    return pos

# 绘制立方体边框
def plot_linear_cube(ax, x, y, z, dx, dy, dz, color='red', linestyle=None):
    xx = [x, x, x+dx, x+dx, x]
    yy = [y, y+dy, y+dy, y, y]
    kwargs = {"alpha": 1, "color": color, "linewidth": 2.5, "zorder": 2}
    if linestyle:
        kwargs["linestyle"] = linestyle
    ax.plot3D(xx, yy, [z]*5, **kwargs)
    ax.plot3D(xx, yy, [z+dz]*5, **kwargs)
    ax.plot3D([x, x], [y, y], [z, z+dz], **kwargs)
    ax.plot3D([x, x], [y+dy, y+dy], [z, z+dz], **kwargs)
    ax.plot3D([x+dx, x+dx], [y+dy, y+dy], [z, z+dz], **kwargs)
    ax.plot3D([x+dx, x+dx], [y, y], [z, z+dz], **kwargs)

# 立方体
def cuboid_data2(o, size=(1, 1, 1)):
    X = [[[0, 1, 0], [0, 0, 0], [1, 0, 0], [1, 1, 0]],
         [[0, 0, 0], [0, 0, 1], [1, 0, 1], [1, 0, 0]],
         [[1, 0, 1], [1, 0, 0], [1, 1, 0], [1, 1, 1]],
         [[0, 0, 1], [0, 0, 0], [0, 1, 0], [0, 1, 1]],
         [[0, 1, 0], [0, 1, 1], [1, 1, 1], [1, 1, 0]],
         [[0, 1, 1], [0, 0, 1], [1, 0, 1], [1, 1, 1]]]
    X = np.array(X).astype(float)
    for i in range(3):
        X[:, :, i] *= size[i]
    X += np.array(o)
    return X

# 绘制立方体
def plotCubeAt2(positions, sizes=None, colors=None, **kwargs):
    if not isinstance(colors, (list, np.ndarray)):
        colors = ["C0"] * len(positions)
    if not isinstance(sizes, (list, np.ndarray)):
        sizes = [(1, 1, 1)] * len(positions)
    g = []
    for p, s, c in zip(positions, sizes, colors):
        g.append(cuboid_data2(p, size=s))
    pc = Poly3DCollection(np.concatenate(g), **kwargs)
    pc.set_facecolor(np.repeat(colors, 6))
    return pc

# 绘制排样结果
def draw_packing_result(problem: Problem, ps: PackingState):
    global canvas
    global figure_window
    global dimension_unit  # 获取当前的单位信息

    # 如果已经有一个弹出窗口，先将其关闭
    if figure_window is not None:
        figure_window.destroy()

    # 创建新的弹出窗口
    figure_window = tk.Toplevel(root)
    figure_window.title("三维装箱结果")
    figure_window.geometry("1000x800")  # 设置窗口大小，可根据需要调整

    # 创建 Matplotlib Figure 对象
    fig = plt.figure()
    ax1 = mplot3d.Axes3D(fig, auto_add_to_figure=False)
    fig.add_axes(ax1)

    # 根据用户选择的单位，确定缩放因子
    if dimension_unit == 'in':
        scale = 1.0
    elif dimension_unit == 'cm':
        scale = 2.54  # 1 in = 2.54 cm
    else:
        scale = 1.0  # 默认不缩放

    # 绘制容器边框
    plot_linear_cube(ax1, 0, 0, 0,
                    problem.container.lx * scale,
                    problem.container.ly * scale,
                    problem.container.lz * scale,
                    color='red')

    # 用于计算装箱后的实际尺寸
    max_x = 0
    max_y = 0
    max_z = 0

    for p in ps.plan_list:
        box_pos = build_box_position(p.block, (p.space.x, p.space.y, p.space.z), problem.box_list)
        positions = []
        sizes = []
        colors = []

        for bp in sorted(box_pos, key=lambda x: (x[0], x[1], x[2])):
            # 根据选择的单位调整尺寸
            x, y, z, lx, ly, lz, box_type = bp
            x *= scale
            y *= scale
            z *= scale
            lx *= scale
            ly *= scale
            lz *= scale
            positions.append((x, y, z))
            sizes.append((lx, ly, lz))
            color = f"C{box_type % 10}"
            colors.append(color)

            # 更新最大尺寸
            max_x = max(max_x, x + lx)
            max_y = max(max_y, y + ly)
            max_z = max(max_z, z + lz)

        pc = plotCubeAt2(positions, sizes, colors=colors, edgecolor="k")
        ax1.add_collection3d(pc)

    # 设置轴标签，添加单位
    ax1.set_xlabel(f'X ({dimension_unit})')
    ax1.set_ylabel(f'Y ({dimension_unit})')
    ax1.set_zlabel(f'Z ({dimension_unit})')

    # 设置坐标轴范围
    ax1.set_xlim(0, problem.container.lx * scale)
    ax1.set_ylim(0, problem.container.ly * scale)
    ax1.set_zlim(0, problem.container.lz * scale)

    # 添加图例，显示装箱后的尺寸
    legend_text = (f"装箱后尺寸:\n"
                   f"长度 (X): {max_x:.2f} {dimension_unit}\n"
                   f"宽度 (Y): {max_y:.2f} {dimension_unit}\n"
                   f"高度 (Z): {max_z:.2f} {dimension_unit}")
    ax1.text2D(0.05, 0.95, legend_text, transform=ax1.transAxes)

    # 如果之前存在 canvas，先销毁
    if canvas is not None:
        canvas.get_tk_widget().destroy()

    # 创建新的 FigureCanvasTkAgg 对象
    canvas = FigureCanvasTkAgg(fig, master=figure_window)
    canvas.draw()
    canvas.get_tk_widget().pack(fill=tk.BOTH, expand=1)

    # 添加 Matplotlib 的导航工具栏（可选）
    from matplotlib.backends.backend_tkagg import NavigationToolbar2Tk
    toolbar = NavigationToolbar2Tk(canvas, figure_window)
    toolbar.update()
    canvas.get_tk_widget().pack(fill=tk.BOTH, expand=1)

# 基本启发式算法
def basic_heuristic(is_complex, search_params, problem: Problem):
    global tmp_best_ps
    tmp_best_ps = PackingState([], Stack(), [])

    if is_complex:
        # 生成复合块
        block_table = gen_complex_block(problem.container, problem.box_list, problem.num_list, problem.weight_limit)
    else:
        # 生成简单块
        block_table = gen_simple_block(problem.container, problem.box_list, problem.num_list, problem.weight_limit)

    # 初始化排样状态
    ps = PackingState(avail_list=problem.num_list.copy())
    # 开始时，剩余空间堆栈中只有容器本身
    ps.space_stack.push(problem.container)

    # 所有剩余空间均转满，则停止
    while ps.space_stack.size() > 0:
        space = ps.space_stack.top()
        block_list = gen_block_list(space, ps.avail_list, block_table, problem.weight_limit - ps.weight)
        if block_list:
            # 查找下一个近似最优块
            block = find_next_block(ps, block_list, block_table, search_params, problem.weight_limit)
            # 弹出顶部剩余空间
            ps.space_stack.pop()
            # 更新可用物品数量
            ps.avail_list = (np.array(ps.avail_list) - np.array(block.require_list)).tolist()
            # 更新排样计划
            ps.plan_list.append(Place(space, block))
            # 更新已利用体积
            ps.volume += block.volume
            # 更新排样重量
            ps.weight += block.weight
            # 压入新裁切的剩余空间
            cuboid1, cuboid2, cuboid3 = gen_residual_space(space, block)
            ps.space_stack.push(cuboid1, cuboid2, cuboid3)
        else:
            # 转移剩余空间
            transfer_space(space, ps.space_stack)

    # 返回最终的排样状态对象
    return ps

# 从数据库获取产品信息
def get_product_info(goods_code):
    try:
        # 发送 HTTP GET 请求到 Web API
        url = f"http://192.168.1.228:8866/get_product_info?goods_code={goods_code}"
        print(f"正在请求 URL: {url}")  # 打印 URL 以供调试
        response = requests.get(url)
        
        print(f"HTTP 状态码: {response.status_code}")  # 打印 HTTP 状态码
        print(f"响应内容: {response.text}")  # 打印返回的响应内容
        
        if response.status_code == 200:
            data = response.json()
            return float(data['length']), float(data['width']), float(data['height']), float(data['weight'])
        else:
            error_message = response.json().get('error', 'Unknown error')
            print(f"错误: {error_message}")
            return None
    except Exception as e:
        print(f"访问 API 时出现错误: {e}")
        return None

# 运行装箱算法
def run_packing(length, width, height, weight_limit, goods_list):
    global tmp_best_ps
    tmp_best_ps = PackingState([], Stack(), [])
    global dimension_unit
    global weight_unit

    # 初始化箱体列表和数量列表
    box_list = []
    num_list = []
    total_weight = 0.0

    # 检查产品信息
    for idx, (goods_code, quantity) in enumerate(goods_list):
        product_info = get_product_info(goods_code)
        if not product_info:
            messagebox.showerror("错误", f"无法获取货号为 {goods_code} 的产品信息。")
            return None, None
        product_length, product_width, product_height, product_weight = product_info

        # 检查单个产品尺寸是否超出容器限制
        if product_length > length or product_width > width or product_height > height:
            messagebox.showerror(
                "尺寸超限错误",
                f"货号为 {goods_code} 的产品尺寸超出容器限制，无法摆放。\n"
                f"货物尺寸：{product_length}x{product_width}x{product_height} "
                f"（容器尺寸：{length}x{width}x{height}）"
            )
            return None, None

        # 检查单个产品重量是否超重
        if product_weight > weight_limit:
            messagebox.showerror(
                "超重错误",
                f"货号为 {goods_code} 的产品超重，无法摆放。"
            )
            return None, None

        # 创建箱体对象，type设置为当前索引
        box = Box(product_length, product_width, product_height, idx, product_weight)
        box_list.append(box)
        num_list.append(quantity)
        total_weight += product_weight * quantity

    if not box_list:
        messagebox.showerror("错误", "没有可摆放的产品。")
        return None, None

    # 计算所有货物的总体积
    total_volume = 0.0
    for idx, box in enumerate(box_list):
        quantity = num_list[idx]
        total_volume += box.lx * box.ly * box.lz * quantity

    # 计算容器的容量
    container_volume = length * width * height

    if total_volume > container_volume:
        messagebox.showerror(
            "容量超限错误",
            f"所有货物的总体积超出了容器的容量，无法摆放。\n"
            f"货物总体积：{total_volume:.2f} 立方{dimension_unit}\n"
            f"容器容量：{container_volume:.2f} 立方{dimension_unit}"
        )
        return None, None

    if total_weight > weight_limit:
        messagebox.showerror(
            "重量超限错误",
            f"所有货物的总重量超出了容器的重量限制，无法摆放。\n"
            f"货物总重量：{total_weight:.2f} {weight_unit}\n"
            f"容器重量限制：{weight_limit:.2f} {weight_unit}"
        )
        return None, None

    # 容器
    container = Space(0, 0, 0, length, width, height)
    # 问题
    problem = Problem(container, box_list, num_list, weight_limit)
    search_params = dict()

    # 执行算法并获取结果状态
    ps = basic_heuristic(True, search_params, problem)

    if ps is None or not ps.plan_list:
        messagebox.showerror("错误", "未能生成有效的排样方案，请检查输入参数。")
        return None, None

    # 检查是否所有货物都已放置
    if any(np.array(ps.avail_list) > 0):
        # 计算每种货物实际放置的数量
        initial_quantities = np.array(problem.num_list)
        remaining_quantities = np.array(ps.avail_list)
        placed_quantities = initial_quantities - remaining_quantities

        # 构建提示信息
        message = "无法将所有货物装入容器，未能完全装箱。\n\n"
        message += "以下是每种货物的装载情况：\n"
        for idx, (goods_code, _) in enumerate(goods_list):
            message += f"货号 {goods_code}：已放入 {placed_quantities[idx]} 个，剩余 {remaining_quantities[idx]} 个未能放入。\n"
        # 分析未能放入的原因
        message += "\n可能的原因：\n"
        message += "1. 剩余空间不足以放入更多的货物。\n"
        message += "2. 算法限制，未能找到合适的放置方式。\n"
        message += "3. 货物尺寸或重量超过了剩余空间的限制。\n"
        messagebox.showwarning("部分装箱完成", message)
        # 如果未能全部装箱，则不生成三维图
        return None, None

    # 成功返回结果
    return ps, problem

# 异步任务完成后，将绘图操作调度到主线程中
def run_packing_async(length, width, height, weight_limit, goods_list):
    def packing_task():
        global tmp_best_ps

        tmp_best_ps = PackingState([], Stack(), [])

        try:
            ps, problem = run_packing(length, width, height, weight_limit, goods_list)
            if ps is not None:
                root.after(0, lambda: draw_packing_result(problem, ps))
            else:
                # 在主线程中显示信息，表示未生成排样方案
                root.after(0, lambda: messagebox.showinfo("装箱结果", "未能将所有货物装入容器，未生成排样方案。"))
        except Exception as e:
            # 在主线程中显示错误信息
            root.after(0, lambda: messagebox.showerror("错误", f"装箱算法出现异常：{e}"))

    # 启动异步线程执行装箱任务
    packing_thread = threading.Thread(target=packing_task)
    packing_thread.start()

def main():
    global root
    global dimension_unit
    global weight_unit
    root = tk.Tk()
    root.title("三维装箱问题求解器")

    # 容器尺寸输入
    container_frame = tk.Frame(root)
    container_frame.pack(pady=10)

    tk.Label(container_frame, text="容器尺寸").grid(row=0, column=0, columnspan=4)

    tk.Label(container_frame, text="长度:").grid(row=1, column=0)
    entry_length = tk.Entry(container_frame)
    entry_length.grid(row=1, column=1)
    unit_length = tk.StringVar(value="in")
    tk.OptionMenu(container_frame, unit_length, "in", "cm").grid(row=1, column=2)

    tk.Label(container_frame, text="宽度:").grid(row=2, column=0)
    entry_width = tk.Entry(container_frame)
    entry_width.grid(row=2, column=1)
    unit_width = tk.StringVar(value="in")
    tk.OptionMenu(container_frame, unit_width, "in", "cm").grid(row=2, column=2)

    tk.Label(container_frame, text="高度:").grid(row=3, column=0)
    entry_height = tk.Entry(container_frame)
    entry_height.grid(row=3, column=1)
    unit_height = tk.StringVar(value="in")
    tk.OptionMenu(container_frame, unit_height, "in", "cm").grid(row=3, column=2)

    # 重量限制输入
    tk.Label(container_frame, text="重量限制:").grid(row=4, column=0)
    entry_weight_limit = tk.Entry(container_frame)
    entry_weight_limit.grid(row=4, column=1)
    unit_weight_limit = tk.StringVar(value="lb")
    tk.OptionMenu(container_frame, unit_weight_limit, "lb", "kg").grid(row=4, column=2)

    # 产品输入
    products_frame = tk.Frame(root)
    products_frame.pack(pady=10)

    tk.Label(products_frame, text="产品列表").grid(row=0, column=0, columnspan=5)

    tk.Label(products_frame, text="产品货号:").grid(row=1, column=0)
    entry_product_code = tk.Entry(products_frame)
    entry_product_code.grid(row=1, column=1)

    tk.Label(products_frame, text="数量:").grid(row=1, column=2)
    entry_quantity = tk.Entry(products_frame)
    entry_quantity.grid(row=1, column=3)

    # 添加产品按钮
    def add_product():
        product_code = entry_product_code.get().strip()
        quantity = entry_quantity.get().strip()
        if product_code and quantity.isdigit():
            product_listbox.insert(tk.END, f"{product_code},{quantity}")
            entry_product_code.delete(0, tk.END)
            entry_quantity.delete(0, tk.END)
        else:
            messagebox.showwarning("输入错误", "请输入有效的产品货号和数量。")

    tk.Button(products_frame, text="添加产品", command=add_product).grid(row=1, column=4)

    # 产品列表显示
    product_listbox = tk.Listbox(products_frame, width=50)
    product_listbox.grid(row=2, column=0, columnspan=5, pady=10)

    # 移除选定的产品
    def remove_product():
        selected_indices = product_listbox.curselection()
        for index in reversed(selected_indices):
            product_listbox.delete(index)

    tk.Button(products_frame, text="移除选定产品", command=remove_product).grid(row=3, column=0, columnspan=5)

    # 提交按钮
    def submit():
        global tmp_best_ps
        global dimension_unit
        global weight_unit
        # 获取容器尺寸
        try:
            length_input = float(entry_length.get())
            if unit_length.get() == "in":
                length = length_input  # 保持英寸
                dimension_unit = "in"
            elif unit_length.get() == "cm":
                length = length_input / 2.54  # 转换为英寸
                dimension_unit = "cm"
            else:
                messagebox.showerror("输入错误", "未知的长度单位。")
                return

            width_input = float(entry_width.get())
            if unit_width.get() == "in":
                width = width_input
                dimension_unit = "in"
            elif unit_width.get() == "cm":
                width = width_input / 2.54
                dimension_unit = "cm"
            else:
                messagebox.showerror("输入错误", "未知的宽度单位。")
                return

            height_input = float(entry_height.get())
            if unit_height.get() == "in":
                height = height_input
                dimension_unit = "in"
            elif unit_height.get() == "cm":
                height = height_input / 2.54
                dimension_unit = "cm"
            else:
                messagebox.showerror("输入错误", "未知的高度单位。")
                return
        except ValueError:
            messagebox.showerror("输入错误", "请输入有效的容器尺寸。")
            return

        # 获取重量限制
        try:
            weight_limit_input = float(entry_weight_limit.get())
            if unit_weight_limit.get() == "lb":
                weight_limit = weight_limit_input  # 保持磅
                weight_unit = "lb"
            elif unit_weight_limit.get() == "kg":
                weight_limit = weight_limit_input * 2.20462  # 转换为磅
                weight_unit = "kg"
            else:
                messagebox.showerror("输入错误", "未知的重量单位。")
                return
        except ValueError:
            messagebox.showerror("输入错误", "请输入有效的重量限制。")
            return

        # 获取产品列表
        goods_list = []
        for item in product_listbox.get(0, tk.END):
            parts = item.strip().split(',')
            if len(parts) != 2:
                messagebox.showerror("输入错误", f"无效的产品输入：{item}")
                return
            goods_code = parts[0].strip()
            try:
                quantity = int(parts[1].strip())
            except ValueError:
                messagebox.showerror("输入错误", f"无效的数量：{parts[1]}")
                return
            goods_list.append((goods_code, quantity))

        if not goods_list:
            messagebox.showerror("输入错误", "请添加至少一个产品。")
            return

        # 清空放置计划和全局状态
        tmp_best_ps = PackingState([], Stack(), [])
        # 调用异步执行装箱
        run_packing_async(length, width, height, weight_limit, goods_list)

        # 清空产品列表框，避免重复输入
        product_listbox.delete(0, tk.END)

    tk.Button(root, text="提交", command=submit).pack(pady=10)

    root.mainloop()

if __name__ == "__main__":
    main()
