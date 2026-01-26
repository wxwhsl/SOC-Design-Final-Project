#!/usr/bin/env python3
"""
评估器主程序
用法:
    python evaluator.py grid_layout.json netlist.json routing.json min_layers(可选)

输出:
    JSON报告，包含：
    - disconnected_nets: 未连通的网络
    - invalid_segments: 非法布线段
    - grid_overuse: 网格重叠使用
    - sharp_angles: 锐角位置
    - notes: 提示
    - wirelength_by_net: 每个net线段长度
    - wirelength: 线段总长度*
    - layers: 存在哪些层
    - layers_count: 总层数
    - layer_factor: 层数指标*（如果不输入min_layers则不计算该指标）
    - summary: 检查结果汇总
"""

import json
import math
import sys
from collections import defaultdict, deque

# 工具函数
def load_json(path):
    """读取JSON文件"""
    with open(path, 'r', encoding='utf-8') as f:
        return json.load(f)

def find_bump_coord(name, grid_layout):
    """根据名称查找焊点坐标"""
    name_norm = name.strip().lower()

    def get_coords(item):
        try:
            x = int(item.get('grid_coord_x', item.get('x', 0)))
            y = int(item.get('grid_coord_y', item.get('y', 0)))
            return (x, y)
        except (ValueError, TypeError):
            return None

    for t, layer in (('top_layer','Top'), ('bottom_layer','Bottom')):
        arr = grid_layout.get(t, [])
        for item in arr:
            # 只匹配 bump_name 和 c4_name
            for key in ('bump_name', 'c4_name'):
                if key in item and item[key].strip().lower() == name_norm:
                    coords = get_coords(item)
                    if coords:
                        return (*coords, layer)
    return None

def coords_equal(a, b):
    """判断两个坐标是否完全相同"""
    return a[0] == b[0] and a[1] == b[1] and a[2] == b[2]

def neighbours8(a, b):
    """判断两个点是否为8邻域（含对角线）"""
    dx = abs(a[0]-b[0]); dy = abs(a[1]-b[1])
    return max(dx,dy)==1 and not (dx==0 and dy==0)

def expand_segment(start, end):
    """将布线段展开为网格点列表，支持直线和通孔"""
    x1,y1,lay1 = start
    x2,y2,lay2 = end
    # 通孔（同一坐标，不同层）
    if x1==x2 and y1==y2 and lay1!=lay2:
        return [(x1,y1,lay1), (x2,y2,lay2)]
    if lay1 != lay2 and (x1 != x2 or y1 != y2):
        # 不允许在位置变化的同时换层移动（仅允许在同一网格上的通孔）
        return None
    dx = x2 - x1
    dy = y2 - y1
    adx = abs(dx); ady = abs(dy)
    # 必须是直线或对角线：dx==0 或 dy==0 或 abs(dx)==abs(dy)
    if not (dx==0 or dy==0 or adx==ady):
        return None
    steps = max(adx, ady)
    if steps == 0:
        # 退化情况：同一点同层
        return [(x1,y1,lay1)]
    step_x = dx // steps
    step_y = dy // steps
    points = []
    for i in range(steps+1):
        xi = x1 + step_x * i
        yi = y1 + step_y * i
        points.append((xi, yi, lay1))
    return points

def angle_between(p_prev, p_curr, p_next):
    """
    计算三点形成的转角（内角）。
    返回角度范围：0°到180°
    0°：完全反向（U-turn）
    180°：完全同向（直线）
    90°：直角转弯
    """
    x1, y1, _ = p_prev
    x2, y2, _ = p_curr
    x3, y3, _ = p_next
    
    v1 = (x1 - x2, y1 - y2)  # 指向p_prev
    v2 = (x3 - x2, y3 - y2)  # 指向p_next
    
    # 处理重复点
    if (abs(v1[0]) < 1e-6 and abs(v1[1]) < 1e-6) or \
       (abs(v2[0]) < 1e-6 and abs(v2[1]) < 1e-6):
        return 180.0  # 或根据需求返回特定值
    
    len1 = math.hypot(v1[0], v1[1])
    len2 = math.hypot(v2[0], v2[1])
    
    dot = v1[0] * v2[0] + v1[1] * v2[1]
    cross = v1[0] * v2[1] - v1[1] * v2[0]
    
    # 使用atan2获取带方向的夹角
    angle_rad = math.atan2(abs(cross), dot)  # 或 math.atan2(cross, dot)获取有符号角度
    angle_deg = math.degrees(angle_rad)
    
    # 转换为内角（0-180°）
    if angle_deg < 0:
        angle_deg = 360 + angle_deg
    
    # 确保在0-180°范围内
    if angle_deg > 180:
        angle_deg = 360 - angle_deg
    
    return round(angle_deg, 2)
    
def evaluate(grid_layout, netlist, routing, min_layers=None):
    """主评估流程，检查网络连通性、布线合法性等"""
    report = {
        'disconnected_nets': [],
        'invalid_segments': [],
        'grid_overuse': [],  # list of {coord, count, nets}
        'sharp_angles': [],  # list of {net, coordinate, angle_deg, context}
        'notes': []
    }

    # 构建焊点名称到坐标的映射
    nets = netlist.get('nets', []) if isinstance(netlist, dict) else []
    # 支持 dict 或 list 格式，直接使用原始 key（如 net_0、net_1）
    if isinstance(routing, dict):
        routing_map = dict(routing)
    elif isinstance(routing, list):
        routing_map = {}
        for item in routing:
            if isinstance(item, dict):
                for k, v in item.items():
                    routing_map[k] = v
    else:
        routing_map = {}

    # 展开布线段，统计网格占用，构建连通图
    occupancy = defaultdict(lambda: {'count':0, 'nets': set()})  # key=(x,y,layer)
    # 同时为每个网构建连通性图：节点以 (x,y,layer) 为键
    net_graph_nodes = defaultdict(set)  # net_name -> set of nodes present in routing
    net_graph_adj = defaultdict(lambda: defaultdict(set))  # net_name -> node -> set(neigh nodes)
    # 统计 wirelength（以网格单位计算，使用点间欧几里得距离；通孔（同 xy 不同层）视为 0 长度）
    total_wirelength = 0.0
    wirelength_by_net = defaultdict(float)
    # 统计在 routing 中出现的不同层（归一化为小写以便去重）
    layers_set = set()

    # 验证布线段，填充占用和邻接信息
    for net_name, segs in routing_map.items():
        if not isinstance(segs, list):
            report['notes'].append(f"routing for net {net_name} is not a list; skipped")
            continue
        for seg in segs:
            if not isinstance(seg, dict):
                report['notes'].append(f"segment for net {net_name} malformed: {seg}")
                continue
            s = seg.get('start_grid_coordinate')
            e = seg.get('end_grid_coordinate')
            if s is None or e is None or len(s)<3 or len(e)<3:
                report['notes'].append(f"segment for net {net_name} missing coords: {seg}")
                continue
            start = (int(s[0]), int(s[1]), str(s[2]))
            end   = (int(e[0]), int(e[1]), str(e[2]))
            expanded = expand_segment(start, end)
            if expanded is None:
                report['invalid_segments'].append({'net': net_name, 'start': start, 'end': end, 'reason': 'non-queen-line or invalid layer-change move'})
                continue
            # 计算该段的长度（按展开点之间的欧几里得距离累加，忽略层变化）
            seg_len = 0.0
            if len(expanded) >= 2:
                for i in range(1, len(expanded)):
                    x1, y1, _ = expanded[i-1]
                    x2, y2, _ = expanded[i]
                    seg_len += math.hypot(x2 - x1, y2 - y1)
            total_wirelength += seg_len
            wirelength_by_net[net_name] += seg_len
            # 如果是通孔，expanded 包含两个不同层的节点
            # 为所有网格位置登记占用（对跨多个网格的段）
            # 并为相邻展开点构建邻接关系
            prev = None
            for pt in expanded:
                # 记录层名（归一化）
                try:
                    layers_set.add(str(pt[2]).strip().lower())
                except Exception:
                    layers_set.add(str(pt[2]))
                # occupancy 按 (x,y,layer) 计数
                occupancy[pt]['count'] += 1
                occupancy[pt]['nets'].add(net_name)
                net_graph_nodes[net_name].add(pt)
                if prev is not None:
                    # 邻接关系（无向）
                    net_graph_adj[net_name][prev].add(pt)
                    net_graph_adj[net_name][pt].add(prev)
                prev = pt

    # 检查网格重叠使用

    overuse_list = []
    for coord, info in occupancy.items():
        nets_here = sorted(list(info['nets']))
    # 如果一个格点被多个不同的网占用，则视为冲突
        if len(nets_here) > 1:
            overuse_list.append({
                'coord': coord,
                'count': info['count'],
                'nets': nets_here
            })
    report['grid_overuse'] = overuse_list

    # 将 wirelength 汇总写入报告（总长度与按网统计，保留 4 位小数）
    
    report['wirelength_by_net'] = {k: round(v, 4) for k, v in wirelength_by_net.items()}
    report['wirelength'] = round(total_wirelength, 4)
    # 将不同层信息写入报告：按字母序返回归一化的小写层名列表
    report['layers'] = sorted(list(layers_set))
    report['layers_count'] = len(layers_set)

    # 可选：如果提供了 min_layers，计算 layer_factor 并写入报告
    if min_layers is not None:
        try:
            ml = float(min_layers)
            if ml > 0:
                layer_factor = (report['layers_count'] / ml - 1) * 0.2 + 1
                report['layer_factor'] = round(layer_factor, 4)
            else:
                report['notes'].append(f"min_layers provided <= 0: {min_layers}; layer_factor skipped")
        except Exception as e:
            report['notes'].append(f"invalid min_layers '{min_layers}': {e}")


    # 检查每个网络的焊点是否全部连通
    disconnected = []
    for net in nets:
        net_name = net.get('net_name')
        bumps = net.get('bumps', [])
        expected_nodes = []
        for b in bumps:
            cand = None
            if isinstance(b, dict) and 'bump_name' in b:
                cand = b['bump_name']
            if cand is None:
                continue
            coord = find_bump_coord(cand, grid_layout)
            if coord is None:
                report['notes'].append(f"Cannot locate bump named '{cand}' for net '{net_name}' in grid_layout.")
            else:
                expected_nodes.append((coord[0], coord[1], coord[2]))
        # 如果 netlist 不可用（routing_map 可能包含 netlist 中没有的网），可回退到 routing 中的节点
        if len(expected_nodes)==0:
            report['notes'].append(f"No bump coordinates found for net '{net_name}'; skipping connectivity check.")
            continue

    # 检查焊点是否在路由中可达
        present_nodes = net_graph_nodes.get(net_name, set())
            
    # 确保期望节点存在
    # 构建从 xy -> present_nodes 列表的映射
        xy_to_nodes = defaultdict(list)
        for n in present_nodes:
            xy_to_nodes[(n[0],n[1])].append(n)
            
        # 对于每个期望节点，在路由中查找对应节点：检查是否存在可达路径
        mapped_expected = []
        missing_expected = []
        for en in expected_nodes:
            xy_key = (en[0], en[1])
            connected = False
            # 检查是否有完全匹配的点
            if xy_key in xy_to_nodes:
                for node in xy_to_nodes[xy_key]:
                    if node[2].lower() == en[2].lower():
                        mapped_expected.append(node)
                        connected = True
                        break
                
                # 如果没有完全匹配，但有其他层的点，并且存在通过通孔的连接
                if not connected and len(xy_to_nodes[xy_key]) > 0:
                    # 检查是否有通过通孔连接到目标层的路径
                    target_layer = en[2].lower()
                    for node in xy_to_nodes[xy_key]:
                        if any(n[2].lower() == target_layer for n in net_graph_adj[net_name][node]):
                            mapped_expected.append(node)
                            connected = True
                            break
                    if not connected:
                        # 如果至少有一个点在这个位置，就认为它是连通的
                        # （因为已经在图中建立了层间的连接）
                        mapped_expected.append(xy_to_nodes[xy_key][0])
                        connected = True
            
            if not connected:
                missing_expected.append(en)
                
        if missing_expected:
            report['disconnected_nets'].append({'net': net_name, 'reason': 'expected bump(s) not present in routing', 'missing_bumps': missing_expected})
            continue
    # 从第一个映射到的期望节点进行 BFS，以检查可达节点
        start = mapped_expected[0]
        q = deque([start])
        visited = set([start])
        while q:
            u = q.popleft()
            for v in net_graph_adj[net_name].get(u, []):
                if v not in visited:
                    visited.add(v); q.append(v)
        # check that all mapped_expected in visited
        not_reached = [n for n in mapped_expected if n not in visited]
        if not_reached:
            report['disconnected_nets'].append({'net': net_name, 'reason': 'some bumps not connected', 'unreached': not_reached})
        # else connected

    # 检查路径中的锐角
    for net_name, adj in net_graph_adj.items():
        nodes = list(adj.keys())
        if not nodes:
            continue
        visited_comp = set()
        for node in nodes:
            if node in visited_comp:
                continue
            # 使用 BFS 提取这个连通分量（视为无向图），然后尝试生成路径
            comp_nodes = set()
            q = deque([node]); comp_nodes.add(node)
            while q:
                u = q.popleft()
                for v in adj[u]:
                    if v not in comp_nodes:
                        comp_nodes.add(v); q.append(v)
            visited_comp |= comp_nodes
            # 希望生成覆盖边的路径（walk）：简单方法是把所有度 != 2 的节点视为端点，然后在端点间追踪路径
            deg = {n: len(adj[n]) for n in comp_nodes}
            endpoints = [n for n,d in deg.items() if d != 2]
            if not endpoints:
                # 环路：任选一个节点并沿环路遍历
                endpoints = [next(iter(comp_nodes))]
            used_edges = set()
            def trace_path(start_node):
                path = [start_node]
                prev = None
                cur = start_node
                while True:
                    nbrs = [v for v in adj[cur] if v != prev]
                    if not nbrs:
                        break
                    nxt = nbrs[0]
                    edge = tuple(sorted((cur,nxt)))
                    if edge in used_edges:
                        break
                    used_edges.add(edge)
                    prev, cur = cur, nxt
                    path.append(cur)
                return path
            paths = []
            for ep in endpoints:
                p = trace_path(ep)
                if len(p) >= 2:
                    paths.append(p)
            # Also try to capture leftover edges
            # 现在对每条路径计算角度
            for p in paths:
                # compress consecutive duplicate xy positions (could appear due to via entries)
                # 压缩连续重复的 xy（可能由通孔导致）
                p2 = []
                for pt in p:
                    if not p2 or (pt[0],pt[1]) != (p2[-1][0], p2[-1][1]):
                        p2.append(pt)
                # iterate triplets
                for i in range(1, len(p2)-1):
                    prev_pt = p2[i-1]
                    cur_pt = p2[i]
                    next_pt = p2[i+1]
                    if prev_pt[2] == cur_pt[2] == next_pt[2]:
                        ang = angle_between(prev_pt, cur_pt, next_pt)
                        if ang is None:
                            continue
                        if ang < 90.0 and ang != 0:
                            report['sharp_angles'].append({'net': net_name, 'at': cur_pt, 'angle_deg': round(ang,2),
                                                        'prev': prev_pt, 'next': next_pt})
    # 汇总所有检查结果
    ok = (len(report['disconnected_nets'])==0 and len(report['invalid_segments'])==0 and len(report['grid_overuse'])==0 and len(report['sharp_angles'])==0)
    report['summary'] = {
        'pass': ok,
        'disconnected_nets_count': len(report['disconnected_nets']),
        'invalid_segments_count': len(report['invalid_segments']),
        'grid_overuse_count': len(report['grid_overuse']),
        'sharp_angles_count': len(report['sharp_angles']),
    }
    return report

def main(argv):
    # 支持可选的第四个参数 min_layers
    if len(argv) not in (4, 5):
        print("Usage: python evaluator.py grid_layout.json netlist.json routing.json [min_layers]")
        sys.exit(2)
    grid_path, netlist_path, routing_path = argv[1], argv[2], argv[3]
    min_layers = None
    if len(argv) == 5:
        # 解析错误反馈
        try:
            min_layers = float(argv[4])
        except Exception as e:
            print(json.dumps({'error': f'invalid min_layers: {e}'}))
            sys.exit(2)
    try:
        grid_layout = load_json(grid_path)
        netlist = load_json(netlist_path)
        routing = load_json(routing_path)
    except Exception as e:
        print(json.dumps({'error': str(e)}))
        sys.exit(1)
    report = evaluate(grid_layout, netlist, routing, min_layers=min_layers)
    # 将评估结果写入文件
    out_path = 'report.json'
    try:
        with open(out_path, 'w', encoding='utf-8') as f:
            json.dump(report, f, ensure_ascii=False, indent=2)
        # 仅输出保存确认信息
        print(f"Report written to {out_path}")
    except Exception as e:
        # 如果写入失败，则返回错误信息并以非零状态退出
        print(json.dumps({'error': str(e)}))
        sys.exit(1)

if __name__ == '__main__':
    # argv = ['./evaluator.py', './case4/grid_layout.json', './case4/netlist.json', './case4/routing_fordebug']
    # argv = ['./evaluator.py', './case2/grid_layout.json', './case2/netlist.json', './case2/output.json']
    # main(argv)
    main(sys.argv)
