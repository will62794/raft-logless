import json
import graphviz
import os
import shutil


def parse_logs(trace_file):
    """Parse trace file and extract logs for each node"""
    with open(trace_file) as f:
        trace = json.load(f)

    # Clean up old files from imgs directory
    if os.path.exists('imgs'):
        shutil.rmtree('imgs')
    os.makedirs('imgs')

    # Extract all states from the trace
    states = []
    for state in trace["state"]:
        states.append(state[1]) # Each action has state at index 0,1

    # Extract logs for each node from each state
    node_logs = {}
    n = 0
    for state in states:
        tree_edges = []
        tree_nodes = []
        print("State:", n)
        for node, log in state["log"].items():
            print(node, log)
            if node not in node_logs:
                node_logs[node] = []
            node_logs[node].append(log)
            
            # Add edges between adjacent log entries
            for i in range(len(log)-1):
                edge = ((i+1, log[i]), (i+2, log[i+1]))
                tree_edges.append(edge)
            for i in range(len(log)):
                tree_nodes.append((i+1, log[i]))
        print(tree_edges)
        # Create graphviz graph from edges
        dot = graphviz.Digraph(strict=True)
        dot.attr(rankdir='LR')
        dot.attr(fontname='Helvetica')
        dot.attr('node', fontname='Helvetica')
        dot.attr('edge', fontname='Helvetica')
        dot.attr(dpi='300') # Increase resolution

        def last_log_entry(n):
            return (len(state["log"][n]), state["log"][n][-1])
        
        for node in tree_nodes:
            src = f"({node[0]},{node[1]})"
            is_committed = (list(node) + [node[1]]) in state["committed"]
            # print((list(node) + [node[1]]), state["committed"], is_committed)
            nodeatset = [n for n in state["log"].keys() if len(state["log"][n]) > 0 and last_log_entry(n) == node]
            nodeat_xlabel = ",".join([n for n in nodeatset])
            if len(nodeatset) > 0:
               nodeat_xlabel = "{" + nodeat_xlabel + "}"
            node_attrs = {
                'shape': 'box',
                'style': 'filled',
                'fillcolor': 'lightgreen' if is_committed else 'white',
                'xlabel': nodeat_xlabel,
                'fontsize': '10',  # Add smaller font size for xlabel
            }
            dot.node(src, **node_attrs)

        # Add edges to graph
        for edge in tree_edges:
            # Convert tuple coordinates to strings for node labels
            src = f"({edge[0][0]},{edge[0][1]})"
            dst = f"({edge[1][0]},{edge[1][1]})"
            
            # Add nodes and edge
            # dot.node(src, shape='box')
            # dot.node(dst, shape='box')
            dot.edge(src, dst)

        # Render graph to PNG
        if len(tree_nodes) > 0:
            dot.render(f"imgs/log_tree_{n}", format="png", cleanup=True)
        n += 1
    return node_logs


if __name__ == "__main__":
    node_logs = parse_logs("trace.json")
    # print(node_logs)
    # for n in node_logs:
        # print(n)
        # print(node_logs[n])
        # for log in node_logs[n]:
            # print(log)
        # print("-" * 100)