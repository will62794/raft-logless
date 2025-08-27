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
        
        for node in tree_nodes:
            src = f"({node[0]},{node[1]})"
            dot.node(src, shape='box')

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
        if len(tree_edges) > 0:
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