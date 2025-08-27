import json
import graphviz
import os
import shutil
from PIL import Image



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

    actions = []
    for action in trace["action"]:
        name = action[1]["name"]
        context = action[1]["context"]
        parameters = action[1]["parameters"]
        actions.append((name, context, parameters))
    print(actions)

    html_out = "<table>"

    html_div_template = """
<div style="text-align: center;margin-bottom:20px">
<img src="/assets/logless-raft/imgs/log_tree_{n}.png" alt="Logless Raft Diagram" height="{height}">
State {n} - {action_str}
</div>
"""

    html_div_template = """
<tr>
<td style="text-align: left; font-size: 12px; padding-right: 20px">State {n} - {action_str}</td>
<td style="text-align: left">
<img src="/assets/logless-raft/imgs/log_tree_{n}.png" alt="Logless Raft Diagram" height="{height}">
</td>
</tr>
"""


    # Extract logs for each node from each state
    node_logs = {}
    n = 0
    for state in states:
        tree_edges = []
        tree_nodes = []
        print("State:", n)
        # print("Action:", actions[n-1])
        action_args = [str(actions[n-1][1][arg]) for arg in actions[n-1][2]]
        print(action_args)
        action_str = f"{actions[n-1][0]}({', '.join(action_args)})"
        print("Action:", action_str)
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
                'fontsize': '13'  # Add smaller font size for xlabel,
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
            png_file = f"imgs/log_tree_{n}.png"
            img = Image.open(png_file)
            width, height = img.size
            html_out += html_div_template.format(n=n, action_str=action_str, height=height*0.2)
        n += 1
    html_out += "</table>"

    # Save the HTML output to a file
    with open('log_tree.html', 'w') as f:
        f.write(html_out)

    # Combine all PNGs into a filmstrip
    import glob

    # Get all PNG files in imgs directory, sorted numerically
    png_files = sorted(glob.glob('imgs/log_tree_*.png'), key=lambda x: int(x.split('_')[-1].split('.')[0]))
    
    if png_files:
        # Get dimensions of each image
        images = []
        total_width = 0
        max_height = 0
        # First pass to get max dimensions
        max_width = 0
        max_height = 0
        heights = []
        for png_file in png_files:
            img = Image.open(png_file)
            width, height = img.size
            heights.append(height + 100)
            max_width = max(max_width, width)
            max_height = max(max_height, height)
            images.append(img)

        max_height += 100
        max_width += 100

        total_height = sum(heights)

        # Calculate grid dimensions
        images_per_row = 1
        num_rows = (len(images) + images_per_row - 1) // images_per_row  # Ceiling division
        
        # Create new image with dimensions for grid layout
        filmstrip = Image.new('RGB', 
                            (max_width * min(images_per_row, len(images)), 
                             total_height + 10 * len(images)), 
                            'white')
        
        # Paste each image in grid pattern
        for i, img in enumerate(images):
            row = i
            # row = i // images_per_row
            col = 0
            # col = i % images_per_row
            x_offset = col * max_width
            # y_offset = row * max_height
            y_offset = sum(heights[:i]) + 20
            filmstrip.paste(img, (x_offset, y_offset))
            
        # Save combined image
        filmstrip.save('imgs/log_tree_filmstrip.png')
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