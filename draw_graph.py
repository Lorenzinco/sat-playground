from pyvis.network import Network
import networkx as nx

g = nx.drawing.nx_pydot.read_dot("graph.dot")

net = Network(height="900px", width="100%", directed=True, notebook=False)
net.from_nx(g)

for node in net.nodes:
    node["size"] = 40
    node["font"] = {
        "size": 24,
        "face": "monospace",
        "color": "black",
    }

net.barnes_hut()
net.write_html("graph.html", open_browser=True, notebook=False)
