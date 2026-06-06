# Math-157-Project-Code-component

This is my submission for the Math 157 Project, specifically on the code component. My goal was to formalize the Handshaking Lemma and its proof using lists and induction rather than Mathlib's graph functions. I was curious on if I would be able to do so. On the Zulip community page, most of the related proofs to the Handshaking Lemma utilized Mathlib's graph functions. Also, I made a few adjustments that don't necessarily adhere to the proof of the Handshaking Lemma, but I believe demonstrates a very similar and even equivalent path.

One adjustment I made was defining the function to find the total degree of a graph. Here, I base the function on edges rather than vertices since this was causing errors when I was calling the function later in the code. I believe this offers a valid representation. However, this does result in the lack of use for my V (vertices) list. Furthermore, I assume a simple and undirected graph for simplicity, since I was having a hard time with the self-loops.

The MyProject.lean contains my actual code.

Note: I did use ChatGPT to help create an outline of what structures, functions, and lemmas needed to build up the Handshaking Lemma. I also consulted the Mathematics in Lean page.
