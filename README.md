# Definitional UIP Makes Constructing Inductive-Inductive Types Straightforward

Performing a Forsberg-style 2-layer construction of Inductive-Inductive types, with the second layer in SProp with UIP, everything works like a charm. For the eliminator, perform a similar 2-layer dance, and you get the general eliminator with definitional computation rules. Everything you want you get.

This repository is a work in progress, but the essential idea is demonstrated in `theories/Example.v`. Eventually, I want to add in the construction of an internal universe of II types (which I know how to do, just haven't done it yet), but right now I'm not motivated to do so.

Talk to me if you want help understanding the code, or want to hear more about my idea for an internal universe of II types. I think these ideas are worthy of a paper, but right now I don't want to write it. If you do, go ahead.
