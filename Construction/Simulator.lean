/-
The simulator machine's construction root: the CRT machine (`Construction/Simulator/CRT/Simulator.lean`) and the
release-r1 blocks it is assembled from (`Construction/Simulator/{Prog, Blocks, Layout, Stage1, Request, Stage2,
Opening}.lean`). The machine itself, `CrtTop.crtSimulator`, is closed on the proof side
(`Proof/Simulator/CRT/Machine.lean`), where its cost bound is proved.
-/

import Construction.Simulator.CRT.Simulator
