matt-s-stuff
============

matt's stuff


GearCurve[n_][t_] := (1 + 1/10 Tanh[10 Sin[n t]]) {Cos[t], Sin[t]}

Plot[1 + 1/10 Tanh[10 Sin[12 t]], {t, 0, 2 \[Pi]}]
