(set-logic ALL)
(synth-fun g 
	((r Int)) Bool 
	((B Bool) (I Int) (IConst Int)) 
	(
		(B Bool ((= I I) (=> B B)))
		(I Int ((Variable Int) 0 (mod I IConst)))
		(IConst Int ((Constant Int)))
	)
) 
(constraint (g 0))
(constraint (not (g 1)))
(constraint (g 2))
(check-synth)
