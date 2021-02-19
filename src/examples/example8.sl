(set-logic ALL)
(synth-fun g 
	((r Float)) Bool 
	((B Bool) (F Float)) 
	(
		(B Bool ((= F F) (=> B B)))
		(F Float ((Variable Float) 0))
	)
) 
(constraint (g 0.0))
(constraint (not (g 1.5)))
(constraint (g 2.43))
(check-synth)
