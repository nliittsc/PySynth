(set-logic PBE_SLIA)
(synth-fun f ((fname String) (lname String)) String
    ((ntString String) (ntInt Int))
    ((ntString String (fname lname " "
                       (str.++ ntString ntString)
                       (str.replace ntString ntString ntString)
                       (str.at ntString ntInt)
                       (int.to.str ntString)
                       (str.substr ntString ntInt ntInt)))
     (ntInt Int (0 1 2
                 (+ ntInt ntInt)
                 (- ntInt ntInt)
                 (str.len ntString)
                 (str.to.int ntString)
                 (str.indexof ntString ntString ntInt)))))
(constraint (= (f "Nancy" "FreeHafer") "Nancy FreeHafer"))
(constraint (= (f "Andrew" "Cencici") "Andrew Cencici"))
(constraint (= (f "Jan" "Kotas") "Jan Kotas"))
(constraint (= (f "Mariya" "Sergienko") "Mariya Sergienko"))
(check-synth)
