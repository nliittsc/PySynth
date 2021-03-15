(set-logic SLIA)
(synth-fun f ((_arg_0 String) (_arg_1 String)) String 
 ( (Start String (ntString)) 
 (ntString String (
	_arg_0 _arg_1
	"" " " "_"
	(str.++ ntString ntString) 
	(str.replace ntString ntString ntString) 
	(str.at ntString ntInt)
	(int.to.str ntInt)
	(ite ntBool ntString ntString)
	(str.substr ntString ntInt ntInt)
)) 
 (ntInt Int (
	
	1 0 -1
	(+ ntInt ntInt)
	(- ntInt ntInt)
	(str.len ntString)
	(str.to.int ntString)
	(ite ntBool ntInt ntInt)
	(str.indexof ntString ntString ntInt)
)) 
 (ntBool Bool (
	
	true false
	(= ntInt ntInt)
	(str.prefixof ntString ntString)
	(str.suffixof ntString ntString)
	(str.contains ntString ntString)
)) ))
(constraint (= (f "ann chang" "achang_maaker.com") "achang"))
(constraint (= (f "bobby smith" "bobt_sphynx.uk.co") "bobt"))
(constraint (= (f "art lennox" "art.lennox_svxn.com") "art.lennox"))
(check-synth)
(define-fun f_1 ((_arg_0 String) (_arg_1 String)) String (str.substr _arg_1 0 (str.indexof _arg_1 "_" 1)))
