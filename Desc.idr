module Desc
data Desc : (0 tI : Type) -> (0 tO : tI -> Type) -> Type where
  End : (i : tI) -> tO i -> Desc tI tO
  Rec : (i : tI) -> (b : tO i -> Desc tI tO) -> Desc tI tO
  Ref : (i : tA -> tI) 
    -> ((o : (a : tA) -> tO (i a)) -> Desc tI tO) 
    -> Desc tI tO
  Arg : (tA : Type) -> (tA -> Desc tI tO) -> Desc tI tO
  
el : (d : Desc tI tO) 
  -> (tX : tI -> Type )
  -> (tY : {0 i : tI} -> tX i -> tO i)
  -> tI -> Type  
el (End j o) tX tY i = i = j
el (Rec j b) tX tY i = (x : (tX j) ** el (b (tY x)) tX tY i )
el (Ref j b) tX tY i = ( f : ((a : _) -> tX (j a)) ** el (b (\a => tY (f a))) tX tY i)
el (Arg tA b) tX tY i = (a : _ ** el (b a) tX tY i)

mutual
  data Fix : (d : Desc tI tO) -> (i : tI) -> Type where
    init : el d (Fix d) (foldO {tI = tI} d) i  -> Fix d i
    
  foldO : {0 tO : tI -> Type} -> (d : Desc tI tO) -> Fix d i -> tO i  
  foldsO : {0 tO : tI -> Type} -> (d : Desc tI tO) 
    -> (e : Desc tI tO) -> el d (Fix e) (foldO e) i
    -> tO i
    
  foldO d (init xs) = foldsO d d xs
  foldsO (End j o) e Refl = o
  foldsO (Rec j b) e (x ** xs) = foldsO (b (foldO e x)) e xs
  foldsO (Ref j b) e (f ** xs) = foldsO (b (\a => foldO e (f a))) e xs
  foldsO (Arg tA b) e (a ** xs) = foldsO (b a) e xs
