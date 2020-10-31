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
  -> (tY : {i : tI} -> tX i -> tO i)
  -> tI -> Type  
el (End j o) tX tY i = i = j
el (Rec j b) tX tY i = (x : (tX j) ** el (b (tY x)) tX tY i )
el (Ref j b) tX tY i = ( f : ((a : _) -> tX (j a)) ** el (b (\a => tY (f a))) tX tY i)
el (Arg tA b) tX tY i = (a : _ ** el (b a) tX tY i)

mutual
  data Fix : (0 d : Desc tI tO) -> (i : tI) -> Type where
    init : el d (Fix d) (foldO {tI = tI} d) i  -> Fix d i
    
  foldO : {0 tO : tI -> Type} -> (d : Desc tI tO) -> (1 _ : Fix d i) -> tO i  
  foldsO : {0 tO : tI -> Type} -> (1 d : Desc tI tO) 
    -> (e : Desc tI tO) -> el d (Fix e) (foldO e) i
    -> tO i
    
  foldO d (init xs) = foldsO d d xs
  foldsO (End j o) e Refl = o
  foldsO (Rec j b) e (x ** xs) = foldsO (b (foldO e x)) e xs
  foldsO (Ref j b) e (f ** xs) = foldsO (b (\a => foldO e (f a))) e xs
  foldsO (Arg tA b) e (a ** xs) = foldsO (b a) e xs


tHyps : (1 d : Desc tI tO) -> (tX : tI -> Type) -> (tY : {i : tI} -> tX i -> tO i)
  -> (p : {0 i : tI} -> tX i -> Type) -> (i : tI) -> (xs : el d tX tY i) -> Type
tHyps (End j o) tX tY p i x = ()
tHyps (Rec j d) tX tY p i (x ** xs) = (p x , tHyps (d (tY x)) tX tY p i xs)
tHyps (Ref j d) tX tY p i (f ** xs) = ((a : _) -> p (f a) , tHyps (d (\a => tY (f a))) tX tY p i xs)
tHyps (Arg tA b) tX tY p i (a ** xs) = tHyps (b a) tX tY p i xs


mutual
  ind : (d : Desc tI tO) 
        -> (0 p : {i : _} -> Fix d i -> Type )
        -> (alpha : {i : _} 
              -> (xs : el d (Fix d) (foldO d) i) 
              -> (ihs : tHyps d (Fix d) (foldO d) p i xs)
              -> (p (init {i = i} xs)))
        -> {i : tI} -> (x : Fix d i) -> (p x)
        
  hyps : (d : Desc tI tO) -> (e : Desc tI tO) 
    -> (0 p : {i : _} -> Fix e i -> Type)
    -> (alpha : {i : _} 
      -> (xs : el e (Fix e) (foldO e) i)
      -> (ihs : tHyps e (Fix e) (foldO e) p i xs)
      -> p (init {i = i} xs))
    -> {i : tI} -> (xs : el d (Fix e) (foldO e) i)
    -> tHyps d (Fix e) (foldO e) p i xs
  
  ind d p alpha (init xs) = alpha xs (hyps d d p alpha xs)
  
  hyps (End i o) e p alpha x = ()
  hyps (Rec i b) e p alpha (x ** xs) = (ind e p alpha x , hyps (b (foldO e x)) e p alpha xs)
  hyps (Ref i b) e p alpha (f ** xs) = ((\a => ind e p alpha (f a)), hyps (b (\a => foldO e (f a))) e p alpha xs )
  hyps (Arg tA b) e p alpha (a ** xs) = hyps (b a) e p alpha xs
