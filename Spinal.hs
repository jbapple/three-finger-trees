import qualified Data.Sequence as S
import qualified Data.List as L

type Deque = S.Seq
             
data Rest a = R0
            | R1 a
            | R2 a a
            | R3 a a a deriving (Show)

data LSpine a = LSpine (Deque (Rest (RSpine a, a))) deriving (Show)
data RSpine a = RSpine (Deque (Rest (a, LSpine a))) deriving (Show)

data LConc a = LEmpty
             | LConc a (LSpine a) deriving (Show)
data RConc a = REmpty
             | RConc (RSpine a) a deriving (Show)

lsplit :: LConc a -> (LConc a, RConc a)
lsplit LEmpty = (LEmpty, REmpty)
lsplit x@(LConc d (LSpine xs)) =
    case S.viewr xs of
      S.EmptyR -> (x, REmpty)
      ys S.:> y ->
          case y of
            R0 -> lsplit (LConc d (LSpine ys))
            R1 (zs,v) -> (LConc d (LSpine ys), RConc zs v)
            R2 (zs1,v1) (zs2,v2) -> (LConc d (LSpine (ys S.|> (R1 (zs1,v1)))), RConc zs2 v2)
            R3 (zs1,v1) (zs2,v2) (RSpine zs3,v3)-> (LConc d (LSpine (ys S.|> (R1 (zs1,v1)))), RConc (RSpine ((R1 (toLspine (zs2,v2))) S.<| zs3)) v3)

approxSplitSameType x =
    let (a,b) = lsplit x
    in (a, toLConc b)

ltail :: LConc a -> Maybe (a,LConc a)
ltail LEmpty = Nothing
ltail (LConc x xs) = Just (x,lsconc xs)

lsconc :: LSpine a -> LConc a
lsconc (LSpine xs) =
    case S.viewl xs of
      S.EmptyL -> LEmpty
      y S.:< ys -> 
          case y of
            R0 -> lsconc (LSpine ys)
            R1 (ps,p) -> let (q,LSpine qs) = toLspine (ps,p)
                         in LConc q (LSpine (qs S.>< ys))
            R2 (ps,p) qsq -> let (q,LSpine qs) = toLspine (ps,p)
                             in LConc q (LSpine ((qs S.|> (R1 qsq)) S.>< ys))
            R3 (ps,p) qsq rsr -> let (q,LSpine qs) = toLspine (ps,p)
                                 in LConc q (LSpine ((qs S.|> (R2 qsq rsr)) S.>< ys))

lcons :: a -> LConc a -> LConc a
lcons x LEmpty = LConc x (LSpine S.empty)
lcons x xs@(LConc d r) =
    LConc x (lconsRspine (RSpine S.empty,d) r) 

lconsRspine :: (RSpine a, a) -> LSpine a -> LSpine a
lconsRspine x (LSpine xs) =
    case S.viewl xs of
      S.EmptyL -> LSpine ((R1 x) S.<| S.empty)
      y S.:< ys -> 
          case y of
            R0 -> LSpine ((R1 x) S.<| ys)
            R1 z1 -> LSpine ((R2 x z1) S.<| ys)
            R2 z1 z2 -> LSpine ((R3 x z1 z2) S.<| ys)
            R3 z1 z2 z3-> 
               let LSpine zs = lconsRspine (bothRs z2 z3) (LSpine ys)
               in LSpine ((R2 x z1) S.<| zs)

bothRs :: (RSpine a, a) -> (RSpine a, a) -> (RSpine a, a)
bothRs x (RSpine ys, d) =
    let z = toLspine x
    in (RSpine ((R1 z) S.<| ys),d)

toLspine :: (RSpine a, a) -> (a,LSpine a)
toLspine (RSpine xs,d) =
    case S.viewl xs of
      S.EmptyL -> (d,LSpine S.empty)
      y S.:< ys ->
          case y of
            R0 -> toLspine (RSpine ys,d)
            R1 (v1,LSpine x1) ->  (v1,LSpine (x1 S.|> (R1 (RSpine ys, d))))
            R2 (v1,LSpine x1) xv2 ->  (v1,LSpine (x1 S.|> (R1 (RSpine ((R1 xv2) S.<| ys), d))))
            R3 (v1,LSpine x1) xv2 xv3 ->  (v1,LSpine (x1 S.|> (R1 (RSpine ((R2 xv2 xv3) S.<| ys), d))))

toLConc REmpty = LEmpty
toLConc (RConc a b) =
    let (c,d) = toLspine (a,b)
    in LConc c d

toList :: LConc a -> [a]
toList LEmpty = []
toList (LConc d xs) = d :(toListLspine xs)

toListLspine (LSpine xs) =
    let extract (r,d) = (toListRspine r) ++ ([d])
        restExtract = restConcatMap extract
        ys = concatMap restExtract $ stoList xs
    in ys

toListRspine (RSpine xs) =
    let extract (d,l) = d:(toListLspine l)
        restExtract = restConcatMap extract
        ys = concatMap restExtract $ stoList xs
    in ys

restConcatMap _ R0 = []
restConcatMap f (R1 x) = f x
restConcatMap f (R2 x y) = f x ++ f y
restConcatMap f (R3 x y z) = f x ++ f y ++ f z
        
stoList xs =
    case S.viewl xs of
      S.EmptyL -> []
      y S.:< ys -> y:(stoList ys)

fromList [] = LEmpty
fromList (x:xs) = lcons x (fromList xs)

bug1 n = and [[1..i] == (toList $ fromList [1..i]) | i <- [1..(max 68 n)]]
test2 n = and [(splitToList $ fromList [1..i]) | i <- [1..(max 68 n)]]
splitToList x =
    let (p,q) = lsplit x
        q' = toLConc q
        small x = length (toList x) <= 1
    in if toList x == toList p ++ (toList q')
       then (small p || splitToList p) && 
            (small q' || splitToList q')
       else error (show x)
test3 n = and [(sizeDiff $ fromList [1..i]) | i <- [1..n]]
sizeDiff LEmpty = True
sizeDiff x =
    let (p,q') = lsplit x
        q = toLConc q'
        (r,s) = (toList p,toList q)
        (t,u) = (toInteger $ length r, toInteger $ length s)
        small x = x <= 1
    in if (t+2)^2 > u && (u+2)^2 > t
       then 
           (small t || sizeDiff p) && 
           (small u || sizeDiff q)
       else error (show (t,u))

mtoList = L.unfoldr ltail

test4 n = and [[1..i] == (mtoList $ fromList [1..i]) | i <- [1..(max 68 n)]]
test5 n = and [(splitToList' $ fromList [1..i]) | i <- [1..(max 68 n)]]
splitToList' x =
    let (p,q) = lsplit x
        q' = toLConc q
        small x = length (toList x) <= 1
    in if mtoList x == mtoList p ++ (mtoList q')
       then (small p || splitToList p) && 
            (small q' || splitToList q')
       else error (show x)