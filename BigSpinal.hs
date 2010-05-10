import qualified Data.Sequence as S
import qualified Data.List as L
import qualified Monad as M

type Deque = S.Seq
             
data Rest a = R1 a
            | R2 a a
            | R3 a a a 
            | R4 a a a a deriving (Show)

-- TODO: is R4 necessary?

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
            R1 (zs,v) -> (LConc d (LSpine ys), RConc zs v)
            R2 zvs1 (zs2,v2) -> (LConc d (LSpine (ys S.|> (R1 zvs1))), RConc zs2 v2)
            R3 zvs1 zvs2 (zs3,v3) -> (LConc d (LSpine (ys S.|> (R2 zvs1 zvs2))), RConc zs3 v3)
            R4 zvs1 zvs2 zvs3 (zs4,v4) -> (LConc d (LSpine (ys S.|> (R3 zvs1 zvs2 zvs3))), RConc zs4 v4)

{-
approxSplitSameType x =
    let (a,b) = lsplit x
    in (a, toLConc b)
-}

toLspine :: (RSpine a, a) -> (a,LSpine a)
toLspine (RSpine xs,d) =
    case S.viewl xs of
      S.EmptyL -> (d,LSpine S.empty)
      y S.:< ys ->
          case y of
            R1 (v1,LSpine x1) ->  (v1,LSpine (x1 S.|> (R1 (RSpine ys, d))))
            R2 (v1,LSpine x1) xv2 ->  (v1,LSpine (x1 S.|> (R2 (toRspine xv2) (RSpine ys, d))))
            R3 (v1,LSpine x1) xv2 xv3 ->  (v1,LSpine (x1 S.|> (R3 (toRspine xv2) (toRspine xv3) (RSpine ys, d))))
            R4 (v1,LSpine x1) xv2 xv3 xv4 ->  (v1,LSpine (x1 S.|> (R4 (toRspine xv2) (toRspine xv3) (toRspine xv4) (RSpine ys, d))))

toRspine :: (a,LSpine a) -> (RSpine a,a)
toRspine (d,LSpine xs) =
    case S.viewr xs of
      S.EmptyR -> (RSpine S.empty,d)
      ys S.:> y ->
          case y of
            R1 (RSpine x1,v1) ->  (RSpine ((R1 (d,LSpine ys)) S.<| x1),v1)
            R2 xv2 (RSpine x1,v1) ->  (RSpine ((R2 (d,LSpine ys) (toLspine xv2)) S.<| x1),v1)
            R3 xv3 xv2 (RSpine x1,v1) ->  (RSpine ((R3 (d,LSpine ys) (toLspine xv3) (toLspine xv2)) S.<| x1),v1)
            R4 xv4 xv3 xv2 (RSpine x1,v1) ->  (RSpine ((R4 (d,LSpine ys) (toLspine xv4) (toLspine xv3) (toLspine xv2)) S.<| x1),v1)

lview :: LSpine a -> Maybe ((RSpine a, a),LSpine a) -- w -> ((x,y),z) : w:[a,b+1], x:a, z:[a,(b or b+1)]
lview (LSpine xs) = -- xs : [a,b+1]
    case S.viewl xs of
      S.EmptyL -> Nothing
      y S.:< ys -> -- y: a, ys:[a+1,b+1]
          case y of
            R1 z -> -- z: a
                case lview (LSpine ys) of
                  Nothing -> Just (z,LSpine S.empty)
                  Just ((RSpine q,qv),LSpine qs) -> -- q:a+1 , qs:[a+1,(b+1 or b)]
                      case S.viewl q of
                        S.EmptyL -> Just (z, LSpine ((R1 (RSpine q,qv)) S.<| qs))
                        r S.:< rs -> -- r:a+1, rs:a
                            case r of -- c,d,e,f: a
                              R1 c -> Just (z, LSpine ((R2 (toRspine c) (RSpine rs, qv)) S.<| qs))
                              R2 c d -> Just (z, LSpine ((R3 (toRspine c) (toRspine d) (RSpine rs, qv)) S.<| qs))
                              R3 c d e -> Just (z, LSpine ((R4 (toRspine c) (toRspine d) (toRspine e) (RSpine rs, qv)) S.<| qs))
                              R4 c d e f -> 
                                  let LSpine zs = lpush (RSpine ((R2 e f) S.<| rs),qv) (LSpine qs)
                                  in Just (z, LSpine ((R2 (toRspine c) (toRspine d)) S.<| zs))
            R2 b c -> Just (b, LSpine ((R1 c) S.<| ys))
            R3 b c d -> Just (b, LSpine ((R2 c d) S.<| ys))
            R4 b c d e-> Just (b, LSpine ((R3 c d e) S.<| ys))

{-
lSpineTail x = 
    case lview x of
      Nothing -> Nothing
      Just (_,y) -> y
-}

ltail :: LConc a -> Maybe (a,LConc a)
ltail LEmpty = Nothing
ltail (LConc x xs) = 
    case lview xs of
      Nothing -> Just (x,LEmpty)
      Just ((_,y),ys) -> Just (x,LConc y ys)


lpush :: (RSpine a, a) -> LSpine a -> LSpine a -- w -> x -> y : w:a, x:[a,b], y:[a,(b or b+1)]
lpush x (LSpine xs) =
    case S.viewl xs of
      S.EmptyL -> LSpine ((R1 x) S.<| S.empty)
      y S.:< ys -> 
          case y of
            R1 c -> LSpine ((R2 x c) S.<| ys)
            R2 c d -> LSpine ((R3 x c d) S.<| ys)
            R3 c d e -> LSpine ((R4 x c d e) S.<| ys)
            R4 c d e (RSpine f,fv) -> 
                let d' = toLspine d
                    e' = toLspine e
                    LSpine zs = lpush (RSpine ((R2 d' e') S.<| f),fv) (LSpine ys)
                in LSpine ((R2 x c) S.<| zs)


{-
lsconc :: LSpine a -> LConc a
lsconc (LSpine xs) =
    case S.viewl xs of
      S.EmptyL -> LEmpty
      y S.:< ys -> 
          case y of {-
            R1 (ps,p) -> let (q,LSpine qs) = toLspine (ps,p)
                         in LConc q (LSpine (qs S.>< ys)) -- TODO: bug here -}

            R1 (ps,p) -> let (q,LSpine qs) = toLspine (ps,p)
                         in case lsconc (LSpine ys) of
                              LEmpty -> LConc q (LSpine qs)
                              LConc r (LSpine rs) -> LConc q (LSpine ((qs S.|> (R1 (RSpine S.empty,r))) S.>< rs)) -- TODO: bug here
-}{-
            R1 (ps,p) -> let (q,LSpine qs) = toLspine (ps,p)
                         in case S.viewl ys of
                              S.EmptyL -> LConc q (LSpine qs)
                              (rr,rv) S.:< rs ->
                                  case toListRspine r
                                  case lsconc (LSpine rs) of
                              LEmpty -> LConc q (LSpine qs)
                              LConc r (LSpine rs) -> LConc q (LSpine ((qs S.|> (R1 (RSpine S.empty,r))) S.>< rs)) -- TODO: bug here
            R2 (ps,p) qsq -> let (q,LSpine qs) = toLspine (ps,p)
                             in LConc q (LSpine ((qs S.|> (R1 qsq)) S.>< ys))
            R3 (ps,p) qsq rsr -> let (q,LSpine qs) = toLspine (ps,p)
                                 in LConc q (LSpine ((qs S.|> (R2 qsq rsr)) S.>< ys))
            R4 (ps,p) qsq rsr sss -> let (q,LSpine qs) = toLspine (ps,p)
                                     in LConc q (LSpine ((qs S.|> (R3 qsq rsr sss)) S.>< ys))


lspine
-}

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
            R1 z1 -> LSpine ((R2 x z1) S.<| ys)
            R2 z1 z2 -> LSpine ((R3 x z1 z2) S.<| ys)
            R3 z1 z2 z3 -> LSpine ((R4 x z1 z2 z3) S.<| ys)
            R4 z1 z2 z3 z4 -> 
               let LSpine zs = lconsRspine (bothRs z3 z4) (LSpine ys)
               in LSpine ((R3 x z1 z2) S.<| zs)

bothRs :: (RSpine a, a) -> (RSpine a, a) -> (RSpine a, a)
bothRs x (RSpine ys, d) =
    let z = toLspine x
    in (RSpine ((R1 z) S.<| ys),d)


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

restConcatMap f (R1 x) = f x
restConcatMap f (R2 x y) = f x ++ f y
restConcatMap f (R3 x y z) = f x ++ f y ++ f z
restConcatMap f (R4 x y z w) = f x ++ f y ++ f z ++ f w
        
stoList xs =
    case S.viewl xs of
      S.EmptyL -> []
      y S.:< ys -> y:(stoList ys)

fromList [] = LEmpty
fromList (x:xs) = lcons x (fromList xs)

bug1 n = and [[1..i] == (toList $ fromList [1..i]) | i <- [1..(max 68 n)]]
test1 = bug1
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
    in if (t+2)^3 > u && (u+2)^3 > t
       then 
           (small t || sizeDiff p) && 
           (small u || sizeDiff q)
       else error (show (t,u,p,q,x))

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

lconcDepth LEmpty = Just 0
lconcDepth (LConc _ xs) = fmap (+1) $ lspineDepth 0 xs

sameDepth LEmpty = True
sameDepth (LConc _ xs) = 
    case lspineDepth 0 xs of
      Nothing -> False
      Just _ -> True

depthClose [] = True
depthClose (x:xs) = depthClose' x xs

depthClose' x [] = True
depthClose' x (y:ys) = if x == y
                       then depthClose' x ys
                       else x+2 >y && y+2 > x && depthClose'' x y ys

depthClose'' _ _ [] = True
depthClose'' x y (z:zs) = (z==x || z==y) && (depthClose'' x y zs)

lspineDepth n (LSpine d) =
    case S.viewl d of
      S.EmptyL -> Just 0
      x S.:< xs -> fmap (1+) $
          case x of 
            R1 (ps,_) -> 
                case rspineDepth 0 ps of
                  Nothing -> Nothing
                  Just m -> if depthClose [m,n]
                            then lspineDepth (n+1) (LSpine xs)
                            else Nothing
            R2 (ps,_) (qs,_) ->
                case (rspineDepth 0 ps, rspineDepth 0 qs) of
                  (Just i, Just j) -> if depthClose [i,j,n]
                                      then lspineDepth (n+1) (LSpine xs)
                                      else Nothing
                  _ -> Nothing
            R3 (ps,_) (qs,_) (rs,_) ->
                case (rspineDepth 0 ps, rspineDepth 0 qs, rspineDepth 0 rs) of
                  (Just i, Just j, Just k) -> 
                      if depthClose [i,j,k,n]
                      then lspineDepth (n+1) (LSpine xs)
                      else Nothing
                  _ -> Nothing
            R4 (ps,_) (qs,_) (rs,_) (ss,_) ->
                case (rspineDepth 0 ps, rspineDepth 0 qs, rspineDepth 0 rs, rspineDepth 0 ss) of
                  (Just i, Just j, Just k, Just l) -> 
                      if depthClose [i,j,k,l,n]
                      then lspineDepth (n+1) (LSpine xs)
                      else Nothing
                  _ -> Nothing

rspineDepth n (RSpine d) =
    case S.viewr d of
      S.EmptyR -> Just 0
      xs S.:> x -> fmap (1+) $
          case x of 
            R1 (_,ps) -> 
                case lspineDepth 0 ps of
                  Nothing -> Nothing
                  Just m -> if depthClose [n,m]
                            then rspineDepth (n+1) (RSpine xs)
                            else Nothing
            R2 (_,ps) (_,qs) ->
                case (lspineDepth 0 ps, lspineDepth 0 qs) of
                  (Just i, Just j) -> if depthClose [i,j,n]
                                      then rspineDepth (n+1) (RSpine xs)
                                      else Nothing
                  _ -> Nothing
            R3 (_,ps) (_,qs) (_,rs) ->
                case (lspineDepth 0 ps, lspineDepth 0 qs, lspineDepth 0 rs) of
                  (Just i, Just j, Just k) -> 
                      if depthClose [i,j,k,n]
                      then rspineDepth (n+1) (RSpine xs)
                      else Nothing
                  _ -> Nothing
            R4 (_,ps) (_,qs) (_,rs) (_,ss) ->
                case (lspineDepth 0 ps, lspineDepth 0 qs, lspineDepth 0 rs, lspineDepth 0 ss) of
                  (Just i, Just j, Just k, Just l) -> 
                      if depthClose [i,j,k,l,n]
                      then rspineDepth (n+1) (RSpine xs)
                      else Nothing
                  _ -> Nothing

test6 n = and [sameDepth (fromList [1..i]) | i <- [1..n]]
test7 n = and [pairDepth (fromList [1..i]) | i <- [1..n]]
pairDepth LEmpty = True
pairDepth x =
    let (p,q) = lsplit x
        q' = toLConc q
        small x = length (toList x) <= 1
    in case (lconcDepth p, lconcDepth q') of
         (Just pn, Just qn) ->
             if pn +2 > qn && qn+2>pn
             then (small p || splitToList p) && 
                  (small q' || splitToList q')
             else error (show (x,pn,qn))
         z -> error (show (x,p,q',z))

test8 n = and [alltails sameDepth (fromList [1..i]) | i <- [1..n]]
alltails :: (LConc a -> Bool) -> LConc a -> Bool
alltails f xs = f xs &&
    case ltail xs of
      Nothing -> True
      Just (_,ys) -> alltails f ys

bug2 = test8 5

test9 n = and [alltails sizeDiff (fromList [1..i]) | i <- [1..n]] 

bug3 = test9 50

bug4 = test8 6
