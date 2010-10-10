import qualified Data.Sequence as S
import qualified Data.List as L
import qualified Monad as M

type Deque = S.Seq
             
data Rest a b = R1 b
              | R2 a b
              | R3 a a b 
              | R4 a a a b deriving (Show)

data Lest a b = L1 a
              | L2 a b
              | L3 a b b 
              | L4 a b b b deriving (Show)

-- TODO: is R4 necessary?

data LSpine a = LSpine (Deque (Rest (Spine a) (RSpine a, a))) deriving (Show)
data RSpine a = RSpine (Deque (Lest (a, LSpine a) (Spine a))) deriving (Show)
type Spine a = Either (a,LSpine a) (RSpine a, a)

-- TODO: will rview force the root node? Perhaps make Rest and Lest smaller, and include the opposing spine in the constructor

data LConc a = LEmpty
             | LConc a (LSpine a) deriving (Show)
data RConc a = REmpty
             | RConc (RSpine a) a deriving (Show)

toLspine :: (RSpine a, a) -> (a,LSpine a)
toLspine (RSpine xs,d) =
    case S.viewl xs of
      S.EmptyL -> (d,LSpine S.empty)
      y S.:< ys ->
          case y of
            L1 (v1,LSpine x1) ->  (v1,LSpine (x1 S.|> (R1 (RSpine ys, d))))
            L2 (v1,LSpine x1) xv2 ->  (v1,LSpine (x1 S.|> (R2 xv2 (RSpine ys, d))))
            L3 (v1,LSpine x1) xv2 xv3 ->  (v1,LSpine (x1 S.|> (R3 xv2 xv3 (RSpine ys, d))))
            L4 (v1,LSpine x1) xv2 xv3 xv4 ->  (v1,LSpine (x1 S.|> (R4 xv2 xv3 xv4 (RSpine ys, d))))

toRspine :: (a,LSpine a) -> (RSpine a,a)
toRspine (d,LSpine xs) =
    case S.viewr xs of
      S.EmptyR -> (RSpine S.empty,d)
      ys S.:> y ->
          case y of
            R1 (RSpine x1,v1) ->  (RSpine ((L1 (d,LSpine ys)) S.<| x1),v1)
            R2 xv2 (RSpine x1,v1) ->  (RSpine ((L2 (d,LSpine ys) xv2) S.<| x1),v1)
            R3 xv3 xv2 (RSpine x1,v1) ->  (RSpine ((L3 (d,LSpine ys) xv3 xv2) S.<| x1),v1)
            R4 xv4 xv3 xv2 (RSpine x1,v1) ->  (RSpine ((L4 (d,LSpine ys) xv4 xv3 xv2) S.<| x1),v1)

forceLspine (Left x) = x
forceLspine (Right x) = toLspine x

forceRspine (Left x) = toRspine x
forceRspine (Right x) = x

ldivide :: LConc a -> (LConc a, RConc a)
ldivide LEmpty = (LEmpty, REmpty)
ldivide x@(LConc d (LSpine xs)) =
    case S.viewr xs of
      S.EmptyR -> (x, REmpty)
      ys S.:> y ->
          case y of
            R1 (zs,v) -> (LConc d (LSpine ys), RConc zs v)
            R2 zvs3 (RSpine zs4,v4) -> (LConc d (LSpine (ys S.|> (R1 (forceRspine zvs3)))), RConc (RSpine zs4) v4)
            R3 zvs2 zvs3 (RSpine zs4,v4) -> (LConc d (LSpine (ys S.|> (R1 (forceRspine zvs2)))), RConc (RSpine ((L1 (forceLspine zvs3)) S.<| zs4)) v4)
            R4 zvs1 zvs2 zvs3 (RSpine zs4,v4) -> (LConc d (LSpine (ys S.|> (R2 zvs1 (forceRspine zvs2)))), RConc (RSpine ((L1 (forceLspine zvs3)) S.<| zs4)) v4)

approxSplitSameType x =
    let (a,b) = ldivide x
    in (a, toLConc b)

lpush :: Spine a -> LSpine a -> LSpine a -- w -> x -> y : w:a, x:[a,b], y:[a,(b or b+1)]
lpush x (LSpine xs) =
    case S.viewl xs of
      S.EmptyL -> LSpine ((R1 (forceRspine x)) S.<| S.empty)
      y S.:< ys -> 
          case y of
            R1 c -> LSpine ((R2 x c) S.<| ys)
            R2 c d -> LSpine ((R3 x c d) S.<| ys)
            R3 c d e -> LSpine ((R4 x c d e) S.<| ys)
            R4 c d e (RSpine f,fv) -> 
                let d' = forceLspine d
                    c' = forceRspine c
                    LSpine zs = lpush (Right (RSpine ((L2 d' e) S.<| f),fv)) (LSpine ys)
                in LSpine ((R2 x c') S.<| zs)

lview :: LSpine a -> Maybe (Spine a,LSpine a) -- w -> ((x,y),z) : w:[a,b+1], x:a, z:[a,(b or b+1)]
lview (LSpine xs) = -- xs : [a,b+1]
    case S.viewl xs of
      S.EmptyL -> Nothing
      y S.:< ys -> -- y: a, ys:[a+1,b+1]
          case y of
            R1 z -> -- z: a
                case lview (LSpine ys) of
                  Nothing -> Just (Right z,LSpine S.empty)
                  Just (qqv,LSpine qs) -> -- q:a+1 , qs:[a+1,(b+1 or b)]
                      let (RSpine q,qv) = forceRspine qqv in
                      case S.viewl q of
                        S.EmptyL -> Just (Right z, LSpine ((R1 (RSpine q,qv)) S.<| qs))
                        r S.:< rs -> -- r:a+1, rs:a
                            case r of -- c,d,e,f: a
                              L1 c -> Just (Right z, LSpine ((R2 (Left c) (RSpine rs, qv)) S.<| qs))
                              L2 c d -> Just (Right z, LSpine ((R3 (Left c) d (RSpine rs, qv)) S.<| qs))
                              L3 c d e -> Just (Right z, LSpine ((R4 (Left c) d e (RSpine rs, qv)) S.<| qs))
                              L4 c d e f -> 
                                  let LSpine zs = lpush (Right (RSpine ((L2 (forceLspine e) f) S.<| rs),qv)) (LSpine qs)
                                  in Just (Right z, LSpine ((R2 (Left c) (forceRspine d)) S.<| zs))
            R2 b c -> Just (b, LSpine ((R1 c) S.<| ys))
            R3 b c d -> Just (b, LSpine ((R2 c d) S.<| ys))
            R4 b c d e-> Just (b, LSpine ((R3 c d e) S.<| ys))

ltail :: LConc a -> Maybe (a,LConc a)
ltail LEmpty = Nothing
ltail (LConc x xs) = 
    case lview xs of
      Nothing -> Just (x,LEmpty)
      Just (yv,ys) -> 
          case yv of
            Left (y,_) -> Just (x,LConc y ys)
            Right (_,y) -> Just (x,LConc y ys)

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
            R1 z1 -> LSpine ((R2 (Right x) z1) S.<| ys)
            R2 z1 z2 -> LSpine ((R3 (Right x) z1 z2) S.<| ys)
            R3 z1 z2 z3 -> LSpine ((R4 (Right x) z1 z2 z3) S.<| ys)
            R4 z1 z2 z3 z4 -> 
               let LSpine zs = lconsRspine (bothRs (forceRspine z3) z4) (LSpine ys)
               in LSpine ((R3 (Right x) z1 (forceRspine z2)) S.<| zs)

bothRs :: (RSpine a, a) -> (RSpine a, a) -> (RSpine a, a)
bothRs x (RSpine ys, d) =
    let z = toLspine x
    in (RSpine ((L1 z) S.<| ys),d)

restConcatMap f (R1 x) = f (Right x)
restConcatMap f (R2 x y) = f x ++ f (Right y)
restConcatMap f (R3 x y z) = f x ++ f y ++ f (Right z)
restConcatMap f (R4 x y z w) = f x ++ f y ++ f z ++ f (Right w)

lestConcatMap f (L1 x) = f (Left x)
lestConcatMap f (L2 x y) = f (Left x) ++ f y
lestConcatMap f (L3 x y z) = f (Left x) ++ f y ++ f z
lestConcatMap f (L4 x y z w) = f (Left x) ++ f y ++ f z ++ f w

toListLspine (LSpine xs) =
    let restExtract = restConcatMap toListSpine
        ys = concatMap restExtract $ stoList xs
    in ys

toListRspine (RSpine xs) =
    let lestExtract = lestConcatMap toListSpine
        ys = concatMap lestExtract $ stoList xs
    in ys

toListSpine (Left (d,x)) = d:(toListLspine x)
toListSpine (Right (x,d)) = (toListRspine x)++[d]
        
stoList xs =
    case S.viewl xs of
      S.EmptyL -> []
      y S.:< ys -> y:(stoList ys)

toLConc REmpty = LEmpty
toLConc (RConc a b) =
    let (c,d) = toLspine (a,b)
    in LConc c d

toList :: LConc a -> [a]
toList LEmpty = []
toList (LConc d xs) = d :(toListLspine xs)

fromList [] = LEmpty
fromList (x:xs) = lcons x (fromList xs)

bug1 n = and [[1..i] == (toList $ fromList [1..i]) | i <- [1..(max 68 n)]]
test1 = bug1
test2 n = and [(splitToList $ fromList [1..i]) | i <- [1..(max 68 n)]]
splitToList x =
    let (p,q) = ldivide x
        q' = toLConc q
        small x = length (toList x) <= 1
    in if toList x == toList p ++ (toList q')
       then (small p || splitToList p) && 
            (small q' || splitToList q')
       else error (show x)
test3 n = and [(sizeDiff $ fromList [1..i]) | i <- [1..n]]
sizeDiff LEmpty = True
sizeDiff x =
    let (p,q') = ldivide x
        q = toLConc q'
        (r,s) = (toList p,toList q)
        (t,u) = (fromIntegral $ length r, fromIntegral $ length s)
        small x = x <= 1
    in if (t+2)**(5/2) > u && (u+2)**(5/2) > t
       then 
           (small t || sizeDiff p) && 
           (small u || sizeDiff q)
       else error (show (t,u,p,q,x))


mtoList = L.unfoldr ltail

test4 n = and [[1..i] == (mtoList $ fromList [1..i]) | i <- [1..(max 68 n)]]
test5 n = and [(splitToList' $ fromList [1..i]) | i <- [1..(max 68 n)]]
splitToList' x =
    let (p,q) = ldivide x
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
            R2 ps (qs,_) ->
                case (spineDepth 0 ps, rspineDepth 0 qs) of
                  (Just i, Just j) -> if depthClose [i,j,n]
                                      then lspineDepth (n+1) (LSpine xs)
                                      else Nothing
                  _ -> Nothing
            R3 ps qs (rs,_) ->
                case (spineDepth 0 ps, spineDepth 0 qs, rspineDepth 0 rs) of
                  (Just i, Just j, Just k) -> 
                      if depthClose [i,j,k,n]
                      then lspineDepth (n+1) (LSpine xs)
                      else Nothing
                  _ -> Nothing
            R4 ps qs rs (ss,_) ->
                case (spineDepth 0 ps, spineDepth 0 qs, spineDepth 0 rs, rspineDepth 0 ss) of
                  (Just i, Just j, Just k, Just l) -> 
                      if depthClose [i,j,k,l,n]
                      then lspineDepth (n+1) (LSpine xs)
                      else Nothing
                  _ -> Nothing

spineDepth n (Left (_,x)) = lspineDepth n x
spineDepth n (Right (x,_)) = rspineDepth n x

rspineDepth n (RSpine d) =
    case S.viewr d of
      S.EmptyR -> Just 0
      xs S.:> x -> fmap (1+) $
          case x of 
            L1 (_,ps) -> 
                case lspineDepth 0 ps of
                  Nothing -> Nothing
                  Just m -> if depthClose [n,m]
                            then rspineDepth (n+1) (RSpine xs)
                            else Nothing
            L2 (_,ps) qs ->
                case (lspineDepth 0 ps, spineDepth 0 qs) of
                  (Just i, Just j) -> if depthClose [i,j,n]
                                      then rspineDepth (n+1) (RSpine xs)
                                      else Nothing
                  _ -> Nothing
            L3 (_,ps) qs rs ->
                case (lspineDepth 0 ps, spineDepth 0 qs, spineDepth 0 rs) of
                  (Just i, Just j, Just k) -> 
                      if depthClose [i,j,k,n]
                      then rspineDepth (n+1) (RSpine xs)
                      else Nothing
                  _ -> Nothing
            L4 (_,ps) qs rs ss ->
                case (lspineDepth 0 ps, spineDepth 0 qs, spineDepth 0 rs, spineDepth 0 ss) of
                  (Just i, Just j, Just k, Just l) -> 
                      if depthClose [i,j,k,l,n]
                      then rspineDepth (n+1) (RSpine xs)
                      else Nothing
                  _ -> Nothing

test6 n = and [sameDepth (fromList [1..i]) | i <- [1..n]]
test7 n = and [pairDepth (fromList [1..i]) | i <- [1..n]]
pairDepth LEmpty = True
pairDepth x =
    let (p,q) = ldivide x
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

test10 n = 
    let (w,x,y,z) = L.unzip4 [(sizeDiffVal $ fromList [1..i]) | i <- [1..n]]
    in ((sum w)/(fromIntegral n),
        (sum x)/(fromIntegral n),
        L.maximum y,
        L.maximum z
       )

sizeDiffVal LEmpty = (1,1,(1,1),(1,1))
sizeDiffVal x =
    let (p,q') = ldivide x
        q = toLConc q'
        (r,s) = (toList p,toList q)
        (t,u) = (fromIntegral $ length r, fromIntegral $ length s)
        t' = max t u
        u' = min t u
    in (log (t'+2) / log (u'+2),
            (t'+2)/(u'+2),
        (log (t'+2) / log (u'+2),t+u),
            ((t'+2)/(u'+2),t+u))

joinSmall :: (a,LSpine a) -> (a,LSpine a) -> (a,LSpine a)
joinSmall (b,LSpine c) d = (b,LSpine (c S.|> (R1 (toRspine d))))

smallOne = (1,LSpine S.empty)

joinBig :: (a,LSpine a) -> (a,LSpine a) -> (a,LSpine a) -> (a,LSpine a) -> (a,LSpine a) -> (a,LSpine a)
joinBig (b,LSpine c) d e f g = (b,LSpine (c S.|> (R4 (Left d) (Left e) (Left f) (toRspine g))))

verySmall 0 = smallOne
verySmall n = 
    let x = verySmall (n-1)
    in joinSmall x x

veryBig 0 = smallOne
veryBig n = 
    let x = veryBig (n-1)
    in joinBig x x x x x

llconc (a,b) = LConc a b

test11 = sizeDiffVal $ llconc $ joinSmall (veryBig 8) (verySmall 8)