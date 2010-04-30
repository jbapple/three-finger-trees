import qualified Data.Sequence as S
import qualified Data.List as L

type Deque = S.Seq

data Digit a = D1 a
             | D2 a a
             | D3 a a a
             | D4 a a a a deriving (Show)
               
data Rest a = R0
            | R1 a
            | R2 a a
            | R3 a a a deriving (Show)

data LSpine a = LSpine (Deque (Rest (RSpine a, Digit a))) deriving (Show)
data RSpine a = RSpine (Deque (Rest (LSpine a, Digit a))) deriving (Show)

data LConc a = LEmpty
             | LConc (Digit a) (LSpine a) deriving (Show)
data RConc a = REmpty
             | RConc (Digit a) (RSpine a) deriving (Show)

lsplit :: LConc a -> (LConc a, RConc a)
lsplit LEmpty = (LEmpty, REmpty)
lsplit x@(LConc d (LSpine xs)) =
    case S.viewr xs of
      S.EmptyR -> (x, REmpty)
      ys S.:> y ->
          case y of
            R0 -> lsplit (LConc d (LSpine ys))
            R1 (zs,v) -> (LConc d (LSpine ys), RConc v zs)
            R2 (zs1,v1) (zs2,v2) -> (LConc d (LSpine (ys S.|> (R1 (zs1,v1)))), RConc v2 zs2)
            R3 (zs1,v1) (zs2,v2) (zs3,v3)-> (LConc d (LSpine (ys S.|> (R2 (zs1,v1) (zs2,v2)))), RConc v3 zs3)

lcons :: a -> LConc a -> LConc a
lcons x LEmpty = LConc (D1 x) (LSpine S.empty)
lcons x xs@(LConc d r) =
    case d of
      D1 y1 -> LConc (D2 x y1) r
      D2 y1 y2 -> LConc (D3 x y1 y2) r
      D3 y1 y2 y3 -> LConc (D4 x y1 y2 y3) r
      D4 y1 y2 y3 y4 -> LConc (D2 x y1) (lconsDigit (D3 y2 y3 y4) r)

lconsDigit :: Digit a -> LSpine a -> LSpine a
lconsDigit d = lconsRspine (RSpine S.empty,d)

lconsRspine :: (RSpine a,Digit a) -> LSpine a -> LSpine a
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

bothRs :: (RSpine a, Digit a) -> (RSpine a, Digit a) -> (RSpine a, Digit a)
bothRs x (RSpine ys, d) =
    let z = toLspine x
    in (RSpine ((R1 z) S.<| ys),d)

toLspine :: (RSpine a,Digit a) -> (LSpine a,Digit a)
toLspine (RSpine xs,d) =
    case S.viewl xs of
      S.EmptyL -> (LSpine S.empty,d)
      y S.:< ys ->
          case y of
            R0 -> toLspine (RSpine ys,d)
            R1 (LSpine x1,v1) ->  (LSpine ((R1 (RSpine ys, d)) S.<| x1),v1)
            R2 (LSpine x1,v1) xv2 ->  (LSpine ((R1 (RSpine ((R1 xv2) S.<| ys), d)) S.<| x1),v1)
            R3 (LSpine x1,v1) xv2 xv3 ->  (LSpine ((R1 (RSpine ((R2 xv2 xv3) S.<| ys), d)) S.<| x1),v1)

toList :: LConc a -> [a]
toList LEmpty = []
toList (LConc d xs) = toListDigit' d (toListLspine xs)

toListDigit' (D1 p) xs = p:xs
toListDigit' (D2 p q) xs = p:q:xs
toListDigit' (D3 p q r) xs = p:q:r:xs
toListDigit' (D4 p q r s) xs = p:q:r:s:xs

toListLspine (LSpine xs) =
    let extract (r,d) = (toListRspine r) ++ (toListDigit' d [])
        restExtract = restConcatMap extract
        ys = concatMap restExtract $ stoList xs
    in ys

toListRspine (RSpine xs) =
    let extract (l,d) = toListDigit' d (toListLspine l)
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

{-
(\x -> [1..x] == (toList $ fromList [1..x])) 68
-}

bug1 = LConc (D4 1 2 3 4) 
           (LSpine (S.fromList [R3 (RSpine (S.fromList []),D3 5 6 7) 
                                (RSpine (S.fromList []),D3 8 9 10) 
                                (RSpine (S.fromList []),D3 11 12 13),
                                R3 (RSpine (S.fromList [R1 (LSpine (S.fromList []),
                                                            D3 14 15 16)]),
                                    D3 17 18 19) 
                                       (RSpine (S.fromList [R1 (LSpine (S.fromList []),D3 20 21 22)]),
                                               D3 23 24 25) 
                                       (RSpine (S.fromList [R1 (LSpine (S.fromList []),D3 26 27 28)]),D3 29 30 31),
                                R3 (RSpine (S.fromList [R1 (LSpine (S.fromList [R1 (RSpine (S.fromList []),D3 35 36 37)]),D3 32 33 34),
                                                           R1 (LSpine (S.fromList []),D3 38 39 40)]),D3 41 42 43) 
                                       (RSpine (S.fromList [R1 (LSpine (S.fromList [R1 (RSpine (S.fromList []),D3 47 48 49)]),D3 44 45 46),
                                                               R1 (LSpine (S.fromList []),D3 50 51 52)]),D3 53 54 55) 
                                       (RSpine (S.fromList [R1 (LSpine (S.fromList [R1 (RSpine (S.fromList []),D3 59 60 61)]),D3 56 57 58),
                                                               R1 (LSpine (S.fromList []),D3 62 63 64)]),D3 65 66 67)]))

