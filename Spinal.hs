import Data.Sequence as S

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
