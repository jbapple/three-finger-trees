import Control.Monad
import Data.Bits
import Data.List
import Data.Maybe

data Tree k v = Empty
              | Full (Full k v) deriving (Show)

type Nat = Int

data Full k v = One k v
              | More Nat [(Full k v,k)] deriving (Show)


{-

A 3B tree inspired by B+ trees and trees of bounded balance, is defined for an alpha > 3 as follows:

A tree may be empty, or a leaf, or an n-ary branch, where n is unconstrained.
An n-ary branch has n pointers to 3B trees (its children) and n pointers to leaf values (the maximum in each child).
It also has a natural number indicating its size.

The size of a 3B tree is defined as follows:
An empty tree has size 0
A leaf has size 1.
A branch's size is the sum of the sizes of its children.

Any tree with size n has a level l defined as follows:
level(0) = -1
level(1) = 0
level(n) = the number of digits required to represent a (n-1) with base alpha

digits(0) = 0
digits(n) = 1 + digits(floor(n/alpha))

For instance, if alpha = 4, level(2) = 1, level(4) = 1, level(5) = 2, level(16) = 2, level(17) = 3.

3B trees are constrained in level such that every child of a level n+1 tree has level n.
This ensures that every branch has no fewer than 2 and no more than alpha^2 -1 children.
If a tree had only one child, it would be the same level as that child.
If a tree had alpha^2 children, it would be at least of size alpha^2 * |smallest child|, and would therefore have level at least 2+level(smallest child).

To perform a deletion, we navigate down to the leaf and unlink it from its parent.
This can invalidate every node on the path from the root to the now-deleted leaf, because any one may have decreased in level.
To fix a branch that is the same level (n) as its children, first concatenate its child-array to the child-array of one of its siblings.
(If the branch has no siblings, it is the root. In this case, concatenate the child-arrays of its children, which is now a well-formed node)
If the combined node has the proper level, replace the pair of child pointers in their shared parent with a pointer to the new node.
Otherwise, the combined node is too large.
Split it into two groups.
Since its total size is >alpha^(n+1), but its children all have size in (alpha^(n-1),alpha^n], it can be split into two contiguous arrays each of which has size in [(alpha^(n+1) - alpha^n)/2, (alpha^(n+1) + alpha^n)/2] = [alpha^n*(alpha-1)/2,alpha^n*(alpha+1)/2] which has level n when 3<alpha.
(If the smaller half of an ideal split is less than alpha^n*(alpha-1)/2 in size, remove a tree from its neighbor.
This tree has size <= alpha^n, so the formerly smaller half has size more than alpha^n*(alpha-1)/2 but <= alpha^n*(alpha+1)/2, which is thus closer to half 


In this case, split it into alpha-1 groups, each approximately 

Divide an array of length n and measure p into m contiguous roughly equal-measure parts when no element has measure larger than k

When m = 1, exactly 1 equal-measure part
When m = 2, If larger-measure part has size > p/2+k/2, then the smaller part has size < p/2-k/2, so we can move an element from the larger part to the smaller and make them more even
When m = 3, first take off p/3 +- k/2. p - (p/3) +- k/2 is left. By above, the most any can be off if k/2, which is now (2p/3 +- k/2)/2 +- k/2, or p/3 +- 3k/4
When m = 4, the same process gives (3p/4 +- k/2)/3 +- 3k/4 = p/4 +- 11k/12
(4p/5 +- k/2)/4 +- 11k/12 = 4p/5 +- 25k/24
((m-1)p/m +- k/2)/(m-1) +- k/2 * \sum^{i=m-2} 1/i = p/m +-  k/2 * \sum^{i=m-1} 1/i
This is roughly p/m +- k/2 * lg m
Conjecture: worst case is p/m +- 2((m-1)!)
when m = 4, just divide in half twice to get 3k/4.
when m = 5, take 1 for 1/2, then 1/8 + 3/4 = 7/8
when m = 6, max(1/6+12, 1/6+3/4) = 11/12
when m = 8, divide once, each side within 1/2.



Then split the child-array as evenly as possible, producing two new branches.

-}

{-
base = 3

isLevel s l = 
    let lower = base^l
        upper = base*lower
    in lower <= s && s <= upper
-}

-- Power of 2 that is the balance factor
base = 2

levelOf :: Nat -> Nat
levelOf s = go (s-1) (-1)
    where go s r =
              if s == 0
              then r
              else go (s `shiftR` base) (1+r)

isLevel s l = l == levelOf s

splitEven total getSize accumSize accumList (x:xs) =
    let nextSize = getSize x
        nextAccumSize = accumSize + nextSize
    in if abs (accumSize*2 - total) <= abs (nextAccumSize*2 - total)
       then (More accumSize (reverse accumList), More (total-accumSize) (x:xs))
       else splitEven total getSize nextAccumSize (x:accumList) xs
splitEven _ _ s r [] = error "splitEven"

sizeOf One{} = 1
sizeOf (More s _) = s

splitFull (More s cs) = 
    let (left,rite) = splitEven s (sizeOf . fst) 0 [] cs
    in More s [(left, maxOf left),(rite, maxOf rite)]

maxOf (One k _) = k
maxOf (More _ xs) = snd $ last xs

--joinLeftChild tree maxx 

insertFull k v t@(One x _) =
    case compare k x of
      EQ -> One k v
      LT -> More 2 [(One k v,k),(t,x)]
      GT -> More 2 [(t,x),(One k v,k)]
insertFull bk bv bt =
    let noup k v t@(More s ((c,x):cs@(_:_))) =
            if k <= x
            then let c' = insertFull k v c
                     l = level c
                     l' = level c'
                 in if l' > l
                    then let More s' gs = c'
                         in  More (s+1) (gs++cs)
                    else More (s-sizeOf c+sizeOf c') ((c',maxOf c'):cs)
            else let cSize = sizeOf c 
                     More s' cs' = noup k v (More (s-cSize) cs)
                 in More (s'+cSize) ((c,x):cs')
        noup k v t@(More s [(c,x)]) =
            let c' = insertFull k v c
                cSize = sizeOf c 
                l = level c
                l' = level c'
            in if l' > l
               then c'
               else More (s-sizeOf c+sizeOf c') [(c',maxOf c')]
    in let tl = level bt
           bt' = noup bk bv bt
           tl' = level bt'
       in if tl' > tl
          then splitFull bt'
          else bt'
{-
deleteFull k v t@(One x _) = 
    case compare k x of
-}
level One{} = (-1)
level x = levelOf $ sizeOf x

insertTree k v Empty = Full (One k v)
insertTree k v (Full x) = Full (insertFull k v x)

{- 

Invariant : 

-}

levelCheck One{} = Just (-1)
levelCheck (More s cs) =
    let ls = map (levelCheck . fst) cs
        allJust (Just x:xs) = go xs
            where go [] = Just x
                  go (Just y:ys) = 
                      if x == y
                      then go ys
                      else Nothing
        allJust _ = Nothing
    in do l <- allJust ls
          guard (s `isLevel` (l+1))
          return $ l+1

levelSizes :: Full k v -> [Int]
levelSizes One{} = []
levelSizes (More _ xs) = (length xs):(concatMap (levelSizes . fst) xs)

least (One k _) = k
least (More _ (x:_)) = least $ fst x

sorted x = isJust $ go (least x) x    
    where go a (One k _) = if a <= k
                           then Just k
                           else Nothing
          go a (More _ [x]) = go a $ fst x
          go a (More s (x:xs)) = 
              do y <- go a $ fst x
                 go y (More s xs)