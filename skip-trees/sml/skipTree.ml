signature DIVTREE =
sig
    type 'a divtree
    val empty : 'a divtree
    val single : 'a -> 'a divtree
    val join : 'a divtree -> 'a divtree -> 'a divtree
    val pop : 'a divtree -> ('a * 'a divtree) option
    val divide : 'a divtree -> ('a divtree * 'a divtree)
end

signature SPINE =
sig
    type 'a spine
    val empty : 'a spine
    val push : 'a -> 'a spine -> 'a spine
    val pop : 'a spine -> ('a * 'a spine) option
    val inject : 'a spine -> 'a -> 'a spine
    val eject : 'a spine -> ('a spine * 'a) option
    val splitAt : int -> 'a spine -> ('a spine * 'a spine)
    val join : 'a spine -> 'a spine -> 'a spine
end

structure ListSpine : SPINE =
struct 
type 'a spine = 'a list
val empty = []
fun push x xs = x::xs
fun pop [] = NONE
  | pop (x::xs) = SOME (x,xs)
fun inject xs x = xs@[x]
fun eject xs =
    case rev xs 
     of [] => NONE
      | y::ys => SOME (rev ys, y)
fun splitAt n xs = (List.take (xs,n), List.drop (xs,n))
fun join x y = x@y
end


functor SKIPTREE (S:SPINE) = struct

datatype 'a lspine = 
	 Leaf of ('a * 'a list * 'a lspineCont)
and 'a lspineCont =
    Lont of ((('a spine) list * 'a rspine) option) S.spine
and 'a rspine =
    Reaf of ('a rspineCont * 'a list * 'a)
and 'a rspineCont =
    Ront of (('a lspine * ('a spine) list) option) S.spine
and 'a spine = 
    Left of 'a lspine
  | Right of 'a rspine

datatype 'a skiptree = 
	 Empty
       | One of 'a
       | Two of ('a * 'a)
       | More of ('a lspine * ('a spine) list * 'a rspine)

fun lextend (Leaf (hed, tyl, Lont xs)) = Leaf (hed, tyl, Lont (S.inject xs NONE))

fun toLeft (Left x) = x
  | toLeft (Right (Reaf (Ront xs, heds, lst))) =
    case S.pop xs 
     of NONE =>
	(case heds 
	  of [] => Leaf (lst, [], Lont S.empty)
	   | (y::ys) => Leaf (y, ys@[lst], Lont S.empty))
      | SOME (NONE,ys) => lextend (toLeft (Right (Reaf (Ront ys, heds, lst))))
      | SOME (SOME (Leaf (hed, tyl, Lont ls), midl),ys) =>
	Leaf (hed, tyl, Lont (S.inject ls (SOME (midl, Reaf (Ront ys,heds,lst)))))

fun rextend (Reaf (Ront xs, heds, lst)) = Reaf (Ront (S.push NONE xs), heds, lst)

fun toRight (Right x) = x
  | toRight (Left (Leaf (hed, tyl, Lont xs))) =
    case S.eject xs 
     of NONE =>
	(case rev tyl 
	  of [] => Reaf (Ront S.empty, [], hed)
	   | (y::ys) => Reaf (Ront S.empty, hed::(rev ys), y))
      | SOME (ys,NONE) => rextend (toRight (Left (Leaf (hed, tyl, Lont ys))))
      | SOME (ys,SOME (midl,Reaf (Ront rs, heds, lst))) =>
	Reaf (Ront (S.push (SOME (Leaf (hed, tyl, Lont ys),midl)) rs), heds, lst)

fun splitNode xs =
    let val n = Int.quot (length xs,2) (* TODO: this is not a fair split -- odd always round down *)
    in let val (p,q) = (List.take (xs,n), List.drop (xs,n))
       in let val p = case rev p 
		       of [] => NONE
			| y::ys => SOME (rev ys, toRight y)
	  in let val q = case q 
			  of [] => NONE
			   | y::ys => SOME (toLeft y, ys)
	     in (p,q)
	     end
	  end			  
       end 
    end

fun pushLeftTreeH (~1) _ ys = ys
  | pushLeftTreeH 0 s ys =
    (case S.pop ys 
      of NONE => S.push (SOME ([],s)) S.empty
       | SOME (NONE,ys) => S.push (SOME ([],s)) ys
       | SOME (SOME (midl,lst),ys) => S.push (SOME (Right s::midl,lst)) ys)
  | pushLeftTreeH n (s as (Reaf (Ront xs,heds,lst))) ys =
    (case S.pop ys 
      of NONE => S.push NONE (pushLeftTreeH (n-1) (Reaf (Ront (S.push NONE xs),heds,lst)) S.empty)
       | SOME (NONE,ys) => S.push NONE (pushLeftTreeH (n-1) (Reaf (Ront (S.push NONE xs),heds,lst)) ys)
       | SOME (SOME (midl,fin),ys) => 
	 let val (p,q) = splitNode (Right s::midl)
	 in case fin 
	     of Reaf (Ront fxs, fhd, ftl) =>
		S.push p (pushLeftTreeH (n-1) (Reaf (Ront (S.push q fxs),fhd,ftl)) ys)
	 end)
	
fun splitLeaf xs =
    let val n = Int.quot (length xs,2) (* TODO: not even, odds round down *)
    in let val (p,q) = (List.take (xs,n), List.drop (xs,n))
       in let val p = case p 
		       of y::ys => (y,ys)
	  in let val q = case rev q 
			  of y::ys => (rev ys,y)
	     in (p,q)
	     end
	  end			  
       end 
    end
    

(* push a singlular value onto a left spine with the given height *)
fun pushLeftH 0 x (Leaf (hed,tyl,Lont ys)) = Leaf (x,hed::tyl,Lont ys)
  | pushLeftH n x (Leaf (hed,tyl,Lont ys)) = 
    let val ((p,ps),(qs,q)) = splitLeaf (x::hed::tyl)
    in Leaf (p,ps,Lont (pushLeftTreeH (n-1) (Reaf (Ront S.empty, qs, q)) ys))
    end
	    
end


structure what = SKIPTREE(ListSpine);
