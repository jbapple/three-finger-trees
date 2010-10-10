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

datatype 'a midTree = 
	 Leaf of 'a list
       | Node of (int * ('a midTree) list)


type 'a nodeCont = ('a midTree) list

datatype 'a spine = Spine of ('a * 'a list * ('a nodeCont) S.spine)

datatype 'a skipTree = 
	 None
       | One of 'a list
       | Many of (int * 'a spine * ('a midTree) list * 'a spine * int)

fun midSize (Leaf xs) = length xs
  | midSize (Node (n,_)) = n

fun rightToMid (Spine (x,xs,ss)) =
    case S.eject ss 
     of NONE => 
	let val n = length xs
	in Node (n+1,[Leaf (xs@[x])])
	end
      | SOME (ss,[]) => 
	let val kid = rightToMid (Spine (x,xs,ss))
	in Node (midSize kid, [kid])
	end
      | SOME (ss,zs) =>
	let val lastKid = rightToMid (Spine (x,xs,ss))
	    val kids = (rev zs) @ [lastKid]
	    val n = foldl (Int.+) 0 (map midSize kids)
	in Node (n,kids)
	end
	
(*	


fun pushLeftTreeH 0 s ls cs rs =
    (case S.pop ls 
      of NONE => S.push (SOME ([],s)) (S.push (S.empty
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

(* push a singlular value onto a left spine with the given height *)
fun pushLeftH 0 x (Leaf (hed,tyl,ys)) = Leaf (x,hed::tyl,ys)
  | pushLeftH n x (Leaf (hed,tyl,Lont ys)) = 
    let val rst = More (1 + length tyl, map One (hed::tyl))  (*TODO: calculate length and map at same time*)
    in Leaf (x,[],pushLeftTree (n-1) rst ys)


	
    

(*
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

fun splitList xs =
    let val n = Int.quot (length xs,2) (* TODO: not an even division: odds round down *)
		(* TODO: even division is random enough? What is model of random tree? *)
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
*)
(*
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
*)
*)
	    
end


structure what = SKIPTREE(ListSpine);
