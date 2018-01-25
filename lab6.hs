-- Lab 6: FSM constructions for regular operators
--- Carlos Reyes


-- If two people meet and a third person walks into the meet is that a threeway???


import Data.List (nub, sort, subsequences)


-- Fixed alphabet, but everything below should work for any sigma!
sigma = "ab"

-- Finite state machines indexed by the type of their states
-- M = (states, start, final, transitions)
type FSM a = ([a], a, [a], [(a, Char, a)])


---------------- A solution to Lab 5, ported to FSM a ------------------------
  
-- no_dups xs = "xs has no duplicates"
no_dups :: Eq a => [a] -> Bool
no_dups [] = True
no_dups (x:xs) = not (elem x xs) && no_dups xs

-- subset xs ys == "xs is a subset of ys"
subset :: Eq a => [a] -> [a] -> Bool
subset [] ys = True
subset (x:xs) ys = elem x ys && subset xs ys

-- func3 as bs ts == "ts determines a function from (as x bs) to cs"
func3 :: (Eq a, Eq b, Eq c) => [a] -> [b] -> [c] -> [(a,b,c)] -> Bool
func3 as bs cs ts = and [single (thirds a b ts) cs | a <- as, b <- bs] where
  thirds a b ts = [c' | (a',b',c') <- ts, a' == a, b' == b]
  single [x] ys = elem x ys
  single _ _ = False

-- check whether a finite state machine is correct/complete:
checkFSM :: Eq a => FSM a -> Bool
checkFSM (qs, s, fs, d) = no_dups qs &&        -- (1)
                          elem s qs &&         -- (2)
                          subset fs qs &&      -- (3)
                          func3 qs sigma qs d  -- (4)

-- All functions below assume that the machine is correct

-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

delta :: Eq a => FSM a -> a -> Char -> a
delta (_, _, _, d) = ap d

delta_star :: Eq a => FSM a -> a -> [Char] -> a
delta_star = foldl . delta

accept1 :: Eq a => FSM a -> [Char] -> Bool
accept1 m@(qs, q0, fs, d) w = elem (delta_star m q0 w) fs

accept2_aux :: Eq a => FSM a -> a -> [Char] -> Bool
accept2_aux m@(_, _, fs, _) q [] = elem q fs
accept2_aux m q (a:w) = accept2_aux m (delta m q a) w

accept2 :: Eq a => FSM a -> [Char] -> Bool
accept2 m@(_, q0, _, _) w = accept2_aux m q0 w

-- even_as is a machine that accepts strings with an even number of a's
-- states: (number of a's read so far) mod 2
even_as :: FSM Int
even_as = ([0,1], 0, [0], [(i, a, d i a) | i <- [0,1], a <- sigma]) where
  d i 'a' = (i + 1) `mod` 2
  d i 'b' = i

-- no_aaa is a machine that accepts strings that don't have three a's in a row
-- states: number of a's in a row just read (n = 0, 1, 2), 3 is a trap
no_aaa :: FSM Int
no_aaa = ([0..3], 0, [0..2], [(i, a, d i a) | i <- [0..3], a <- sigma]) where
  d i 'a' = min 3 (i + 1)
  d 3 'b' = 3
  d _ 'b' = 0


---------------- Some additional useful functions --------------------------

-- Normalize a list, i.e., sort and remove (now adjacent) duplicates.
-- Two lists determine the same set if they normalize to the same list
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

6
-- Check whether two lists overlap
overlap :: Eq a => [a] -> [a] -> Bool
overlap [] ys = False
overlap (x:xs) ys = elem x ys || overlap xs ys


---------------- Lab 6 begins here -----------------------------------------
astar :: FSM Int
astar = ([0,1,2], 0, [1],[(0,'a',1),(0,'b',2),(1,'a',1),(1,'b',2),(2,'a',2), (2,'b',2)])

bstar :: FSM Int
bstar = ([3,4,5],3, [4],[(3,'a',5),(3,'b',4),(4,'a',5),(4,'b',4),(5,'a',5), (5,'b',5)])


onea :: FSM Int
onea = ([0,1,2], 0, [1],[(0,'a',1),(0,'b',2),(1,'a',2),(1,'b',2),(2,'a',2), (2,'b',2)])

oneb :: FSM Int
oneb = ([3,4,5],3, [4],[(3,'a',5),(3,'b',4),(4,'a',5),(4,'b',5),(5,'a',5), (5,'b',5)])

-- Complete the FSM constructions for the 6 language constructs and test your
-- functions adequately


-- Machine that accepts the empty language
emptyFSM :: FSM Int
emptyFSM = ([0], 0, [], [(0,a,0) | a <- sigma])

------------- Testing emptyFSM -------------
--- *Main> accept2 emptyFSM ""
--- False
--- *Main> accept2 emptyFSM "aaa"
--- False
--- *Main> accept2 emptyFSM "bbbb"
--- False
--- *Main> accept2 emptyFSM "bbaaabb"
--- False


-- Machine that accepts the language {"a"} where a in sigma
letterFSM :: Char -> FSM Int
letterFSM a = ([0,1,2], 0, [1], [(i, x, d i x) | i <- [0..2], x <- sigma ]) 
     where
	 d 0 'a' = 1
	 d _ _ = 2 
	 
------------- Testing emptyFSM -------------
--- *Main> accept2 (letterFSM 'a') "a"
--- True
--- *Main> accept2 (letterFSM 'a') "ab"
--- False
--- *Main> accept2 (letterFSM 'a') "bab"
--- False
--- *Main> accept2 (letterFSM 'a') "ba"
--- False
--- *Main> accept2 (letterFSM 'a') "aa"
--- False


-- Machine that accepts the language {w} where w in sigma*
stringFSM :: [Char] -> FSM Int
stringFSM w = (qs, 0,f, d) where
	qs = [0..length w + 1]
	f = [length w]
	d = [(i, a, ds i a) | i <- qs, a <-sigma] where
		ds i a = if (i < length w) && (w !! i == a) then i + 1 else length w + 1
		
		
------------- Testing emptyFSM -------------		
--- *Main> stringFSM "ab"
--- ([0,1,2,3],0,[2],[(0,'a',1),(0,'b',3),(1,'a',3),(1,'b',2),(2,'a',3),(2,'b',3),(3,'a',3),(3,'b',3)])
--- *Main> accept2 (stringFSM "ab") "ab"
--- True
--- *Main> accept2 (stringFSM "ab") "abb"
--- False
--- *Main> accept2 (stringFSM "ab") "babb"
--- False
--- *Main> accept2 (stringFSM "bab") "babb"
--- False
--- *Main> accept2 (stringFSM "babb") "babb"
--- True


-- Machine that accepts the union of the languages accepted by m1 and m2
unionFSM :: (Eq a, Eq b) => FSM a -> FSM b -> FSM (a, b)
unionFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
  qs = qs1 >< qs2
  s  = (s1,s2)
  fs = [(q1, q2) | q1 <- qs1, q2 <- qs2, (q1 `elem` fs1 || q2 `elem` fs2)]
  d  = [(q, a, ds q a) | q <- qs, a <- sigma] where
  	ds (q1,q2) a = (ap d1 q1 a, ap d2 q2 a)

------------- Testing unionFSM -------------

--- *Main> accept2 (unionFSM astar bstar) "b"
--- True
--- *Main> accept2 (unionFSM astar bstar) "bbbb"
--- True
--- *Main> accept2 (unionFSM astar bstar) "a"
--- True
--- *Main> accept2 (unionFSM astar bstar) "aaaaa"
--- True
--- *Main> accept2 (unionFSM astar bstar) "aaaaab"
--- False
--- *Main> accept2 (unionFSM astar bstar) "bbbba"
--- False

-- Machine that accepts the concatenation of the languages accepted by m1 and m2
catFSM :: (Eq a, Ord b) => FSM a -> FSM b -> FSM (a, [b])
catFSM (qs1, s1, fs1, d1) (qs2, s2, fs2, d2) = (qs, s, fs, d) where
	qs = [ (q, xq q x)| q <- qs1, x <- subsequences qs2] where
		xq q x = x ++ [s2 | elem q fs1]
	s  = (s1, [s2 | elem s1 fs1])
	fs = [q | q <- qs, overlap (snd q) fs2]
	d  = [(q, a, (q' (fst q) a, x' (snd q) a)) | q <- qs, a <- sigma] where
		q' qq aa = ap d1 qq aa
		x' x a' = [ ap d2 xt a'| xt <- x] 

-- Machine that accepts the Kleene star of the language accepted by m1
starFSM :: Ord a => FSM a -> FSM [a]
starFSM m1@(qs1, s1, fs1, d1) = (qs, s, fs, d) where
  qs = [[]] ++ [xc x | x <- subsequences  qs1] where
  	xc x = 	x ++ [s1 | overlap x fs1]
  s  = []
  fs = [[]] ++ [x | x <- qs, overlap x fs1]
  d  = undefined 
  ---d = [(q, a, step q a) | q <- qs, a <- sigma] where
  		---step [] a = norm $ [s | elem q fs1] ++ [q] where q = delta m1 s a
    	---step b a  = norm $ [s | overlap b' fs] ++ b' where
        	---b' = map (\q -> ap dm q a) b

-- Bonus Feature (for testing):

-- reachable m == the part of m that is reachable from the start state
reachable :: Ord a => FSM a -> FSM a
reachable m@(qs, q0, fs, d) = (qs', q0, fs', d') where
  qs' = sort $ stable $ iterate close ([q0], [])
  fs' = filter (`elem` qs') fs
  d'  = filter (\(q,_,_) -> q `elem` qs') d
  stable ((fr,qs):rest) = if null fr then qs else stable rest
  close (fr, xs) = (fr', xs') where
    xs' = fr ++ xs
    fr' = nub $ filter (`notElem` xs') (concatMap step fr)
    step q = map (ap d q) sigma
