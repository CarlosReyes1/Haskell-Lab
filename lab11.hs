-- Carlos Reyes

import Data.List (nub,sort,tails)

sigma :: [Char]
sigma = "ab"

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }
  
-- imported from lab6
-- Cartesian product
(><) :: [a] -> [b] -> [(a,b)]
xs >< ys = [(x,y) | x <- xs, y <- ys]

-- imported from lab7
-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
  					  | otherwise = x : mynub ys

ap:: Ord a => [(a,a)] -> a -> a
ap ((x,y):rs) a = if x == a then y else ap rs a

closure :: Ord a => [a] -> (a -> [a]) -> [a]
closure start step = stable $ iterate close (start,[]) where
  stable ((fr,xs):rest) = if null fr then xs else stable rest
  close (fr, xs) = (fr', xs') where  
      xs' = fr ++ xs
      fr' = nub $ filter (`notElem` xs') (concatMap step fr)
	  
	  
-- Minimize
minimize :: Ord a => FSM a -> FSM a
minimize m1 = FSM {
	states = norm $ map snd equiv',
	start = ap equiv' (start m1),
	finals = [q | q <- (norm $ map snd equiv'), elem q (finals m1)],
	delta = [(q,a,ap equiv' q') | (q,a,q') <- (delta m1), elem q (norm $ map snd equiv')]
} where
	lessThan = [(q1, q2) | (q1:rest) <- tails (sort (states m1)), q2 <- rest]
	lessveq = [(q1, q2) | (q1:rest) <- tails (sort (states m1)), q2 <- q1:rest]
	deltaInv q a = [q1 | (q1, a', q2) <- (delta m1), q2 == q, a == a']
	cinitstep = closure initXs step
	step (q1,q2) = (concatMap (\a -> deltaInv q1 a >< deltaInv q2 a) sigma)
	initXs = [q | q <- lessThan, notElem q cinitstep]
	equiv = [q | q <- lessveq, notElem q cinitstep]
	equiv' = [q' | (q':rs) <- tails equiv, null rs || fst q' < fst (head rs)]
