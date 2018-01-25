-- Lab 7: Convert FSMs to regular expressions

-- Carlos Reyes
-- Once I had a dream that I was tall. It was scary ass f***[9]. I wasn't used to being so high off the ground'!!!!

import Data.List (sort, elemIndex)

findFive :: [Int] -> Int
findFive xs = case elemIndex 5 xs of
	Just x -> x
	Nothing -> (-1)

---------------- Given functions ----------------

-- normalize a list, i.e., sort and remove (now adjacent) duplicates
norm :: Ord a => [a] -> [a]
norm = mynub . sort where
  mynub [] = []
  mynub [x] = [x]
  mynub (x:ys@(y:zs)) | x == y = mynub ys
                      | otherwise = x : mynub ys

-- Ordinary regular expressions and a show method for them
data RE  = Empty | Letter Char | Union RE RE | Cat RE RE | Star RE
instance (Show RE) where    -- use precedence to minimize parentheses
  showsPrec d Empty         = showString "@"
  showsPrec d (Letter c)    = showString [c]
  showsPrec d (Union r1 r2) = showParen (d > 6) $  -- prec(Union) = 6
                              showsPrec 6 r1 .
                              showString "+" .
                              showsPrec 6 r2
  showsPrec d (Cat r1 r2)   = showParen (d > 7) $  -- prec(Cat) = 7
                              showsPrec 7 r1 .
                              showsPrec 7 r2
  showsPrec d (Star r1)     = showsPrec 9 r1 .     -- prec(Star) = 8
                              showString "*"

-- Extended regular expressions, including a name for One = Star Empty,
-- and arbitrary numbers of arguments for (associative) Union and Cat
data RE' = Zero | One | Letter' Char | Union' [RE'] | Cat' [RE'] | Star' RE'
  deriving (Eq, Ord, Show)

--- ex2 = Union' [Letter' 'a', Letter' 'b', Star' (Letter' 'b')]

-- Convert ordinary REs into extended REs
toRE' :: RE -> RE'
toRE' Empty = Zero
toRE' (Letter c) = Letter' c
toRE' (Union r1 r2) = Union' [toRE' r1, toRE' r2]
toRE' (Cat r1 r2) = Cat' [toRE' r1, toRE' r2]
toRE' (Star r1) = Star' (toRE' r1)

-- Convert extended REs into ordinary REs, eliminating Union' and Cat' on
-- lists of length < 2, and right-associating them on longer lists
toRE :: RE' -> RE
toRE Zero = Empty
toRE One = Star Empty
toRE (Letter' c) = Letter c
toRE (Union' []) = Empty
toRE (Union' [r]) = toRE r
toRE (Union' (r:rs)) = Union (toRE r) (toRE (Union' rs))
toRE (Cat' []) = Star Empty
toRE (Cat' [r]) = toRE r
toRE (Cat' (r:rs)) = Cat (toRE r) (toRE (Cat' rs))
toRE (Star' r) = Star (toRE r)

-- Basic postfix parser for RE', assuming binary + and ., for testing
re :: String -> RE'
re w = re' w [] where
  re' [] [r] = r
  re' ('0':xs) rs = re' xs (Zero:rs)
  re' ('1':xs) rs = re' xs (One:rs)
  re' ('+':xs) (r2:r1:rs) = re' xs (Union' [r1,r2]:rs)
  re' ('.':xs) (r2:r1:rs) = re' xs (Cat' [r1,r2]:rs)
  re' ('*':xs) (r:rs) = re' xs (Star' r:rs)
  re' (x:xs) rs = re' xs (Letter' x:rs)

--' no green

-- Finite state machines (as records), indexed by the type of their states
-- M = FSM {states=qs, start=s, finals=fs, delta=d}
data FSM a = FSM {
  states :: [a],
  start  :: a,
  finals :: [a],
  delta  :: [(a,Char,a)]
  }---deriving Show

ex3 = FSM { states = [0,1],
			start = 0,
			finals = [1],
			delta = [(0,'a',1), (0,'b',0), (1,'a',0), (1,'b',0)]
		}
		
		
-- ap ts q a == the unique q' such that (q, a, q') is in ts;  assumes success
ap :: Eq a => [(a,Char,a)] -> a -> Char -> a 
ap ((q1, a1, q2):ts) q a | q1 == q && a1 == a = q2
                         | otherwise = ap ts q a

---------------- Lab 7 begins here ----------------

sigma = "ab"  -- Everything below should work with any choice of sigma


-------- Part 1

-- Reimplement your RE operations from Part 1 of Lab 4 for the type RE'
emptiness :: RE' -> Bool
emptiness (Zero) = True
emptiness (One) = False
emptiness (Letter' a) = False
emptiness (Union' []) = True
emptiness (Union' [r]) = emptiness r
emptiness (Union' (r:rs)) = emptiness r && emptiness (Union' rs)
emptiness (Cat' []) = emptiness One 
emptiness (Cat' [r]) = emptiness r
emptiness (Cat' (r:rs)) = emptiness r || emptiness (Cat' rs) 
emptiness (Star' r) = False

--------- Test Cases emptiness --------------
--- *Main> emptiness Zero
--- True
--- *Main> emptiness One
--- False
--- *Main> emptiness (Letter' 'a')
--- False
--- *Main> emptiness (Union' [Letter' 'a', Star' (Letter' 'b')])
--- False
--- *Main> emptiness (Union'  [Zero, Zero])
--- True
--- *Main> emptiness (Cat' [Letter' 'a', Star' (Letter' 'b')])
--- False
--- *Main> emptiness (Cat'  [Zero, Letter' 'a'])
--- True
--- *Main> emptiness (Star' (Letter' 'b'))
--- False

unitarity :: RE' -> Bool
unitarity (Zero) = False
unitarity (One) = True
unitarity (Letter' a) = False
unitarity (Union' []) = False 
unitarity (Union' (r:rs)) = (unitarity r && emptiness (Union' rs)) || (emptiness r && unitarity (Union' rs)) || (unitarity r && unitarity (Union' rs))
unitarity (Cat' []) = True
unitarity (Cat' (r:rs)) = unitarity r && unitarity (Cat' rs)
unitarity (Star' r) = emptiness (r) || unitarity (r)

--------- Test Cases unitarity --------------
--- *Main> unitarity Zero
--- False
--- *Main> unitarity One
--- True
--- *Main> unitarity (Letter' 'a')
--- False
--- *Main> unitarity (Union' [Star' Zero, Star' (Letter' 'a')])
--- False
--- *Main> unitarity (Union' [Star' Zero, Star' Zero])
--- True
--- *Main> unitarity (Cat' [Star' Zero, Star' Zero])
--- True
--- *Main> unitarity (Cat' [Star' Zero, Letter' 'a'])
--- False
--- *Main> unitarity (Star' Zero)
--- True
--- *Main> unitarity (Star' (Letter' 'a'))
--- False

bypassability :: RE' -> Bool
bypassability (Zero) = False
bypassability (One) = True
bypassability (Letter' a) = False
bypassability (Union' []) = False
bypassability (Union' (r:rs)) = bypassability r || bypassability (Union' rs)
bypassability (Cat' []) = True
bypassability (Cat' (r:rs)) =  bypassability r && bypassability (Cat' rs)
bypassability (Star' r) = True

--------- Test Cases for bypassability --------------
--- *Main> bypassability (Union' [Letter'  'a', Letter' 'a', Zero])
--- False
--- *Main> bypassability (Union' [Star' (Letter'  'a'), Star' (Letter'  'b')])
--- True
--- *Main> bypassability (Cat'  [Star' (Letter'  'a'), Letter' 'b'])
--- False
--- *Main> bypassability (Cat'  [Star' (Letter'  'a'), Zero])
--- False
--- *Main> bypassability (Star' (Letter'  'a'))
--- True


infiniteness :: RE' -> Bool
infiniteness (Zero) = False
infiniteness (One) = False
infiniteness (Letter' a) = False
infiniteness (Union' []) = False
infiniteness (Union' (r:rs)) = infiniteness r || infiniteness (Union' rs)
infiniteness (Cat' []) = False
infiniteness (Cat' (r:rs)) = (infiniteness r && not (emptiness(Cat' rs))) || (infiniteness (Cat' rs) && not (emptiness r))
infiniteness (Star' r) = not (emptiness r) && not (unitarity r)

--------- Test Cases for infiniteness --------------
--- *Main> infiniteness (Union' [Star' (Letter' 'a'), Zero])
--- True
--- *Main> infiniteness (Union' [Star' (Letter' 'a'), Letter' 'b'])
--- True
--- *Main> infiniteness (Union' [Letter' 'a', Letter' 'b'])
--- False
--- *Main> infiniteness (Cat' [Star' (Letter' 'a'), Star' (Letter' 'b')])
--- True
--- *Main> infiniteness (Cat' [Star' (Letter' 'a'), Letter' 'b'])
--- True
--- *Main> infiniteness (Cat' [Letter' 'a', Letter' 'b'])
--- False
--- *Main> infiniteness (Star' (Letter' 'a'))
--- True
--- *Main> infiniteness (Star' (Zero))
--- False

rev :: RE' -> RE'
rev (Zero) = Zero
rev (One) = One
rev (Letter' a) = Letter' a
rev (Union' []) = Zero
rev (Union' [r]) = rev(r)
rev (Union' (r:rs)) = Union' [rev(r), rev (Union' rs)] 
rev (Cat' []) = Zero
rev (Cat' [r]) = rev(r)
rev (Cat' (r:rs)) = Cat' [rev (Cat' rs), rev (r)]
rev (Star' r) = Star' (rev r)

--- *Main> rev (re "aab+@*+.bab+@*+.+")
--- Union' [Cat' [Union' [Union' [Letter' 'a',Letter' 'b'],Star' (Letter' '@')],Letter' 'a'],Cat' [Union' [Union' [Letter' 'a',Letter' 'b'],Star' (Letter' '@')],Letter' 'b']]
--- *Main> toRE it
--- (a+b+@*)a+(a+b+@*)b

left_quotient :: Char -> RE' -> RE'
left_quotient s (Zero) = Zero
left_quotient s (One) = Zero
left_quotient s (Letter' a) = if a == s then One else Zero
left_quotient s (Union' []) = Zero
left_quotient s (Union' [r]) = left_quotient s r
left_quotient s (Union' (r:rs)) = Union' [(left_quotient s r), (left_quotient s (Union' rs))]
left_quotient s (Cat' []) = Zero
left_quotient s (Cat' [r]) = left_quotient s r
left_quotient s (Cat' (r:rs)) = if bypassability r then Union' [ Cat' ([(left_quotient s r)] ++ rs), (left_quotient s (Union' rs))] else Cat' ([(left_quotient s r)] ++ rs)
left_quotient s (Star' r) = Cat' [(left_quotient s r), (Star' r)]

-- *Main> left_quotient 'a' (re "aab+@*+.bab+@*+.+")
-- Union' [Cat' [One,Union' [Union' [Letter' 'a',Letter' 'b'],Star' (Letter' '@')]],Cat' [Zero,Union' [Union' [Letter' 'a',Letter' 'b'],Star' (Letter' '@')]]]
-- *Main> toRE it
-- @*(a+b+@*)+@(a+b+@*)

-- Implement one more function: proper (cannot recognize epsilon)
proper :: RE' -> Bool
proper (Zero) = True
proper (One) = False
proper (Letter' r) = True
proper (Union' []) = True
proper (Union' [r]) = proper r
proper (Union' (r:rs)) = proper r || proper (Union' rs)
proper (Cat' []) = True
proper (Cat' [r]) = proper r
proper (Cat' (r:rs)) = proper r && proper (Cat' rs)
proper (Star' r') = False


--------- Test Cases for proper --------------
--- *Main> proper Zero
--- True
--- *Main> proper One
--- False
--- *Main> proper (Union' [Zero, One, Letter' 'a'])
--- True
--- *Main> proper (Union' [One, One, One])
--- False
--- *Main> proper (Cat' [Letter' 'a', Zero, One])
--- False
--- *Main> proper (Cat' [Letter' 'a', Letter' 'b', Zero])
--- True
--- *Main> proper (Star' (Letter' 'a'))
--- False
--- *Main> proper (Star' (One))
--- False


-------- Part 2

-- Solve a system of proper linear equations
-- You can assume that the system is correctly formed and proper
solve :: [[RE']] -> [RE'] -> [RE']

solve [] [] = []
solve ((l11:l1J) : rows) (l1':lI') = simp x1 : xI where
  -- l11 is the corner element, and l1J = [l12,...,l1n] is the rest of 1st row
  -- rows are the rest of the rows [[l21,...,l2n], ..., [ln1,...,lnn]]
  -- l1' is the first constant
  -- lI' are the rest of the contants [l2',...,ln']
  
  -- first column [l21, ..., ln1]
  lI1 = map head rows

  -- sub-matrix [[l22,...,l2n], ..., [ln2,...,lnn]]
  lIJ = rows

  -- [[l22_bar,...,l2n_bar], ..., [ln2_bar,...,lnn_bar]] computed via (6)
  lIJ_bar = zipWith3 six lI1 lIJ l1J
  six li1 liJ l1j = map tail rows

  -- [l2'_bar,..., ln'_bar] computed via (7)
  lI'_bar = zipWith seven lI1 lI'
  seven li1 li' = undefined
    
  -- recursively solve the system of size n-1
  xI = solve lIJ_bar lI'_bar

  -- compute x1 from xI via (5)
  x1 = undefined


-- Generate a regular SPLE from an FSM via formulas in Theorem 6.5
toSPLE :: FSM Int -> ([[RE']], [RE'])
toSPLE m = (lIJ, lI') where
  qs = states m
  
  -- Construct matrix of coefficients (coef i j = Lij)
  lIJ = [[simp (coef i j) | j <- qs] | i <- qs]
  coef i j = undefined

  -- Construct constants
  lI' = undefined


-- Convert an FSM to a RE'
conv :: FSM Int -> RE'
conv m = simp $ solution !! start m where
  (matrix, consts) = toSPLE m
  solution = solve matrix consts


-- Test! Test! Test! (and show your tests here)



---------------- Lab 7 ends here ----------------------------------


{----------------------------------------------------------------------------
| Bonus feature:  A regular-expression simplifier
|----------------------------------------------------------------------------

A "simplified" RE' satisfies the following conditions:
(1) Every Union' is applied to a normalized list of two or more arguments,
    each of which is a One, Letter', Cat', or Star' (i.e., not Zero or Union')
(2) Every Cat' is applied to a list of two or more arguments, each of which is
    a Letter' or Star' (i.e., not Zero, One, Union', or Cat')
(3) Every Star' is applied to a Letter', Union', or Cat' (i.e., not Zero, One,
    or Star')

The following simplification rules, when applied repeatedly at every subterm
of a RE' until the RE' no longer changes, result in a simplified RE':

   Union' []                          --> Zero
   Union' [r]                         --> r
   Union' (rs1 ++ [Zero] ++ rs2)      --> Union' (rs1 ++ rs2)
   Union' (rs1 ++ [Union' rs] ++ rs2) --> Union' (rs1 ++ rs ++ rs2)
   Union' rs                          --> Union' (norm rs)                  (*)

   Cat' []                            --> One
   Cat' [r]                           --> r
   Cat' (rs1 ++ [Zero] ++ rs2)        --> Zero
   Cat' (rs1 ++ [One] ++ rs2)         --> Cat' (rs1 ++ rs2)
   Cat' (rs1 ++ [Union' rs] ++ rs2)   --> Union' (map (\r -> Cat' (rs1 ++ [r] ++ rs2)) rs)
   Cat' (rs1 ++ [Cat' rs] ++ rs2)     --> Cat' (rs1 ++ rs ++ rs2)

   Star' Zero                         --> One
   Star' One                          --> One
   Star' (Star' r)                    --> Star' r

(*) Note: this rule should only be applied if rs is not already normalized;
    normalization is used to realize the commutativity and idempotency of union
    (i.e., that  L1 u L2 = L2 u L1  and  L u L = L ).

However, it would be very inefficient to attempt to apply these rules in the
manner indicated. Instead, our approach is to stage the application of these
rules carefully to minimize the number of traversals of the regular expression.
-------------------------------------------------------------------------------}

simp :: RE' -> RE'
simp Zero = Zero
simp One = One
simp (Letter' c) = Letter' c
simp (Union' rs) = union' $ flat_uni $ map simp rs
simp (Cat' rs) = union' $ flat_cat $ map simp rs
simp (Star' r) = star' $ simp r

-- Smart constructor for Union' that normalizes its arguments and
-- handles the empty and singleton cases
union' :: [RE'] -> RE'
union' rs =  case norm rs of
  []  ->  Zero
  [r] -> r
  rs  -> Union' rs

-- Smart constructor for Cat' that handles the empty and singleton cases
cat' :: [RE'] -> RE'
cat' [] = One
cat' [r] = r
cat' rs = Cat' rs

-- Smart constructor for Star' that handles the constant and Star' cases
star' :: RE' -> RE'
star' Zero = One
star' One = One
star' (Star' r) = star' r
star' r = Star' r

-- Flatten a list of arguments to Union'; assumes each argument is simplified
flat_uni :: [RE'] -> [RE']
flat_uni [] = []
flat_uni (Zero:rs) = flat_uni rs
flat_uni (Union' rs':rs) = rs' ++ flat_uni rs
flat_uni (r:rs) = r : flat_uni rs

-- Flatten a list of arguments to Cat', turning them into a list of arguments
-- to Union'; assumes each argument is simplified
flat_cat :: [RE'] -> [RE']
flat_cat rs = fc [] rs where
  -- fc (args already processed, in reverse order) (args still to be processed)
  fc :: [RE'] -> [RE'] -> [RE']
  fc pr [] = [cat' $ reverse pr]
  fc pr (Zero:rs) = []
  fc pr (One:rs) = fc pr rs
  fc pr (Cat' rs':rs) = fc (reverse rs' ++ pr) rs
  fc pr (Union' rs':rs) = concat $ map (fc pr . (:rs)) rs'
  fc pr (r:rs) = fc (r:pr) rs

