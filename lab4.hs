-- CSci 119, Lab 4
-- Carlos Reyes
-- Fall 2017

-- I Like it 3 ways

---- Regular expressions, along with input and output
data RegExp = Empty
             | Letter Char
             | Union RegExp RegExp
             | Cat RegExp RegExp
             | Star RegExp

instance (Show RegExp) where    -- use precedence to minimize parentheses
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

-- Quick and dirty postfix regex parser, gives non-exaustive match on error
toRE :: String -> RegExp
toRE w = toRE' w [] where
  toRE' [] [r] = r
  toRE' ('+':xs) (r2:r1:rs) = toRE' xs (Union r1 r2:rs)
  toRE' ('.':xs) (r2:r1:rs) = toRE' xs (Cat r1 r2:rs)
  toRE' ('*':xs) (r:rs) = toRE' xs (Star r:rs)
  toRE' ('@':xs) rs = toRE' xs (Empty:rs)
  toRE' (x:xs) rs = toRE' xs (Letter x:rs)


---------------- Part 1 ----------------

-- Implement the six recursive predications/operations on RegExp given in
-- Section 3.3 of the notes. Each should begin with a type declaration.
-- Include several tests for each function.
emptiness :: RegExp -> Bool
emptiness (Empty) = True
emptiness (Letter a) = False
emptiness (Union r1 r2) = emptiness r1 && emptiness r2
emptiness (Cat r1 r2) = emptiness r1 || emptiness r2
emptiness (Star r) =  False

--------- Test Cases emptiness --------------
--- *Main> emptiness Empty
--- True
--- *Main> emptiness (Letter 'a')
--- False
--- *Main> emptiness (Union (Letter 'a') (Star (Letter 'b')))
--- False
--- *Main> emptiness (Union  (Empty) (Empty))
--- True
--- *Main> emptiness (Cat (Letter 'a') (Star (Letter 'b')))
--- False
--- *Main> emptiness (Cat  (Empty) (Letter 'a'))
--- True
--- *Main> emptiness (Star (Letter 'b'))
--- False

unitarity :: RegExp -> Bool
unitarity (Empty) = False
unitarity (Letter a) = False
unitarity (Union r1 r2) = (unitarity r1 && emptiness r2) || (emptiness r1 && unitarity r2) || (unitarity r1 && unitarity r2)
unitarity (Cat r1 r2) = unitarity r1 && unitarity r2
unitarity (Star r) = emptiness (r) || unitarity (r)

--------- Test Cases unitarity --------------
--- *Main> unitarity Empty
--- False
--- *Main> unitarity (Letter 'a')
--- False
--- *Main> unitarity (Union (Star Empty) (Star (Letter 'a')))
--- False
--- *Main> unitarity (Union (Star Empty) (Star Empty))
--- True
--- *Main> unitarity (Cat (Star Empty) (Star Empty))
--- True
--- *Main> unitarity (Cat (Star Empty) (Letter 'a'))
--- False
--- *Main> unitarity (Star Empty)
--- True
--- *Main> unitarity (Star (Letter 'a')))
--- *Main> unitarity (Star (Letter 'a'))
--- False


bypassability :: RegExp -> Bool
bypassability (Empty) = False
bypassability (Letter a) = False
bypassability (Union r1 r2) = bypassability r1 || bypassability r2
bypassability (Cat r1 r2) =  bypassability r1 && bypassability r2
bypassability (Star r) = True

--------- Test Cases for bypassability --------------
--- *Main> bypassability (Union (Letter  'a') (Letter 'a'))
--- False
--- *Main> bypassability (Union (Star (Letter  'a')) (Star (Letter  'b')))
--- True
--- *Main> bypassability (Cat  (Star (Letter  'a')) (Letter 'b'))
--- False
--- *Main> bypassability (Cat  (Star (Letter  'a')) (Empty))
--- False
--- *Main> bypassability (Star (Letter  'a'))
--- True


infiniteness :: RegExp -> Bool
infiniteness (Empty) = False
infiniteness (Letter a) = False
infiniteness (Union r1 r2) = infiniteness r1 || infiniteness r2
infiniteness (Cat r1 r2) = (infiniteness r1 && not (emptiness r2)) || (infiniteness r2 && not (emptiness r1))
infiniteness (Star r) = not (emptiness r) && not (unitarity r)

--------- Test Cases for infiniteness --------------
--- *Main> infiniteness (Union (Star (Letter 'a')) (Empty))
--- True
--- *Main> infiniteness (Union (Star (Letter 'a')) (Letter 'b'))
--- True
--- *Main> infiniteness (Union (Letter 'a') (Letter 'b'))
--- False
--- *Main> infiniteness (Cat (Star (Letter 'a')) (Star (Letter 'b')))
--- True
--- *Main> infiniteness (Cat (Star (Letter 'a')) (Letter 'b'))
--- True
--- *Main> infiniteness (Cat (Letter 'a') (Letter 'b'))
--- False
--- *Main> infiniteness (Star (Letter 'a'))
--- True
--- *Main> infiniteness (Star (Empty))
--- False
--- *Main> 


rev :: RegExp -> RegExp
rev (Empty) = Empty
rev (Letter a) = Letter a
rev (Union r1 r2) = Union (rev(r1)) (rev(r2))
rev (Cat r1 r2) = Cat (rev(r2)) (rev(r1))
rev (Star r) = Star (rev r)

left_quotient :: Char -> RegExp -> RegExp
left_quotient s (Empty) = Empty
left_quotient s (Letter a) = if a == s then Star(Empty) else Empty
left_quotient s (Union r1 r2) = Union (left_quotient s r1) (left_quotient s r2)
left_quotient s (Cat r1 r2) = if bypassability r1 then Union (Cat(left_quotient s r1) r2) (left_quotient s r2) else Cat (left_quotient s r1) r2
left_quotient s (Star r) = Cat (left_quotient s r) (Star r)

-- *Main> left_quotient 'a' (toRE "aab+@*+.bab+@*+.+")
-- @*(a+b+@*)+@(a+b+@*)



---------------- Part 2 ----------------

-- Implement the two matching algorithms given in Section 3.4 of the notes.
-- Call them match1 and match2. Start by implementing splits:

-- splits xs = list of all possible splits of xs, in order. For example,
-- splits "abc" = [("","abc"), ("a","bc"), ("ab","c"), ("abc","")]
splits :: [a] -> [([a], [a])]
splits xs = splits' [] xs 
	where
	splits' :: [a] -> [a] -> [([a],[a])]
	splits' a [] = [(a,[])]
	splits' a (b:bs) = [(a, b:bs)] ++ splits' (a ++ [b]) bs
	
---getting rid of green 420 =)'

match1 :: RegExp -> String -> Bool
match1 (Empty) w = False
match1 (Letter a) w = w == [a]
match1 (Union r1 r2) w = match1 r1 w || match1 r2 w
match1 (Cat r1 r2) w = and [(match1 r1 w1) && (match1 r2 w2) | (w1,w2) <- (splits w)]
match1 (Star r) w = (w == "") || and [(w1 /= "") && ((match1 r w1) && (match1 (Star r) w2)) | (w1, w2) <- (splits w)]


match2 :: RegExp -> String -> Bool
match2 r w = match2' [r] w False where
	match2' :: [RegExp] -> String -> Bool -> Bool
	match2' [] w c = w == ""
	match2' (Empty : rs) w c = False
	match2' ((Letter a) : rs) (w:ws) c = a == w && match2' rs ws False
	match2' ((Union r1 r2) : rs) w c = (match2' (r1 : rs) w c) || (match2' (r2 : rs) w c)
	match2' ((Cat r1 r2) : rs) w c = (match2' (r1 : r2 : rs) w c) || (c == True && bypassability r1 && match2' (r2 : rs) w True)
	match2' ((Star r) : rs) w c = c == False && match2' rs w False || match2' (r : (Star r) : rs) w True


-- Some regular expressions for testing. Also, test them on other solutions
-- to the exercises of Section 3.2 (as many as you can get).

ab   = toRE "aa.bb.+*"            -- every letter is duplicated
ttla = toRE "ab+*a.ab+.ab+."      -- third to last letter is a
ena  = toRE "b*a.b*.a.*b*."       -- even number of a's
bb1  = toRE "aba.+*b.b.aab.+*."   -- contains bb exactly once