-- Carlos Reyes
-- CSCI_119 / Lab3
-- Fall 2017

import Data.List (nub)


---- String operations (note: String = [Char])

-- Length and concatenation (Def 2.2, reimplements len and ++)
strlen :: String -> Int
strlen [] = 0
strlen (x:xs) = 1 + strlen xs

strcat :: String -> String -> String
strcat [] ys = ys
strcat (x:xs) ys = x : strcat xs ys


---- Language operations. Assume inputs contain no duplicates, and insure that
---- outputs also contain no duplicates

type Language = [String]

-- Union of languages
union_lang :: Language -> Language -> Language
union_lang [] l2 = l2
union_lang (x:l1) l2 = if x `elem` l2 then union_lang l1 l2 else x : union_lang l1 l2

-- Concatenation of languages (Def 2.5)
concat_lang :: Language -> Language -> Language
concat_lang l1 [] = l1
concat_lang [] l2 = l2
concat_lang l1 l2 = nub [strcat w1 w2 | w1 <- l1, w2 <- l2]

-- L^n = L * L * ... * L (n times)
power_lang :: Language -> Int -> Language
power_lang l 0 = [""]
power_lang l n = concat_lang l (power_lang l (n-1))

-- Bounded Kleene star, L* = L^0 U L^1 U L^2 U ... U L^n
bstar_lang :: Language -> Int -> Language
bstar_lang l 0 = [""]
bstar_lang l n = union_lang (power_lang l n) (bstar_lang l (n-1))
--the language containing the empty string

-- Reimplements elem for Languages
element :: String -> Language -> Bool
element xs [] = False
element "" l = False
element xs (y:l) = if xs==y then True else element xs l

-- L1 subset L2
subset :: Language -> Language -> Bool
subset l1 [] = False
subset [] l2 = True
subset (l:l1) l2 = l `elem` l2 && subset l1 l2


---- Regular expressions and the languages they denote 
data RegExp = Empty
             | Str String
             | Cat RegExp RegExp
             | Union RegExp RegExp
             | Star RegExp

-- [[r]], except use bound 5 for Kleene star
lang_of :: RegExp -> Language
lang_of (Empty) = []
lang_of (Str r) = [r]
lang_of (Cat r1 r2) = concat_lang (lang_of r1) (lang_of r2)
lang_of (Union r1 r2) = union_lang (lang_of r1) (lang_of r2)
lang_of (Star r) = bstar_lang (lang_of r) 5
              