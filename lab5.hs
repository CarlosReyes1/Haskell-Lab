-- CSci 119, Lab 5
-- Reference: Lecture notes, Sections 4.1, 4.2

-- Carlos Reyes

sigma = ['a', 'b']

-- Finite State Machine M = (Q, q0, F, d)
type FSM = ([Int], Int, [Int], [(Int,Char,Int)])

atleastonea :: FSM
atleastonea = ([0,1], 0, [1], [(0,'a',1), (0,'b', 0), (1,'a',1), (1,'b',1)])

-- Check whether a finite state machine (qs, q0, fs, ts) is correct/complete:
-- (1) States qs are unique (no duplicates)
-- (2) Start state is a state (q0 is in qs)
-- (3) Final states are states (fs is a subset of qs; don't worry about dups)
-- (4) Transition relation is a function from qs and sigma to qs (exactly one
--     output state for each state and letter from sigma)'

checkFSM :: FSM -> Bool
checkFSM (qs, q0, fs, ts) = nodups qs && elem q0 qs && subset fs qs && transRel ts qs
	where
	nodups :: [Int] -> Bool
	nodups [] = True
	nodups (q:qs) = not(elem q qs) && nodups qs
	
	subset :: [Int] -> [Int] -> Bool
	subset [] _ = True
	subset (f:fs) qs = (elem f qs) && subset fs qs
	
	transRel :: [(Int, Char, Int)] -> [Int] -> Bool
	transRel ts qs = and [ length [ (x,y)| (x,y,z) <- ts, x==q, y==a] == 1| q <- qs, a <- sigma]
	
-- Gives the transition function of the machine as a function
-- i.e., delta m q a = the state machine m goes to when reading a in state q
delta :: FSM -> Int -> Char -> Int
delta (qs, q0, fs, (s, c, n) :ts) q a = if s == q && c == a then n else delta (qs, q0, fs, ts) q a

-- Gives the delta* function
delta_star :: FSM -> Int -> [Char] -> Int
delta_star m q [] = q
delta_star m q (w:ws) = delta_star m (delta m q w) ws

-- Machine acceptance, Definition 1 (via delta*)
-- Starts at start state
accept1 :: FSM -> [Char] -> Bool
accept1 m@(qs, q0, fs, ts) w = checkFSM m && elem (delta_star m q0 w) fs


-- Machine acceptance, Definition 2 (via L_q(M))

-- accept2_aux m q w = whether m, starting in q, accepts w (recursive in w)
-- Starts at any state given as q
accept2_aux :: FSM -> Int -> [Char] -> Bool
accept2_aux (qs, q0, fs, ts) q [] = elem q fs
accept2_aux m@(qs, q0, fs, ts)q w = elem (delta_star m q w) fs

-- Defined (non-recursively) in terms of accept2_aux
accept2 :: FSM -> [Char] -> Bool
accept2 m@(qs, q0, fs, ts) w = accept2_aux m q0 w


-- Define a machine that accepts exactly the strings with an even number of a's
-- and test it adequately'

evena :: FSM
evena = ([0,1], 0, [0], [(0,'a',1), (0,'b', 0), (1,'a',1), (1,'b',1)])

-- Define a machine that accepts exactly the strings that do not contain "aaa"
-- as a substring and test it adequately

noconsa :: FSM
noconsa = ([0,1,2,3], 0, [0,1,2], [(0,'a',1), (0,'b', 0), (1,'a',2), (1,'b',0), (2,'a',3), (2,'b',0), (3,'a',3), (3,'b',3)])