-- To do:
-- When inventing a predicate p(x:y,z) -> q(x,y,z),
-- see if we can split it into q(x,y) & r(y,z).
-- Can check this by exhaustive testing.
--
-- Allow variables to appear twice in patterns (equality).
--
-- Allow conjunction w/ synthesised predicates e.g.
--   mult(X+1,Y,Z) :- mult(X,Y,Q), add(Q,Y,Z)
-- we can try mult(X,Y,Q) and use that to generate test data
-- (for Q) to synthesise add.
-- This works only because mult is a function (X,Y -> Q)---
-- good because it gives us a better way of synthesising functions
-- and we won't get too many conjuncts

-- "Inverse entailment and Progol" gives:
--   f(A, B) :- d(A, C), f(C, D), m(A, D, B)
-- where f is factorial and d is predecessor.
-- Look---pattern-matching is conjunction!
-- This gives a nice way of incorporating equality, etc.
-- This means that normal candidates don't need to follow
-- traditional pattern matching.
-- We could still say that synthesised predicates
-- must use only simple pattern matching, to reduce
-- the amount of choice.
--
-- not . anyLeq: I suspect we need lossless join decomposition.
--
-- Shrink the test data: given a program,
-- find the minimal set of test data that leads to that program.
--
-- Wait---do we really need [| prog |] to be monotone?!
-- Provided that each clause is consistent with the
-- target predicate, we can always recover the predicate
-- by adding more clauses. Does this make subsynthesis harder?
--
-- Think about problem whereby changing T/F to X in a specification
-- can make a predicate unguessable by weakening recursive case.
-- Think about interaction with idea to intersect guessed predicate
-- with recursive calls. I think I worked out it would be alright.
-- It makes some things X that would've been F before.
-- Those things would've been T in the subprogram because of
-- negation. Changing T to X makes it easier to satisfy clauses.
-- But if that subprogram in turn synthesises a new predicate,
-- that predicate will have things that are X but would have been F.
-- Wait, I don't understand---doesn't that make it easier to satisfy clauses too?
--
-- But it is plainly the case that if we go with e.g.
--  \xs ys -> if xs == ys then xs == reverse ys else X
-- that this is harder to discover than
--  \xs ys -> xs == reverse ys
-- So something is up with the recursive calls.
-- What is it, and can it affect conjunctions of recursive and
-- synthesised calls?
--
-- Also, remember that
--   p & q & ~r = ~(~p | ~q | r)
-- so maybe (maybe) we can avoid conjunction of synthed predicates
-- altogether and use mutual recursion to do the same trick.
-- Or maybe synthesised predicates are only useful when they
-- allow us to decompose a problem by eliminating variables.
--
-- There clearly is a problem with the "X"s we generate in subpredicates.
-- Maybe the current approach (accidentally evaluate the parent predicate
-- when checking recursive calls) is the best one. Each X on the RHS
-- of a recursive call gives us a choice---did the recursive call return
-- true or not? By evaluating the parent predicate, we make an arbitrary
-- choice. But is this sound? Isn't this exactly what the "nasty"
-- example proves is unsound?
--
-- Try printing out all places where we have an "X" that's reachable
-- by recursion from a non-"X".
--
-- Add synthesised candidates to shrink list.

{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Prelude hiding (elem, pred, negate, even)
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Data.List hiding (elem)
import Data.Maybe
import Data.Function
import Data.Ord
import Control.Spoon
import System.Timeout

-- Lisp terms.
data Term = Nil Type | Cons Type Term Term | Var Type Int
  deriving (Eq, Ord)

data Type = Unit | Nat | List Type | Tree Type | Pair Type Type deriving (Eq, Ord)

invert :: Type -> Maybe (Type, Type)
invert Unit = Nothing
invert Nat = Just (Unit, Nat)
invert (List ty) = Just (ty, List ty)
invert (Tree ty) = Just (ty, Pair (Tree ty) (Tree ty))
invert (Pair ty tz) = Just (ty, tz)

instance Show Type where
  show Unit = "()"
  show Nat = "Nat"
  show (List ty) = "[" ++ show ty ++ "]"
  show (Tree ty) = "{" ++ show ty ++ "}"
  show (Pair ty tz) = "(" ++ show ty ++ "," ++ show tz ++ ")"

termType :: Term -> Type
termType (Nil ty) = ty
termType (Cons ty _ _) = ty
termType (Var ty _) = ty

instance Show Term where
  showsPrec _ (Nil Unit) = showString "()"
  showsPrec _ (Nil Nat) = showString "0"
  showsPrec _ (Nil (List _)) = showString "[]"
  showsPrec _ (Nil (Tree _)) = showString "{}"
  showsPrec n (Cons Nat x y) =
    showParen (n > 10) (showsPrec 11 y . showString "+1")
  showsPrec n (Cons (List _) x y) =
    showString "[" . showsPrec 0 x . showString "|" . showsPrec 0 y . showString "]"
  showsPrec n (Cons Unit x y) =
    error "show: Cons _ _ :: Unit"
  showsPrec n (Cons (Tree _) x (Cons _ y z)) =
    showString "{" . shows x . showString "," . shows y . showString "," . shows z . showString "}"
  showsPrec n (Cons (Tree _) x y) =
    showString "{" . shows x . showString "," . shows y . showString "}"
  showsPrec n (Cons (Pair _ _) x y) =
    showString "(" . shows x . showString "," . shows y . showString ")"
  showsPrec n (Var ty i) = showString (twiddle ty (vars !! i))
    where
      twiddle (List ty) x = twiddle ty (x ++ "s")
      twiddle _ x = x

class Lisp a where
  fromTerm :: Term -> a
  sample :: a -> Set

instance Lisp () where
  fromTerm (Nil _) = ()

  sample _ = nil Unit

instance Lisp Int where
  fromTerm (Nil Nat) = 0
  fromTerm (Cons Nat (Nil Unit) x) = succ (fromTerm x)

  sample _ = listOf (nil Unit) Nat 3

instance Lisp a => Lisp [a] where
  fromTerm (Nil _) = []
  fromTerm (Cons _ x xs) = fromTerm x:fromTerm xs

  sample xs = listOf sx (List (setType sx)) 3
    where sx = sample (head xs)

instance (Lisp a, Lisp b) => Lisp (a, b) where
  fromTerm (Cons _ x y) = (fromTerm x, fromTerm y)

  sample ~(x, y) = ConsS (Pair (setType sx) (setType sy)) sx sy
    where
      sx = sample x
      sy = sample y

data Tree a = Node a (Tree a) (Tree a) | Leaf

instance Lisp a => Lisp (Tree a) where
  fromTerm (Cons _ x (Cons _ y z)) = Node (fromTerm x) (fromTerm y) (fromTerm z)
  fromTerm (Nil _) = Leaf

  sample ~(Node x _ _) = treeOf sx (Tree (setType sx)) 3
    where sx = sample x

-- Sets of test data.
data Set
  = Empty Type
  | InsertNil Type Set
  | ConsS Type Set Set

setType :: Set -> Type
setType (Empty ty) = ty
setType (InsertNil _ s) = setType s
setType (ConsS ty _ _) = ty

table :: Set -> [Term]
table Empty{} = []
table (InsertNil ty s) = Nil ty:table s
table (ConsS ty s t) = liftM2 (Cons ty) (table s) (table t)

elem :: Term -> Set -> Bool
Nil{} `elem` InsertNil{} = True
t `elem` InsertNil _ s = t `elem` s
Cons _ x y `elem` ConsS _ s t = x `elem` s && y `elem` t
_ `elem` _ = False

nil :: Type -> Set
nil ty = InsertNil ty (Empty ty)

singleton :: Term -> Set
singleton (Nil ty) = nil ty
singleton (Cons ty t u) = ConsS ty (singleton t) (singleton u)
singleton Var{} = error "singleton: non-ground term"

listOf :: Set -> Type -> Int -> Set
listOf x ty 0 = nil ty
listOf x ty n = InsertNil ty (ConsS ty x (listOf x ty (n-1)))

treeOf :: Set -> Type -> Int -> Set
treeOf x ty 0 = nil ty
treeOf x ty n = InsertNil ty (ConsS ty x (ConsS (Pair ty ty) y y))
  where y = treeOf x ty (n-1)

-- Patterns.
data Pattern = Pattern {
  trivial :: Bool,
  bound :: [Type],
  match :: Set -> Maybe [Set],
  undo :: [Term] -> Term
  }

instance Show Pattern where
  show patt =
    show (bound patt) ++ ":" ++
    show (undo patt (zipWith Var (bound patt) [0..]))

idP :: Type -> Pattern
idP ty = Pattern {
  trivial = True,
  bound = [ty],
  match = \s -> Just [s],
  undo = \[t] -> t
  }

nilP :: Type -> Pattern
nilP ty = Pattern {
  trivial = False,
  bound = [],
  match = \s -> if Nil ty `elem` s then Just [] else Nothing,
  undo = \[] -> Nil ty
  }

consP :: Type -> Pattern
consP ty = Pattern {
  trivial = False,
  bound = [hd, tl],
  match =
     let match Empty{} = Nothing
         match (InsertNil _ s) = match s
         match (ConsS _ s t) = Just [s, t]
     in match,
  undo = \[t, u] -> Cons ty t u
  }
  where
    Just (hd, tl) = invert ty

patterns :: Type -> [Pattern]
patterns Unit = [nilP Unit]
patterns ty =
  idP ty:
  case invert ty of
    Nothing -> []
    Just (l, r) -> [nilP ty, consP ty]

patternsOrder :: [Pattern] -> Int
patternsOrder = count (not . trivial)
  where count p = length . filter p

boundPatts :: [Pattern] -> [Type]
boundPatts = concatMap bound

matchPatts :: [Pattern] -> [Set] -> Maybe [Set]
matchPatts ps ss = fmap concat (zipWithM match ps ss)

undoPatts :: [Pattern] -> [Term] -> [Term]
undoPatts [] [] = []
undoPatts (p:ps) ts = undo p us:undoPatts ps vs
  where (us, vs) = splitAt (length (bound p)) ts

-- Predicates.
data Predicate = Predicate {
  domain :: [Set],
  func :: [Term] -> Maybe Bool
  }

predType :: Predicate -> [Type]
predType = map setType . domain

tests :: Predicate -> [[Term]]
tests pred = [ ts | ts <- mapM table (domain pred), func pred ts /= Nothing ]

matchPred :: [Pattern] -> Predicate -> Predicate
matchPred patts pred =
  case matchPatts patts (domain pred) of
    Just domain ->
      Predicate {
        domain = domain,
        func = func pred . undoPatts patts
        }
    Nothing ->
      Predicate {
        domain = map Empty (predType pred),
        func = const Nothing
        }

-- Programs.
data Program = Program {
  args :: [Type],
  clauses :: [Clause]
  }

data Clause = Clause {
  pattern :: [Pattern],
  rhs :: RHS
  }

instance Show Clause where
  show clause =
    show Program {
      args = [],
      clauses = [clause]
      }

clauseOrder (Clause pattern rhs) =
  (patternsOrder pattern, rhsOrder rhs)

data RHS = Top | App Target [Term] | Not RHS | Shrink RHS (Maybe RHS) deriving Show
data Target = Rec Int | Call Program deriving Show

depth :: Program -> Int
depth (Program _ cs) = maximum (0:map (rhsDepth . rhs) cs)

rhsDepth Top = 0
rhsDepth (App (Call p) _) = 1+depth p
rhsDepth (App (Rec _) _) = 0
rhsDepth (Not r) = rhsDepth r
rhsDepth (Shrink r _) = rhsDepth r

numVars :: Program -> Int
numVars (Program args cs) = length args + sum (map (rhsVars . rhs) cs)

rhsVars Top = 0
rhsVars (App (Call p) _) = numVars p
rhsVars (App (Rec _) _) = 0
rhsVars (Not r) = rhsVars r
rhsVars (Shrink r _) = rhsVars r

rhsOrder Top = 0
rhsOrder (Not r) = 1+rhsOrder r
rhsOrder App{} = 2
rhsOrder (Shrink r _) = rhsOrder r

type ShowM = StateT ShowState (Writer String)
data ShowState = ShowState {
  names :: [String],
  queue :: [([String], Program)]
  }

preds, vars :: [String]
preds = infinite ['p','q','r','s']
vars = infinite $ ['X','Y','Z','W','T','U','V']
infinite xs = concat [ replicateM n xs | n <- [1..] ]

instance Show Program where
  show p =
    execWriter (execStateT (loop showProgram) (ShowState (tail preds) [(take 1 preds, p)]))

loop :: ([String] -> Program -> ShowM ()) -> ShowM ()
loop f = do
  ShowState ns q <- get
  case q of
    [] -> return ()
    ((n,p):ps) -> do
      put (ShowState ns ps)
      f n p
      loop f

showProgram :: [String] -> Program -> ShowM ()
showProgram names (Program args cs) = do
  tell $
    "%% " ++ head names ++ " :: " ++
    concat [ show ty ++ " -> " | ty <- args ] ++ "Bool\n"
  mapM_ (showClause names) cs
  tell "\n"

showClause :: [String] -> Clause -> ShowM ()
showClause names (Clause patts rhs) = do
  tell $ head names ++ showArgs (undoPatts patts vs)
  unless (case rhs of Top -> True; _ -> False) $ do
    tell " :- "
    showRHS names rhs
  tell ".\n"
  where
    vs = zipWith Var (concatMap bound patts) [0..]

showRHS :: [String] -> RHS -> ShowM ()
showRHS _ Top = tell "true"
showRHS names (Not x) = do
  tell "not "
  showRHS names x
showRHS names (App f ts) = do
  showTarget names f
  tell (showArgs ts)
showRHS names (Shrink r _)= showRHS names r

showTarget :: [String] -> Target -> ShowM ()
showTarget names (Rec i) = tell (names !! i)
showTarget ctx (Call prog) = do
  ShowState (name:names) progs <- get
  put (ShowState names (progs ++ [(name:ctx, prog)]))
  tell name

showArgs :: [Term] -> String
showArgs [] = ""
showArgs ts = "(" ++ intercalate ", " (map show ts) ++ ")"

-- 3-valued logic.
or3 :: Maybe Bool -> Maybe Bool -> Maybe Bool
or3 (Just True) _ = Just True
or3 _ (Just True) = Just True
or3 (Just False) (Just False) = Just False
or3 _ _ = Nothing

ors3 :: [Maybe Bool] -> Maybe Bool
ors3 = foldr or3 (Just False)

not3 :: Maybe Bool -> Maybe Bool
not3 = fmap not

eq3 :: Maybe Bool -> Maybe Bool -> Bool
eq3 (Just x) (Just y) = x == y
eq3 _ _ = False

-- Evaluation.
evaluate :: Program -> [Term] -> Maybe Bool
evaluate p@(Program _ cs) ts = evaluateClauses [evaluate p] cs ts

evaluateClauses :: [[Term] -> Maybe Bool] -> [Clause] -> [Term] -> Maybe Bool
evaluateClauses ps cs ts =
  ors3 [ evaluateClause ps c ts | c <- cs ]

evaluateClause :: [[Term] -> Maybe Bool] -> Clause -> [Term] -> Maybe Bool
evaluateClause ps (Clause patts rhs) ts =
  ors3 [ evaluateRHS ps rhs us
       | Just ss <- [matchPatts patts (map singleton ts)],
         us <- mapM table ss ]

evaluateRHS :: [[Term] -> Maybe Bool] -> RHS -> [Term] -> Maybe Bool
evaluateRHS _ Top _ = Just True
evaluateRHS ps (Not r) ts = not3 (evaluateRHS ps r ts)
evaluateRHS ps (App (Rec i) ts) us = (ps !! i) (map (subst us) ts)
evaluateRHS _ (App (Call p) ts) us = evaluate p (map (subst us) ts)
evaluateRHS ps (Shrink r _) ts = evaluateRHS ps r ts

subst :: [Term] -> Term -> Term
subst ts (Var _ i) = ts !! i
subst ts (Cons ty t u) = Cons ty (subst ts t) (subst ts u)
subst ts n@Nil{} = n

-- Predicate operators.
implements, consistentWith :: ([Term] -> Maybe Bool) -> Predicate -> Bool
f `implements` pred = and [ f ts `eq3` func pred ts | ts <- tests pred ]
f `consistentWith` pred =
  and [ func pred ts == Just True || f ts == Just False | ts <- tests pred ]

extends :: ([Term] -> Maybe Bool) -> ([Term] -> Maybe Bool) -> Predicate -> Bool
extends f g pred = or [ f ts == Just True && g ts /= Just True | ts <- tests pred ]

except :: Predicate -> ([Term] -> Maybe Bool) -> Predicate
except pred f = Predicate {
  domain = domain pred,
  func = \ts -> if f ts == Just True then Nothing else func pred ts
  }

negate :: Predicate -> Predicate
negate pred = pred { func = not3 . func pred }

-- Guessing.
guess_ :: Int -> Predicate -> Program
guess_ depth pred
  | evaluate p1 `implements` pred = p1
  | otherwise = p2
  where
    p1 = Program args cands
    p2 = Program args (cands ++ synth)

    consistentWithPred c =
      evaluateClause [func pred] c `consistentWith` pred

    args = predType pred
    cands = filter consistentWithPred (candidates1 args)
    synth = [ c
            | c <- candidates2 depth pred',
              consistentWithPred c,
              extends (evaluateClause [func pred] c) (evaluate p1) pred' ]
    pred' = pred `except` evaluateClauses [func pred] cands

candidates1 :: [Type] -> [Clause]
candidates1 args = sortBy (comparing clauseOrder) $ do
  patts <- mapM patterns args
  rhs <- Top:
         map (App (Rec 0)) (descending args patts)
  return (Clause patts rhs)

descending :: [Type] -> [Pattern] -> [[Term]]
descending args patts
  | length ctx <= length args = []
  | otherwise =
    filter wellTyped .
    filter (all ((/= Unit) . termType)) .
    uniq . map (take (length args)) . permutations $
    zipWith Var ctx [0..]
  where
    ctx = boundPatts patts
    wellTyped ts = and (zipWith (==) args (map termType ts))
    uniq = map head . group . sort

candidates2 :: Int -> Predicate -> [Clause]
candidates2 0 _ = []
candidates2 d pred = do
  patts <- sortBy (comparing patternsOrder) $ mapM patterns (predType pred)
  guard (not (all trivial patts))
  let pred' = matchPred patts pred
      prog = Not (synthesise (d-1) (negate pred'))
      prog' = synthesise (rhsDepth prog-1) pred'
      err = error "candidates2: recursive synthesis"
  return . Clause patts . Shrink prog $
    if evaluateRHS err prog' `implements` pred' &&
      rhsVars prog' <= rhsVars prog
    then Just prog' else Nothing

synthesise :: Int -> Predicate -> RHS
synthesise depth pred =
  App (Call prog) (filter (relevant pred . varId) vars)
  where
    prog = guess_ depth (matchPred rels pred)
    varId (Var _ i) = i
    vars = zipWith Var (predType pred) [0..]
    rels = [
        if relevant pred i then idP ty else nilP ty
      | Var ty i <- vars ]

relevant p i = not (irrelevant p i)
irrelevant p i =
  all equal . groupBy ((==) `on` shell) .
              sortBy (comparing shell) . tests $ p
  where
    shell ts = take i ts ++ drop (i+1) ts
    equal tss = and (zipWith (==) xs (tail xs))
      where xs = map (func p) tss

-- Shrinking.
shrink :: Predicate -> Program -> Program
shrink pred prog =
  case [ prog'
       | prog' <- candidates prog,
         evaluate prog' `implements` pred ] of
    [] -> prog
    (prog':_) -> shrink pred prog'

candidates :: Program -> [Program]
candidates (Program args cs) =
  map (Program args) (candidateClausess cs)

candidateClausess :: [Clause] -> [[Clause]]
candidateClausess [] = []
candidateClausess (c:cs) =
  cs:
  map (:cs) (candidateClauses c) ++
  map (c:) (candidateClausess cs)

candidateClauses :: Clause -> [Clause]
candidateClauses (Clause patt rhs) =
  map (Clause patt) (candidateRHSs rhs)

candidateRHSs :: RHS -> [RHS]
candidateRHSs Top = []
candidateRHSs (Not r) = Top:map Not (candidateRHSs r)
candidateRHSs (App (Rec _) ts) = [Top]
candidateRHSs (App (Call prog) ts) =
  Top:[ App (Call prog') ts | prog' <- candidates prog ]
candidateRHSs (Shrink r Nothing) = [r]
candidateRHSs (Shrink _ (Just r)) = [r]

-- A nicer interface.
class Pred a where
  domain_ :: a -> [Set]
  func_ :: a -> [Term] -> Maybe Bool

instance Pred Bool where
  domain_ _ = []
  func_ x [] = Just x

instance (Lisp a, Pred b) => Pred (a -> b) where
  domain_ f = sample x:domain_ (f x)
    where x = undefined :: a
  func_ f (x:xs) = func_ (f (fromTerm x)) xs

instance Pred Predicate where
  domain_ = domain
  func_ = func

pred :: Pred a => a -> Predicate
pred x = Predicate {
  domain = domain_ x,
  func = func_ x
  }

guess :: Pred a => a -> Program
guess x = shrink (pred x) (guess_ 10 (pred x))

-- Examples.
sorted :: [Int] -> Bool
sorted xs = xs == sort xs

sortPred :: [Int] -> [Int] -> Bool
sortPred xs ys = ys == sort xs

anyLeq :: Int -> [Int] -> Bool
anyLeq x xs = any (x <=) xs

allLeq :: Int -> [Int] -> Bool
allLeq x xs = all (x <=) xs

append :: [Int] -> [Int] -> [Int] -> Bool
append = predicate2 (++)

zipRev :: [Int] -> [Int] -> Bool
zipRev xs ys =
  zipp (reverse xs) (reverse ys) =!=
    reverse (zipp xs ys)
  where
    x =!= y =
      case teaspoon (x == y) of
        Nothing -> False
        Just x -> x

zipp [] [] = []
zipp (x:xs) (y:ys) = (x,y):zipp xs ys

lastDrop :: Int -> [Int] -> Bool
lastDrop n xs =
  case teaspoon (last (drop n xs) == last xs) of
    Nothing -> False
    Just x -> x

leq :: [Int] -> [Int] -> Bool
leq = (<=)

plus :: Int -> Int -> Int -> Bool
plus = predicate2 (+)

mult :: Int -> Int -> Int -> Bool
mult = predicate2 (*)

depthIs :: Int -> Tree () -> Bool
depthIs 0 Leaf = True
depthIs n (Node _ l r) = depthIs (n-1) l && depthIs (n-1) r
depthIs _ _ = False

predicate :: Eq b => (a -> b) -> (a -> b -> Bool)
predicate f x y = f x == y

predicate2 :: Eq c => (a -> b -> c) -> (a -> b -> c -> Bool)
predicate2 f = curry (predicate (uncurry f))

nubbed :: [Int] -> Bool
nubbed xs = nub xs == xs

noconsec :: [Int] -> Bool
noconsec xs = map head (group xs) == xs

rev :: [Int] -> Bool
rev xs = reverse xs == xs

reverse_ :: [Int] -> [Int] -> Bool
reverse_ = predicate reverse

even :: Int -> Bool
even x = x `mod` 2 == 0

-- Shows the importance of three-valued logic
nasty :: Predicate
nasty = Predicate {
  domain = replicate 2 (sample (undefined :: Int)),
  func = \[t, u] ->
    if (fromTerm t, fromTerm u) == ((0, 0) :: (Int, Int))
    then Nothing
    else Just ((fromTerm t :: Int) == (fromTerm u :: Int))
  }

main = do
  run "nasty" nasty
  run "sorted" sorted
  run "sortPred" sortPred
  run "anyLeq" anyLeq
  run "allLeq" allLeq
  run "append" append
  run "zipRev" zipRev
  run "lastDrop" lastDrop
  run "leq" leq
  run "plus" plus
  run "mult" mult
  run "depthIs" depthIs
  run "nubbed" nubbed
  run "noconsec" noconsec
  run "rev" rev
  run "reverse" reverse_
  run "even" even
  where
    run name prog = do
      putStrLn ("=== " ++ name)
      run1 prog
      putStrLn ("=== not . " ++ name)
      run1 (negate (pred prog))
    run1 prog = do
      r <- timeout 10000000 (print (guess prog))
      when (r == Nothing) $ do
        putStrLn "Timeout!"
        putStrLn ""
        putStrLn ""
