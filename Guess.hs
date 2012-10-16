-- To do:
-- When inventing a predicate p(x:y,z) -> q(x,y,z),
-- see if we can split it into q(x,y) & r(y,z).
-- Can check this by exhaustive testing.
--
-- Allow variables to appear twice in patterns (equality).
--
-- Synthesise predicates using a subset of all available variables.
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

{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Prelude hiding (elem, pred, negate)
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Data.List hiding (elem)
import Data.Maybe
import Data.Function
import Data.Ord
import Control.Spoon
import Debug.Trace

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
    showParen (n > 10) (showsPrec 11 x . showString ":" . showsPrec 0 y)
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
  specified :: [Term] -> Bool,
  func :: [Term] -> Bool
  }

predType :: Predicate -> [Type]
predType = map setType . domain

tests :: Predicate -> [[Term]]
tests pred = [ ts | ts <- mapM table (domain pred), specified pred ts ]

matchPred :: [Pattern] -> Predicate -> Predicate
matchPred patts pred =
  case matchPatts patts (domain pred) of
    Just domain ->
      Predicate {
        domain = domain,
        specified = specified pred . undoPatts patts,
        func = func pred . undoPatts patts
        }
    Nothing ->
      Predicate {
        domain = map Empty (predType pred),
        specified = const False,
        func = const True
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

data RHS = Top | App Target [Term] | Not RHS deriving Show
data Target = Self | Call Program deriving Show

rhsOrder Top = 0
rhsOrder (Not r) = 1+rhsOrder r
rhsOrder App{} = 2

type ShowM = StateT ShowState (Writer String)
data ShowState = ShowState {
  names :: [String],
  queue :: [(String, Program)]
  }

preds, vars :: [String]
preds = infinite ['p','q','r','s']
vars = infinite $ ['x','y','z','w','t','u','v']
infinite xs = concat [ replicateM n xs | n <- [1..] ]

instance Show Program where
  show p =
    execWriter (execStateT (loop showProgram) (ShowState (tail preds) [(head preds, p)]))

loop :: (String -> Program -> ShowM ()) -> ShowM ()
loop f = do
  ShowState ns q <- get
  case q of
    [] -> return ()
    ((n,p):ps) -> do
      put (ShowState ns ps)
      f n p
      loop f

showProgram :: String -> Program -> ShowM ()
showProgram name (Program args cs) = do
  tell $
    name ++ " :: " ++
    concat [ show ty ++ " -> " | ty <- args ] ++ "Bool\n"
  mapM_ (showClause name) cs
  tell "\n"

showClause :: String -> Clause -> ShowM ()
showClause name (Clause patts rhs) = do
  tell $ name ++ showArgs (undoPatts patts vs) ++ " -> "
  showRHS name rhs
  tell "\n"
  where
    vs = zipWith Var (concatMap bound patts) [0..]

showRHS :: String -> RHS -> ShowM ()
showRHS _ Top = tell "True"
showRHS name (Not x) = do
  tell "~"
  showRHS name x
showRHS name (App f ts) = do
  showTarget name f
  tell (showArgs ts)

showTarget :: String -> Target -> ShowM ()
showTarget name Self = tell name
showTarget _ (Call prog) = do
  ShowState (name:names) progs <- get
  put (ShowState names (progs ++ [(name, prog)]))
  tell name

showArgs :: [Term] -> String
showArgs [] = ""
showArgs ts = " (" ++ intercalate ", " (map show ts) ++ ")"

-- Evaluation.
evaluate :: Program -> [Term] -> Bool
evaluate p@(Program _ cs) ts = evaluateClauses (evaluate p) cs ts

evaluateClauses :: ([Term] -> Bool) -> [Clause] -> [Term] -> Bool
evaluateClauses p cs ts =
  or [ evaluateClause p c ts | c <- cs ]

evaluateClause :: ([Term] -> Bool) -> Clause -> [Term] -> Bool
evaluateClause p (Clause patts rhs) ts =
  or [ evaluateRHS p rhs us
      | Just ss <- [matchPatts patts (map singleton ts)],
        us <- mapM table ss ]

evaluateRHS :: ([Term] -> Bool) -> RHS -> [Term] -> Bool
evaluateRHS _ Top _ = True
evaluateRHS p (Not r) ts = not (evaluateRHS p r ts)
evaluateRHS p (App Self ts) us = p (map (subst us) ts)
evaluateRHS _ (App (Call p) ts) us = evaluate p (map (subst us) ts)

subst :: [Term] -> Term -> Term
subst ts (Var _ i) = ts !! i
subst ts (Cons ty t u) = Cons ty (subst ts t) (subst ts u)
subst ts n@Nil{} = n

-- Predicate operators.
implements, consistentWith :: ([Term] -> Bool) -> Predicate -> Bool
f `implements` pred = and [ f ts == func pred ts | ts <- tests pred ]
f `consistentWith` pred =
  and [ func pred ts || not (f ts) | ts <- tests pred ]

extends :: ([Term] -> Bool) -> ([Term] -> Bool) -> Predicate -> Bool
extends f g pred = or [ f ts && not (g ts) | ts <- tests pred ]

except :: Predicate -> ([Term] -> Bool) -> Predicate
except pred f = Predicate {
  domain = domain pred,
  specified = \ts -> specified pred ts && not (f ts),
  func = func pred
  }

negate :: Predicate -> Predicate
negate pred = pred { func = not . func pred }

-- Guessing.
guess_ :: Int -> Predicate -> Program
guess_ depth pred = Program args (refine pred [] cands)
  where
    args = predType pred
    cands = map const (candidates1 args) ++
            candidates2 depth pred

refine :: Predicate -> [Clause] -> [[Clause] -> Clause] -> [Clause]
refine pred cs cs'
  | evaluate (Program (predType pred) cs) `implements` pred = cs
refine pred cs [] = cs
refine pred cs (f:fs)
  | not (cs' `implements` pred') &&
    rhs' `consistentWith` pred' &&
    extends rhs' cs' pred' =
      refine pred (c:cs) fs
  | otherwise = refine pred cs fs
  where
    c@(Clause patts rhs) = f cs
    pred' = matchPred patts pred
    rhs' = evaluateRHS (func pred) rhs
    cs' = evaluateClauses (func pred) cs . undoPatts patts

candidates1 :: [Type] -> [Clause]
candidates1 args = sortBy (comparing clauseOrder) $ do
  patts <- mapM patterns args
  rhs <- Top:
         map (App Self) (descending args patts)
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

candidates2 :: Int -> Predicate -> [[Clause] -> Clause]
candidates2 0 _ = []
candidates2 depth pred = do
  -- d <- [0..depth-1]
  -- pol <- [True, False]
  let pol = False
      d = depth-1
  patts <- sortBy (comparing patternsOrder) $ mapM patterns (predType pred)
  guard (not (all trivial patts))
  let polarise f = if pol then id else f
  return
    (\cs ->
      Clause patts
       (polarise Not
        (synthesise d
         (matchPred patts
          (polarise negate
           (pred `except` evaluateClauses (func pred) cs))))))

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
candidateRHSs (App Self ts) = [Top]
candidateRHSs (App (Call prog) ts) =
  Top:[ App (Call prog') ts | prog' <- candidates prog ]

-- A nicer interface.
class Pred a where
  domain_ :: a -> [Set]
  specified_ :: a -> [Term] -> Bool
  func_ :: a -> [Term] -> Bool

instance Pred Bool where
  domain_ _ = []
  specified_ _ [] = True
  func_ x [] = x

instance (Lisp a, Pred b) => Pred (a -> b) where
  domain_ f = sample x:domain_ (f x)
    where x = undefined :: a
  specified_ f (x:xs) = specified_ (f (fromTerm x)) xs
  func_ f (x:xs) = func_ (f (fromTerm x)) xs

pred :: Pred a => a -> Predicate
pred x = Predicate {
  domain = domain_ x,
  specified = specified_ x,
  func = func_ x
  }

guess :: Pred a => a -> Program
guess x =
  let prog = guess_ 10 (pred x)
  in if evaluate prog `implements` pred x
     then shrink (pred x) prog
     else error "guess failed"

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

even :: Int -> Bool
even x = x `mod` 2 == 0

main = print (guess sorted)
