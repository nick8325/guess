-- To do:
-- When inventing a predicate p(x:y,z) -> q(x,y,z),
-- see if we can split it into q(x,y) & r(y,z).
-- Can check this by exhaustive testing.

{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Prelude hiding (elem, pred, negate)
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Data.List hiding (elem)
import Data.Maybe
import Control.Spoon
import Debug.Trace

-- Lisp terms.
data Term = Nil Type | Cons Type Term Term | Var Type Int String
  deriving (Eq, Ord)

data Type = Unit | Nat | List Type deriving (Eq, Ord)

invert :: Type -> Maybe (Type, Type)
invert Unit = Nothing
invert Nat = Just (Unit, Nat)
invert (List ty) = Just (ty, List ty)

instance Show Type where
  show Unit = "()"
  show Nat = "Nat"
  show (List ty) = "[" ++ show ty ++ "]"

termType :: Term -> Type
termType (Nil ty) = ty
termType (Cons ty _ _) = ty
termType (Var ty _ _) = ty

instance Show Term where
  showsPrec _ (Nil Unit) = showString "()"
  showsPrec _ (Nil Nat) = showString "0"
  showsPrec _ (Nil (List _)) = showString "[]"
  showsPrec n (Cons Nat x y) =
    showParen (n > 10) (showsPrec 11 y . showString "+1")
  showsPrec n (Cons (List _) x y) =
    showParen (n > 10) (showsPrec 11 x . showString ":" . showsPrec 0 y)
  showsPrec n (Cons Unit x y) =
    error "show: Cons _ _ :: Unit"
  showsPrec n (Var _ _ x) = showString x

class Lisp a where
  fromTerm :: Term -> a
  sample :: a -> Set

instance Lisp Int where
  fromTerm (Nil Nat) = 0
  fromTerm (Cons Nat (Nil Unit) x) = succ (fromTerm x)

  sample _ = listOf (nil Unit) Nat 3

instance Lisp a => Lisp [a] where
  fromTerm (Nil _) = []
  fromTerm (Cons _ x xs) = fromTerm x:fromTerm xs

  sample xs = listOf sx (List (setType sx)) 3
    where sx = sample (head xs)

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

-- Patterns.
data Pattern = Pattern {
  bound :: [Type],
  match :: Set -> Maybe [Set],
  apply :: [Term] -> Term
  }

idP :: Type -> Pattern
idP ty = Pattern {
  bound = [ty],
  match = \s -> Just [s],
  apply = \[t] -> t
  }

nilP :: Type -> Pattern
nilP ty = constP (Nil ty)

constP :: Term -> Pattern
constP t = Pattern {
  bound = [],
  match =
     \s ->
     if t `elem` s
     then Just []
     else Nothing,
  apply = \[] -> t
  }

consP :: Type -> Pattern
consP ty = Pattern {
  bound = [hd, tl],
  match =
     let match Empty{} = Nothing
         match (InsertNil _ s) = match s
         match (ConsS _ s t) = Just [s, t]
     in match,
  apply = \[t, u] -> Cons ty t u
  }
  where
    Just (hd, tl) = invert ty

patterns :: Type -> [Pattern]
patterns ty =
  idP ty:
  case invert ty of
    Nothing -> []
    Just (l, r) -> [nilP ty, consP ty]

boundPatts :: [Pattern] -> [Type]
boundPatts = concatMap bound

matchPatts :: [Pattern] -> [Set] -> [Set]
matchPatts ps ss =
  fromMaybe (map Empty (boundPatts ps))
    (fmap concat (zipWithM match ps ss))

applyPatts :: [Pattern] -> [Term] -> [Term]
applyPatts [] [] = []
applyPatts (p:ps) ts = apply p us:applyPatts ps vs
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
matchPred patts pred = Predicate {
  domain = matchPatts patts (domain pred),
  specified = specified pred . applyPatts patts,
  func = func pred . applyPatts patts
  }

-- Programs.
data Program = Program {
  args :: [Type],
  clauses :: [Clause]
  }

data Clause = Clause {
  pattern :: [Pattern],
  rhs :: [Term] -> RHS
  }

data RHS = Bot | App Target [Term] | Not RHS
data Target = Self | Call Program

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
  tell $ name ++ showArgs (applyPatts patts vs) ++ " -> "
  showRHS name (rhs vs)
  tell "\n"
  where
    vs = zipWith3 f (concatMap bound patts) [0..] vars
    f ty n name = Var ty n (twiddle ty name)
    twiddle (List ty) name = twiddle ty (name ++ "s")
    twiddle _ name = name

showRHS :: String -> RHS -> ShowM ()
showRHS _ Bot = tell "False"
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
  and [ evaluateClause p c ts | c <- cs ]

evaluateClause :: ([Term] -> Bool) -> Clause -> [Term] -> Bool
evaluateClause p (Clause patts rhs) ts =
  and [ evaluateRHS p (rhs us)
      | let ss = matchPatts patts (map singleton ts),
        us <- mapM table ss ]

evaluateRHS :: ([Term] -> Bool) -> RHS -> Bool
evaluateRHS _ Bot = False
evaluateRHS p (Not r) = not (evaluateRHS p r)
evaluateRHS p (App Self ts) = p ts
evaluateRHS _ (App (Call p) ts) = evaluate p ts

-- Predicate operators.
implements, consistentWith :: ([Term] -> Bool) -> Predicate -> Bool
f `implements` pred = and [ f ts == func pred ts | ts <- tests pred ]
f `consistentWith` pred =
  and [ not (func pred ts) || f ts | ts <- tests pred ]

extends :: ([Term] -> Bool) -> ([Term] -> Bool) -> Predicate -> Bool
extends f g pred = or [ not (f ts) && g ts | ts <- tests pred ]

except :: Predicate -> ([Term] -> Bool) -> Predicate
except pred f = Predicate {
  domain = domain pred,
  specified = \ts -> specified pred ts && f ts,
  func = func pred
  }

negate :: Predicate -> Predicate
negate pred = pred { func = not . func pred }

-- Guessing.
guess_ :: Int -> Predicate -> Program
guess_ depth pred = traceShow (length cands, args) $ Program args (refine pred [] cands)
  where
    args = predType pred
    cands = map const (candidates1 args) ++
            candidates2 depth pred

refine :: Predicate -> [Clause] -> [[Clause] -> Clause] -> [Clause]
refine pred cs cs'
  | evaluate (Program (predType pred) cs) `implements` pred = cs
refine pred cs [] = cs
refine pred cs (f:fs)
  | evalC `consistentWith` pred &&
    extends (evaluateRHS (func pred) . rhs)
            (evaluateClauses (func pred) cs)
            (matchPred patts pred) =
      refine pred (c:cs) fs
  | otherwise = refine pred cs fs
  where
    evalC = evaluateClause (func pred) c
    c@(Clause patts rhs) = f cs

candidates1 :: [Type] -> [Clause]
candidates1 args = do
  patts <- mapM patterns args
  rhs <- const Bot:
         map (App Self .) (descending args patts)
  return (Clause patts rhs)

descending :: [Type] -> [Pattern] -> [[Term] -> [Term]]
descending args patts
  | length ctx <= length args = []
  | otherwise =
    map permute . filter wellTyped .
    map uniq . map (take (length args)) . permutations $
    [0..length ctx-1]
  where
    ctx = boundPatts patts
    permute is ts = [ ts !! i | i <- is ]
    wellTyped is =
      and (zipWith (==) args [ ctx !! i | i <- is ])
    uniq = map head . group

candidates2 :: Int -> Predicate -> [[Clause] -> Clause]
candidates2 0 _ = []
candidates2 depth pred = do
  d <- [0..depth-1]
  pol <- [True, False]
  patts <- mapM patterns (predType pred)
  traceShow (d, pol) $ return (synthesise d pol patts pred)

synthesise :: Int -> Bool -> [Pattern] -> Predicate -> [Clause] -> Clause
synthesise depth pol patts pred cs =
  Clause patts (polarise Not . App (Call prog))
  where
    pred' =
      matchPred patts
        (polarise negate
         (pred `except` evaluateClauses (func pred) cs))
    polarise f = if pol then id else f
    prog = guess_ depth pred'

-- Shrinking.
shrink :: Predicate -> Program -> Program
shrink _ = id

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
guess x = shrink (pred x) (guess_ 10 (pred x))

-- Examples.
sorted :: [Int] -> Bool
sorted xs = xs == sort xs

sortPred :: [Int] -> [Int] -> Bool
sortPred xs ys = ys == sort xs

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

predicate :: Eq b => (a -> b) -> (a -> b -> Bool)
predicate f x y = f x == y

predicate2 :: Eq c => (a -> b -> c) -> (a -> b -> c -> Bool)
predicate2 f = curry (predicate (uncurry f))

main = print (guess sorted)

{-
guessBase :: Int -> Int -> Predicate -> Predicate -> [RHS]
guessBase depth constrs rec p = refine depth candidates []
  where
    refine _ _ cs
      | interpretBody (interpret rec) (And cs) `implements` p = cs
    refine 0 [] cs = cs
    refine d [] cs = refine 0 synthed cs
      where p' = p `except` interpretBody (interpret rec) (And cs)
            g d p' =
              App (guess_ d (filterP (relevant p') p'))
                (map Arg (filter (relevant p') [0..arity p-1]))
            synthed = concat [
              [ g i p', Not (g i (notP p')) ]
              | i <- [0..depth-1] ]
    refine d (c:cs) cs'
      | interpretRHS (interpret rec) c `redundantIn` interpretBody (interpret rec) (And cs') =
          refine d cs cs'
      | interpretRHS (interpret rec) c `consistentWith` p =
          refine d cs (c:cs')
      | otherwise = refine d cs cs'

    redundantIn prog prog' =
      and [ subsumed (interpret p ts) (prog ts) (prog' ts) | ts <- tests p ]
      where subsumed F F T = False
            subsumed F F X = False
            subsumed _ _ _ = True

    candidates =
      Bot:
      map Rec (sortBy (comparing (sum . map argConstrs)) tss)
      where
        tss =
          [ ts
          | vs <- permutations (zip [0..] (predType p)),
            ts <- map head . group . map (take (arity rec)) . collect $ vs,
            [ argType (predType p) t | t <- ts ] == predType rec,
            sum (map argConstrs ts) < constrs,
            arity rec > 0 ]

    collect [] = return []
    collect ((t,ty):ts) = pair ts `mplus` fmap (Arg t:) (collect ts)
      where
        pair ((u,Int):ts)
          | ty == Unit = fmap (ConsA t u Int:) (collect ts)
        pair ((u,ty'):ts)
          | ty' == List ty = fmap (ConsA t u ty':) (collect ts)
        pair _ = mzero

    argType ts (Arg x) = ts !! x
    argType ts (ConsA _ _ t) = t

    argConstrs Arg{} = 0
    argConstrs ConsA{} = 1

relevant p i = not (irrelevant p i)
irrelevant p i =
  all equal . groupBy ((==) `on` shell) .
              sortBy (comparing shell) . tests $ p
  where
    shell ts = take i ts ++ drop (i+1) ts
    equal tss = and (zipWith (==) xs (tail xs))
      where xs = filter (/= X) (map (interpret p) tss)

shrink :: Predicate -> Program -> Program
shrink pred p =
  case [ p' | p' <- candidates p, interpretProg p' `implements` pred ] of
    [] -> p
    (p':_) -> shrink pred p'

candidates (Program ts x) = map (Program ts) (candidatesBody x)

candidatesBody (Case n l r) =
  [ Case n l' r | l' <- candidatesBody l ] ++
  [ Case n l r' | r' <- candidatesBody r ]
candidatesBody (And rs) = map And (candidatesRHSs rs)

candidatesRHSs [] = []
candidatesRHSs (r:rs) =
  rs:
  map (:rs) (candidatesRHS r) ++
  map (r:) (candidatesRHSs rs)

candidatesRHS Bot = []
candidatesRHS (App prog ts) =
  Bot:[ App prog' ts | prog' <- candidates prog ]
candidatesRHS _ = [Bot]
-}
