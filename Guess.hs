-- To do:
-- When inventing a predicate p(x:y,z) -> q(x,y,z),
-- see if we can split it into q(x,y) & r(y,z).
-- Can check this by exhaustive testing.
--
-- Perhaps remove X and instead just remove the Xs from the domain.

{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Prelude hiding (elem)
import Control.Monad
import Control.Monad.State
import Control.Monad.Writer
import Data.List hiding (elem)
-- import Prelude hiding (pred)
-- import Control.Monad
-- import Data.Maybe
-- import Data.List
-- import Data.Ord
-- import Control.Monad.State
-- import Control.Monad.Writer
-- import Data.Function
-- import Control.Spoon

-- Lisp terms.
data Term = Nil Type | Cons Type Term Term | Var Type String
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
termType (Var ty _) = ty

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
  showsPrec n (Var _ x) = showString x

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

listOf :: Set -> Type -> Int -> Set
listOf x ty 0 = nil ty
listOf x ty n = InsertNil ty (ConsS ty x (listOf x ty (n-1)))

-- Patterns.
data Pattern = Pattern {
  bound :: [Type],
  match :: Set -> Maybe [Set],
  apply :: [Term] -> Term
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

matchPatts :: [Pattern] -> [Set] -> Maybe [Set]
matchPatts ps ss = fmap concat (zipWithM match ps ss)

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

matchPred :: [Pattern] -> Predicate -> Maybe Predicate
matchPred patts pred = do
  domain <- matchPatts patts (domain pred)
  return Predicate {
    domain = domain,
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
  tell (concat [ show ty ++ " -> " | ty <- args ] ++ "Bool")
  mapM_ (showClause name) cs
  tell "\n"

showClause :: String -> Clause -> ShowM ()
showClause name (Clause patts rhs) = do
  tell $ name ++ showArgs (applyPatts patts vs) ++ " -> "
  showRHS name (rhs vs)
  tell "\n"
  where
    vs = zipWith Var (concatMap bound patts) vars

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
showArgs ts = "(" ++ intercalate "," (map show ts) ++ ")"

{-

notP :: Predicate -> Predicate
notP p = p { interpret = notR . interpret p }

filterP :: (Int -> Bool) -> Predicate -> Predicate
filterP rel p = Predicate {
  predType = [ predType p !! i | i <- rels ],
  tests = [ [ ts !! i | i <- rels ] | ts <- tests p ],
  interpret = \ts -> interpret p $
                      foldr update arb (zip rels ts)
  }
  where rel' x = x `elem` rels
        rels = [ i | i <- [0..arity p-1], rel i ]
        update (i, x) ts = take i ts ++ [x] ++ drop (i+1) ts
        arb = head (tests p)

data Range = F | X | T deriving (Eq, Show)

F `andR` _ = F
_ `andR` F = F
T `andR` T = T
_ `andR` _ = X

notR T = F
notR F = T
notR X = X

implements, consistentWith :: ([Term] -> Range) -> Predicate -> Bool
f `implements` p =
  and [ f ts `describes` interpret p ts | ts <- tests p ]
  where
    _ `describes` X = True
    x `describes` y = x == y

f `consistentWith` p =
  and [ f ts `follows` interpret p ts | ts <- tests p ]
  where
    T `follows` _ = True
    _ `follows` X = True
    F `follows` F = True
    _ `follows` _ = False

except :: Predicate -> ([Term] -> Range) -> Predicate
p `except` f = Predicate {
  predType = predType p,
  tests = tests p,
  interpret = \ts -> interpret p ts `exceptR` f ts
  }
  where
    F `exceptR` F = X
    F `exceptR` _ = F
    T `exceptR` _ = T
    X `exceptR` _ = X

data Program = Program [Type] Body

data Body
  = Case Int Body Body
  | And [RHS]

data RHS = Not RHS | App Program [Arg] | Rec [Arg] | Bot

data Arg = Arg Int | ConsA Int Int Type deriving Eq
guess_ :: Int -> Predicate -> Program
guess_ d p = Program (predType p) (aux 0 0 p)
  where
    aux n m p'
      | n >= arity p' = And (guessBase d m p p')
      | irrelevant p' n = aux (n+1) m p'
      | otherwise = Case n (aux n m (nil n p'))
                           (aux (n+2) (m+1) (cons n p'))

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

interpretBody :: ([Term] -> Range) -> Body -> [Term] -> Range
interpretBody rec (And rhss) ts =
  foldr andR T [ interpretRHS rec rhs ts | rhs <- rhss ]
interpretBody rec (Case i n c) ts =
  case ts !! i of
    Nil _ -> interpretBody rec n (take i ts ++ drop (i+1) ts)
    Cons x xs _ ->
      interpretBody rec c (take i ts ++ [x, xs] ++ drop (i+1) ts)

interpretProg :: Program -> [Term] -> Range
interpretProg (Program _ body) = x
  where x = interpretBody x body

interpretRHS :: ([Term] -> Range) -> RHS -> [Term] -> Range
interpretRHS p Bot _ = F
interpretRHS p (Not prog) ts =
  notR (interpretRHS p prog ts)
interpretRHS p (App prog vs) ts =
  interpretProg prog [ interpretArg ts v | v <- vs ]
interpretRHS p (Rec vs) ts =
  p [ interpretArg ts v | v <- vs ]

interpretArg ts (Arg v) = ts !! v
interpretArg ts (ConsA x y t) = Cons (ts !! x) (ts !! y) t

class Pred a where
  predType_ :: a -> [Type]
  tests_ :: a -> [[Term]]
  interpret_ :: a -> [Term] -> Range

instance Pred Bool where
  predType_ _ = []
  tests_ _ = [[]]
  interpret_ False [] = F
  interpret_ True [] = T

instance (Lisp a, Pred b) => Pred (a -> b) where
  predType_ (f :: a -> b) = lispType (undefined :: a):predType_ (undefined :: b)
  tests_ (f :: a -> b) = liftM2 (:) (map term (sample :: [a])) (tests_ (undefined :: b))
  interpret_ f (x:xs) =
    interpret_ (f (back x)) xs

pred :: Pred a => a -> Predicate
pred x = Predicate {
  predType = predType_ x,
  tests = tests_ x,
  interpret = interpret_ x
  }

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

guess :: Pred a => a -> Program
guess x = shrink (pred x) (guess_ 10 (pred x))

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

main = print (guess ((<=) :: [Int] -> [Int] -> Bool))
-}
main = undefined