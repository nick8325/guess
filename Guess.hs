-- To do:
-- When inventing a predicate p(x:y,z) -> q(x,y,z),
-- see if we can split it into q(x,y) & r(y,z).
-- Can check this by exhaustive testing.
--
-- Perhaps remove X and instead just remove the Xs from the domain.

{-# LANGUAGE ScopedTypeVariables #-}
module Main where

import Prelude hiding (pred)
import Control.Monad
import Data.Maybe
import Data.List
import Data.Ord
import Control.Monad.State
import Control.Monad.Writer
import Data.Function

data Term = Nil Type | Cons Term Term Type | Var String deriving (Eq, Ord)
data Type = Unit | Int | List Type deriving (Eq, Ord)

uncons :: Type -> (Type, Type)
uncons Int = (Unit, Int)
uncons Unit = error "uncons: Unit"
uncons (List x) = (x, List x)

instance Show Term where
  showsPrec _ (Nil Unit) = showString "()"
  showsPrec _ (Nil Int) = showString "0"
  showsPrec _ (Nil (List _)) = showString "[]"
  showsPrec n (Cons x y Int) =
    showParen (n > 10) (showsPrec 11 y . showString "+1")
  showsPrec n (Cons x y (List _)) =
    showParen (n > 10) (showsPrec 11 x . showString ":" . showsPrec 0 y)
  showsPrec n (Cons x y Unit) =
    error "show: Cons _ _ :: Unit"
  showsPrec n (Var x) = showString x

class Lisp a where
  term :: a -> Term
  back :: Term -> a

  lispType :: a -> Type
  sample :: [a]

instance Lisp Int where
  term 0 = Nil Int
  term n = Cons (Nil Unit) (term (n-1)) Int

  back (Nil Int) = 0
  back (Cons (Nil Unit) x Int) = succ (back x)

  lispType _ = Int
  sample = [0..3]

instance Lisp a => Lisp [a] where
  term xs@[] = Nil (lispType xs)
  term (x:xs) = Cons (term x) (term xs) (lispType xs)

  back (Nil _) = []
  back (Cons x xs _) = back x:back xs

  lispType xs = List (lispType (head xs))
  sample = concat [ sequence (replicate i sample) | i <- [0..4] ]

data Predicate = Predicate {
  predType :: [Type],
  tests :: [[Term]],
  interpret :: [Term] -> Range
  }

arity :: Predicate -> Int
arity = length . predType

instance Show Predicate where
  show p =
    unlines $
      ["{"] ++
      [ intercalate ", " (map show ts) ++ " -> " ++ show (interpret p ts) | ts <- tests p, interpret p ts /= X ] ++
      ["}"]

nil :: Int -> Predicate -> Predicate
nil n p = Predicate {
  predType = take n (predType p) ++ drop (n+1) (predType p),
  tests = [ take n ts ++ drop (n+1) ts
          | ts <- tests p,
            Nil _ <- [ts !! n] ],
  interpret = \ts -> interpret p $
                     take n ts ++ [Nil xt] ++ drop n ts
  }
  where xt = predType p !! n

cons :: Int -> Predicate -> Predicate
cons n p = Predicate {
  predType =
     let (x, y) = uncons (predType p !! n)
     in take n (predType p) ++ [x, y] ++ drop (n+1) (predType p),
  tests = [ take n ts ++ [x,y] ++ drop (n+1) ts
          | ts <- tests p,
            Cons x y _ <- [ts !! n] ],
  interpret = \ts -> interpret p $
                      take n ts ++ [Cons (ts !! n) (ts !! (n+1)) xt] ++
                      drop (n+2) ts
  }
  where xt = predType p !! n

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

type ShowM = StateT ShowState (Writer String)
data ShowState = ShowState {
  names :: [String],
  queue :: [(String, Program)]
  }

instance Show Program where
  show p =
    execWriter (execStateT showProgram (ShowState (tail preds) [(head preds, p)]))

showProgram :: ShowM ()
showProgram = do
  ShowState ns q <- get
  case q of
    [] -> return ()
    ((n,Program ty p):ps) -> do
      put (ShowState ns ps)
      showBody n (map VarP ty) p >>= (tell . (++ "\n\n"))
      showProgram

preds, vars :: [String]
preds = infinite ['p','q','r','s']
vars = infinite $ ['x','y','z','w','t','u','v']
infinite xs = concat [ replicateM n xs | n <- [1..] ]

data Pattern = NilP Type | ConsP Type | VarP Type

splice :: (Type -> Pattern) -> Int -> [Pattern] -> [Pattern]
splice p n (NilP ty:ps) = NilP ty:splice p n ps
splice p n (ConsP ty:ps) | n >= 2 = ConsP ty:splice p (n-2) ps
splice p 0 (VarP ty:ps) = p ty:ps
splice p n (VarP ty:ps) = VarP ty:splice p (n-1) ps

showBody :: String -> [Pattern] -> Body -> ShowM String
showBody n ctx (And []) =
  liftM2 (++) (showHead n vars ctx) (return " = True")
showBody n ctx (And rhss) = do
  head <- showHead n vars ctx
  xs <- mapM (showRHS n vars) rhss
  return (head ++ " = " ++ intercalate " && " xs)
showBody n ctx (Case v nil cons) = do
  nil' <- showBody n (splice NilP v ctx) nil
  cons' <- showBody n (splice ConsP v ctx) cons
  return (nil' ++ "\n" ++ cons')

showHead :: String -> [String] -> [Pattern] -> ShowM String
showHead n _ [] = return n
showHead n vs ps = return (n ++ "(" ++ intercalate "," (map show (aux vs ps)) ++ ")")
  where aux vs [] = []
        aux vs (NilP ty:ps) = Nil ty:aux vs ps
        aux (v:vs) (VarP ty:ps) = Var v:aux vs ps
        aux (v:w:vs) (ConsP ty:ps) = Cons (Var v) (Var w) ty:aux vs ps

showRHS :: String -> [String] -> RHS -> ShowM String
showRHS n vs (Not prog) = fmap ('~':) (showRHS n vs prog)
showRHS n vs (App prog ts) = do
  ShowState (n':ns) ps <- get
  put (ShowState ns (ps ++ [(n', prog)]))
  case ts of
    [] -> return n'
    _ -> return (n' ++ "(" ++ intercalate "," [ showArg vs t | t <- ts ] ++ ")")
showRHS n vs (Rec ts) =
  case ts of
    [] -> return n
    _ -> return (n ++ "(" ++ intercalate "," [ showArg vs t | t <- ts ] ++ ")")
showRHS n vs Bot = return "False"

showArg :: [String] -> Arg -> String
showArg vs (ConsA x y t) = show (Cons (Var (vs !! x)) (Var (vs !! y)) t)
showArg vs (Arg x) = vs !! x

guess_ :: Predicate -> Program
guess_ p = Program (predType p) (aux 0 p)
  where
    aux n p'
      | n >= arity p' = And (guessBase p p')
      | irrelevant p' n = aux (n+1) p'
      | otherwise = Case n (aux n (nil n p'))
                           (aux (n+2) (cons n p'))

guessBase :: Predicate -> Predicate -> [RHS]
guessBase rec p = refine candidates []
  where
    refine _ cs
      | interpretBody (interpret rec) (And cs) `implements` p = cs
    refine [] cs =
      refine (Not
              (App (guess_ (filterP (relevant p') p'))
               (map Arg (filter (relevant p') [0..arity p-1]))):cs) []
      where p' = notP (p `except` interpretBody (interpret rec) (And cs))
    refine (c:cs) cs'
      | interpretRHS (interpret rec) c `redundantIn` interpretBody (interpret rec) (And cs') =
          refine cs cs'
      | interpretRHS (interpret rec) c `consistentWith` p =
          refine cs (c:cs')
      | otherwise = refine cs cs'

    redundantIn prog prog' =
      and [ subsumed (interpret p ts) (prog ts) (prog' ts) | ts <- tests p ]
      where subsumed F F T = False
            subsumed F F X = False
            subsumed _ _ _ = True

    candidates =
      Bot:
      map Rec (sortBy (comparing (length . map argVars)) tss)
      where
        tss =
          [ ts
          | vs <- permutations (zip [0..] (predType p)),
            ts <- map head . group . map (take (arity rec)) . collect $ vs,
            [ argType (predType p) t | t <- ts ] == predType rec,
            sum (map argVars ts) < arity p,
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

    argVars Arg{} = 1
    argVars ConsA{} = 2

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

guess :: Pred a => a -> Program
guess x = guess_ (pred x)

sorted :: [Int] -> Bool
sorted xs = xs == sort xs

sortPred :: [Int] -> [Int] -> Bool
sortPred xs ys = ys == sort xs

allLeq :: Int -> [Int] -> Bool
allLeq x xs = all (x <=) xs

append :: [Int] -> [Int] -> [Int] -> Bool
append xs ys zs = xs ++ ys == zs

main = print (guess sorted)
