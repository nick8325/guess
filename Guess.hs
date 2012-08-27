module Guess where

import Control.Monad
import Data.Maybe
import Data.List
import Data.Ord
import Control.Spoon
import Control.Monad.State
import Control.Monad.Writer

data Term = Nil | Cons Term Term deriving Eq

instance Show Term where
  showsPrec _ Nil = showString "Nil"
  showsPrec n (Cons x y) =
    showParen (n > 10) (showsPrec 11 x . showString ":" . showsPrec 0 y)

class Lisp a where
  term :: a -> Term
  back :: Term -> a

instance Lisp Int where
  term 0 = Nil
  term n = Cons Nil (term (n-1))

  back Nil = 0
  back (Cons Nil x) = succ (back x)

instance Lisp a => Lisp [a] where
  term [] = Nil
  term (x:xs) = Cons (term x) (term xs)

  back Nil = []
  back (Cons x xs) = back x:back xs

data Predicate = Predicate {
  arity :: Int,
  tests :: [[Term]],
  interpret_ :: [Term] -> Range
  }

instance Show Predicate where
  show p =
    unlines $
      ["{"] ++
      [ intercalate ", " (map show ts) ++ " -> " ++ show (interpret p ts) | ts <- tests p ] ++
      ["}"]

interpret :: Predicate -> [Term] -> Range
interpret p ts = fromMaybe X (teaspoon (interpret_ p ts))

nil :: Int -> Predicate -> Predicate
nil n p = Predicate {
  arity = arity p - 1,
  tests = [ take n ts ++ drop (n+1) ts | ts <- tests p, ts !! n == Nil ],
  interpret_ = \ts -> interpret p $
                     take n ts ++ [Nil] ++ drop n ts
  }

cons :: Int -> Predicate -> Predicate
cons n p = Predicate {
  arity = arity p + 1,
  tests = [ take n ts ++ [x,y] ++ drop (n+1) ts
          | ts <- tests p,
            Cons x y <- [ts !! n] ],
  interpret_ = \ts -> interpret p $
                      take n ts ++ [Cons (ts !! n) (ts !! (n+1))] ++
                      drop (n+2) ts
  }

filterP :: (Int -> Bool) -> Predicate -> Predicate
filterP rel p = Predicate {
  arity = length rels,
  tests = [ [ ts !! i | i <- rels ] | ts <- tests p ],
  interpret_ = \ts -> interpret p $
                      foldr update arb (zip rels ts)
  }
  where rel' x = x `elem` rels
        rels = [ i | i <- [0..arity p-1], rel i ]
        update (i, x) ts = take i ts ++ [x] ++ drop (i+1) ts
        arb = head (tests p)

data Range = F | X | T deriving (Eq, Show)

fromBool :: Bool -> Range
fromBool False = F
fromBool True = T

F `andR` _ = F
_ `andR` F = F
T `andR` T = T
_ `andR` _ = X

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
  arity = arity p,
  tests = tests p,
  interpret_ = \ts -> interpret p ts `exceptR` f ts
  }
  where
    F `exceptR` F = X
    F `exceptR` _ = F
    T `exceptR` _ = T
    X `exceptR` _ = X

data Program = Program Int Body

data Body
  = Case Int Body Body
  | And [RHS]

data RHS = App Program [Int] | Rec [Int] | Bot deriving Show

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
    ((n,Program a p):ps) -> do
      put (ShowState ns ps)
      showBody n (replicate a VarP) p >>= (tell . (++ "\n"))
      showProgram

preds, vars :: [String]
preds = infinite ["p","q","r","s"]
vars = infinite $ ["x","y","z","w","t","u","v"]
infinite xs = xs ++ [ x ++ y | x <- xs, y <- infinite xs ]

data Pattern = NilP | ConsP | VarP

splice :: Pattern -> Int -> [Pattern] -> [Pattern]
splice p n (NilP:ps) = NilP:splice p n ps
splice p n (ConsP:ps) | n >= 2 = ConsP:splice p (n-2) ps
splice p 0 (VarP:ps) = p:ps
splice p n (VarP:ps) = VarP:splice p (n-1) ps

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
showHead n vs ps = return (n ++ "(" ++ intercalate "," (aux vs ps) ++ ")")
  where aux vs [] = []
        aux vs (NilP:ps) = "[]":aux vs ps
        aux (v:vs) (VarP:ps) = v:aux vs ps
        aux (v:w:vs) (ConsP:ps) = (v ++ ":" ++ w):aux vs ps

showRHS :: String -> [String] -> RHS -> ShowM String
showRHS n vs (App prog ts) = do
  ShowState (n':ns) ps <- get
  put (ShowState ns (ps ++ [(n', prog)]))
  case ts of
    [] -> return n'
    _ -> return (n' ++ "(" ++ intercalate "," [ vs !! t | t <- ts ] ++ ")")
showRHS n vs (Rec ts) =
  case ts of
    [] -> return n
    _ -> return (n ++ "(" ++ intercalate "," [ vs !! t | t <- ts ] ++ ")")
showRHS n vs Bot = return "False"

guess :: Predicate -> Program
guess p = Program (arity p) (aux 0 p)
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
      refine (App (guess (filterP (relevant p') p'))
              (filter (relevant p') [0..arity p-1]):cs) []
      where p' = p `except` interpretBody (interpret rec) (And cs)
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
      [ Rec vs
      | vs <- map head . group . map (take (arity rec)) . permutations $ [0..arity p-1],
        length vs == arity rec,
        arity rec > 0 ]

relevant p i = not (irrelevant p i)
irrelevant p i =
  and [ interpret p ts `elem` [X, interpret p ts']
      | ts <- tests p,
        let ts' = take i ts ++ [Nil] ++ drop (i+1) ts ]

interpretBody :: ([Term] -> Range) -> Body -> [Term] -> Range
interpretBody rec (And rhss) ts =
  foldr andR T [ interpretRHS rec rhs ts | rhs <- rhss ]
interpretBody rec (Case i n c) ts =
  case ts !! i of
    Nil -> interpretBody rec n (take i ts ++ drop (i+1) ts)
    Cons x xs ->
      interpretBody rec c (take i ts ++ [x, xs] ++ drop (i+1) ts)

interpretProg :: Program -> [Term] -> Range
interpretProg (Program _ body) = x
  where x = interpretBody x body

interpretRHS :: ([Term] -> Range) -> RHS -> [Term] -> Range
interpretRHS p Bot _ = F
interpretRHS p (App prog vs) ts =
  interpretProg prog [ ts !! v | v <- vs ]
interpretRHS p (Rec vs) ts =
  p [ ts !! v | v <- vs ]

ints :: [Term]
ints = map term [0..4 :: Int]

lists :: [Term]
lists = concat [ map term (sequence (replicate i [0..4 :: Int])) | i <- [0..4] ]

leq :: Predicate
leq = Predicate {
  arity = 2,
  tests = sequence [ints, ints],
  interpret_ = \[x, y] -> fromBool $ (back x :: [Int]) <= back y
  }

sorted :: Predicate
sorted = Predicate {
  arity = 1,
  tests = sequence [lists],
  interpret_ = \[xs] ->
    let xs' = back xs :: [Int] in
    fromBool (sort xs' == xs')
  }

test, test2 :: Program
test = guess leq
test2 = guess sorted
