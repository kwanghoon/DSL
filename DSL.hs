-- An Embedded DSL for Parallel Reductions
--
-- Copyright (C) 2012 Kwanghoon Choi 
--
-- This module offers a very simple DSL allowing one to write a specification
-- of parallel reduction. Each DSL program is compiled by the module to generate
-- a parallelizable function in Haskell. 

-- TODO:
--  * Collaborate with the Monad-Par library
--  * Nice demo examples (Currently, we have only two examples.)

module DSL where

import List
import Maybe
import Debug.Trace

{- Generic Combinator Declarations -}
type Name     = String
type TypeName = String

type CombDecl = (TypeName, [(Name, [TypeName])])

-- A declaration of the SKI combinators
--   C ::= S | K | I | App C C

-- Example
--   ("C", [("S", []), ("K", []), ("I", []), ("@", ["C", "C"])])

c   = "C"
s   = "S"
k   = "K"
i   = "I"
app = "@"

skiCombDecl = (c, [(s, []), (k, []), (i, []), (app, [c, c])])

-- A declaration of the Insertion Sort combinators
--   I ::= Ins Int  I | Con Int I | Nil

ins = "Ins"
con = "Con"
nil = "Nil"
int = "Int"

insCombDecl = (i, [(ins, [int, i]), (con, [int, i]), (nil, [])])

-- Example
--  Ins 4 (Ins 2 (Ins 1 (Ins 3 Nil)))

expINS =
  Comb ins proc
    [ Const "4"
    , Comb ins proc 
      [ Const "2"
      , Comb ins proc
        [ Const "1"
        , Comb ins proc
          [ Const "3"
          , Comb nil proc []
          ]
        ]
      ] 
    ]

-- The pointer jumping combinators
--   D ::= P Int D | Nil

d = "D"
p = "P"

ptrCombDecl = (d, [(p, [int, d]), (nil, [])])

-- Example
--   P 1 (P 2 (P 3 (P 4 (P 5 (P 6 Nil)))))

expPTR =
  Comb p proc
    [ Const "1"
    , Comb p proc
      [ Const "2"
      , Comb p proc
        [ Const "3"
        , Comb p proc
          [ Const "4"
          , Comb p proc
            [ Const "5"
            , Comb p proc
              [ Const "6"
              , Comb nil proc []
              ]]]]]]

{- Generic Parallel Reduction Rules -}

type Judgment    = (Pat, Exp)
type ParRedRule  = ([Judgment], Judgment)
type ParRedRules = [ParRedRule]

data Pat = PVar  Name Kind       -- Variable Pattern
         | PComb Name Kind [Pat] -- Combinator Pattern
           deriving Show
                    
{-
A set of parallel reduction for the SKI combinators

       x => x'
  -----------------
  @ (@ K x) y => x'

     x => x'
  ------------
  @ I x => x'

         f => f'  g => g'  x => x'
 ------------------------------------------
 @ (@ (@ S f) g) x => @ (@ f' x') (@ g' x')

 S => S  K => K  I => I
 
 f => f'  x => x'
 ----------------
 @ f x => @ f' x'
-}

x  = PVar "x" proc
y  = PVar "y" proc
f  = PVar "f" proc
g  = PVar "g" proc

x' = Var "x'" proc
y' = Var "y'" proc
f' = Var "f'" proc
g' = Var "g'" proc

proc = Proc
val  = Val

patS   = PComb s proc []
patK   = PComb k proc [] 
patI   = PComb i proc [] 
patApp = PComb app proc

expS   = Comb s proc [] 
expK   = Comb k proc [] 
expI   = Comb i proc [] 
expApp = Comb app proc

skiRules :: ParRedRules
skiRules =
  [ ([(x, x')], (patApp [patApp [patK, x], y], x'))
  , ([(x, x')], (patApp [patI, x], x'))
  , ([(f, f'), (g, g'), (x, x')], (patApp [patApp [patApp [patS, f], g], x],
                 expApp [expApp [f', x'], expApp [g', x']]))
  , ([], (patS, expS))
  , ([], (patK, expK))
  , ([], (patI, expI))
  , ([(f, f'), (x, x')], (patApp [f, x], expApp [f', x']))
  ]
  
{-
A set of parallel reduction for the insertion sorting combinators:

                    l => l'
---------------------------------------------------
Ins a (Con b l) => Con (min a b) (Ins (max a b) l')


Ins a Nil => Con a Nil


      l => l'
-------------------
Ins a l => Ins a l'

      l => l'
-------------------
Con a l => Con a l'


Nil => Nil
-}

l    = PVar "l" proc
pata = PVar "a" val
patb = PVar "b" val
  
l'   = Var "l'" proc
vara = Var "a"  val  -- Same as a
varb = Var "b"  val  -- Same as b

insRules :: ParRedRules
insRules =
  [ ( [(l, l')]
    , ( PComb ins proc [pata, PComb con proc [patb, l]]
      , Comb con proc [ Prim "min" [vara, varb]
                 , Comb ins proc [Prim "max" [vara, varb], l']
                 ]
      )
    )
  , ( []
    , ( PComb ins proc [pata, PComb nil proc []]
      , Comb con proc [vara, Comb nil proc []]
      )
    )
  , ( [(l, l')]
    , ( PComb ins proc [pata, l]
      , Comb ins proc [vara, l']
      )
    )
  , ( [(l, l')]
    , ( PComb con proc [pata, l]
      , Comb con proc [vara, l']
      )
    )
  , ( []
    , ( PComb nil proc []
      , Comb nil proc []
      )
    )
  ]

{-  
A set of parallel reduction for the pointer jumping:

Nil => Nil

P a Nil => P a Nil

          l => l'
-------------------------
P a (P b l) => P (a+b) l'

Note. The order of the rules is important.
-}

ptrRules :: ParRedRules
ptrRules =
  [ 
    (  [], (PComb nil proc [], Comb nil proc [])),
    (  [], (PComb p proc [pata, PComb nil proc []], Comb p proc [vara, Comb nil proc []])),
    (  [(l, l')], 
       (PComb p proc 
           [pata, 
            PComb p proc 
              [patb, l]
           ], Comb p proc [Prim "+" [vara, varb], l']) )
  ]
  
{- Expression -}

data Exp = Comb Name Kind [Exp] -- Combinator 
         | Var Name Kind
         | If Exp Exp Exp 
         | Let Name Exp Exp 
         | Prim Name [Exp]
         | Const Name
           deriving Eq
           
data Kind = Proc | Val deriving (Eq, Show) -- Either a processor or a value


instance Show Exp where
  showsPrec t (Comb n k es) = (++) n 
                            . (++) "(" 
                            . foldr (.) id (intersperse ((++) ",") (map (showsPrec t) es))
                            . (++) ")"
  showsPrec t (Var n k) = (++) n
  showsPrec t (If ce et ee) = (++) "if " 
                              . showsPrec t ce 
                              . (++) " then " 
                              . showsPrec t et 
                              . (++) " else " 
                              . showsPrec t ee
  showsPrec t (Let n be e) = (++) "let " 
                             . (++) n 
                             . (++) " = " 
                             . showsPrec t be 
                             . (++) " in " 
                             . showsPrec t e
  showsPrec t (Prim n es) = (++) n 
                            . (++) "(" 
                            . foldr (.) id (intersperse ((++) ",") (map (showsPrec t) es))
                            . (++) ")"
  showsPrec t (Const n) = (++) n 
  
-- Example
--   S K K I

expSKII = Comb "@" proc
          [Comb "@" proc
           [Comb "@" proc
            [Comb "S" proc []
            , Comb "K" proc []]
           , Comb "K" proc []]
          , Comb "I" proc []]
          
-----
type Env             = [(Name, Prop_Pat)]

type CombPropPatEnvMaybeExp  = (Name, Prop_Pat, Env, Maybe Exp)
type CombPropPatEnvMaybeExps = [CombPropPatEnvMaybeExp]
  
type CombPropPat  = (Name, Prop_Pat)
type CombPropPats = [CombPropPat]

type CombPropPatEnv  = (Name, Prop_Pat, Env)
type CombPropPatEnvs = [CombPropPatEnv]

type VarPropPat   = (Name, Prop_Pat)
type VarPropPats  = [VarPropPat]
type VarPropPatss = [VarPropPats]

type VarPropPatPropPat   = (Name, Prop_Pat, Prop_Pat)
type VarPropPatPropPats  = [VarPropPatPropPat]
type VarPropPatPropPatss = [VarPropPatPropPats]

type VarPropPatPropPatExp   = (Name, Prop_Pat, Prop_Pat, Exp)
type VarPropPatPropPatExps  = [VarPropPatPropPatExp]
type VarPropPatPropPatExpss = [VarPropPatPropPatExps]

type VarPropPatPropPatPropPatExp   = (Name, Prop_Pat, Prop_Pat, Prop_Pat, Exp)
type VarPropPatPropPatPropPatExps  = [VarPropPatPropPatPropPatExp]
type VarPropPatPropPatPropPatExpss = [VarPropPatPropPatPropPatExps]

type NamePat = (Name,Prop_Pat)
type NamePats = [NamePat]
type NamePatss = [NamePats]

{- Propositions specifying patterns of terms -}
data Prop_Pat = P_CombPat Name 
              | P_DownPat Int Prop_Pat
              | P_UpPat   Int Prop_Pat
              | P_AndPat  Prop_Pat Prop_Pat 
              | P_AnyPat
              | P_NextPat Prop_Pat
              | P_VarPat  Name   -- Used specially for P_NextPat only.
                deriving Eq
                
instance Show Prop_Pat where
  showsPrec t (P_CombPat n)   = (++) n
  showsPrec t (P_VarPat n)    = (++) n
  showsPrec t (P_DownPat i p) = (++) (show i) . (++) "_(" . showsPrec t p . (++) ")"
  showsPrec t (P_UpPat i p)   = (++) (show i) . (++) "^(" . showsPrec t p . (++) ")"
  showsPrec t (P_AndPat p q)  = (++) "/\\ " . (++) "(" . showsPrec t p . (++) ") " . (++) "(" . showsPrec t q . (++) ")"
  showsPrec t (P_NextPat p)   = (++) "<>(" . showsPrec t p . (++) ")"
  showsPrec t (P_AnyPat)      = (++) "*"

tab n = take n (repeat ' ')
  
-- Simpliflication of Pattern Propositions
--  * No redundant propositions such as P_AndPat (P_CombPat "I") (P_CombPat "I")
--  * (Almost completely) Sorting conjuncts of P_AndPat by the depth or height of paths
minimize :: Prop_Pat -> Prop_Pat
minimize p = check ps
  where
    ps = p : map rule ps
    check (p:q:ps) = if p == q then p else check (q:ps)
    
rule :: Prop_Pat -> Prop_Pat
rule (P_DownPat i (P_AndPat p q))
  = P_AndPat (P_DownPat i p) (P_DownPat i q)
rule (P_DownPat i (P_UpPat j p)) 
  = if i==j then p else (P_DownPat i (rule (P_UpPat j p)))
rule (P_DownPat i p)                        
  = P_DownPat i (rule p)
    
rule (P_UpPat i (P_AndPat p q)) 
  = P_AndPat (P_UpPat i p) (P_UpPat i q)
rule (P_UpPat i (P_DownPat j p)) 
  = if i==j then p else (P_UpPat i (rule (P_DownPat j p)))
rule (P_UpPat i p)
  = P_UpPat i (rule p)
    
rule (P_AndPat (P_AndPat p q) s)
  = P_AndPat p (P_AndPat q  s)
rule (P_AndPat p (P_AndPat q r))
  | lessThan q p = (P_AndPat q (P_AndPat p r))
  | lessThan r p = (P_AndPat r (P_AndPat q p))
  | p == q = P_AndPat q r
  | p == r = P_AndPat q r
  | otherwise = P_AndPat (rule p) (rule (P_AndPat q r))
rule (P_AndPat p q)
  | p == q = q 
  | lessThan q p = P_AndPat q p
  | otherwise = P_AndPat (rule p) (rule q)
                
rule p = p

lessThan p q = lessThan' (len p) (len q)
  where
    lessThan' (Just i) (Just j) = i < j
    lessThan' _ _ = Prelude.False

len :: Prop_Pat -> Maybe Int
len (P_CombPat n) = Just 0
len (P_VarPat n) = Just 0
len (P_DownPat i p) = do n <- len p; return (1 + n)
len (P_UpPat i p) = do n <- len p; return (1 + n)
len (P_AnyPat) = Just 0
len (P_AndPat p q) = Nothing
len (P_NextPat p) = Nothing


-- 
genRules :: ParRedRules -> (CombPropPatEnvMaybeExps, VarPropPatPropPatPropPatExpss, NamePatss)
genRules rules = (concat cpmess, vpppess, npss)
  where
    l       = map genRule rules
    cpmess  = [ [(c, p, env, Just e)] ++ [(c, p, env, Nothing) | (c,p,env) <- cpps]
              | (_, (c,p,env), cpps, vpps, e) <- l]
    vpppess = [ [(v,p,r,q,e) | (v,p,r) <- vpps, (n,q) <- nps, v==n] | (nps, _, _, vpps, e) <- l]
    npss    = [ nps | (nps, _, _, _, _) <- l]

genRule :: ParRedRule -> (NamePats, CombPropPatEnv, CombPropPatEnvs, VarPropPatPropPats, Exp)
genRule (judgs, judg) = (e, a, b, c, d)
  where
    e = map f judgs
    (a,b,c,d) = genJudg judg
    f (PVar n k1, Var m k2) = (n, P_NextPat (P_VarPat m))
    f _                     = error "genRule: unexpected judgs"
  

genJudg :: Judgment -> (CombPropPatEnv, CombPropPatEnvs, VarPropPatPropPats, Exp)
genJudg (pat, exp) = (cpp, cpps, vpps, exp)
  where
    (cpp, cpps, vpps) = genPPat pat

genPPat :: Pat -> (CombPropPatEnv, CombPropPatEnvs, VarPropPatPropPats)
genPPat pat = (head cpps, tail cpps, vpps)
  where
    (cpps, vpps) = gp pat p_fwd p_root
    p_fwd  = gp_fwd pat
    p_env  = gp_env pat (\p->p)
    p_root = (\p->p)
    
    gp_fwd (PVar n k) = P_AnyPat
    gp_fwd (PComb n k pats) = 
      foldr P_AndPat (P_CombPat n)
      [P_DownPat k (gp_fwd pat) | (k, pat) <- zip [1..] pats]
      
    gp_env (PVar n k) f = [(n, f P_AnyPat)]
    gp_env (PComb n k pats) f = concat
      [gp_env pat (f . (P_DownPat k)) | (k, pat) <- zip [1..] pats]
      
    
    gp :: Pat -> Prop_Pat -> (Prop_Pat -> Prop_Pat) -> (CombPropPatEnvs, VarPropPatPropPats)
    gp (PVar n k)       p_fwd p_root = ([], [(n, minimize p_fwd, minimize (p_root P_AnyPat))])
    gp (PComb n k pats) p_fwd p_root = 
      let list = [gp pat (P_UpPat k p_fwd) (P_UpPat k . p_root)
                 | (k, pat) <- zip [1..] pats]
          (cipps, vipps) = (concat $ map fst list, concat $ map snd list)
          prop = P_AndPat (P_CombPat n) p_fwd
          prop_minimized = minimize prop
          env = map (\(x,p) -> (x, minimize (p_root p))) p_env
      in  ((n, prop_minimized, env):cipps, vipps)
          

-- Parent
                           
parent :: Name -> Prop_Pat -> Name -> Exp -> [Prop_Pat]    -- x -> (path from x to the root) -> x' -> [the parent of x']
parent x p x' e = parent' (\p->p) e 
  where
    parent' :: (Prop_Pat -> Prop_Pat) -> Exp -> [Prop_Pat]
    parent' p_fwd (Comb n k es) = 
      let f (i,e) ps = parent' (mk_p_fwd i) e ++ ps
          mk_p_fwd i p = p_fwd (P_AndPat (P_CombPat n) (P_DownPat i p))
      in  foldr f [] (zip [1..] es)
          
    parent' p_fwd (Var n k) =
      if x' == n
      then [p_fwd P_AnyPat]
      else []
           
    parent' p_fwd (If cond et ee) = parent' p_fwd et ++ parent' p_fwd ee
    parent' p_fwd (Let n be e) = 
      if x' == n 
      then [] 
      else (parent' p_fwd be ++ parent' p_fwd e)
    parent' p_fwd (Prim n es) = []
    parent' p_fwd (Const n) = []
    
-- prCombPropPatEnvMaybeExps :: [(Name, Prop_Pat, Env, Maybe Exp)] -> IO ()
-- prCombPropPatEnvMaybeExps xs = mapM_ pr xs
--   where
--     pr (n, p, env, maybe_exp) = 
--       do putStr n
--          putStr " : "
--          putStrLn $ show $ p
--          putStrLn $ show $ env
--          putStr " => "
--          putStrLn $ show $ maybe_exp

-- prVarPropPatPropPatPropPatExps :: [(Name, Prop_Pat, Prop_Pat, Prop_Pat, Exp)] -> IO ()
-- prVarPropPatPropPatPropPatExps xs = mapM_ pr xs
--   where
--     pr (n, p, r, q, e) = 
--       do putStr n
--          putStrLn " if matched with: "
--          putStr "\t"
--          putStrLn $ show $ p         
--          putStrLn "  Go up to the root: "
--          putStr "\t"
--          putStrLn $ show $ r
--          putStrLn "  Cross the bridge: "
--          putStr "\t"
--          putStrLn $ show $ q
--          putStrLn "  Go down to: "
--          putStr "\t"
--          case q of P_NextPat (P_VarPat m) -> putStrLn (show (map minimize (parent n p m e)))
--          putStrLn "  In: "
--          putStr "\t"
--          putStrLn $ show $ e
         
-- Examples
exGenRules = genRules skiRules
          
-- exPr1 = prCombPropPatEnvMaybeExps (case exGenRules of (a,_,_) -> a)
-- exPr2 = mapM_ prVarPropPatPropPatPropPatExps (case exGenRules of (_,b,_) -> b)
-- exPr3 = case exGenRules of (_,_,c) -> c
                           
--

compile :: CombDecl -> Exp -> ParRedRules 
           -> IO (DLExp, [DLExp], DLExp -> (Maybe DLExp, [DLExp]))
compile cdecl exp rules = 
  do putStrLn "Compiling..."
     putStrLn ""
     mapM_ prRow rows
     putStrLn ""
     mapM_ prCol cols
     return (dlexp, cs, reduce cdecl rows cols)
     
  where
    (dlexp, cs)            = dlE cdecl rows cols exp
    (cpmes, vpppess, npss) = genRules rules
    
    rows = [ (n, p, env, maybe_exp
               , [ (v, q, r, m, ts, e) 
                 | isJust maybe_exp, (v,q,r,s,e) <- concat vpppess
                 , let P_NextPat (P_VarPat m) = s
                 , let ts = map minimize (parent v q m e)])
           | (n, p, env, maybe_exp) <- cpmes ]
           
    cols = [ (v, q, r, m, ts, e)
           | (v,q,r,s,e) <- concat vpppess
           , let P_NextPat (P_VarPat m) = s
           , let ts = map minimize (parent v q m e)]
           
type Link  = (Name, Prop_Pat, Prop_Pat, Name, [Prop_Pat], Exp)
type Links = [Link]
type Row   = [(Name, Prop_Pat, [(Name, Prop_Pat)], Maybe Exp, Links)]
type Col   = [(Name, Prop_Pat, Prop_Pat, Name, [Prop_Pat], Exp)]

{- reduce 함수 구조

reduce l =
  if l |= P_comb_i then 
     set up an environment E i.e., { x_j -> P_j }
     evaluate e_i with E
        Comb => create a combinator
        x'   => if x=>x' then next ( E(x) l)
        n+m  => evaluate n+m
        up   => upPtr l
-}

reduce :: CombDecl -> Row -> Col -> DLExp -> (Maybe DLExp, [DLExp])
reduce combdecl rows cols l =
  case maybe_exp of
    Nothing -> (Nothing, [])
    Just e  -> let (dle, cs) = evalExp l e
               in  (Just dle, cs)
    
  where 
    (n, p_comb, env, maybe_exp, links) = 
      head [ row | row <- rows
           , let (n, p_comb, env, maybe_exp, links) = row
           , eval p_comb l]
      
    updowns = [(q,u,ds) | (_, q, u, _, ds, _) <- cols]
      
    evalExp :: DLExp -> Exp -> (DLExp, [DLExp])   -- The 2nd elements are combinators.
    evalExp l (Comb n k es) = (c, [c] ++ concat cs)
      where
        c        = DLComb n ls up (reduce combdecl rows cols c)
        (ls, cs) = unzip [ evalExpLocal l [(n, i, c)] e | (i,e) <- zip [1..] es ]
        
        up = upPtr updowns l
    
    evalExp l (Var n' Proc) = (c, [])
      where 
        c = next (path p l)
        n = head [ x | (x, _, _, y, _, _) <- links, y==n']
        p = head [ p | (x,p) <- env, x==n ]
        
    evalExp l (Var n' Val) = (c, [])
      where 
        c = fetch n' env l
        
    -- evalExp l env links (DLLet x be e) =  Combinator와 다른 값을 구분해야 함!
    --   where
    evalExp l (If ce et ee) =
      if b then (e1, cs ++ cs1 ++ cs2)
      else (e2, cs ++ cs1 ++ cs2)
      where
        (DLConst n, cs) = evalExp l ce
        b = read n :: Bool
        
        (e1, cs1) = evalExp l et
        (e2, cs2) = evalExp l et
        
    evalExp l (Prim binop [e1,e2]) =
      (
        
      case binop of 
        "+" -> DLConst (show $ i1 + i2)
        "-" -> DLConst (show $ i1 - i2)
        "*" -> DLConst (show $ i1 * i2)
        "/" -> DLConst (show $ i1 `div` i2)
        "<" -> DLConst (show $ i1 < i2)
        "==" -> DLConst (show $ i1 == i2)
        "&&" -> DLConst (show $ b1 && b2)
        "||" -> DLConst (show $ b1 || b2)
        "min" -> DLConst (show $ min i1 i2)
        "max" -> DLConst (show $ max i1 i2)
        
      , [])
        
      where
        i1 = read n1 :: Int
        i2 = read n2 :: Int
        b1 = read n1 :: Bool
        b2 = read n2 :: Bool
        ([DLConst n1, DLConst n2], cs) = unzip (map (evalExp l) [e1,e2])
    evalExp l (Const n) = (DLConst n, [])
    
    evalExpLocal :: DLExp -> [(Name, Int, DLExp)] -> Exp -> (DLExp, [DLExp])
    evalExpLocal l up (Comb n k es) = (c, [c] ++ concat cs)
      where
        c  = DLComb n ls up (reduce combdecl rows cols c)
        (ls, cs) = unzip [ evalExpLocal l [(n, i, c)] e | (i,e) <- zip [1..] es ]
    evalExpLocal l up e =
      evalExp l e
      
fetch :: Name -> Env -> DLExp -> DLExp      
fetch n env l = path p l
  where
    p = head [p | (m, p) <- env, n==m]
           
type UpDownss = [(Prop_Pat, Prop_Pat, [Prop_Pat])]
  
-- If an Up ptr is * then take the next of the parent of the root as the next up ptr.
upPtr :: UpDownss -> DLExp -> [(Name, Int, DLExp)]
upPtr cols l = concat
  [ if p_down == P_AnyPat
    then upPtr cols (path p_up l)
    else down p_down (next (path p_up l))  -- The lazy evaluation is necessary here,
                                           -- or the notion of pointer is required.
  | (p_qualifier, p_up, p_downs) <- cols
  , eval p_qualifier l
  , p_down <- p_downs ]
  
  where 
    down :: Prop_Pat -> DLExp -> [(Name, Int, DLExp)]  -- Maybe
    down (P_AnyPat) l = []  -- No parent exists.
    down (P_DownPat i P_AnyPat) (l@(DLComb n dles _ _)) = [(n, i, l)]
    down (P_DownPat i p) (DLComb n dles _ _) = down p (dles !! (i-1))
    down (P_AndPat p q) l = down p l ++ down q l
    down (P_CombPat m) (DLComb n _ _ _) = 
      if n == m then [] 
      else error ("upPtr/down: unexpectd case" ++ n ++ m)
    down p l = error ("upPtr/down: unexpected case" ++ show p)
  
-- Given l and p, return l' that one reaches after following a path specified by p.  
-- Of course, p must be a proposition specifying a path, not a tree.
    
path :: Prop_Pat -> DLExp -> DLExp
path (P_AnyPat) l  = l  
path (P_DownPat i p) (DLComb _ dles _ _) = path p (dles !! (i-1))
path (P_UpPat i p)   (DLComb _ _ [(_,j,l)] _)  = if i==j then l else error "path: unexpected up"
path p l = error "path: unexpected args"

-- The eval function verifies the satisfiability of p in terms of l.
-- If satisfied, return True. Otherwise, return False.

eval :: Prop_Pat -> DLExp -> Bool
eval (P_CombPat n) (DLComb m _ _ _)      = n==m
eval (P_DownPat i p) (DLComb _ dles _ _) = 1 <= i && i <= length dles && eval p (dles !! (i-1))
eval (P_UpPat i p) (DLComb _ _ [(n,j,l)] _) = if i==j then eval p l else error "eval: unexpected up"
eval (P_AndPat p q) l                    = eval p l && eval q l
eval (P_AnyPat) l                        = Prelude.True
eval p l                                 = Prelude.False

-- Printing patterns and environment,  if exists, with an expression.

prRow (n, p, env, maybe_exp, vqrmtses) = 
  do putStr "Pattern:\t"
     putStrLn $ show $ p
     putStr "Environment:\t"
     putStrLn $ show $ env
     putStr "Expression:\t"
     putStrLn $ case maybe_exp of { Nothing -> "."; Just e -> show e }
     putStrLn ""
--      putStrLn "with up ptrs such that" 
--      putStrLn ""
--      mapM_ prCol vqrmtses

-- Printing variable contexts
     
prCol (v, q, r, m, ts, e) = 
  do putStr "Variable:\t"
     putStrLn v
     putStr "Context:\t"
     putStrLn $ show $ q
     putStr "Path(up):\t"
     putStr "by\t"
     putStr $ show $ r
     putStr "\t\t(FROM "
     putStr v
     putStrLn " TO THE ROOT)"
     putStr "Path(down):\t"
     putStr "by\t"
     putStr (show ts)
     putStr "\t(FROM THE NEXT ROOT TO "
     putStr m
     putStrLn ")"
     putStr "Expression:\t"
     putStrLn (show e)
     putStrLn ""

    
-- examples
compEx1 = compile skiCombDecl expSKII skiRules
compEx2 = compile insCombDecl expINS insRules
compEx3 = compile ptrCombDecl expPTR ptrRules

-- Run
run compiledExp n = do
  (l, ls, reduce) <- compiledExp
  let h ls = par reduce ls
  let lss  = ls : map h lss
  let hs   = l  : map next hs
  putStrLn "Executing..."
  putStrLn ""
  mapM_ pr (take n (zip hs lss))
  where
    pr (l,ls) = 
      do putStrLn (show (ldE l))
         putStrLn ""
                   
par :: (DLExp -> (Maybe DLExp, [DLExp])) -> [DLExp] -> [DLExp]
par reduce ls = concat $ map (snd . reduce) $ ls

-- examples
runEx2 = run compEx2 6
runEx3 = run compEx3 6


{- Expressions with doubly-linked lists -}

-- Values are one of DLComb and DLConst. DLComb is defined to have a up pointer. 
-- Having multiple up pointers makes it difficult to design DSL. An interesting future work.

data DLExp = DLComb Name [DLExp] UpExps Future -- UpExps is either [] or [dlexp] for the moment!
           | DLVar Name
           | DLIf DLExp DLExp DLExp
           | DLLet Name DLExp DLExp
           | DLPrim Name [DLExp]
           | DLConst Name
             deriving Show
                      
dlexp_true  = "True"
dlexp_false = "False"

next :: DLExp -> DLExp                      
next (DLComb _ _ _ (Just f, _)) = f
next (DLComb _ _ _ (Nothing, _)) = error $ "next: unexpected Nothing"
next (DLConst n) = error $ "next: unexpected DLConst " ++ n
next dlexp = error "next: unexpected DLExp"
                      
type UpExp = (Name, Int, DLExp)
type UpExps = [UpExp]

type Future = (Maybe DLExp, [DLExp])

dlE :: CombDecl -> Row -> Col -> Exp -> (DLExp, [DLExp])
dlE combdecl rows cols e = dlE' [] e 
  where
    dlE' :: UpExps -> Exp -> (DLExp, [DLExp])
    dlE' up (Comb n k es) = (l, [l] ++ concat cs)
      where
        l  = DLComb n ls up f
        f  = reduce combdecl rows cols l
        (ls, cs) = unzip [dlE' [(n,i,l)] e | (i,e) <- zip [1..] es]
    dlE' up (Var n k) = (DLVar n, [])
    dlE' up (If ce et ee) = (DLIf l0 l1 l2, cs0 ++ cs1 ++ cs2)
      where
        (l0, cs0) = dlE' up ce
        (l1, cs1) = dlE' up et
        (l2, cs2) = dlE' up ee
    dlE' up (Let n e1 e2) = (DLLet n l1 l2, cs1 ++ cs2)
      where
        (l1, cs1) = dlE' up e1
        (l2, cs2) = dlE' up e2
        
    dlE' up (Prim n es) = (DLPrim n ls, concat cs)
      where
        (ls, cs) = unzip (map (dlE' up) es) 
    dlE' up (Const n) = (DLConst n, [])
                    
ldE :: DLExp -> Exp
ldE (DLComb n ls up l) = Comb n proc (map ldE ls)
ldE (DLConst n)        = Const n
ldE dle                = error "ldE: unexpected pattern"  
