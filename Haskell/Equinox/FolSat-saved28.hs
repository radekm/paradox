module Equinox.FolSat where

{-
Equinox -- Copyright (c) 2003-2007, Koen Claessen

Permission is hereby granted, free of charge, to any person obtaining a
copy of this software and associated documentation files (the
"Software"), to deal in the Software without restriction, including
without limitation the rights to use, copy, modify, merge, publish,
distribute, sublicense, and/or sell copies of the Software, and to
permit persons to whom the Software is furnished to do so, subject to
the following conditions:

The above copyright notice and this permission notice shall be included
in all copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS
OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
-}

import Form
import qualified Sat
import Name( name, prim, (%) )
import List hiding ( union, insert, delete )
import Maybe
import Equinox.Fair
import Equinox.TermSat hiding ( Lit(..) )
import Equinox.TermSat ( Lit )
import qualified Equinox.TermSat as T
import Data.Set( Set )
import qualified Data.Set as S
import Data.Map( Map )
import qualified Data.Map as M
import Data.Maybe( isJust, fromJust )
import IO
import Flags
import Control.Monad
import Equinox.PSequence
import Equinox.TopSort

prove :: Flags -> [Clause] -> [Clause] -> IO ClauseAnswer
prove flags theory oblig =
  run $
    do true  <- newCon "$true"
       st    <- newCon "*"
       
       --lift (print "hej")
       --sequence_
       --  [ do lift (print c)
       --  | c <- theory
       --  ]
       --lift (print "hopp")
       sequence_
         [ do put 1 "P: "
              addClauseSub true M.empty c
         | c <- groundCs
         ]

       {-
       sequence_
         [ do lift (print dc)
         | c <- nonGroundCs
         , dc <- mkDClause c
         ]
       -}
       
       sequence_
         [ addGroundTerm x
         | c <- nonGroundCs -- was: oblig
         , l <- c
         , a :=: b <- [the l]
         , x <- [a,b]
         , x /= truth
         ]

       let getModelCons =
             do tabs <- sequence [ getModelTable f | f <- S.toList fs ]
                return (S.toList (S.fromList (st:[ c | tab <- tabs, (_,c) <- tab ])))

       let refineLib   = refine flags L (true,st) syms getModelCons nonGroundCs
           refineBasic = refine flags P (true,st) syms getModelCons nonGroundCs

       lift (putStrLn "#elt|m|#instances")
       r <- cegar Nothing Nothing refineLib
          $ cegar Nothing Nothing refineBasic
          $ Just `fmap` do ans  <- getTable answer
                           mins <- getTable min
                           mls  <- solveWithConflict flags [ y T.:=: true  | (_,y) <- mins ]
                                                           [ y T.:/=: true | (_,y) <- ans ]
                           case mls of
                             Just ls@(_:_) ->
                               do lift $ putStrLn $ ("+++ ANSWER: " ++) $
                                    concat $ intersperse " | " $
                                      [ "(" ++ concat (intersperse "," (map show xs)) ++ ")" | (xs,y) <- ans, (y T.:=: true) `elem` ls ]
                             _ ->
                               do return ()
                           return (isNothing mls)

       return $ case r of
                  Just False -> Unsatisfiable
                  Just True  -> Satisfiable
                  Nothing    -> NoAnswerClause GaveUp
 where
  put   v s = when (v <= verbose flags) $ lift $ do putStr s;   hFlush stdout
  putLn v s = when (v <= verbose flags) $ lift $ do putStrLn s; hFlush stdout
  
  cs = concatMap (norm []) (theory ++ oblig)
  
  (groundCs,nonGroundCs) = partition isGround cs
  
  syms = symbols cs
  
  answer = head $ [ ans
                  | ans@(nam ::: (_ :-> t)) <- S.toList syms
                  , t == bool
                  , nam == name "$answer"
                  ] ++ [ name "$no_answer" ::: ([] :-> bool) ]
  
  min    = head $ [ mn
                  | mn@(nam ::: (_ :-> t)) <- S.toList syms
                  , t == bool
                  , nam == name "$min"
                  ] ++ [ name "$no_min" ::: ([] :-> bool) ]
  
  fs = S.filter (\f ->
    case f of
      _ ::: (_ :-> t) -> t /= bool
      _               -> False) syms

solveWithConflict flags mins ass =
  do b <- solve flags ass
     if b then
       do a <- T.newLit

          let try mins =
-- {-
                do mins' <- sequence
                            [ do b <- getModelValue m
                                 if b then do return [m]
                                      else do addClause [T.neg a, T.neg m]
                                              return []
                            | m <- mins
                            ]
                   let mins = concat mins'
                   addClause (T.neg a : map T.neg mins)
-- -}
{-
                do bms <- sequence
                            [ do c <- getValue m
                                 case c of
                                   Nothing -> do b <- getModelValue m
                                                 return [(b,m)]
                                   Just _  -> do return []
                            | m <- mins
                            ]
                   let (bs,mins) = unzip (concat bms)
                       n = length [ b | b <- bs, b ]
                   lift (do putStr ("("++show n++"/"++show (length mins)++")"); hFlush stdout)
                   
                   let atMost n cl ms | n < 0 = [ cl ]
                       atMost _ cl []         = []
                       atMost n cl (m:ms)     = atMost (n-1) (T.neg m : cl) ms
                                             ++ atMost n cl ms
                   
                   sequence_ [ addClause cl | cl <- atMost (n-1) [T.neg a] mins ]
-}
                   b <- solve flags (a:ass)
                   if b then try mins else return ()
          
          try mins
          return Nothing
      else
       do ls <- conflict
          let ass' = map neg ls
                
          let try [] =
                do return (Just ls)
                    
              try (ass:asss) =
                do mls <- solveWithConflict flags [] ass
                   case mls of
                     Nothing -> do try asss
                     _       -> do lift $ putStr "<>"
                                   return mls
              
           in try [ ass' \\ [a] | a <- ass' ]

norm :: [Signed Atom] -> [Signed Atom] -> [[Signed Atom]]
norm ls' [] =
  [reverse ls']

norm ls' (Neg (Var x :=: Var y) : ls) =
  norm [] (subst (x |=> Var y) (reverse ls' ++ ls))

norm ls' (Neg (Var x :=: t) : ls) | not (x `S.member` free t) = -- just testing
  norm [] (subst (x |=> t) (reverse ls' ++ ls))

norm ls' (Neg (t :=: Var x) : ls) | not (x `S.member` free t) = -- just testing
  norm [] (subst (x |=> t) (reverse ls' ++ ls))

norm ls' (Pos (Var x :=: Fun f ts) : ls) =
  norm (Pos (Fun f ts :=: Var x) : ls') ls

norm ls' (Neg (Var x :=: Fun f ts) : ls) =
  norm (Neg (Fun f ts :=: Var x) : ls') ls

norm ls' (Pos (s :=: t) : ls) | s == t =
  []

norm ls' (Neg (s :=: t) : ls) | s == t =
  norm ls' ls

norm ls' (l : ls) =
  norm (l : ls') ls

addClauseSub :: Con -> Map Symbol Con -> Clause -> T ()
addClauseSub true sub cl =
  do --lift (print (sub,cl))
     --lift (print sub)
     ls <- sequence [ literal l | l <- cl ]
     --lift (print ls)
     addClause ls
 where
  term (Var x) =
    do return (fromJust $ M.lookup x sub)
  
  term (Fun f [t]) | show f == "$weak" =
    do term t
  
  term (Fun f ts) =
    do as <- sequence [ term t | t <- ts ]
       f `app` as
  
  atom (s :=: t) | t == truth =
    do a <- term s
       return (a T.:=: true)
  
  atom (s :=: t) =
    do a <- term s
       b <- term t
       return (a T.:=: b)
  
  literal (Pos a) = atom a
  literal (Neg a) = neg `fmap` atom a

addGroundTerm :: Term -> T (Maybe Con)
addGroundTerm (Var _) =
  do return Nothing

addGroundTerm (Fun f [t]) | show f == "$weak" =
  addGroundTerm t

addGroundTerm (Fun f ts) =
  do mxs <- sequence [ addGroundTerm t | t <- ts ]
     if all isJust mxs
       then Just `fmap` (f `app` map fromJust mxs)
       else return Nothing

type Model = ([Maybe (Set Symbol)], Map Symbol [([Con],Con)])

cegar :: Maybe Int -> Maybe Model -> (Maybe Model -> T (Bool,Model)) -> T (Maybe Bool) -> T (Maybe Bool)
cegar mk mmodel refine solve =
  do mb <- solve
     case mb of
       Just True | mk /= Just 0 ->
         do (r,model') <- refine mmodel
            if r then
              cegar (subtract 1 `fmap` mk) (Just model') refine solve
             else
              return (Just True)
       
       _ ->
         do return mb

data Refine = P | L
 deriving (Show, Eq)

isModelPoint :: Refine -> Bool
isModelPoint r = True

letter :: Refine -> String
letter r = show r

refine :: Flags -> Refine -> (Con,Con) -> Set Symbol -> T [Con] -> [[Signed Atom]] -> Maybe Model -> T (Bool,Model)
refine flags opts (true,st') syms getCons cs mOldModel =
  do cons' <- getCons
     --lift (print cons')
     st    <- getModelRep st'
     let cons = st : (cons' \\ [st])
     lift (putStr ( let s = show (length cons)
                 in replicate (4 - length s) ' ' ++ s
                 ++ "|"
                 ++ letter opts
                 ++ "|"
                  ) >> hFlush stdout)
     
     model <- getModelTables
     let sameFs = S.fromList
                  [ f
                  | Just (cms, model') <- [mOldModel]
                  , f <- S.toList fs
                  , let how m = fmap sort (M.lookup f m :: Maybe [([Con],Con)])
                  , how model == how model'
                  ]

     esubss <- lift $ psequence (nrOfThreads flags)
                 [ if not (hasFreeVar c)
                   && case ms of
                        Just fs -> fs `S.isSubsetOf` sameFs
                        Nothing -> False
                     then ( 0
                          , \send -> do send '_'
                                        return (Right ms)
                          )
                     else ( S.size (free c)
                          , \send ->
                            do esubs <- check opts send model c true cons st
                               case esubs of
                                 Left subs -> return (Left [ (c,sub) | sub <- subs ])
                                 Right ms  -> return (Right (Just ms))
                          )
                 | (c,ms) <- cs `zip` case mOldModel of
                                        Nothing      -> repeat Nothing
                                        Just (cms,_) -> cms
                 ]
     
     let subs = [ csub | Left subs <- esubss, csub <- subs ]
     sequence_ [ addClauseSub true sub cl | (cl,sub) <- subs ]
     lift (putStrLn "")

     if null subs && isModelPoint opts && isJust (mfile flags)
       then writeModel (fromJust (mfile flags)) true (S.toList fs)
       else return ()
     return (not (null subs), ([ case esubs of
                                   Right ms -> ms
                                   _        -> Nothing | esubs <- esubss ], model))
 where
  hasFreeVar c = any (\x -> all (notBound x) c) xs
   where
    xs = S.toList (free c)

    notBound x (Pos (Var _ :=: Var _)) = True
    notBound x (Pos (Var _ :=: t))     = not (x `S.member` free t)
    notBound x (Pos (s     :=: Var _)) = not (x `S.member` free s)
    notBound x atom                    = not (x `S.member` free atom)

  fs = S.filter (\f ->
    case f of
      _ ::: (_ :-> t) -> True
      _               -> False) syms

writeModel :: FilePath -> Con -> [Symbol] -> T ()
writeModel file true fs =
  do lls <- sequence
              [ do tab <- getModelTable f
                   return (table f tab)
              | f <- fs
              -- , arity f > 0 || isPredSymbol f
              ]
     lift (writeFile file (unlines (concat (intersperse [""] lls))))
 where
  table f tab
    | isPredSymbol f = [ app f xs
                      ++ " <=> "
                      ++ (if y == true then "$true" else "$false")
                       | (xs,y) <- tab
                       ]
    | otherwise      = [ app f xs
                      ++ " = "
                      ++ (if show y == app f xs then "<..>" else show y)
                       | (xs,y) <- tab
                       ]

  app f [] = show f
  app f xs = show f ++ "(" ++ concat (intersperse "," (map show xs)) ++ ")"

----------------------------------------------------------------------------
{- HERE BEGINS THE NEW STUFF -}
check :: Refine -> (Char -> IO ()) -> Map Symbol [([Con],Con)] -> [Signed Atom] -> Con -> [Con] -> Con -> IO (Either [Map Symbol Con] (Set Symbol))
check opts send fmap' cl true cons st =
  do Sat.run $
       do vs <- sequence [ newValue cons | x <- xs ]
          let vmap = M.fromList (xs `zip` vs)
          base  <- Sat.newLit
          stars <- Sat.newLit
          ms <- sequence [ Sat.newLit | f <- M.toList fmap ]
          let mmap = M.fromList (map fst (M.toList fmap) `zip` ms)
          sequence_ [ buildLit (base,stars) st true mmap fmap vmap l | l <- cl ]
          
          -- continue here!
          let findAllSubs i | i > 100 = -- an arbitrary choice! just testing
                -- ouch
                do Sat.lift (send '>')
                   return (Left [])
          
              findAllSubs i =
                do b <- case opts of
                          P -> solveMin [ Sat.neg (v =? st) | v <- vs ] ([base] ++ ms)
                          L -> solveMin [ Sat.neg (v =? st) | v <- vs ] ms
                   if b then
                     do Sat.lift (showOne (i+1))
                        cs <- sequence [ getModelValueValue v | v <- vs ]
                        let sub = M.fromList (xs `zip` cs)
                        Sat.addClause [ Sat.neg (v =? c) | (v,c) <- vs `zip` cs, c /= st ]
                        Left subs <- findAllSubs (i+1)
                        return (Left (sub:subs))
                    else
                     do if i == 0 then
                          do cfl <- Sat.conflict
                             Sat.lift (send '.')
                             return (Right (S.fromList [ f | (f,m) <- M.toList mmap, Sat.neg m `elem` cfl ]))
                         else
                          do return (Left [])
               where
                showOne i | i <=    9 = send (head (show i))
                          | i ==   10 = send 'X'
                          | i ==   25 = send 'L'
                          | i ==   75 = send 'C'
                          | i ==  250 = send 'D'
                          | i ==  750 = send 'M'
                          | i == 2000 = send '#'
                          | otherwise = return ()

          Sat.lift (send '-')
          findAllSubs 0
 where
  fs   = filter (not . isVarSymbol) (S.toList (symbols cl))
  xs   = S.toList (free cl)
  fmap = M.fromList [ (f, if isPredSymbol f
                            then fixFalses tab
                            else tab)
                    | f <- fs
                    , let tab = case M.lookup f fmap' of
                                  Nothing -> []
                                  Just t  -> t
                    ]
   where
    fixFalses tab = [ (xs,fix y) | (xs,y) <- tab ]
     where
      false = head [ y | (_,y) <- tab, y /= true ]
      fix y | y == true = true
            | otherwise = false

atMostOr :: Int -> Sat.Lit -> [Sat.Lit] -> Sat.S ()
atMostOr k x _ | k < 0 =
  do Sat.addClause [x]
     return ()

atMostOr k x ls | k == 0 =
  do sequence_ [ Sat.addClause [x, Sat.neg l] | l <- ls ]

atMostOr k x ls | k >= length ls =
  do return ()
  
atMostOr k y ls =
  do Sat.addClause (y : map Sat.neg lsa)
     if not (null lsb) then
       do zs <- sequence [ Sat.newLit | i <- [1..k] ]
          sequence_ [ Sat.addClause ([y, Sat.neg x, z]) | (x,z) <- lsa `zip` zs ]
          let x = last lsa
          sequence_ [ Sat.addClause ([y, Sat.neg x] ++ map Sat.neg (take i lsa) ++ [z]) | (i,z) <- [0..] `zip` zs ]
          atMostOr k y (zs ++ lsb)
      else
       do return ()
 where
  lsa = take (k+1) ls
  lsb = drop (k+1) ls

solveMin :: [Sat.Lit] -> [Sat.Lit] -> Sat.S Bool
solveMin xs as =
  do b <- Sat.solve as
     if b then
       let mins a =
             do bs <- sequence [ Sat.getModelValue x | x <- xs ]
                let k = length [ b | b <- bs, b ]
                if k >= 1 then
                  do atMostOr (k-1) a xs
                     b <- Sat.solve (Sat.neg a:as)
                     if b then mins a else return True
                 else
                  do return True
           
        in do a <- Sat.newLit
              mins a
      else
       do return False

buildLit :: (Sat.Lit,Sat.Lit) -> Con -> Con -> Map Symbol Sat.Lit -> Map Symbol [([Con],Con)] -> Map Symbol (Value Con) -> Signed Atom -> Sat.S ()
buildLit opts st true mmap fmap vmap (Pos (s :=: t)) =
  do a <- build opts st true mmap fmap vmap s
     b <- build opts st true mmap fmap vmap t
     a /=! b

buildLit opts st true mmap fmap vmap (Neg (s :=: t)) =
  do a <- build opts st true mmap fmap vmap s
     b <- build opts st true mmap fmap vmap t
     a =! b

build :: (Sat.Lit,Sat.Lit) -> Con -> Con -> Map Symbol Sat.Lit -> Map Symbol [([Con],Con)] -> Map Symbol (Value Con) -> Term -> Sat.S (Value Con)
build opts st true mmap fmap vmap t | t == truth =
  do t <- newValue [true]
     return t

build opts st true mmap fmap vmap (Var x) =
  do return val
 where
  Just val = M.lookup x vmap

build opts@(base,stars) st true mmap fmap vmap (Fun f [t]) | show f == "$weak" =
  do build (Sat.mkFalse,stars) st true mmap fmap vmap t
--  do build (base,stars) st true fmap vmap t

build opts@(base,stars) st true mmap fmap vmap (Fun f ts) =
  do z  <- newValue image
     let opts' | show f == "$answer" = (Sat.mkFalse,stars)
               | otherwise           = opts
     vs <- sequence [ build opts' st true mmap fmap vmap t | t <- ts ]
     
     let entries hist [] =
           do return []
         
         entries hist ((xs,y):tab) =
           do e <- conj ( [ v =? x    | (v,x) <- vs `zip` xs, x /= st ]
                       ++ [ Sat.neg e | (zs,e) <- hist, and (zipWith over zs xs) ]
                        )
              Sat.addClause [Sat.neg e, Sat.neg m, z =? y]
              sequence_ [ Sat.addClause [Sat.neg base, Sat.neg e, v =? st]
                        | isFunSymbol f -- predicates always go free
                        , (v,x) <- vs `zip` xs
                        , x == st
                        ]
              if null tab then -- final f(*,*,*) = ?
                do Sat.addClause [Sat.neg stars, Sat.neg e]
                   return ()
               else
                do return ()
              es <- entries ((xs,e):hist) tab
              return (e:es)
      
         x `over` y = x==st || y==st || x==y
      
     es <- entries [] tab
     Sat.addClause es
     return z
 where
  Just m    = M.lookup f mmap
  Just tab' = M.lookup f fmap
  image     = map snd tab
  
  tab = ( map snd $ sort
          [ (number (==st) xs,(xs,y))
          | (xs,y) <- tab'
          ] ) ++ [(replicate (arity f) st, df)]
   where
    number p = length . filter p
    
    df | isFunSymbol f = head (results ++ [st])
       | otherwise     = st
               
    results = map snd
            . reverse
            . sort
            . map (\xs -> (length xs, head xs))
            . group
            . sort
            . map snd
            $ tab'

occursMost :: Ord a => a -> [a] -> a
occursMost y [] = y
occursMost _ xs = snd . head . reverse . sort . map (\xs -> (length xs, head xs)) . group . sort $ xs

conj, disj :: [Sat.Lit] -> Sat.S Sat.Lit
conj xs
  | Sat.mkFalse `elem` xs = return Sat.mkFalse
  | otherwise             = conj' (nub [ x | x <- xs, x /= Sat.mkTrue ])
 where
  conj' [] =
    do return Sat.mkTrue
  conj' [x] =
    do return x
  conj' xs =
    do z <- Sat.newLit
       Sat.addClause (z : map Sat.neg xs)
       sequence_ [ Sat.addClause [ Sat.neg z, x ] | x <- xs ]
       return z

disj xs = Sat.neg `fmap` conj (map Sat.neg xs)

type Value a = [(a,Sat.Lit)]

(=?) :: Eq a => Value a -> a -> Sat.Lit
xls =? x = head ([ l | (x',l) <- xls, x' == x ] ++ [ Sat.mkFalse ])

(=!) :: Ord a => Value a -> Value a -> Sat.S ()
[]         =! ys         =
  do sequence_ [ Sat.addClause [Sat.neg q] | (_,q) <- ys ]
xs         =! []         =
  do sequence_ [ Sat.addClause [Sat.neg p] | (_,p) <- xs ]
((x,p):xs) =! ((y,q):ys) =
  case x `compare` y of
    LT -> do Sat.addClause [Sat.neg p]
             xs =! ((y,q):ys)
    EQ -> do -- only one of these is enough, really
             Sat.addClause [Sat.neg p, q]
             Sat.addClause [Sat.neg q, p]
             xs =! ys
    GT -> do Sat.addClause [Sat.neg q]
             ((x,p):xs) =! ys

(/=!) :: Ord a => Value a -> Value a -> Sat.S ()
[]         /=! ys         = do return ()
xs         /=! []         = do return ()
((x,p):xs) /=! ((y,q):ys) =
  case x `compare` y of
    LT -> do xs /=! ((y,q):ys)
    EQ -> do Sat.addClause [Sat.neg p, Sat.neg q]
             xs /=! ys
    GT -> do ((x,p):xs) /=! ys

newValue :: Ord a => [a] -> Sat.S (Value a)
newValue xs = new (map head . group . sort $ xs)
 where
  new [x] =
    do return [(x,Sat.mkTrue)]
  
  new [x,y] =
    do l <- Sat.newLit
       return [(x,Sat.neg l), (y, l)]

  new xs =
    do ls <- sequence [ Sat.newLit | x <- xs ]
       Sat.addClause ls
       atMostOr 1 Sat.mkFalse ls
       return (xs `zip` ls)

getModelValueValue :: Value a -> Sat.S a
getModelValueValue [(x,_)] =
  do return x
  
getModelValueValue ((x,l):xls) =
  do b <- Sat.getModelValue l
     if b then return x else getModelValueValue xls


