

type Var = String

data Result a = Step (Result a) | Result a | Fail

result :: Result a -> Maybe a
result (Step r)   = result r
result (Result x) = Just x
result Fail       = Nothing

(+++) :: Result a -> Result a -> Result a
Result x +++ _        = Result x
_        +++ Result y = Result y
Fail     +++ q        = q
p        +++ Fail     = p
Step p   +++ Step q   = Step (p +++ q)

solve :: Eq a => [(Var,[a])] -> [(Var,Var)] -> Maybe [(Var,a)]
solve vals neqs = result (search vals neqs [])
 where
  search vals [] _neqsR =
    Result [ (x,v) | (x,v:_) <- vals ]
  
  search vals (xy@(x,y):neqsL) neqsR
    | value x /= value y = search vals neqsL (xy:neqsR)
    | otherwise          = Step (bump x +++ bump y)
   where
    values x = head [ vs | (x',vs) <- vals, x == x' ]
    value x  = head (values x)
    
    bump x = case values x of
               [_]  -> Fail
               _:vs -> search ((x,vs):[ yvs | yvs@(y,_) <- vals, x /= y ]) (neqsL++neqsR) [xy]

