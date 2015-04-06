module Solution where
data Term = App String [Term] | Var String  deriving (Show, Read, Eq)
newtype Subs = Subs [(Term, Term)] deriving (Show)

contains (Var _) [] = False
contains var@(Var _) (v@(Var _):rest) = (var == v) || contains var rest
contains var@(Var _) ((App name tl):rest) = contains var tl || contains var rest

substitute var@(Var _) term list = map (\t -> (case t of v@(Var _) -> (if var == v then term else v)
                                                         (App name tl) -> (App name (substitute var term tl)))) list

substituteall subs list = foldl (\l -> \(name, term) -> substitute name term l) list subs

unify :: Term -> Term -> Maybe Subs
unify t1@(Var _) t2@(Var _) = if t1==t2 then Just (Subs []) else Just (Subs [(t1, t2)])
unify v1@(Var _) (App f2 tl) = if (contains v1 tl) then Nothing else Just (Subs [(v1, App f2 tl)])
unify (App f1 tl) v2@(Var _) = if (contains v2 tl) then Nothing else Just (Subs [(v2, App f1 tl)])
unify (App f1 tl1) (App f2 tl2) = if (f1==f2) && ((length tl1)==(length tl2)) then lunify (Just (tl1,tl2)) else Nothing
lunify Nothing = Nothing
lunify (Just([],[])) = Just (Subs [])
lunify (Just(a:b,[])) = Nothing
lunify (Just([],a:b)) = Nothing
lunify (Just(vl:restl, vr:restr)) = (let
        vunified = unify vl vr
        in case vunified of
            Nothing  -> Nothing
            Just (Subs v) -> (let
                restunified = lunify (Just (substituteall v restl,substituteall v restr))
                in case restunified of
                    Nothing -> Nothing
                    Just (Subs r) -> Just (Subs (v++r)) ))

solution list = flatten (lunify (Just (map fst list, map snd list)))

flatten Nothing = Nothing
flatten (Just (Subs list)) = Just (Subs (zip (map fst list) (substituteall list (map snd list))))