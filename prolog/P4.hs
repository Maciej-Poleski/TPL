module Solution where
import Control.Monad
import Data.Char
import Data.Maybe
import Debug.Trace

data Term= App String [Term] | Var String deriving (Show,Read,Eq)

newtype Subs = Subs [(Term, Term)] deriving (Show)

data AtomicF = Pred String [Term] deriving (Show, Read)
data Clause = Clause [AtomicF] [AtomicF] deriving (Show,Read)
type Program= [Clause]
type Goals= [AtomicF]

data SLDTree= SLDTree Subs Goals [SLDTree] deriving (Show)

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

flattenedUnify list = flatten (lunify (Just (map fst list, map snd list)))

flatten Nothing = Nothing
flatten (Just (Subs list)) = Just (Subs (zip (map fst list) (substituteall list (map snd list))))

flattenedUnifyAtomicF (Pred name1 list1) (Pred name2 list2) = if name1==name2 then flattenedUnify (zip list2 list1) else Nothing

mapEmpty = []

mapContains [] _ = False
mapContains ((key,_):rest) str = key == str || mapContains rest str

mapGet ((key,value):rest) str = if key == str then value else mapGet rest str

mapPut list (key,value) = (key,value):list

instantiateList instantiateFunction (dict, firstFree, list) =
    foldl (\(dict, firstFree, result) -> \term -> let (newDict, newFirstFree, newTerm) = instantiateFunction (dict, firstFree, term) in (newDict, newFirstFree, result ++ [newTerm])) (dict, firstFree, []) list

instantiateTerm (dict, firstFree, (Var var)) = if mapContains dict var then (dict, firstFree, Var (mapGet dict var)) else 
    let newValue = "gnn" ++ show firstFree
        newDict = mapPut dict (var,newValue)
    in (newDict, firstFree+1, Var newValue)
instantiateTerm (dict, firstFree, (App name list)) = 
    let (newDict, newFirstFree, newList) = instantiateList instantiateTerm (dict, firstFree, list)
    in (newDict, newFirstFree, App name newList)
    
instantiateAtomicF (dict, firstFree, Pred name list) =
    let (newDict, newFirstFree, newList) = instantiateList instantiateTerm (dict, firstFree, list)
    in (newDict, newFirstFree, Pred name newList)

instantiateClause (dict, firstFree, Clause list1 list2) =
    let (newDict, newFirstFree, newList1) = instantiateList instantiateAtomicF (dict, firstFree, list1)
        (newDict2, newFirstFree2, newList2) = instantiateList instantiateAtomicF (newDict, newFirstFree, list2)
    in (newDict2, newFirstFree2, Clause newList1 newList2)
    
substituteInTerms :: Subs -> [Term] -> [Term]
substituteInTerms (Subs substitution) terms = substituteall substitution terms

substituteInAtomicF :: Subs -> AtomicF -> AtomicF
substituteInAtomicF subs (Pred name terms) = Pred name (substituteInTerms subs terms)

substituteInGoals :: Subs -> Goals -> Goals
substituteInGoals subs list = map (substituteInAtomicF subs) list

computeSldTrees program [] _ = []
computeSldTrees program goals firstFree = catMaybes (map (\clause ->
    let (_, newFirst, Clause list1 list2) = instantiateClause (mapEmpty, firstFree, clause)
    in case flattenedUnifyAtomicF (head goals) (head list1) of
            Nothing -> Nothing
            Just subs@(Subs _) ->
                let newGoals = substituteInGoals subs (list2 ++ (tail goals))
                in Just (SLDTree subs newGoals (computeSldTrees program newGoals newFirst))
    ) program)

sldTree :: Program -> Goals -> SLDTree
sldTree program goals = SLDTree (Subs []) goals (computeSldTrees program goals 1)
    
newtype Parser a = Parser (String -> [(a,String)])

parse (Parser p) = p

instance Monad Parser where
    return a = Parser (\string -> [(a,string)])
    p >>= f = Parser (\string -> concat (map (\(a,string) -> parse (f a) string) (parse p string)))

instance MonadPlus Parser where
    mzero = Parser (\_ -> [])
    mplus p q = Parser (\string -> (parse p string) ++ (parse q string))
    
(+++) :: Parser a -> Parser a -> Parser a
p +++ q = Parser (\string -> take 1 (parse (mplus p q) string))
    
item :: Parser Char
item = Parser (\string -> case string of
                               "" -> []
                               (c:rest) -> [(c,rest)])

sat :: (Char -> Bool) -> Parser Char
sat p = do
    c <- item
    if p c then return c else mzero
    
char :: Char -> Parser Char
char c = sat (c ==)

lower :: Parser Char
lower = sat isLower

upper :: Parser Char
upper = sat isUpper

alphaNum :: Parser Char
alphaNum = sat isAlphaNum

string :: String -> Parser String
string "" = return ""
string (c:rest) = do
    char c
    string rest
    return (c:rest)
    
many :: Parser a -> Parser [a]
many p = (many1 p) +++ return []

many1 :: Parser a -> Parser [a]
many1 p = do
    a <- p
    rest <- many p
    return (a:rest)
    
-- manyOpt :: Parser a -> Parser [a]
-- manyOpt p = mplus (return []) (manyOpt1 p)
-- manyOpt1 p = do
--     a <- p
--     rest <- manyOpt p
--     return (a:rest)
    
sepby :: Parser a -> Parser b -> Parser [a]
p `sepby` sep = (p `sepby1` sep) +++ return []

sepby1 :: Parser a -> Parser b -> Parser [a]
p `sepby1` sep = do
    a <- p
    rest <- many (do
        sep
        p)
    return (a:rest)
    
option :: Parser a -> Parser [a]
option p = (do
    a <- p
    return [a]) +++ return []

space :: Parser String
space = many1 (sat isSpace)

anyChar :: Parser Char
anyChar = sat (\_ -> True)

first :: Parser a -> Parser a
first p = p +++ mzero

blockComment :: Parser String
blockComment = do
    string "/*"
    commentBody
    
commentBody = do
    c <- item
    if c=='*' then needSlashNow else commentBody
    
needSlashNow = do
    c <- item
    if c=='/' then return "" else if c=='*' then needSlashNow else commentBody

lineComment :: Parser String
lineComment = do
    char '%'
    comment <- many (sat (\c -> c/='\n'))
    char '\n'
    return comment
    
whiteSpace :: Parser [String]
whiteSpace = many (blockComment +++ lineComment +++ space)

token :: Parser a -> Parser a
token p = do
    a <- p
    whiteSpace
    return a
    
symb :: String -> Parser String
symb s = token (string s)

apply :: Parser a -> String -> [(a,String)]
apply p = parse (do
    whiteSpace
    p)

program = token (many1 clause)

clause = token ((do
    p <- predicate
    symb "."
    return (Clause [p] [])
    ) +++ (do
    p <- option predicate
    symb ":-"
    pr <- predicate `sepby1` (symb ",")
    symb "."
    return (Clause p pr)
    ))
    
predicate = token (do
    name <- pname
    symb "("
    terms <- term `sepby1` (symb ",")
    symb ")"
    return (Pred name terms)
    )
    
pname = token (do
    c <- lower
    rest <- many alphaNum
    return (c:rest)
    )
    
term = token ((do
    name <- fname
    symb "("
    terms <- term `sepby1` (symb ",")
    symb ")"
    return (App name terms)
    ) +++ (do
    name <- fname
    return (App name [])
    ) +++ (do
    name <- vname
    return (Var name)
    ))
    
fname = token (do
    c <- lower
    rest <- many alphaNum
    return (c:rest)
    )
    
vname = token (do
    c <- upper
    rest <- many alphaNum
    return (c:rest)
    )

filterInput [] = []
filterInput ('%':rest) = ignoreToNewline rest
filterInput ('/':rest) = waitForStar rest
filterInput (c:rest) = c:(filterInput rest)

ignoreToNewline [] = []
ignoreToNewline ('\n':rest) = filterInput rest
ignoreToNewline (c:rest) = ignoreToNewline rest

waitForStar [] = "/"
waitForStar ('*':rest) = waitForStarClosing rest
waitForStar (c:rest) = '/':c:rest

waitForStarClosing ('*':rest) = waitForSlashClosing rest
waitForStarClosing (_:rest) = waitForStarClosing rest

waitForSlashClosing ('*':rest) = waitForSlashClosing rest
waitForSlashClosing ('/':rest) = filterInput rest
waitForSlashClosing (_:rest) = waitForStarClosing rest

parseProgram :: String -> Program
parseProgram input = fst (head (apply program (filterInput input)))


solution (Var n) = showString n
solution (App n []) = showString n
solution (App n list) = showString n . showString "(" . foldl1 (\a b -> a . showString "," . b) (map solution list) . showString ")"

