#!/usr/bin/env runhaskell

{-
    Input grammar defined is:
    Form :: Var | Form [ or | and | == | -> ] Form | not Form
    Usage:
    Default output format is csv.
    For example
    ./tables.hs "(A and ((B and C) -> A))" > output.csv
    To execute the program in this way it's necessary to make the script executable (chmod u+x tables.hs)
    Will create a csv file containing the truth table of the formula given in input.
    If more formulas are given the output is just concatenated.
-}

module Tables where
    
import Data.List as List
import Data.Ord (comparing)
import System.Environment(getArgs)
import Text.ParserCombinators.Parsec
import System.Exit
import System.Console.GetOpt
import Data.Map as Map
import Maybe(fromJust, fromMaybe)
-- import Text.Html as Html

-- FIXME fromjusts are not so nice

-- main :: IO ()
main = do
    args <- getArgs
    let parsed = getOpt Permute opts args
    case parsed of
        (flags, arguments, []) ->
             let 
                conf = parseFlags flags defConf
                lev = fromJust $ Map.lookup "Level" conf
                -- point free mapping of printing
                putTab fun = mapM_ (\f -> putStrLn $ fun $ (select (createTable $ formula f) (formula f) lev)) arguments
                -- putTab fun = mapM_ (putStrLn . fun . createTable . formula) arguments
             in
                case (fromJust $ Map.lookup "Type" conf) of
                    "csv" -> putTab tabToCsv
                    "latex" -> putTab tabToLatex
                    "html" -> putTab tabToHtml
        (_, _, msgs) -> error $ concat msgs ++ help

-- We keep manipulating strings without side effects
instructions = "With this simple logic program you can generate truth tables in different formats given a formula in input, formulas goes after options"


-- In this way it only takes the first
parseFlags :: [Flag] -> Conf -> Conf
parseFlags [] def = def
parseFlags (Type t : rest) def = Map.update (\x -> Just t) "Type" (parseFlags rest def)
parseFlags (Level l : rest) def = Map.update (\x -> Just l) "Level" (parseFlags rest def)
    
type Conf = Map String String

defConf = fromList [("Type", "csv"), ("Level", "full")]

help = usageInfo instructions opts

opts :: [OptDescr Flag]
opts = [
        Option ['T'] ["type"] (ReqArg Type "csv") "type of formatted output, possibilities are: csv | tex | html",
        Option ['L'] ["level"] (ReqArg Level "full") "completeness, possibilities are: full | med | min"
        -- Option ['h'] ["help"] (NoArg Help) "show help"
        ]

data Flag = Type String | Level String | Help deriving (Show, Eq, Ord)

{-
    Here there is the logic definition, you can add operators or change
    the meaning of operators defining a different logic
-}
unOps = Map.fromList [("not", Not)]

stToOp = Map.fromList [("and", And), ("or", Or), ("->", Impl), ("==", Eql)]
-- "Inverting" the map
opToSt = Map.fromList [ (x, y) | (y, x) <- Map.toList stToOp ]

unStOp = Map.fromList [("not", Not)]
opToUn = Map.fromList [ (x, y) | (y, x) <- Map.toList unStOp ]

binConstrFun = [(And, (&&)), (Or, (||)), (Impl, (\x y -> (not x) || y)), (Eql, (==))]
unConstrFun = [(Not, not)]


-- FIXME order of table resulting not correct
-- a few examples
taut = BinForm Or (Var "s") (UnForm Not (Var "s"))

usage = unlines $ 
    [
    "Given a logic formula it prints the truth table in the format desired.",
    "Prints optionally to file"]


writeOutput :: FilePath -> String -> IO ()
writeOutput output result =
    writeFile output result


type Id = String

data BinOp = And | Or | Impl | Eql deriving (Eq, Ord)
data UnOp = Not deriving (Eq, Ord)

data Form = Var Id | UnForm UnOp Form | BinForm BinOp Form Form  deriving (Eq, Ord)

type Table = Map Form [Bool]
type Interpretation = [(String, Bool)]

instance Show Form where
    show (Var x) = x
    show (BinForm op x y) = inPar $ unwords [show x, (fromJust $ Map.lookup op opToSt), show y]
    show (UnForm op x) = inPar $ unwords [(fromJust $ Map.lookup op opToUn), show x]

-- get the truth value from a formula and interpretation
calcInt :: Form -> Interpretation -> Bool
calcInt (Var x) i = fromJust (List.lookup x i)
calcInt (BinForm op x y) i  = (fromJust $ List.lookup op binConstrFun) (calcInt x i) (calcInt y i)
calcInt (UnForm op x) i = (fromJust $ List.lookup op unConstrFun) (calcInt x i)

inPar :: String -> String
inPar s = "(" ++ s ++ ")"

binFunC :: (Bool -> Bool -> Bool) -> [Bool] -> [Bool] -> [Bool]
binFunC f v1 v2 = [ f (fst x) (snd x) | x <- (zip v1 v2) ]

unFunC :: (Bool -> Bool) -> [Bool] -> [Bool]
unFunC f v = [ f x | x <- v ]

getVal :: Table -> Form -> [Bool]
getVal t f = fromJust (Map.lookup f t)

createTable :: Form -> Table
createTable f = appFunc (setTable f) f

-- I must always return a Map, in case
-- the formuala is already there we return the same Map
appFunc :: Table -> Form -> Table
appFunc t f@(BinForm op x y) =
    let
        t1 = appFunc t x
        t2 = appFunc t1 y
    in
        -- at this point we assume we have already the elements in the map
        Map.insert f (binFunC (fromJust $ List.lookup op binConstrFun) (getVal t2 x) (getVal t2 y)) t2
        
appFunc t f@(UnForm op x) = 
    let 
        t1 = appFunc t x
    in
        Map.insert f (unFunC (fromJust $ List.lookup op unConstrFun) (getVal t1 x)) t1

appFunc t v@(Var s) =
    case (Map.lookup v t) of
        -- better way to handle errors
        Nothing -> error "variable should be there already, we should never be here"
        -- not making any changes
        Just x -> t

satisf :: Form -> IO ()
satisf f =
    case (sat f) of
        Just t -> putStrLn $ tabToCsv t
        Nothing -> putStrLn "formula not satisfiable"

valid :: Form -> Bool
valid f =
    let t = createTable f
    in all (== True) (getVal t f)

-- FIXME, bug in reporting only the true values
{-
    (A -> B)	A	B
True	True	True
True	True	True
True	True	True
-}
sat:: Form -> Maybe Table
sat form =
    let
        t = createTable form
        isSat = any (== True) (getVal t form)
    in
        case isSat of
            True -> Just $ filterTable (== True) t form
            otherwise -> Nothing

unsat :: Form -> Bool
unsat f = 
    let t = createTable f
    in all (== False) (getVal t f)

getVars :: Form -> [Form]
getVars v@(Var _) = [v]
getVars (BinForm _ x y) = getVars x ++ getVars y
getVars (UnForm _ x) = getVars x

select :: Table -> Form -> String -> Table
select t _ "full" = t
select t f mode = 
    let temp m = case m of
            "mid" -> [(x, fromJust $ Map.lookup x t) | x <- List.filter isVar (Map.keys t)] ++ temp "min"
            "min" -> [(f, fromJust $ Map.lookup f t)]
    in fromList $ temp mode
    where 
        isVar (Var _) = True
        isVar _ = False

-- Creates a new table given a condition satistfied on a certain value
-- FIXME not working correctly
filterTable :: (Bool -> Bool) -> Table -> Form -> Table
filterTable fun t form =
    let 
        indx = List.findIndices fun (fromJust $ Map.lookup form t)
        buildList idxs l = [l !! i | i <- idxs]
    -- Now I build a new table from this
    in
        Map.fromList [(k, buildList indx (fromJust $ Map.lookup k t)) | k <- Map.keys t]

-- output table in csv form, excel compatible
tabToCsv :: Table -> String
tabToCsv t =
    let
        first = putTabIn (List.map show $ Map.keys t)
        strRows = List.map putTabIn (linee t show)
    in
        concat $ intersperse "\r\n" $ (first : strRows)
    where
        putTabIn = concat . intersperse ";"
        
tabToLatex :: Table -> String
tabToLatex t =
    let 
        ccat = \x ->  (concat $ intersperse " & " x) ++ " \\\\"
        first = ccat $ List.map (\x -> toLat (show x) tabToLat) (Map.keys t)
        l = List.map (ccat) (linee t show)
        hl = "\\hline"
        format = "{" ++ (concat $ intersperse "l" [ " | " | x <- [0..(length (Map.keys t))]]) ++ "}"
        env cont = "\\begin{tabular} " ++ format ++ "\n" ++ cont ++ "\\end{tabular}"
        putTab li = List.map (\x -> "\t" ++ x) li
        content = unlines ["\t" ++ hl, "\t" ++ first, "\t" ++ hl] ++ unlines (putTab l) ++ "\t" ++ hl ++ "\n"
    in
        env content

tabToLat :: Subst
tabToLat = [("->", "$ \\rightarrow $")]

type Subst = [(String, String)]

toLat :: String -> Subst -> String
toLat s [] = s
toLat s ((x, y) : rest) = replace (toLat s rest) x y
    
replace :: Eq a => [a] -> [a] -> [a] -> [a]
replace [] _ _ = []
replace s find repl =
    if take (length find) s == find
        then repl ++ (replace (drop (length find) s) find repl)
        else [head s] ++ (replace (tail s) find repl)

tabToHtml :: Table -> String
tabToHtml t = ""

linee :: (Show a) => Table -> (Bool -> a) -> [[a]]
linee t f = [ List.map f x | x <- transpose $ Map.elems t ]


-- The opposite of show is parse
-- unlinee :: [Form] -> []

-- Using the Text.html
-- tabToHtml :: Table -> Html
-- tabToHtml t = 
--     simpleTable [HtmlAttr "border" "1"] [] (mkArray t)
--     where
--         mkArray t = [List.map toHtml $ Map.keys t] ++ [List.map toHtml x | x <- linee show t]


setTable :: Form -> Table
setTable f =
    let 
        -- FIXME not getting duplicates variable at all?
        v = nub $ getVars f
        l = length v
        -- heavy use of replication to create the basic structure
        mkList x y = concat $ replicate x (replicate y True ++ replicate y False)
    in
        Map.fromList $ zip v $ [mkList (2^x) (2^((l-1) - x)) | x <- [0..(l-1)]]

nnf :: Form -> Form
nnf f = clearNot $ toNNF f
-- Translating a formula in negative normal form
toNNF :: Form -> Form
toNNF s@(BinForm op x y) =
    let
        left = toNNF x
        right = toNNF y
    in
        case op of
            Impl -> BinForm Or (UnForm Not left) right
            Eql -> BinForm And (toNNF (BinForm Impl left right)) (toNNF (BinForm Impl right left))
            _ -> s

toNNF (UnForm Not (BinForm op x y)) =
    let
        left = toNNF x
        right = toNNF y
    in
        case op of
            -- And | Or de Morgan rules
            And -> BinForm Or (UnForm Not left) (UnForm Not right)
            Or -> BinForm And (UnForm Not left) (UnForm Not right)
            Impl -> toNNF (UnForm Not (toNNF (BinForm Impl left right)))
            Eql -> toNNF (UnForm Not (toNNF (BinForm Eql left right)))

-- Base cases
toNNF s@(UnForm op x) = s
toNNF v@(Var x) = v

-- Apply recursively the rule "(not (not A)) == A"
clearNot :: Form -> Form
clearNot (UnForm Not (UnForm Not x)) = x
clearNot (UnForm op x) = UnForm op (clearNot x)
clearNot (BinForm op x y) = BinForm op (clearNot x) (clearNot y)
clearNot v@(Var x) = v

simpleTab = setTable myForm
-- 
myForm = BinForm Or (BinForm And (Var "P") (Var "S")) (BinForm Impl (Var "T") (Var "P"))
-- -- generating all possible truth values

formula :: String -> Form
formula x = case (parse term "input" x) of
    Left err -> error ("error in parsing formula " ++ (show x))
    Right res -> res

term :: GenParser Char () Form
term = do
    -- Only one try is enough, but without it doesn't work
    do {c <- try bin; return c}
    <|> do {c <- un; return c}
    <|> do {c <- var; return c}

-- writing a simple parser for logical formulas
var :: GenParser Char () Form
var = do 
    cs <- (many1 upper)
    return (Var cs)
    <?> "error in variable, must but XY"
    
un :: GenParser Char () Form
un = do {
    string "("; spaces;
    u <- un;
    spaces; string ")";
    return u;
    }
    <|> do {
        op <- choice (List.map string $ Map.keys unOps);
        spaces;
        v <- term;
        spaces;
        return ((UnForm $ fromJust $ Map.lookup op unOps) v)
    }
    <?> "error in unary"


bin :: GenParser Char () Form
bin = do {
    string "("; spaces;
    v1 <- term;
    spaces;
    op <- choice (List.map string $ Map.keys stToOp);
    spaces;
    v2 <- term;
    spaces; string ")";
    return ((BinForm $ fromJust $ Map.lookup op stToOp) v1 v2)
    }
    <?> "error in binary operator"