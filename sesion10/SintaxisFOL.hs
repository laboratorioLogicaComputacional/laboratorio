module SintaxisFOL (FOL(..), Term(..), Sym, Alfabeto, showFOL, showTerm)
--Sintaxis de la logica de predicados de primer orden con igualdad FOL^=
--mcb
where
--
--------------------------------------------------------
--
type Id         = String        -- Identificadores para: variables, simbolos de predicado, simbolos de funcion
type Sym        = (Id,Int)      -- Simbolos con aridad: (Identificador, Entero)
type Alfabeto   = ([Sym],[Sym]) -- Alfabetos para FOL: (SimbolosDePredicado, SimbolosDeFuncion)
--
-- Terminos:
data Term =   Var Id            -- una variable 
            | Fun Sym [Term]    -- un simbolo de funcion aplicado a una lista de terminos
            deriving (Eq,Show,Ord,Read)
--
-- Formulas de FOL con igualdad, FOL^=:
data FOL =    Bot | Top | Oimp FOL FOL | Oand FOL FOL | Oor FOL FOL | Oneg FOL -- False,True,Implicacion,Conjuncion,Dis,Negacion
            | Pred Sym [Term]   -- Predicado:           simbolo de predicado aplicado a una lista de terminos
            | All Id FOL        -- Formula universal:   \forall x : phi 
            | Exi Id FOL        -- Formula existencial: \exists x : phi
            | Equ Sym [Term]    -- Igualdad:            simbolo de predicado aplicado a una lista de terminos
            deriving (Eq,Show,Ord,Read)
--
--
--
--
-- Funciones para mostrar terminos y formulas:
--
showTerm :: Term -> String
-- Muestra un termino 
showTerm t  = case t of
                Var v           -> v
                Fun (f,n) lt    -> if length lt/=n 
                                      then error $ "showTerm: el numero de parametros de "++f
                                           ++ " es distinto de la aridad, "++show n
                                      else f++"("++ showLterms lt ++")"
--
showLterms :: [Term] -> String
-- Muestra una lista de terminos
showLterms lt = case lt of
                     []     -> ""
                     t:l    -> showTerm t++"," ++ showLterms l
--
showFOL :: FOL -> String
-- Muestra una formula de la FOL 
showFOL phi = case phi of
    Bot         -> "FF"
    Top         -> "TT"
    Oimp p q    -> "("++ (showFOL p) ++" -> "++ (showFOL q) ++")" 
    Oand p q    -> "("++ (showFOL p) ++" & "++ (showFOL q) ++")"
    Oor  p q    -> "("++ (showFOL p) ++" | "++ (showFOL q) ++")"
    Oneg p      -> "¬"++(showFOL p)
    --
    Pred (p,n) lt   -> if length lt==n 
                            then p++"("++ showLterms lt ++")"
                            else error $ "showFOL: el numero de parametros de "++p
                                ++ " es distinto de la aridad, "++show n
    --
    All x phi       -> "(ForAll "++x++ ": " ++ (show phi)++")"   -- XXX
    Exi x phi       -> "(Exists "++x++ ": " ++ (show phi)++")"   -- XXX
    Equ (p,n) lt    -> if (p,n) /= ("=",2) 
                            then error $ "showFOL: simbolo de igualdad incorrecto: "++ show (p,n)
                            else if length lt /= n 
                                    then error $ "showTerm: el numero de parametros de "++p
                                        ++ " es distinto de la aridad, "++show n
                                    else p++"("++ showLterms lt ++")"
    --_               -> error $ "showFOL: no definida en este caso, phi="++show phi
--
--
--Ejemplo:
sigma0 :: Alfabeto
sigma0 = -- Alfabeto visto en clase
            ([("H",1),("M",1),("A",2)],  -- simbolos de predicado. esHombre, esMujer, amigoDe
             [("f",1),("g",2)]           -- simbolos de funcion
            )

-- Ejemplos
-- P(x,y)
f1 = Pred ("P",2) [Var "x", Var "y"]

-- Q(a,h(w))
f2 = Pred ("Q",2) [Var "a", (Fun ("h",1) [Var "w"])]

-- R(x) → x = b
f3 = Oimp (Pred ("R",1) [Var "x"]) (Equ ("=",2) [Var "x", Var "b"])


-- ¬R(z) ⋁ (S(a) ⋀ f(x) =z)
f4 = Oor (Oneg $ Pred ("R",1) [Var "z"]) (Oand (Pred ("S",1) [Var "a"]) (Equ ("=",2) [(Fun ("f",1) [Var "x"]), Var "z"]))

-- ∀xQ(x,g(y))
f5 = All "x" $ Pred ("Q",2) [Var "x", Fun ("g",1) [Var "y"]]

-- ∀x∃yP(x,y)
f6 = All "x" $ Exi "y" $ Pred ("P",2) [Var "x", Var"y"]



-- Varibales libres en términos
varT :: Term -> [Id]
varT t = case t of
  Var x -> [x]
  Fun _ [] -> []
  Fun n xs -> concat $ map varT xs


-- Variables libres en una Formula
fv :: FOL -> [Id]
fv phi = case phi of
  Pred _ lt -> concat $ map varT lt
  Equ (p,n) lt ->  concat $ map varT lt
  Oimp a b -> fv a ++ fv b
  Oand a b -> fv a ++ fv b
  Oor a b -> fv a ++ fv b
  Oneg a -> fv a
  All x a -> elimn x (fv a)
  Exi x a -> elimn x (fv a)
  Top -> []
  Bot -> []


-- Funcion que elimina el nombre de una variable en una lista de nombres de variables
elimn :: Id -> [Id] -> [Id]
elimn i li = [ v | v <- li, v /= i]


