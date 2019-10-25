module SintaxisFOL (FOL(..), Term(..), Sym, Alfabeto, showFOL, showTerm)
--Sintaxis de la logica de predicados de primer orden con igualdad FOL^=
--mcb
where
--
--------------------------------------------------------
--
type Id         = String        -- Identificadores para: variables, simbolos de predicado, simbolos de funcion
type Cons       = (Id, String)
type Sym        = (Id,Int)      -- Simbolos con aridad: (Identificador, Entero)
type Alfabeto   = ([Sym],[Sym],[Cons]) -- Alfabetos para FOL: (SimbolosDePredicado, SimbolosDeFuncion)
--
-- Terminos:
data Term =   Var Id            -- una variable 
            | Fun Sym [Term]    -- un simbolo de funcion aplicado a una lista de terminos
	    | Cons              -- constantes
            deriving (Eq,Show,Ord,Read)
--
-- Formulas de FOL con igualdad, FOL^=:
data FOL =    Bot | Top | Oimp FOL FOL | Oand FOL FOL | Oor FOL FOL | Oneg FOL   -- False,True,Implicacion,Conjuncion,Dis,Negacion
            | Pred Sym [Term]   -- Predicado:           simbolo de predicado aplicado a una lista de terminos
            | All Id FOL        -- Formula universal:   \forall x : phi 
            | Exi Id FOL        -- Formula existencial: \exists x : phi
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
    --_               -> error $ "showFOL: no definida en este caso, phi="++show phi
--
--
--Ejemplo:
sigma0 :: Alfabeto
sigma0 = -- Alfabeto visto en clase
            ([("H",1),("M",1),("A",2)],  -- simbolos de predicado. esHombre, esMujer, amigoDe
             [("f",1),("g",2)] , []          -- simbolos de funcion
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

-- Tipo substitución:
type Subst = [(Id, Term)]

-- Sustitución en un termino:
apsubT :: Term -> Subst -> Term
apsubT t [] = t

{-
apsubT (V x) [] = V x
apsubT v@(V x) ((y,t):sub) = if x == y then t else apsubT v sub
apsubT c@(F f []) _ = c
apsubT (F f ts) sub = F f $ fmap (\t -> apsubT t sub) ts
-}

--Sustitución en una lista de términos
apsusL :: [Term] -> Subst -> [Term]
apsusL x y = [(apsubT p y) | p <- x]

-- Funcion que nos dice si un termino es igual a un nombre de variable
igu :: Term -> Id -> Bool
igu (Var n1) n2 = if n1 == n2 then True else False


-- Sustitución en una fórmula
apsubF :: FOL -> Subst -> FOL
apsubF f ys = case f of
  (Pred id xs) -> Pred id (apsusL xs ys)

--Funcion que nos dice si una variable se encuentra en las substituciones

estaEn :: Id -> Subst -> Bool
estaEn _ [] = False
estaEn n ((var, term):subst) = if n == var then True else estaEn n subst

--Estados de variables en el universo 'a'
type Estado a = Id -> a

--Interpretación para símbolos de función
type IntF a = Id -> [a] -> a

--Interpretación para símbolos de relación
type IntR a = Id -> [a] -> Bool

--Actualización un estado en una variable 
actEst :: Estado a -> Id -> a -> Estado a
actEst f n v = \y -> if y == n then v else f y

--Interpretación de términos
iTerm :: Estado a -> IntF a -> Term -> a
iTerm f g (Var x) = f x
iTerm f g (Fun (i,a) []) = g i []
iTerm f g (Fun (i,a) y) = g i (iSol f g y)

--Interpretación de lista de terminos
iSol :: Estado a -> IntF a-> [Term] -> [a]
iSol f g [] = []
iSol f g ((Var x):res) = f x:iSol f g res
iSol f g ((Fun (i,a) []):res) = f i:iSol f g res
iSol f g ((Fun x y):res) = iTerm f g (Fun x y): iSol f g res 

--INTERPRETACIÓN Ḿ = <M,I>
--Universo: Enteros
m :: [Int]
m = [0..]

est1 :: Estado Int
est1 "x" = 1
est1 "y" = 2
est1 "z" = 3
est1 x = 0

iF1 :: IntF Int
iF1 "g" = \[a,b,c] -> a+b+c
iF1 "f" = \[a,b,c] -> (a+b)*c
iF1 "h" = \[a,b] -> a*b
iF1 f = \ _ -> 0
