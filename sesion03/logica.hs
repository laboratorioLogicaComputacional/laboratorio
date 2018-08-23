{-Facultad de Ciencias UNAM - Lógica Computacional 2019-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Estefanía Prieto Larios
		  Laboratorio: Mauricio Esquivel Reyes-}

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PL = Top | Bot | Var Indice -- Casos base
  | Oneg PL | Oand PL PL | Oor PL PL | Oimp PL PL deriving Eq -- Casos 

-- Hacemos parte de Show al tipo LP
instance Show PL where
  show Top = "T"
  show Bot = "F"
  show (Var x) = "v"++show x
  -- Casos para la negación
  show (Oneg (Var x)) = "¬" ++ show x
  show (Oneg p) = "¬(" ++ show p ++ ")"
  -- Casos para la conjunción
  show (Oand (Var x) (Var y)) = show x ++ "&" ++ show y
  show (Oand (Var x) q) = show x ++ "&(" ++ show q ++ ")"
  show (Oand p (Var y)) = "(" ++ show p ++ ")&" ++ show y
  show (Oand p q) = "("++show p++")&("++show q++")"
  -- Casos para la disyunción
  show (Oor (Var x) (Var y)) = show x ++ "|" ++ show y
  show (Oor (Var x) q) = show x ++ "|(" ++ show q ++ ")"
  show (Oor p (Var y)) = "(" ++ show p ++ ")|" ++ show y
  show (Oor p q) = "("++show p++")|("++show q++")"
    -- Casos para la implicacion
  show (Oimp (Var x) (Var y)) = show x ++ "-->" ++ show y
  show (Oimp (Var x) q) = show x ++ "-->(" ++ show q ++ ")"
  show (Oimp p (Var y)) = "(" ++ show p ++ ")-->" ++ show y
  show (Oimp p q) = "("++show p++")-->("++show q++")"


-- Función que quita implicaciones de una formula
quitaImp :: PL -> PL
quitaImp phi = case phi of
     Top -> Top
     Bot -> Bot
     Var x -> Var x
     Oneg x -> Oneg (quitaImp x)
     Oand x y -> Oand (quitaImp x) (quitaImp y)
     Oor x y -> Oor (quitaImp x) (quitaImp y)
     Oimp x y -> Oor (quitaImp (Oneg  x)) (quitaImp y)

-- Función que transforma una formula su forma normal de negación
-- Precondición: no debe tener implicaciones.
noImp2NNF :: PL -> PL
noImp2NNF phi = case phi of
  -- Casos base:
  Top -> phi
  Bot -> phi
  Var v -> Var v
  -- Casos recursivos:
  Oneg alfa -> case alfa of
    -- Casos bases (alfa)
    Top -> Bot
    Bot -> Top
    Var v -> Oneg (Var v)
    -- Casos recursivos (alfa)
    Oneg g -> noImp2NNF g
    Oand g h -> noImp2NNF (Oor (Oneg g) (Oneg h))
    Oor g h -> noImp2NNF (Oand (Oneg g) (Oneg h))

  Oand alfa beta -> Oand (noImp2NNF alfa) (noImp2NNF beta)
  Oor alfa beta -> Oor (noImp2NNF alfa) (noImp2NNF beta)

-- Función que transforma una formula a su forma normal de negación.
-- Precondición: ninguna.
toNNF2 :: PL -> PL
toNNF2 = noImp2NNF . quitaImp -- Composicion de funciones.

-- Función que nos da las disyunciones de una formula.
disy :: PL -> [PL]
disy phi = case phi of
  Top -> []
  Bot -> []
  Var p -> []
  Oneg alfa -> disy alfa
  Oand alfa beta -> disy alfa ++ disy beta
  Oor alfa beta -> disy alfa ++ disy beta ++ [Oor alfa beta]
  Oimp alfa beta -> disy alfa ++ disy beta

-- Función que nos da el número de disyunciones de una formula
numdisy :: PL -> Int
numdisy phi = case phi of
  Top -> 0
  Bot -> 0
  Var p -> 0
  Oneg alfa -> numdisy alfa
  Oand alfa beta -> numdisy alfa + numdisy beta
  Oor alfa beta -> numdisy alfa + numdisy beta + 1
  Oimp alfa beta -> numdisy alfa + numdisy beta

--isInNNF phi=True si phi in NNF, i.e. isInNNF(phi) = True si:
--    i)  el operador "->" no ocurre en phi.
--    ii) las ocurrencias de "¬" en phi se aplican solamente a variables proposicionales.
isInNNF :: PL -> Bool
isInNNF phi = case phi of
  --Casos base:
  Top                 -> True
  Bot                 -> True
  Var _               -> True
  --Casos recursivos:
  Oneg alfa           -> case alfa of -- Es decir, phi = ¬alfa.
    Var _   -> True  -- isInNNF(¬alfa)=True  si alfa es una variable.
    _       -> False -- isInNNF(¬alfa)=False si alfa no es una variable.
  alfa `Oand` beta    -> (isInNNF alfa) && (isInNNF beta)
  alfa `Oor`  beta    -> (isInNNF alfa) && (isInNNF beta)
  _    `Oimp` _       -> False    --phi in NNF => "->" no ocurre en phi
