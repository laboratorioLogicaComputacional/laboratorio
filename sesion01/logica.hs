{-Facultad de Ciencias UNAM - Lógica Computacional 2019-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Estefanía Prieto Larios
		  Laboratorio: Mauricio Esquivel Reyes-}

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PL = Top | Bot | Var Indice | Oneg PL | Oand PL PL | Oor PL PL | Oimp PL PL deriving Eq

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

-- Función que cuenta el número de operadores proposicionales
numOp :: PL -> Int
numOp Top = 0
numOp Bot = 0
numOp (Var x) = 0
numOp (Oneg p) = numOp p + 1
numOp (Oand p q) = numOp p + numOp q + 1
numOp (Oor p q) = numOp p + numOp q + 1
numOp (Oimp p q) = numOp p + numOp q + 1

-- Función que elimina las implicaciones
quitaImp :: PL -> PL
quitaImp Top = Top
quitaImp Bot = Bot
quitaImp (Var x) = Var x
quitaImp (Oneg p) = Oneg $ quitaImp p
quitaImp (Oand p q) = Oand (quitaImp p) (quitaImp q)
quitaImp (Oor p q) = Oor (quitaImp p) (quitaImp q)
quitaImp (Oimp p q) = Oor (Oneg $ quitaImp p) (quitaImp q)

-- Función que cuenta los operadores binarios proposicionales
numObin :: PL -> Int
numObin Top = 0
numObin Bot = 0
numObin (Var x) = 0
numObin (Oneg p) = numObin p
numObin (Oand p q) = numObin p + numObin q + 1
numObin (Oor p q) = numObin p + numObin q + 1
numObin (Oimp p q) = numObin p + numObin q + 1

-- Función que transforma una formula a su forma normal negativa
toNNF :: PL -> PL
toNNF p = toNNF $ quitaImp p where
  toNNF (Oneg (Oand p q)) = toNNF $ Oor (Oneg $ toNNF p) (Oneg $ toNNF q)
  toNNF (Oneg (Oor p q)) = toNNF $ Oand (Oneg $ toNNF p) (Oneg $ toNNF q)
  toNNF (Oneg (Oneg p)) = toNNF p
  toNNF (Oand p q) = Oand (toNNF p) (toNNF q)
  toNNF (Oor p q) = Oor (toNNF p) (toNNF q)
  toNNF p = p
