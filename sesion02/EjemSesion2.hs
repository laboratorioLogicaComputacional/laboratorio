{-Facultad de Ciencias UNAM - Lógica Computacional 2019-1 
		  Profesor: Dr. Miguel Carrillo Barajas 
		  Ayudante: Estefanía Prieto Larios
		  Laboratorio: Mauricio Esquivel Reyes-}
module EjemSesion2
where

pote :: Int -> Int -> Int
pote x 0 = 1
pote x y = x * (pote x (y-1))
   
poteB :: Int -> Int -> Int
--Como Int no esta definido recursivamente, poteB no se puede definir usando recursion estructural
poteB x y = case y of -- Observe que y no tiene estructura recursiva.
    0   -> 1
    _   -> if y>0   --como y no tiene estructura recursiva, no se puede usar recursion estructural sobre y
              then x * (poteB x (y-1)) --Aqui hay recursion pero no es recursion estructural.
              else error $ "poteB: el segundo parametro debe ser no negativo, y="++ show y

--pote y poteB no producen los mismos resultados ¿Porqué?

-------------------------------------------------------
data Natural= Cero | Suc Natural deriving(Eq,Show)

suma :: Natural-> Natural -> Natural
--Esta definicion usa recursion estructural sobre y
suma x y= case y of
               Cero     -> x
               Suc z    -> Suc (suma x z)       -- x+(z+1)= (x+z)+1
               --_        -> error $ "suma: no definida en este caso, y="++show y

prod :: Natural-> Natural -> Natural
--Esta definicion usa recursion estructural sobre y
prod x y= case y of
               Cero     -> Cero
               Suc z    -> suma (prod x z) x    -- x*(z+1)= x*z + x
               --_        -> error $ "prod: no definida en este caso, y="++show y

potN :: Natural-> Natural -> Natural
--Como Natural esta definido recursivamente, potN se puede definir usando recursion estructural
--Esta definicion usa recursion estructural sobre y
potN x y= case y of -- Observe que y sí tiene estructura recursiva.
               Cero     -> Suc Cero
               Suc z    -> prod (potN x z) x     -- x^(z+1)= x^z * x
               --_        -> error $ "potN: no definida en este caso, y="++show y

int2Natural :: Int->Natural
int2Natural x = case x of
                     0  -> Cero
                     _  -> if x>0 
                                then Suc (int2Natural (x-1)) --Aqui hay recursion pero no es recursion estructural.
                                else error $ "int2Natural: el parametro debe ser no negativo, x="++ show x

natural2Int :: Natural-> Int 
--Como Natural esta definido recursivamente, natural2Int se puede definir usando recursion estructural
--Esta definicion usa recursion estructural sobre y
natural2Int x = case x of
                     Cero   -> 0
                     Suc z  -> (natural2Int z)+1 
                     --_      -> error $ "natural2Int: no definida en este caso, x="++show x

--Tests:
{-
poteB 2 3== natural2Int (potN (int2Natural 2) (int2Natural 3))
poteB 3 2== natural2Int (potN (int2Natural 3) (int2Natural 2))
-}

--------------------------------------------------------

--Tipo de datos para indices de variables
type Indice = Int

-- Tipo de datos para formulas de la PL
data PL = Top | Bot | Var Indice 
        | Oneg PL | Oand PL PL | Oor PL PL | Oimp PL PL deriving (Eq, Show)

quitaImp :: PL -> PL
--Esta definicion usa recursion estructural sobre phi
quitaImp phi = case phi of --Usando recursion estructural sobre phi
    Top         -> Top
    Bot         -> Bot
    Var x       -> Var x
    Oneg p      -> Oneg (quitaImp p)
    Oand p q    -> Oand (quitaImp p) (quitaImp q)
    Oor p q     -> Oor  (quitaImp p) (quitaImp q)
    Oimp p q    -> Oor  (Oneg (quitaImp p)) (quitaImp q)
    --_      -> error $ "quitaImp: no definida en este caso, phi="++show phi

-- Funcion que nos da las variables de una formula
varsOf :: PL -> [PL]
varsOf phi = case phi of --Usando recursion estructural sobre phi
  Top -> []
  Bot -> []
  Var x -> [Var x]
  Oneg p -> varsOf p
  Oand p q -> varsOf p ++ varsOf q
  Oor p q -> varsOf p ++ varsOf q
  Oimp p q -> varsOf p ++ varsOf q

-- Función que nos da la forma normal de negación
toNNF :: PL -> PL
toNNF phi = case quitaImp phi of -- Usando recursion estructural sobre phi
  Oneg (Oand p q) -> toNNF $ Oor (Oneg $ toNNF p) (Oneg $ toNNF q)
  Oneg (Oor p q) -> toNNF $ Oand (Oneg $ toNNF p) (Oneg $ toNNF q)
  Oneg (Oneg p) -> toNNF p
  Oand p q -> Oand (toNNF p) (toNNF q)
  Oor p q -> Oor (toNNF p) (toNNF q)
  --Oneg Top -> Bot
  --Oneg Bot -> Top
  p -> p
  

