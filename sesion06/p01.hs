module Sesion06
where
import Data.List (nub,union)

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PL = Top | Bot  | Var Indice
              | Oneg PL 
              | Oand PL PL | Oor PL PL 
              | Oimp PL PL deriving (Eq, Show)
-- Tipo de Modelo
type Modelo = [Indice]

-- Tipo de Valuacion
type Valuacion = Indice -> Bool

satMod :: Modelo -> PL -> Bool
satMod m phi = case phi of
 Top -> True
 Bot -> False
 Var n -> elem n m
 Oneg alpha -> not (satMod m alpha)
 Oand alpha beta -> (satMod m alpha) && (satMod m beta)
 Oor alpha beta -> (satMod m alpha) || (satMod m beta)
 Oimp alpha beta -> not (satMod m alpha) || (satMod m beta)


modeloToValuacion :: Modelo -> Valuacion
modeloToValuacion m = sigma_m
  where
    sigma_m :: Valuacion
    sigma_m v = elem v m



satPL :: Valuacion -> PL -> Bool
satPL valor phi = case phi of
  Top -> True
  Bot -> False
  Var n -> valor n
  Oneg alpha -> not (satPL valor alpha)
  Oand alpha beta -> (satPL valor alpha) && (satPL valor beta)
  Oor alpha beta -> (satPL valor alpha) || (satPL valor beta)
  Oimp alpha beta -> not (satPL valor alpha) || (satPL valor beta)


esClausula :: PL -> Bool
esClausula phi = case phi of
  Bot -> True
  Var _ -> True
  Oneg alpha -> case alpha of
    Var _ -> True
    _ -> False
  Oor alpha beta -> esClausula alpha && esClausula beta
  _ -> False

esCNF :: PL -> Bool
esCNF phi = case phi of
  Oand alpha beta -> esCNF alpha && esCNF beta
  _ -> esClausula phi

esTermino :: PL -> Bool
esTermino phi = case phi of
  Top -> True
  Var _ -> True
  Oneg alpha -> case alpha of
    Var _ -> True
    _ -> False
  Oand alpha beta -> esTermino alpha && esTermino beta
  _ -> False
     
esDNF :: PL -> Bool
esDNF phi = case phi of
  Oor alpha beta -> esDNF alpha && esDNF beta
  _ -> esTermino phi


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
noImpNNF :: PL -> PL
noImpNNF phi = case phi of
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
    Oneg g -> noImpNNF g
    Oand g h -> noImpNNF (Oor (Oneg g) (Oneg h))
    Oor g h -> noImpNNF (Oand (Oneg g) (Oneg h))

  Oand alfa beta -> Oand (noImpNNF alfa) (noImpNNF beta)
  Oor alfa beta -> Oor (noImpNNF alfa) (noImpNNF beta)

-- Función que transforma una formula a su forma normal de negación.
-- Precondición: ninguna.
toNNF :: PL -> PL
toNNF = noImpNNF . quitaImp -- Composicion de funciones.


distr :: PL -> PL -> PL
distr phi gam = case (phi,gam) of
  (Oand alpha beta,_) -> Oand (distr alpha gam) (distr beta gam)
  (_,Oand alpha beta) -> Oand (distr phi alpha) (distr phi beta)
  (_,_) -> Oor phi gam

toCNF :: PL -> PL
toCNF phi = case phi of
  Top -> Top
  Bot -> Bot
  Var n -> Var n
  Oneg alpha -> Oneg (toCNF alpha)
  Oand alpha beta -> Oand (toCNF alpha) (toCNF beta)
  Oor alpha beta -> distr (toCNF alpha) (toCNF beta) 


cnf :: PL -> PL
cnf = toCNF . toNNF



-- Conjunto de variables (solo indices) de una formula.
varsOf :: PL -> [Indice]
varsOf phi = case phi of
  Top         -> [] 
  Bot         -> []
  Var v       -> [v]
  Oneg g      -> case g of
    Var n -> [-n]
    _ -> varsOf g
  g `Oand` h    -> nub $ varsOf g ++ (varsOf h) -- nub elimina repeticiones para que la lista sea un conjunto.
  g `Oor`  h    -> nub $ varsOf g ++ (varsOf h) -- nub elimina repeticiones para que la lista sea un conjunto.
  g `Oimp` h    -> nub $ varsOf g ++ (varsOf h) -- nub elimina repeticiones para que la lista sea un conjunto.
    --_           -> error $ "varsOf: no definida en este caso, phi="++show phi

listClau :: PL -> [PL]
listClau phi = case phi of
  Oand alpha beta -> listClau alpha ++ listClau beta
  _ -> [phi]

liteCNF :: PL -> [[Indice]]
liteCNF phi = if esCNF phi then
  (map varsOf (listClau phi))
 else
  error $ "liteCNF: No esta en CNF"

listTerm :: PL -> [PL]
listTerm phi = case phi of
  Oor alpha beta -> listTerm alpha ++ listTerm beta
  _ -> [phi]

liteDNF :: PL -> [[Indice]]
liteDNF phi = if esDNF phi then
  (map varsOf (listTerm phi))
 else
  error $ "liteDNF: No esta en DNF"