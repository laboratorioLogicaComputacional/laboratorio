module Sesion06
where
import Data.List (nub,union)

-- Tipo de dato indice
type Indice = Int

-- Tipo de dato fórmula
data PL = Top | Bot  | Var Indice
              | Oneg PL 
              | Oand PL PL | Oor PL PL 
              | Oimp PL PL deriving Eq

-- Hacemos parte de Show al tipo PL
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

-- Tipo de Modelo
type Modelo = [Indice]

-- Tipo de Valuacion
type Valuacion = Indice -> Bool

-- Funcion que dados un modelo y una formula nos dice si
-- la formula es satisfacible
satMod :: Modelo -> PL -> Bool
satMod m phi = case phi of
 Top -> True
 Bot -> False
 Var n -> elem n m
 Oneg alpha -> not (satMod m alpha)
 Oand alpha beta -> (satMod m alpha) && (satMod m beta)
 Oor alpha beta -> (satMod m alpha) || (satMod m beta)
 Oimp alpha beta -> not (satMod m alpha) || (satMod m beta)

-- Funcion que transforma un modelo a una valuacion
modeloToValuacion :: Modelo -> Valuacion
modeloToValuacion m = sigma_m
  where
    sigma_m :: Valuacion
    sigma_m v = elem v m

-- Funcion que dada una valuacion y una formula nos dice
-- si la formula es satisfacible
satPL :: Valuacion -> PL -> Bool
satPL valor phi = case phi of
  Top -> True
  Bot -> False
  Var n -> valor n
  Oneg alpha -> not (satPL valor alpha)
  Oand alpha beta -> (satPL valor alpha) && (satPL valor beta)
  Oor alpha beta -> (satPL valor alpha) || (satPL valor beta)
  Oimp alpha beta -> not (satPL valor alpha) || (satPL valor beta)


-- Dada una formula nos dice si es una clausula
esClausula :: PL -> Bool
esClausula phi = case phi of
  Bot -> True
  Var _ -> True
  Oneg alpha -> case alpha of
    Var _ -> True
    _ -> False
  Oor alpha beta -> esClausula alpha && esClausula beta
  _ -> False

-- Dada una formula nos indica si esta en CNF
esCNF :: PL -> Bool
esCNF phi = case phi of
  Oand alpha beta -> esCNF alpha && esCNF beta
  _ -> esClausula phi

-- Dada una formula nos indica si es un termino
esTermino :: PL -> Bool
esTermino phi = case phi of
  Top -> True
  Var _ -> True
  Oneg alpha -> case alpha of
    Var _ -> True
    _ -> False
  Oand alpha beta -> esTermino alpha && esTermino beta
  _ -> False

-- Dada una formula nos indica si esta en DNF
esDNF :: PL -> Bool
esDNF phi = case phi of
  Oor alpha beta -> esDNF alpha && esDNF beta
  _ -> esTermino phi

-- Funcion que elimina las implicaciones de una formula de la PL
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

-- Funcion que distribuye and sobre or
distr :: PL -> PL -> PL
distr phi gam = case (phi,gam) of
  (Oand alpha beta,_) -> Oand (distr alpha gam) (distr beta gam)
  (_,Oand alpha beta) -> Oand (distr phi alpha) (distr phi beta)
  (_,_) -> Oor phi gam

-- Funcion que transforma una formula a CNF
-- Precondicion: la formula debe estar en NNF
toCNF :: PL -> PL
toCNF phi = case phi of
  Top -> Top
  Bot -> Bot
  Var n -> Var n
  Oneg alpha -> Oneg (toCNF alpha)
  Oand alpha beta -> Oand (toCNF alpha) (toCNF beta)
  Oor alpha beta -> distr (toCNF alpha) (toCNF beta) 

-- Funcion que transforma una formula a CNF
-- Precondicion: Ninguna
cnf :: PL -> PL
cnf = toCNF . toNNF

-- Material para la sesion 06

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

-- Nos da la lista de clausulas de una formula
-- Precondición: la formula debe estar en CNF
listClau :: PL -> [PL]
listClau phi = case phi of
  Oand alpha beta -> listClau alpha ++ listClau beta
  _ -> [phi]

-- Nos da las clasusulas de una formula en forma de listas de indices
-- Precondición: la formula debe estar en CNF
liteCNF :: PL -> [[Indice]]
liteCNF phi = if esCNF phi then
  (map varsOf (listClau phi))
  else
  error $ "liteCNF: No esta en CNF"
  
-- Nos da la lista de terminos de una formula
-- Precondición: la formula debe estar en DNF
listTerm :: PL -> [PL]
listTerm phi = case phi of
  Oor alpha beta -> listTerm alpha ++ listTerm beta
  _ -> [phi]

-- Nos da los terminos de una formula en forma de lista de indices
-- Precondición: la formula debe estar en DNF
liteDNF :: PL -> [[Indice]]
liteDNF phi = if esDNF phi then
  (map varsOf (listTerm phi))
 else
  error $ "liteDNF: No esta en DNF"

-- Nos indica si en una lista de indices existen dos complementarios
comple :: [Indice] -> Bool
comple ls = case ls of
  [] -> False
  x:xs -> if elem (-x) xs then True  else comple xs

-- Nos dice si una formula en CNF es valida
-- Precondición: la formula debe estar en CNF
valCNF :: PL -> Bool
valCNF phi = if esCNF phi then
  and (map comple (liteCNF phi))
 else
  error $ "valCNF: no esta en CNF"




--
powerSet :: [t] -> [[t]]
powerSet l  = case l of
  []   -> [[]]
  x:xs -> powerXS ++ [x:w | w <- powerXS] -- ¿Porqué? Usar ejemplos
    where
      powerXS = powerSet xs 

--Decide si phi es valida. True sii phi \in VAL-PL, i.e. para todo modelo m: m |= phi.
enValPL :: PL -> Bool
enValPL phi = and [(satMod m phi) | m <- powerSet $ varsOf (phi) ]

--Decide si phi es satisfactible. True sii phi \in SAT-PL, i.e. existe un modelo m: m |= phi.
enSatPL :: PL -> Bool
enSatPL phi = or [(satMod m phi) | m <- powerSet $ varsOf (phi) ]

satDNF :: PL -> Bool
satDNF phi = or (map not (map comple (liteDNF phi)))
{-

-- Nos dice si una formula en DNF es satisfacible
-- Precondición: la formula debe estar en DNF
satDNF phi = if esDNF phi then
  not (and (map comple (liteDNF phi)))
 else
  error $ "satDNF: no esta en DNF"

-- Tipos de datos para formulas de Horn
data Hatom  =  Htop | Hbot | Hvar Indice deriving (Eq) -- Atomos para clausulas de Horn
data Fhorn  =   Himp [Hatom] Hatom                      -- Clausula de Horn: Premisa=[atomo1,...,atomoN] -> Conclusion=Atomo
              | Hand Fhorn Fhorn  deriving (Eq, Show)   -- Conjuncion de formulas de Horn
--
instance Show Hatom where
  show a = case a of
     Htop   -> "TT"
     Hbot   -> "FF"
     Hvar n -> "v"++show n


marcaFormulaHorn :: [Hatom] -> Fhorn -> [Hatom]
--Mientras phi tenga una clausula con conclusion marcable, marca las conclusiones de dichas clausulas.
--Def. f es una clausula con conclusión marcable si: f= p->c, los atomos de p están marcados, y c no está marcada.
marcaFormulaHorn lMarcados phi = 
    if cHornMarcables==[]
        then lMarcados
        else marcaFormulaHorn lMarcadosNew phi
    where
    cHornMarcables  = clausulasHmarcables lMarcados phi
    lMarcadosNew    = marcaConclusiones lMarcados cHornMarcables
--
enSatHorn :: Fhorn -> Bool
--True si phi \in SAT-Horn, i.e. phi es un formula de Horn y existe sigma tal que sigma |= phi.
enSatHorn phi = if Hbot `elem` (marcaFormulaHorn [Htop] phi)
                    then False
                    else True
-}