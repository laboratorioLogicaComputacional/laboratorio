module DeduccionNatural6 (ReglaDN(..), showCheckDedNat) 
--Verifica que los pasos de una deduccion natural sean correctos.
--mcb
where
import Data.List as L (delete,(\\)) -- (nub,union)
--import Data.Set as S
import SintaxisPL
--
--
---------------------------------------------------------------------------------------------------------------
-- Deduccion Natural:
--
data ReglaDN = 
              Icon  Int Int | Econ1 Int | Econ2 Int     -- reglas para la conjuncion
            | Iimp  Int Int | Eimp Int Int              -- reglas para la implicacion
            | Ineg  Int Int | Eneg Int Int              -- reglas para la negacion
            | Idis1 Int | Idis2 Int | Edis Int Int Int  -- reglas para la disyuncion
            | Ebot  Int -- regla para bottom (no hay introduccion de bottom)
            | Isup      -- regla para suposiciones (Assumptions). Las suposiciones se introducen con cajas en una prueba. 
            | Prem      -- ragla para premisas (premises). Las premisas se consideran validas en una prueba.
            | E2neg Int -- regla para eliminacion de doble negacion 
            | Itop      -- regla para top (no hay eliminacion de top). Esta regla no se usa.
            | Copy Int  -- Esta regla permite repetir una formula previa. Huth-Ryan p.20:
                -- The rule ‘copy’ allows us to repeat something that we know already. 
                -- We need to do this in this example, because the rule →i requires that we end the inner box with p. 
                -- The copy rule entitles us to copy formulas that appeared before,
                -- unless they depend on temporary assumptions whose box has already been closed. 
                -- Though a little inelegant, this additional rule is a small price to pay
                -- for the freedom of being able to use premises, or any other ‘visible’ formulas, more than once.            
            deriving (Eq,Show)
--
type Caja   = (Int,Int) -- Caja de suposiciones. Huth-Ryan p.12.
                        -- (i,j), 0<i<=j: caja cerrada de i a j
                        -- (i,j), 0=j<i : caja abierta de i a ...
            -- Proofs may nest boxes or open new boxes after old ones have been closed.
            -- There are rules about which formulas can be used at which points in the proof. 
            -- Generally, we can only use a formula φ in a proof at a given point if:
            --      (1) that formula occurs prior to that point and
            --      (2) no box which encloses that occurrence of φ has been closed already.
            -- The line immediately following a closed box has to match 
            -- the pattern of the conclusion of the rule that uses the box. 
            -- For implies-introduction, this means that we have to continue after the box with φ → ψ, 
            -- where φ was the first and ψ the last formula of that box.
--
type Paso   = (PL,ReglaDN,[Caja])   -- Un paso de una prueba, 
                                    -- (formula,regla_aplicada,listaDeCajas)
type NumPaso= (Int,Paso)            -- Un paso numerado, (numero, paso)
--
phiPasoNum :: Int->[NumPaso] -> PL
--formula del paso numero i en lpasos
phiPasoNum i lpasos = case mpi of
                    Just (fi,_,_) -> fi
                    _               -> error $ "phiPasoNum: i fuera de rango, (i,lpasos)="++show (i,lpasos)
    where
    mpi = lookup i lpasos
--
ultimoPaso :: [NumPaso] -> NumPaso 
ultimoPaso lpasos
    | lpasos /= [] = (n,p)
--     | otherwise = error $ "ultimoPaso: no hay pasos, lpasos="++show lpasos
    | otherwise = (0,(Top,Itop,[]))   -- (nN,(fN,r,lcN))
    where
    (n,p)   = last lpasos
--
eqCon1 :: PL -> PL -> Bool
-- True si g es el conyunto 1 de f
eqCon1 g f = case f of
              f1 `Oand` _   -> g == f1
              _             -> False
--
eqCon2 :: PL -> PL -> Bool
-- True si g es el conyunto 2 de f
eqCon2 g f = case f of
              _ `Oand` f2   -> g == f2
              _             -> False
--
getDis1 :: PL -> PL
--
getDis1 g = case g of
  f1 `Oor` _ -> f1
  _ -> error $ "No es una disyuncion"
--
getDis2 :: PL -> PL
--
getDis2 g = case g of
  _ `Oor`f2 -> f2
  _ -> error $ "No es una disyuncion"
--
--
eqDis1 :: PL -> PL -> Bool
-- True si g es el disyunto 1 de f
eqDis1 g f = case f of
              f1 `Oor` _ -> g == f1
              _          -> False
--
eqDis2 :: PL -> PL -> Bool
-- True si g es el disyunto 1 de f
eqDis2 g f = case f of
              _ `Oor` f2 -> g == f2
              _          -> False
--
eqImp1 :: PL -> PL -> Bool
-- True si g es el disyunto 1 de f
eqImp1 g f = case f of
              f1 `Oimp` _ -> g == f1
              _          -> False
--
eqImp2 :: PL -> PL -> Bool
-- True si g es el disyunto 1 de f
eqImp2 g f = case f of
              _ `Oimp` f2 -> g == f2
              _          -> False
--
usableP :: Int->[Caja]->Int -> Bool
-- True si el paso j es usable. Es decir, si 0<j<=nN y j no esta en ninguna caja cerrada.
usableP j lcajas nN =   0<j && j<=nN    -- j>0 y j es menor o igual que el ultimo paso previo
                    && and [not (k<=j && j<=l) | (k,l) <- cajasCerradas] -- j no está en ninguna caja cerrada.
                    where
                    cajasCerradas= [(k,l) | (k,l) <- lcajas, l/=0]
--
cerrarCaja :: [Caja]->Int->Int -> [Caja]
-- cierra correctamente la caja (i,0) de lcajas. 
cerrarCaja lcajas i j
    | (i,0) `notElem` cajasAbiertas     = error laCajaNoEstaAbierta
    | cajasInternasAbiertas /= []       = error hayUnaCajaInternaAbierta
    | j <= 0                            = error jDebeSerPositivo 
    | otherwise                         = (i,j): (L.delete (i,0) lcajas)
    where
    laCajaNoEstaAbierta     = "\n cerrarCaja: la caja "++show (i,j) ++" no esta abierta."
    hayUnaCajaInternaAbierta= "\n cerrarCaja: hay al menos una caja interna abierta: "++show (head cajasInternasAbiertas)
    jDebeSerPositivo        = "\n cerrarCaja: el final de la caja debe se positivo, j= "++show j
    cajasAbiertas           = [(k,l) | (k,l) <- lcajas, l==0]
    cajasInternasAbiertas   = [(k,l) | (k,l) <- cajasAbiertas, i<k]
--
checkPaso :: [PL]->[NumPaso]->NumPaso -> Bool
checkPaso lprem lpp p = -- listaDePremisas listaDePasosPrevios pasoActual
    case p of
         --Reglas para la conjuncion:
        (m,(g `Oand` h,Icon i j,lc)) -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && usableP j lc nN  -- j es usable, j<nN && j no esta en una caja cerrada 
                                        && g==fi && h==fj   -- introduccion de la conjuncion: fi,fj |- fi & fj
                                            where 
                                            fi= phiPasoNum i lpp -- paso i
                                            fj= phiPasoNum j lpp -- paso j
        (m,(g,Econ1 i,lc))           -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && g `eqCon1` fi    -- g es el conyunto 1 de fi: gi & hi |- gi
                                            where 
                                            fi = phiPasoNum i lpp -- paso i, fi= gi & hi
        (m,(h,Econ2 i,lc))           -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && h `eqCon2` fi    -- h es el conyunto 2 de fi: gi & hi |- hi
                                            where 
                                            fi = phiPasoNum i lpp -- paso i, fi= gi & hi
        --Reglas para la disyuncion:
        (m,(g `Oor` _, Idis1 i, lc)) -> lpp /= [] -- hay pasos previos
                                        && m==nN+1 -- m se incrementa en 1.
                                        && usableP i lcN nN -- i es usable, i<nN && i no esta en una caja cerrada
                                        && lc == lcN -- las cajas no cambiaron
                                        && g == f1
                                            where 
                                            f1 = phiPasoNum i lpp
        (m,(_ `Oor` g, Idis2 i, lc)) -> lpp /= [] -- hay pasos previos
                                        && m==nN+1 -- m se incrementa en 1.
                                        && usableP i lcN nN -- i es usable, i<nN && i no esta en una caja cerrada
                                        && lc == lcN -- las cajas no cambiaron
                                        && g == f1
                                            where 
                                            f1 = phiPasoNum i lpp
        (m,(f, Edis i j k, lc)) -> lpp /= []
                                        && m == nN+1
                                        && usableP i lcN nN -- i es usable, i<nN && i no esta en una caja cerrada
                                        && usableP j lcN nN -- j es usable, j<nN && j no esta en una caja cerrada
                                        && usableP k lcN nN -- k es usable, k<nN && k no esta en una caja cerrada
                                        && lc == lcN -- las cajas no cambiaron
                                        && a `eqDis1` fi
                                        && b `eqDis2` fi
                                        && a `eqImp1` fj && b `eqImp1` fk
                                        && f `eqImp2` fj && f `eqImp2` fk
                                            where
                                              fi = phiPasoNum i lpp
                                              fj = phiPasoNum j lpp
                                              fk = phiPasoNum k lpp
                                              a = getDis1 fi
                                              b = getDis2 fi
                                            
        --Reglas para la implicacion:
        (m,(_ `Oimp` h,Iimp i j,lc)) -> lpp/=[]                  -- hay pasos previos
                                        && m==nN+1                  -- m se incrementa en 1.
                                        && j==nN && h==fN           -- h debe ser la del paso inmediato anterior.Huth-Ryan
                                        && lc L.\\ lcNijCerrada==[] -- se cerro la caja (i,j)
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && usableP j lcN nN -- j es usable, j<=nN && j no esta en una caja cerrada 
                                        && h==fj            -- introduccion de la implicacion: ...fj |- g->fj 
                                            where 
                                            lcNijCerrada= cerrarCaja lcN i j
                                            fj= phiPasoNum j lpp -- formula del paso j.
        (m,(h,Eimp i j,lc))          -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && usableP j lc nN  -- j es usable, j<nN && j no esta en una caja cerrada 
                                        && fj==fi `Oimp` h  -- eliminacion de la implicacion: fi,fi->h |- h
                                            where 
                                            fi= phiPasoNum i lpp -- paso i
                                            fj= phiPasoNum j lpp -- paso j
        --Reglas para la negacion (¬g = g -> Bot):
        (m,(Oneg _,Ineg i j,lc))     -> lpp/=[]                  -- hay pasos previos
                                        && m==nN+1                  -- m se incrementa en 1.
                                        && j==nN && Bot==fN         -- Bot debe ser la del paso inmediato anterior.Huth-Ryan
                                        && lc L.\\ lcNijCerrada==[] -- se cerro la caja (i,j)
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && usableP j lcN nN -- j es usable, j<=nN && j no esta en una caja cerrada 
                                        && Bot==fj  -- introduccion de la negacion: g...Bot |- g->Bot = ¬g
                                            where 
                                            lcNijCerrada= cerrarCaja lcN i j
                                            fj= phiPasoNum j lpp -- formula del paso j.
        (m,(Bot,Eneg i j,lc))        -> lpp/=[]              -- hay pasos previos
                                        && m==nN+1              -- m se incrementa en 1.
                                        && lc== lcN             -- las cajas no cambiaron
                                        && usableP i lc nN      -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && usableP j lc nN      -- j es usable, j<nN && j no esta en una caja cerrada 
                                        && fj==fi `Oimp` Bot    -- eliminacion de la negacion: fi,fi->Bot |- Bot 
                                            where 
                                            fi= phiPasoNum i lpp -- paso i
                                            fj= phiPasoNum j lpp -- paso j
        -- Regla para suposiciones (Assumptions):
        (m,(_,Isup,lc))              -> m==nN+1                          -- m se incrementa en 1.
                                        && lc== lcN ++ [(nN+1,0)]           -- la caja (nN+1,0) se agrego a las cajas
        -- Regla para premisas (Premises):
        (m,(f,Prem,_))                -> f `elem` lprem   -- basta que f este en la lista de premisas
                                        && m==nN+1          -- m se incrementa en 1.
        -- Regla para Bot (no hay introduccion de Bot):
        (m,(_,Ebot i,lc))            -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lc nN  -- i es usable, i<nN && i no esta en una caja cerrada 
                                        && fi==Bot          -- eliminacion de Bot: Bot |- f
                                            where
                                            fi= phiPasoNum i lpp -- paso i
        -- Regla para Top:
        (m,(Top,Itop,_))              -> True -- Top se puede derivar sin restricciones
                                        && m==nN+1          -- m se incrementa en 1.
        -- Regla para usar formulas previas:
        (m,(f,Copy i,lc))            -> lpp/=[]          -- hay pasos previos
                                        && m==nN+1          -- m se incrementa en 1.
                                        && lc== lcN         -- las cajas no cambiaron
                                        && usableP i lcN nN -- i es usable, i<=nN && i no esta en una caja cerrada 
                                        && f== fi           -- f es la formula del paso i
                                            where 
                                            fi= phiPasoNum i lpp -- formula del paso i.
        _                               -> error $ "checkPaso: caso no implementado aun, p="++show p
        where
        (nN,(fN,_,lcN))= ultimoPaso lpp
--
--Tests:
--checkPaso [] [] (Var 1,Isup,S.fromList [Var 1],[(1,0)])
--let{v1=Var 1; lpasos=[(1,(v1,Isup,S.fromList [v1],[(1,0)]))]; p=(v1 `Oimp` v1,Iimp 1 1,S.fromList [],[(1,1)])} in checkPaso [] lpasos p
--checkPaso [] [(1,(Var 1,Isup,S.fromList [Var 1],[]))] (Var 1 `Oimp` (Var 1),Iimp 1 1,S.fromList [],[])
--let {lpasos=[]; f=Var 1; r=Isup; ls=S.fromList [f]; lc=[(1,0)]} in checkPaso [] lpasos (f,r,lc)
--checkPaso [] [] (Var 1,Isup,S.fromList [Var 1],[(1,0)])
--checkPaso [] [(1,(Var 1,Isup,S.fromList [Var 1],[(1,0)]))] (Var 1 `Oimp` (Var 1),Iimp 1 1,S.fromList [],[(1,1)])
--
--
--
checkPrueba :: [PL]->[NumPaso] -> Bool
-- True sii todos los pasos de lpasos son pasos válidos mediante alguna regla de deduccion natural.
checkPrueba lprem lpasos= -- listaDePremisas listaDePasos 
    case lpasos of
         []     -> True -- la lista de pasos vacia es valida
         _:_    -> checkPrueba lprem lpp && checkPaso lprem lpp p
         where
         n  = length lpasos
         lpp= Prelude.take (n-1) lpasos
         p  = last lpasos
--
--Tests:
--checkPrueba [] [(1,(Top,Itop,S.fromList [],[]))]
--checkPrueba [] []
--checkPrueba [] [(1,(Var 1,Isup,S.fromList [Var 1],[]))]
--      False OK
--checkPrueba [] [(1,(Var 1,Isup,S.fromList [Var 1],[(1,0)]))]
--let{v1=Var 1} in checkPrueba [] [(1,(v1,Isup,S.fromList [v1],[(1,0)])), (2,(v1 `Oimp` v1,Iimp 1 1,S.fromList [],[(1,1)]))]
--let{v1=Var 1; lpasos=[(1,(v1,Isup,S.fromList [v1],[(1,0)]))]} in checkPrueba [] lpasos
--checkPrueba [] [(1,(Var 2,Isup,S.fromList [Var 2])), (2,(Var 1 `Oimp` (Var 2),Iimp 1 1,S.fromList [Var 2])), (3,(Var 2 `Oimp`(Var 1 `Oimp` (Var 2)),Iimp 1 2,S.fromList []))]
--
--
---------------------------------------------------------------------------------------------------------------
--
showRegla :: ReglaDN->String
showRegla r= case r of
            -- reglas para la conjuncion:
            Icon  i j   -> "iCon "++show i++","++show j
            Econ1 i     -> "eCon1 "++show i
            Econ2 i     -> "eCon2 "++show i
            -- reglas para la implicacion:
            Iimp  i j   -> "iImp "++show i++"-"++show j
            Eimp i j    -> "eImp "++show i++","++show j
            -- reglas para la negacion:
            Ineg  i j   -> "iNeg "++show i++"-"++show j
            Eneg i j    -> "eNeg "++show i++","++show j
            -- reglas para la disyuncion:
            Idis1 i     -> "iDis1 "++show i
            Idis2 i     -> "iDis2 "++show i
            Edis i j k  -> "eDis "++show i++","++show j++","++show k
            -- regla para bottom (no hay introduccion de bottom):
            Ebot  i     -> "eBot "++show i
            -- regla para suposiciones (Assumptions):
            Isup        ->  "suposicion"
            -- regla para premisas (Premises):
            Prem        ->  "premisa"
            -- regla para eliminacion de la doble negacion:
            E2neg i     ->  "E¬¬ "++show i
            -- regla para top (no hay eliminacion de top). Esta regla no se usa:
            Itop        ->  "iTop"
            -- La siguiente regla permite repetir una formula previa. (***):
            Copy i      ->  "copy "++show i
--             _           ->  show r
            --
--
showLphi :: [PL] -> String
--Muestra una lista de formulas.
showLphi lphi= case lphi of
                    [f]     -> showPL f
                    f:lf    -> showPL f ++","++ showLphi lf
                    []      -> ""
--     
showCaja :: Caja -> String
showCaja (k,l) = showN k++"-"++ showN l
    where
    showN n= if n==0
                then "?"
                else show n
--
--
showLcajas :: [Caja] -> String
--Muestra una lista de cajas.
showLcajas lcajas= case lcajas of
                    [(i,j)] -> showCaja (i,j)
                    c:lc    -> showCaja c ++","++ showLcajas lc
                    []      -> ""
--
--                    
showNumPasoCheck :: Int->NumPaso->Bool -> String
-- Muestra un paso indicando, mediante b, si es correcto, o no.
showNumPasoCheck fSize (n,(f,r,lc)) b = "\t" ++ (show n) ++". "++ fS++ spaceAfterPhi++ rS ++ lcS  ++ checkS
    where
    fS              = showPL f
    spaceAfterPhi   = " " ++ Prelude.take (fSize-(length fS)) (repeat ' ')
    rS              = "\t " ++ (showRegla r)
    lcS             = ". Cajas=["++ showLcajas lc ++"]"
    checkS          = if b 
                        then ". Correcto" 
                        else ". Incorrecto"
--
showLpasos :: Int->[PL]->[NumPaso]->[NumPaso] -> IO ()
-- Muestra los pasos de lpasos indicando si son correctos, o no.
-- Initial call: showLpasos fSize lprem [] lpasos
showLpasos fSize lprem prevLp lpasos = 
    case lpasos of
            []      -> putStr ""
            p:lps   ->  do
                        putStrLn $ showNumPasoCheck fSize p (checkPaso lprem prevLp p)
                        showLpasos fSize lprem (prevLp++[p]) lps
--
--Test:
--let {v1=Var 1; v2=Var 2; proof=[(1,(v2,Isup,S.fromList [v2],[(1,0)]))]} in showLpasos 30 [] [] proof
--let {v1=Var 1; v2=Var 2; proof=[(1,(v2,Isup,S.fromList [v2],[(1,0)])), (2,(v1 `Oimp` v2,Iimp 1 1,S.fromList [v2],[(1,1)]))]} in showLpasos 30 [] [] proof
--let {v1=Var 1; proof=[(1,(v1,Isup,S.fromList [v1],[(1,0)])), (2,(v1 `Oimp` v1,Iimp 1 1,S.fromList [],[(1,1)]))]} in showLpasos 30 [] [] proof
--
--let {v1=Var 1; proof=[(2,(v1 `Oimp` v1,Iimp 1 1,S.fromList [],[(1,1)]))]} in showLpasos 30 [] [(1,(v1,Isup,S.fromList [v1],[(1,0)]))] proof
--let{v1=Var 1; p=(2,(v1 `Oimp` v1,Iimp 1 1,S.fromList [],[(1,1)]))} in (checkPaso [] [(1,(v1,Isup,S.fromList [v1],[(1,0)]))] p)
--      True OK
--let {v1=Var 1; proof=[(1,(v1,Isup,S.fromList [v1],[(1,0)])), (2,(v1 `Oimp` v1,Iimp 1 1,S.fromList [],[(1,1)]))]} in showLpasos 30 [] [] proof
--
--let{lpasos= [ (1,(Var 2,                              Isup,S.fromList     [Var 2], [(1,0)])), (2,(Var 1,                              Isup,S.fromList     [Var 2,Var 1], [(1,0),(2,0)])), (3,(Var 2,                              Copy 1,S.fromList   [Var 2,Var 1], [(1,0),(2,0)])), (4,(Var 1 `Oimp` (Var 2),               Iimp 2 3,S.fromList [Var 2], [(1,0),(2,3)]))]; p=(5,(Var 2 `Oimp`(Var 1 `Oimp` (Var 2)), Iimp 1 4,S.fromList [],      [(1,4),(2,3)]))} in checkPaso [] lpasos p
--
--
showCheckConclusion :: [PL]->[NumPaso]->PL -> IO ()
showCheckConclusion lpremisas lpasos phi =   
    do
    putStrLn mensaje
    putStrLn ""
    where 
    mensaje 
        | not pruebaOK  = "\t*** Hay pasos incorrectos. ***"
        | lcAbiertas/=[]= "\t*** Hay cajas de suposiciones que no se cerraron ***: "++ showLcajas lcAbiertas
        | phi/=fN       = "\t*** La ultima fórmula no es el objetivo ***: "++ (showPL phi) ++" /= "++ (showPL fN)
        | otherwise     = "\tCorrecto. Mediante deduccion natural: "++ lpremS ++ " |- " ++ showPL fN
    pruebaOK            = checkPrueba lpremisas lpasos
    (_,(fN,_,lc))       = ultimoPaso lpasos
    lpremS              = if lpremisas /= []
                             then "{" ++ showLphi lpremisas ++"}"
                             else ""
    lcAbiertas          = [(i,j) | (i,j)<-lc, j==0]
--
maxL :: Ord a => [a] -> a
maxL = foldr1 (\x y ->if x >= y then x else y)
--
showCheckDedNat :: [PL]->[NumPaso]->PL -> IO ()
--Muestra y verifica que lpasos sea una deduccion natural correcta de: lpremisas |- phi.
--Es decir, muestra y verifica que lpasos es una prueba, con deduccion natural, de phi a partir de lpremisas.
showCheckDedNat lpremisas lpasos phi = --listaDePremisas listaDePasos
    do
    showLpasos fSize lpremisas [] lpasos
    showCheckConclusion lpremisas lpasos phi 
    where
    --fSize= 50
    fSize= maxL [length (showPL f) | (_,(f,_,_)) <- lpasos] 
--
--Test:
--let {phi=Var 2 `Oimp`(Var 1 `Oimp` (Var 2)); proof=[(1,(Var 2,Isup,S.fromList [Var 2],[])), (2,(Var 1 `Oimp` (Var 2),Iimp 1 1,S.fromList [Var 2],[])), (3,(Var 2 `Oimp`(Var 1 `Oimp` (Var 2)),Iimp 1 2,S.fromList [],[]))]} in showCheckDedNat [] proof phi
--
--
--
--Ejercicios: -----------------------------------------------------------------------------
-- 1. Agregar a checkPaso implementación de: 
--      a) Idis1    A |- A v B
--      b) Idis2    B |- A v B
--      c) Edis     AvB,A->C,B->C |- C
--      d) E2neg    ¬¬A |- A
--
-- 2. Implementar el ejemplo p.12 de Thompson:
-- thompsonP12c2 :: IO ()
-- thompsonP12c2 = -- |- --((v1 ⇒ v3) ∧ (v2 ⇒ v3)) ⇒ ((v1 ∨ v2) ⇒ v3)
--
-- 3. Resolver los ejercicios de Thompson:
-- Exercises
-- 1.1. Give a proof of the transitivity of implication, by showing that we can
-- derive A ⇒ C from the assumptions A ⇒ B and B ⇒ C.
-- 1.2. Give a proof of ((A ∨ B) ⇒ C) ⇒ ((A ⇒ C) ∧ (B ⇒ C)).
-- 1.3. Give a proof of (A ⇒ (B ⇒ C)) ⇒ ((A ∧ B) ⇒ C).
-- 1.4. Give proofs of (A ⇒ B) ⇒ (B ⇒ A) and A ⇒ ¬¬A.
-- 1.5. From the assumption (B ∨ C) prove ¬(¬A ∧ ¬B).
-- 1.6. Give derivations of the rules (¬I) and (¬E) given above. In other words
--         • Show that from proofs of B and ¬B from the assumption A among
--         others, we can find a proof of ¬A without the assumption A.
--         • Show that from proofs of A and ¬A we can find a proof of any proposition B.
-- 1.7. Show that the three characterisations of classical logic (as an extension
-- of the intuitionistic system above) are equivalent.
-- 1.8. Using one of the classical systems (using E2neg), give a derivation of the formula
-- ((A ⇒ B) ⇒ A) ⇒ A, which is known as Pierce’s Law.
--
