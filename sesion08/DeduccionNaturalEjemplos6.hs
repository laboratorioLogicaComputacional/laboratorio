module DeduccionNaturalEjemplos6 
--Muestra ejemplos de la verificacion de deducciones naturales mediante showCheckDedNat.
--mcb
where
--import Data.List as L (delete,(\\)) -- (nub,union)
--import Data.Set as S
import SintaxisPL
import DeduccionNatural6 (ReglaDN(..),showCheckDedNat)  
--
--
---------------------------------------------------------------------------------------------------------------
--
-- Ejemplos: --------------------------------------------------------------------------------------------------
--
todosLosEjemplos :: IO ()
-- muestra todos los ejemplos.
todosLosEjemplos =
    do
    putStrLn ""
    putStrLn "Ejemplo thompsonP10:"
    thompsonP10
    --
    putStrLn "Ejemplo thompsonP12a:"
    thompsonP12a
    --
    putStrLn "Ejemplo thompsonP12b:"
    thompsonP12b
    --
    putStrLn "Ejemplo thompsonP12c1:"
    thompsonP12c1
    --
    putStrLn "Ejemplo huthRyanP20:"
    huthRyanP20
    --
    putStrLn "Ejemplo huthRyanP8Ej6:"
    huthRyanP8Ej6
    --
    putStrLn "Ejemplo thompsonP10:"
    thompsonP10
    --
--
thompsonP10 :: IO ()
thompsonP10 = -- |- ((v1&v2)&v3) -> (v1&(v2&v3))
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gamma= []
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos= [   (1,((v1∧v2)∧v3,             Isup,       [(1,0)])), 
                (2,((v1∧v2),                    Econ1 1,    [(1,0)])), 
                (3,(v1,                         Econ1 2,    [(1,0)])), 
                (4,(v2,                         Econ2 2,    [(1,0)])), 
                (5,(v3,                         Econ2 1,    [(1,0)])), 
                (6,(v2∧v3,                      Icon 4 5,   [(1,0)])), 
                (7,(v1∧(v2∧v3),                 Icon 3 6,   [(1,0)])), 
                (8,(((v1∧v2)∧v3)⇒(v1∧(v2∧v3)),  Iimp 1 7,   [(1,7)]))
                ]
        phi= ((v1∧v2)∧v3)⇒(v1∧(v2∧v3))
    in showCheckDedNat gamma lpasos phi 
--
thompsonP12a :: IO ()
thompsonP12a = -- |- ((v1 ∧ v2) ⇒ v3) ⇒ (v1 ⇒ (v2 ⇒ v3))
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        gamma= []
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos= [   (1,((v1∧v2)⇒v3,                 Isup,       [(1,0)])), 
                    (2,(v1,                         Isup,       [(1,0),(2,0)])), 
                    (3,(v2,                         Isup,       [(1,0),(2,0),(3,0)])), 
                    (4,(v1∧v2,                      Icon 2 3,   [(1,0),(2,0),(3,0)])), 
                    (5,((v1∧v2)⇒v3,                 Copy 1,     [(1,0),(2,0),(3,0)])), 
                    (6,(v3,                         Eimp 4 5,   [(1,0),(2,0),(3,0)])), 
                    (7,(v2 ⇒ v3,                    Iimp 3 6,   [(1,0),(2,0),(3,6)])), 
                    (8,(v1 ⇒(v2 ⇒ v3),              Iimp 2 7,   [(1,0),(2,7),(3,6)])),
                    (9,(((v1∧v2)⇒v3)⇒(v1⇒(v2⇒v3)),  Iimp 1 8,   [(1,8),(2,7),(3,6)])) 
                    ]
        phi= ((v1∧v2)⇒v3)⇒(v1⇒(v2⇒v3))
    in showCheckDedNat gamma lpasos phi
--
thompsonP12b :: IO ()
--  1. v1 Sup; 2. v1->v1 iImp 1-1. 
-- Huth-Ryan p.13:
-- The rule →i (with conclusion φ → ψ) does not prohibit the possibility that φ and ψ coincide. 
-- They could both be instantiated to p.
thompsonP12b  = -- |- v1->v1
    let 
        gamma   = []
        v1      = Var 1
        (⇒) :: PL->PL->PL
        f⇒g     = Oimp f g
        lpasos  = [ (1,(v1,     Isup,       [(1,0)])), 
                    (2,(v1⇒v1,  Iimp 1 1,   [(1,1)]))
                    ]
        phi     = v1⇒v1
    in showCheckDedNat gamma lpasos phi
--
thompsonP12c1 :: IO ()
-- 1. v2 Sup; 2. v1->v2 iImp 1-1; 3. v2->(v1->v2)
thompsonP12c1 = -- |- v2->(v1->v2) Incorrecta
    let v1= Var 1
        v2= Var 2
        gamma= []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,(v2,             Isup,       [(1,0)])),  
                    (2,(v1⇒v2,          Iimp 1 1,   [(1,0)])), 
                    (3,(v2⇒(v1⇒v2),     Iimp 1 2,   [(1,1)])) 
                    ] 
        phi = v2⇒(v1⇒v2)
    in showCheckDedNat gamma lpasos phi 
--                
huthRyanP20 :: IO ()
huthRyanP20 = --  |- v2->(v1->v2) Correcta 
    let v1= Var 1
        v2= Var 2
        gamma= []
        (⇒) :: PL->PL->PL
        f⇒g= Oimp f g
        lpasos = [  (1,(v2,             Isup,       [(1,0)])), 
                    (2,(v1,             Isup,       [(1,0),(2,0)])), 
                    (3,(v2,             Copy 1,     [(1,0),(2,0)])), 
                    (4,(v1⇒v2,          Iimp 2 3,   [(1,0),(2,3)])), 
                    (5,(v2⇒(v1⇒v2),     Iimp 1 4,   [(1,4),(2,3)]))
                    ]
        phi = v2⇒(v1⇒v2)
    in showCheckDedNat gamma lpasos phi
--
--
huthRyanP8Ej6 :: IO ()
huthRyanP8Ej6 = -- {(v1 ∧ v2) ∧ v3, v4 ∧ v5} |− v2 ∧ v4
    let v1= Var 1
        v2= Var 2
        v3= Var 3
        v4= Var 4
        v5= Var 5
        gamma= [(v1∧v2)∧v3, v4∧v5]
        (∧) :: PL->PL->PL
        f∧g= Oand f g
        lpasos = [  (1,((v1∧v2)∧v3,     Prem,       [])), 
                    (2,(v4∧v5,          Prem,       [])), 
                    (3,(v1∧v2,          Econ1 1,    [])), 
                    (4,(v2,             Econ2 3,    [])),
                    (5,(v4,             Econ1 2,    [])), 
                    (6,(v2∧v4,          Icon 4 5,   []))
                    ]
        phi = v2∧v4
    in showCheckDedNat gamma lpasos phi 
--

thompsonP12c2 :: IO ()
thompsonP12c2 = --  |− ((v1 ⇒ v3) ∧ (v2 ⇒ v3)) ⇒ ((v1 ∨ v2) ⇒ v3)
  let v1 = Var 1
      v2 = Var 2
      v3 = Var 3
      gamma = []
      (∧) :: PL->PL->PL
      f∧g = Oand f g
      (⇒) :: PL->PL->PL
      f⇒g = Oimp f g 
      (∨) :: PL->PL->PL
      f∨g = Oor f g
      {-
      lpasos = [ (1, ((v1⇒v3)∧(v2⇒v3), Isup, [(1,0)])),
                 (2, (v1, Isup, [(1,0), (2,0)])),
                 (3, ( v1⇒v3,  Econ1 1, [(1,0), (2,0)])),
                 (4, (v3, Eimp 2 3, [(1,0), (2,0)])),
                 (5, (v1∨v2, Idis1 2, [(1,0), (2,0)])),
                 (6, ((v1∨v2)⇒v3,Iimp 5 4 ,[(1,0),(2,5)])),
                 (7, (v2, Isup, [(1,0),(7,0)])),
                 (8, (v2⇒v3,  Econ2 1, [(1,0),(7,0)])),
                 (9, (v3, Eimp 7 8, [(1,0),(7,0)])),
                 (10, (v1∨v2, Idis2 7, [(1,0),(7,0)])),
                 (11, ((v1∨v2)⇒v3, Iimp 10 9, [(1,0),(7,10)])),
                 (12, ((v1∨v2)⇒v3, Copy 1, [(1,0)])),
                 (13, (((((v1⇒v3)∧(v2⇒v3)))⇒((v1∨v2)⇒v3)), Iimp 1 12, [(1,12)])) ] -}
      lpasos = [ (1, ( (v1⇒v3)∧(v2⇒v3),  Isup, [(1,0)])),
                 (2, ( v1∨v2,              Isup, [(1,0),(2,0)])),
                 (3, ( v1,                  Isup, [(1,0),(2,0),(3,0)])),
                 (4, ( v2,                  Isup, [(1,0),(2,0),(3,0),(4,0)])),
                 (5, ( v2⇒v3,              Econ2 1, [(1,0),(2,0),(3,0),(4,0)])),
                 (6, ( v3,                  Eimp 4 5, [(1,0),(2,0),(3,0),(4,0)])),
                 (7, ( v1⇒v3,              Econ1 1, [(1,0),(2,0),(3,0),(4,6)])),
                 (8, ( v3,                  Eimp 3 7, [(1,0),(2,0),(3,0),(4,6)]))] 

      phi =  ((((v1⇒v3)∧(v2⇒v3)))⇒((v1∨v2)⇒v3))
       in
      showCheckDedNat gamma lpasos phi
--
--
--Ejercicios: ----------------------------------------------------------
--
-- 0. Agregar ejemplos de deduccion para probar las reglas (ver en Thompson y Huth-Ryan):
--      a) Ineg  introduccion de la negacion
--      b) Eneg  eliminacion de la negacion
--      c) Ebot  eliminacion de bottom
--      d) Itop  introduccion de top
--
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
