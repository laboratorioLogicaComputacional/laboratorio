import Data.List
-- Funcion que nos da la potencia del primer termino respecto al segundo, pero con diferentes casos para números pares e impares.

pote2 :: Int -> Int -> Int
pote2 n 0 = 1
pote2 n 1 = n
pote2 n k = if(mod k 2 == 0) then pote2 (n * n)(div k 2) else n * (pote2 n (k-1))

-- Función que nos da los primeros n elementos de una lista
toma :: [a] -> Int -> [a]
toma [] _ = []
toma _ 0 = []
toma (x:xs) n = [x] ++ toma xs (n-1)

-- Función que nos da los elementos mayores a n
mayores :: Ord a => [a] -> a -> [a]
mayores a n = [x | x <- a, x > n]
