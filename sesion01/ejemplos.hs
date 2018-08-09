import Data.List

--Función que nos da la potencia del primer termino respecto al segundo
pote :: Int -> Int -> Int
pote x 0 = 1
pote x y = x * (pote x (y-1))

-- Función que nos da el factorial del termino dado
fact :: Integer -> Integer
fact 0 = 1
fact x = x * fact (x-1)

-- Función que nos da el numero de elementos de una lista
tam :: [a] -> Int
tam [] = 0
tam (x:xs) = tam xs + 1

-- Función que nos da los primeros n elementos de una lista
primN :: [a] -> Int -> [a]
primN _ 0 = []
primN (x:xs) n = [x] ++ primN xs (n-1)

-- Función que nos da los elementos mayores a n
mayores :: Ord a => [a] -> a -> [a]
mayores a n =[x | x <- a, x > n] 
