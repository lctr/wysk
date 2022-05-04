module Prim where

fn identity :: a -> a | x = x
fn const :: a -> b -> a | x _ = x
fn fst :: (a, b) -> a | (x, _) = x
fn snd :: (a, b) -> b | (_, y) = y


data Bool = False | True with (Show, Eq, Ord)

fn not :: Bool -> Bool
| True = False
| False = True

infixl 2 ||

fn (||) :: Bool -> Bool -> Bool
| True _ = True
| False y = y

infixl 3 &&

fn (&&) :: Bool -> Bool -> Bool
| True y = y
| False _ = False

class Eq a {
   (==) :: a -> a -> Bool;
   (!=) :: a -> a -> Bool
   | x y = not (x == y)
}

impl Eq Bool {
   (==) 
   | True True = True
   | False False = True
   | _ _ = False

   ~~ overwrite default method for efficiency?
   (!=) 
   | True False = True
   | False True = True
   | _ _ = False
}

~~ Note: floating point numbers do NOT implement Eq
impl Eq Int {
   ~~ rust function call
   (==) = prim'IntEq
}

~~ impl |Eq a| Eq [a] {
~~    (==)
~~    | [] [] = True
~~    | (x:xs) (y:ys) = (x == y) && (xs == ys)
~~    | _ _ = False
~~ }

infixl 6 + -
infixl 7 * /

class Add a { (+) :: a -> a -> a }

class Sub a { (-) :: a -> a -> a }

class Mul a { (*) :: a -> a -> a }

type Integer = PrimBigInt

class |Add a, Sub a, Mul a| Num a {
   fromInt :: Int -> a;
   fromInteger :: Integer -> a;
}

impl Add Int { (+) = prim'AddInt }
impl Sub Int { (-) = prim'SubInt }
impl Mul Int { (-) = prim'MulInt }
impl Num Int {
   fromInt = identity;
   fromInteger n = n :: Integer
}
