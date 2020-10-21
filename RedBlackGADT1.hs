{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}

{-# OPTIONS_GHC -Wincomplete-patterns #-}

module RedBlackGADT1 where


-- RedBlack trees that use GADTs to enforce
--    that the Root of the Tree is Black

import qualified Data.Foldable as Foldable
import Data.Kind (Type)
import Test.QuickCheck hiding (elements)

data Color where
  Red :: Color
  Black :: Color

data SColor (c::Color) where
  R :: SColor Red
  B :: SColor Black

data T (c::Color) (a :: Type) where
  E :: T Black a
  N :: Valid c c1 c2 => SColor c -> T c1 a -> a -> T c2 a -> T c a

class Valid (c::Color) (c1 :: Color) (c2 :: Color)
instance Valid Red Black Black
instance Valid Black c1 c2

newtype RBT a = Root (T Black a)

-- Show instances

instance Show Color where
  show Red = "R"
  show Black = "B"

instance Show (SColor c) where
  show R = "R"
  show B = "B"  

instance Show a => Show (T c a) where
  showsPrec _d E = showString "E"
  showsPrec d (N c l x r) =
    showParen (d > node_prec) $
      showString "N " . showsPrec d c
        . showString " "
        . showsPrec (node_prec + 1) l
        . showString " "
        . showsPrec (d + 1) x
        . showString " "
        . showsPrec (node_prec + 1) r
    where
      node_prec = 5

instance Show a => Show (RBT a) where
  show (Root x) = show x

-- Eq instances
instance Eq Color where
  Red == Red = True
  Black == Black = True
  _ == _ = False

(%==) :: SColor c1 -> SColor c2 -> Bool
R %== R = True
B %== B = True
_ %== _ = False


-- Foldable instance
instance Foldable (T c) where
  foldMap _f E = mempty
  foldMap f (N _ l x r) = foldMap f l <> f x <> foldMap f r

instance Foldable RBT where
  foldMap f (Root x) = foldMap f x

-- | List all of the elements of the finite set, in ascending order
elements :: RBT a -> [a]
elements = Foldable.toList

instance Eq a => Eq (RBT a) where
  t1 == t2 = elements t1 == elements t2

-- | access the color of the tree
color :: T c a -> SColor c
color (N c _ _ _) = c
color E = B

-- | calculate the black height of the tree
blackHeight :: T c a -> Int
blackHeight E = 1
blackHeight (N c a _ _) = blackHeight a + (if c %== B then 1 else 0)

good1 :: RBT Int
good1 = Root $ N B (N B E 1 E) 2 (N B E 3 E)

-- Red root
-- bad1 :: RBT Int
-- bad1 = Root $ N R (N B E 1 E) 2 (N B E 3 E)

-- invalid black height
bad2 :: RBT Int
bad2 = Root $ N B (N R E 1 E) 2 (N B E 3 E)

-- bad3  :: RBT Int
-- bad3  = Root (N B (N R (N R E 1 E) 2 (N R E 3 E)) 4 E)

bad4 :: RBT Int
bad4 = Root $ N B (N B E 1 E) 3 (N B E 2 E)

trees :: [(String, RBT Int)]
trees =
  [ ("good1", good1),
    ("bad4", bad4),
    ("empty", empty)
  ]

-- | A red-black tree is a BST if an inorder traversal is strictly ordered.
isBST :: Ord a => RBT a -> Bool
isBST = orderedBy (<) . elements

-- | Are the elements in the list ordered by the provided operation?
orderedBy :: (a -> a -> Bool) -> [a] -> Bool
orderedBy op (x : y : xs) = x `op` y && orderedBy op (y : xs)
orderedBy _ _ = True

isRootBlack :: RBT a -> Bool
isRootBlack (Root t) = color t %== B

consistentBlackHeight :: RBT a -> Bool
consistentBlackHeight (Root t) = aux t
  where
    aux :: T c a -> Bool
    aux (N _ a _ b) = blackHeight a == blackHeight b && aux a && aux b
    aux E = True

noRedRed :: RBT a -> Bool
noRedRed (Root t) = aux t
  where
    aux :: T c a -> Bool
    aux (N R a _ b) = color a %== B && color b %== B && aux a && aux b
    aux (N B a _ b) = aux a && aux b
    aux E = True

valid :: Ord a => RBT a -> Bool
valid t = isRootBlack t && consistentBlackHeight t && noRedRed t && isBST t

testProps :: IO ()
testProps = mapM_ checkTree trees
  where
    checkTree (name, tree) = do
      putStrLn $ "******* Checking " ++ name ++ " *******"
      quickCheck $ once (counterexample "RB2" $ isRootBlack tree)
      quickCheck $ once (counterexample "RB3" $ consistentBlackHeight tree)
      quickCheck $ once (counterexample "RB4" $ noRedRed tree)
      quickCheck $ once (counterexample "BST" $ isBST tree)

type A = Small Int

prop_Valid :: RBT A -> Property
prop_Valid tree =
  counterexample "RB2" (isRootBlack tree)
    .&&. counterexample "RB3" (consistentBlackHeight tree)
    .&&. counterexample "RB4" (noRedRed tree)
    .&&. counterexample "BST" (isBST tree)

instance (Ord a, Arbitrary a) => Arbitrary (RBT a) where
  arbitrary :: Gen (RBT a)
  arbitrary = foldr insert empty <$> (arbitrary :: Gen [a])

  shrink :: RBT a -> [RBT a]
  shrink (Root E) = []
  shrink (Root (N _ l _ r)) = [blacken l, blacken r]

blacken :: T c a -> RBT a
blacken E = Root E
blacken (N _ l v r) = Root (N B l v r)

blackenH :: HT a -> RBT a
blackenH (HN _ l v r) = Root (N B l v r)

empty :: RBT a
empty = Root E

member :: Ord a => a -> RBT a -> Bool
member x0 (Root t) = aux x0 t
  where
    aux :: Ord a => a -> T c a -> Bool
    aux x E = False
    aux x (N _ a y b)
      | x < y = aux x a
      | x > y = aux x b
      | otherwise = True

insert :: Ord a => a -> RBT a -> RBT a
insert x (Root t) = blackenH (ins x t)

-- Hide the tree color
-- Know insert won't give us an empty tree
data HT a where
  HN :: SColor c1 -> T c2 a -> a -> T c3 a -> HT a

ins :: Ord a => a -> T c a -> HT a
ins x E = HN R E x E
ins x s@(N c a y b)
  | x < y = balanceL c (ins x a) y b
  | x > y = balanceR c a y (ins x b)
  | otherwise = HN c a y b

-- Original version of balance
{-
balance :: Color -> T a -> a -> T a -> T a
balance (N B (N R (N R a x b) y c) z d) = N R (N B a x b) y (N B c z d)
balance (N B (N R a x (N R b y c)) z d) = N R (N B a x b) y (N B c z d)

balance (N B a x (N R (N R b y c) z d)) = N R (N B a x b) y (N B c z d)
balance (N B a x (N R b y (N R c z d))) = N R (N B a x b) y (N B c z d)
balance t = t
-}

balanceL :: SColor c -> HT a -> a -> T c2 a -> HT a
balanceL B (HN R (N R a x b) y c) z d = HN R (N B a x b) y (N B c z d)
balanceL B (HN R a x (N R b y c)) z d = HN R (N B a x b) y (N B c z d)
balanceL c (HN B a x b) z d = HN c (N B a x b) z d
balanceL c (HN R a@E x b@E) z d = HN c (N R a x b) z d
balanceL c (HN R a@(N B _ _ _) x b@(N B _ _ _)) z d =
  HN c (N R a x b) z d
balanceL c (HN R a x b) z d = error ("no case for " ++ show (color a) ++ " " ++ show (color b))

-- balanceL col a@(HN ac aa ax ab) x b = HN col (N ac aa ax ab) x b

balanceR :: SColor c -> T c1 a -> a -> HT a -> HT a
balanceR B a x (HN R (N R b y c) z d) = HN R (N B a x b) y (N B c z d)
balanceR B a x (HN R b y (N R c z d)) = HN R (N B a x b) y (N B c z d)
balanceR c a x (HN B b y d) = HN c a x (N B b y d)
balanceR c a x (HN R b@E y d@E) = HN c a x (N R b y d)
balanceR c a x (HN R b@(N B _ _ _) y d@(N B _ _ _)) =
  HN c a x (N R b y d)
balanceR c a x (HN R b y d) = error ("no case for " ++ show (color b) ++ " " ++ show (color d))
--balanceR col a x b@(HN bc ba bx bb) = HN col a x (N bc ba bx bb)

prop_ShrinkValid :: RBT A -> Property
prop_ShrinkValid t = conjoin (map prop_Valid (shrink t))

prop_InsertEmpty :: A -> Bool
prop_InsertEmpty x = elements (insert x empty) == [x]

prop_InsertInsert :: A -> A -> RBT A -> Bool
prop_InsertInsert x y t =
  insert x (insert y t) == insert y (insert x t)

prop_MemberEmpty :: A -> Bool
prop_MemberEmpty x = not (member x empty)

prop_MemberInsert :: A -> A -> RBT A -> Bool
prop_MemberInsert k k0 t =
  member k (insert k0 t) == (k == k0 || member k t)

return []

runTests :: IO Bool
runTests = $quickCheckAll
