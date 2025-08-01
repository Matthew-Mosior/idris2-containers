||| Linear RRB Vector Internals
module Data.RRBVector1.Internal

import Data.Array.Core
import Data.Array.Indexed
import Data.Array.Mutable
import Data.Bits
import Data.List
import Data.Linear.Ref1
import Data.Linear.Token
import Data.Nat
import Data.String
import Derive.Prelude

%default total
%hide Data.Vect.Quantifiers.All.get
%language ElabReflection

--------------------------------------------------------------------------------
--          Internal Utility
--------------------------------------------------------------------------------

||| Convenience interface for bitSize that doesn't use an implicit parameter.
private
bitSizeOf :  (ty : Type)
          -> FiniteBits ty
          => Nat
bitSizeOf ty = bitSize {a = ty}

--------------------------------------------------------------------------------
--          Internals
--------------------------------------------------------------------------------

public export
Shift : Type
Shift = Nat

||| The number of bits used per level.
export
blockshift : Shift
blockshift = 4

||| The maximum size of a block.
export
blocksize : Nat
blocksize = integerToNat $ 1 `shiftL` blockshift

||| The mask used to extract the index into the array.
export
blockmask : Nat
blockmask = minus blocksize 1

export
up :  Shift
   -> Shift
up sh = plus sh blockshift

export
down :  Shift
     -> Shift
down sh = minus sh blockshift

export
radixIndex :  Nat
           -> Shift
           -> Nat
radixIndex i sh = integerToNat ((natToInteger i) `shiftR` sh .&. (natToInteger blockmask))

export
relaxedRadixIndex :  {n : Nat}
                  -> IArray n Nat
                  -> Nat
                  -> Shift
                  -> (Nat, Nat)
relaxedRadixIndex sizes i sh =
  let guess  = radixIndex i sh -- guess <= idx
      idx    = loop sizes guess
      subIdx = case idx == 0 of
                 True  =>
                   i
                 False =>
                   let idx' = case tryNatToFin $ minus idx 1 of
                                Nothing    =>
                                  assert_total $ idris_crash "Data.RRBVector1.Internal.relaxedRadixIndex: index out of bounds"
                                Just idx'' =>
                                  idx''
                     in minus i (at sizes idx')
    in (idx, subIdx)
  where
    loop :  IArray n Nat
         -> Nat
         -> Nat
    loop sizes idx =
      let current = case tryNatToFin idx of
                      Nothing       =>
                        assert_total $ idris_crash "Data.RRBVector1.Internal.relaxedRadixIndex.loop: index out of bounds"
                      Just idx' =>
                        at sizes idx' -- idx will always be in range for a well-formed tree
        in case i < current of
             True  =>
               idx
             False =>
               assert_total $ loop sizes (plus idx 1)

--------------------------------------------------------------------------------
--          Internal Tree Representation
--------------------------------------------------------------------------------

||| A linear internal tree representation.
public export
data Tree1 : (s : Type) -> Type -> Type where
  Balanced   : {bsize : Nat} -> (bsize ** MArray s bsize (Tree1 s a)) -> Tree1 s a
  Unbalanced : {usize : Nat} -> (usize ** MArray s usize (Tree1 s a)) -> IArray usize Nat -> Tree1 s a
  Leaf       : {lsize : Nat} -> (lsize ** MArray s lsize a) -> Tree1 s a

--------------------------------------------------------------------------------
--          Tree Utilities
--------------------------------------------------------------------------------

export
singleton :  a
          -> F1 s (MArray s 1 a)
singleton x t =
  marray1 1 x t

export
singleton' :  Tree1 s a
           -> F1 s (MArray s 1 (Tree1 s a))
singleton' tree t =
  marray1 1 tree t

export
treeToArray :  Tree1 s a
            -> Either (bsize ** MArray s bsize (Tree1 s a))
                      (usize ** MArray s usize (Tree1 s a))
treeToArray (Balanced   arr)   =
  Left arr
treeToArray (Unbalanced arr _) =
  Right arr
treeToArray (Leaf       _)     =
  assert_total $ idris_crash "Data.RRBVector1.Internal.treeToArray: leaf"

export
treeToArray' :  Tree1 s a
             -> (lsize ** MArray s lsize a)
treeToArray' (Balanced _)     =
  assert_total $ idris_crash "Data.RRBVector1.Internal.treeToArray': balanced"
treeToArray' (Unbalanced _ _) =
  assert_total $ idris_crash "Data.RRBVector1.Internal.treeToArray': unbalanced"
treeToArray' (Leaf arr)       =
  arr

export
treeBalanced :  Tree1 s a
             -> Bool
treeBalanced (Balanced   _)   =
  True
treeBalanced (Unbalanced _ _) =
  False
treeBalanced (Leaf       _ )  =
  True

||| Computes the size of a tree with shift.
export
treeSize :  Shift
         -> Tree1 s a
         -> F1 s Nat
treeSize t =
  go 0 t
  where
    go :  Shift
       -> Shift
       -> Tree1 s a
       -> F1 s Nat
    go acc _  (Leaf       (l ** arr))       t =
      plus acc l # t
    go acc _  (Unbalanced (u ** arr) sizes) t =
      let i := tryNatToFin $ minus u 1
        in case i of
             Nothing =>
               (assert_total $ idris_crash "Data.RRBVector1.Internal.treeSize: index out of bounds") # t
             Just i' =>
               (plus acc (at sizes i')) # t
    go acc sh (Balanced  (b ** arr))        t =
      let i := minus b 1
        in case tryNatToFin i of
             Nothing =>
               (assert_total $ idris_crash "Data.RRBVector1.Internal.treeSize: index out of bounds") # t
             Just i' =>
               let i'' # t := get arr i' t
                 in go (plus acc (mult i (integerToNat (1 `shiftL` sh))))
                       (down sh)
                       (assert_smaller arr i'')
                       t

||| Turns an array into a tree node by computing the sizes of its subtrees.
||| sh is the shift of the resulting tree.
export
computeSizes :  {n : Nat}
             -> Shift
             -> MArray s n (Tree1 s a)
             -> F1 s (Tree1 s a)
computeSizes sh arr t =
  let isbalanced # t := isBalanced arr t
    in case isbalanced of
         True  =>
           (Balanced {bsize=n} (n ** arr)) # t
         False =>
           let arrnat # t := createArrNat arr t
             in (Unbalanced {usize=n} (n ** arr) arrnat) # t
  where
    createArrNat :  MArray s n (Tree1 s a)
                 -> F1 s (IArray n Nat)
    createArrNat arr t =
      let tant # t := unsafeMArray1 n t
        in go 0 n 0 tant t
      where
        go :  (m, x, acc : Nat)
           -> (an : MArray s n Nat)
           -> {auto v : Ix x n}
           -> F1 s (IArray n Nat)
        go m Z     acc an t =
          freeze an t
        go m (S j) acc an t =
          let j'       # t := getIx arr j t
              treesize # t := treeSize (down sh) j' t
              acc'         := plus acc treesize
            in case tryNatToFin m of
                 Nothing =>
                   (assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.createArrNat.go: can't convert Nat to Fin") # t
                 Just m' =>
                   let () # t := set an m' acc' t
                     in go (S m) j acc' an t
    maxsize : Integer
    maxsize = 1 `shiftL` sh -- the maximum size of a subtree
    lenM1 : Nat
    lenM1 = minus n 1
    isBalanced :  {n : Nat}
               -> MArray s n (Tree1 s a)
               -> F1 s Bool
    isBalanced arr t =
      let bool' # t := go arr 0 t
        in bool' # t
      where
        go :  {n : Nat}
           -> MArray s n (Tree1 s a)
           -> Nat
           -> F1 s Bool
        go arr i t =
          case tryNatToFin i of
            Nothing =>
              (assert_total $ idris_crash "Data.RRBVector.Internal.computeSizes.isBalanced: can't convert Nat to Fin") # t
            Just i' =>
              let subtree # t := get arr i' t
                in case i < lenM1 of
                     True  =>
                       let go'      # t := assert_total $ go arr (plus i 1) t
                           treesize # t := treeSize (down sh) subtree t
                         in ((natToInteger treesize == maxsize) && go') # t
                     False =>
                       treeBalanced subtree # t

export
countTrailingZeros :  Nat
                   -> Nat
countTrailingZeros x =
  go 0
  where
    w : Nat
    w = bitSizeOf Int
    go : Nat -> Nat
    go i =
      case i >= w of
        True  =>
          i
        False =>
          case tryNatToFin i of
            Nothing =>
              assert_total $ idris_crash "Data.RRBVector1.Internal.countTrailingZeros: can't convert Nat to Fin"
            Just i' =>
              case testBit (the Int (cast x)) i' of
                True  =>
                  i
                False =>
                  assert_total $ go (plus i 1)

||| Nat log base 2.
export
log2 :  Nat
     -> Nat
log2 x =
  let bitSizeMinus1 = minus (bitSizeOf Int) 1
    in minus bitSizeMinus1 (countLeadingZeros x)
  where
    countLeadingZeros : Nat -> Nat
    countLeadingZeros x =
      minus (minus w 1) (go (minus w 1))
      where
        w : Nat
        w = bitSizeOf Int
        go : Nat -> Nat
        go i =
          case i < 0 of
            True  =>
              i
            False =>
              case tryNatToFin i of
                Nothing =>
                  assert_total $ idris_crash "Data.RRBVector1.Internal.log2: can't convert Nat to Fin"
                Just i' =>
                  case testBit (the Int (cast x)) i' of
                    True  =>
                      i
                    False =>
                      assert_total $ go (minus i 1)

--------------------------------------------------------------------------------
--          Linear RRB Vectors
--------------------------------------------------------------------------------

||| A linear relaxed radix balanced vector (RRB-Vector).
||| It supports fast indexing, iteration, concatenation and splitting.
public export
data RRBVector1 : (s : Type) -> Type -> Type where
  Root :  Nat   -- size
       -> Shift -- shift (blockshift * height)
       -> Tree1 s a
       -> RRBVector1 s a
  Empty : RRBVector1 s a
