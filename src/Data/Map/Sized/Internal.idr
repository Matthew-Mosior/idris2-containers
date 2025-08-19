||| Map Internals
module Data.Map.Sized.Internal

import public Data.Map.Sized.Internal.Tree

import Data.List
import Data.String
import Derive.Prelude

%default total
%language ElabReflection

--------------------------------------------------------------------------------
--          Map
--------------------------------------------------------------------------------

||| A finite map of size n from keys k to values v.
public export
data Map : (n : Nat) -> (k : Type) -> (v : Type) -> Type where
  MkMap :  Tree k v
        -> Map n k v

%runElab derive "Map" [Eq,Ord,Show]

--------------------------------------------------------------------------------
--          Getter
--------------------------------------------------------------------------------

||| Extract the underlying tree from a map.
export
getTree :  Map n k v
        -> Tree k v
getTree (MkMap t) =
  t
