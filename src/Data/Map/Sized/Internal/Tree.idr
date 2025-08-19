||| Finite Trees
module Data.Map.Sized.Internal.Tree

import public Data.Map.Sized.Internal.Tree.Internal

import Data.Bits
import Data.List

%hide Prelude.null
%hide Prelude.toList

%default total

--------------------------------------------------------------------------------
--          Creating Trees
--------------------------------------------------------------------------------

||| The empty tree. O(1)
export
empty : Tree k v
empty = Tip

--------------------------------------------------------------------------------
--          Folds
--------------------------------------------------------------------------------

||| Fold the values in the tree using the given left-associative binary operator. O(n)
export
foldl :  (v -> w -> v)
      -> v
      -> Tree k w
      -> v
foldl f z Tip             =
  z
foldl f z (Bin _ _ x l r) =
  foldl f (f (foldl f z l) x) r

||| Fold the values in the tree using the given right-associative binary operator. O(n)
export
foldr :  (v -> w -> w)
      -> w
      -> Tree k v
      -> w
foldr f z Tip             =
  z
foldr f z (Bin _ _ x l r) =
  foldr f (f x (foldr f z r)) l

||| Fold the keys and values in the tree using the given left-associative binary operator. O(n)
export
foldlWithKey :  (v -> k -> w -> v)
             -> v
             -> Tree k w
             -> v
foldlWithKey f z Tip              =
  z
foldlWithKey f z (Bin _ kx x l r) =
  foldlWithKey f (f (foldlWithKey f z l) kx x) r

||| Fold the keys and values in the tree using the given right-associative binary operator. O(n)
export
foldrWithKey :  (k -> v -> w -> w)
             -> w
             -> Tree k v
             -> w
foldrWithKey f z Tip              =
  z
foldrWithKey f z (Bin _ kx x l r) =
  foldrWithKey f (f kx x (foldrWithKey f z r)) l

--------------------------------------------------------------------------------
--          Insertion
--------------------------------------------------------------------------------

||| Insert a new key and value in the tree.
||| If the key is already present in the map, the associated value is
||| replaced with the supplied value. O(log n)
export
insert :  Eq (Tree k v)
       => Eq v
       => Ord k
       => k
       -> v
       -> Tree k v
       -> Tree k v
insert kx0 vx0 m =
  go kx0 kx0 vx0 m
  where
    go :  k
       -> k
       -> v
       -> Tree k v
       -> Tree k v
    go orig _  x Tip                 =
      singleton orig x
    go orig kx x t@(Bin sz ky y l r) =
      case compare kx ky of
        LT =>
          let l' = go orig kx x l
            in case l' == l of
                 True  =>
                   t
                 False =>
                   balanceL ky y l' r
        GT =>
          let r' = go orig kx x r
            in case r' == r of
                 True  =>
                   t
                 False =>
                   balanceR ky y l r'
        EQ =>
          case (x == y && orig == ky) of
            True  =>
              t
            False =>
              Bin sz orig x l r

private
insertR :  Eq (Tree k v)
        => Eq v
        => Ord k
        => k
        -> v
        -> Tree k v
        -> Tree k v
insertR kx0 =
  go kx0 kx0
  where
    go :  k
       -> k
       -> v
       -> Tree k v
       -> Tree k v
    go orig _  x Tip                =
      singleton orig x
    go orig kx x t@(Bin _ ky y l r) =
      case compare kx ky of
        LT =>
          let l' = go orig kx x l
            in case l' == l of
                 True  =>
                   t
                 False =>
                   balanceL ky y l' r
        GT =>
          let r' = go orig kx x r
            in case r' == r of
                 True  =>
                   t
                 False =>
                   balanceR ky y l r'
        EQ =>
          t

||| Insert with a function, combining new value and old value.
||| insertWith f key value tree
||| will insert the pair (key, value) into tree if key does
||| not exist in the tree. If the key does exist, the function will
||| insert the pair (key, f new_value old_value). O(log n)
export
insertWith :  Ord k
           => (v -> v -> v)
           -> k
           -> v
           -> Tree k v
           -> Tree k v
insertWith =
  go
  where
    go :  (a -> a -> a)
       -> k
       -> a
       -> Tree k a
       -> Tree k a
    go _ kx x Tip               =
      singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          balanceL ky y (go f kx x l) r
        GT =>
          balanceR ky y l (go f kx x r)
        EQ =>
          Bin sy kx (f x y) l r

private
insertWithR :  Ord k
            => (v -> v -> v)
            -> k
            -> v
            -> Tree k v
            -> Tree k v
insertWithR =
  go
  where
    go :  (v -> v -> v)
       -> k
       -> v
       -> Tree k v
       -> Tree k v
    go _ kx x Tip               =
      singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          balanceL ky y (go f kx x l) r
        GT =>
          balanceR ky y l (go f kx x r)
        EQ =>
          Bin sy ky (f y x) l r

private
insertWithKeyR :  Ord k
               => (k -> v -> v -> v)
               -> k
               -> v
               -> Tree k v
               -> Tree k v
insertWithKeyR =
  go
  where
    go :  (k -> v -> v -> v)
       -> k
       -> v
       -> Tree k v
       -> Tree k v
    go _ kx x Tip               =
      singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          balanceL ky y (go f kx x l) r
        GT =>
          balanceR ky y l (go f kx x r)
        EQ =>
          Bin sy ky (f ky y x) l r

||| Insert with a function, combining key, new value and old value.
||| insertWithKey f key value tree
||| will insert the pair (key, value) into tree if key does
||| not exist in the tree. If the key does exist, the function will
||| insert the pair (key,f key new_value old_value). O(log n)
export
insertWithKey :  Ord k
              => (k -> v -> v -> v)
              -> k
              -> v
              -> Tree k v
              -> Tree k v
insertWithKey =
  go
  where
    go :  (k -> v -> v -> v)
       -> k
       -> v
       -> Tree k v
       -> Tree k v
    go _ kx x Tip               =
      singleton kx x
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          balanceL ky y (go f kx x l) r
        GT =>
          balanceR ky y l (go f kx x r)
        EQ =>
          Bin sy kx (f kx x y) l r

||| Combines insert operation with old value retrieval.
||| The expression (insertLookupWithKey f k x tree)
||| is a pair where the first element is equal to (lookup k tree)
||| and the second element equal to (insertWithKey f k x map). O(log n)
export
insertLookupWithKey :  Ord k
                    => (k -> v -> v -> v)
                    -> k
                    -> v
                    -> Tree k v
                    -> (Maybe v, Tree k v)
insertLookupWithKey f0 k0 x0 =
  go f0 k0 x0
  where
    go :  (k -> a -> a -> a)
       -> k
       -> a
       -> Tree k a
       -> (Maybe a, Tree k a)
    go _ kx x Tip               =
      (Nothing, singleton kx x)
    go f kx x (Bin sy ky y l r) =
      case compare kx ky of
        LT =>
          let (found, l') = go f kx x l
              t'          = balanceL ky y l' r
            in (found, t')
        GT =>
          let (found, r') = go f kx x r
              t'          = balanceR ky y l r'
            in (found, t')
        EQ =>
          (Just y, Bin sy kx (f kx x y) l r)

--------------------------------------------------------------------------------
--          Deletion/Update
--------------------------------------------------------------------------------

||| Delete a key and its value from the tree. When the key is not
||| a member of the tree, the original tree is returned. O(log n)
export
delete :  Eq (Tree k v)
       => Eq k
       => Ord k
       => k
       -> Tree k v
       -> Tree k v
delete =
  go
  where
    go :  k
       -> Tree k v
       -> Tree k v
    go _ Tip                =
      Tip
    go k t@(Bin _ kx x l r) =
      case compare k kx of
        LT =>
          let l' = go k l
            in case l' == l of
                 True  =>
                   t
                 False =>
                   balanceR kx x l' r
        GT =>
          let r' = go k r
            in case r' == r of
                 True  =>
                   t
                 False =>
                   balanceL kx x l r'
        EQ =>
          glue l r

||| Adjust a value at a specific key. When the key is not
||| a member of the tree, the original tree is returned. O(log n)
export
adjustWithKey :  Ord k
              => (k -> v -> v)
              -> k
              -> Tree k v
              -> Tree k v
adjustWithKey =
  go
  where
    go :  (k -> v -> v)
       -> k
       -> Tree k v
       -> Tree k v
    go _ _ Tip               =
      Tip
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          Bin sx kx x (go f k l) r
        GT =>
          Bin sx kx x l (go f k r)
        EQ =>
          Bin sx kx (f kx x) l r

||| Update a value at a specific key with the result of the provided function.
||| When the key is not a member of the tree, the original tree is returned. O(log n)
export
adjust :  Ord k
       => (v -> v)
       -> k
       -> Tree k v
       -> Tree k v
adjust f =
  adjustWithKey (\_, x => f x)

||| The expression (updateWithKey f k tree) updates the
||| value x at k (if it is in the tree). If (f k x) is Nothing,
||| the element is deleted. If it is (Just y), the key k is bound
||| to the new value y. O(log n)
export
updateWithKey :  Ord k
              => (k -> v -> Maybe v)
              -> k
              -> Tree k v
              -> Tree k v
updateWithKey =
  go
  where
    go :  (k -> v -> Maybe v)
       -> k
       -> Tree k v
       -> Tree k v
    go _ _ Tip               =
      Tip
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          balanceR kx x (go f k l) r
        GT =>
          balanceL kx x l (go f k r)
        EQ =>
          case f kx x of
            Just x' =>
              Bin sx kx x' l r
            Nothing =>
              glue l r

||| The expression (update f k tree) updates the value x
||| at k (if it is in the tree). If (f x) is Nothing, the element is
||| deleted. If it is (Just y), the key k is bound to the new value y. O(log n)
export
update :  Ord k
       => (v -> Maybe v)
       -> k
       -> Tree k v
       -> Tree k v
update f =
  updateWithKey (\_, x => f x)

||| Lookup and update. See also updateWithKey.
||| The function returns changed value, if it is updated.
||| Returns the original key value if the tree entry is deleted. O(log n)
export
updateLookupWithKey :  Ord k
                    => (k -> v -> Maybe v)
                    -> k
                    -> Tree k v
                    -> (Maybe v, Tree k v)
updateLookupWithKey f0 k0 =
  go f0 k0
  where
    go :  (k -> v -> Maybe v)
       -> k
       -> Tree k v
       -> (Maybe v, Tree k v)
    go _ _ Tip               =
      (Nothing, Tip)
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          let (found, l') = go f k l
              t'          = balanceR kx x l' r
            in (found, t')
        GT =>
          let (found, r') = go f k r
              t'          = balanceL kx x l r'
            in (found, t')
        EQ =>
          case f kx x of
            Just x' =>
              (Just x', Bin sx kx x' l r)
            Nothing =>
              let glued = glue l r
                in (Just x, glued)

||| The expression (alter f k tree) alters the value x at k, or absence thereof.
||| alter can be used to insert, delete, or update a value in a tree. O(log n)
export
alter :  Ord k
      => (Maybe v -> Maybe v)
      -> k
      -> Tree k v
      -> Tree k v
alter =
  go
  where
    go :  (Maybe v -> Maybe v)
       -> k
       -> Tree k v
       -> Tree k v
    go f k Tip               =
      case f Nothing of
        Nothing =>
          Tip
        Just x  =>
          singleton k x
    go f k (Bin sx kx x l r) =
      case compare k kx of
        LT =>
          balance kx x (go f k l) r
        GT =>
          balance kx x l (go f k r)
        EQ =>
          case f (Just x) of
            Just x' =>
              Bin sx kx x' l r
            Nothing =>
              glue l r

--------------------------------------------------------------------------------
--          Query
--------------------------------------------------------------------------------

||| Lookup the value at a key in the tree.
||| The function will return the corresponding value as (Just value),
||| or Nothing if the key isn't in the tree. O(log n)
export
lookup :  Ord k
       => k
       -> Tree k v
       -> Maybe v
lookup =
  go
  where
    go :  k
       -> Tree k v
       -> Maybe v
    go _ Tip              =
      Nothing
    go k (Bin _ kx x l r) =
      case compare k kx of
        LT =>
          go k l
        GT =>
          go k r
        EQ =>
          Just x

||| Find the value at a key.
||| Returns Nothing when the element can not be found. O(log n)
export
(!?) :  Ord k
     => Tree k v
     -> k
     -> Maybe v
(!?) m k =
  lookup k m

||| Is the key a member of the tree? See also notMember. O(log n)
export
member :  Ord k
       => k
       -> Tree k v
       -> Bool
member _ Tip              =
  False
member k (Bin _ kx _ l r) =
  case compare k kx of
    LT =>
      member k l
    GT =>
      member k r
    EQ =>
      True

||| Is the key not a member of the tree? See also member. O(log n)
export
notMember :  Ord k
          => k
          -> Tree k v
          -> Bool
notMember k m =
  not $
    member k m

||| Find the value at a key.
||| Calls idris_crash when the element can not be found. O(log n)
export
find :  Ord k
     => k
     -> Tree k v
     -> v
find _ Tip              =
  assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.find: given key is not an element in the map"
find k (Bin _ kx x l r) =
  case compare k kx of
    LT =>
      find k l
    GT =>
      find k r
    EQ =>
      x

||| Find the value at a key.
||| Calls idris_crash when the element can not be found. O(log n)
export
(!!) :  Ord k
     => Tree k v
     -> k
     -> v
(!!) m k =
  find k m

||| The expression (findWithDefault def k tree) returns
||| the value at key k or returns default value def
||| when the key is not in the tree. O(log n)
export
findWithDefault :  Ord k
                => v
                -> k
                -> Tree k v
                -> v
findWithDefault def _ Tip              =
  def
findWithDefault def k (Bin _ kx x l r) =
  case compare k kx of
    LT =>
      findWithDefault def k l
    GT =>
      findWithDefault def k r
    EQ =>
      x

||| Find largest key smaller than the given one and return the
||| corresponding (key, value) pair. O(log n)
export
lookupLT :  Ord k
         => k
         -> Tree k v
         -> Maybe (k, v)
lookupLT =
  goNothing
  where
    goJust :  k
           -> k
           -> v
           -> Tree k v
           -> Maybe (k, v)
    goJust _ kx' x' Tip              =
      Just (kx', x')
    goJust k kx' x' (Bin _ kx x l r) =
      case k <= kx of
        True  =>
          goJust k kx' x' l
        False =>
          goJust k kx x r
    goNothing :  k
              -> Tree k v
              -> Maybe (k, v)
    goNothing _ Tip              =
      Nothing
    goNothing k (Bin _ kx x l r) =
      case k <= kx of
        True  =>
          goNothing k l
        False =>
          goJust k kx x r

||| Find smallest key greater than the given one and return the
||| corresponding (key, value) pair. O(log n)
export
lookupGT :  Ord k
         => k
         -> Tree k v
         -> Maybe (k, v)
lookupGT =
  goNothing
  where
    goJust :  k
           -> k
           -> v
           -> Tree k v
           -> Maybe (k, v)
    goJust _ kx' x' Tip              =
      Just (kx',x')
    goJust k kx' x' (Bin _ kx x l r) =
      case k < kx of
        True  =>
          goJust k kx x l
        False =>
          goJust k kx' x' r
    goNothing :  k
              -> Tree k v
              -> Maybe (k, v)
    goNothing _ Tip              =
      Nothing
    goNothing k (Bin _ kx x l r) =
      case k < kx of
        True  =>
          goJust k kx x l
        False =>
          goNothing k r

||| Find largest key smaller or equal to the given one and return
||| the corresponding (key, value) pair. O(log n)
export
lookupLE :  Ord k
         => k
         -> Tree k v
         -> Maybe (k, v)
lookupLE =
  goNothing
  where
    goJust :  k
           -> k
           -> v
           -> Tree k v
           -> Maybe (k, v)
    goJust _ kx' x' Tip              =
      Just (kx', x')
    goJust k kx' x' (Bin _ kx x l r) =
      case compare k kx of
        LT =>
          goJust k kx' x' l
        EQ =>
          Just (kx,x)
        GT =>
          goJust k kx x r
    goNothing :  k
              -> Tree k v
              -> Maybe (k, v)
    goNothing _ Tip              =
      Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT =>
          goNothing k l
        EQ =>
          Just (kx,x)
        GT =>
          goJust k kx x r

||| Find smallest key greater or equal to the given one and return
||| the corresponding (key, value) pair. O(log n)
export
lookupGE :  Ord k
         => k
         -> Tree k v
         -> Maybe (k, v)
lookupGE =
  goNothing
  where
    goJust :  k
           -> k
           -> v
           -> Tree k v
           -> Maybe (k, v)
    goJust _ kx' x' Tip              =
      Just (kx', x')
    goJust k kx' x' (Bin _ kx x l r) =
      case compare k kx of
        LT =>
          goJust k kx x l
        EQ =>
          Just (kx, x)
        GT =>
          goJust k kx' x' r
    goNothing :  k
              -> Tree k v
              -> Maybe (k, v)
    goNothing _ Tip              =
      Nothing
    goNothing k (Bin _ kx x l r) =
      case compare k kx of
        LT =>
          goJust k kx x l
        EQ =>
          Just (kx, x)
        GT =>
          goNothing k r

--------------------------------------------------------------------------------
--          Size
--------------------------------------------------------------------------------

||| Is the tree empty? O(1)
export
null :  Tree k v
     -> Bool
null Tip =
  True
null _   =
  False

--------------------------------------------------------------------------------
--          Filter
--------------------------------------------------------------------------------

private
splitMember :  Ord k
            => k
            -> Tree k v
            -> (Tree k v, Bool, Tree k v)
splitMember k0 m =
  go k0 m
  where
    go :  k
       -> Tree k v
       -> (Tree k v, Bool, Tree k v)
    go k t =
      case t of
        Tip            =>
          (Tip, False, Tip)
        Bin _ kx x l r =>
          case compare k kx of
            LT =>
              let (lt, z, gt) = go k l
                in (lt, z, link kx x gt r)
            GT =>
              let (lt, z, gt) = go k r
                in (link kx x l lt, z, gt)
            EQ =>
              (l, True, r)

||| Decompose a tree into pieces based on the structure of the underlying tree.
||| This function is useful for consuming a tree in parallel. O(1)
export
splitRoot :  Tree k v
          -> List (Tree k v)
splitRoot orig =
  case orig of
    Tip           =>
      []
    Bin _ k v l r =>
      [l, singleton k v, r]

||| The expression (splitLookup k tree) splits a tree just
||| like split but also returns lookup k tree. O(log n)
export
splitLookup :  Ord k
            => k
            -> Tree k v
            -> (Tree k v, Maybe v, Tree k v)
splitLookup k0 m =
  go k0 m
  where
    go :  k
       -> Tree k v
       -> (Tree k v, Maybe v, Tree k v)
    go k t =
      case t of
        Tip            =>
          (Tip, Nothing, Tip)
        Bin _ kx x l r =>
          case compare k kx of
          LT =>
            let (lt,z,gt) = go k l
              in (lt,z,link kx x gt r)
          GT =>
            let (lt,z,gt) = go k r
              in (link kx x l lt, z, gt)
          EQ =>
            (l, Just x, r)

||| The expression (split k tree) is a pair (tree1,tree2) where
||| the keys in tree1 are smaller than k and the keys in tree2 larger than k.
||| Any key equal to k is found in neither tree1 nor tree2. O(log n)
export
split :  Ord k
      => k
      -> Tree k v
      -> (Tree k v, Tree k v)
split k0 t0 =
  go k0 t0
  where
    go :  k
       -> Tree k v
       -> (Tree k v, Tree k v)
    go k t =
      case t of
        Tip            =>
          (Tip, Tip)
        Bin _ kx x l r =>
          case compare k kx of
            LT =>
              let (lt, gt) = go k l
                in (lt, link kx x gt r)
            GT =>
              let (lt, gt) = go k r
                in (link kx x l lt, gt)
            EQ =>
              (l, r)

||| Filter all keys/values that satisfy the predicate. O(n)
export
filterWithKey :  Eq (Tree k v)
              => (k -> v -> Bool)
              -> Tree k v
              -> Tree k v
filterWithKey _ Tip                =
  Tip
filterWithKey p t@(Bin _ kx x l r) =
  case p kx x of
    True  =>
      case (filterWithKey p l) == l && (filterWithKey p r) == r of
        True  =>
          t
        False =>
          link kx x (filterWithKey p l) (filterWithKey p r)
    False =>
      link2 (filterWithKey p l) (filterWithKey p r)

||| Filter all values that satisfy the predicate. O(n)
export
filter :  Eq (Tree k v)
       => (v -> Bool)
       -> Tree k v
       -> Tree k v
filter p m =
  filterWithKey (\_, x => p x) m

||| Partition the tree according to a predicate. The first
||| tree contains all elements that satisfy the predicate, the second all
||| elements that fail the predicate. See also split. O(n)
export
partitionWithKey :  Eq (Tree k v)
                 => (k -> v -> Bool)
                 -> Tree k v
                 -> (Tree k v, Tree k v)
partitionWithKey p0 t0 =
  go p0 t0
  where
    go :  (k -> v -> Bool)
       -> Tree k v
       -> (Tree k v, Tree k v)
    go _ Tip                =
      (Tip, Tip)
    go p t@(Bin _ kx x l r) =
      case p kx x of
        True  =>
          ( case (fst $ go p l) == l && (fst $ go p r) == r of
             True  =>
               t
             False =>
               link kx x (fst $ go p l) (fst $ go p r)
          , link2 (snd $ go p l) (snd $ go p r)
          )
        False =>
          ( link2 (fst $ go p l) (fst $ go p r)
          , case (snd $ go p l) == l && (snd $ go p r) == r of
              True  =>
                t
              False =>
                link kx x (snd $ go p l) (snd $ go p r)
          )

||| Take while a predicate on the keys holds.
||| The user is responsible for ensuring that for all keys j and k in the tree,
||| j < k ==> p j >= p k. See note at spanAntitone. O(log n)
export
takeWhileAntitone :  (k -> Bool)
                  -> Tree k v
                  -> Tree k v
takeWhileAntitone _ Tip              =
  Tip
takeWhileAntitone p (Bin _ kx x l r) =
  case p kx of
    True  =>
      link kx x l (takeWhileAntitone p r)
    False =>
      takeWhileAntitone p l

||| Drop while a predicate on the keys holds.
||| The user is responsible for ensuring that for all keys j and k in the tree,
||| j < k ==> p j >= p k. See note at spanAntitone. O(log n)
export
dropWhileAntitone :  (k -> Bool)
                  -> Tree k v
                  -> Tree k v
dropWhileAntitone _ Tip              =
  Tip
dropWhileAntitone p (Bin _ kx x l r) =
  case p kx of
    True  =>
      dropWhileAntitone p r
    False =>
      link kx x (dropWhileAntitone p l) r

||| Divide a map at the point where a predicate on the keys stops holding.
||| The user is responsible for ensuring that for all keys j and k in the tree,
||| j < k ==> p j>= p k. O(log n)
export
spanAntitone :  (k -> Bool)
             -> Tree k v
             -> (Tree k v, Tree k v)
spanAntitone p0 m =
  go p0 m
  where
    go :  (k -> Bool)
       -> Tree k v
       -> (Tree k v, Tree k v)
    go _ Tip              =
      (Tip, Tip)
    go p (Bin _ kx x l r) =
      case p kx of
        True  =>
          let (u, v) = go p r
            in (link kx x l u, v)
        False =>
          let (u, v) = go p l
            in (u, link kx x v r)

||| Map keys/values and collect the Just results. O(n)
export
mapMaybeWithKey :  (k -> a -> Maybe b)
                -> Tree k a
                -> Tree k b
mapMaybeWithKey _ Tip              =
  Tip
mapMaybeWithKey f (Bin _ kx x l r) =
  case f kx x of
    Just y  =>
      link kx y (mapMaybeWithKey f l) (mapMaybeWithKey f r)
    Nothing =>
      link2 (mapMaybeWithKey f l) (mapMaybeWithKey f r)

||| Map values and collect the Just results. O(n)
export
mapMaybe :  (a -> Maybe b)
         -> Tree k a
         -> Tree k b
mapMaybe f =
  mapMaybeWithKey (\_, x => f x)

||| Map keys/values and separate the Left and Right results. O(n)
export
mapEitherWithKey :  (k -> a -> Either b c)
                 -> Tree k a
                 -> (Tree k b, Tree k c)
mapEitherWithKey f0 t0 =
  go f0 t0
  where
    go :  (k -> a -> Either b c)
       -> Tree k a
       -> (Tree k b, Tree k c)
    go _ Tip              =
      (Tip, Tip)
    go f (Bin _ kx x l r) =
      case f kx x of
        Left  y =>
          (link kx y (fst $ go f l) (fst $ go f r), link2 (snd $ go f l) (snd $ go f r))
        Right z =>
          (link2 (fst $ go f l) (fst $ go f r), link kx z (snd $ go f l) (snd $ go f r))

||| Map values and separate the Left and Right results. O(n)
export
mapEither :  (a -> Either b c)
          -> Tree k a
          -> (Tree k b, Tree k c)
mapEither f m =
  mapEitherWithKey (\_, x => f x) m

--------------------------------------------------------------------------------
--          Subtree
--------------------------------------------------------------------------------

private
subtree' :  Ord a
         => (b -> c -> Bool)
         -> Tree a b
         -> Tree a c
         -> Bool
subtree' _ Tip _              =
  True
subtree' _ _   Tip            =
  False
subtree' f (Bin 1 kx x _ _) t =
  case lookup kx t of
    Just y  =>
      f x y
    Nothing =>
      False
subtree' f (Bin _ kx x l r) t =
  let (lt,found,gt) = splitLookup kx t
    in case found of
         Nothing =>
           False
         Just y  =>
           f x y && size l <= size lt
                 && size r <= size gt
                 && subtree' f l lt
                 && subtree' f r gt

||| The expression (isSubtreeOfBy f t1 t2) returns True if
||| all keys in t1 are in tree t2, and when f returns True when
||| applied to their respective values.
export
isSubtreeOfBy :  Ord k
              => (a -> b -> Bool)
              -> Tree k a
              -> Tree k b
              -> Bool
isSubtreeOfBy f t1 t2 =
  size t1 <= size t2 && subtree' f t1 t2

||| This function is defined as (isSubtreeOf = isSubtreeOfBy (==)).
export
isSubtreeOf :  Eq v
            => Ord k
            => Tree k v
            -> Tree k v
            -> Bool
isSubtreeOf m1 m2 =
  isSubtreeOfBy (==) m1 m2

||| Is this a proper subtree? (ie. a subtree but not equal).
||| The expression (isProperSubtreeOfBy f m1 m2) returns True when
||| keys m1 and keys m2 are not equal,
||| all keys in m1 are in m2, and when f returns True when
||| applied to their respective values.
export
isProperSubtreeOfBy :  Ord k
                    => (a -> b -> Bool)
                    -> Tree k a
                    -> Tree k b
                    -> Bool
isProperSubtreeOfBy f t1 t2 =
  size t1 < size t2 && subtree' f t1 t2

||| Is this a proper subtree? (ie. a subtree but not equal).
||| Defined as (isProperSubtreeOf = isProperSubtreeOfBy (==)).
export
isProperSubmapOf :  Eq v
                 => Ord k
                 => Tree k v
                 -> Tree k v
                 -> Bool
isProperSubmapOf m1 m2 =
  isProperSubtreeOfBy (==) m1 m2

--------------------------------------------------------------------------------
--          Indexed
--------------------------------------------------------------------------------

||| Lookup the index of a key, which is its zero-based index in
||| the sequence sorted by keys. The index is a number from 0 up to, but not
||| including, the size of the tree. O(log n)
export
lookupIndex :  Ord k
            => k
            -> Tree k v
            -> Maybe Nat
lookupIndex =
  go 0
  where
    go :  Nat
       -> k
       -> Tree k a
       -> Maybe Nat
    go _  _ Tip               =
      Nothing
    go idx k (Bin _ kx _ l r) =
      case compare k kx of
        LT =>
          go idx k l
        GT =>
          go (idx + size l + 1) k r
        EQ =>
          Just $ idx + size l

||| Return the index of a key, which is its zero-based index in
||| the sequence sorted by keys. The index is a number from 0 up to, but not
||| including, the size of the tree. Calls idris_crash when the key is not
||| a member of the tree. O(log n)
export
findIndex :  Ord k
          => k
          -> Tree k v
          -> Nat
findIndex =
  go 0
  where
    go :  Nat
       -> k
       -> Tree k a
       -> Nat
    go _   _ Tip              =
      assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.findIndex: element is not in the tree"
    go idx k (Bin _ kx _ l r) =
      case compare k kx of
        LT =>
          go idx k l
        GT =>
          go (idx + size l + 1) k r
        EQ =>
          idx + size l

||| Retrieve an element by its index, i.e. by its zero-based
||| index in the sequence sorted by keys. If the index is out of range (less
||| than zero, greater or equal to size of the map), idris_crash is called. O(log n)
export
elemAt :  Nat
       -> Tree k v
       -> (k, v)
elemAt _ Tip              =
  assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.elemAt: index out of range"
elemAt i (Bin _ kx x l r) =
  case compare i (size l) of
     LT =>
       elemAt i l
     GT =>
       elemAt ((i `minus` (size l)) `minus` 1) r
     EQ =>
       (kx,x)

||| Update the element at index, i.e. by its zero-based index in
||| the sequence sorted by keys. If the index is out of range (less than zero,
||| greater or equal to size of the tree), idris_crash is called. O(log n)
export
updateAt :  (k -> v -> Maybe v)
         -> Nat
         -> Tree k v
         -> Tree k v
updateAt f i t =
  case t of
    Tip             =>
      assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.updateAt: index out of range"
    Bin sx kx x l r =>
      case compare i (size l) of
        LT =>
          balanceR kx x (updateAt f i l) r
        GT =>
          balanceL kx x l (updateAt f ((i `minus` (size l)) `minus` 1) r)
        EQ =>
          case f kx x of
            Just x' =>
              Bin sx kx x' l r
            Nothing =>
              glue l r

||| Delete the element at index, i.e. by its zero-based index in
||| the sequence sorted by keys. If the index is out of range (less than zero,
||| greater or equal to size of the tree), idris_crash is called. O(log n)
export
deleteAt :  Nat
         -> Tree k v
         -> Tree k v
deleteAt i t =
  case t of
    Tip            =>
      assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.deleteAt: index out of range"
    Bin _ kx x l r =>
      case compare i (size l) of
        LT =>
          balanceR kx x (deleteAt i l) r
        GT =>
          balanceL kx x l (deleteAt ((i `minus` (size l)) `minus` 1) r)
        EQ =>
          glue l r

||| Take a given number of entries in key order, beginning
||| with the smallest keys. O(log n)
export
take :  Nat
     -> Tree k v
     -> Tree k v
take i m =
  case i >= size m of
    True  =>
      m
    False =>
      go i m
  where
    go :  Nat
       -> Tree k v
       -> Tree k v
    go _ Tip              =
      Tip
    go i (Bin _ kx x l r) =
      case i <= 0 of
        True  =>
          Tip
        False =>
          case compare i (size l) of
            LT =>
              go i l
            GT =>
              link kx x l (go ((i `minus` (size l)) `minus` 1) r)
            EQ =>
              l

||| Drop a given number of entries in key order, beginning
||| with the smallest keys. O(log n)
export
drop :  Nat
     -> Tree k v
     -> Tree k v
drop i m =
  case i >= size m of
    True  =>
      Tip
    False =>
      go i m
  where
    go :  Nat
       -> Tree k v
       -> Tree k v
    go _ Tip              =
      Tip
    go i (Bin _ kx x l r) =
      case i <= 0 of
        True  =>
          m
        False =>
          case compare i (size l) of
            LT =>
              link kx x (go i l) r
            GT =>
              go ((i `minus` (size l)) `minus` 1) r
            EQ =>
              insertMin kx x r

||| Split a tree at a particular index. O(log n)
export
splitAt :  Nat
        -> Tree k v
        -> (Tree k v, Tree k v)
splitAt i m =
  case i >= size m of
    True  =>
      (m,Tip)
    False =>
      go i m
  where
    go :  Nat
       -> Tree k v
       -> (Tree k v, Tree k v)
    go _ Tip              =
      (Tip, Tip)
    go i (Bin _ kx x l r) =
      case i <= 0 of
        True  =>
          (Tip, m)
        False =>
          case compare i (size l) of
            LT =>
              case go i l of
                (ll, lr) =>
                  (ll, link kx x lr r)
            GT =>
              case go ((i `minus` (size l)) `minus` 1) r of
                (rl, rr) =>
                  (link kx x l rl, rr)
            EQ =>
              (l, insertMin kx x r)

--------------------------------------------------------------------------------
--          Min/Max
--------------------------------------------------------------------------------

private
lookupMinSure :  k
              -> v
              -> Tree k v
              -> (k, v)
lookupMinSure k v Tip             =
  (k, v)
lookupMinSure _ _ (Bin _ k v l _) =
  lookupMinSure k v l

||| The minimal key of the tree. Returns Nothing if the tree is empty. O(log n)
export
lookupMin :  Tree k v
          -> Maybe (k, v)
lookupMin Tip             =
  Nothing
lookupMin (Bin _ k v l _) =
  Just $ lookupMinSure k v l

private
lookupMaxSure :  k
              -> v
              -> Tree k v
              -> (k, v)
lookupMaxSure k v Tip             =
  (k, v)
lookupMaxSure _ _ (Bin _ k v _ r) =
  lookupMaxSure k v r

||| The maximal key of the tree. Returns Nothing if the tree is empty. O(log n)
export
lookupMax :  Tree k v
          -> Maybe (k, v)
lookupMax Tip             =
  Nothing
lookupMax (Bin _ k v _ r) =
  Just $ lookupMaxSure k v r

||| The minimal key of the tree. Calls idris_crash if the tree is empty. O(log n)
export
findMin :  Tree k v
        -> (k, v)
findMin t =
  case lookupMin t of
    Just r  =>
      r
    Nothing =>
      assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.findMin: empty map has no minimal element"

||| The maximal key of the tree. Calls idris_crash if the tree is empty. O(log n)
export
findMax :  Tree k v
        -> (k, v)
findMax t =
  case lookupMax t of
    Just r  =>
      r
    Nothing =>
      assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.findMax: empty map has no maximal element"

||| Delete the minimal key. Returns an empty tree if the tree is empty. O(log n)
export
deleteMin :  Tree k v
          -> Tree k v
deleteMin Tip                 =
  Tip
deleteMin (Bin _ _  _ Tip r)  =
  r
deleteMin (Bin _ kx x l   r)  =
  balanceR kx x (deleteMin l) r

||| Delete the maximal key. Returns an empty tree if the tree is empty. O(log n)
export
deleteMax :  Tree k v
          -> Tree k v
deleteMax Tip                 =
  Tip
deleteMax (Bin _ _  _ l Tip)  =
  l
deleteMax (Bin _ kx x l r)    =
  balanceL kx x l (deleteMax r)

||| Retrieves the minimal (key,value) pair of the tree, and
||| the tree stripped of that element, or Nothing if passed an empty tree. O(log n)
export
minViewWithKey :  Tree k v
               -> Maybe ((k, v), Tree k v)
minViewWithKey Tip             =
  Nothing
minViewWithKey (Bin _ k x l r) =
  Just $
    case minViewSure k x l r of
      MinView' km xm t =>
        ((km, xm), t)

||| Delete and find the minimal element. O(log n)
export
deleteFindMin :  Tree k v
              -> ((k, v), Tree k v)
deleteFindMin t =
  case minViewWithKey t of
    Just res =>
      res
    Nothing  =>
      (assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.deleteFindMin: can not return the minimal element of an empty map", Tip)

||| Retrieves the maximal (key,value) pair of the tree, and
||| the tree stripped of that element, or Nothing if passed an empty tree. O(log n)
export
maxViewWithKey :  Tree k v
               -> Maybe ((k, v), Tree k v)
maxViewWithKey Tip             =
  Nothing
maxViewWithKey (Bin _ k x l r) =
  Just $
    case maxViewSure k x l r of
      MaxView' km xm t =>
        ((km, xm), t)

||| Delete and find the maximal element. O(log n)
export
deleteFindMax :  Tree k v
              -> ((k, v), Tree k v)
deleteFindMax t =
  case maxViewWithKey t of
    Just res =>
      res
    Nothing  =>
      (assert_total $ idris_crash "Data.Map.Sized.Internal.Tree.deleteFindMax: can not return the maximal element of an empty map", Tip)

||| Update the value at the minimal key. O(log n)
export
updateMinWithKey :  (k -> v -> Maybe v)
                 -> Tree k v
                 -> Tree k v
updateMinWithKey _ Tip                 =
  Tip
updateMinWithKey f (Bin sx kx x Tip r) =
  case f kx x of
    Nothing => r
    Just x' => Bin sx kx x' Tip r
updateMinWithKey f (Bin _ kx x l r)    =
  balanceR kx x (updateMinWithKey f l) r

||| Update the value at the minimal key. O(log n)
export
updateMin :  (v -> Maybe v)
          -> Tree k v
          -> Tree k v
updateMin f m =
  updateMinWithKey (\_, x => f x) m

||| Update the value at the maximal key. O(log n)
export
updateMaxWithKey :  (k -> v -> Maybe v)
                 -> Tree k v
                 -> Tree k v
updateMaxWithKey _ Tip                 =
  Tip
updateMaxWithKey f (Bin sx kx x l Tip) =
  case f kx x of
    Nothing =>
      l
    Just x' =>
      Bin sx kx x' l Tip
updateMaxWithKey f (Bin _ kx x l r)    =
  balanceL kx x l (updateMaxWithKey f r)

||| Update the value at the maximal key. O(log n)
export
updateMax :  (v -> Maybe v)
          -> Tree k v
          -> Tree k v
updateMax f m =
  updateMaxWithKey (\_, x => f x) m

||| Retrieves the value associated with minimal key of the
||| tree, and the tree stripped of that element, or Nothing if passed an empty tree. O(log n)
export
minView :  Tree k v
        -> Maybe (v, Tree k v)
minView t =
  case minViewWithKey t of
    Nothing           =>
      Nothing
    Just ((_, x), t') =>
      Just (x, t')

||| Retrieves the value associated with maximal key of the
||| tree, and the tree stripped of that element, or Nothing if passed an empty tree. O(log n)
export
maxView :  Tree k v
        -> Maybe (v, Tree k v)
maxView t =
  case maxViewWithKey t of
    Nothing           =>
      Nothing
    Just ((_, x), t') =>
      Just (x, t')

--------------------------------------------------------------------------------
--          Combine
--------------------------------------------------------------------------------

||| The expression (union t1 t2) takes the left-biased union of t1 and t2.
||| It prefers t1 when duplicate keys are encountered.
export
union :  Eq (Tree k v)
      => Eq v
      => Ord k
      => Tree k v
      -> Tree k v
      -> Tree k v
union t1                     Tip                 =
  t1
union t1                     (Bin _ k x Tip Tip) =
  insertR k x t1
union (Bin _ k x Tip Tip)    t2                  =
  insert k x t2
union Tip                    t2                  =
  t2
union t1@(Bin _ k1 x1 l1 r1) t2                  =
  let (l2, r2) = split k1 t2
    in case (union l1 l2) == l1 && (union r1 r2) == r1 of
         True  =>
           t1
         False =>
           link k1 x1 (union l1 l2) (union r1 r2)

||| Union with a combining function.
export
unionWith :  Ord k
          => (v -> v -> v)
          -> Tree k v
          -> Tree k v
          -> Tree k v
unionWith _ t1                  Tip                 =
  t1
unionWith f t1                  (Bin _ k x Tip Tip) =
  insertWithR f k x t1
unionWith f (Bin _ k x Tip Tip) t2                  =
  insertWith f k x t2
unionWith _ Tip                 t2                  =
  t2
unionWith f (Bin _ k1 x1 l1 r1) t2                  =
  let (l2, mb, r2) = splitLookup k1 t2
    in case mb of
         Nothing =>
           link k1 x1 (unionWith f l1 l2) (unionWith f r1 r2)
         Just x2 =>
           link k1 (f x1 x2) (unionWith f l1 l2) (unionWith f r1 r2)

||| Union with a combining function.
export
unionWithKey :  Ord k
             => (k -> v -> v -> v)
             -> Tree k v
             -> Tree k v
             -> Tree k v
unionWithKey _ t1                  Tip                 =
  t1
unionWithKey f t1                  (Bin _ k x Tip Tip) =
  insertWithKeyR f k x t1
unionWithKey f (Bin _ k x Tip Tip) t2                  =
  insertWithKey f k x t2
unionWithKey _ Tip                 t2                  =
  t2
unionWithKey f (Bin _ k1 x1 l1 r1) t2                  =
  let (l2, mb, r2) = splitLookup k1 t2
    in case mb of
         Nothing =>
           link k1 x1 (unionWithKey f l1 l2) (unionWithKey f r1 r2)
         Just x2 =>
           link k1 (f k1 x1 x2) (unionWithKey f l1 l2) (unionWithKey f r1 r2)

||| The union of a list of trees.
export
unions :  Eq (Tree k v)
       => Eq v
       => Foldable f
       => Ord k
       => f (Tree k v)
       -> Tree k v
unions ts =
  foldl union empty ts

||| The union of a list of trees, with a combining operation.
export
unionsWith :  Foldable f
           => Ord k
           => (v -> v -> v)
           -> f (Tree k v)
           -> Tree k v
unionsWith f ts =
  foldl (unionWith f) empty ts

--------------------------------------------------------------------------------
--          Difference
--------------------------------------------------------------------------------

||| Difference of two trees.
||| Return elements of the first tree not existing in the second tree.
export
difference :  Ord k
           => Tree k a
           -> Tree k b
           -> Tree k a
difference Tip _                =
  Tip
difference t1 Tip               =
  t1
difference t1 (Bin _ k _ l2 r2) =
  let (l1, r1) = split k t1
    in case size (difference l1 l2) + size (difference r1 r2) == size t1 of
         True  =>
           t1
         False =>
           link2 (difference l1 l2) (difference r1 r2)

||| Same as difference.
export
(\\) :  Ord k
     => Tree k a
     -> Tree k b
     -> Tree k a
m1 \\ m2 =
  difference m1 m2

--------------------------------------------------------------------------------
--          Intersection
--------------------------------------------------------------------------------

||| Intersection of two trees.
||| Return data in the first tree for the keys existing in both trees.
export
intersection :  Eq (Tree k a)
             => Ord k
             => Tree k a
             -> Tree k b
             -> Tree k a
intersection Tip                  _   =
  Tip
intersection _                    Tip =
  Tip
intersection t1@(Bin _ k x l1 r1) t2  =
  case splitMember k t2 of
    (l2, True, r2)  =>
      case (intersection l1 l2) == l1 && (intersection r1 r2) == r1 of
        True  =>
          t1
        False =>
          link k x (intersection l1 l2) (intersection r1 r2)
    (l2, False, r2) =>
      link2 (intersection l1 l2) (intersection r1 r2)

||| Intersection with a combining function.
export
intersectionWith :  Ord k
                 => (a -> b -> c)
                 -> Tree k a
                 -> Tree k b
                 -> Tree k c
intersectionWith f Tip                _   =
  Tip
intersectionWith f _                  Tip =
  Tip
intersectionWith f (Bin _ k x1 l1 r1) t2  =
  case splitLookup k t2 of
    (l2, Just x2, r2) =>
      link k (f x1 x2) (intersectionWith f l1 l2) (intersectionWith f r1 r2)
    (l2, Nothing, r2) =>
      link2 (intersectionWith f l1 l2) (intersectionWith f r1 r2)

||| Intersection with a combining function.
export
intersectionWithKey :  Ord k
                    => (k -> a -> b -> c)
                    -> Tree k a
                    -> Tree k b
                    -> Tree k c
intersectionWithKey f Tip                _   =
  Tip
intersectionWithKey f _                  Tip =
  Tip
intersectionWithKey f (Bin _ k x1 l1 r1) t2  =
  case splitLookup k t2 of
    (l2, Just x2, r2) =>
      link k (f k x1 x2) (intersectionWithKey f l1 l2) (intersectionWithKey f r1 r2)
    (l2, Nothing, r2) =>
      link2 (intersectionWithKey f l1 l2) (intersectionWithKey f r1 r2)

--------------------------------------------------------------------------------
--          Disjoint
--------------------------------------------------------------------------------

||| Check whether the key sets of two
||| trees are disjoint (i.e., their intersection is empty).
export
disjoint :  Ord k
         => Tree k a
         -> Tree k b
         -> Bool
disjoint Tip             _   =
  True
disjoint _               Tip =
  True
disjoint (Bin 1 k _ _ _) t   =
  k `notMember` t
disjoint (Bin _ k _ l r) t   =
  let (lt,found,gt) = splitMember k t
    in not found && disjoint l lt && disjoint r gt

--------------------------------------------------------------------------------
--          Compose
--------------------------------------------------------------------------------

||| Relate the keys of one tree to the values of
||| the other, by using the values of the former as keys for lookups in the latter.
||| O(n * log(m)), where m is the size of the first argument.
export
compose :  Ord b
        => Tree b c
        -> Tree a b
        -> Tree  a c
compose bc ab =
  case null bc of
    True  =>
      empty
    False =>
      mapMaybe ((!?) bc) ab

--------------------------------------------------------------------------------
--          Traversal
--------------------------------------------------------------------------------

||| Map a function over all values in the tree. O(n)
export
map :  (v -> w)
    -> Tree k v
    -> Tree k w
map _ Tip               =
  Tip
map f (Bin sx kx x l r) =
  Bin sx kx (f x) (map f l) (map f r)

||| Map a function over all values in the tree. O(n)
export
mapWithKey :  (k -> v -> w)
           -> Tree k v
           -> Tree k w
mapWithKey _ Tip               =
  Tip
mapWithKey f (Bin sx kx x l r) =
  Bin sx kx (f kx x) (mapWithKey f l) (mapWithKey f r)

||| The function mapAccumL threads an accumulating
||| argument through the tree in ascending order of keys. O(n)
export
mapAccumL :  (v -> k -> w -> (v, c))
          -> v
          -> Tree k w
          -> (v, Tree k c)
mapAccumL _ a Tip               =
  (a, Tip)
mapAccumL f a (Bin sx kx x l r) =
  let (a1, l') = mapAccumL f a l
      (a2, x') = f a1 kx x
      (a3, r') = mapAccumL f a2 r
    in (a3, Bin sx kx x' l' r')

||| The function mapAccumRWithKey threads an accumulating
||| argument through the tree in descending order of keys. O(n)
export
mapAccumRWithKey :  (v -> k -> w -> (v, c))
                 -> v
                 -> Tree k w
                 -> (v, Tree k c)
mapAccumRWithKey _ a Tip               =
  (a, Tip)
mapAccumRWithKey f a (Bin sx kx x l r) =
  let (a1, r') = mapAccumRWithKey f a r
      (a2, x') = f a1 kx x
      (a3, l') = mapAccumRWithKey f a2 l
    in (a3, Bin sx kx x' l' r')

||| The function mapAccumWithKey threads an accumulating
||| argument through the tree in ascending order of keys. O(n)
export
mapAccumWithKey :  (v -> k -> w -> (v, c))
                -> v
                -> Tree k w
                -> (v, Tree k c)
mapAccumWithKey f a t =
  mapAccumL f a t

||| The function mapAccum threads an accumulating
||| argument through the tree in ascending order of keys. O(n)
export
mapAccum :  (v -> w -> (v, c))
         -> v
         -> Tree k w
         -> (v, Tree k c)
mapAccum f a m =
  mapAccumWithKey (\a', _, x' => f a' x') a m

--------------------------------------------------------------------------------
--          Lists
--------------------------------------------------------------------------------

||| Convert the tree to a list of key/value pairs where the keys are in descending order. O(n)
export
toDescList :  Tree k v
           -> List (k, v)
toDescList Tip               =
  []
toDescList t@(Bin _ _ _ _ _) =
  foldlWithKey (\xs, k, x => (k,x) :: xs) [] t

||| Convert the tree to a list of key/value pairs where the keys are in ascending order. O(n)
export
toAscList :  Tree k v
          -> List (k, v)
toAscList Tip               =
  []
toAscList t@(Bin _ _ _ _ _) =
  foldrWithKey (\k, x, xs => (k,x) :: xs) [] t

||| Convert the tree to a list of key/value pairs.
export
toList :  Tree k v
       -> List (k, v)
toList =
  toAscList

||| Build a tree from a list of key/value pairs.
||| If the list contains more than one value for the same key, the last value
||| for the key is retained.
||| If the keys of the list are ordered, a linear-time implementation is used. O(n * log(n))
export
fromList :  Ord k
         => Eq v
         => Eq (Tree k v)
         => List (k, v)
         -> Tree k v
fromList Nil                =
  Tip
fromList ((kx, x) :: [])    =
  Bin 1 kx x Tip Tip
fromList ((kx0, x0) :: xs0) =
  case notOrdered kx0 xs0 of
    True  =>
      fromList' (Bin 1 kx0 x0 Tip Tip) xs0
    False =>
      go 1 (Bin 1 kx0 x0 Tip Tip) xs0
  where
    notOrdered :  Ord a
               => a
               -> List (a, b)
               -> Bool
    notOrdered _  []             =
      False
    notOrdered kx ((ky, _) :: _) =
      kx >= ky
    fromList' :  Tree k v
              -> List (k, v)
              -> Tree k v
    fromList' t0 xs =
      foldl (\t, (k, x) => insert k x t) t0 xs
    create :  Nat
           -> List (k, v)
           -> (Tree k v, List (k, v), List (k, v))
    create _ []                  =
      (Tip, [], [])
    create s xs@((kx, x) :: xss) =
      case s == 1 of
        True  =>
          case notOrdered kx xss of
            True  =>
              (Bin 1 kx x Tip Tip, [], xss)
            False =>
              (Bin 1 kx x Tip Tip, xss, [])
        False =>
          let create' = assert_total $ create (integerToNat ((natToInteger s) `shiftR` 1)) xs
            in case create' of
                 res@(_, []                 , _)  =>
                   res
                 (l    , [(ky, y)]          , zs) =>
                   (insertMax ky y l, [], zs)
                 (l    , ys@((ky, y) :: yss), _)  =>
                   case notOrdered ky yss of
                     True  =>
                       (l, [], ys)
                     False =>
                       let (r, zs, ws) = assert_total $ create (integerToNat ((natToInteger s) `shiftR` 1)) yss
                         in (link ky y l r, zs, ws)
    go :  Nat
       -> Tree k v
       -> List (k, v)
       -> Tree k v
    go _ t []                  =
      t
    go _ t ((kx, x) :: [])     =
      insertMax kx x t
    go s l xs@((kx, x) :: xss) =
      case notOrdered kx xss of
        True  =>
          fromList' l xs
        False =>
          case create s xss of
            (r, ys, []) =>
              assert_total $ go (integerToNat ((natToInteger s) `shiftL` 1)) (link kx x l r) ys
            (r, _,  ys) =>
              fromList' (link kx x l r) ys

--------------------------------------------------------------------------------
--          Keys
--------------------------------------------------------------------------------

||| Gets the keys of the tree.
export
keys :  Tree k v
     -> List k
keys =
  map fst . toList

--------------------------------------------------------------------------------
--          Values
--------------------------------------------------------------------------------

||| Gets the values of the tree.
||| Could contain duplicates.
export
values :  Tree k v
       -> List v
values =
  map snd . toList

--------------------------------------------------------------------------------
--          Interfaces
--------------------------------------------------------------------------------

export
Functor (Tree k) where
  map f m = map f m

export
Foldable (Tree k) where
  foldl f z = foldl f z . values
  foldr f z = foldr f z . values
  null      = null

private
Show k => Show v => Show (List (k, v)) where
  show xs = "[" ++ show' xs ++ "]"
    where
      show'' : (k, v) -> String
      show'' (k, v) = "(" ++ show k ++ ", " ++ show v ++ ")"
      show' : List (k, v) -> String
      show' Nil        = ""
      show' (x :: Nil) = show'' x
      show' (x :: xs)  = show'' x ++ ", " ++ show' xs

export
Show (List (k, v)) => Show (Tree k v) where
  show m = "fromList " ++ (show $ toList m)
