{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module GHC.Generics.Pruning
  ( GPruning(..)
  , Unifies

  , Unify
  , test_Unify_var_match
  , test_Unify_nested_match
  , test_Unify_complex_match
  , test_Unify_no_match_var
  , test_Unify_no_match_const
  , test_Unify_match_list

  , UnifyVar
  , test_UnifyVar_fresh
  , test_UnifyVar_twice
  , test_UnifyVar_no_match_var
  )
  where

import Data.Kind ( Type )
import Data.Proxy ( Proxy(..)  )
import Data.Type.Equality ( (:~:)(Refl), type (==) )

import GHC.Generics
import GHC.Generics.Exts
import GHC.TypeLits (Symbol)



-- | Pruning of unreachable summands from a Generic representation.
--   This makes sense when working with GADTs, since knowing a specific
--   type may make summands impossible to pattern match.
class GPruning (a :: [Type]) (rep :: k -> Type) where
    type Pruned a rep :: k -> Type

    gprune  :: Proxy a -> rep x -> Pruned a rep x
    gextend :: Proxy a -> Pruned a rep x -> rep x


instance GPruning a V1 where
    type Pruned a V1 = V1

    gprune  _ = \case
    gextend _ = \case

instance GPruning a U1 where
    type Pruned a U1 = U1

    gprune  _ = id
    gextend _ = id

instance GPruning a (K1 r x) where
    type Pruned a (K1 r x) = K1 r x

    gprune  _ = id
    gextend _ = id

instance GPruning a (GEx free bound ftvars btvars t) where
    type Pruned a (GEx free bound ftvars btvars t) = GEx free bound ftvars btvars t

    gprune  _ = id
    gextend _ = id

instance GPruning a (c :=>: t) where
    type Pruned a (c :=>: t) = (c :=>: t)

    gprune  _ = id
    gextend _ = id

instance GPruning a (l :*: r) where
    type Pruned a (l :*: r) = l :*: r

    gprune  _ = id
    gextend _ = id

instance (GPruning a t, PruneM1If (Pruned a t == V1)) => GPruning a (M1 i c t) where
    type Pruned a (M1 i c t) = PrunedM1 (Pruned a t == V1) i c (Pruned a t)

    gprune  = pruneM1  (Proxy :: Proxy (Pruned a t == V1))
    gextend = extendM1 (Proxy :: Proxy (Pruned a t == V1))

instance
  ( GPruning a l
  , GPruning a r
  , PruneSummands (ReachableSummands (Pruned a l) (Pruned a r))
  ) => GPruning a (l :+: r) where
    type Pruned a (l :+: r) = PrunedSummands (ReachableSummands (Pruned a l) (Pruned a r)) (Pruned a l) (Pruned a r)

    gprune  = pruneSummands  (Proxy :: Proxy (ReachableSummands (Pruned a l) (Pruned a r)))
    gextend = extendSummands (Proxy :: Proxy (ReachableSummands (Pruned a l) (Pruned a r)))

instance PruneGC1IfNot (Unifies a a_gd1) => GPruning a_gd1 (GC1 a t) where
    type Pruned a_gd1 (GC1 a t)
      = PrunedIfNot (Unifies a a_gd1) a t

    gprune  = pruneGC1  (Proxy :: Proxy (Unifies a a_gd1))
    gextend = extendGC1 (Proxy :: Proxy (Unifies a a_gd1))


-- ----------------------------------------------------------------------------
-- Prune metadata
-- ----------------------------------------------------------------------------

class PruneM1If (b :: Bool) where
  type PrunedM1 b i (c :: Meta) (rep :: k -> Type) :: k -> Type

  pruneM1
    :: ( b ~ (Pruned a rep == V1)
       , GPruning a rep
       )
    => Proxy b
    -> Proxy a
    -> M1 i c rep x
    -> PrunedM1 b i c (Pruned a rep) x

  extendM1
    :: ( b ~ (Pruned a rep == V1)
       , GPruning a rep
       )
    => Proxy b
    -> Proxy a
    -> PrunedM1 b i c (Pruned a rep) x
    -> M1 i c rep x

instance PruneM1If 'True where
    type PrunedM1 'True i c rep = V1

    pruneM1  _ pa (M1 rep) = case gprune pa rep of _ -> error "pruneM1: impossible -- V1"
    extendM1 _ _ = \case

instance PruneM1If 'False where
    type PrunedM1 'False i c rep = M1 i c rep

    pruneM1  _ pa (M1 rep)  = M1 (gprune  pa rep)
    extendM1 _ pa (M1 prep) = M1 (gextend pa prep)


-- ----------------------------------------------------------------------------
-- Prune sums
-- ----------------------------------------------------------------------------

data Summands
  = LeftSummand
  | RightSummand
  | BothSummands
  | NoSummand

type family ReachableSummands (repl :: k -> Type) (repr :: k -> Type):: Summands where
  ReachableSummands V1 V1 = 'NoSummand
  ReachableSummands V1 _  = 'RightSummand
  ReachableSummands  _ V1 = 'LeftSummand
  ReachableSummands  _ _  = 'BothSummands


class PruneSummands (s :: Summands) where
    type PrunedSummands s (l :: k -> Type) (r :: k -> Type) :: k -> Type

    pruneSummands
      :: ( s ~ ReachableSummands (Pruned a l) (Pruned a r)
         , GPruning a l
         , GPruning a r
         )
      => Proxy s
      -> Proxy a
      -> (l :+: r) x
      -> PrunedSummands s (Pruned a l) (Pruned a r) x

    extendSummands
      :: ( s ~ ReachableSummands (Pruned a l) (Pruned a r)
         , GPruning a l
         , GPruning a r
         )
      => Proxy s
      -> Proxy a
      -> PrunedSummands s (Pruned a l) (Pruned a r) x
      -> (l :+: r) x



instance PruneSummands 'NoSummand where
    type PrunedSummands 'NoSummand l r = V1

    pruneSummands  _ _ = error "pruneSummands: impossible -- no summands"
    extendSummands _ _ = \case

instance PruneSummands 'LeftSummand where
    type PrunedSummands 'LeftSummand l r = l

    pruneSummands _ pa = \case
      L1 l -> gprune pa l
      _    -> error "pruneSummands: impossible -- no right summand"

    extendSummands _ pa = L1 . gextend pa

instance PruneSummands 'RightSummand where
    type PrunedSummands 'RightSummand l r = r

    pruneSummands _ pa = \case
      R1 r -> gprune pa r
      _    -> error "pruneSummands: impossible -- no left summand"

    extendSummands _ pa = R1 . gextend pa


instance PruneSummands 'BothSummands where
    type PrunedSummands 'BothSummands l r = l :+: r

    pruneSummands  _ pa = \case
      L1 l -> L1 $ gprune pa l
      R1 r -> R1 $ gprune pa r

    extendSummands _ pa = \case
      L1 pl -> L1 $ gextend pa pl
      R1 pr -> R1 $ gextend pa pr



-- ----------------------------------------------------------------------------
-- Prune GC1 values
-- ----------------------------------------------------------------------------

class PruneGC1IfNot (b :: Bool) where
  type PrunedIfNot b (a :: [Type]) (t :: k -> Type) :: k -> Type

  pruneGC1
    :: b ~ Unifies a a_gd1
    => Proxy b
    -> Proxy a_gd1
    -> GC1 a t x
    -> PrunedIfNot b a t x

  extendGC1
    :: b ~ Unifies a a_gd1
    => Proxy b
    -> Proxy a_gd1
    -> PrunedIfNot b a t x
    -> GC1 a t x

instance PruneGC1IfNot 'True where
   type PrunedIfNot 'True a t
     = GC1 a t

   pruneGC1  _ _ = id
   extendGC1 _ _ = id


instance PruneGC1IfNot 'False where
    type PrunedIfNot 'False a t
      = V1

    pruneGC1  _ _ = error "pruneGC1: impossible, types don't unify"
    extendGC1 _ _ = \case


-- ----------------------------------------------------------------------------
-- Type unification
-- ----------------------------------------------------------------------------


type Unifies (a' :: k) (a :: k)
  = Fst (Unify a' a)

type family Fst (pair :: (k, k')) :: k where
  Fst '(a, b) = a


type Unify (a' :: k) (a :: k)
  = Unify' '( 'True, '[] ) a' a

type family Unify' (state :: (Bool, [Type])) (a' :: k) (a :: k) :: (Bool , [Type]) where
  Unify' '( 'False, assign) _ _ = '( 'False, assign)
  Unify' '(_, assign) (Sk n :: k) (a :: k) = UnifyVar assign n a
  Unify' accum (f x) (f' x') = Unify' (Unify' accum f f') x x'
  Unify' accum a a = accum
  Unify' '(_, assign) _ _ = '( 'False, assign)


test_Unify_var_match
  :: Unify (Sk "n" :: Type) Int
     :~:
     '( 'True, '["n" :> Int])
test_Unify_var_match = Refl

test_Unify_nested_match
  :: Unify [Sk "n"] [Bool]
     :~:
     '( 'True, '["n" :> Bool] )
test_Unify_nested_match = Refl

test_Unify_complex_match
  :: Unify (Sk "n", Sk "m", Sk "n") (Int, Bool, Int)
     :~:
     '( 'True, '["m" :> Bool, "n" :> Int])
test_Unify_complex_match = Refl

test_Unify_no_match_var
  :: Unify (Sk "n", Sk "m", Sk "n") (Int, Bool, Bool)
     :~:
     '( 'False, '["m" :> Bool, "n" :> Int])
test_Unify_no_match_var = Refl

test_Unify_no_match_const
  :: Unify (Sk "n", Sk "m", Int) (Int, Bool, Bool)
     :~:
     '( 'False, '["m" :> Bool, "n" :> Int])
test_Unify_no_match_const = Refl

test_Unify_match_list
  :: Unify '[Sk "n", Sk "m", Sk "n"] '[Int, Bool, Int]
     :~:
     '( 'True, '["m" :> Bool, "n" :> Int])
test_Unify_match_list = Refl

-- ----------------------------------------------------------------------------
-- Variable unification
-- ----------------------------------------------------------------------------


type UnifyVar (assign :: [Type]) (n :: Symbol) (a :: k)
  = UnifyVar' assign assign n a


type family UnifyVar' (assign0 :: [Type]) (assign :: [Type]) (n :: Symbol) (a :: k) :: (Bool, [Type]) where
  UnifyVar' assign0 '[] n a = '( 'True, (n :> a ': assign0))
  UnifyVar' assign0 (n :> a ': _) n a = '( 'True, assign0)
  UnifyVar' assign0 (n :> _ ': _) n a = '( 'False, assign0)
  UnifyVar' assign0 (_ ': assign) n a = UnifyVar' assign0 assign n a

test_UnifyVar_fresh
  :: UnifyVar '["m" :> Bool] "n" Int
     :~:
     '( 'True, '["n" :> Int, "m" :> Bool])
test_UnifyVar_fresh = Refl

test_UnifyVar_twice
  :: UnifyVar '["m" :> Bool, "n" :> Int] "n" Int
  :~:
  '( 'True, '["m" :> Bool, "n" :> Int])
test_UnifyVar_twice = Refl

test_UnifyVar_no_match_var
  :: UnifyVar '["n" :> Int] "n" Bool
     :~:
     '( 'False, '["n" :> Int])
test_UnifyVar_no_match_var = Refl

