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
class GPruning (rep :: k -> Type) where
    type Pruned rep :: k -> Type

    gprune  :: rep x -> Pruned rep x
    gextend :: Pruned rep x -> rep x


instance GPruning V1 where
    type Pruned V1 = V1

    gprune  = \case
    gextend = \case

instance GPruning U1 where
    type Pruned U1 = U1

    gprune  = id
    gextend = id

instance GPruning (K1 r a) where
    type Pruned (K1 r a) = K1 r a

    gprune  = id
    gextend = id

instance GPruning (l :*: r) where
    type Pruned (l :*: r) = l :*: r

    gprune  = id
    gextend = id

instance (GPruning t, PruneM1If (Pruned t == V1)) => GPruning (M1 i c t) where
    type Pruned (M1 i c t) = PrunedM1 (Pruned t == V1) i c (Pruned t)

    gprune  = pruneM1  (Proxy :: Proxy (Pruned t == V1))
    gextend = extendM1 (Proxy :: Proxy (Pruned t == V1))

instance
  ( GPruning l
  , GPruning r
  , PruneSummands (ReachableSummands (Pruned l) (Pruned r))
  ) => GPruning (l :+: r) where
    type Pruned (l :+: r) = PrunedSummands (ReachableSummands (Pruned l) (Pruned r)) (Pruned l) (Pruned r)

    gprune  = pruneSummands  (Proxy :: Proxy (ReachableSummands (Pruned l) (Pruned r)))
    gextend = extendSummands (Proxy :: Proxy (ReachableSummands (Pruned l) (Pruned r)))

instance
  PruneGExIfNot (Unifies refined a)
    => GPruning (GEx free bound ftvars btvars refined a t) where

    type Pruned (GEx free bound ftvars btvars refined a t)
      = PrunedIfNot (Unifies refined a) free bound ftvars btvars refined a t

    gprune  = pruneGEx  (Proxy :: Proxy (Unifies refined a))
    gextend = extendGEx (Proxy :: Proxy (Unifies refined a))


-- ----------------------------------------------------------------------------
-- Prune metadata
-- ----------------------------------------------------------------------------

class PruneM1If (b :: Bool) where
  type PrunedM1  b i (c :: Meta) (rep :: k -> Type) :: k -> Type

  pruneM1
    :: ( b ~ (Pruned rep == V1)
       , GPruning rep
       )
    => Proxy b
    -> M1 i c rep x
    -> PrunedM1 b i c (Pruned rep) x

  extendM1
    :: ( b ~ (Pruned rep == V1)
       , GPruning rep
       )
    => Proxy b
    -> PrunedM1 b i c (Pruned rep) x
    -> M1 i c rep x

instance PruneM1If 'True where
    type PrunedM1 'True i c rep = V1

    pruneM1  _ (M1 rep) = case gprune rep of _ -> error "pruneM1: impossible -- V1"
    extendM1 _ = \case

instance PruneM1If 'False where
    type PrunedM1 'False i c rep = M1 i c rep

    pruneM1  _ (M1 rep)  = M1 (gprune rep)
    extendM1 _ (M1 prep) = M1 (gextend prep)


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
      :: ( s ~ ReachableSummands (Pruned l) (Pruned r)
         , GPruning l
         , GPruning r
         )
      => Proxy s
      -> (l :+: r) x
      -> PrunedSummands s (Pruned l) (Pruned r) x

    extendSummands
      :: ( s ~ ReachableSummands (Pruned l) (Pruned r)
         , GPruning l
         , GPruning r
         )
      => Proxy s
      -> PrunedSummands s (Pruned l) (Pruned r) x
      -> (l :+: r) x



instance PruneSummands 'NoSummand where
    type PrunedSummands 'NoSummand l r = V1

    pruneSummands  _ = error "pruneSummands: impossible -- no summands"
    extendSummands _ = \case

instance PruneSummands 'LeftSummand where
    type PrunedSummands 'LeftSummand l r = l

    pruneSummands _ = \case
      L1 l -> gprune l
      _    -> error "pruneSummands: impossible -- no right summand"

    extendSummands _ = L1 . gextend

instance PruneSummands 'RightSummand where
    type PrunedSummands 'RightSummand l r = r

    pruneSummands _ = \case
      R1 r -> gprune r
      _    -> error "pruneSummands: impossible -- no left summand"

    extendSummands _ = R1 . gextend


instance PruneSummands 'BothSummands where
    type PrunedSummands 'BothSummands l r = l :+: r

    pruneSummands  _ = \case
      L1 l -> L1 $ gprune l
      R1 r -> R1 $ gprune r

    extendSummands _ = \case
      L1 pl -> L1 $ gextend pl
      R1 pr -> R1 $ gextend pr



-- ----------------------------------------------------------------------------
-- Prune GEx values
-- ----------------------------------------------------------------------------

class PruneGExIfNot (b :: Bool) where
  type PrunedIfNot b
         (free    :: [Type]) (bound  :: [Type])
         (ftvars  :: [Type]) (btvars :: [Type])
         (refined :: [Type]) (a      :: [Type])
         (t :: k -> Type)
    :: k -> Type

  pruneGEx
    :: b ~ Unifies refined a
    => Proxy b
    -> GEx free bound ftvars btvars refined a t x
    -> PrunedIfNot b free bound ftvars btvars refined a t x

  extendGEx
    :: b ~ Unifies refined a
    => Proxy b
    -> PrunedIfNot b free bound ftvars btvars refined a t x
    -> GEx free bound ftvars btvars refined a t x

instance PruneGExIfNot 'True where
   type PrunedIfNot 'True free bound ftvars btvars refined a t
     = GEx free bound ftvars btvars refined a t



   pruneGEx  _ = id
   extendGEx _ = id

instance PruneGExIfNot 'False where
    type PrunedIfNot 'False free bound ftvars btvars refined a t
      = V1

    pruneGEx  _ = error "pruneGEx: impossible, types don't unify"
    extendGEx _ = \case


-- ----------------------------------------------------------------------------
-- Type unification
-- ----------------------------------------------------------------------------


type Unifies (refined :: k) (a :: k)
  = Fst (Unify refined a)

type family Fst (pair :: (k, k')) :: k where
  Fst '(a, b) = a


type Unify (refined :: k) (a :: k)
  = Unify' '( 'True, '[] ) refined a

type family Unify' (state :: (Bool, [Type])) (refined :: k) (a :: k) :: (Bool , [Type]) where
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

