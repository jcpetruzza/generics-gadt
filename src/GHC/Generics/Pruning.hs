{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE QuantifiedConstraints #-}
{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module GHC.Generics.Pruning
  ( Prunable (..), Extendable (..)
  , prune
  , Pruning (..)
  )
  where

import Data.Kind ( Type )
import Data.Proxy( Proxy(..) )
import Data.Type.Equality ( type (==) )

import GHC.Generics
import GHC.Generics.Exts

-- ----------------------------------------------------------------------------
-- Pruning adapter
-- ----------------------------------------------------------------------------

-- | A newtype wrapper to provide alternative generic instances via
--   generic representation pruning. This way, one can opt-in to these
--   versions using the @DerivingVia@ extension.
newtype Pruning a
  = Pruning { unPruning :: a }


-- ----------------------------------------------------------------------------
-- Pruning
-- ----------------------------------------------------------------------------

-- | Pruning of unreachable summands from a Generic representation.
--   This makes special sense when working with GADTs, since knowing a specific
--   type may make summands impossible to pattern match.
class
  Prunable (rep :: k -> Type)
  where
    type Pruned rep :: k -> Type
    pruning  :: (Pruned rep x -> r) -> rep x -> r

prune :: (Prunable rep) => rep x -> Pruned rep x
prune = pruning id

class
   ( Prunable rep
   )
  => Extendable rep
  where
    extend :: Pruned rep x -> rep x


instance
  Prunable V1
  where
    type Pruned V1 = V1
    pruning _ = \case

instance
  Extendable V1
  where
    extend = \case


instance
  Prunable U1
  where
    type Pruned U1 = U1
    pruning f = f

instance
  Extendable U1
  where
    extend = id


instance
  Prunable (K1 r a)
  where
    type Pruned (K1 r a) = K1 r a
    pruning f  = f

instance
  Extendable (K1 r a)
  where
    extend = id


instance
   ( PruneQFIf b free t
   , b ~ (Subst free t == V1)
   )
  => Prunable (QF free t)
  where
    type Pruned (QF free t) = PrunedQFIf (Subst free t == V1) free t
    pruning = pruningQFIf (Proxy @b)

instance
   ( ExtendQFIf b free t
   , b ~ (Subst free t == V1)
   )
  => Extendable (QF free t)
  where
    extend = extendQFIf (Proxy @b)


instance
   ( PruneLetIf b a sf free t
   , b ~ (Pruned (sf ('Assgn a free) t) == V1)
   )
  => Prunable (Let a sf free t)
  where
    type Pruned (Let a sf free t)
      = PrunedLetIf (Pruned (sf ('Assgn a free) t) == V1) a sf free t
    pruning
      = pruningLetIf (Proxy @b)

instance
   ( ExtendLetIf b a sf free t
   , b ~ (Pruned (sf ('Assgn a free) t) == V1)
   )
  => Extendable (Let a sf free t)
  where
    extend = extendLetIf (Proxy @b)


instance
   ( PruneExIf b ka sf free t
   , b ~ (Pruned (sf ('Assgn (Sk free ka) free) t) == V1)
   )
  => Prunable (Ex ka sf free t)
  where
    type Pruned (Ex ka sf free t)
      = PrunedExIf (Pruned (sf ('Assgn (Sk free ka) free) t) == V1) ka sf free t
    pruning
      = pruningExIf (Proxy @b)

instance
   ( ExtendExIf b ka sf free t
   , b ~ (Pruned (sf ('Assgn (Sk free ka) free) t) == V1)
   )
  => Extendable (Ex ka sf free t)
  where
    extend = extendExIf (Proxy @b)


instance
   ( PruneMatch m pat a sf free t
   , (m :: Matching km) ~ TryMatch km pat a
   )
  => Prunable (Match km pat a sf free t)
  where
    type Pruned (Match km pat a sf free t)
      = PrunedMatch (TryMatch km pat a :: Matching km) pat a sf free t
    pruning = pruningMatch (Proxy @m)


instance
   ( ExtendMatch m pat a sf free t
   , (m :: Matching km) ~ TryMatch km pat a
   )
  => Extendable (Match km (pat :: kpat) (a :: ka) sf free t)
  where
    extend = extendMatch (Proxy @m)

instance
   ( PruneIf b ((:=>:) c) t
   , b ~ (Pruned t == V1)
   )
  => Prunable (c :=>: t)
  where
    type Pruned (c :=>: t) = PrunedIf (Pruned t == V1) ((:=>:) c) t
    pruning f ct@Ct{} = pruningIf (Proxy @b) Ct unCt f ct

instance
   ( ExtendIfNot b((:=>:) c) t
   , b ~ (Pruned t == V1)
   , c
   )
  => Extendable (c :=>: t)
  where
    extend = extendIfNot (Proxy @b) Ct unCt


instance
   ( PruneIf b (M1 i c) t
   , b ~ (Pruned t == V1)
   )
  => Prunable (M1 i c t)
  where
    type Pruned (M1 i c t) = PrunedIf (Pruned t == V1) (M1 i c) t
    pruning  = pruningIf (Proxy @b) M1 unM1

instance
   ( ExtendIfNot b (M1 i c) t
   , b ~ (Pruned t == V1)
   )
  => Extendable (M1 i c t)
  where
    extend = extendIfNot (Proxy @b) M1 unM1


instance
   ( Prunable l
   , Prunable r
   , PruneSum loc l r
   , loc ~ GetBinOpV1Loc (Pruned l) (Pruned r)
   )
  => Prunable (l :+: r) where
    type Pruned (l :+: r) = PrunedSum (GetBinOpV1Loc (Pruned l) (Pruned r)) l r
    pruning = pruningSum (Proxy @loc)

instance
   ( Extendable l
   , Extendable r
   , ExtendSum loc l r
   , loc ~ GetBinOpV1Loc (Pruned l) (Pruned r)
   )
  => Extendable (l :+: r)
  where
    extend = extendSum (Proxy @loc)


instance
   ( Prunable l
   , Prunable r
   , PruneProd loc l r
   , loc ~ GetBinOpV1Loc (Pruned l) (Pruned r)
   )
  => Prunable (l :*: r) where
    type Pruned (l :*: r) = PrunedProd (GetBinOpV1Loc (Pruned l) (Pruned r)) l r
    pruning = pruningProd (Proxy @loc)

instance
   ( Extendable l
   , Extendable r
   , ExtendProd loc l r
   , loc ~ GetBinOpV1Loc (Pruned l) (Pruned r)
   )
  => Extendable (l :*: r)
  where
    extend = extendProd (Proxy @loc)


-- ----------------------------------------------------------------------------
-- Being absurd
-- ----------------------------------------------------------------------------

absurd1 :: V1 x -> a
absurd1 = \case


-- ----------------------------------------------------------------------------
-- Prune wrapper types
-- ----------------------------------------------------------------------------

class
   ( Prunable rep
   )
  => PruneIf
       (b :: Bool)
       (wrapper :: (k -> Type) -> k -> Type)
       (rep :: k -> Type)
  where
  type PrunedIf b wrapper rep :: k -> Type

  pruningIf
    :: Proxy b
    -> (Pruned rep x -> wrapper (Pruned rep) x)
    -> (wrapper rep x -> rep x)
    -> (PrunedIf b wrapper rep x -> r)
    -> wrapper rep x
    -> r

instance
   ( Prunable rep
   , Pruned rep ~ V1
   )
  => PruneIf 'True wrapper rep
  where
    type PrunedIf 'True wrapper rep = V1
    pruningIf  _ _ unwrap _ wrappedRep = absurd1 (prune $ unwrap wrappedRep)

instance
   ( Prunable rep
   )
  => PruneIf 'False wrapper rep
  where
    type PrunedIf 'False wrapper rep = wrapper (Pruned rep)
    pruningIf  _ wrap unwrap f wrappedRep = pruning (f . wrap) $ unwrap wrappedRep


class
   ( PruneIf b wrapper rep
   , Extendable rep
   )
  => ExtendIfNot b wrapper rep
  where
    extendIfNot
      :: Proxy b
      -> (rep x -> wrapper rep x)
      -> (wrapper (Pruned rep) x -> Pruned rep x)
      -> PrunedIf b wrapper rep x
      -> wrapper rep x

instance
   ( Extendable rep
   , Pruned rep ~ V1
   )
  => ExtendIfNot 'True wrapper rep
  where
    extendIfNot _ _ _ = \case

instance
   ( Extendable rep
   )
  => ExtendIfNot 'False wrapper rep
  where
    extendIfNot _ wrap unwrap wrappedPrunedRep = wrap $ extend $ unwrap wrappedPrunedRep

-- ----------------------------------------------------------------------------
-- Prune QF values
-- ----------------------------------------------------------------------------

class
  PruneQFIf (b :: Bool) (free :: Assgns) (t :: k -> Type)
  where
    type PrunedQFIf b free t :: k -> Type

    pruningQFIf
      :: Proxy b
      -> (PrunedQFIf b free t x -> r)
      -> QF free t x
      -> r

instance
   ( Subst free t ~ V1
   )
  => PruneQFIf 'True free t
  where
   type PrunedQFIf 'True free t = V1
   pruningQFIf _ f = f . unQF

instance
  PruneQFIf 'False free t
  where
    type PrunedQFIf 'False free t = QF free t
    pruningQFIf _ f = f

class
   ( PruneQFIf b free t
   )
  => ExtendQFIf b free t
  where
    extendQFIf
      :: Proxy b
      -> PrunedQFIf b free t x
      -> QF free t x

instance
   ( Subst free t ~ V1
   )
  => ExtendQFIf 'True free t
  where
    extendQFIf _ = \case

instance
  ExtendQFIf 'False free t
  where
    extendQFIf _ = id


-- ----------------------------------------------------------------------------
-- Prune Let types
-- ----------------------------------------------------------------------------

class
  PruneLetIf
     (b :: Bool)
     (a :: ka)
     (sf :: Assgns -> (k -> Type) -> k -> Type)
     (free :: Assgns)
     (t :: k -> Type)
  where
    type PrunedLetIf b a sf free t :: k -> Type

    pruningLetIf
      :: Proxy b
      -> (PrunedLetIf b a sf free t x -> r)
      -> Let a sf free t x
      -> r

instance
   ( Prunable (sf ('Assgn a free) t)
   , Pruned (sf ('Assgn a free) t) ~ V1
   )
  => PruneLetIf 'True a sf free t
  where
    type PrunedLetIf 'True a sf free t = V1
    pruningLetIf _ _ (Let ta) = absurd1 (prune ta)

instance
  PruneLetIf 'False a sf free t
  where
    type PrunedLetIf 'False a sf free t = Let a sf free t
    pruningLetIf _ f = f


class
   ( PruneLetIf b a sf free t
   )
  => ExtendLetIf b a sf free t
  where
    extendLetIf
      :: Proxy b
      -> PrunedLetIf b a sf free t x
      -> Let a sf free t x

instance
   ( Prunable (sf ('Assgn a free) t)
   , Pruned (sf ('Assgn a free) t) ~ V1
   )
  => ExtendLetIf 'True a sf free t
  where
    extendLetIf _ = \case

instance
  ExtendLetIf 'False a sf free t
  where
    extendLetIf _ = id



-- ----------------------------------------------------------------------------
-- Prune existential types
-- ----------------------------------------------------------------------------

-- | Skolem term to be introduced during skolemization of a variable of kind @k@.
data family Sk :: a -> k -> k

class
   PruneExIf
     (b :: Bool)
     ka
     (sf :: Assgns -> (k -> Type) -> k -> Type)
     (free :: Assgns)
     (t :: k -> Type)
  where
    type PrunedExIf b ka sf free t :: k -> Type

    pruningExIf
      :: b ~ (Pruned (sf ('Assgn (Sk free ka) free) t) == V1)
      => Proxy b
      -> (PrunedExIf b ka sf free t x -> r)
      -> Ex ka sf free t x
      -> r

instance
   ( (forall (a :: ka). PruneLetIf 'True a sf free t)
   )
  => PruneExIf 'True ka sf free t
  where
    type PrunedExIf 'True ka sf free t = V1
    pruningExIf pt f = letEx (pruningLetIf pt f)

instance
  PruneExIf 'False ka sf free t
  where
    type PrunedExIf 'False ka sf free t = Ex ka sf free t
    pruningExIf _ f = f


class
   ( PruneExIf b ka sf free t
   )
  => ExtendExIf b ka sf free t
  where
    extendExIf
      :: Proxy b
      -> PrunedExIf b ka sf free t x
      -> Ex ka sf free t x

instance
   ( (forall (a :: ka). PruneLetIf 'True a sf free t)
   )
  => ExtendExIf 'True ka sf free t
  where
    extendExIf _ = \case

instance
  ExtendExIf 'False ka sf free t
  where
    extendExIf _ = id


letEx
  :: (forall (a :: ka). Let a sf free t x -> r)
  -> Ex ka sf free t x
  -> r
letEx f (Ex lta) = f lta


-- ----------------------------------------------------------------------------
-- Prune matchings
-- ----------------------------------------------------------------------------

class
  PruneMatch
     (m :: Matching km)
     pat
     a
     (sf :: Assgns -> (k -> Type) -> k -> Type)
     (free :: Assgns)
     (t :: k -> Type)
  where
    type PrunedMatch m pat a sf free t :: k -> Type

    pruningMatch
      :: Proxy m
      -> (PrunedMatch m pat a sf free t x -> r)
      -> Match km pat a sf free t x
      -> r

instance
   ( ('MatchFail :: Matching km) ~ TryMatch km pat a
   )
  => PruneMatch ('MatchFail :: Matching km) (pat :: kpat) (a :: ka) sf free t
  where
    type PrunedMatch 'MatchFail pat a sf free t = V1
    pruningMatch _ _ _match
      = error "PruneMatch: impossible"
          -- Can we prove it from the types?
          -- I think not, since this would require ghc to use that `DoMatch km pat a`
          -- is not stuck.

instance
   ( 'Captured (ma :: km) ~ TryMatch km pat a
   , PruneMatchedIf b ma pat a sf free t
   , b ~ (Pruned (sf ('Assgn ma free) t) == V1)
   )
  => PruneMatch (('Captured ma) :: Matching km) pat a sf free t
  where
    type PrunedMatch ('Captured (ma :: km)) pat a sf free t
      = PrunedMatchedIf (Pruned (sf ('Assgn ma free) t) == V1) (ma :: km) pat a sf free t

    pruningMatch _ f mlta@Match{}
      = pruningMatchedIf @_ @ma (Proxy @b) f mlta

class
  PruneMatchedIf
     (b :: Bool)
     (ma :: km)
     pat
     (a :: ka)
     (sf :: Assgns -> (k -> Type) -> k -> Type)
     (free :: Assgns)
     (t :: k -> Type)
  where
    type PrunedMatchedIf b (ma :: km) pat a sf free t :: k -> Type

    pruningMatchedIf
      :: Proxy b
      -> (PrunedMatchedIf b (ma :: km) pat a sf free t x -> r)
      -> Match km pat a sf free t x
      -> r


instance
   ( PruneLetIf 'True ma sf free t
   , ma ~ (DoMatch km pat a)
   )
  => PruneMatchedIf 'True (ma :: km) pat a sf free t
  where
    type PrunedMatchedIf 'True (ma :: km) pat a sf free t = V1
    pruningMatchedIf pt f = letMatch (pruningLetIf pt f)

instance
  PruneMatchedIf 'False (ma :: km) pat a sf free t
  where
    type PrunedMatchedIf 'False (ma :: km) pat a sf free t = Match km pat a sf free t
    pruningMatchedIf _ f = f


letMatch
  :: ma ~ DoMatch km pat a
  => (Let ma sf free t x -> r)
  -> Match km pat a sf free t x
  -> r
letMatch f (Match lta) = f lta

class
   ( PruneMatch m pat a sf free t
   )
  => ExtendMatch (m :: Matching km) pat a sf free t
  where
    extendMatch
      :: Proxy m
      -> PrunedMatch m pat a sf free t x
      -> Match km pat a sf free t x

instance
   ( ('MatchFail :: Matching km) ~ TryMatch km pat a
   )
  => ExtendMatch ('MatchFail :: Matching km) pat a sf free t
  where
    extendMatch _ = \case

instance
   ( 'Captured (ma :: km) ~ TryMatch km pat a
   , ExtendMatchedIf b ma pat a sf free t
   , b ~ (Pruned (sf ('Assgn ma free) t) == V1)
   )
  => ExtendMatch (('Captured ma) :: Matching km) pat a sf free t
  where
    extendMatch _ = extendMatchedIf @_ @ma (Proxy @b)

class
   ( PruneMatchedIf b ma pat a sf free t
   )
  => ExtendMatchedIf b (ma :: km) pat (a :: ka) sf free (t :: k -> Type)
  where
    extendMatchedIf
      :: Proxy b
      -> PrunedMatchedIf b ma pat a sf free t x
      -> Match km pat a sf free t x

instance
   ( ma ~ DoMatch km pat a
   , Prunable (sf ('Assgn ma free) t)
   , Pruned (sf ('Assgn ma free) t) ~ V1
   )
  => ExtendMatchedIf 'True (ma :: km) pat a sf free t
  where
    extendMatchedIf _ = \case

instance
  ExtendMatchedIf 'False (ma :: km) pat a sf free t
  where
    extendMatchedIf _ = id

-- ----------------------------------------------------------------------------
-- Product and sum support
-- ----------------------------------------------------------------------------

data BinOpV1Loc
  = V1OnLeftOnly
  | V1OnRightOnly
  | V1OnBoth
  | V1OnNone


type family GetBinOpV1Loc (repl :: k -> Type) (repr :: k -> Type) :: BinOpV1Loc where
  GetBinOpV1Loc V1 V1 = 'V1OnBoth
  GetBinOpV1Loc V1 _  = 'V1OnLeftOnly
  GetBinOpV1Loc  _ V1 = 'V1OnRightOnly
  GetBinOpV1Loc  _ _  = 'V1OnNone


-- ----------------------------------------------------------------------------
-- Prune sums
-- ----------------------------------------------------------------------------

class
   ( Prunable l
   , Prunable r
   )
  => PruneSum (loc :: BinOpV1Loc) (l :: k -> Type) (r :: k -> Type) where
    type PrunedSum loc l r :: k -> Type

    pruningSum
      :: Proxy loc
      -> (PrunedSum loc l r x -> result)
      -> (l :+: r) x
      -> result

instance
   ( Prunable l
   , Prunable r
   , Pruned l ~ V1
   , Pruned r ~ V1
   )
  => PruneSum 'V1OnBoth l r
  where
    type PrunedSum 'V1OnBoth l r = V1
    pruningSum _ f = \case
      L1 l -> pruning f l
      R1 r -> pruning f r

instance
   ( Prunable l
   , Prunable r
   , Pruned l ~ V1
   )
  => PruneSum 'V1OnLeftOnly l r
  where
    type PrunedSum 'V1OnLeftOnly l r = Pruned r
    pruningSum _ f = \case
      L1 l -> absurd1 (prune l)
      R1 r -> pruning f r

instance
   ( Prunable l
   , Prunable r
   , Pruned r ~ V1
   )
  => PruneSum 'V1OnRightOnly l r
  where
    type PrunedSum 'V1OnRightOnly l r = Pruned l
    pruningSum _ f = \case
      L1 l -> pruning f l
      R1 r -> absurd1 (prune r)

instance
   ( Prunable l
   , Prunable r
   )
  => PruneSum 'V1OnNone l r
  where
    type PrunedSum 'V1OnNone l r = (Pruned l) :+: (Pruned r)
    pruningSum _ f = \case
      L1 l -> pruning (f . L1) l
      R1 r -> pruning (f . R1) r


class
   ( PruneSum loc l r
   )
  => ExtendSum loc l r
  where
    extendSum
      :: Proxy loc
      -> PrunedSum loc l r x
      -> (l :+: r) x

instance
   ( Extendable l
   , Extendable r
   , Pruned l ~ V1
   , Pruned r ~ V1
   )
  => ExtendSum 'V1OnBoth l r
  where
    extendSum _ = \case

instance
   ( Extendable l
   , Extendable r
   , Pruned l ~ V1
   )
  => ExtendSum 'V1OnLeftOnly l r
  where
    extendSum _ =  R1 . extend

instance
   ( Extendable l
   , Extendable r
   , Pruned r ~ V1
   )
  => ExtendSum 'V1OnRightOnly l r
  where
    extendSum _ =  L1 . extend

instance
   ( Extendable l
   , Extendable r
   )
  => ExtendSum 'V1OnNone l r
  where
    extendSum _ = \case
      L1 l -> L1 (extend l)
      R1 r -> R1 (extend r)


-- ----------------------------------------------------------------------------
-- Prune products
-- ----------------------------------------------------------------------------

class
   ( Prunable l
   , Prunable r
   )
  => PruneProd (loc :: BinOpV1Loc) (l :: k -> Type) (r :: k -> Type) where
    type PrunedProd loc l r :: k -> Type

    pruningProd
      :: Proxy loc
      -> (PrunedProd loc l r x -> result)
      -> (l :*: r) x
      -> result

instance
   ( Prunable l
   , Prunable r
   , Pruned l ~ V1
   , Pruned r ~ V1
   )
  => PruneProd 'V1OnBoth l r
  where
    type PrunedProd 'V1OnBoth l r = V1
    pruningProd _ _ (l :*: _) = absurd1 (prune l)

instance
   ( Prunable l
   , Prunable r
   , Pruned l ~ V1
   )
  => PruneProd 'V1OnLeftOnly l r
  where
    type PrunedProd 'V1OnLeftOnly l r = V1
    pruningProd _ _ (l :*: _) = absurd1 (prune l)

instance
   ( Prunable l
   , Prunable r
   , Pruned r ~ V1
   )
  => PruneProd 'V1OnRightOnly l r
  where
    type PrunedProd 'V1OnRightOnly l r = V1
    pruningProd _ _ (_ :*: r) = absurd1 (prune r)

instance
   ( Prunable l
   , Prunable r
   )
  => PruneProd 'V1OnNone l r
  where
    type PrunedProd 'V1OnNone l r = l :*: r
    pruningProd _ f = f


class
   ( PruneProd loc l r
   )
  => ExtendProd loc l r
  where
    extendProd
      :: Proxy loc
      -> PrunedProd loc l r x
      -> (l :*: r) x

instance
   ( Extendable l
   , Extendable r
   , Pruned l ~ V1
   , Pruned r ~ V1
   )
  => ExtendProd 'V1OnBoth l r
  where
    extendProd _ = \case

instance
   ( Extendable l
   , Extendable r
   , Pruned l ~ V1
   )
  => ExtendProd 'V1OnLeftOnly l r
  where
    extendProd _ = \case

instance
   ( Extendable l
   , Extendable r
   , Pruned r ~ V1
   )
  => ExtendProd 'V1OnRightOnly l r
  where
    extendProd _ = \case

instance
   ( Extendable l
   , Extendable r
   )
  => ExtendProd 'V1OnNone l r
  where
    extendProd _ (l :*: r) = (l :*: r)
