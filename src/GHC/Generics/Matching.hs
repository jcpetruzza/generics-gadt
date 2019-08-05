{-# LANGUAGE UndecidableInstances #-}
module GHC.Generics.Matching
  ( Matching(..)
  , TryMatch
  , Pat
  , MatchPat(..)
  , PVar, PAny
  , Exact
  ) where

import Data.Kind ( Type )
import Data.Type.Bool( If )
import Data.Type.Equality ( type (:~:)(..), type (==) )
import GHC.TypeLits ( TypeError, ErrorMessage(..) )

data Matching (a :: k) where
  Captured  :: a -> Matching a
  Matched   :: Matching a
  MatchFail :: Matching a


-- | Match a type of kind @km@ occurring in @a@ following the given @pat@.
type family TryMatch km kpat ka (pat :: kpat) (a :: ka) :: Matching km where
  TryMatch Type ka ka (Exact pat) a
    = If (TryMatch ka ka ka pat a == 'Matched) ('Captured ()) 'MatchFail

  TryMatch km kpat ka (Pat pat) a
    = TryMatchPat pat km a

  TryMatch km kpat ka (f (x :: kx)) (g (y :: ky))
    = TryMatch km (kx -> kpat) (ky -> ka) f g /\ TryMatch km kx ky x y

  TryMatch _ ka ka a a
    = 'Matched

  TryMatch _ _ _ _ _  -- wrong kind or type
    = 'MatchFail


type family (/\) (l :: Matching a) (r :: Matching a) :: Matching a where
  'MatchFail /\ _ = 'MatchFail
  _ /\ 'MatchFail = 'MatchFail

  'Matched /\ r = r
  l /\ 'Matched = l

  'Captured a /\ 'Captured a = 'Captured a
  'Captured a /\ 'Captured b = 'MatchFail

data family Exact (pat :: k) :: k


-- | A pattern to match types
data family Pat (pat :: k) :: k

class MatchPat (pat :: kpat) where
  type TryMatchPat pat km (a :: ka) :: Matching km


-- | Variable to match in a pattern
data family PVar :: k

instance MatchPat (PVar :: kv) where
  type TryMatchPat (PVar :: kv) km (a :: ka)
    = TryMatchPVar kv km a

type family TryMatchPVar kv km (a :: ka) :: Matching km where
  TryMatchPVar km km (a :: km) = 'Captured a
  TryMatchPVar km km (a :: ka) = 'MatchFail
  TryMatchPVar _  _  _ = TypeError ('Text "PVar has the wrong kind")

-- | A pattern that matches anything
data family PAny :: k

instance MatchPat (PAny :: k) where
  type TryMatchPat (PAny :: k) _ (a :: ka)
    = TryMatchPAny k a

type family TryMatchPAny k (a :: ka) :: Matching km where
  TryMatchPAny k (_ :: k) = 'Matched
  TryMatchPAny k (a :: ka) = 'MatchFail


-- ----------------------------------------------------------------------------
-- Test cases
-- ----------------------------------------------------------------------------

-- PVar
_testMatchPVar
  :: TryMatch
       (Type -> Type)
       (Type -> Type)
       (Type -> Type)
       (Pat PVar)
       Maybe
     :~:
     'Captured Maybe
_testMatchPVar = Refl

_testMatchPVarFail
  :: TryMatch
       Type
       Type
       (Type -> Type)
       (Pat PVar)
       Maybe
     :~:
     'MatchFail
_testMatchPVarFail = Refl


-- PAny
_testMatchPAny
  :: TryMatch
       Type
       Type
       Type
       (Pat PAny)
       [Int]
     :~:
     'Matched
_testMatchPAny = Refl

_testMatchPAnyFail
  :: TryMatch
       Type
       Type
       (Type -> Type)
       (Pat PAny)
       Maybe
     :~:
     'MatchFail
_testMatchPAnyFail = Refl


-- Match constant
_testMatchConst
  :: TryMatch
       (Type -> Type)
       (Type -> Type)
       (Type -> Type)
       Maybe
       Maybe
     :~:
     'Matched
_testMatchConst
  = Refl

_testMatchConstFail
  :: TryMatch
       (Type -> Type)
       (Type -> Type)
       (Type -> Type)
       Maybe
       []
     :~:
     'MatchFail
_testMatchConstFail
  = Refl

_testMatchConstFailKind
  :: TryMatch
       (Type -> Type)
       (Type -> Type)
       Type
       Maybe
       Int
     :~:
     'MatchFail
_testMatchConstFailKind
  = Refl


-- Match compound expression
_testMatchCompound
  :: TryMatch
       Type
       Type
       Type
       ((,) Bool (Pat PVar))
       ((,) Bool Int)
     :~:
     ('Captured Int)
_testMatchCompound
  = Refl


_testMatchCompoundFail
  :: TryMatch
       Type
       Type
       Type
       ((,) Bool (Pat PVar))
       ((,) Int Int)
     :~:
     'MatchFail
_testMatchCompoundFail
  = Refl
