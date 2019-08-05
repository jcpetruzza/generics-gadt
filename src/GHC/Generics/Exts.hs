{-# LANGUAGE UndecidableInstances #-}
module GHC.Generics.Exts
  ( (:=>:)(..)
  , QF(..), Ex(..), Let(..), Match(..)
  , Var, Subst
  , Assgns(..)
  , Matching(..)
  , DoMatch, TryMatch
  , Matching.Pat, Matching.PVar, Matching.PAny, Matching.Exact
 )
where

import Data.Kind ( Constraint, Type )
import GHC.TypeLits ( Nat, type (-), TypeError, ErrorMessage(..) )

import qualified GHC.Generics.Matching as Matching

-- | A de-Bruijn style variable of kind @k@.
data family Var :: Nat -> k

-- | Constraints, typically used together with existential types.
data (:=>:) (c :: Constraint) t x where
  Ct :: c => { unCt :: t x } -> (:=>:) c t x
infixr 4 :=>:


-- | Substitution of variables by types.
type family Subst (free :: Assgns) (t :: kt) :: kt where
  Subst 'Grnd t = t
  Subst ('Assgn (a :: k) _) (Var 0 :: k)  = a
  Subst ('Assgn (_ :: k) _) (Var 0 :: k') = Var 0
  Subst ('Assgn _ as) (Var n) = Subst as (Var (n - 1))
  Subst as (f x) = (Subst as f) (Subst as x)
  Subst as t = t


-- | A quantifier-free existential type.
newtype QF (free :: Assgns) (t :: k -> Type) (x :: k) where
  QF :: { unQF :: Subst free t x } -> QF free t x

-- | An existential type.
data Ex k sf (free :: Assgns) t x where
  Ex :: Let (a :: k) sf free t x -> Ex k sf free t x

-- | Like )an existential, a 'Let' introduces a new type-variable,
--   but unlike the former, bound to a type that is statically known.
newtype Let a sf (free :: Assgns) (t :: k -> Type) (x :: k) where
  Let :: { unLet :: sf ('Assgn a free) t x } -> Let a sf free t x

-- | Similar to a 'Let' but the actual type is obtained by matching
--   the given pattern on @a@, as is done on a GADT. Pattern matching
--   can fail (unreachable constructor), in which case we get a type
--   isomorphic to 'V1'.
data Match km pat a sf (free :: Assgns) t x where
  Match
    :: (ma :: km) ~ DoMatch km pat a
    => Let ma sf free t x
    -> Match km pat a sf free t x

type family DoMatch k (pat :: kpat) (a :: ka) :: k where
  DoMatch k (pat :: kpat) (a :: ka) = CaseDoMatch k (TryMatch k pat a)

type family CaseDoMatch k (m :: Matching k) :: k where
  CaseDoMatch k ('Captured a) = a


data Matching (a :: k) where
  Captured  :: a -> Matching a
  MatchFail :: Matching a

type TryMatch k (pat :: kpat) (a :: ka)
  = CaseTryMatch k (Matching.TryMatch k kpat ka pat a)

type family CaseTryMatch k (m :: Matching.Matching k) where
  CaseTryMatch k 'Matching.MatchFail = 'MatchFail
  CaseTryMatch k ('Matching.Captured (a :: k)) = 'Captured a
  CaseTryMatch _  'Matching.Matched = TypeError ('Text "Pattern didn't capture anything")

data Assgns where
  Grnd  :: Assgns
  Assgn :: k -> Assgns -> Assgns

