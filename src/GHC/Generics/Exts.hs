{-# LANGUAGE UndecidableInstances #-}
module GHC.Generics.Exts
  ( (:=>:)(..)
  , GM1(..), GD1, GC1
  , QF(..), Let(..), Ex(..)
  , (:>)
  , Sk, SubstSk
  , Ty
  , Sel, Hp, Lp, Rp, Subp
 )

where

import Data.Kind ( Constraint, Type )
import GHC.Generics ( C, D )
import GHC.TypeLits ( Nat, Symbol, type (-) )


-- | A /Skolem constant/ of kind @k@, used to remove
--   universally quantified variables of kind @k@ from types.
data family Sk :: Symbol -> k

-- | Type-level proxy
data Ty (t :: k)

-- | Constraints, typically used together with existential types.
data (:=>:) (c :: Constraint) t x where
  Ct :: c => t x -> (:=>:) c t x
infixr 4 :=>: 

data (:>) (n :: Symbol) (t :: k)

-- | Substitution of a Skolem constants by types.
type family SubstSk (as :: [Type]) (t :: kt) :: kt where
    SubstSk '[] t = t
    SubstSk (n :> (a :: k) ': _) (Sk n :: k) = a
    SubstSk (_ :> _ ': as) (Sk n) = SubstSk as (Sk n)
    SubstSk as (f x) = (SubstSk as f) (SubstSk as x)
    SubstSk as ts = SubstSkInList as ts
    SubstSk as t = t

type family SubstSkInList (as :: [Type]) (ts :: [kt]) where
  SubstSkInList as '[] = '[]
  SubstSkInList as (t ': ts) = SubstSk as t ': SubstSkInList as ts

-- | Meta-information about GADT type-arguments (both on type and on constructors)
newtype GM1 (i :: Type) (c :: [Type]) (f :: k -> Type) (p :: k)
  = GM1 { unGM1 :: f p }
  deriving (Read, Show, Eq, Ord) -- XXX missing instances

-- | Type synonym for enconding meta-information about a GADT type arguments
type GD1 = GM1 D

-- | Type synonym for enconding meta-information about a GADT constructor type arguments
type GC1 = GM1 C

-- | A quantifier-free existential type.
newtype QF (free :: [Type]) (t :: k -> Type) (x :: k)
  = QF { unQF :: SubstSk free t x }

-- | A type-level let expression, as used in GADTs.
newtype Let n (vn :: kvn) sf (free :: [Type]) t x
  = Let { unLet :: sf (n :> vn ': free) t x }

-- | An existential type.
data Ex n kvn sf (free :: [Type]) t x where
  Ex :: sf (n :> (vn :: kvn) ': free) t x -> Ex n kvn sf free t x


-- | Select a type occurring in @a@ following the given @path@.
type family Sel k (path :: Type) (a :: ka) :: k

-- | Path ends "Here"
data Hp

-- | Make a "Left" turn
data Lp path

-- | Make a "Right" turn
data Rp path

-- | "Subtract" @n@
data Subp (n :: Nat)

type instance Sel k Hp (a :: k) = a
type instance Sel k (Lp path) (f _) = Sel k path f
type instance Sel k (Rp path) (_ x) = Sel k path x
type instance Sel Nat (Subp n) m = m - n
