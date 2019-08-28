{-# LANGUAGE UndecidableInstances #-}
module Vector
  ( Vector(..)
  ) where

import Data.Kind ( Type  )

import GHC.Generics
import GHC.Generics.Exts
import GHC.Generics.Pruning

import Generics.Deriving.Exts ()
import Generics.Deriving.Eq ( GEq(..) )
import Generics.Deriving.Monoid( GMonoid(..) )
import Generics.Deriving.Semigroup ( GSemigroup(..) )
import Generics.Deriving.Show ( GShow(..) )


data Peano
  = Z
  | Succ Peano

data Vector (n :: Peano) (a :: Type) where
    VecZ :: Vector 'Z a
    VecS :: a -> Vector n a -> Vector ('Succ n) a

-- XXX In order for this to work, we'd need to wait for UnsaturatedTypeFamilies:
-- We need a `data family`-wrapper `TF` that turns an unmatchable arrow into
-- a matchable one. So that we can write:
-- ```
-- TF (TF (+) (Sk "n")) 1
-- ```
-- This would allow us to use `SubstSk` to replace `Sk "n"`, which would
-- otherwise be under an unmatchable type-family application. Of course,
-- then we need an additional interpretation call after the `SubstSk` that
-- removes all the `TF` occurrences.
-- data Vector (n :: Nat) (a :: Type) where
--     VecZ :: Vector 0 a
--     VecS :: a -> Vector n a -> Vector (n + 1) a

instance GShow a => GShow (Vector n a)
instance GEq a => GEq (Vector n a)

deriving via (Pruning (Vector 'Z a))
  instance GSemigroup (Vector 'Z a)

deriving via (Pruning (Vector ('Succ n) a))
  instance (GSemigroup a, GSemigroup (Vector n a)) => GSemigroup (Vector ('Succ n) a)

deriving via (Pruning (Vector 'Z a))
  instance GMonoid (Vector 'Z a)
deriving via (Pruning (Vector ('Succ n) a))
  instance (GMonoid a, GMonoid (Vector n a)) => GMonoid (Vector ('Succ n) a)

instance Generic (Vector n a) where
    type Rep (Vector n a)
       = D1 ('MetaData "Vector" "Vector" "package-name" 'False)
           (
             (C1 ('MetaCons "VecZ" 'PrefixI 'False)
               (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                 (Let a (Let n (Match Type (Exact 'Z) n QF)) 'Grnd
                     ((Var 1 ~ 'Z) :=>: U1)
                 )
               )
             )
           :+:
             (C1 ('MetaCons "VecS" 'PrefixI 'False)
               (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                 (Let a (Let n (Match Peano ('Succ (Pat PVar)) n QF)) 'Grnd
                   (Var 1 ~ 'Succ (Var 0) :=>:
                     (K1 R (Var 2) :*: K1 R (Vector (Var 0) (Var 2)))
                   )
                 )
               )
             )
           )

    from = \case
      VecZ
        -> M1 $ L1 $ M1 $ M1 $ Let $ Let $ Match $ Let $ QF $ Ct U1

      VecS a vn
        -> M1 $ R1 $ M1 $ M1 $
             Let $ Let $ Match $ Let $ QF $ Ct $ K1 a :*: K1 vn


    to = \case
      M1 (L1 (M1 (M1 (Let (Let (Match (Let (QF (Ct U1))))))))) -> VecZ
      M1 (R1 (M1 (M1 (Let (Let (Match (Let (QF (Ct (K1 a :*: K1 vn)))))))))) -> VecS a vn
