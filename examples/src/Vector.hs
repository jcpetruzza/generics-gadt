{-# LANGUAGE UndecidableInstances #-}
module Vector
  ( Vector(..)
  ) where

import Data.Kind ( Type  )
import Data.Proxy

import GHC.Generics
import GHC.Generics.Exts

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
instance GSemigroup (Vector 'Z a)
instance (GSemigroup a, GSemigroup (Vector n a)) => GSemigroup (Vector ('Succ n) a)
instance GMonoid (Vector 'Z a)
instance (GMonoid a, GMonoid (Vector n a)) => GMonoid (Vector ('Succ n) a)

instance Generic (Vector n a) where
    type Rep (Vector n a)
       = D1 ('MetaData "Vector" "Vector" "package-name" 'False)
           (GD1 '[Ty n, Ty a]
             (
               (C1 ('MetaCons "VecZ" 'PrefixI 'False)
                 (GC1 '[Ty 'Z, Ty (Sk "a" :: Type)]
                   (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                     (G '["n" :> n, "a" :> a] '[] '[Ty 'Z, Ty (Sk "a" :: Type)] '[Ty n, Ty a]
                       (Sk "n" ~ 'Z :=>: U1)
                     )
                   )
                 )
               )
             :+:
               (C1 ('MetaCons "VecS" 'PrefixI 'False)
                 (GC1 '[Ty ('Succ (Sk "n'")), Ty (Sk "a" :: Type)] 
                   (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                     (G '["n" :> n, "a" :> a] '[V "n'" Peano K] '[Ty ('Succ (Sk "n'")), Ty (Sk "a" :: Type)] '[Ty n, Ty a]
                       (Sk "n" ~ 'Succ (Sk "n'") :=>:
                         (K1 R (Sk "a") :*: K1 R (Vector (Sk "n'") (Sk "a")))
                       )
                     )
                   )
                 )
               )
             )
           )

    from = \case
      VecZ
        -> M1 $ GM1 $ L1 $ M1 $ GM1 $ M1 $ QF $ Ct U1

      VecS a vn
        -> M1 $ GM1 $ R1 $ M1 $ GM1 $ M1 $
             existsG_ (unapplyR $ unapplyL $ pure vn) $ QF $ Ct $ K1 a :*: K1 vn

    to = \case
      M1 (GM1 (L1 (M1 (GM1 (M1 (QF (Ct U1))))))) -> VecZ
      M1 (GM1 (R1 (M1 (GM1 (M1 (ExG (QF (Ct (K1 a :*: K1 vn))))))))) -> VecS a vn




unapplyL :: Proxy (f a) -> Proxy f
unapplyL Proxy = Proxy

unapplyR :: Proxy (f a) -> Proxy a
unapplyR Proxy = Proxy
