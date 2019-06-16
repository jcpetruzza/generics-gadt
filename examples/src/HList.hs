{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
module HList
  ( HList(..)
  , updateCt
  , All
  ) where

import Data.Kind ( Constraint, Type )
import Data.Proxy ( Proxy(..)  )

import Generics.Deriving.Exts ()
import Generics.Deriving.Eq ( GEq(..) )
import Generics.Deriving.Monoid( GMonoid(..) )
import Generics.Deriving.Semigroup ( GSemigroup(..) )
import Generics.Deriving.Show ( GShow(..) )

import GHC.Generics
import GHC.Generics.Exts


data HList c a where
  HNil :: HList c '[]
  HCons :: c t => t -> HList c ts -> HList c (t ': ts)

instance GShow (HList GShow a)
instance GEq (HList GEq a)
instance GSemigroup (HList c '[])
instance GSemigroup (HList GSemigroup as) => GSemigroup (HList GSemigroup (a ': as))
instance GMonoid (HList c '[])
instance (GMonoid a, GMonoid (HList GMonoid as)) => GMonoid (HList GMonoid (a ': as))

type family All (c :: Type -> Constraint) (as :: [Type]) :: Constraint where
    All c '[] = ()
    All c (a ': as) = (c a, All c as)

updateCt :: All c as => HList d as -> HList c as
updateCt = \case
  HNil -> HNil
  HCons a has -> HCons a (updateCt has)

instance Generic (HList c a) where
  type Rep (HList c a)
    = D1 ('MetaData "HList" "HList" "package-name" 'False)
        (GADT
          (
            (C1 ('MetaCons "HNil" 'PrefixI 'False)
              (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                (G '["c" :> c] '[] '[Ty ('[] :: [Type])] '[Ty a] U1)
              )
            )
          :+:
            (C1 ('MetaCons "HCons" 'PrefixI 'False)
              (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                (G '["c" :> c] '[V "t" Type K, V "ts" [Type] K] '[Ty ((Sk "t" :: Type) ': Sk "ts")] '[Ty a]
                  ( (Sk "c" :: Type -> Constraint) (Sk "t")
                      :=>: (K1 R (Sk "t") :*: K1 R (HList (Sk "c" :: Type -> Constraint) (Sk "ts")))
                  )
                )
              )
             )
           )
         )

  from = \case
    HNil
      -> M1 $ GADT $ L1 $ M1 $ M1 $ QF U1

    HCons t hts
      ->
        let proxy_ts = snd $ unApply $ pure hts
        in M1 $ GADT $ R1 $ M1 $ M1 $
             existsG t $ existsG_ proxy_ts $ QF $ Ct $ K1 t :*: K1 hts

  to = \case
    M1 (GADT (L1 (M1 (M1 (QF U1))))) -> HNil
    M1 (GADT (R1 (M1 (M1 (ExG (ExG (QF (Ct (K1 t :*: K1 hts))))))))) -> HCons t hts


unApply :: Proxy (f a) -> (Proxy f, Proxy a)
unApply Proxy = (Proxy, Proxy)
