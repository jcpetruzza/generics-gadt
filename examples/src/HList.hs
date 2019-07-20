{-# LANGUAGE Rank2Types #-}
{-# LANGUAGE UndecidableInstances #-}
module HList
  ( HList(..)
  , updateCt
  , All
  ) where

import Data.Kind ( Constraint, Type )

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
        (GD1 '[Ty a]
          (
            (C1 ('MetaCons "HNil" 'PrefixI 'False)
              (GC1 '[Ty ('[] :: [Type])]
                (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                  (QF '["a" :> a, "c" :> c]
                    ('[] ~ (Sk "a" :: [Type]) :=>: U1)
                  )
                )
              )
            )
          :+:
            (C1 ('MetaCons "HCons" 'PrefixI 'False)
              (GC1 '[Ty ((Sk "t" :: Type) ': Sk "ts")]
                (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                  (Let "t" (Sel Type (Lp (Rp Hp)) a)
                    (Let "ts" (Sel [Type] (Rp Hp) a)
                       QF
                    )
                    '["a" :> a, "c" :> c]
                    ( (((Sk "t" :: Type) ': (Sk "ts" :: [Type])) ~ Sk "a")
                        :=>:
                          ((Sk "c" :: Type -> Constraint) (Sk "t"))
                               :=>: (K1 R (Sk "t") :*: K1 R (HList (Sk "c" :: Type -> Constraint) (Sk "ts")))
                    )
                  )
                )
              )
           )
         )
       )


  from = \case
    HNil
      -> M1 $ GM1 $ L1 $ M1 $ GM1 $ M1 $
           QF $ Ct $ U1

    HCons t hts
      -> M1 $ GM1 $ R1 $ M1 $ GM1 $ M1 $
           Let $ Let $ QF $ Ct $ Ct $ K1 t :*: K1 hts

  to = \case
    M1 (GM1 (L1 (M1 (GM1 (M1 (QF (Ct U1))))))) -> HNil
    M1 (GM1 (R1 (M1 (GM1 (M1 (Let (Let (QF (Ct (Ct (K1 t :*: K1 hts))))))))))) -> HCons t hts

