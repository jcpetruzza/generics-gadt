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
import GHC.Generics.Pruning


data HList c a where
  HNil :: HList c '[]
  HCons :: c t => t -> HList c ts -> HList c (t ': ts)

instance c ~ GEq => GEq (HList c a)
instance c ~ GShow => GShow (HList c a)

deriving via (Pruning (HList c '[]))
  instance GSemigroup (HList c '[])

deriving via (Pruning (HList c (a ': as)))
  instance (GSemigroup a, GSemigroup (HList c as)) => GSemigroup (HList c (a ': as))


deriving via (Pruning (HList c '[]))
  instance GMonoid (HList c '[])

deriving via (Pruning (HList c (a ': as)))
  instance (c a, GMonoid a, GMonoid (HList c as)) => GMonoid (HList c (a ': as))


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
        (
           (C1 ('MetaCons "HNil" 'PrefixI 'False)
             (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
               (Let a (Let c (Match Type (Exact ('[] :: [Type])) a QF)) 'Grnd
                  ((Var 2 :: [Type]) ~ '[] :=>: U1)
               )
             )
           )
        :+:
            (C1 ('MetaCons "HCons" 'PrefixI 'False)
              (S1 ('MetaSel 'Nothing 'NoSourceUnpackedness 'NoSourceStrictness 'DecidedLazy)
                (Let a (Let c
                  (Match Type   ((Pat PVar :: Type) ': (Pat PAny)) a
                  (Match [Type] ((Pat PAny :: Type) ': (Pat PVar)) a QF))) 'Grnd
                    ( (((Var 1 :: Type) ': (Var 0 :: [Type])) ~ Var 3)
                        :=>:
                          ((Var 2 :: Type -> Constraint) (Var 1))
                               :=>: (K1 R (Var 1 :: Type) :*: K1 R (HList (Var 2 :: Type -> Constraint) (Var 0)))
                    )
                )
              )
            )
        )

  from = \case
    HNil
      -> M1 $ L1 $ M1 $ M1 $ Let $ Let $ Match $ Let $ QF $ Ct U1

    HCons t hts
      -> M1 $ R1 $ M1 $ M1 $
           Let $ Let $ Match $ Let $ Match $ Let $ QF $ Ct $ Ct (K1 t :*: K1 hts)

  to = \case
    M1 (L1 (M1 (M1 (Let (Let (Match (Let (QF (Ct U1))))))))) -> HNil
    M1 (R1 (M1 (M1 (Let (Let (Match (Let (Match (Let (QF (Ct (Ct (K1 t :*: K1 hts))))))))))))) -> HCons t hts
