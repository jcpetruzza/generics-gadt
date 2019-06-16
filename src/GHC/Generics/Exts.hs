{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module GHC.Generics.Exts
  (
    (:=>:)(..)
  , GADT(..)
  , G, Ex
  , GEx(..)
  , exists, exists_
  , existsG, existsG_
  , V, K, (:>)
  , Sk, SubstSk
  , Ty, TVars, NoTVars
  )

where

import Data.Kind ( Constraint, Type )
import GHC.TypeLits ( Symbol )


-- | A kind proxy.
data family K :: k

-- | Type-level representation of a type variable called @n@ with kind @kind@.
data V (n :: Symbol) kind (proxy :: kind)

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

type family (\/) (l :: Type) (r :: Type) where
    () \/ r = r
    l  \/ _ = l


type family FindTVar (sk :: k) (refined1 :: kt1) (refined0 :: kt) (a :: kt) :: Type where
  FindTVar (Sk n :: k) (Sk n :: k) r0 a = Ty (FromTy k (ExtractType (Sk n :: k) r0 a))
  FindTVar _ (Sk m) _ _ = ()
  FindTVar sk (f x) r0 a = (FindTVar sk f r0 a) \/ (FindTVar sk x r0 a)
  FindTVar sk ts r0 a = FindTVarInList sk ts r0 a
  FindTVar _ _ _ _ = ()

type family FindTVarInList (sk :: k) (refined1 :: [kt1]) (refined0 :: [kt]) (as :: [kt]) :: Type where
  FindTVarInList sk '[] _ a = ()
  FindTVarInList sk (x ':xs) r0 a = FindTVar sk x r0 a \/ FindTVarInList sk xs r0 a

type family ExtractType (sk :: k) (refined :: kt) (a :: kt) :: Type where
  ExtractType (Sk n :: k) (Sk n :: k) t = Ty t
  ExtractType _ (Sk m) _ = ()
  ExtractType skn (f (x :: k)) (f' (x' :: k)) = (ExtractType skn f f') \/ (ExtractType skn x x')
  ExtractType sk ts ts' = ExtractTypeFromList sk ts ts'
  ExtractType _ _ _ = ()

type family  ExtractTypeFromList (sk :: k) (refined :: [kt]) (a :: [kt]) :: Type where
  ExtractTypeFromList _ '[] _ = ()
  ExtractTypeFromList sk (x ': xs) (y ': ys) = ExtractType sk x y \/ ExtractTypeFromList sk xs ys



type family FromTy k (tyv :: Type) :: k where
  FromTy k (Ty (v :: k)) = v

type family TVars (bound :: [Type]) (refined :: k) (a :: k) :: [Type] where
  TVars '[] _ _
    = '[]
  TVars (V n k K ': bound') refined a
    = FindTVar (Sk n :: k) refined refined a ': TVars bound' refined a

type family NoTVars (bound :: [Type]) :: [Type] where
  NoTVars '[] = '[]
  NoTVars (_ ': xs) = () ': NoTVars xs

-- | Metadata marking a type as a GADT.
newtype GADT (f :: k -> Type) (p :: k)
  = GADT (f p)
  deriving (Read, Show, Eq, Ord) -- XXX missing instances

-- | Existential type
type Ex free bound
  = GEx free bound '[] (NoTVars bound) '[] '[]

-- | GADT constructor
type G free bound refined a
  = GEx free bound '[] (TVars bound refined a) refined a

-- | Generalized existential type
data GEx
       (free   :: [Type]) (bound  :: [Type])
       (ftvars :: [Type]) (btvars :: [Type])
       (refined :: [Type]) (a :: [Type])
       t x
  where
    QF
      :: SubstSk free t x
      -> GEx
           free   '[]
           ftvars '[]
           refined (SubstSk free refined)
           t x
    Ex
      :: GEx
           (n :> (g :: kg) ': free)   bound
           (  ()           ': ftvars) btvars
           refined a'
           t x
      -> GEx
           free   (V n kg K ': bound)
           ftvars (  ()     ': btvars)
           refined a'
           t x
  
    ExG
      :: GEx
           (n :> (g :: kg) ': free)   bound
           (Ty   (g :: kg) ': ftvars) btvars
           refined a'
           t x
      -> GEx
           free   (V n kg K     ': bound)
           ftvars (Ty (g :: kg) ': btvars)
           refined a'
           t x
exists
  :: g
  -> GEx
       (n :> g ': free)   bound
       (  ()   ': ftvars) btvars
       refined a'
       t x
  -> GEx
       free   (V n Type K ': bound)
       ftvars (  ()       ': btvars)
       refined a'
       t x
exists _ = Ex


exists_
  :: proxy (g :: kg)
  -> GEx
       (n :> g ': free)   bound
       (  ()   ': ftvars) btvars
       refined a'
       t x
  -> GEx
       free   (V n kg K ': bound)
       ftvars (  ()     ': btvars)
       refined a'
       t x
exists_ _ = Ex


existsG
  :: g
  -> GEx
       (n :> g ': free) bound
       (Ty g ': ftvars) btvars
       refined a'
       t x
  -> GEx
       free (V n Type K ': bound)
       ftvars (Ty g ': btvars)
       refined a'
       t x
existsG _ = ExG


existsG_
  :: proxy (g :: kg)
  -> GEx
       (n :> g ': free) bound
       (Ty g ': ftvars) btvars
       refined a'
       t x
  -> GEx
       free (V n kg K ': bound)
       ftvars (Ty g ': btvars)
       refined a'
       t x
existsG_ _ = ExG
