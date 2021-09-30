-- | An implementation in PureScript of
-- |
-- | Clowns to the Left of me, Jokers to the Right (Pearl):
-- | Dissecting Data Structures by Conor McBride
module Main where

import Prelude

import Control.Monad.Rec.Class (Step(..), tailRec)
import Data.Bifunctor (class Bifunctor, bimap)
import Data.Either (Either)
import Data.Either as E
import Data.Foldable (foldr)
import Data.Functor.Clown (Clown(..))
import Data.Functor.Joker (Joker(..))
import Data.Functor.Mu (Mu(..))
import Data.List (List(..), (:), reverse)
import Data.Tuple (Tuple(..))
import Effect (Effect)
import Effect.Console (logShow)
import Partial.Unsafe (unsafeCrashWith)

-- Polyomial Functor Kit

-- | constant
newtype Const ∷ ∀ k. Type → k → Type
newtype Const a x = Const a

-- | element
newtype Id x = Id x

-- | choice
data Choice ∷ ∀ k. (k → Type) → (k → Type) → k → Type
data Choice x y z = Left (x z) | Right (y z)

-- | pairing
data Pairing ∷ ∀ k. (k → Type) → (k → Type) → k → Type
data Pairing x y z = Pair (x z) (y z)

-- | one
type One ∷ ∀ k. k → Type
type One = Const Unit

instance Functor (Const a) where
  map _ (Const a) = Const a

instance Functor Id where
  map f (Id a) = Id (f a)

instance (Functor p, Functor q) ⇒ Functor (Choice p q) where
  map f (Left p) = Left (map f p)
  map f (Right q) = Right (map f q)

instance (Functor p, Functor q) ⇒ Functor (Pairing p q) where
  map f (Pair p q) = Pair (map f p) (map f q)

-- Polynomial Bifunctor Kit
newtype Const2 ∷ ∀ k1 k2. Type → k1 → k2 → Type
newtype Const2 a x y = Const2 a

newtype Fst ∷ ∀ k. Type → k → Type
newtype Fst x y = Fst x

newtype Snd ∷ ∀ k. k → Type → Type
newtype Snd x y = Snd y

data Choice2 ∷ ∀ k1 k2. (k1 → k2 → Type) → (k1 → k2 → Type) → k1 → k2 → Type
data Choice2 p q x y = Left2 (p x y) | Right2 (q x y)

data Pairing2 ∷ ∀ k1 k2. (k1 → k2 → Type) → (k1 → k2 → Type) → k1 → k2 → Type
data Pairing2 p q x y = Pair2 (p x y) (q x y)

type One2 ∷ ∀ k1 k2. k1 → k2 → Type
type One2 = Const2 Unit

instance Bifunctor (Const2 a) where
  bimap _ _ (Const2 a) = Const2 a

instance Bifunctor Fst where
  bimap f _ (Fst x) = Fst (f x)

instance Bifunctor Snd where
  bimap _ g (Snd y) = Snd (g y)

instance (Bifunctor p, Bifunctor q) ⇒ Bifunctor (Choice2 p q) where
  bimap f g (Left2 p) = Left2 (bimap f g p)
  bimap f g (Right2 q) = Right2 (bimap f g q)

instance (Bifunctor p, Bifunctor q) ⇒ Bifunctor (Pairing2 p q) where
  bimap f g (Pair2 p q) = Pair2 (bimap f g p) (bimap f g q)

type Zero ∷ ∀ k. k → Type
type Zero = Const Void

type Zero2 ∷ ∀ k1 k2. k1 → k2 → Type
type Zero2 = Const2 Void

refute ∷ ∀ a. Void → a
refute _ = unsafeCrashWith "we shouldn't be here..."

-- | Dissections!
class (Functor p, Bifunctor p') ⇐ Dissect p p' | p → p' where
  right
    ∷ ∀ c j
    . Either (p j) (Tuple (p' c j) c)
    → Either (Tuple j (p' c j)) (p c)

instance Dissect (Const a) Zero2 where
  right x = case x of
    E.Left (Const a) → E.Right (Const a)
    E.Right (Tuple (Const2 z) _) → refute z

instance Dissect Id One2 where
  right x = case x of
    E.Left (Id j) → E.Left (Tuple j (Const2 unit))
    E.Right (Tuple (Const2 _) c) → E.Right (Id c)

instance
  ( Dissect p p'
  , Dissect q q'
  ) ⇒
  Dissect (Choice p q) (Choice2 p' q') where
  right x = case x of
    E.Left (Left pj) → mindp (right (E.Left pj))
    E.Left (Right qj) → mindq (right (E.Left qj))
    E.Right (Tuple (Left2 pd) c) → mindp (right (E.Right (Tuple pd c)))
    E.Right (Tuple (Right2 qd) c) → mindq (right (E.Right (Tuple qd c)))
    where
    mindp (E.Left (Tuple j pd)) = E.Left (Tuple j (Left2 pd))
    mindp (E.Right pc) = E.Right (Left pc)

    mindq (E.Left (Tuple j qd)) = E.Left (Tuple j (Right2 qd))
    mindq (E.Right qc) = E.Right (Right qc)

instance
  ( Dissect p p'
  , Dissect q q'
  ) ⇒
  Dissect (Pairing p q) (Choice2 (Pairing2 p' (Joker q)) (Pairing2 (Clown p) q')) where
  right x = case x of
    E.Left (Pair pj qj) → mindp (right (E.Left pj)) qj
    E.Right (Tuple (Left2 (Pair2 pd (Joker qj))) c) → mindp (right (E.Right (Tuple pd c))) qj
    E.Right (Tuple (Right2 (Pair2 (Clown pc) qd)) c) → mindq pc (right (E.Right (Tuple qd c)))
    where
    mindp (E.Left (Tuple j pd)) qj = E.Left (Tuple j (Left2 (Pair2 pd (Joker qj))))
    mindp (E.Right pc) qj = mindq pc (right (E.Left qj))

    mindq pc (E.Left (Tuple j qd)) = E.Left (Tuple j (Right2 (Pair2 (Clown pc) qd)))
    mindq pc (E.Right qc) = E.Right (Pair pc qc)

tmap ∷ ∀ p p' s t. Dissect p p' ⇒ (s → t) → p s → p t
tmap f ps = continue (right (E.Left ps))
  where
  continue (E.Left (Tuple s pd)) = continue (right (E.Right (Tuple pd (f s))))
  continue (E.Right pt) = pt

tcata ∷ ∀ p p' v. Dissect p p' ⇒ (p v → v) → Mu p → v
tcata algebra t = load algebra t mempty

load ∷ ∀ p p' v. Dissect p p' ⇒ (p v → v) → Mu p → List (p' v (Mu p)) → v
load algebra (In pt) stk = next algebra (right (E.Left pt)) stk

next ∷ ∀ p p' v. Dissect p p' ⇒ (p v → v) → Either (Tuple (Mu p) (p' v (Mu p))) (p v) → List (p' v (Mu p)) → v
next algebra (E.Left (Tuple t pd)) stk = load algebra t (pd : stk)
next algebra (E.Right pv) stk = unload algebra (algebra pv) stk

unload ∷ ∀ p p' v. Dissect p p' ⇒ (p v → v) → v → List (p' v (Mu p)) → v
unload algebra v (pd : stk) = next algebra (right (E.Right (Tuple pd v))) stk
unload _ v Nil = v

tcata' ∷ ∀ p p' v. Dissect p p' ⇒ (p v → v) → Mu p → v
tcata' algebra (In pt) = next algebra (right (E.Left pt)) mempty

next' ∷ ∀ p p' v. Dissect p p' ⇒ (p v → v) → Either (Tuple (Mu p) (p' v (Mu p))) (p v) → List (p' v (Mu p)) → v
next' algebra i s = tailRec go { index: i, stack: s }
  where
  go { index, stack } =
    case index of
      E.Left (Tuple (In pt) pd) →
        Loop { index: (right (E.Left pt)), stack: (pd : stack) }
      E.Right pv → case stack of
        (pd : stk) → Loop { index: (right (E.Right (Tuple pd (algebra pv)))), stack: stk }
        Nil → Done (algebra pv)

tcata'' ∷ ∀ p p' v. Dissect p p' ⇒ (p v → v) → Mu p → v
tcata'' algebra (In pt_) = go (right (E.Left pt_)) mempty
  where
  go index stack =
    case index of
      E.Left (Tuple (In pt) pd) →
        go (right (E.Left pt)) (pd : stack)
      E.Right pv →
        case stack of
          (pd : stk) →
            go (right (E.Right (Tuple pd (algebra pv)))) stk
          Nil →
            algebra pv

infixl 3 type Choice as :+:
infixl 4 type Pairing as :*:

type List' a = Mu (Const a :*: Id :+: One)

nil :: forall a. List' a
nil = In (Right (Const unit))

cons :: forall a. a -> List' a -> List' a
cons a (In l) = In (Left (Pair (Const a) (Id (In l))))

fromZeroTo :: Int -> List' Int
fromZeroTo n = go nil 0 (n + 1)
  where
  go v _ 0 = v
  go v a b = go (cons a v) (a + 1) (b - 1)

xs :: List' Int
xs = fromZeroTo 1_000_000

sum :: List' Int -> Int
sum = tcata'' go
  where
  go (Left (Pair (Const l) (Id r))) = l + r
  go (Right (Const _)) = 0

tana :: forall p p' v. Dissect p p' => (v -> p v) -> v -> Mu p
tana coalgebra = go mempty
  where
  go stack seed = do
    let head = coalgebra seed
    case right (E.Left head) of
      E.Left (Tuple tail _) -> go (head : stack) tail
      E.Right end -> In (foldr (\a b -> map (const (In b)) a) end (reverse stack))

mkList :: Int -> List' Int
mkList = tana go
  where
  go :: Int -> (Const Int :*: Id :+: One) Int
  go 0 = Right (Const unit)
  go n = Left (Pair (Const n) (Id (n - 1)))

main ∷ Effect Unit
main = logShow (sum (mkList 10000))
