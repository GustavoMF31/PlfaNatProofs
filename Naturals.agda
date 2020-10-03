module Naturals where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; cong )
open Eq.≡-Reasoning using (begin_; _≡⟨⟩_; _∎ )

data ℕ : Set where
  zero : ℕ 
  suc : ℕ → ℕ
{-# BUILTIN NATURAL ℕ #-}

infixl 6 _+_
_+_ : ℕ → ℕ → ℕ
zero + x = x
(suc a) + x = suc (a + x)

-- Exercise: Write the reasoning chain of 3 + 4
_ : 3 + 4 ≡ 7
_ = 
  begin
    3 + 4
  ≡⟨⟩
    suc (2 + 4)
  ≡⟨⟩
    suc (suc (1 + 4))
  ≡⟨⟩
    suc (suc (suc (0 + 4)))
  ≡⟨⟩
    suc (suc (suc 4))
  ≡⟨⟩
    7
  ∎

infixl 7 _*_
_*_ : ℕ → ℕ → ℕ
zero * y = zero
suc x * y = y + (x * y)

_ : 3 * 4 ≡ 12
_ =
  begin
    3 * 4
  ≡⟨⟩
    4 + (2 * 4)
  ≡⟨⟩
    4 + (4 + (1 * 4))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + (0 * 4)))
  ≡⟨⟩
    4 + (4 + (4 + 0))
  ≡⟨⟩
    12
  ∎

_^_ : ℕ → ℕ → ℕ
x ^ zero = 1
x ^ suc y = x * (x ^ y)

-- Kinda like minus, but not exactly
infixl 6 _monus_
_monus_ : ℕ → ℕ → ℕ
zero monus y = zero
suc x monus zero = suc x
suc x monus suc y = x monus y

_ : 5 monus 3 ≡ 2
_ =
  begin
    5 monus 3
  ≡⟨⟩
    4 monus 2
  ≡⟨⟩
    3 monus 1
  ≡⟨⟩
    2 monus 0
  ≡⟨⟩
    2
  ∎

_ : 3 monus 5 ≡ 0
_ =
  begin
    2 monus 4
  ≡⟨⟩
    1 monus 3
  ≡⟨⟩
    0 monus 2
  ≡⟨⟩
    0    
  ∎

{-# BUILTIN NATPLUS _+_ #-}
{-# BUILTIN NATTIMES _*_ #-}
{-# BUILTIN NATMINUS _monus_ #-}

data Bin : Set where
  -- Empty bitstring
  ⟨⟩ : Bin
  -- Append a zero
  _O : Bin → Bin
  -- Append a one
  _I : Bin → Bin

inc : Bin → Bin
inc ⟨⟩ = ⟨⟩ I
inc (b O) = b I
inc (b I) = (inc b) O

to : ℕ → Bin
to zero = ⟨⟩ O
to (suc n) = inc (to n)

from : Bin → ℕ
from ⟨⟩ = zero
from (b O) = from b * 2
from (b I) = from b * 2 + 1

-- I tried to prove these things doing some basic stuff but sadly got nowhere
-- I probably should just read the next chapter! (lol)
--multCommutes : (a : ℕ) → (b : ℕ) → a * b ≡ b * a
--multCommutes zero zero = refl
--multCommutes zero (suc b) = multCommutes zero b
--multCommutes (suc a) zero = multCommutes a zero
--multCommutes (suc a) (suc b) = {! cong (multCommutes a b) !}

--multIsAssociative : (a : ℕ) → (b : ℕ) → (c : ℕ) → (a * b) * c ≡ a * (b * c)
--multIsAssociative zero b c = refl
--multIsAssociative (suc a) zero c = refl
--multIsAssociative (suc a) (suc b) zero = refl
--multIsAssociative (suc a) (suc b) (suc c) = {! multIsAssociative a b c  !}

