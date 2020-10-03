module PlfaInduction where
import Relation.Binary.PropositionalEquality as Eq
open Eq using (_≡_ ; refl ; cong ; sym)
open Eq.≡-Reasoning using (begin_ ; _≡⟨⟩_ ; _≡⟨_⟩_ ; _∎ )
open import Data.Nat using (ℕ ; zero ; suc ; _+_ ; _*_ ; _^_ )

+-assoc : ∀ (a b c : ℕ) → (a + b) + c ≡ a + (b + c)
+-assoc zero b c =
  begin
    (zero + b) + c
  ≡⟨⟩
    b + c
  ≡⟨⟩
    zero + (b + c)
  ∎

+-assoc (suc a) b c =
  begin
    (suc a + b) + c 
  ≡⟨⟩
    suc (a + b) + c 
  ≡⟨⟩
    suc ((a + b) + c) 
  ≡⟨ cong suc (+-assoc a b c) ⟩ 
    suc (a + (b + c)) 
  ≡⟨⟩
    suc a + (b + c)
  ∎

+-identityʳ : ∀ (a : ℕ) → a + zero ≡ a
+-identityʳ zero =
  begin
    zero + zero
  ≡⟨⟩
    zero
  ∎

+-identityʳ (suc a) =
  begin
    suc a + zero
  ≡⟨⟩
    suc (a + zero)
  ≡⟨ cong suc (+-identityʳ a) ⟩
    suc a
  ∎

+-suc : ∀ (a b : ℕ) → a + suc b ≡ suc (a + b)
+-suc zero b =
  begin
    zero + suc b
  ≡⟨⟩
    suc b
  ≡⟨⟩
   suc (zero + b) 
  ∎

+-suc (suc a) b =
  begin
    suc a + suc b
  ≡⟨⟩
    suc (a + suc b) 
  ≡⟨ cong suc (+-suc a b) ⟩
    suc (suc a + b)
  ∎

+-comm : ∀ (a b : ℕ) → a + b ≡ b + a
+-comm zero b =
  begin
    zero + b
  ≡⟨⟩
    b
  ≡⟨ sym (+-identityʳ b) ⟩
    b + zero
  ∎
  
+-comm (suc a) b =
  begin
    suc a + b
  ≡⟨⟩
    suc (a + b)
  ≡⟨ cong suc (+-comm a b) ⟩
    suc (b + a)
  ≡⟨ sym (+-suc b a) ⟩
    b + suc a
  ∎

+-rearrange : ∀ (a b c d : ℕ) → (a + b) + (c + d)  ≡ (a + (b + c)) + d
+-rearrange a b c d =
  begin
    -- Because addition associates to the left
    -- a + b + (c + d)
    -- is the same as
    (a + b) + (c + d)
  ≡⟨ +-assoc a b (c + d) ⟩
    a + (b + (c + d))
  -- Lesson: The + and the _ in in (a +_) MUST be next to each other (no spaces allowed)
  ≡⟨ cong (a +_) (sym (+-assoc b c d)) ⟩
    a + ((b + c) + d)
  ≡⟨ sym (+-assoc a (b + c) d) ⟩
    (a + (b + c)) + d
  ∎  

-- Let's do it again, now using the rewrite magic
--+-assoc' : ∀ (a b c : ℕ) → a + b + c ≡ a + (b + c)
--+-assoc' zero b c = refl
--+-assoc' (suc a) b c rewrite +-assoc' a b c = refl

--+-suc' : ∀ (a b : ℕ) → a + suc b ≡ suc (a + b)
--+-suc' zero b = refl
--+-suc' (suc a) b rewrite +-suc' a b = refl

+-swap : ∀ (a b c : ℕ) → a + (b + c) ≡ b + (a + c)
+-swap a b c rewrite sym (+-assoc a b c) | +-comm a b | +-assoc b a c = refl 

*-zero : ∀ (a : ℕ) → a * zero ≡ zero 
*-zero zero = refl
*-zero (suc a) rewrite *-zero a = refl

*-rsucdist : ∀ (n m : ℕ) → n * suc m ≡ n + n * m
*-rsucdist zero m = refl
*-rsucdist (suc n) m rewrite *-rsucdist n m | +-swap m n (n * m) = refl

*-distrib : ∀ (x b c : ℕ) → (b + c) * x ≡ b * x + c * x 
*-distrib zero b c rewrite *-zero (b + c) | *-zero b | *-zero c = refl
*-distrib (suc x) b c rewrite *-rsucdist (b + c) x
                            | *-distrib x b c
                            | +-rearrange b c (b * x) (c * x)
                            | +-comm c (b * x)
                            | sym (+-rearrange b (b * x) c (c * x) )
                            | sym (*-rsucdist b x)
                            | sym (*-rsucdist c x) = refl

*-assoc : ∀ (a b c : ℕ) → (a * b) * c ≡ a * (b * c) 
*-assoc zero b c = refl
*-assoc (suc a) b c =
  begin
    (suc a * b) * c
  ≡⟨⟩
    (b + a * b) * c
  ≡⟨ *-distrib c b (a * b) ⟩
    b * c + (a * b) * c
  ≡⟨ cong (λ { x → b * c + x }) (*-assoc a b c) ⟩
    suc a * (b * c)
  ∎

*-comm : ∀ (a b : ℕ) → a * b ≡ b * a
*-comm zero b rewrite *-zero b = refl
*-comm (suc a) b rewrite *-comm a b | sym (*-rsucdist b a) = refl

infixl 6 _∸_
_∸_ : ℕ → ℕ → ℕ
m ∸ zero = m
zero ∸ (suc n) = zero
(suc m) ∸ (suc n) = m ∸ n

∸-zero : ∀ (a : ℕ) → zero ∸ a ≡ zero
∸-zero zero = refl
∸-zero (suc a) = refl

∸-suc : ∀ (a b : ℕ) → a ∸ suc b ≡ a ∸ 1 ∸ b
∸-suc zero b rewrite ∸-zero b = refl
∸-suc (suc a) b = refl

-- ∸-+-assoc : ∀ (a b c : ℕ) → a ∸ b ∸ c ≡ a ∸ (b + c)
-- ∸-+-assoc a zero c = refl
-- ∸-+-assoc a (suc b) c =
--   begin
--     a ∸ suc b ∸ c 
--   ≡⟨ cong (λ x → x ∸ c) (∸-suc a b) ⟩
--     a ∸ 1 ∸ b ∸ c -- Remember this is equal to ((a ∸ 1) ∸ b) ∸ c 
--   ≡⟨ ∸-+-assoc  ⟩
--   ≡⟨ ∸-suc a (b + c) ⟩
--     a ∸ (b + c) 
--   ∎
