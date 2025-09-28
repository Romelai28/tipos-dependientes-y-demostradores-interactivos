----
---- Práctica 2: Naturales e igualdad
----

open import Data.Empty
       using (⊥; ⊥-elim)
open import Data.Bool
       using (Bool; true; false)
open import Data.Nat
       using (ℕ; zero; suc)
open import Data.Product
       using (_,_; Σ-syntax; proj₁; proj₂)
open import Relation.Binary.PropositionalEquality
       using (_≡_; refl; sym; trans; cong)
import Relation.Binary.PropositionalEquality as Eq
open Eq.≡-Reasoning

infixl 20 _+_
infixl 30 _*_

---- Parte A ----

-- Considerar las siguientes definiciones de la suma y el producto:

_+_ : ℕ → ℕ → ℕ
zero  + b = b
suc a + b = suc (a + b)

_*_ : ℕ → ℕ → ℕ
zero  * _ = zero
suc a * b = b + a * b

-- A.1) Demostrar que la suma es asociativa.
+-assoc : {a b c : ℕ} → (a + b) + c ≡ a + (b + c)
+-assoc {zero} = refl
+-assoc {suc a} = cong suc (+-assoc {a})

-- A.2) Demostrar que la suma es conmutativa.
-- Sugerencia: demostrar lemas auxiliares que prueben que:

-- Lemas auxiliares:
--   a + zero = a
+-zero-neutro-por-derecha : {a : ℕ} -> a + zero ≡ a
+-zero-neutro-por-derecha {zero} = refl
+-zero-neutro-por-derecha {suc a} = cong suc (+-zero-neutro-por-derecha {a})

--   a + suc b = suc (a + b)
+-sacar-afuera-suc-derecho : {a b : ℕ} -> a + suc b ≡ suc (a + b)
+-sacar-afuera-suc-derecho {zero} {b} = refl
+-sacar-afuera-suc-derecho {suc a} {b} = cong suc +-sacar-afuera-suc-derecho

+-comm : {a b : ℕ} → a + b ≡ b + a
+-comm {zero} = sym +-zero-neutro-por-derecha
+-comm {suc a} {b} = sym (trans +-sacar-afuera-suc-derecho (cong suc (+-comm {b} {a})))

-- A.3) Demostrar que el producto distribuye sobre la suma (a izquierda).
*-+-distrib-l : {a b c : ℕ} → (a + b) * c ≡ a * c + b * c
*-+-distrib-l {zero} = refl
*-+-distrib-l {suc a} {b} {c} =
  begin
    (suc a + b) * c
  ≡⟨ refl ⟩
    c + (a + b) * c
  ≡⟨ cong (λ x -> c + x) (*-+-distrib-l {a} {b} {c}) ⟩
    c + (a * c + b * c)
  ≡⟨ sym (+-assoc {c} {a * c} {b * c}) ⟩
    c + a * c + b * c
  ∎

-- A.4) Demostrar que el producto es asociativo:
*-assoc : {a b c : ℕ} → (a * b) * c ≡ a * (b * c)
*-assoc {zero} = refl
*-assoc {suc a} {b} {c} =
  begin
    (suc a * b) * c
  ≡⟨ refl ⟩
    (b + a * b) * c
  ≡⟨ *-+-distrib-l {b} {a * b} {c} ⟩
    b * c + (a * b) * c
  ≡⟨ cong (λ x -> b * c + x) (*-assoc {a} {b} {c}) ⟩
    b * c + a * (b * c)
  ∎

-- A.5) Demostrar que el producto es conmutativo.
-- Sugerencia: demostrar lemas auxiliares que prueben que:

-- Lemas auxiliares:
--   a * zero = zero
*-zero-absorbente-por-derecha : {a : ℕ} -> a * zero ≡ zero
*-zero-absorbente-por-derecha {zero} = refl
*-zero-absorbente-por-derecha {suc a} = *-zero-absorbente-por-derecha {a}

--   a * suc b = a + a * b
*-desarrollo-un-paso-por-derecha : {a b : ℕ} -> a * suc b ≡ a + a * b
*-desarrollo-un-paso-por-derecha {zero} = refl
*-desarrollo-un-paso-por-derecha {suc a} {b} =
  begin
    suc a * suc b
  ≡⟨ refl ⟩ 
    suc (b + a * suc b)
  ≡⟨ cong suc ((cong (λ x -> b + x) (*-desarrollo-un-paso-por-derecha {a} {b}))) ⟩
    suc (b + (a + a * b))
  ≡⟨ cong suc (sym (+-assoc {b} {a} {a * b})) ⟩
    suc (b + a + a * b)
  ≡⟨ cong suc (cong (λ x -> x + a * b) ((+-comm {b} {a}))) ⟩
    suc (a + b + a * b)
  ≡⟨ cong suc (+-assoc {a} {b} {a * b}) ⟩
    suc (a + (b + a * b))
  ≡⟨ refl ⟩
    suc a + suc a * b
  ∎

*-comm : {a b : ℕ} → a * b ≡ b * a
*-comm {zero} {b} = sym (*-zero-absorbente-por-derecha {b})
*-comm {suc a} {b} =
  begin
    suc a * b
  ≡⟨ refl ⟩
    b + a * b
  ≡⟨ cong (λ x -> b + x) (*-comm {a} {b}) ⟩
    b + b * a
  ≡⟨ sym (*-desarrollo-un-paso-por-derecha {b} {a}) ⟩
    b * suc a
  ∎
  
-- A.6) Demostrar que el producto distribuye sobre la suma (a derecha).
-- Sugerencia: usar la conmutatividad y la distributividad a izquierda.
*-+-distrib-r : {a b c : ℕ} → a * (b + c) ≡ a * b + a * c
*-+-distrib-r {zero} = refl
*-+-distrib-r {suc a} {b} {c} =
  begin
    suc a * (b + c)
  ≡⟨ *-comm {suc a} {b + c} ⟩
    (b + c) * suc a
  ≡⟨ *-+-distrib-l {b} {c} {suc a} ⟩
    b * suc a + c * suc a
  ≡⟨ cong (λ x -> x + c * suc a) (*-comm {b} {suc a}) ⟩
    suc a * b + c * suc a
  ≡⟨ cong (λ x -> suc a * b + x) (*-comm {c} {suc a}) ⟩
    suc a * b + suc a * c
  ∎

--------------------------------------------------------------------------------

---- Parte B ----

-- Considerar la siguiente definición del predicado ≤ que dados dos números
-- naturales devuelve la proposición cuyos habitantes son demostraciones de que
-- n es menor o igual que m, y la siguiente función ≤? que dados dos
-- números naturales devuelve un booleano que indica si n es menor o igual que
-- n.

_≤_ : ℕ → ℕ → Set
n ≤ m = Σ[ k ∈ ℕ ] k + n ≡ m

_≤?_ : ℕ → ℕ → Bool
zero  ≤? m     = true
suc _ ≤? zero  = false
suc n ≤? suc m = n ≤? m

-- B.1) Demostrar que la función es correcta con respecto a su especificación.
-- Sugerencia: seguir el esquema de inducción con el que se define la función _≤?_.

≤?-correcta : {n m : ℕ} → (n ≤? m) ≡ true → n ≤ m
≤?-correcta {zero} {m} _ = m , +-zero-neutro-por-derecha
≤?-correcta {suc n} {zero} ()
≤?-correcta {suc n} {suc m} x = proj₁ (≤?-correcta {n} {m} x) ,
  (
    begin
      proj₁ (≤?-correcta {n} {m} x) + suc n
    ≡⟨ +-sacar-afuera-suc-derecho {proj₁ (≤?-correcta {n} {m} x)} {n} ⟩
      suc (proj₁ (≤?-correcta {n} {m} x) + n)
    ≡⟨ cong suc (proj₂ (≤?-correcta {n} {m} x)) ⟩
      suc m
    ∎
  )

-- B.2) Demostrar que es imposible que el cero sea el sucesor de algún natural:

zero-no-es-suc : {n : ℕ} → suc n ≡ zero → ⊥
zero-no-es-suc ()

-- B.3) Demostrar que la función es completa con respecto a su especificación.
-- Sugerencia: seguir el esquema de inducción con el que se define la función _≤?_.
-- * Para el caso en el que n = suc n' y m = zero, usar el ítem B.2 y propiedades de la suma.
-- * Para el caso en el que n = suc n' y m = suc m', recurrir a la hipótesis inductiva y propiedades de la suma.

-- Lema auxiliar: 
suc-es-inyectivo : {n m : ℕ} → suc n ≡ suc m → n ≡ m
suc-es-inyectivo {n} {m} refl = refl

≤?-completa : {n m : ℕ} → n ≤ m → (n ≤? m) ≡ true
≤?-completa {zero} x = refl
≤?-completa {suc n} {zero} (k , p) = ⊥-elim (zero-no-es-suc (trans (sym (+-sacar-afuera-suc-derecho {k} {n})) p))
{--
≤?-completa {suc n} {zero} (k , p) =
  let zzz = begin
              suc (k + n)
            ≡⟨ sym +-sacar-afuera-suc-derecho ⟩
              k + suc n
            ≡⟨ p ⟩
              zero
            ∎
  in ⊥-elim (zero-no-es-suc zzz)
--}
≤?-completa {suc n} {suc m} (k , p) =  ≤?-completa {n} {m} (k , suc-es-inyectivo (trans (sym (+-sacar-afuera-suc-derecho {k} {n})) p))

--------------------------------------------------------------------------------

---- Parte C ----

-- La siguiente función corresponde al principio de inducción en naturales:

indℕ : (C : ℕ → Set)
       (c0 : C zero)
       (cS : (n : ℕ) → C n → C (suc n))
       (n : ℕ)
       → C n
indℕ C c0 cS zero    = c0
indℕ C c0 cS (suc n) = cS n (indℕ C c0 cS n)

-- Definimos el predicado de "menor estricto" del siguiente modo:
_<_ : ℕ → ℕ → Set
n < m = suc n ≤ m

-- C.1) Demostrar el principio de inducción completa, que permite recurrir a la hipótesis
-- inductiva sobre cualquier número estrictamente menor.
ind-completa : (C : ℕ → Set)
               (f : (n : ℕ)
                  → ((m : ℕ) → suc m ≤ n → C m)
                  → C n)
               (n : ℕ)
               → C n
ind-completa C f zero = {!!}
ind-completa C f (suc n) = {!!}

--------------------------------------------------------------------------------

---- Parte D ----

-- D.1) Usando pattern matching, definir el principio de inducción sobre la
-- igualdad:

ind≡ : {A : Set}
       {C : (a b : A) → a ≡ b → Set}
     → ((a : A) → C a a refl)
     → (a b : A) (p : a ≡ b) → C a b p
ind≡ {A} {C} cRefl a b refl = cRefl a

-- D.2) Demostrar nuevamente la simetría de la igualdad, usando ind≡:

sym' : {A : Set} {a b : A} → a ≡ b → b ≡ a
sym' {A} {a} {b} p = ind≡ {A} {λ a b _ -> b ≡ a} (λ _ → refl) a b p

-- D.3) Demostrar nuevamente la transitividad de la igualdad, usando ind≡:

trans' : {A : Set} {a b c : A} → a ≡ b → b ≡ c → a ≡ c
trans' {A} {a} {b} {c} refl q = {!!}

-- D.4) Demostrar nuevamente que la igualdad es una congruencia, usando ind≡:

cong' : {A B : Set} {a b : A} → (f : A → B) → a ≡ b → f a ≡ f b
cong' {A} {B} {a} {b} f p = ind≡ {A} {λ a b _ -> f a ≡ f b} (λ _ -> refl) a b p
