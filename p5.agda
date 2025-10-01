
----
---- Práctica 5: Programas correctos por construcción
----

open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.List using (List; []; _∷_)
open import Data.Product using (_×_; Σ-syntax; _,_; proj₁; proj₂)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Data.Nat using (ℕ; zero; suc; _+_; _≤_; _≟_)
open import Data.Nat.Properties using (≤-step; ≤-refl; ≤-trans; +-monoʳ-≤; ≤-pred)
open import Relation.Nullary using (Dec; yes; no; ¬_)

-- Recordemos la definición de algunas funciones básicas sobre listas:

_++_ : {A : Set} → List A → List A → List A
[]       ++ ys = ys
(x ∷ xs) ++ ys = x ∷ (xs ++ ys)

length : {A : Set} → List A → ℕ
length []       = zero
length (_ ∷ xs) = suc (length xs)

reverse : {A : Set} → List A → List A
reverse []       = []
reverse (x ∷ xs) = reverse xs ++ (x ∷ [])

---- Parte A ----

-- A.1) Demostrar que dada una lista xs y un entero k ≤ length xs,
-- es posible partir la lista xs en un prefijo ys de longitud k
-- seguido de un sufijo zs.

split : {A : Set} (xs : List A) (k : ℕ)
      → k ≤ length xs
      → Σ[ ys ∈ List A ] Σ[ zs ∈ List A ] ((xs ≡ ys ++ zs) × k ≡ length ys)
split {A} []        zero k≤length_xs = [] , [] , refl , refl
split {A} (x ∷ xs) zero k≤length_xs = [] , (x ∷ xs) , refl , refl
split {A} (x ∷ xs) (suc k) k≤length_xs with split {A} xs k (≤-pred k≤length_xs)
... | ys , zs , (p1 , p2) = x ∷ ys ,
                            zs ,
                            cong (λ l → x ∷ l) p1 ,
                            cong suc p2

{-
-- Sin usar pattern matching sobre el resultado de rec:
split : {A : Set} (xs : List A) (k : ℕ)
      → k ≤ length xs
      → Σ[ ys ∈ List A ] Σ[ zs ∈ List A ] ((xs ≡ ys ++ zs) × k ≡ length ys)
split {A} [] zero foo = [] , [] , refl , refl
split {A} (x ∷ xs) zero foo    = [] , (x ∷ xs) , refl , refl
split {A} (x ∷ xs) (suc k) foo =
  let rec = split {A} xs k (≤-pred foo) in
    x ∷ (proj₁ rec) ,
    proj₁ (proj₂ rec) ,
    cong (λ l -> x ∷ l) (proj₁ (proj₂ (proj₂ rec))) ,
    cong suc (proj₂ (proj₂ (proj₂ rec)))
-}

-- Definimos un predicado "x ∈ ys" que es verdadero si x aparece en ys:

data _∈_ : ℕ → List ℕ → Set where
  zero : {x : ℕ} {xs : List ℕ} → x ∈ (x ∷ xs)
  suc  : {x y : ℕ} {xs : List ℕ} → x ∈ xs → x ∈ (y ∷ xs)

-- A.2) Demostrar que es posible decidir si un número natural aparece en una lista.
-- (Usar _≟_ para decidir la igualdad de números naturales).

-- Lemas auxiliares:
nadie-pertenece-a-la-lista-vacia : {x : ℕ} → x ∈ [] → ⊥
nadie-pertenece-a-la-lista-vacia {x} ()

zero-con-prueba-de-igualdad : {x y : ℕ} {ys : List ℕ} → (p : x ≡ y) → x ∈ (y ∷ ys)
zero-con-prueba-de-igualdad {x} {y} {ys} refl = zero

∈-absurdo : {x y : ℕ} {ys : List ℕ} → (¬ x ≡ y) → ¬ x ∈ ys → x ∈ (y ∷ ys) → ⊥
∈-absurdo {x} {y} {ys} ¬x≡y ¬x∈ys zero        = ¬x≡y refl
∈-absurdo {x} {y} {ys} ¬x≡y ¬x∈ys (suc x∈ys) = ¬x∈ys x∈ys

∈-decidible : {x : ℕ} {ys : List ℕ} → Dec (x ∈ ys)
∈-decidible {x} {[]}     = no (λ x∈[] → nadie-pertenece-a-la-lista-vacia x∈[])
∈-decidible {x} {y ∷ ys} with x ≟ y
... | yes x≡y = yes (zero-con-prueba-de-igualdad x≡y)
... | no ¬x≡y with ∈-decidible {x} {ys}
... | yes x∈ys  = yes (suc x∈ys)
... | no ¬x∈ys  = no (λ x∈y∷ys → ∈-absurdo {x} {y} {ys} ¬x≡y ¬x∈ys x∈y∷ys)

-- A.3) Demostrar que la igualdad de listas es decidible
-- asumiendo que es decidible la igualdad de sus elementos.

-- Lemas auxiliares:
head-coincide : {A : Set} {x y : A} {xs ys : List A} → (x ∷ xs ≡ y ∷ ys) → (x ≡ y)
head-coincide {A} {x} {y} {xs} {ys} refl = refl

-- Reciproco de head-coincide.
¬x≡y⇒¬x∷xs≡y∷ys : {A : Set} {x y : A} {xs ys : List A} → (¬ x ≡ y) → ¬ (x ∷ xs ≡ y ∷ ys)
¬x≡y⇒¬x∷xs≡y∷ys {A} {x} {y} {xs} {ys} ¬x≡y = λ x∷xs≡y∷ys → ¬x≡y (head-coincide x∷xs≡y∷ys)

tail-coincide : {A : Set} {x y : A} {xs ys : List A} → (x ∷ xs ≡ y ∷ ys) → (xs ≡ ys)
tail-coincide {A} {x} {y} {xs} {ys} refl = refl

-- Reciproco de tail-coincide.
¬xs≡ys⇒¬x∷xs≡y∷ys : {A : Set} {x y : A} {xs ys : List A} → (¬ xs ≡ ys) → ¬ (x ∷ xs ≡ y ∷ ys)
¬xs≡ys⇒¬x∷xs≡y∷ys {A} {x} {y} {xs} {ys} ¬xs≡ys = λ x∷xs≡y∷ys → ¬xs≡ys (tail-coincide x∷xs≡y∷ys)

x≡y∧xs≡ys⇒x∷xs≡y∷ys : {A : Set} {x y : A} {xs ys : List A} → (x ≡ y) → (xs ≡ ys) → (x ∷ xs ≡ y ∷ ys)
x≡y∧xs≡ys⇒x∷xs≡y∷ys {A} {x} {y} {xs} {ys} refl refl = refl

-- OBSERVACIÓN: Prodría ser interesante armarme una función reciproco para no tener código repetido.

List-igualdad-decidible : {A : Set}
                        → ((x y : A) → Dec (x ≡ y))
                        → ((xs ys : List A) → Dec (xs ≡ ys))
List-igualdad-decidible dec-eq-A [] [] = yes refl
List-igualdad-decidible dec-eq-A (x ∷ xs) [] = no λ ()
List-igualdad-decidible dec-eq-A [] (y ∷ ys) = no λ ()
List-igualdad-decidible dec-eq-A (x ∷ xs) (y ∷ ys) with dec-eq-A x y
... | no ¬x≡y = no (¬x≡y⇒¬x∷xs≡y∷ys ¬x≡y)
... | yes x≡y with List-igualdad-decidible dec-eq-A xs ys
... | yes xs≡ys = yes (x≡y∧xs≡ys⇒x∷xs≡y∷ys x≡y xs≡ys)
... | no ¬xs≡ys = no (¬xs≡ys⇒¬x∷xs≡y∷ys ¬xs≡ys)

---- Parte B ----

infix  3 _~_
infix  3 _<<_
infixr 3 _~⟨_⟩_
infix  4 _~∎

-- Considerar el siguiente tipo de las permutaciones:

data _~_ : List ℕ → List ℕ → Set where
  ~-empty : [] ~ []
  ~-cons  : {x : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ xs ~ x ∷ ys
  ~-swap  : {x y : ℕ} {xs ys : List ℕ}
          → xs ~ ys
          → x ∷ y ∷ xs ~ y ∷ x ∷ ys
  ~-trans : {xs ys zs : List ℕ}
          → xs ~ ys
          → ys ~ zs
          → xs ~ zs

-- B.1) Demostrar que "~" es reflexiva:

~-refl : {xs : List ℕ} → xs ~ xs
~-refl = {!!}

-- Definimos operadores auxiliares para poder hacer razonamiento ecuacional
-- con permutaciones:

_~⟨_⟩_ : (xs : List ℕ)
       → {ys : List ℕ} → xs ~ ys
       → {zs : List ℕ} → ys ~ zs
       → xs ~ zs
_ ~⟨ p ⟩ q = ~-trans p q

_~∎ : (xs : List ℕ) → xs ~ xs
_ ~∎ = ~-refl

-- B.2) Demostrar que "~" es simétrica:

~-sym : {xs ys : List ℕ} → xs ~ ys → ys ~ xs
~-sym ~-empty       = {!!}
~-sym (~-cons p)    = {!!}
~-sym (~-swap p)    = {!!}
~-sym (~-trans p q) = {!!}

-- B.3) Demostrar que "~" es una congruencia con respecto a la concatenación de listas:

~-++ : {xs ys xs' ys' : List ℕ}
     → xs ~ xs'
     → ys ~ ys'
     → xs ++ ys ~ xs' ++ ys'
~-++ p q = {!!}

-- B.4) Demostrar que una lista invertida es permutación de la lista original:

~-reverse : {xs : List ℕ} → reverse xs ~ xs
~-reverse {[]}     = ~-empty
~-reverse {x ∷ xs} =
    reverse (x ∷ xs)
  ~⟨ ~-refl ⟩
    reverse xs ++ (x ∷ [])
  ~⟨ {!!} ⟩
    xs ++ (x ∷ [])
  ~⟨ {!!} ⟩
    x ∷ xs
  ~∎

----

-- Definimos una función que vale 1 si dos números son iguales, y 0 si no.
iguales? : ℕ → ℕ → ℕ
iguales? x y with x ≟ y
... | yes _ = 1
... | no  _ = 0

-- Definimos una función que cuenta el número de apariciones de un
-- número natural en una lista.
cantidad-apariciones : ℕ → List ℕ → ℕ
cantidad-apariciones x []       = zero
cantidad-apariciones x (y ∷ ys) = iguales? x y + cantidad-apariciones x ys

-- Definimos un predicado xs << ys
-- que es verdadero si cada natural z
-- aparece en xs a lo sumo tantas veces como aparece en ys:

_<<_ : List ℕ → List ℕ → Set
xs << ys = (z : ℕ) → cantidad-apariciones z xs ≤ cantidad-apariciones z ys

-- B.5) Demostrar las siguientes propiedades de "<<":

<<-empty : [] << []
<<-empty = {!!}

<<-refl : {xs : List ℕ} → xs << xs
<<-refl z = {!!}    -- útil: Data.Nat.Properties.≤-refl 

<<-cons : {x : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ xs << x ∷ ys
<<-cons {x} xs<<ys z = {!!}    -- útil:   +-monoʳ-≤ (iguales? z x) ?

<<-swap : {x y : ℕ} {xs ys : List ℕ} → xs << ys → x ∷ y ∷ xs << y ∷ x ∷ ys
<<-swap xs<<ys z = {!!}    -- útil: Data.Nat.Properties.+-monoʳ-≤

<<-trans : {xs ys zs : List ℕ} → xs << ys → ys << zs → xs << zs
<<-trans xs<<ys ys<<zs z = {!!}    -- útil: Data.Nat.Properties.≤-trans

-- B.6) Usando los lemas de B.5, demostrar que la relación "~" es
-- correcta con respecto a "<<".

~-correcta : {xs ys : List ℕ}
           → xs ~ ys 
           → xs << ys 
~-correcta ~-empty       = {!!}
~-correcta (~-cons p)    = {!!}
~-correcta (~-swap p)    = {!!}
~-correcta (~-trans p q) = {!!}
