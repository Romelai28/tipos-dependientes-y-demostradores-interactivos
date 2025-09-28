open import Agda.Builtin.Equality

-- Ej 1 --------------
flip : {A B C : Set} -> (A -> B -> C) -> B -> A -> C
flip f b a = f a b

compose : {A B C : Set} -> (B -> C) -> (A -> B) -> A -> C
compose f g a = f (g a)

-- Punto de vista logico:
-- flip: [(A implica B) implica C] implica [(B implica A) implica C]  (de hecho es un sii)
-- compose: A partir de B => C y A => B y A podemos construir evidencia de que vale C. 

-- Punto de vista computacional:
-- flip: Toma una funcion que toma argumentos a, b y devuelve la "misma" funcion que toma los argumentos en el otro orden, b, a.
-- compose: composicion matematica de funciones.


-- Ej2 --------------
data Bool : Set where
  false : Bool
  true : Bool

recBool : {C : Set} -> C -> C -> Bool -> C
recBool a _ true = a
recBool _ b false = b

not : Bool -> Bool
not b = recBool false true b

-- Tests:
test_not_true : not true ≡ false
test_not_true = refl

test_not_false : not false ≡ true
test_not_false = refl


-- Ej 3 --------------
data _×_ (A B : Set) : Set where
  _,_ : A -> B -> A × B

-- a)
recProduct : {A B : Set} {C : Set} -> (A -> B -> C) -> A × B -> C
recProduct f (a , b) = f a b

-- b)
elimProduct :  {A B : Set} -> (C : A × B -> Set) -> ((a : A) (b : B) -> C (a , b)) -> (x : A × B) -> C x  
elimProduct c f (a , b) = f a b

-- elimProductv2 :  {A B : Set} {C : A × B -> Set} -> ((a : A) (b : B) -> C (a , b)) -> (x : A × B) -> C x  
-- elimProductv2 f (a , b) = f a b

-- c)
-- i)
π₁ : {A B : Set} -> (A × B) -> A 
π₁ {A} {B} = elimProduct (λ _ → A) (( λ a b -> a ))

-- ii)
π₂ : {A B : Set} -> (A × B) -> B
π₂ {A} {B} = elimProduct (λ _ -> B) ((λ a b -> b))

-- CONSULTAR!!!! ¿Esta bien que le pase a la funcion el c?
-- iii)
curry : {A B : Set} -> (C : A × B -> Set) -> ((x : A × B) -> C x) -> (a : A) -> (b : B) -> C (a , b)
curry c f a b = elimProduct c (λ a b -> f (a , b)) (a , b)

-- curryv2 : {A B : Set} {C : A × B -> Set} -> ((x : A × B) -> C x) -> (a : A) -> (b : B) -> C (a , b)
-- curryv2 f a b = elimProductv2 (λ a b -> f (a , b)) (a , b)

-- iv)
uncurry : {A B : Set} -> (C : A × B -> Set) -> ((a : A) -> (b : B) -> C (a , b)) -> (x : A × B) -> C x
uncurry c f (a , b) = elimProduct c f (a , b) 

-- Cuando C no depende de x las dos funciones corresponden a curry, uncurry.


-- Ej 4 --------------
data ⊥ : Set where

-- a)
⊥-elim : {C : Set} -> ⊥ -> C
⊥-elim ()

-- b)
-- i) (A -> ⊥) -> A -> B
deAbsurdoConcluyoCualquierCosa : {A B : Set} -> (A -> ⊥) -> A -> B
deAbsurdoConcluyoCualquierCosa f a = ⊥-elim (f a)


-- Ej 5 --------------
data ⊤ : Set where
  tt : ⊤

indUnit : {C : ⊤ -> Set} -> C tt -> (x : ⊤) -> C x
indUnit v tt = v


-- Ej 6 --------------
data Σ (A : Set) (B : A -> Set) : Set where
  _,_ : (a : A) -> B a -> Σ A B

-- 1)
Σ-elim : {A : Set} {B : A -> Set} -> (C : Σ A B -> Set) -> ((a : A) (b : B a) -> C (a , b)) -> (x : Σ A B) -> C x
Σ-elim c f (a , b) = f a b

-- 2)
proj₁ : {A : Set} {B : A -> Set} -> Σ A B -> A
proj₁ (a , _) = a

proj₂ : {A : Set} {B : A -> Set} -> (p : Σ A B) -> B (proj₁ p) 
proj₂ (_ , b) = b

-- 3)

ac-debil : {A B : Set} {C : A -> B -> Set} ->
              ((a : A) -> (Σ B (C a))) ->
              (Σ (A -> B) (λ f -> (a : A) -> C a (f a)))
              
