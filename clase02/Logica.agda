{- 

    Introducción a la Programación con Tipos Dependientes
      
           Mauro Jaskelioff

-}


module Logica where

{- Lógica proposicional y Lógica de predicados.

 Veremos como hacer pruebas en Agda.

 Empezamos con lógica proposicional.
 
 A partir de la idea de "Proposiciones como tipos" o "Isomoforfismo de Curry-Howard"
 se pueden interpretar
   - los tipos como proposiciones
   - los programas de un tipo como las pruebas de la proposición correspondiente.
   
 Por lo tanto una proposición es verdadera si el tipo correspondiente es no vacío.

-}

{-

A menudo no nos interesa distinguir entre diferentes pruebas para una
misma proposición. Es decir que sólo nos interesa si un tipo está
habitado o no.  Esto fenómeno en donde no nos interesa distinguir a
dos términos del mismo tipo se conoce como "proof irrelevance", o
irrelevancia de la prueba. El lenguaje Coq distingue entre Prop (cosas
con irrelevancia de prueba) y Set (donde dos habitantes del mismo tipo
no son considerados necesariamente iguales).

En Agda esta distinción no existe y hay otras maneras de manejar la
irrelevancia de prueba.

-}

prop : Set₁
prop = Set


{- introducimos tipos para true (⊤) y para false (⊥) -}

{- \top = ⊤ -}
data ⊤ : prop where
  tt : ⊤




{- \bot = ⊥ -}
data ⊥ : prop where
{- este espacio dejado intencionalmente en blanco. -}





efq : {P : prop} → ⊥ → P
efq ()


{- Usamos el patrón () para indicar un patrón absurdo.  Dado que el
   tipo de datos ⊥ no tiene constructores (es vacío), es absurdo hacer
   pattern matching sobre él.
-}








{- A partir de la interpretación de "proposiciones como tipos", las
conjunciones de la lógica proposicional surgen naturalmente:

  - La conjunción (A ∧ B) (tanto A como B son verdaderos) está
    representada por el producto cartesiano (A × B), ya que dar un
    término de tipo (A × B) es dar un término de tipo A y un término
    de tipo B.
  - La implicación (A → B) es una función (A → B), que dada una
    prueba de A me devuelve una prueba de B.

  - La disyunción (A ∨ B) (tengo una prueba de A o una prueba de B),
    está dada por la unión disjunta.
-}

{- Conjunción -}
data _∧_ (P Q : prop) : prop where
  _,_ : (p : P) → (q : Q) → P ∧ Q

infixr 2 _∧_

{- C-c C-, nos da el "estado de la prueba" -}
{- C-c C-. dentro de un agujero, compara el tipo del agujero con el objetivo. -}
∧-comm : {P Q : prop} → P ∧ Q → Q ∧ P
∧-comm (p , q) = q , p

fst : {P Q : prop} → P ∧ Q → P
fst (p , q) = p

snd : {P Q : prop} → P ∧ Q → Q
snd (p , q) = q



{- Disyunción -}

data _∨_ (P Q : prop) : prop where
    left : (p : P) → P ∨ Q
    right : (q : Q) → P ∨ Q

case : {P Q R : prop} → (P → R) → (Q → R) → P ∨ Q → R
case f g (left p) = f p
case f g (right q) = g q

or-com : {P Q : prop} → P ∨ Q → Q ∨ P
or-com (left p) = right p
or-com (right q) = left q

distrib→ : {P Q R : prop} → P ∧ (Q ∨ R) → (P ∧ Q) ∨ (P ∧ R)
distrib→ (p , left q) = left (p , q)
distrib→ (p , right r) = right (p , r)


distrib← : {P Q R : prop} → (P ∧ Q) ∨ (P ∧ R) → P ∧ (Q ∨ R)
distrib← (left (p , q)) = p , (left q)
distrib← (right (p , q)) = p , right q


{- Definimos equivalencia lógica -}

_⇔_ : prop → prop → prop
P ⇔ Q = (P → Q) ∧ (Q → P)

infixr 0 _⇔_

copy : {A : prop} → A ⇔ A ∧ A
copy = (λ x → x , x) , snd

distrib⇔ : {P Q R : prop} → P ∧ (Q ∨ R) ⇔ (P ∧ Q) ∨ (P ∧ R)
distrib⇔ = distrib→ , distrib←

{- Probamos currificación -}
curry→ : {P Q R : prop} → (P ∧ Q → R) → (P → Q → R)
curry→ pyqr = λ p q → pyqr (p , q)

curry← : {P Q R : prop} → (P → Q → R) → (P ∧ Q → R)
curry← f (p , q) = f p q

curry⇔ : {P Q R : prop} → (P ∧ Q → R) ⇔ (P → Q → R)
curry⇔ = curry→ , curry←


--------------------------------------
{- Ejercicios -}
∨∧→ : {P Q R : prop} → (P ∨ Q → R) → ((P → R) ∧ (Q → R))
∨∧→ poqr = (λ x → poqr (left x)) , (λ x → poqr (right x))

∨∧← : {P Q R : prop} → ((P → R) ∧ (Q → R)) → (P ∨ Q → R) 
∨∧← (p , q) (left po) = p po
∨∧← (p , q) (right qo) = q qo

∨∧ : {P Q R : prop} → (P ∨ Q → R) ⇔ ((P → R) ∧ (Q → R))
∨∧ = ∨∧→ , ∨∧←
----------------------------------------

{- Introducimos la negación
   ¬ = \neg 
-}

¬ : prop → prop
¬ P = P → ⊥
                     -- (P ∧ ¬ P) → ⊥    
contradict : {P : prop} → ¬ (P ∧ ¬ P)
contradict (p , q) = q p

contrapos : {P Q : prop} → (P → Q) → ¬ Q → ¬ P
contrapos pq nq p = nq (pq p)

-----------------------------------------------
{- Ejercicio: paradoja -}
paradox : {P : prop} → ¬ (P ⇔ ¬ P) -- ((P → ¬P) ^ (¬P → P)) → ⊥ <---> ((P → P → ⊥) ^ (P → ⊥ → P)) → ⊥
paradox (p , q) = p (q (λ x → p x x)) (q (λ x → p x x)) -- good ol hay que dejarse llevar por los tipos

{- Ejercicio: Probamos las leyes de de Morgan -}

deMorgan¬∨ : {P Q : prop} → ¬ (P ∨ Q) → ¬ P ∧ ¬ Q -- (P v Q → ⊥ ) → ((P → ⊥) ^ (Q → ⊥))
deMorgan¬∨ npq = (λ poq → npq (left poq)) , (λ poq → npq (right poq)) 
  
deMorgan¬∧¬ : {P Q : prop} → (¬ P) ∧ (¬ Q) → ¬ (P ∨ Q) -- (P → ⊥) ^ (Q → ⊥) → (P v Q) → ⊥
deMorgan¬∧¬ (p , q) (left po) = p po
deMorgan¬∧¬ (p , q) (right qo) = q qo 
  
deMorgan¬∨¬ : {P Q : prop} → (¬ P) ∨ (¬ Q) → ¬ (P ∧ Q) -- (P → ⊥) v (Q → ⊥) → (P ^ Q) → ⊥
deMorgan¬∨¬ (left np) (p , q) = np p
deMorgan¬∨¬ (right nq) (p , q) = nq q

-- deMorgan¬∧ : {P Q : prop} → ¬ (P ∧ Q) → (¬ P) ∨ (¬ Q) -- (P ^ Q → ⊥) → (P → ⊥) v (Q → ⊥)
-- deMorgan¬∧ npq = {!!} -- no se puede?? no se :(((

-------------------------------------------------------

{- sobre razonamiento clásico vs. razonamiento intuicionístico. -}

{- En Agda no podemos probar la ley del tercero excluído.
  No podemos probar tampoco que la doble negación (¬¬ P → P)

terex : {P : prop} → P ∨ ¬ P
terex = {! !} -- no se puede probar.
-}


{- Lógica de Predicados -}

{- La cuantificación universal se expresa de la siguiente manera:

  Dados A : Set,
        P : A → prop

el predicado
   
      ∀ a : A. P a : prop
      
   se escribe
   (a : A) → P a
-}

∀∧ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a ∧ Q a) → ((a : A) → P a) ∧ ((a : A) → Q a)
∀∧ h = (λ a → fst (h a)) , (λ a → snd (h a))

∧∀ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a) ∧ ((a : A) → Q a) → ((a : A) → P a ∧ Q a)
∧∀ (p , q) = λ a → (p a) , (q a)

{-
∀∨ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a ∨ Q a) → ((a : A) → P a) ∨ ((a : A) → Q a)
∀∨ pq = {! !}

Falso
-}

∨∀ : {A : Set}{P Q : A → prop} → 
  ((a : A) → P a) ∨ ((a : A) → Q a) → ((a : A) → P a ∨ Q a)
∨∀ (left p) = λ a → left (p a)
∨∀ (right q) = λ a → right (q a)

{- La cuantificación existencial:
   Dados:  A : Set ,
           P : A → Prop
   el predicado
          ∃ A P : Prop
   significa que para algún a : A, P a es verdadero (está habitado).
   
   Una prueba para este tipo es un par dependiente (a , p) donde
       a : A es el "testigo", y 
       p : P a es la prueba de P a es verdadero (está habitado).
-}
data ∃ (A : Set)(P : A → prop) : prop where
  _,_ : (a : A) → P a → ∃ A P


{- Notar que la cuantificación universal (Π-type) es una primitiva
   del lenguaje, mientras que la existencial (Σ-type) la tuvimos
   que definir.  -}

∃∧ : {A : Set}{P Q : A → prop} → (∃ A (λ a → P a ∧ Q a))
                                → (∃ A P) ∧ (∃ A Q)
∃∧ (a , (p , q)) = (a , p) , (a , q)

{-
∧∃ : {A : Set}{P Q : A → prop} →
  (∃ A P) ∧ (∃ A Q) → (∃ A (λ a → P a ∧ Q a))
∧∃ ((a , p) , (a' , q)) = a , (p , {! q  !})

unprovable
-}

∃∨ : {A : Set}{P Q : A → prop} → 
  (∃ A (λ a → P a ∨ Q a)) → (∃ A P) ∨ (∃ A Q)
∃∨ (a , left p) = left (a , p)
∃∨ (a , right q) = right (a , q)

∨∃ : {A : Set}{P Q : A → prop} → 
  (∃ A P) ∨ (∃ A Q) → (∃ A (λ a → P a ∨ Q a))
∨∃ (left (a , p)) = a , (left p)
∨∃ (right (a , q)) = a , right q

------------------------------------------------------------
{- Ejercicio: las leyes de deMorgan infinitas -
      ¿Cuáles se pueden probar?
-}

{- ¬ (∃ x:A. P x) ⇔ ∀ x:A. ¬ P x -}
deMorgan¬∃ : {A : Set}{P : A → prop} →
           ¬ (∃ A (λ x → P x)) → ((x : A) → ¬ (P x))
deMorgan¬∃ ne a p = ne (a , p)

deMorgan∀¬ : {A : Set}{P : A → prop} →
           ((x : A) → ¬ (P x)) → ¬ (∃ A (λ x → P x))
deMorgan∀¬ f (a , p) = f a p 

{- ¬ (∀ x:A. P x) ⇔ ∃ x:A . ¬ P x -}
-- deMorgan¬∀ : {A : Set}{P : A → prop} →
--              ¬ ((x : A) → P x) → ∃ A (λ x → ¬ (P x))
-- deMorgan¬∀ x = {!!} unprovable, saldría con un contraejemplo

deMorgan∃¬ : {A : Set}{P : A → prop} →
           ∃ A (λ x → ¬ (P x)) → ¬ ((x : A) → P x)
deMorgan∃¬ (a , np) p = np (p a)

--------------------------------------------------
{- relación entre ∀ y ∃ -}

curry∀→ : {A : Set}{P : A → Set}{Q : prop}
         → ((∃ A P) → Q) → (a : A) → P a → Q
curry∀→ f a p = f (a , p)

curry∀← : {A : Set}{P : A → Set}{Q : prop}
         → ((a : A) → P a → Q) → ((∃ A P) → Q)
curry∀← f (a , p) = f a p

--------------------------------------------------
-- Ejercicios adicionales

{- Si bien en la logica constructiva no tenemos tercero excluído,
 Toda la lógica clásica se puede hacer dentro de la constructiva mediante
  la traducción de doble negación.
-}

¬¬ : prop → prop
¬¬ P = ¬ (¬ P)

pnnp : {P : prop} → P → ¬¬ P 
pnnp p np = np p

-- raa : {P : prop} → ¬¬ P → P
-- raa nnp = efq (nnp (λ x → nnp (λ x' → {!!}))) unprovable!

¬¬terex : {P : prop} → ¬¬ (P ∨ ¬ P) -- ¬ (¬ (P ∨ ¬ P) ) <--> ¬ ((P ∨ ¬ P) → ⊥) <--> ((P ∨ ¬ P) → ⊥) → ⊥ <--> ((P ∨ P → ⊥) → ⊥) → ⊥
¬¬terex ponp = ponp (right (λ p → ponp (left p)))

TerEx : Set₁
TerEx = {P : prop} → P ∨ ¬ P

RAA : Set₁
RAA = {P : prop} → ¬¬ P → P

RAA→TerEx : RAA → TerEx
RAA→TerEx raa = raa (λ nnp → nnp (right (λ ponp → nnp (left ponp)))) -- wtf

-- TerEx→RND : TerEx → RAA
-- TerEx→RND terex = {!!} unprovable?

ret¬¬ : {P : prop} → P → ¬¬ P -- P → ¬ (¬ P)
ret¬¬ p np = np p

bind¬¬ : {P Q : prop} → ¬¬ P → (P → ¬¬ Q) → ¬¬ Q 
bind¬¬ nnp pnnq nq = nnp (λ z₃ → pnnq z₃ nq)

map¬¬ : {P Q : prop} → ¬¬ P → (P → Q) → ¬¬ Q
map¬¬ nnp pq nq = nnp (λ z₃ → nq (pq z₃))

app¬¬ : {P Q : prop} → ¬¬ (P → Q) → ¬¬ P → ¬¬ Q
app¬¬ nnpq nnp nq = nnp (λ z₃ → nnpq (λ z₄ → nq (z₄ z₃)))

∧¬¬-1 : {P Q : prop} → ¬¬ (P ∧ Q) → ¬¬ P ∧ ¬¬ Q
∧¬¬-1 nnpyq = (λ np → nnpyq (λ pyq → np (fst pyq)))  , (λ nq → nnpyq (λ pyq → nq (snd pyq)))

∧¬¬-2 : {P Q : prop} → ¬¬ P ∧ ¬¬ Q → ¬¬ (P ∧ Q) 
∧¬¬-2 (nnp , nnq) npyq = nnp (λ p → nnq (λ q → npyq (p , q)))

∧¬¬ : {P Q : prop} → ¬¬ (P ∧ Q) ⇔ ¬¬ P ∧ ¬¬ Q
∧¬¬ = ∧¬¬-1 , ∧¬¬-2


-- ∨¬¬-1 : {P Q : prop} → ¬¬ (P ∨ Q) → ¬¬ P ∨ ¬¬ Q
-- ∨¬¬-1 nnpq = {!!}  unprovable!

∨¬¬-2 : {P Q : prop} → ¬¬ P ∨ ¬¬ Q → ¬¬ (P ∨ Q) 
∨¬¬-2 (left nnp) npoq = nnp (λ p → npoq (left p))
∨¬¬-2 (right nnq) npoq = nnq (λ q → npoq (right q))



-- ∨¬¬ : {P Q : prop} → ¬¬ (P ∨ Q) ⇔ ¬¬ P ∨ ¬¬ Q
-- ∨¬¬ = {!!} , ∨¬¬-2 unprovable!

¬¬deMorgan¬∧ : {P Q : prop} → ¬ (P ∧ Q) → ¬¬ ((¬ P) ∨ (¬ Q))
¬¬deMorgan¬∧ npyq nnponq = nnponq (left λ p → nnponq (right (λ q → npyq (p , q))))
-- misma técnica que en RAA→TerEx sumandole la magia de ir haciendo aparecer los argumentos como en los ultimos ejercicios, turbina
