module HindleyMilner where

open import Data.Nat
open import Data.Bool
open import Data.Fin
open import Data.Fin.Props renaming (_≟_ to _F≟_)
open import Data.List hiding (any)
open import Data.List.Any using (any)
open import Data.Vec as Vec using (Vec; lookup; _∷_; [])
open import Function using (_$_)
open import Relation.Nullary.Core
open import Relation.Nullary.Decidable

data Con : Set where
  cUnit : Con
  cNat : ℕ → Con
  cBool : Bool → Con
  cLeft cRight cProd : Con

data Expr : ℕ → Set where
  C : ∀ {n} → Con → Expr n
  Var : ∀ {n} → Fin n → Expr n
  Abs : ∀ {n} → Expr (suc n) → Expr n
  _·_ : ∀ {n} → Expr n → Expr n → Expr n
  Let_In_ : ∀ {n} → Expr n → Expr (suc n) → Expr n
  Fix : ∀ {n} → Expr n → Expr n

infixl 20 _·_

TPoly : ℕ → Set
TPoly = Fin

TRigid : ℕ → Set
TRigid = Fin

data Type (p m : ℕ) : Set where
  tPoly : (α : TPoly p) → Type p m
  tRigid : (a : TRigid m) → Type p m
  _↣_ : (τ₁ : Type p m) → (τ₂ : Type p m) → Type p m
  tUnit tNat tBool : Type p m
  tSum tProd : (τ₁ : Type p m) → (τ₂ : Type p m) → Type p m

infixr 20 _↣_

record PolyType (m : ℕ) : Set where
  constructor Poly
  field
    p : ℕ
    τ : Type p m

Mono : ∀ {m} → Type 0 m → PolyType m
Mono = Poly 0

conType : ∀ {m} → Con → PolyType m
conType cUnit = Mono tUnit
conType (cNat _) = Mono tNat
conType (cBool _) = Mono tBool
conType cLeft = Poly 2 $ let α = tPoly zero; β = tPoly (suc zero) in α ↣ tSum α β
conType cRight = Poly 2 $ let α = tPoly zero; β = tPoly (suc zero) in β ↣ tSum α β
conType cProd = Poly 2 $ let α = tPoly zero; β = tPoly (suc zero) in α ↣ β ↣ tProd α β

gen : ∀ {m} → TRigid m → PolyType m → PolyType m
gen {m} a (Poly p τ) = Poly (suc p) (go τ)
  where
  go : Type p m → Type (suc p) m
  go (tPoly α) = tPoly (suc α)
  go (tRigid b) with b F≟ a
  go (tRigid b) | yes b≡a = tPoly zero
  go (tRigid b) | no b≠a = tRigid b
  go (τ₁ ↣ τ₂) = go τ₁ ↣ go τ₂
  go tUnit = tUnit
  go tBool = tBool
  go tNat = tNat
  go (tSum τ₁ τ₂) = tSum (go τ₁) (go τ₂)
  go (tProd τ₁ τ₂) = tProd (go τ₁) (go τ₂)

data Simp {p m : ℕ} : Type p m → Type p 0 → Set where
  sPoly : ∀ {α} → Simp (tPoly α) (tPoly α)
  sFun : ∀ {τ₁ τ₁′ τ₂ τ₂′} → Simp τ₁ τ₁′ → Simp τ₂ τ₂′ → Simp (τ₁ ↣ τ₂) (τ₁′ ↣ τ₂′)

MonoType : ℕ → Set
MonoType = Type 0

Inst : ℕ → ℕ → Set
Inst p m = TPoly p → MonoType m

inst : ∀ {p m} → Inst p m → Type p m → MonoType m
inst Θ (tPoly α) = Θ α
inst Θ (tRigid a) = tRigid a
inst Θ (τ₁ ↣ τ₂) = (inst Θ τ₁) ↣ (inst Θ τ₂)
inst θ tUnit = tUnit
inst θ tBool = tBool
inst θ tNat = tNat
inst Θ (tSum τ₁ τ₂) = tSum (inst Θ τ₁) (inst Θ τ₂)
inst Θ (tProd τ₁ τ₂) = tProd (inst Θ τ₁) (inst Θ τ₂)

TCtxt : ℕ → ℕ → Set
TCtxt m = Vec (PolyType m)

rigidVarsOf : ∀ {p m} → Type p m → List (TRigid m)
rigidVarsOf (tPoly α) = []
rigidVarsOf (tRigid a) = [ a ]
rigidVarsOf (τ₁ ↣ τ₂) = rigidVarsOf τ₁ ++ rigidVarsOf τ₂
rigidVarsOf tUnit = []
rigidVarsOf tBool = []
rigidVarsOf tNat = []
rigidVarsOf (tSum τ₁ τ₂) = rigidVarsOf τ₁ ++ rigidVarsOf τ₂
rigidVarsOf (tProd τ₁ τ₂) = rigidVarsOf τ₁ ++ rigidVarsOf τ₂

NonFree : ∀ {m n} → TCtxt m n → TRigid m → Set
NonFree {m} Γ b = False $ any (_F≟_ b) (concatMap monoVarsOfPoly (Vec.toList Γ))
  where
  monoVarsOfPoly : PolyType m → List (TRigid m)
  monoVarsOfPoly (Poly p τ) = rigidVarsOf τ

mutual
  data _#_⊢′_∷_ {n : ℕ} (m : ℕ) (Γ : TCtxt m n) : Expr n → PolyType m → Set where
    tCon : ∀ {con} → m # Γ ⊢′ (C con) ∷ conType con
    tVar : ∀ {i} → m # Γ ⊢′ (Var i) ∷ lookup i Γ
    tGen₀ : ∀ {E τ} → m # Γ ⊢ E ∷ τ → m # Γ ⊢′ E ∷ Mono τ
    tGen : ∀ {E σ} → (a : TRigid m) → {nonfree : NonFree Γ a} → m # Γ ⊢′ E ∷ σ → m # Γ ⊢′ E ∷ gen a σ

  data _#_⊢_∷_ {n : ℕ} (m : ℕ) (Γ : TCtxt m n) : Expr n → MonoType m → Set where
    tInst : ∀ {p τ E} → (Θ : Inst p m) → (tPoly : m # Γ ⊢′ E ∷ Poly p τ)
          → m # Γ ⊢ E ∷ (inst Θ τ)

    tAbs : (τ : MonoType m) → ∀ {E τ′} → (tBody : m # (Mono τ ∷ Γ) ⊢ E ∷ τ′)
         → m # Γ ⊢ Abs E ∷ τ ↣ τ′
    tApp : ∀ {τ τ′ E₁ E₂} → (tFun : m # Γ ⊢ E₁ ∷ τ ↣ τ′) → (tArg : m # Γ ⊢ E₂ ∷ τ)
         → m # Γ ⊢ E₁ · E₂ ∷ τ′

    tLet : ∀ {E₀ E σ τ} → (tBind : m # Γ ⊢′ E₀ ∷ σ) → (tBody : m # (σ ∷ Γ) ⊢ E ∷ τ)
         → m # Γ ⊢ Let E₀ In E ∷ τ

    tFix : ∀ {E τ} → (tBody : m # Γ ⊢ E ∷ τ ↣ τ)
         → m # Γ ⊢ Fix E ∷ τ

_#⊢_∷_ : (m : ℕ) → Expr 0 → PolyType m → Set
m #⊢ E ∷ σ = m # [] ⊢′ E ∷ σ

module Examples where
  module Id where
    {-
      id = λ x → x
    -}
    #id : ∀ {n} → Expr n
    #id = Abs $ Var zero

    module _ where
      α : Type 1 1
      α = tPoly zero

      a : Type 0 1
      a = tRigid zero

      t : 1 #⊢ #id ∷ Poly 1 (α ↣ α)
      t = tGen zero $ tGen₀ $
          tAbs a $ tInst (λ ()) $ tVar

  module Const where
    {-
      const = λ x y → x
    -}
    #const : ∀ {n} → Expr n
    #const = Abs $ Abs $ Var (suc zero)

    module _ where
      α β : Type 2 2
      α = tPoly zero
      β = tPoly (suc zero)

      a b : Type 0 2
      a = tRigid zero
      b = tRigid (suc zero)

      T#const′ : 2 # [] ⊢ #const ∷ a ↣ b ↣ a
      T#const′ = tAbs a $ tAbs b $ tInst (λ ()) tVar

      T#const : 2 #⊢ #const ∷ Poly 2 (α ↣ β ↣ α)
      T#const = tGen zero $ tGen (suc zero) $ tGen₀ T#const′

  ⟨_,_⟩ : ∀ {n} → Expr n → Expr n → Expr n
  ⟨ x , y ⟩ = C cProd · x · y

  ⟨_×_⟩ : ∀ {p m} → Type p m → Type p m → Type p m
  ⟨_×_⟩ = tProd
  infix 19 ⟨_×_⟩

  module Mono where
    {-
      λ x → let f = λ y → x
            in (f, f)
    -}
    #mono : ∀ {n} → Expr n
    #mono = Abs $ Let (Abs $ Var (suc zero)) In ⟨ Var zero , Var zero ⟩

    module _ where
      α β γ : Type 3 3
      α = tPoly zero
      β = tPoly (suc zero)
      γ = tPoly (suc (suc zero))

      a b c : Type 0 3
      a = tRigid zero
      b = tRigid (suc zero)
      c = tRigid (suc (suc zero))

      T#mono : 3 #⊢ #mono ∷ Poly 3 (α ↣ ⟨ β ↣ α × γ ↣ α ⟩)
      T#mono = tGen zero $ tGen (suc zero) $ tGen (suc (suc zero)) $ tGen₀ $
               tAbs a $ tLet (tGen (suc zero) $ tGen₀ $ tAbs b $ tInst (λ ()) tVar) $
               tApp (tApp (tInst Θ₁ tCon) (tInst (λ _ → b) tVar)) (tInst (λ _ → c) tVar)
        where
          Θ₁ : TRigid 2 → Type 0 3
          Θ₁ zero = b ↣ a
          Θ₁ (suc zero) = c ↣ a
          Θ₁ (suc (suc ()))
