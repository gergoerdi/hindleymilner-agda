module HindleyMilner where

open import Data.Nat
open import Data.Bool
open import Data.Fin
open import Data.Fin.Props renaming (_≟_ to _F≟_)
open import Data.List
open import Data.List.All using (All; []; _∷_)
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
  _t+_ _t×_ : (τ₁ : Type p m) → (τ₂ : Type p m) → Type p m

infixr 20 _↣_
infixr 19 _t+_ _t×_

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
conType cLeft = Poly 2 $ let α = tPoly zero; β = tPoly (suc zero) in α ↣ (α t+ β)
conType cRight = Poly 2 $ let α = tPoly zero; β = tPoly (suc zero) in β ↣ (α t+ β)
conType cProd = Poly 2 $ let α = tPoly zero; β = tPoly (suc zero) in α ↣ β ↣ (α t× β)

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
inst Θ (τ₁ t+ τ₂) = (inst Θ τ₁) t+ (inst Θ τ₂)
inst Θ (τ₁ t× τ₂) = (inst Θ τ₁) t× (inst Θ τ₂)

TCtxt : ℕ → ℕ → Set
TCtxt m = Vec (PolyType m)

rigidVarsOf : ∀ {p m} → Type p m → List (TRigid m)
rigidVarsOf (tPoly α) = []
rigidVarsOf (tRigid a) = [ a ]
rigidVarsOf (τ₁ ↣ τ₂) = rigidVarsOf τ₁ ++ rigidVarsOf τ₂
rigidVarsOf tUnit = []
rigidVarsOf tBool = []
rigidVarsOf tNat = []
rigidVarsOf (τ₁ t+ τ₂) = rigidVarsOf τ₁ ++ rigidVarsOf τ₂
rigidVarsOf (τ₁ t× τ₂) = rigidVarsOf τ₁ ++ rigidVarsOf τ₂

data Flex {p} : ∀ {m} → Type p m → Set where
  flPoly : ∀ {m α} → Flex {m = m} (tPoly α)
  flRigid : ∀ {m a} → Flex {m = suc m} (tRigid (suc a))
  flFun : ∀ {m τ₁ τ₂} → Flex {m = m} τ₁ → Flex {m = m} τ₂ → Flex (τ₁ ↣ τ₂)
  flUnit : ∀ {m} → Flex {m = m} tUnit
  flBool : ∀ {m} → Flex {m = m} tBool
  flNat :  ∀ {m} → Flex {m = m} tNat
  flSum : ∀ {m τ₁ τ₂} → Flex {m = m} τ₁ → Flex {m = m} τ₂ → Flex (τ₁ t+ τ₂)
  flProd : ∀ {m τ₁ τ₂} → Flex {m = m} τ₁ → Flex {m = m} τ₂ → Flex (τ₁ t× τ₂)

flex : ∀ {p m} → (τ : Type p (suc m)) → Flex τ → Type p m
flex (tPoly α) flPoly = tPoly α
flex (tRigid .(suc a)) (flRigid {a = a}) = tRigid a
flex (τ₁ ↣ τ₂) (flFun fl₁ fl₂) = (flex τ₁ fl₁) ↣ (flex τ₂ fl₂)
flex tUnit flUnit = tUnit
flex tNat flNat = tNat
flex tBool flBool = tBool
flex (τ₁ t+ τ₂) (flSum fl₁ fl₂) = (flex τ₁ fl₁) t+ (flex τ₂ fl₂)
flex (τ₁ t× τ₂) (flProd fl₁ fl₂) = (flex τ₁ fl₁) t× (flex τ₂ fl₂)

Flex⋆ : ∀ {m n} → TCtxt m n → Set
Flex⋆ {m} {n} Γ = All check (Vec.toList Γ)
  where
  check : PolyType m → Set
  check (Poly p τ) = Flex τ

gen : ∀ {m} → PolyType (suc m) → PolyType m
gen {m} (Poly p τ) = Poly (suc p) (go τ)
  where
  go : Type p (suc m) → Type (suc p) m
  go (tPoly α) = tPoly (suc α)
  go (tRigid zero) = tPoly zero
  go (tRigid (suc a)) = tRigid a
  go (τ₁ ↣ τ₂) = go τ₁ ↣ go τ₂
  go tUnit = tUnit
  go tBool = tBool
  go tNat = tNat
  go (τ₁ t+ τ₂) = (go τ₁) t+ (go τ₂)
  go (τ₁ t× τ₂) = (go τ₁) t× (go τ₂)

genCtxt : ∀ {m n} → (Γ : TCtxt (suc m) n) → Flex⋆ Γ → TCtxt m n
genCtxt [] [] = []
genCtxt (Poly p τ ∷ Γ) (nf ∷ nf⋆) = Poly p (flex τ nf) ∷ (genCtxt Γ nf⋆)

mutual
  data _#_⊢′_∷_ {n : ℕ} : (m : ℕ) → (Γ : TCtxt m n) → Expr n → PolyType m → Set where
    tCon : ∀ {m Γ} {con} → m # Γ ⊢′ (C con) ∷ conType con
    tVar : ∀ {m Γ} {i} → m # Γ ⊢′ (Var i) ∷ lookup i Γ
    tGen₀ : ∀ {m Γ} {E τ} → m # Γ ⊢ E ∷ τ → m # Γ ⊢′ E ∷ Mono τ
    tGen : ∀ {m Γ} {E σ} → {flex : Flex⋆ Γ} → suc m # Γ ⊢′ E ∷ σ → m # (genCtxt Γ flex) ⊢′ E ∷ gen σ

  data _#_⊢_∷_ {n : ℕ} : (m : ℕ) → (Γ : TCtxt m n) → Expr n → MonoType m → Set where
    tInst : ∀ {m Γ} {p τ E} → (Θ : Inst p m) → (tPoly : m # Γ ⊢′ E ∷ Poly p τ)
          → m # Γ ⊢ E ∷ (inst Θ τ)

    tAbs : ∀ {m Γ} → (τ : MonoType m) → ∀ {E τ′} → (tBody : m # (Mono τ ∷ Γ) ⊢ E ∷ τ′)
         → m # Γ ⊢ Abs E ∷ τ ↣ τ′
    tApp : ∀ {m Γ} {τ τ′ E₁ E₂} → (tFun : m # Γ ⊢ E₁ ∷ τ ↣ τ′) → (tArg : m # Γ ⊢ E₂ ∷ τ)
         → m # Γ ⊢ E₁ · E₂ ∷ τ′

    tLet : ∀ {m Γ} {E₀ E σ τ} → (tBind : m # Γ ⊢′ E₀ ∷ σ) → (tBody : m # (σ ∷ Γ) ⊢ E ∷ τ)
         → m # Γ ⊢ Let E₀ In E ∷ τ

    tFix : ∀ {m Γ} {E τ} → (tBody : m # Γ ⊢ E ∷ τ ↣ τ)
         → m # Γ ⊢ Fix E ∷ τ

⊢_∷_ : Expr 0 → PolyType 0 → Set
⊢ E ∷ σ = 0 # [] ⊢′ E ∷ σ

module Examples where
  module Id where
    {-
      id = λ x → x
    -}
    #id : ∀ {n} → Expr n
    #id = Abs $ Var zero

    module _ where
      α : Type 1 0
      α = tPoly zero

      a : Type 0 1
      a = tRigid zero

      t : ⊢ #id ∷ Poly 1 (α ↣ α)
      t = tGen {Γ = []} {flex = []} $ tGen₀ $
          tAbs a $ tInst (λ ()) $ tVar

  module Const where
    {-
      const = λ x y → x
    -}
    #const : ∀ {n} → Expr n
    #const = Abs $ Abs $ Var (suc zero)

    module _ where
      α β : Type 2 0
      α = tPoly zero
      β = tPoly (suc zero)

      a b : Type 0 2
      a = tRigid zero
      b = tRigid (suc zero)

      T#const′ : 2 # [] ⊢ #const ∷ b ↣ a ↣ b
      T#const′ = tAbs b $ tAbs a $ tInst (λ ()) tVar

      T#const : ⊢ #const ∷ Poly 2 (α ↣ β ↣ α)
      T#const = tGen $ tGen $ tGen₀ T#const′

  ⟨_,_⟩ : ∀ {n} → Expr n → Expr n → Expr n
  ⟨ x , y ⟩ = C cProd · x · y

  module Mono where
    {-
      λ x → let f = λ y → x
            in (f, f)
    -}
    #mono : ∀ {n} → Expr n
    #mono = Abs $ Let (Abs $ Var (suc zero)) In ⟨ Var zero , Var zero ⟩

    module _ where
      α β γ : Type 3 0
      α = tPoly zero
      β = tPoly (suc zero)
      γ = tPoly (suc (suc zero))

      a : ∀ {m} → Type 0 (suc m)
      a = tRigid zero

      b : Type 0 {!!}
      b = tRigid (suc zero)

      c : Type 0 {!!}
      c = tRigid (suc (suc zero))

      T#mono : ⊢ #mono ∷ Poly 3 (α ↣ ((β ↣ α) t× (γ ↣ α)))
      T#mono = tGen $ tGen $ tGen $ tGen₀ $
               tAbs a $ tLet (tGen $ tGen₀ $ tAbs a $ tInst (λ ()) tVar) $
               tApp (tApp (tInst Θ₁ tCon) (tInst (λ _ → b) tVar)) (tInst (λ _ → c) tVar)
        where
          Θ₁ : TRigid 2 → Type 0 3
          Θ₁ zero = b ↣ a
          Θ₁ (suc zero) = c ↣ a
          Θ₁ (suc (suc ()))
