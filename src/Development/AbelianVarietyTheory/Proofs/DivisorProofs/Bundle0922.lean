module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0873
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0012
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0882
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0886
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0004
public import Formalism.LocalToGlobal.Divisibility.LiftLatLemmas
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsEffectivePicClassAddIntegral
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory CategoryTheory.Hom.group

noncomputable section

namespace GlobalTheory.EffBound

open GlobalTheory.CechPic TopologicalSpace

theorem res_res_apply {X : Scheme.{0}} {U V W : X.Opens} (h₁ : V ≤ U) (h₂ : W ≤ V) (x : Γ(X, U)) :
    (X.presheaf.map (homOfLE h₂).op).hom ((X.presheaf.map (homOfLE h₁).op).hom x) =
      (X.presheaf.map (homOfLE (h₂.trans h₁)).op).hom x := by
  rw [← CommRingCat.comp_apply, ← Functor.map_comp]; rfl

theorem mul_compat {X : Scheme.{0}} {A₁ A₂ B₁ B₂ : X.Opens} (s₁ : Γ(X, A₁)) (s₂ : Γ(X, A₂))
    (t₁ : Γ(X, B₁)) (t₂ : Γ(X, B₂)) (gA : Γ(X, A₁ ⊓ A₂)ˣ) (gB : Γ(X, B₁ ⊓ B₂)ˣ)
    (hs : (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ A₂ ≤ A₁)).op).hom s₁ =
      (gA : Γ(X, A₁ ⊓ A₂)) * (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ A₂ ≤ A₂)).op).hom s₂)
    (ht : (X.presheaf.map (homOfLE (inf_le_left : B₁ ⊓ B₂ ≤ B₁)).op).hom t₁ =
      (gB : Γ(X, B₁ ⊓ B₂)) * (X.presheaf.map (homOfLE (inf_le_right : B₁ ⊓ B₂ ≤ B₂)).op).hom t₂) :
    (X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ B₁)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₁ ⊓ B₁ ≤ A₁)).op).hom s₁ *
          (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ≤ B₁)).op).hom t₁) =
      ((res (le_inf (inf_le_left.trans inf_le_left) (inf_le_right.trans inf_le_left) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂) gA *
        res (le_inf (inf_le_left.trans inf_le_right) (inf_le_right.trans inf_le_right) :
          A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂) gB : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))ˣ) : Γ(X, A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂))) *
      (X.presheaf.map (homOfLE (inf_le_right : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₂ ⊓ B₂)).op).hom
        ((X.presheaf.map (homOfLE (inf_le_left : A₂ ⊓ B₂ ≤ A₂)).op).hom s₂ *
          (X.presheaf.map (homOfLE (inf_le_right : A₂ ⊓ B₂ ≤ B₂)).op).hom t₂) := by
  have hσ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_left)
    (inf_le_right.trans inf_le_left) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ A₁ ⊓ A₂)).op).hom hs
  have hτ := congrArg (X.presheaf.map (homOfLE (le_inf (inf_le_left.trans inf_le_right)
    (inf_le_right.trans inf_le_right) : A₁ ⊓ B₁ ⊓ (A₂ ⊓ B₂) ≤ B₁ ⊓ B₂)).op).hom ht
  rw [res_res_apply, map_mul, res_res_apply] at hσ hτ
  simp only [res, Units.val_mul, Units.coe_map, MonoidHom.coe_coe, map_mul, res_res_apply]
  rw [hσ, hτ]
  ring

def tensSec {X : Scheme.{0}} {A B : LB X} (σ : LB.Sec A) (τ : LB.Sec B) : LB.Sec (tens A B) where
  f p := (X.presheaf.map (homOfLE (inf_le_left : A.U p.1 ⊓ B.U p.2 ≤ A.U p.1)).op).hom (σ.f p.1) *
    (X.presheaf.map (homOfLE (inf_le_right : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2)).op).hom (τ.f p.2)
  compat p q := mul_compat _ _ _ _ _ _ (σ.compat p.1 q.1) (τ.compat p.2 q.2)

theorem germ_sec_ne_zero {X : Scheme.{0}} [IsIntegral X] {N : LB X} (σ : LB.Sec N) {j : N.ι}
    (hj : σ.f j ≠ 0) (i : N.ι) (y : X) (hy : y ∈ N.U i) : X.presheaf.germ (N.U i) y hy (σ.f i) ≠ 0 := by
  intro h0
  have hi0 : σ.f i = 0 := germ_injective_of_isIntegral X y hy (by rw [h0, map_zero])
  apply hj
  by_cases hne : (N.U j : Set X).Nonempty
  · obtain ⟨z, hz⟩ := hne
    obtain ⟨w, hwi, hwj⟩ :=
      nonempty_preirreducible_inter (N.U i).isOpen (N.U j).isOpen ⟨y, hy⟩ ⟨z, hz⟩
    apply germ_injective_of_isIntegral X w hwj
    rw [map_zero]
    have hw : w ∈ N.U i ⊓ N.U j := ⟨hwi, hwj⟩
    have e := congrArg (X.presheaf.germ (N.U i ⊓ N.U j) w hw) (σ.compat i j)
    rw [X.presheaf.germ_res_apply, hi0, map_zero, map_mul, X.presheaf.germ_res_apply] at e
    rcases mul_eq_zero.mp e.symm with h | h
    · exact absurd h (((N.g i j).isUnit.map (X.presheaf.germ (N.U i ⊓ N.U j) w hw).hom).ne_zero)
    · exact h
  · have hT : N.U j = ⊥ := by
      ext x
      simp only [Opens.coe_bot, Set.mem_empty_iff_false, iff_false]
      exact fun hx => hne ⟨x, hx⟩
    haveI : Subsingleton Γ(X, N.U j) := CommRingCat.subsingleton_of_isTerminal (X.sheaf.isTerminalOfEqEmpty hT)
    exact Subsingleton.elim _ _

theorem eff_add {X : Scheme.{0}} [IsIntegral X] (a b : Pic X) (ha : Eff a) (hb : Eff b) : Eff (a + b) := by
  obtain ⟨A, hA, rfl, σ, j, hσ⟩ := ha
  obtain ⟨B, hB, rfl, τ, k, hτ⟩ := hb
  obtain ⟨y⟩ := (inferInstance : Nonempty X)
  have hyA : y ∈ ⨆ i, A.U i := hA.cover ▸ trivial
  have hyB : y ∈ ⨆ i, B.U i := hB.cover ▸ trivial
  obtain ⟨p, hp⟩ := Opens.mem_iSup.1 hyA
  obtain ⟨q, hq⟩ := Opens.mem_iSup.1 hyB
  refine ⟨tens A B, isLB_tens hA hB, cls_tens hA hB _, tensSec σ τ, (p, q), ?_⟩
  have hy : y ∈ A.U p ⊓ B.U q := ⟨hp, hq⟩
  intro h0
  have h0' : (X.presheaf.map (homOfLE (inf_le_left : A.U p ⊓ B.U q ≤ A.U p)).op).hom (σ.f p) *
      (X.presheaf.map (homOfLE (inf_le_right : A.U p ⊓ B.U q ≤ B.U q)).op).hom (τ.f q) = 0 := h0
  have e' := congrArg (X.presheaf.germ (A.U p ⊓ B.U q) y hy) h0'
  rw [map_mul, X.presheaf.germ_res_apply, X.presheaf.germ_res_apply, map_zero] at e'
  rcases mul_eq_zero.mp e' with h | h
  · exact germ_sec_ne_zero σ hσ p y hp h
  · exact germ_sec_ne_zero τ hτ q y hq h

end GlobalTheory.EffBound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
section
noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.RealLift

section OnePlace

variable {P Q R S : ℕ}

def IsLift (x t : ℚ) (M : GKMod R S) (pr : Formalism.BasicNotions.TH.Pol P Q R S →ₗ[ℂ] M.V) : Prop :=
  Function.Surjective pr ∧ (∀ X f, pr (fockAct1 P Q R S X f) = ((x : ℂ) * X.trace) • pr f) ∧
    ∀ Y f, M.act Y (pr f) = pr (fockAct2 P Q R S Y f) + ((t : ℂ) * Y.trace) • pr f

def lam (P Q R S : ℕ) (κ : ℤ) : Ix R S → ℚ
  | .inl i => if (i : ℕ) < P then (κ : ℚ) / 2 - cPair R S + cPair P Q else cPair P Q
  | .inr j => if (j : ℕ) < Q then (κ : ℚ) / 2 + cPair R S - cPair P Q else -cPair P Q

def casK (μ : Ix R S → ℚ) : ℚ :=
  ∑ a, μ a ^ 2 + (∑ i : Fin R, μ (.inl i) * ((R : ℚ) - 1 - 2 * (i : ℕ))) + ∑ j : Fin S, μ (.inr j) * ((S : ℚ) - 1 - 2 * (j : ℕ))

def GenBy (M : GKMod R S) (Λ : Ix R S → ℚ) : Prop := ∃ v, IsHW M.act Λ v ∧ genSub M.act {v} = ⊤

def ScalarEnd (M : GKMod R S) : Prop :=
  ∀ T : M.V →ₗ[ℂ] M.V, (∀ Z, T ∘ₗ M.act Z = M.act Z ∘ₗ T) → ∃ c : ℂ, T = c • LinearMap.id

def heisOp (c : Matrix (Ix P Q) (Ix R S) ℂ) : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S) :=
  ((Real.sqrt (2 * Real.pi) : ℝ) : ℂ) • ∑ l : Ln P Q R S,
    (c l.1 l.2 • raiB l - (lineSign (p := P) (q := Q) (r := R) (s := S) l.1 l.2 * star (c l.1 l.2)) • lowB l)

def IsFrame {α : Type} [Fintype α] [DecidableEq α] (M : Matrix α α ℂ) (A : Matrix α (Ix P Q) ℂ) : Prop :=
  Aᵀ * M * A.map star = Jm P Q ∧ ∃ A' : Matrix (Ix P Q) α ℂ, A * A' = 1

end OnePlace

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

def atPl (w : ι) (L : Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) :=
  PiTensorProduct.map (Function.update (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L)

def sumPl (L : ∀ w, Module.End ℂ (V w)) : Module.End ℂ (⨂[ℂ] i, V i) := ∑ w, atPl w (L w)

end Tensor

def LocFin {V : Type} [AddCommGroup V] [Module ℂ V] (L : Module.End ℂ V) : Prop :=
  ∀ v, ∃ N : Submodule ℂ V, FiniteDimensional ℂ N ∧ v ∈ N ∧ ∀ y ∈ N, L y ∈ N

def IsExp {V : Type} [AddCommGroup V] [Module ℂ V] (L U : Module.End ℂ V) : Prop :=
  ∀ (v : V) (l : V →ₗ[ℂ] ℂ), HasSum (fun n : ℕ => ((n.factorial : ℂ))⁻¹ * l ((L ^ n) v)) (l (U v))

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
  {α β κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] {P Q R S : ℕ}


variable (F) in
abbrev Tens (P Q R S : ℕ) : Type := ⨂[ℂ] _ : InfinitePlace F, Formalism.BasicNotions.TH.Pol P Q R S

def SD (T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), ∀ l ∈ (adeleClass F).adm κ, HasDerivAt (fun t => l (T t (pureA F f g))) (l (pureA F f₁ g)) 0

def SA (T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ) (f f₁ : SInf F κ) : Prop :=
  ∀ g ∈ SB (κ → Af F), T (pureA F f g) = pureA F f₁ g

def Framed (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E)) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ) : Prop :=
  a * b = Complex.I ∧ (∀ w, IsFrame (a • JA.map (piInf (τ w))) (A w)) ∧ ∀ w, IsFrame (b • JB.map (piInf (τ w))) (C w)

def IsFockMap (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) {JA : Matrix α α (AE F E)}
    {JB : Matrix β β (AE F E)} (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) : Prop :=
  Function.Injective Φ ∧ ∀ u : Matrix α β (AE F E), At (evI F) u → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
    (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      ∀ T, SD (fun t => d.rho ψ (realAd F t • u)) (Φ T) (Φ (sumPl (fun w => heisOp (c w)) T))


variable (σ) in
def RLines (J : Matrix β β (AE F E)) : Set (Multiplicative ℝ →* UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J) :=
  {γ | Continuous γ ∧ ∀ t, At (evI F) (((γ t).1 : Matrix β β (AE F E)) - 1)}

def IsGen (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (γ : Multiplicative ℝ →* UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J) (Y : InfinitePlace F → Mat R S) : Prop :=
  ∀ (t : ℝ) w, ((γ (Multiplicative.ofAdd t)).1 : Matrix β β (AE F E)).map (piInf (τ w)) * C w =
    C w * NormedSpace.exp (t • Y w)

def ActsBy (τ : ∀ w : InfinitePlace F, EmbOver E w) {J : Matrix β β (AE F E)} {r s : ℕ}
    (C : InfinitePlace F → Matrix β (Ix r s) ℂ) (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J →* Module.End ℂ ((κ → AF F) → ℂ))
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (act : Mat r s →ₗ[ℂ] Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S))
    (c : InfinitePlace F → ℂ) : Prop :=
  ∀ γ ∈ RLines (σ := σ) J, ∀ Y, IsGen τ C γ Y → ∀ T, SD (fun t => om (γ (Multiplicative.ofAdd t))) (Φ T)
    (Φ (sumPl (fun w => act (Y w) + (c w * (Y w).trace) • 1) T))

end Adelic

def ActsLaws : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] (f f₁ f₂ : SInf F κ),
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, (∀ t, T t 0 = 0) → SD T f f₁ → ActsD (evI F) T f f₁) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, T 0 = 0 → SA T f f₁ → Acts (evI F) T f f₁) ∧
    (∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, ActsD (evI F) T f f₁ → ActsD (evI F) T f f₂ → f₁ = f₂) ∧
    (∀ T : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, Acts (evI F) T f f₁ → Acts (evI F) T f f₂ → f₁ = f₂) ∧
    ∀ T : ℝ → ((κ → AF F) → ℂ) → (κ → AF F) → ℂ, SD T f f₁ → SD T f f₂ → f₁ = f₂

def DerEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (ψ : AddChar (AF F) ℂ) (JA : Matrix α α (AE F E))
    (JB : Matrix β β (AE F E)) (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ), (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    ∃ D : Matrix α β (AE F E) → (SInf F κ →L[ℂ] SInf F κ), ∀ u, At (evI F) u → ∀ f,
      SD (fun t => d.rho ψ (realAd F t • u)) f (D u f) ∧ ∀ x, D u f x =
        fderiv ℝ f x (fun i => evI F ((d.e u).1 i)) - 2 * Real.pi * Complex.I *
          (Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (∑ i, x i * evI F ((d.e u).2 i)) : ℝ) * f x

def FockEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → Framed τ JA JB a b A C →
    ∃ Φ, IsFockMap ψ τ d A C Φ

def VacLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → ∀ (f₀ : SInf F κ) (ε : InfinitePlace F → ℤˣ),
    (∀ u u' : Matrix α β (AE F E), At (evI F) u → At (evI F) u' → ∀ c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ,
      (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) →
      (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) →
      ∀ f f' : SInf F κ, SD (fun t => d.rho ψ (realAd F t • u)) f₀ f → SD (fun t => d.rho ψ (realAd F t • u')) f₀ f' →
        f' = Complex.I • f) →
    ∃ z : ℂ, f₀ = z • Φ (PiTensorProduct.tprod ℂ fun _ => 1)

def GenEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ γ ∈ RLines (σ := σ) J, ∃ Y, (∀ w, Y w ∈ upq R S) ∧ IsGen τ C γ Y

def LineEx : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ), IsCMExt F E σ → (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) →
    ∀ Y : InfinitePlace F → Mat R S, (∀ w, Y w ∈ upq R S) → ∃ γ ∈ RLines (σ := σ) J, IsGen τ C γ Y

def LieScalar : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUSplitting (adeleClass F) ψ d (actB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ)) om →
    ∃ c, ActsBy τ C om Φ (fockAct2 P Q R S) c

def LieSecond : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ)
    (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JB →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E) (m : InfinitePlace F → ℤ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ → IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) JA JB d χ om → HasExp τ χ m →
    ActsBy τ C om Φ (fockAct2 P Q R S) fun w => (m w : ℂ) / 2

def LieFirst : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (α β κ : Type) [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ) (ψ : AddChar (AF F) ℂ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (AE F E)) (JB : Matrix β β (AE F E))
    (d : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JA JB) κ) (d' : Darboux (symp (R := AF F) (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (-1) JB JA) κ) (a b : ℂ)
    (A : InfinitePlace F → Matrix α (Ix P Q) ℂ) (C : InfinitePlace F → Matrix β (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F κ) (om : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) JA →* Module.End ℂ ((κ → AF F) → ℂ)) (χ : Chr F E)
    (m : InfinitePlace F → ℤ), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) → Framed τ JA JB a b A C → IsFockMap ψ τ d A C Φ →
    (∀ x : Matrix α β (AE F E), d'.e xᵀ = d.e x) → IsUWeilB (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) (adeleClass F) ψ (-1) JB JA d' χ om → HasExp τ χ m →
    ActsBy τ A om Φ (fockAct1 P Q R S) fun w => (m w : ℂ) / 2

def KLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (β : Type) [Fintype β]
    [DecidableEq β] (R S : ℕ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (J : Matrix β β (AE F E)) (b : ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (θ : InfinitePlace F → Matrix β β ℂ), IsCMExt F E σ →
    (∀ w, IsFrame (b • J.map (piInf (τ w))) (C w)) → (∀ w, θ w * C w = C w * Jm R S) → ∀ k : UG (_root_.Algebra.TensorProduct.map (_root_.AlgHom.id (AF F) (AF F)) σ) J,
    At (evI F) ((k.1 : Matrix β β (AE F E)) - 1) → (∀ w, Commute ((k.1 : Matrix β β (AE F E)).map (piInf (τ w))) (θ w)) →
    ∃ γ ∈ RLines (σ := σ) J, ∃ Y, IsGen τ C γ Y ∧ (∀ w, IsKC (Y w)) ∧ γ (Multiplicative.ofAdd 1) = k

def FrameEx : Prop :=
  ∀ (n r s : ℕ) (M θ : Matrix (Fin n) (Fin n) ℂ), HasSig M r s → IsCartan M θ →
    ∃ A : Matrix (Fin n) (Ix r s) ℂ, IsFrame M A ∧ θ * A = A * Jm r s

def PolRange : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n d P Q R S : ℕ)
    (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (A : InfinitePlace F → Matrix (Fin n) (Ix P Q) ℂ) (C : InfinitePlace F → Matrix (Fin d) (Ix R S) ℂ)
    (Φ : Tens F P Q R S →ₗ[ℂ] SInf F (Fin n × Fin d)), IsCMExt F E σ → (_root_.Continuous ψ ∧ (∀ x : F, ψ (algebraMap F (AF F) x) = 1) ∧ ∀ a : (AF F), _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.At (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a → ψ a = _root_.Complex.exp (-(2 * _root_.Real.pi * _root_.Complex.I) * (_root_.Algebra.trace ℝ (_root_.NumberField.mixedEmbedding.mixedSpace F) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.evI (F := F)) a) : ℝ))) →
    Framed τ ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) X.J) ((_root_.Matrix.map · (_root_.Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.inclR (F := F) (AF F))) W.J) 1 Complex.I A C → (∀ w, X.θ w * A w = A w * Jm P Q) →
    (∀ w, W.θ w * C w = C w * Jm R S) → IsFockMap ψ τ M.co A C Φ → LinearMap.range Φ = M.Pol ψ τ

def Parity : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ w, Even (B.mα w - B.mβ w)

end GlobalTheory.RealLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntVZero
section
noncomputable section

open IsDedekindDomain GlobalTheory.LKTrip
open scoped TensorProduct

namespace GlobalTheory.OrbFinAf

variable {p : ℕ} [Fact p.Prime]

def iotaF (G : HTGroup p) (v : AwayP p) : Qv v ⊗[ℚ] G.F →ₐ[Qv v] Qv v ⊗[ℚ] G.C :=
  Algebra.TensorProduct.map (AlgHom.id (Qv v) (Qv v)) (IsScalarTower.toAlgHom ℚ G.F G.C)

theorem iotaF_tmul (G : HTGroup p) (v : AwayP p) (a : Qv v) (x : G.F) :
    iotaF G v (a ⊗ₜ[ℚ] x) = a ⊗ₜ[ℚ] algebraMap G.F G.C x := rfl

theorem isIntV_zero (G : HTGroup p) (v : AwayP p) : IsIntV G v 0 := fun i => by
  rw [map_zero, Finsupp.zero_apply]; exact zero_mem _

theorem isIntV_add' (G : HTGroup p) (v : AwayP p) {a b : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a)
    (hb : IsIntV G v b) : IsIntV G v (a + b) := fun i => by
  rw [map_add (f := _), Finsupp.add_apply]; exact add_mem (ha i) (hb i)

theorem isIntV_neg (G : HTGroup p) (v : AwayP p) {a : Qv v ⊗[ℚ] G.C} (ha : IsIntV G v a) :
    IsIntV G v (-a) := fun i => by
  rw [map_neg, Finsupp.neg_apply]; exact neg_mem (ha i)

theorem isIntV_sum (G : HTGroup p) (v : AwayP p) {ι : Type*} (s : Finset ι) (f : ι → Qv v ⊗[ℚ] G.C)
    (h : ∀ i ∈ s, IsIntV G v (f i)) : IsIntV G v (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isIntV_zero G v
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isIntV_add' G v (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

def intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) :
    Subring (Qv v ⊗[ℚ] G.F) where
  carrier := {m | IsIntV G v (iotaF G v m)}
  one_mem' := by simp only [Set.mem_setOf_eq, map_one]; exact h1
  mul_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_mul] at *; exact hm _ _ ha hb
  zero_mem' := by simp only [Set.mem_setOf_eq, map_zero]; exact isIntV_zero G v
  add_mem' {a b} ha hb := by simp only [Set.mem_setOf_eq, map_add (f := _)] at *; exact isIntV_add' G v ha hb
  neg_mem' {a} ha := by simp only [Set.mem_setOf_eq, map_neg] at *; exact isIntV_neg G v ha

theorem mem_intF (G : HTGroup p) (v : AwayP p) (h1 : IsIntV G v 1)
    (hm : ∀ y z : Qv v ⊗[ℚ] G.C, IsIntV G v y → IsIntV G v z → IsIntV G v (y * z)) (m : Qv v ⊗[ℚ] G.F) :
    m ∈ intF G v h1 hm ↔ IsIntV G v (iotaF G v m) := Iff.rfl

end GlobalTheory.OrbFinAf
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralOfIsIntegralConj
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.LocIntSpan

theorem exists_finset_algebraMap_mem (s : Finset ℚ) :
    ∃ S : Finset (HeightOneSpectrum ℤ), ∀ v ∉ S, ∀ q ∈ s,
      algebraMap ℚ (v.adicCompletion ℚ) q ∈ v.adicCompletionIntegers ℚ := by
  let d : ℤ := ∏ q ∈ s, (q.den : ℤ)
  have hd : d ≠ 0 := Finset.prod_ne_zero_iff.2 fun q _ => by exact_mod_cast q.den_nz
  have hfin : {v : HeightOneSpectrum ℤ | v.asIdeal ∣ Ideal.span {d}}.Finite :=
    Ideal.finite_factors (by simpa [Ideal.span_singleton_eq_bot] using hd)
  refine ⟨hfin.toFinset, fun v hv q hq => ?_⟩
  have hden : (q.den : ℤ) ∉ v.asIdeal := by
    intro h
    apply hv
    rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]
    exact Ideal.mem_of_dvd _ (Finset.dvd_prod_of_mem _ hq) h
  rw [HeightOneSpectrum.mem_adicCompletionIntegers]
  have e : Valued.v (algebraMap ℚ (v.adicCompletion ℚ) q) = v.valuation ℚ q :=
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v q
  rw [e]
  have hq' : q = ((q.num : ℤ) : ℚ) / ((q.den : ℤ) : ℚ) := by
    push_cast; exact (Rat.num_div_den q).symm
  rw [hq', map_div₀]
  have h1 : v.valuation ℚ ((q.num : ℤ) : ℚ) ≤ 1 := by
    rw [show ((q.num : ℤ) : ℚ) = algebraMap ℤ ℚ q.num from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact v.intValuation_le_one _
  have h2 : v.valuation ℚ ((q.den : ℤ) : ℚ) = 1 := by
    rw [show ((q.den : ℤ) : ℚ) = algebraMap ℤ ℚ q.den from rfl, HeightOneSpectrum.valuation_of_algebraMap]
    exact le_antisymm (v.intValuation_le_one _)
      (not_lt.1 fun h => hden ((v.intValuation_lt_one_iff_mem _).1 h))
  rw [h2, div_one]
  exact h1

theorem isIntegral_of_isIntegral_conj {R A : Type} [CommRing R] [Ring A] [Algebra R A] (X : Aˣ) (y : A)
    (h : IsIntegral R (↑X * y * ↑X⁻¹)) : IsIntegral R y := by
  let f : A →ₐ[R] A :=
    { toFun := fun z => ↑X⁻¹ * z * ↑X
      map_one' := by simp
      map_mul' := fun a b => by simp [mul_assoc]
      map_zero' := by simp
      map_add' := fun a b => by simp [mul_add, add_mul]
      commutes' := fun r => by
        show _ * _ * _ = _
        rw [mul_assoc, Algebra.commutes, Units.inv_mul_cancel_left] }
  have := h.map f
  simpa [f, mul_assoc] using this

theorem map_id_injective (K : Type) [CommRing K] [Algebra ℚ K] {L C : Type} [Ring L] [Algebra ℚ L] [Ring C]
    [Algebra ℚ C] (ι : L →ₐ[ℚ] C) (hι : Function.Injective ι) :
    Function.Injective (Algebra.TensorProduct.map (AlgHom.id ℚ K) ι) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := K) ι.toLinearMap hι

theorem mem_of_isIntegral (v : HeightOneSpectrum ℤ) {x : v.adicCompletion ℚ}
    (hx : IsIntegral (v.adicCompletionIntegers ℚ) x) : x ∈ v.adicCompletionIntegers ℚ := by
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.isIntegral_iff.1 hx
  exact y.2

theorem trace_one_tmul' {F E : Type} [Field F] [Field E] [Algebra F E] [Module.Finite F E]
    (R : Type) [CommRing R] [Algebra F R] (e : E) :
    Algebra.trace R (R ⊗[F] E) ((1 : R) ⊗ₜ[F] e) = algebraMap F R (Algebra.trace F E e) := by
  rw [Algebra.trace_apply, Algebra.trace_apply, ← Algebra.baseChange_lmul, LinearMap.trace_baseChange]

end GlobalTheory.LocIntSpan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenLevelGroupFiniteAdelic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Polynomial
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.CuspMult

namespace GlobalTheory.LevelOpen

theorem isOpen_levG : ∀ {D : D7} (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (L : LevDat D.host.E ℂ V.rank), IsOpen {g : GfC V | (g : GA D V) ∈ levG V β L} := by
  intro D V β L
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  obtain ⟨U, hU, hle⟩ := GlobalTheory.GoodFiniteDim.exists_open_subgroup V β L
  have h1 : IsOpen ((U.subgroupOf (GfC V) : Subgroup (GfC V)) : Set (GfC V)) := hU.preimage continuous_subtype_val
  exact Subgroup.isOpen_mono (H₂ := (levG V β L).subgroupOf (GfC V)) (fun g hg => (hle g.1 hg g.2).1) h1

end GlobalTheory.LevelOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSmallB
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount IsDedekindDomain GlobalTheory.AdicSpan
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.AdicSpan

def IsSmallB (v : HeightOneSpectrum ℤ) {M : Type} [AddCommGroup M] [Module ℚ M] {κ : Type}
    (b : Module.Basis κ ℚ M) (y : v.adicCompletion ℚ ⊗[ℚ] M) : Prop :=
  ∀ i, Valued.v ((Algebra.TensorProduct.basis (v.adicCompletion ℚ) b).repr y i) < 1

end GlobalTheory.AdicSpan
end
end

