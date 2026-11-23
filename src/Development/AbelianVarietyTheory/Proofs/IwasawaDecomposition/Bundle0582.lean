module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0575
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0526
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0564
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0474
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0034
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0031
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0572
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0570
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.NonemptyFiniteRootsOfBimul
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Defs

variable {O : Type} [CommRing O] (bar : O → O) (q : ℕ)

def InRCone {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (β : LinearMap.BilinForm ℤ X) :
    Prop :=
  ∃ c : Fin m → ℝ, (∀ i, 0 ≤ c i) ∧ toReal β = ∑ i, c i • toReal (γ i)

def genRank {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) : ℕ :=
  Module.finrank ℤ (Submodule.span ℤ (Set.range γ))

def IsCarrierDim (ψ lab : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      lab.evalZ β = ((sInf {k : ℕ | ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧ InRCone γ β ∧
        genRank γ = k} : ℕ) : ℝ)

def IsBaryStage (ψ lab φ : InvFun O) (i : ℕ) : Prop :=
  IsPolyFan bar q φ ∧ Subordinate bar q φ ψ ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar φ γ →
      ∃ (b a : ℕ) (v : Fin b → LinearMap.BilinForm ℤ X) (u : Fin a → LinearMap.BilinForm ℤ X),
        IsCell bar φ (Fin.append v u) ∧ IsCell bar ψ v ∧ (∀ j, InRCone (Fin.append v u) (γ j)) ∧
        Function.Injective (fun j => lab.evalZ (u j)) ∧ (∀ j, (i : ℝ) < lab.evalZ (u j)) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone v β → lab.evalZ β ≤ i) ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone (Fin.append v u) β → ¬ InRCone v β → (i : ℝ) < lab.evalZ β) ∧
        ∀ (d : Fin b → ℤ) (c : Fin a → ℤ), ∑ j, c j • u j = ∑ k, d k • v k → c = 0

def IsCentreSet (ψ w : InvFun O) : Prop :=
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 0 ∨ w.evalZ β = 1) ∧
    (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → w.evalZ β = 1 →
      ∀ (k : ℕ) (β' : LinearMap.BilinForm ℤ X), (k : ℤ) • β' = β → k = 1) ∧
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∀ β' ∈ balForms bar X, (∀ y, 0 ≤ β' y y) →
        w.evalZ β = 1 → w.evalZ β' = 1 → InRCone γ β → InRCone γ β' → β = β'

def IsFaceCut {X : Type} [AddCommGroup X] {m m' : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m)
    (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) : Prop :=
  (∀ j, 0 ≤ h (γ j)) ∧ ∀ j, h (γ j) = 0 ↔ j ∈ Set.range s

def IsStarOf (ψ w ψ' : InvFun O) : Prop :=
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsCell bar ψ' γ) ∧
  (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
      ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
          IsCell bar ψ' (Fin.cons β₀ fun j => γ (s j))) ∧
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
    ∀ (n : ℕ) (γ' : Fin n → LinearMap.BilinForm ℤ X), IsCell bar ψ' γ' →
      (∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ ∧
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) ∧ ∀ j, InRCone γ (γ' j)) ∨
      ∃ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (β₀ : LinearMap.BilinForm ℤ X) (m' : ℕ) (s : Fin m' ↪ Fin m)
        (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsCell bar ψ γ ∧ β₀ ∈ balForms bar X ∧ (∀ y, 0 ≤ β₀ y y) ∧
        w.evalZ β₀ = 1 ∧ InRCone γ β₀ ∧ IsFaceCut γ s h ∧ 0 < h β₀ ∧
        ∀ j, InRCone (Fin.cons β₀ fun j => γ (s j)) (γ' j)

end Defs

section Basic

variable {O : Type} [CommRing O] {bar : O → O} {q : ℕ}

theorem inRCone_self {X : Type} [AddCommGroup X] {m : ℕ} (γ : Fin m → LinearMap.BilinForm ℤ X) (j : Fin m) :
    InRCone γ (γ j) :=
  ⟨Pi.single j 1, fun i => by by_cases h : i = j <;> simp [Pi.single_apply, h], by
    rw [Finset.sum_eq_single j (fun i _ hi => by simp [Pi.single_apply, hi]) (by simp)]
    simp⟩

theorem isBaryStage_start {ψ lab : InvFun O} (hψ : IsPolyFan bar q ψ) {N : ℕ}
    (hN : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Module.finrank O X ≤ q →
      ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → lab.evalZ β ≤ N) :
    IsBaryStage bar q ψ lab ψ N := by
  refine ⟨hψ, Subordinate.refl ψ, fun X _ _ _ _ hX m γ hγ => ?_⟩
  have e : Fin.append γ (Fin.elim0 : Fin 0 → LinearMap.BilinForm ℤ X) = γ := by
    funext i; simp [Fin.append_elim0]
  refine ⟨m, 0, γ, Fin.elim0, by rw [e]; exact hγ, hγ, fun j => by rw [e]; exact inRCone_self γ j,
    fun i => i.elim0, fun i => i.elim0, fun β hβ hp _ => hN X hX β hβ hp, fun β _ _ h h' => (h' (e ▸ h)).elim,
    fun d c _ => funext fun i => i.elim0⟩

end Basic

end GlobalTheory.PolFan
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictIff
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X] {m : ℕ}

def linW (w : (X × X) →₀ ℤ) : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ where
  toFun β := w.sum fun p k => k * β p.1 p.2
  map_add' β γ := by
    simp only [LinearMap.add_apply, mul_add]
    exact Finsupp.sum_add
  map_smul' c β := by
    simp only [LinearMap.smul_apply, smul_eq_mul, RingHom.id_apply, Finsupp.mul_sum]
    exact Finsupp.sum_congr fun _ _ => by ring

def evalW (w : (X × X) →₀ ℤ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : ℝ := w.sum fun p k => (k : ℝ) * B p.1 p.2

theorem linW_apply (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : linW w β = w.sum fun p k => k * β p.1 p.2 := rfl

theorem evalW_toReal (w : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) : evalW w (toReal β) = linW w β := by
  simp [evalW, linW_apply, Finsupp.sum]

theorem evalW_add (w : (X × X) →₀ ℤ) (B B' : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (B + B') = evalW w B + evalW w B' := by
  simp only [evalW, LinearMap.add_apply, mul_add]
  exact Finsupp.sum_add

theorem evalW_smul (w : (X × X) →₀ ℤ) (t : ℝ) (B : X →ₗ[ℤ] X →ₗ[ℤ] ℝ) : evalW w (t • B) = t * evalW w B := by
  simp only [evalW, LinearMap.smul_apply, smul_eq_mul, Finsupp.mul_sum]
  exact Finsupp.sum_congr fun _ _ => by ring

def evalWL (w : (X × X) →₀ ℤ) : (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) →ₗ[ℝ] ℝ where
  toFun := evalW w
  map_add' := evalW_add w
  map_smul' t B := evalW_smul w t B

theorem evalW_sum (w : (X × X) →₀ ℤ) (t : Fin m → ℝ) (u : Fin m → LinearMap.BilinForm ℤ X) :
    evalW w (∑ i, t i • toReal (u i)) = ∑ i, t i * linW w (u i) := by
  have := map_sum (evalWL w) (fun i => t i • toReal (u i)) Finset.univ
  simp only [evalWL, LinearMap.coe_mk, AddHom.coe_mk] at this
  rw [this]
  exact Finset.sum_congr rfl fun i _ => by rw [evalW_smul, evalW_toReal]

def rcone (u : Fin m → LinearMap.BilinForm ℤ X) : Set (X →ₗ[ℤ] X →ₗ[ℤ] ℝ) :=
  {B | ∃ t : Fin m → ℝ, (∀ i, 0 ≤ t i) ∧ B = ∑ i, t i • toReal (u i)}

def StrictWith {O : Type} [CommRing O] (bar : O → O) (φ : InvFun O) [Module O X] [Module.Finite O X] (N : ℕ)
    (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ) (u : Fin m → LinearMap.BilinForm ℤ X) : Prop :=
  (∀ i, (ℓ (u i) : ℝ) = N * φ.evalZ (u i)) ∧ (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β ≤ ℓ β) ∧
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → N * φ.evalZ β = ℓ β →
      ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • β = ∑ i, c i • u i

theorem isStrict_iff {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} [Module O X] [Module.Finite O X]
    {u : Fin m → LinearMap.BilinForm ℤ X} : IsStrict bar φ u ↔ ∃ (N : ℕ) (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), 0 < N ∧
      StrictWith bar φ N ℓ u := Iff.rfl

def kDen (N n : ℕ) (𝓜 : Finset ℕ) : ℕ := N * ∏ M ∈ 𝓜, (M + 1) ^ n

def lamW (D N n : ℕ) (𝓜 : Finset ℕ) (r : (Fin n → ℤ) →ₗ[ℤ] X) (w : (X × X) →₀ ℤ)
    (a : ∀ M : ℕ, (Fin n → ZMod (M + 1)) → Fin n → ℤ) : (X × X) →₀ ℤ :=
  (D : ℤ) • ((∏ M ∈ 𝓜, ((M : ℤ) + 1) ^ n) • w +
    ∑ M ∈ 𝓜, ((N : ℤ) * ∏ M' ∈ 𝓜.erase M, ((M' : ℤ) + 1) ^ n) • ∑ y, Finsupp.single (r (a M y), r (a M y)) 1)

end GlobalTheory.PolCell
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftFormsLatticeDefiniteLatticeBaseChangeExtende
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open scoped TensorProduct InnerProductSpace ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar Formalism.IndefR.principalLevelFrame.instCMHostI
open GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.Mem.R3.Tr
open scoped Matrix

namespace GlobalTheory.Mem.R3.LiftLat0

section Key

open Formalism.IndefR.Cx

variable {K K' : Type} [Field K] [NumberField K] [Field K'] [NumberField K']

theorem map_mulVec_fun (φ : K →+* K') {m n : ℕ} (θ : Matrix (Fin m) (Fin n) K) (x : Fin n → K) :
    (fun k => φ ((θ *ᵥ x) k)) = θ.map φ *ᵥ fun k => φ (x k) := by
  funext k; exact RingHom.map_mulVec φ θ x k

theorem cpt_single (σ : K' →+* ℂ) {n : ℕ} (k : Fin n) : cpt σ (Pi.single k (1 : K')) = Pi.single k 1 := by
  funext i; by_cases h : i = k
  · subst h; simp [cpt]
  · simp [cpt, Pi.single_apply, h]

theorem kOf_apply (σ : K' →+* ℂ) (a : K') : kOf σ (σ a) = a := by
  classical
  have h : ∃ b : K', σ b = σ a := ⟨a, rfl⟩
  unfold kOf
  rw [dite_eq_left h]
  exact σ.injective h.choose_spec

theorem matLat_relMat_of_heq (φ : K →+* K') (σ : K →+* ℂ) (σ' : K' →+* ℂ)
    {W W' : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W'] {dW dW' dZ dZ' : ℕ}
    (w0 : (Fin dW → ℂ) →ₗ[ℂ] W) (t0 : (Fin dZ → ℂ) →ₗ[ℂ] W) (w0' : (Fin dW' → ℂ) →ₗ[ℂ] W')
    (t0' : (Fin dZ' → ℂ) →ₗ[ℂ] W') (θ : Matrix (Fin dW) (Fin dZ) K) (G : Matrix (Fin dW') (Fin dW) K')
    (N : Matrix (Fin dZ') (Fin dZ) K') (hN : Function.Bijective N.mulVec)
    (hG : ∀ y : Fin dW → K, HEq (w0' (cpt σ' (G *ᵥ fun k => φ (y k)))) (w0 (cpt σ y)))
    (hNc : ∀ x : Fin dZ → K, HEq (t0' (cpt σ' (N *ᵥ fun k => φ (x k)))) (t0 (cpt σ x)))
    (hR : ∀ x : Fin dZ → K, w0 (cpt σ (θ *ᵥ x)) = t0 (cpt σ x)) (hI : Function.Injective w0')
    (L : Submodule (𝓞 K) (Fin dZ → K)) :
    Formalism.DivisionValues.matLat (kMat σ' (relMat w0' t0'))
              (Submodule.span (𝓞 K') ((fun x : Fin dZ → K => N *ᵥ fun k => φ (x k)) '' (L : Set (Fin dZ → K)))) =
      Submodule.span (𝓞 K') ((fun x : Fin dW → K => G *ᵥ fun k => φ (x k)) ''
        (Formalism.DivisionValues.matLat θ L : Set (Fin dW → K))) := by
  classical
  set eN := LinearEquiv.ofBijective (Matrix.mulVecLin N) hN with heN
  have hNe : ∀ v, eN v = N *ᵥ v := fun v => rfl
  have hb : ∀ x : Fin dZ → K, t0' (cpt σ' (N *ᵥ fun k => φ (x k))) =
      w0' (cpt σ' (G *ᵥ (θ.map φ *ᵥ fun k => φ (x k)))) := by
    intro x
    rw [← map_mulVec_fun φ θ x]
    exact eq_of_heq ((hNc x).trans ((heq_of_eq (hR x)).symm.trans (hG (θ *ᵥ x)).symm))

  have hL : ((t0'.comp (cptL σ' dZ')).comp N.mulVecLin : (Fin dZ → K') →ₛₗ[σ'] W') =
      (w0'.comp (cptL σ' dW')).comp (G.mulVecLin.comp (θ.map φ).mulVecLin) := by
    refine (Pi.basisFun K' (Fin dZ)).ext fun i => ?_
    have hs : (Pi.basisFun K' (Fin dZ)) i = fun k => φ ((Pi.single i (1 : K) : Fin dZ → K) k) := by
      rw [Pi.basisFun_apply]; funext k; by_cases h : k = i
      · subst h; simp
      · simp [Pi.single_apply, h]
    rw [hs]
    simpa [cptL, Matrix.mulVecLin_apply] using hb (Pi.single i 1)

  have hθ : ∀ u : Fin dZ' → K', kMat σ' (relMat w0' t0') *ᵥ u = G *ᵥ (θ.map φ *ᵥ eN.symm u) := by
    have hk : ∀ k : Fin dZ', ∀ i, kMat σ' (relMat w0' t0') i k = (G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1))) i := by
      intro k i
      set v := G *ᵥ (θ.map φ *ᵥ eN.symm (Pi.single k 1)) with hv
      have hw : w0' (cpt σ' v) = t0' (Pi.single k 1) := by
        have h1 := congrArg (fun f => f (eN.symm (Pi.single k 1))) hL
        simp only [LinearMap.comp_apply, cptL, LinearMap.coe_mk, AddHom.coe_mk, Matrix.mulVecLin_apply] at h1
        have h2 : N *ᵥ eN.symm (Pi.single k 1) = Pi.single k 1 := by
          rw [← hNe]; exact eN.apply_symm_apply (Pi.single k 1)
        rw [h2, cpt_single] at h1
        exact h1.symm
      have hex : ∃ y, w0' y = t0' (Pi.single k 1) := ⟨_, hw⟩
      have hsol : solve w0' (t0' (Pi.single k 1)) = cpt σ' v := by
        apply hI
        unfold solve
        rw [dite_eq_left hex]
        exact hex.choose_spec.trans hw.symm
      show kOf σ' (solve w0' (t0' (Pi.single k 1)) i) = v i
      rw [hsol]
      exact kOf_apply σ' (v i)
    have hlin : (kMat σ' (relMat w0' t0')).mulVecLin =
        G.mulVecLin.comp ((θ.map φ).mulVecLin.comp eN.symm.toLinearMap) := by
      refine (Pi.basisFun K' (Fin dZ')).ext fun k => ?_
      rw [Pi.basisFun_apply]
      funext i
      simp only [Matrix.mulVecLin_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
      rw [← hk k i, Matrix.mulVec_single_one]
      rfl
    intro u
    exact congrArg (fun f => f u) hlin

  unfold Formalism.DivisionValues.matLat
  rw [Submodule.map_span, Submodule.map_coe, Set.image_image, Set.image_image]
  congr 1
  refine Set.image_congr fun x _ => ?_
  simp only [LinearMap.restrictScalars_apply, Matrix.mulVecLin_apply]
  rw [hθ, map_mulVec_fun φ θ x]
  congr 2
  rw [← hNe]; exact eN.symm_apply_apply (fun k => φ (x k))

end Key


set_option maxHeartbeats 16000000 in
theorem liftFormsLattice_definiteLattice_baseChange_extended_alt : GlobalTheory.Published.DiscreteSeriesCover → GlobalTheory.Published.HarishChandraModules → GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.CasselmanWallach → GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → (StepW Pinned fun K B' f' T' w' => ∀ (B : Base) (f : Fr B.toPre) (T : TwDat B) (w : ColW B f T), Enl0 B B' →
  HEq f' f → Pinned K B f T w → HEq w'.px w.px → ∀ (Z : w.Lt) (hX : B.fields.Ok) (Wt : Set B.places.Pl)
    (z : Dat (w.st Z) w.I hX T Wt), GrpTrue Z.N f → GrpAt (w.st Z) w.I → Fine z → HoldsL z.R z.F →
    ∀ (Z' : w'.Lt) (hX' : B'.fields.Ok), GrpTrue Z'.N f' → GrpAt (w'.st Z') w'.I → VolTieG (w'.D Z') →
      ∀ z' : Dat (w'.st Z') w'.I hX' T' {v | B'.places.resChar v ∈ T'.pl}, Fine z' → ExtN z z' →
        ∀ (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m), (j : ℕ) = j' →
        ∀ φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL, (∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x) →
        ∃ G : Matrix (Fin ((s0Of z'.R z'.F).dW j')) (Fin ((s0Of z.R z.F).dW j)) (w'.st Z').toD7.what₂.LL, Function.Bijective G.mulVec ∧
          (s0Of z'.R z'.F).M j' = Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' (((s0Of z.R z.F).M j : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL))) ∧
          Formalism.DivisionValues.matLat ((s0Of z'.R z'.F).θ j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) (((famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).side3 z'.F.P0 z'.F.ψ0 (zsOf z'.R z'.F)).Tl j' (famR (w'.st Z') w'.I hX' (usedOf w'.I T' {v | B'.places.resChar v ∈ T'.pl}) z'.Xg z'.tr).A.μ0) =
            Submodule.span (𝓞 (w'.st Z').toD7.what₂.LL) ((fun x : Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL => Matrix.mulVec G fun k => φ (x k)) '' ((Formalism.DivisionValues.matLat ((s0Of z.R z.F).θ j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) (((famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).side3 z.F.P0 z.F.ψ0 (zsOf z.R z.F)).Tl j (famR (w.st Z) w.I hX (usedOf w.I T Wt) z.Xg z.tr).A.μ0) : Submodule (𝓞 (w.st Z).toD7.what₂.LL) (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)) : Set (Fin ((s0Of z.R z.F).dW j) → (w.st Z).toD7.what₂.LL)))) := by
  intro h1 h2 h3 h4 h5 h6 h7
  refine StepW.trans (StepW.and (StepW.and (_root_.GlobalTheory.Mem.R3.LiftForms.extendedData_liftFormsLattice_baseLevel_baseChange h1 h2 h3 h4 h5 h6 h7) (_root_.GlobalTheory.Mem.R3.LiftLatBC.lift_lattice_bc h1 h2 h3 h4 h5 h6 h7))
    (StepW.and (_root_.GlobalTheory.Mem.R3.LiftMatBase.baseLevelLiftMatrix_solves_relation_extendedData h1 h2 h3 h4 h5 h6 h7) (_root_.GlobalTheory.Mem.R3.LiftInj.baseLevelComplexPoints_injective_extendedData h1 h2 h3 h4 h5 h6 h7))) (StepW.of_all ?_)
  intro K B' f' T' w' _ _ H B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨G, hGb, hM, hGc⟩ := H.1.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  obtain ⟨N, hNb, hTl, hNc⟩ := H.1.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hR := H.2.1 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  have hI := H.2.2 B f T w hE hf hPin hpx Z hX Wt z hG hGA hFi hHL Z' hX' hG' hGA' hV z' hFi' hExt j j' hj φ hφ
  refine ⟨G, hGb, hM, ?_⟩
  rw [hTl]
  exact matLat_relMat_of_heq φ _ _ _ _ _ _ _ G N hNb hGc hNc hR hI _

end GlobalTheory.Mem.R3.LiftLat0
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftScalarEqLabelScalarStatement
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.liftScalar_eq_labelScalar : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  first | exact @GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label | exact GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label | (intros; apply GlobalTheory.Mem.R3.LamLab.eigenvalue_eq_of_label <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealMapOfGermsAffineScheme
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GermAff

theorem mem_map_of_germ : ∀ {T Y' : Scheme.{0}} [IsAffine T] (χ : T ⟶ Y') (I : Y'.IdealSheafData) (W : Y'.affineOpens)
    (hle : ⊤ ≤ χ ⁻¹ᵁ (W : Y'.Opens)) (s : Γ(T, ⊤)),
    (∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ FinalTheorems.stalkId (I.comap χ) t) →
      s ∈ (I.ideal W).map (χ.appLE W ⊤ hle).hom := by
  intro T Y' _ χ I W hle s hs
  set K := (I.ideal W).map (χ.appLE W ⊤ hle).hom with hK
  have hc : I.comap χ = Scheme.IdealSheafData.ofIdealTop K := by
    refine (GlobalTheory.Vanishing.eq_comap_of_stalk fun z => ?_).symm
    have hz : χ z ∈ W.1 := hle trivial
    rw [GlobalTheory.LocM.stalkId_ofIdealTop, ds_stalkId_eq_map I W _ hz, Ideal.map_map, Ideal.map_map,
      ← CommRingCat.hom_comp, ← CommRingCat.hom_comp, Scheme.Hom.germ_stalkMap, Scheme.Hom.appLE, Category.assoc]
    congr 3
    exact T.presheaf.germ_res (homOfLE hle) z (by trivial)
  have hs' : ∀ t : T, (T.presheaf.germ ⊤ t trivial).hom s ∈ K.map (T.presheaf.germ ⊤ t trivial).hom := by
    intro t
    rw [← GlobalTheory.LocM.stalkId_ofIdealTop, ← hc]
    exact hs t
  by_contra hns
  have hne : K.colon {s} ≠ ⊤ := by
    intro htop
    have h1 : (1 : Γ(T, ⊤)) ∈ K.colon {s} := htop ▸ Submodule.mem_top
    rw [Submodule.mem_colon_singleton, one_smul] at h1
    exact hns h1
  obtain ⟨P, hP, hCP⟩ := Ideal.exists_le_maximal _ hne
  let y : PrimeSpectrum Γ(T, ⊤) := ⟨P, hP.isPrime⟩
  have hA := isAffineOpen_top T
  let t : T := hA.fromSpec y
  have ht : t ∈ (⊤ : T.Opens) := trivial
  letI : Algebra Γ(T, ⊤) (T.presheaf.stalk t) := T.presheaf.algebra_section_stalk ⟨t, ht⟩
  haveI : IsLocalization y.asIdeal.primeCompl (T.presheaf.stalk t) := hA.isLocalization_stalk' y ht
  have hg : (T.presheaf.germ ⊤ t trivial).hom = algebraMap Γ(T, ⊤) (T.presheaf.stalk t) := rfl
  have h := hs' t
  rw [hg, IsLocalization.mem_map_algebraMap_iff y.asIdeal.primeCompl] at h
  obtain ⟨⟨⟨k, hk⟩, ⟨m, hm⟩⟩, he⟩ := h
  simp only at he
  rw [← map_mul, IsLocalization.eq_iff_exists y.asIdeal.primeCompl] at he
  obtain ⟨⟨c, hcm⟩, hc'⟩ := he
  simp only at hc'
  have hmem : c * m ∈ K.colon {s} := by
    rw [Submodule.mem_colon_singleton, smul_eq_mul]
    have : c * m * s = c * k := by rw [← hc']; ring
    rw [this]
    exact K.mul_mem_left c hk
  have hnot : c * m ∉ P := fun h' => (hP.isPrime.mem_or_mem h').elim hcm hm
  exact hnot (hCP hmem)

end GlobalTheory.GermAff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MemIdealSheafMapOfAffineCoverPreimage
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open scoped TensorProduct

namespace GlobalTheory.IdealPushCover

theorem mem_map_ideal_of_cover : ∀ {X Y' : Scheme.{0}} (ρ : Y' ⟶ X) [QuasiCompact ρ] (I : Y'.IdealSheafData) (U : X.affineOpens) {ι : Type} (W : ι → Y'.affineOpens) (hW : ∀ i, (W i : Y'.Opens) ≤ ρ ⁻¹ᵁ (U : X.Opens)), ρ ⁻¹ᵁ (U : X.Opens) ≤ ⨆ i, (W i : Y'.Opens) → ∀ b : Γ(X, U), (∀ i, (ρ.appLE U (W i) (hW i)).hom b ∈ I.ideal (W i)) → b ∈ (I.map ρ).ideal U := by
  intro X Y' ρ _ I U ι W hW hcov b hb
  have hk : ∀ V : Y'.affineOpens, I.ideal V = RingHom.ker (I.subschemeι.app V.1).hom := fun V => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [Scheme.IdealSheafData.map, Scheme.Hom.ker_apply, RingHom.mem_ker, Scheme.Hom.comp_app]
  change (I.subschemeι.app (ρ ⁻¹ᵁ U.1)).hom ((ρ.app U.1).hom b) = 0
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  rw [map_zero]
  have hz' : I.subschemeι z ∈ ⨆ i, (W i : Y'.Opens) := hcov hz
  obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hz'
  have hzi : z ∈ I.subschemeι ⁻¹ᵁ (W i : Y'.Opens) := hi
  have h0 : (I.subschemeι.app (W i).1).hom ((ρ.appLE U (W i) (hW i)).hom b) = 0 := by
    have := hb i
    rw [hk, RingHom.mem_ker] at this
    exact this
  have e1 : (ρ.appLE U (W i) (hW i)).hom b = resG Y' (hW i) ((ρ.app U.1).hom b) := rfl
  rw [e1, GlobalTheory.Cartier.app_resG] at h0
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono (hW i)) z hzi, h0, map_zero]

end GlobalTheory.IdealPushCover
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef

namespace GlobalTheory.PolFan

section Mult

variable {O : Type} [CommRing O] (bar : O → O) {X : Type} [AddCommGroup X] [Module O X]

def cellMult {m : ℕ} (δ : Fin m → balForms bar X) : ℕ :=
  Nat.card (Submodule.torsion ℤ (balForms bar X ⧸ Submodule.span ℤ (Set.range δ)))

def IsPrim (β : balForms bar X) : Prop :=
  ∀ (k : ℕ) (β' : balForms bar X), β = k • β' → k = 1

def maxMult (q : ℕ) (φ : InvFun O) : ℕ∞ :=
  ⨆ (X : Type) (_ : AddCommGroup X) (_ : Module O X) (_ : Module.Finite O X) (_ : Module.Projective O X)
    (_ : Module.finrank O X ≤ q) (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ)
    (_ : LinearIndependent ℤ δ) (_ : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)),
    ((cellMult bar fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) : ℕ∞)

variable {bar}

theorem not_isPrim_zero : ¬ IsPrim bar (0 : balForms bar X) := fun h => by
  have := h 0 0 (by simp)
  exact zero_ne_one this

end Mult

end GlobalTheory.PolFan
end
end

