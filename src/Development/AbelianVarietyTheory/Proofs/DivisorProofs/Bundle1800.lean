module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1413
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1063
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1787
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1000
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1458
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0912
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1552
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1783
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasBlockOfOccurs
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1755
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1747
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1786
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0280
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0218
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1281
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0839
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
public import GroundTheory.AutomorphicForms.MultiplicityOne.Injective

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantFormDoubledSpaceSplitPlace
section
open scoped TensorProduct Matrix ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.DblSplitForm

section Abstract

variable {G M : Type} [AddCommGroup G] [AddCommGroup M] [Module ℂ M] {Y : AddSubgroup G} {ρ : G → M →ₗ[ℂ] M}

theorem exists_ext_form (hadd : ∀ x ∈ Y, ∀ x' ∈ Y, ∀ f, ρ x (ρ x' f) = ρ (x + x') f) (h0 : ∀ f, ρ 0 f = f) {Θ : Set M}
    (hsm : ∀ u ∈ Y, ∀ g ∈ Θ, ∃ k : ℕ, 0 < k ∧ ρ (k • u) g = g) (l0 : M →ₗ[ℂ] ℂ) (gen : Set M)
    (hinv : ∀ u ∈ Y, ∀ p ∈ gen, l0 (ρ u p) = l0 p) :
    ∃ ℓ : M →ₗ[ℂ] ℂ, (∀ u ∈ Y, ∀ g ∈ Θ, ℓ (ρ u g) = ℓ g) ∧ ∀ p ∈ gen, ℓ p = l0 p := by
  classical
  let P : Submodule ℂ M := Submodule.span ℂ gen
  let K : Submodule ℂ M := Submodule.span ℂ {m | ∃ u ∈ Y, ∃ g ∈ Θ, m = ρ u g - g}
  have hl0P : ∀ u ∈ Y, ∀ p ∈ P, l0 (ρ u p) = l0 p := by
    intro u hu p hp
    induction hp using Submodule.span_induction with
    | mem f hf => exact hinv u hu f hf
    | zero => simp
    | add a b _ _ ha hb => rw [map_add (f := _), map_add (f := _), map_add (f := _), ha, hb]
    | smul c a _ ha => rw [map_smul, map_smul, map_smul, ha]
  have hPK : ∀ m ∈ P, m ∈ K → l0 m = 0 := by
    intro m hmP hmK
    obtain ⟨ι, s, y, hy, ⟨i, hi, -⟩, h⟩ := GlobalTheory.HalfCoinv.exists_sum_eq_zero hadd h0 hsm hmK
    have h1 : l0 (∑ j ∈ s, ρ (y j) m) = (s.card : ℂ) * l0 m := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, Finset.sum_congr rfl (fun j _ => hl0P (y j) (hy j) m hmP), Finset.sum_const, nsmul_eq_mul]
    rw [h, map_zero] at h1
    have hc : (s.card : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨i, hi⟩)
    exact (mul_eq_zero.1 h1.symm).resolve_left hc
  let fP : M →ₗ.[ℂ] ℂ := ⟨P, l0 ∘ₗ P.subtype⟩
  let fK : M →ₗ.[ℂ] ℂ := ⟨K, 0⟩
  have H : ∀ (x : fP.domain) (y : fK.domain), (x : M) = y → fP x = fK y := by
    intro x y hxy
    change l0 (x : M) = 0
    exact hPK _ x.2 (hxy ▸ y.2)
  obtain ⟨L, hL⟩ := LinearMap.exists_extend (fP.sup fK H).toFun
  have hLv : ∀ z : (fP.sup fK H).domain, L z = (fP.sup fK H) z := fun z => LinearMap.congr_fun hL z
  refine ⟨L, fun u hu g hg => ?_, fun p hp => ?_⟩
  · have hk : ρ u g - g ∈ K := Submodule.subset_span ⟨u, hu, g, hg, rfl⟩
    have hz : ρ u g - g ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_right hk
    have : L (ρ u g - g) = 0 := by
      refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H (0 : fP.domain) ⟨_, hk⟩ ⟨_, hz⟩ (by simp)).trans ?_)
      change l0 0 + 0 = 0
      simp
    rwa [map_sub, sub_eq_zero] at this
  · have hp' : p ∈ P := Submodule.subset_span hp
    have hz : p ∈ (fP.sup fK H).domain := by
      rw [LinearPMap.domain_sup]; exact Submodule.mem_sup_left hp'
    refine (hLv ⟨_, hz⟩).trans ((LinearPMap.sup_apply H ⟨_, hp'⟩ (0 : fK.domain) ⟨_, hz⟩ (by simp)).trans ?_)
    change l0 p + 0 = _
    rw [add_zero]

end Abstract

def conjForm {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) : (X → ℂ) →ₗ[ℂ] ℂ where
  toFun g := conj (ℓ (fun y => conj (g y)))
  map_add' a b := by
    have : (fun y => conj ((a + b) y)) = (fun y => conj (a y)) + fun y => conj (b y) := by
      funext y; simp
    rw [this, map_add (f := _), map_add (f := _)]
  map_smul' c a := by
    have : (fun y => conj ((c • a) y)) = conj c • fun y => conj (a y) := by
      funext y; simp
    rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj, RingHom.id_apply, smul_eq_mul]

theorem conjForm_mul {X : Type} (ℓ : (X → ℂ) →ₗ[ℂ] ℂ) (c : ℂ) (b : X → ℂ) :
    conjForm ℓ (fun y => c * conj (b y)) = c * conj (ℓ b) := by
  have : (fun y => conj (c * conj (b y))) = conj c • b := by
    funext y; simp
  show conj (ℓ (fun y => conj (c * conj (b y)))) = _
  rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]

open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {nS nT : ℕ}

def joinR (x₁ x₂ : WOF F E nS nT) : WOF F E nS (nT + nT) := (Matrix.fromRows x₁ x₂).submatrix finSumFinEquiv.symm id

theorem topR_joinR (x₁ x₂ : WOF F E nS nT) : topR (joinR x₁ x₂) = x₁ := by
  ext i j
  simp [joinR, topR, Matrix.submatrix_apply]

theorem botR_joinR (x₁ x₂ : WOF F E nS nT) : botR (joinR x₁ x₂) = x₂ := by
  ext i j
  show Matrix.fromRows x₁ x₂ (finSumFinEquiv.symm (finSumFinEquiv (Sum.inr i))) j = x₂ i j
  rw [Equiv.symm_apply_apply]; rfl

def dblForm (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) : (WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ :=
  ℓ ∘ₗ LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y))

theorem dblForm_deltaT (ℓ : (WOF F E nS nT → ℂ) →ₗ[ℂ] ℂ) (a b : WOF F E nS nT → ℂ) :
    dblForm ℓ (deltaT a b) = ℓ a * conj (ℓ b) := by
  have h : (LinearMap.pi fun x₁ => conjForm ℓ ∘ₗ LinearMap.funLeft ℂ ℂ (fun y => joinR x₁ (-y)))
      (deltaT a b) = conj (ℓ b) • a := by
    funext x₁
    have e : (LinearMap.funLeft ℂ ℂ (fun y : WOF F E nS nT => joinR x₁ (-y))) (deltaT a b) =
        fun y => a x₁ * conj (b y) := by
      funext y
      simp [LinearMap.funLeft_apply, deltaT_apply, topR_joinR, botR_joinR]
    simp only [LinearMap.pi_apply, LinearMap.comp_apply, e, conjForm_mul, Pi.smul_apply, smul_eq_mul]
    ring
  rw [dblForm, LinearMap.comp_apply, h, map_smul, smul_eq_mul, mul_comm]

end GlobalTheory.DblSplitForm

namespace GlobalTheory.DblSplitForm
open Formalism.IndefR.DatumF GlobalTheory.DblTargetDelta GlobalTheory.WeilSchrodinger.DblTargetF

theorem exists_invForm_dbl : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ e, Formalism.IndefR.DatumF.IsSplitIdemF σ e →
        ∃ ℓ : (Formalism.IndefR.DatumF.WOF F E nS (nT + nT) → ℂ) →ₗ[ℂ] ℂ,
          (∀ u : Formalism.IndefR.DatumF.WOF F E nS (nT + nT), (∀ i j, Formalism.IndefR.DatumF.cAF σ e * u i j = u i j) →
            ∀ f, Formalism.IndefR.DatumF.IsThetaFunOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ f →
              ℓ (Formalism.IndefR.DatumF.heisOF σ JS (GlobalTheory.WeilSchrodinger.DblTargetF.dblG JT) ξ₀ B.ψ u f) = ℓ f) ∧
          ∃ f₁ f₂ : Formalism.IndefR.DatumF.WOF F E nS nT → ℂ, Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₁ ∧
            Formalism.IndefR.DatumF.IsThetaFunOF σ JS JT ξ₀ B.ψ f₂ ∧ ℓ (GlobalTheory.DblTargetDelta.deltaT f₁ f₂) ≠ 0 := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he
  obtain ⟨f₀, hf₀, hf₀0⟩ : ∃ f₀ : WOF F E nS nT → ℂ, IsThetaFunOF σ JS JT ξ₀ B.ψ f₀ ∧ f₀ ≠ 0 :=
    _root_.GlobalTheory.ThetaNonzeroF.exists_isThetaFunOF_ne_zero F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ₁, hℓ₁, f, hf, hℓf⟩ := _root_.GlobalTheory.SplitInvFormF.exists_invForm_split F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ e he f₀ hf₀ hf₀0
  have hheis := GlobalTheory.DblHeis.heisOF_dblG_deltaT F E σ B hB nS nT JS JT hS hT ξ₀ hξ hσξ
  obtain ⟨ℓ, h1, h2⟩ := exists_ext_form (Y := GlobalTheory.SplitInvFormF.conjHalf σ e nS (nT + nT))
    (ρ := GlobalTheory.SplitInvFormF.heisL σ JS (dblG JT) ξ₀ B.ψ)
    (Θ := {g | IsThetaFunOF σ JS (dblG JT) ξ₀ B.ψ g})
    (fun x hx x' hx' g => by
      show heisOF σ JS (dblG JT) ξ₀ B.ψ x (heisOF σ JS (dblG JT) ξ₀ B.ψ x' g) = heisOF σ JS (dblG JT) ξ₀ B.ψ (x + x') g
      rw [GlobalTheory.SplitInvFormF.heisOF_heisOF, GlobalTheory.SplitInvFormF.symplOHF_half he hx hx', AddChar.map_zero_eq_one, one_smul])
    (fun g => GlobalTheory.SplitInvFormF.heisOF_zero g)
    (fun u hu g hg => GlobalTheory.SplitInvFormF.exists_nsmul_fix he hu hg)
    (dblForm ℓ₁) {p | ∃ a b, IsThetaFunOF σ JS JT ξ₀ B.ψ a ∧ IsThetaFunOF σ JS JT ξ₀ B.ψ b ∧ p = deltaT a b}
    (fun u hu p hp => by
      obtain ⟨a, b, ha, hb, rfl⟩ := hp
      have hu' : ∀ i j, cAF σ e * u i j = u i j := hu
      have ht : ∀ i j, cAF σ e * topR u i j = topR u i j := fun i j => hu' _ _
      have hb' : ∀ i j, cAF σ e * (-botR u) i j = (-botR u) i j := fun i j => by
        show cAF σ e * -(u _ j) = -(u _ j)
        rw [mul_neg, hu']
      show dblForm ℓ₁ (heisOF σ JS (dblG JT) ξ₀ B.ψ u (deltaT a b)) = dblForm ℓ₁ (deltaT a b)
      rw [hheis, dblForm_deltaT, dblForm_deltaT, hℓ₁ _ ht a ha, hℓ₁ _ hb' b hb])
  refine ⟨ℓ, fun u hu g hg => h1 u hu g hg, f, f, hf, hf, ?_⟩
  rw [h2 _ ⟨f, f, hf, hf, rfl⟩, dblForm_deltaT]
  exact mul_ne_zero hℓf ((map_ne_zero _).2 hℓf)

end GlobalTheory.DblSplitForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsJointRowWeightDualWeylModule
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.ExpTie GlobalTheory.ExpFrame Formalism.CohomologicalDescent.DepthNonnegative Formalism.CohomologicalDescent.LogSmallConstantBounds Formalism.CohomologicalDescent.ShortWeightBounds Formalism.CohomologicalDescent.LD Formalism.RankGapBounds.FormsTensorLocalization

set_option autoImplicit false

noncomputable section

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory.HighWt

theorem rowWeight_le_colSum (N : ℕ) (d : Fin N × Fin N →₀ ℕ) (a : Fin N) :
    (Finsupp.weight (rowW N N) d) a ≤ ∑ s, (Finsupp.weight (colW N N) d) s := by
  simp only [Finsupp.weight_apply, Finsupp.sum, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro i _
  rw [← Finset.mul_sum]
  simp only [rowW, colW, Finset.sum_pi_single', Finset.mem_univ, if_true]
  apply Nat.mul_le_mul_left
  rw [Pi.single_apply]
  split_ifs <;> omega

variable (O : Type) [CommRing O] (N : ℕ) {ι : Type} [DecidableEq ι] (lam : ι → ℕ → ℕ)

def wtBox (τ : ι) : Finset (Fin N → ℕ) :=
  Fintype.piFinset fun _ => Finset.range (∑ s : Fin N, res N (lam τ) s + 1)

theorem sum_box (τ : ι) (f : MvPolynomial (Fin N × Fin N) O) (hf : f ∈ dualWeyl O N N (res N (lam τ))) :
    ∑ w ∈ wtBox N lam τ, weightedHomogeneousComponent (rowW N N) w f = f := by
  classical
  have hc : IsWeightedHomogeneous (colW N N) f (res N (lam τ)) := by
    have := (Submodule.mem_inf.mp hf).1
    simpa [mem_weightedHomogeneousSubmodule] using this
  ext d
  rw [coeff_sum]
  simp only [coeff_weightedHomogeneousComponent]
  rw [Finset.sum_ite_eq]
  split_ifs with h
  · rfl
  · by_contra hne
    apply h
    have hd := hc (Ne.symm hne)
    simp only [wtBox, Fintype.mem_piFinset, Finset.mem_range]
    intro a
    have := rowWeight_le_colSum N d a
    rw [hd] at this
    omega

section Ops

variable {O N lam}

theorem isProj_idem {τ : ι} {w : Fin N → ℕ} {a : Module.End O (NablaT O N lam)} (h : IsProj O N lam τ w a) :
    a * a = a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  rw [h x y hy]
  have hy' : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ y) τ : MvPolynomial _ O) := by
    rw [Function.update_self, hy, weightedHomogeneousComponent_eq_self
      (weightedHomogeneousComponent_isWeightedHomogeneous _ _)]
  rw [h _ y hy', Function.update_idem]

theorem isProj_comm {τ τ' : ι} (hne : τ ≠ τ') {w w' : Fin N → ℕ} {a b : Module.End O (NablaT O N lam)}
    (ha : IsProj O N lam τ w a) (hb : IsProj O N lam τ' w' b) : a * b = b * a := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  simp only [LinearMap.compMultilinearMap_apply, Module.End.mul_apply]
  let y : dualWeyl O N N (res N (lam τ)) := rowProj O N (res N (lam τ)) w (x τ)
  let y' : dualWeyl O N N (res N (lam τ')) := rowProj O N (res N (lam τ')) w' (x τ')
  have hy : (y : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w (x τ : MvPolynomial _ O) := rfl
  have hy' : (y' : MvPolynomial (Fin N × Fin N) O) = weightedHomogeneousComponent (rowW N N) w' (x τ' : MvPolynomial _ O) := rfl
  rw [hb x y' hy', ha x y hy]
  have h1 : (y : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w ((Function.update x τ' y') τ : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne]; exact hy
  have h2 : (y' : MvPolynomial (Fin N × Fin N) O) =
      weightedHomogeneousComponent (rowW N N) w' ((Function.update x τ y) τ' : MvPolynomial _ O) := by
    rw [Function.update_of_ne hne.symm]; exact hy'
  rw [ha _ y h1, hb _ y' h2, Function.update_comm hne]

theorem isProj_sum (τ : ι) (e : (Fin N → ℕ) → Module.End O (NablaT O N lam)) (he : ∀ w, IsProj O N lam τ w (e w)) :
    ∑ w ∈ wtBox N lam τ, e w = 1 := by
  apply PiTensorProduct.ext
  apply MultilinearMap.ext
  intro x
  rw [LinearMap.compMultilinearMap_apply, LinearMap.compMultilinearMap_apply, LinearMap.sum_apply, Module.End.one_apply]
  have key : ∀ w, e w (PiTensorProduct.tprod O x) =
      (PiTensorProduct.tprod O).toLinearMap x τ (rowProj O N (res N (lam τ)) w (x τ)) := by
    intro w
    rw [MultilinearMap.toLinearMap_apply]
    exact he w x _ rfl
  rw [Finset.sum_congr rfl (fun w _ => key w)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← map_sum, MultilinearMap.toLinearMap_apply]
  have : ∑ w ∈ wtBox N lam τ, rowProj O N (res N (lam τ)) w (x τ) = x τ := by
    apply Subtype.ext
    rw [Submodule.coe_sum]
    exact sum_box O N lam τ _ (x τ).2
  rw [this, Function.update_eq_self]

end Ops

section Main

variable {O N lam}

def projA [Fintype ι] (τ : ι) (w : Fin N → ℕ) : alg O N lam :=
  ⟨(exists_unique_isProj O N ι lam τ w).choose,
    Algebra.subset_adjoin (Or.inr ⟨τ, w, (exists_unique_isProj O N ι lam τ w).choose_spec.1⟩)⟩

variable [Fintype ι]

theorem projA_isProj (τ : ι) (w : Fin N → ℕ) : IsProj O N lam τ w (projA (O := O) (lam := lam) τ w : Module.End O (NablaT O N lam)) :=
  (exists_unique_isProj O N ι lam τ w).choose_spec.1

theorem projA_eq {τ : ι} {w : Fin N → ℕ} {a : alg O N lam} (h : IsProj O N lam τ w a) : a = projA τ w :=
  Subtype.ext ((exists_unique_isProj O N ι lam τ w).choose_spec.2 _ h)

theorem projA_idem (τ : ι) (w : Fin N → ℕ) : projA (O := O) (lam := lam) τ w * projA τ w = projA τ w :=
  Subtype.ext (isProj_idem (projA_isProj τ w))

theorem projA_comm {τ τ' : ι} (hne : τ ≠ τ') (w w' : Fin N → ℕ) :
    projA (O := O) (lam := lam) τ w * projA τ' w' = projA τ' w' * projA τ w :=
  Subtype.ext (isProj_comm hne (projA_isProj τ w) (projA_isProj τ' w'))

theorem projA_sum (τ : ι) : ∑ w ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ w = 1 := by
  apply Subtype.ext
  rw [AddSubmonoidClass.coe_finsetSum, OneMemClass.coe_one]
  exact isProj_sum τ _ (projA_isProj τ)

end Main

theorem exists_jointWt : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] (N : ℕ) (ι : Type) [Fintype ι]
    [DecidableEq ι] (lam : ι → ℕ → ℕ) (Gm : Type) [AddCommGroup Gm] [Module (alg O N lam) Gm], Nontrivial Gm →
    ∃ w : ι → Fin N → ℕ, GlobalTheory.HighWt.JointWt O N lam Gm w := by
  intro O _ _ _ _ N ι _ _ lam Gm _ _ _
  have step : ∀ s : Finset ι, ∃ z : Gm, z ≠ 0 ∧ ∃ w : ι → Fin N → ℕ,
      ∀ τ ∈ s, projA (O := O) (lam := lam) τ (w τ) • z = z := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      obtain ⟨z, hz⟩ := exists_ne (0 : Gm)
      exact ⟨z, hz, 0, by simp⟩
    | insert τ s hτ ih =>
      obtain ⟨z, hz, w, hw⟩ := ih
      have hsum : ∑ v ∈ wtBox N lam τ, projA (O := O) (lam := lam) τ v • z = z := by
        rw [← Finset.sum_smul, projA_sum, one_smul]
      obtain ⟨v, -, hv⟩ := Finset.exists_ne_zero_of_sum_ne_zero (hsum.symm ▸ hz)
      refine ⟨projA τ v • z, hv, Function.update w τ v, ?_⟩
      intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ
      · rw [Function.update_self, smul_smul, projA_idem]
      · have hne : σ ≠ τ := fun h => hτ (h ▸ hσ)
        rw [Function.update_of_ne hne, smul_smul, projA_comm hne, mul_smul, hw σ hσ]
  obtain ⟨z, hz, w, hw⟩ := step Finset.univ
  exact ⟨w, z, hz, fun τ a ha => by rw [projA_eq ha]; exact hw τ (Finset.mem_univ _)⟩

end GlobalTheory.HighWt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalFiniteDimFinitePartsWeilOperators
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

noncomputable section

namespace GlobalTheory.WeilCont

theorem adeleJoin_zero_zero (F : Type) [Field F] [NumberField F] (κ : Type) :
    adeleJoin F (0 : κ → mixedEmbedding.mixedSpace F) 0 = 0 := by
  funext i
  simp only [adeleJoin, Pi.zero_apply, map_zero, Prod.mk_zero_zero]

theorem sum_mul_zero_prod {κ : Type} [Fintype κ] {A B : Type} [CommRing A] [CommRing B] (z : κ → A × B)
    (y : κ → B) : (∑ i, z i * ((0 : A), y i)) = ((0 : A), ∑ i, (z i).2 * y i) := by
  ext <;> simp [Prod.fst_sum, Prod.snd_sum]

theorem dotProduct_adeleJoin_zero (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (z : κ → AdeleRing (𝓞 F) F) (y : κ → FiniteAdeleRing (𝓞 F) F) :
    z ⬝ᵥ adeleJoin F 0 y = pairA F 0 ((fun i => (z i).2) ⬝ᵥ y) := by
  simp only [dotProduct, adeleJoin, pairA, Pi.zero_apply, map_zero]
  exact sum_mul_zero_prod (A := InfiniteAdeleRing F) (B := FiniteAdeleRing (𝓞 F) F) z y

theorem exists_local_finite_parts : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ p0, ∃ N ∈ nhds p0, ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F) → ℂ)
      (y : Fin m → κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 D.host.F) D.host.F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ p ∈ N, ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ,
        om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f i) (g i) := by
  intro D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ _ co hco ω hω om hom Φ hΦ p0
  obtain ⟨pres, impl⟩ := GlobalTheory.T.transportedWeil_preserves_schwartz_heisenberg_equivariant D ψ hψ S T χS χT hS hT hrS hrT JA JB ξ hJA hJB κ co hco ω hω om hom
  obtain ⟨L₁, L₂, hL₁, hL₂, hinv⟩ := _root_.GlobalTheory.SchrFixNbhd.schr_fix_nbhd D ψ hψ κ Φ hΦ
  obtain ⟨N, hN, L₁', L₂', hL₁', hL₁c, hL₂', hNL⟩ := _root_.GlobalTheory.WeilTransNbhdD.exists_nhds_finite_preimage_D D T.rank S.rank JA JB ξ κ co L₁ L₂ hL₁ hL₂ p0
  have hK := _root_.GlobalTheory.AnnCompactStdChar.isCompact_annihilator_of_isStdChar D ψ hψ κ L₂' hL₂'
  have hA := _root_.GlobalTheory.WeilCont.schA_periodic_finite_cosets D.host.F κ L₁' hL₁' hL₁c _ hK
  obtain ⟨m, g, y, hg, hgy, hrep⟩ := hA
  refine ⟨N, hN, m, g, y, hg, hgy, fun p hp => ?_⟩
  have fix : ∀ x ∈ L₁', ∀ y₁ ∈ L₂', GlobalTheory.WeilM.schr ψ (adeleJoin D.host.F 0 x,
      adeleJoin D.host.F 0 y₁) (om p Φ) = om p Φ := by
    intro x hx y₁ hy₁
    have hxy := hNL p hp x hx y₁ hy₁
    obtain ⟨x', hx', y', hy', he⟩ := hxy
    have := impl p (co.e.symm (adeleJoin D.host.F 0 x', adeleJoin D.host.F 0 y')) Φ hΦ
    simp only [GlobalTheory.WeilM.Darboux.rho, LinearEquiv.apply_symm_apply, hinv x' hx' y' hy', he] at this
    exact this.symm
  refine hrep (om p Φ) (pres p Φ hΦ) ?_ ?_
  · intro x hx z
    have := congrFun (fix x hx 0 (zero_mem _)) z
    simp only [GlobalTheory.WeilM.schr, adeleJoin_zero_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul] at this
    exact this
  · intro z hz y₁ hy₁
    have := congrFun (fix 0 (zero_mem _) y₁ hy₁) z
    simp only [GlobalTheory.WeilM.schr, adeleJoin_zero_zero, zero_dotProduct, mul_zero, add_zero,
      dotProduct_adeleJoin_zero] at this
    exact (mul_eq_right₀ hz).mp this

end GlobalTheory.WeilCont

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSatakeSphericalVectorDefiniteUnitary
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FrameAut

theorem exists_locComp_hasSatGL_heckeVec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (π : Submodule ℂ (UA E n → ℂ)), IsAutRepU π →
    ∀ w : HeightOneSpectrum (𝓞 E), IsSplitAt w → ∀ φ ∈ π, φ ≠ 0 →
    (∀ x ∈ locU n w, cLoc w x ∈ GlobalTheory.LFun.KGL w (n := n) → RU E n x φ = φ) →
    ∃ (σ : SmIrr (GL (Fin n) (w.adicCompletion E))) (S : Multiset ℂˣ),
      IsCompAlong π (locU n w) ((cLoc w).comp (locU n w).subtype) σ.ρ ∧ GlobalTheory.LFun.HasSatGL w σ.ρ S ∧
      ∀ k ≤ n, GlobalTheory.LFun.heckeVec ((RU E n).comp (locU n w).subtype) ((GlobalTheory.LFun.KGL w (n := n)).comap ((cLoc w).comp (locU n w).subtype))
        (fun x => GlobalTheory.SphPar.divInd (Formalism.UG.Ov E w) (Formalism.IndefR.Mult.dualLab (Formalism.IndefR.Mult.splitLab n k)) ((cLoc w).comp (locU n w).subtype x)) φ =
        GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n S k • φ := by
  intro E _ _ _ n π hπ w hw φ hφ h0 hfix
  obtain ⟨σ, -, hloc, hiff⟩ := GlobalTheory.DefU.exists_locComp_split E n ⟨π, hπ⟩ w hw
  obtain ⟨S, hS⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible σ.smooth σ.irred (hiff.1 ⟨φ, hφ, h0, hfix⟩)
  obtain ⟨e, he⟩ := GlobalTheory.locU_equiv_GL E n w hw
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LFun.exists_isUnifV w
  have hp : Function.Surjective ((cLoc w).comp (locU n w).subtype) := fun g =>
    ⟨e.symm g, (he _).symm.trans (e.apply_symm_apply g)⟩
  refine ⟨σ, S, hloc, hS, fun k hk => ?_⟩
  rw [GlobalTheory.SphPar.divInd_dualLab_splitLab E w n k hϖ]
  exact GlobalTheory.SplitTransfer.heckeVec_eq_of_isCompAlong hπ w (Formalism.UG.Final.GLintComm E w n) _ hp σ.ρ hloc
    (GlobalTheory.LFun.Tj_mem_hecke hϖ k) (fun v hv hv0 => (hS.2 v hv hv0).2.2.2 ϖ hϖ k hk) hφ fun x hx => hfix x x.2 hx

end GlobalTheory.FrameAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.KirillovSemilocalSmoothBumpStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix
open scoped ContDiff
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kirillov_semilocal_smooth_bump : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (m : ℕ) (S : Finset (HeightOneSpectrum (𝓞 E))) (b : GA E (m + 1) → ℂ), (∀ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), ∀ g, b (u * g) = GlobalTheory.JSW.psiN u * b g) → (∃ C : Set (GA E (m + 1)), IsCompact C ∧ ∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), b p ≠ 0 → ∃ u ∈ GlobalTheory.JSW.NA (E := E) (a := (m + 1)), u⁻¹ * p ∈ C) → (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, b (g * finGL E (m + 1) u) = b g) → (∀ g, ContDiffOn ℝ ∞ (chart b g) (invSet E (m + 1))) → ∀ (π : CuspSub E (m + 1)) (φ : Sm E (m + 1)), φ ∈ π.V → (∃ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 x ≠ 0) → ∃ F ∈ GlobalTheory.JSW.mspanR π, (∀ p ∈ (GlobalTheory.JSW.supS (E := E) (a := m + 1) S ∩ GlobalTheory.JSW.mirSet (GlobalTheory.CuspRep.Ad E) m), GlobalTheory.JSW.whit F p = b p) ∧ (∃ U : Subgroup (GL (Fin (m + 1)) (Af E)), IsOpen (U : Set (GL (Fin (m + 1)) (Af E))) ∧ ∀ u ∈ U, ∀ g, F (g * finGL E (m + 1) u) = F g) ∧ (∀ t : GA E (m + 1), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ g, φ.1 (g * t) = φ.1 g) → ∀ g, F (g * t) = F g) ∧ ∀ (t : GA E (m + 1)) (c : ℂ), GeneralLinearGroup.map (pInf E) t = 1 → (∀ w ∈ S, GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) t = 1) → (∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit φ.1 (x * t) = c * GlobalTheory.JSW.whit φ.1 x) → ∀ x ∈ GlobalTheory.JSW.supS (E := E) (a := (m + 1)) S, GlobalTheory.JSW.whit F (x * t) = c * GlobalTheory.JSW.whit F x := by
  first | (exact @GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (exact GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump) | (intros; apply GlobalTheory.JSW.KirSemi.kirillov_semilocal_bump  <;> assumption)
end

