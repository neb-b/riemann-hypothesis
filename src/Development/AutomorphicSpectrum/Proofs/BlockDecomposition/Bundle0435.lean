module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0385
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0418
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MirabolicDoubleCosetDecomposition
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0420
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0380
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0396
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0422
public import Development.AutomorphicSpectrum.Proofs.HermitianForms.Imports
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.AffineGLForms.CuspInvariantsFinite.CuspInvFin
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaNormCommutation.LocalComparisonSplitting.EulerFactorLevels.EulerFinOf
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0409

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfEigOfMemTwKer
section
noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.BZPhiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPhiPG.LocO

open MeasureTheory GlobalTheory.CompanionTheory.TwistedAverage GlobalTheory.CompanionTheory.Rodier

theorem eq_zero_of_eig_of_mem_twKer {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) {L : Subgroup G}
    (hL : IsCompact (L : Set G)) (θ : L →* ℂˣ) (hθ : IsOpen (θ.ker : Set L)) {x : V}
    (hx : x ∈ twKer ρ L θ) (he : ∀ l : L, ρ (l : G) x = (θ l : ℂ) • x) : x = 0 := by
  classical
  obtain ⟨M, hM, hs⟩ := exists_sum_eq_zero hρ hL θ hθ hx
  haveI : M.FiniteIndex := hM
  haveI : M.normalCore.FiniteIndex := inferInstance
  haveI : M.normalCore.Normal := Subgroup.normalCore_normal _
  haveI : Finite (L ⧸ M.normalCore) := Subgroup.finite_quotient_of_finiteIndex
  letI : Fintype (L ⧸ M.normalCore) := Fintype.ofFinite _
  have h0 := hs M.normalCore (Subgroup.normalCore_le M)
  have h1 : ∀ t : L, twOrbit ρ L θ x t = x := fun t => by
    rw [twOrbit, he t, smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
  simp only [h1, Finset.sum_const, Finset.card_univ] at h0
  rw [← Nat.cast_smul_eq_nsmul ℂ, smul_eq_zero] at h0
  rcases h0 with h0 | h0
  · exact absurd h0 (Nat.cast_ne_zero.2 Fintype.card_ne_zero)
  · exact h0

theorem isSmooth_cInd {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) : IsSmooth (cInd H σ) := by
  intro f
  have h : {g : G | cInd H σ g f = f} = {g : G | ind H σ g f.1.1 = f.1.1} := by
    ext g
    exact ⟨fun h => congrArg (fun x : cIndSpace H σ => x.1.1) h, fun h => Subtype.ext (Subtype.ext h)⟩
  rw [h]
  exact f.1.2

def evL {G Z : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] (H : Subgroup G) (σ : Representation ℂ H Z) (x : G) : cIndSpace H σ →ₗ[ℂ] Z :=
  (LinearMap.proj x) ∘ₗ (indSpace H σ).subtype ∘ₗ (smoothPart (ind H σ)).subtype ∘ₗ (cIndSpace H σ).subtype

theorem avgVanish_of_fibre {G Z Γ A : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup Z] [Module ℂ Z] [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure]
    (H : Subgroup G) (σ : Representation ℂ H Z) (U : Subgroup G) (θ : U →* ℂˣ)
    (ρ₁ : Representation ℂ Γ Z) (hρ₁ : IsSmooth ρ₁)
    (C : Subgroup Γ) (hC : IsCompact (C : Set Γ)) (χ : C →* ℂˣ) (hχ : IsOpen (χ.ker : Set C))
    (c : C → H) (hc : ∀ (b : C) (w : Z), σ (c b) w = ρ₁ (b : Γ) w)
    (e : A → G) (he : ∀ a a', e (a + a') = e a * e a')
    (hce : ∀ (b : C) (a : A), ((c b : H) : G) * e a = e a * ((c b : H) : G))
    (y : G) (D : Set A) (hD0 : (0 : A) ∈ D) (hDs : ∀ a a', a ∈ D → a' ∈ D → a - a' ∈ D)
    (hDc : IsCompact D) (hDo : IsOpen D)
    (L : Subgroup G) (hLU : L ≤ U) (hLc : IsCompact (L : Set G))
    (hθ : IsOpen ((θ.comp (Subgroup.inclusion hLU)).ker : Set L))
    (hL1 : ∀ l : L, ∃ (b : C) (a : A), a ∈ D ∧ y * (l : G) * y⁻¹ = ((c b : H) : G) * e a ∧
      θ (Subgroup.inclusion hLU l) = χ b)
    (hL2 : ∀ b : C, ∃ l : L, y * (l : G) * y⁻¹ = ((c b : H) : G) ∧ θ (Subgroup.inclusion hLU l) = χ b)
    (hL3 : ∀ a ∈ D, ∃ l : L, y * (l : G) * y⁻¹ = e a ∧ θ (Subgroup.inclusion hLU l) = 1)
    (hU : ∀ u ∈ U, ∃ h ∈ H, ∃ a : A, y * u * y⁻¹ = h * e a)
    (hfib : ∀ f' : cIndSpace H σ, IsLocallyConstant (fun a => evL H σ (e a * y) f') ∧
      HasCompactSupport (fun a => evL H σ (e a * y) f'))
    (f : cIndSpace H σ) (hsupp : ∀ a, evL H σ (e a * y) f ≠ 0 → a ∈ D)
    (hz : smInt μ (fun a => evL H σ (e a * y) f) ∈ twKer ρ₁ C χ) :
    AvgVanish H σ U θ f y := by
  classical
  have hev : ∀ (x l : G) (f' : cIndSpace H σ), evL H σ x (cInd H σ l f') = evL H σ (x * l) f' := fun _ _ _ => rfl
  have hleft : ∀ (h : H) (x : G) (f' : cIndSpace H σ), evL H σ ((h : G) * x) f' = σ h (evL H σ x f') :=
    fun h x f' => f'.1.1.2 h x
  have he0 : e 0 = 1 := by
    have := he 0 0
    rw [add_zero] at this
    exact (mul_eq_left.1 this.symm)
  set θL : L →* ℂˣ := θ.comp (Subgroup.inclusion hLU) with hθL
  obtain ⟨ι, _, r, c₀, h1, h2⟩ := GlobalTheory.CompanionTheory.TwAvgInd.exists_finite_average (cInd H σ) (isSmooth_cInd H σ) hLc θL hθ f
  obtain ⟨g, hg⟩ : ∃ g : cIndSpace H σ, g = c₀ • ∑ i, twOrbit (cInd H σ) L θL f (r i) := ⟨_, rfl⟩
  rw [← hg] at h1
  simp only [← hg] at h2

  let T : cIndSpace H σ →ₗ[ℂ] Z :=
    { toFun := fun f' => smInt μ (fun a => evL H σ (e a * y) f')
      map_add' := fun f₁ f₂ => by
        have := SmIntEl.smInt_add μ (hfib f₁).1 (hfib f₁).2 (hfib f₂).1 (hfib f₂).2
        rw [← this]
        congr 1
      map_smul' := fun s f' => by
        have := SmIntEl.smInt_linear μ (s • (LinearMap.id : Z →ₗ[ℂ] Z)) (hfib f').1 (hfib f').2
        simp only [LinearMap.smul_apply, LinearMap.id_apply, RingHom.id_apply] at this ⊢
        rw [← this]
        congr 1 }
  have hTdef : ∀ f', T f' = smInt μ (fun a => evL H σ (e a * y) f') := fun _ => rfl
  have hpoint : ∀ (l : G) (b : C) (a₁ a : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ →
      e a * y * l = ((c b : H) : G) * (e (a₁ + a) * y) := by
    intro l b a₁ a h
    have h' : y * l = ((c b : H) : G) * e a₁ * y := by rw [← h]; group
    have h2 : e (a₁ + a) = e a * e a₁ := by rw [add_comm, he]
    rw [mul_assoc, h', h2]
    simp only [← mul_assoc]
    rw [← hce b a]
  have hTl : ∀ (l : G) (b : C) (a₁ : A), y * l * y⁻¹ = ((c b : H) : G) * e a₁ → ∀ f',
      T (cInd H σ l f') = ρ₁ (b : Γ) (T f') := by
    intro l b a₁ hl f'
    set φ : A → Z := fun a => evL H σ (e a * y) f' with hφ
    have hfun : (fun a => evL H σ (e a * y) (cInd H σ l f')) = (ρ₁ (b : Γ)) ∘ (φ ∘ (fun a => a₁ + a)) := by
      funext a
      rw [hev, hpoint l b a₁ a hl, hleft, hc]
      rfl
    have hl₂ : IsLocallyConstant (φ ∘ fun a => a₁ + a) := (hfib f').1.comp_continuous (by fun_prop)
    have hc₂ : HasCompactSupport (φ ∘ fun a => a₁ + a) := (hfib f').2.comp_homeomorph (Homeomorph.addLeft a₁)
    rw [hTdef, hfun, SmIntEl.smInt_linear μ _ hl₂ hc₂,
      SmIntEl.smInt_comp_measurePreserving μ (measurePreserving_add_left μ a₁) (hfib f').1]
    rfl
  have hker : ∀ x ∈ twKer (cInd H σ) L θL, T x ∈ twKer ρ₁ C χ := by
    intro x hx
    have hle : twKer (cInd H σ) L θL ≤ (twKer ρ₁ C χ).comap T := by
      refine Submodule.span_le.2 ?_
      rintro w ⟨l, v, rfl⟩
      obtain ⟨b, a, -, h3, h4⟩ := hL1 l
      show T (_ - _) ∈ twKer ρ₁ C χ
      rw [map_sub, map_smul, hTl _ b a h3]
      have : θL l = χ b := h4
      rw [this]
      exact Submodule.subset_span ⟨b, T v, rfl⟩
    exact hle hx
  have hTg : T g ∈ twKer ρ₁ C χ := by
    have : T g = T f - T (f - g) := by rw [map_sub]; abel
    rw [this]
    exact Submodule.sub_mem _ hz (hker _ h1)
  have heig : ∀ b : C, ρ₁ (b : Γ) (T g) = (χ b : ℂ) • T g := by
    intro b
    obtain ⟨l, h3, h4⟩ := hL2 b
    have h5 : y * (l : G) * y⁻¹ = ((c b : H) : G) * e 0 := by rw [he0, mul_one, h3]
    rw [← hTl _ b 0 h5 g, h2 l, map_smul]
    have : θL l = χ b := h4
    rw [this]
  have hTg0 : T g = 0 := eq_zero_of_eig_of_mem_twKer hρ₁ hC χ hχ hTg heig

  have hsg : ∀ a, evL H σ (e a * y) g ≠ 0 → a ∈ D := by
    intro a ha
    by_contra hn
    apply ha
    have hz0 : ∀ i, evL H σ (e a * y) (twOrbit (cInd H σ) L θL f (r i)) = 0 := by
      intro i
      obtain ⟨b, a₁, ha₁, h3, -⟩ := hL1 (r i)
      rw [twOrbit, map_smul, hev, hpoint _ b a₁ a h3, hleft]
      have : evL H σ (e (a₁ + a) * y) f = 0 := by
        by_contra h
        have h6 := hsupp _ h
        apply hn
        have := hDs _ _ h6 ha₁
        rwa [add_sub_cancel_left] at this
      rw [this, map_zero, smul_zero]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hg, map_smul, map_sum, Finset.sum_eq_zero fun i _ => hz0 i, smul_zero]

  have hper : ∀ a ∈ D, evL H σ (e a * y) g = evL H σ (e 0 * y) g := by
    intro a ha
    obtain ⟨l, h3, h4⟩ := hL3 a ha
    have h5 := congrArg (evL H σ (e 0 * y)) (h2 l)
    rw [hev, map_smul] at h5
    have h6 : e 0 * y * (l : G) = e a * y := by
      rw [he0, one_mul]
      have : y * (l : G) = e a * y := by rw [← h3]; group
      exact this
    rw [h6] at h5
    have h7 : θL l = 1 := h4
    rw [h5, h7]
    simp
  have hφ : (fun a => evL H σ (e a * y) g) = D.indicator fun _ => evL H σ (e 0 * y) g := by
    funext a
    by_cases ha : a ∈ D
    · rw [Set.indicator_of_mem ha, hper a ha]
    · rw [Set.indicator_of_notMem ha]
      by_contra h
      exact ha (hsg a h)
  have hv0 : evL H σ (e 0 * y) g = 0 := by
    have h3 : T g = (((μ D).toReal : ℝ) : ℂ) • evL H σ (e 0 * y) g := by
      rw [hTdef, hφ, SmIntEl.smInt_indicator]
    rw [hTg0] at h3
    have hpos : (μ D).toReal ≠ 0 :=
      (ENNReal.toReal_pos (hDo.measure_pos μ ⟨0, hD0⟩).ne' hDc.measure_lt_top.ne).ne'
    rcases smul_eq_zero.1 h3.symm with h4 | h4
    · exact absurd (Complex.ofReal_eq_zero.1 h4) hpos
    · exact h4
  refine ⟨L, hLU, hLc, g, h1, fun l => h2 l, fun u hu => ?_⟩
  obtain ⟨h, hh, a, hua⟩ := hU u hu
  have h3 : y * u = (h : G) * (e a * y) := by
    have : y * u = (y * u * y⁻¹) * y := by group
    rw [this, hua, mul_assoc]
  show evL H σ (y * u) g = 0
  rw [h3]
  have h4 : evL H σ ((h : G) * (e a * y)) g = σ ⟨h, hh⟩ (evL H σ (e a * y) g) := hleft ⟨h, hh⟩ _ g
  rw [h4]
  have h5 : evL H σ (e a * y) g = 0 := by
    rw [show evL H σ (e a * y) g = _ from congrFun hφ a, hv0]
    simp
  rw [h5, map_zero]

end GlobalTheory.CompanionTheory.BZPhiPG.LocO

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOnUnitaryOfVanishAtOne
section
noncomputable section

open Matrix Finset MeasureTheory
open scoped ContDiff ComplexConjugate InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD
open PositivityTheory.RgTw (Mat)
open GlobalTheory.CompanionTheory.GLK (e1 e2 f1)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace GlobalTheory.CompanionTheory.ModelS.Sep

variable {n : ℕ}

theorem sum_swap (X P Q : Fin n → Fin n → ℂ) :
    ∑ a, ∑ b, X a b * (P a b - Q b a) = ∑ a, ∑ b, (X a b * P a b - X b a * Q a b) := by
  simp only [mul_sub, Finset.sum_sub_distrib]
  congr 1
  exact Finset.sum_comm

theorem real_linear_skew (L : Mat n →ₗ[ℝ] ℂ) (X : Mat n) (hX : Xᴴ = -X) :
    L X = ∑ a, ∑ b, X a b * ((1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I))
      - (1 / 2 : ℂ) * (L (Matrix.single b a 1) + Complex.I * L (Matrix.single b a Complex.I))) := by
  have hs : ∀ (a b : Fin n) (z : ℂ), Matrix.single a b z =
      z.re • Matrix.single a b (1 : ℂ) + z.im • Matrix.single a b Complex.I := by
    intro a b z
    simp only [Matrix.smul_single]
    rw [← Matrix.single_add]
    simp only [Complex.real_smul, mul_one, Complex.re_add_im]
  have hX' : ∀ a b, X b a = -conj (X a b) := by
    intro a b
    have := congrFun (congrFun hX a) b
    simp only [Matrix.conjTranspose_apply, Matrix.neg_apply] at this
    have h2 := congrArg (starRingEnd ℂ) this
    simpa using h2
  have h1 : L X = ∑ a, ∑ b, (((X a b).re : ℂ) * L (Matrix.single a b 1) + ((X a b).im : ℂ) * L (Matrix.single a b Complex.I)) := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single X]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    rw [hs a b (X a b), map_add (f := _), map_smul, map_smul]
    simp [Complex.real_smul]
  rw [h1]
  refine Eq.trans ?_ (sum_swap (fun a b => X a b)
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) - Complex.I * L (Matrix.single a b Complex.I)))
    (fun a b => (1 / 2 : ℂ) * (L (Matrix.single a b 1) + Complex.I * L (Matrix.single a b Complex.I)))).symm
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [hX' a b]
  have hc : conj (X a b) = ((X a b).re : ℂ) - ((X a b).im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  have hz : ((X a b).re : ℂ) + ((X a b).im : ℂ) * Complex.I = X a b := Complex.re_add_im _
  have key : ∀ x y p q : ℂ, x * p + y * q = (x + y * Complex.I) * ((1 / 2 : ℂ) * (p - Complex.I * q))
      - (-(x - y * Complex.I)) * ((1 / 2 : ℂ) * (p + Complex.I * q)) := by
    intro x y p q
    linear_combination (y * q) * Complex.I_sq
  have := key (X a b).re (X a b).im (L (Matrix.single a b 1)) (L (Matrix.single a b Complex.I))
  rw [hz, ← hc] at this
  exact this

theorem Kf_apply (a b : Fin n) (h : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (1 / 2 : ℂ) * (Rd (Matrix.single a b 1) h.1 g - Complex.I * Rd (Matrix.single a b Complex.I) h.1 g)
      - (1 / 2 : ℂ) * (Rd (Matrix.single b a 1) h.1 g + Complex.I * Rd (Matrix.single b a Complex.I) h.1 g) := by
  have e : (GlobalTheory.CompanionTheory.ModelS.Kf a b h).1 g = (e1 GlobalTheory.CompanionTheory.ModelS.DR a b h).1 g - (f1 GlobalTheory.CompanionTheory.ModelS.DR b a h).1 g := by
    simp [GlobalTheory.CompanionTheory.ModelS.Kf, e2, sub_eq_add_neg]
  rw [e, GlobalTheory.CompanionTheory.ModelS.orderedCechToCatCochainsOne_apply_valueAtSubset a b h hg, GlobalTheory.CompanionTheory.ModelS.liftOneFormsToCompatible_apply b a h hg]
  simp [Eu]
  ring

def AX (X : Mat n) : Module.End ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n) := ∑ a, ∑ b, X a b • GlobalTheory.CompanionTheory.ModelS.Kf a b

theorem AX_apply (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) {g : Mat n} (hg : g ∈ GLs n) :
    (AX X w).1 g = Rd X w.1 g := by
  let L : Mat n →ₗ[ℝ] ℂ := ((fderiv ℝ w.1 g).comp (GlobalTheory.CompanionTheory.RCalc.mulL g)).toLinearMap
  have hL : ∀ v, L v = Rd v w.1 g := fun _ => rfl
  have e : (AX X w).1 g = ∑ a, ∑ b, X a b * (GlobalTheory.CompanionTheory.ModelS.Kf a b w).1 g := by
    simp [AX, LinearMap.sum_apply, Finset.sum_apply]
  rw [e, ← hL X, real_linear_skew L X hX]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
  rw [Kf_apply a b w hg]
  rfl

theorem AX_mem (X : Mat n) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n))
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) {w : GlobalTheory.CompanionTheory.ModelS.SmF n} (hw : w ∈ S) :
    AX X w ∈ S := by
  simp only [AX, LinearMap.sum_apply, LinearMap.smul_apply]
  exact S.sum_mem fun a _ => S.sum_mem fun b _ => S.smul_mem _ (hS a b w hw)

open scoped Matrix.Norms.Operator in
theorem exp_entry (X : Mat n) (t : ℝ) (i j : Fin n) :
    HasDerivAt (fun t : ℝ => (NormedSpace.exp ((t : ℂ) • X)) i j) ((NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
  have h := hasDerivAt_exp_smul_const (𝕂 := ℝ) X t
  let L : Mat n →L[ℝ] ℂ := LinearMap.toContinuousLinearMap (Matrix.entryLinearMap ℝ ℂ i j)
  have := L.hasFDerivAt.comp_hasDerivAt t h
  simp only [Complex.coe_smul] at this ⊢
  exact this

theorem exp_deriv (X : Mat n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => NormedSpace.exp ((t : ℂ) • X)) (NormedSpace.exp ((t : ℂ) • X) * X) t := by
  have : HasDerivAt (fun t : ℝ => (fun i j => (NormedSpace.exp ((t : ℂ) • X)) i j : Fin n → Fin n → ℂ))
      (fun i j => (NormedSpace.exp ((t : ℂ) • X) * X) i j) t := by
    rw [hasDerivAt_pi]
    intro i
    rw [hasDerivAt_pi]
    intro j
    exact exp_entry X t i j
  exact this

theorem exp_mem (X : Mat n) (t : ℝ) : NormedSpace.exp ((t : ℂ) • X) ∈ GLs n := by
  have h : IsUnit (NormedSpace.exp ((t : ℂ) • X)) := (GlobalTheory.CompanionTheory.GLK.expG X t).isUnit
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h).ne_zero

theorem curve_deriv (X : Mat n) (hX : Xᴴ = -X) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (t : ℝ) :
    HasDerivAt (fun t : ℝ => w.1 (NormedSpace.exp ((t : ℂ) • X))) ((AX X w).1 (NormedSpace.exp ((t : ℂ) • X))) t := by
  have hg := exp_mem X t
  have hd := (GlobalTheory.CompanionTheory.RCalc.differentiableAt_of_smooth w.2.1 hg).hasFDerivAt
  have := hd.comp_hasDerivAt t (exp_deriv X t)
  rw [AX_apply X hX w hg]
  exact this

theorem ode_zero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (B : E →L[ℝ] E) (f : ℝ → E)
    (h : ∀ t, HasDerivAt f (B (f t)) t) (h0 : f 0 = 0) (t : ℝ) : f t = 0 := by
  have := ODE_solution_unique_univ (v := fun _ => B) (s := fun _ => Set.univ) (K := ‖B‖₊) (t₀ := 0)
    (f := f) (g := fun _ => 0)
    (fun _ => B.lipschitzWith.lipschitzOnWith)
    (fun t => ⟨h t, trivial⟩) (fun t => ⟨by simpa using hasDerivAt_const t (0 : E), trivial⟩) h0
  exact congrFun this t

theorem vanish_curve (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)) (fd : FiniteDimensional ℂ S)
    (hS : ∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) (h1 : ∀ w ∈ S, w.1 1 = 0)
    (X : Mat n) (hX : Xᴴ = -X) (t : ℝ) (w : GlobalTheory.CompanionTheory.ModelS.SmF n) (hw : w ∈ S) :
    w.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := by
  classical
  let bs := Module.finBasis ℂ S
  let C : Matrix (Fin (Module.finrank ℂ S)) (Fin (Module.finrank ℂ S)) ℂ :=
    fun i j => bs.repr ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ j
  have hexp : ∀ (u : S) (g : Mat n), u.1.1 g = ∑ j, bs.repr u j * (bs j).1.1 g := by
    intro u g
    have h := congrArg (fun v : S => v.1.1 g) (bs.sum_repr u)
    simp only [Submodule.coe_sum, Submodule.coe_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h
    exact h.symm
  let f : ℝ → Fin (Module.finrank ℂ S) → ℂ := fun t i => (bs i).1.1 (NormedSpace.exp ((t : ℂ) • X))
  let B : (Fin (Module.finrank ℂ S) → ℂ) →L[ℝ] (Fin (Module.finrank ℂ S) → ℂ) :=
    (LinearMap.toContinuousLinearMap (Matrix.toLin' C)).restrictScalars ℝ
  have hd : ∀ t, HasDerivAt f (B (f t)) t := by
    intro t
    rw [hasDerivAt_pi]
    intro i
    have hc := curve_deriv X hX (bs i).1 t
    have e : (AX X (bs i).1).1 (NormedSpace.exp ((t : ℂ) • X)) = B (f t) i := by
      have := hexp ⟨AX X (bs i).1, AX_mem X S hS (bs i).2⟩ (NormedSpace.exp ((t : ℂ) • X))
      refine this.trans ?_
      show _ = (C.mulVec (f t)) i
      rfl
    rw [← e]
    exact hc
  have h0 : f 0 = 0 := by
    funext i
    simpa [f] using h1 _ (bs i).2
  have hz := ode_zero B f hd h0 t
  rw [hexp ⟨w, hw⟩]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : (bs j).1.1 (NormedSpace.exp ((t : ℂ) • X)) = 0 := congrFun hz j
  rw [this, mul_zero]

theorem main : ∀ (n : ℕ) (S : Submodule ℂ (GlobalTheory.CompanionTheory.ModelS.SmF n)), FiniteDimensional ℂ S →
    (∀ a b : Fin n, ∀ w ∈ S, GlobalTheory.CompanionTheory.ModelS.Kf a b w ∈ S) → (∀ w ∈ S, w.1 1 = 0) →
    ∀ w ∈ S, ∀ k : Matrix.unitaryGroup (Fin n) ℂ, w.1 k.1 = 0 := by
  intro n S fd hS h1 w hw k
  obtain ⟨X, hX, hk⟩ := GlobalTheory.CompanionTheory.UnitaryLog.main n k
  have := vanish_curve S fd hS h1 X hX 1 w hw
  simp only [Complex.ofReal_one, one_smul] at this
  rw [hk]
  exact this

end GlobalTheory.CompanionTheory.ModelS.Sep
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMonicAevalMemOfLeSup
section
open NumberField GlobalTheory.CuspRep MeasureTheory PositivityTheory.Affgl

namespace GlobalTheory.CompanionTheory.Affgl

theorem exists_monic_aeval_mem_of_le_sup {R : Type*} [Ring R] [Algebra ℂ R] (A : Subalgebra ℂ R)
    (V I : Submodule ℂ R) [FiniteDimensional ℂ V] (h : ∀ z ∈ A, z ∈ V ⊔ I) (z : R) (hz : z ∈ A) :
    ∃ p : Polynomial ℂ, p.Monic ∧ Polynomial.aeval z p ∈ I := by
  have hmemA : ∀ p : Polynomial ℂ, Polynomial.aeval z p ∈ A := by
    intro p
    have e : Polynomial.aeval z p = ((Polynomial.aeval (⟨z, hz⟩ : A) p : A) : R) := by
      simpa using (Polynomial.aeval_algHom_apply A.val (⟨z, hz⟩ : A) p)
    rw [e]
    exact Subtype.property _
  let f : Polynomial ℂ →ₗ[ℂ] R ⧸ I := I.mkQ ∘ₗ (Polynomial.aeval z).toLinearMap
  have hf : ∀ p, f p ∈ V.map I.mkQ := by
    intro p
    obtain ⟨v, hv, i, hi, e⟩ := Submodule.mem_sup.1 (h _ (hmemA p))
    refine ⟨v, hv, ?_⟩
    change I.mkQ v = I.mkQ (Polynomial.aeval z p)
    have hi0 : I.mkQ i = 0 := by simpa using hi
    rw [← e, map_add (f := _), hi0, add_zero]
  let g : Polynomial ℂ →ₗ[ℂ] V.map I.mkQ := f.codRestrict _ hf
  have hnot : ¬ Function.Injective g := fun hinj =>
    Polynomial.not_finite (R := ℂ) (Module.Finite.of_injective g hinj)
  obtain ⟨p, hgp, hp⟩ : ∃ p, g p = 0 ∧ p ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hnot ((injective_iff_map_eq_zero g).2 fun p hp => hcon p hp)
  have hI : Polynomial.aeval z p ∈ I := by
    have : f p = 0 := congrArg Subtype.val hgp
    simpa [f] using this
  refine ⟨p * Polynomial.C p.leadingCoeff⁻¹, Polynomial.monic_mul_leadingCoeff_inv hp, ?_⟩
  rw [map_mul, Polynomial.aeval_C, ← Algebra.commutes, ← Algebra.smul_def]
  exact I.smul_mem _ hI

theorem exists_monic_aeval_apply_eq_zero (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E]
    (a : ℕ) (J : Set (Module.End ℂ (Sm E a))) (hJ : Cofin J) (z : Module.End ℂ (Sm E a))
    (hz : z ∈ Zalg E a) :
    ∃ p : Polynomial ℂ, p.Monic ∧ ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) →
      Polynomial.aeval z p φ = 0 := by
  obtain ⟨-, V, hV, hcov⟩ := hJ
  obtain ⟨p, hp, hI⟩ := exists_monic_aeval_mem_of_le_sup (Zalg E a) V _ hcov z hz
  refine ⟨p, hp, fun φ hφ => ?_⟩
  have key : ∀ y ∈ Submodule.span ℂ {y | ∃ x ∈ Zalg E a, ∃ j ∈ J, y = x * j}, y φ = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨x, -, j, hj, rfl⟩ := hy
      simp [hφ j hj]
    | zero => simp
    | add u v _ _ hu hv => simp [hu, hv]
    | smul c u _ hu => simp [hu]
  exact key _ hI

theorem minpoly_on_killed : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ),
    ∀ J : Set (Module.End ℂ (Sm E a)), Cofin J → ∀ z ∈ Zalg E a, ∃ p : Polynomial ℂ, p.Monic ∧
      ∀ φ : Sm E a, (∀ j ∈ J, j φ = 0) → Polynomial.aeval z p φ = 0 :=
  fun E _ _ _ a J hJ z hz => exists_monic_aeval_apply_eq_zero E a J hJ z hz

end GlobalTheory.CompanionTheory.Affgl
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeIntegralFiniteSum
section
open GlobalTheory.BCT PositivityTheory.Rg.BcB.G8.Fin
open scoped Classical

namespace GlobalTheory.CompanionTheory.HintLevelPt

theorem hint_eq_level_of_forall : ∀ (H : Type) [Group H] (K L : Subgroup H) (u : H → ℂ), L ≤ K →
    L.relIndex K ≠ 0 → (∀ l ∈ L, ∀ x, u (x * l) = u x) →
    hint K u = ((L.relIndex K : ℕ) : ℂ)⁻¹ * ∑ᶠ p : H ⧸ L, u p.out := by
  intro H _ K L u hLK hfin hu
  exact GlobalTheory.CompanionTheory.HintLevel.hint_eq_level H K L u hLK (fun l hl x => hu l hl x) hfin

end GlobalTheory.CompanionTheory.HintLevelPt
end

