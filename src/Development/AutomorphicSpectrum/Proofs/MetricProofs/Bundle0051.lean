module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.LatticeLemmas.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.ArithDegreeExact
public import GroundTheory.HeightsAndTheta.Heights.Slopes
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0041
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0034
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianBundleQuotientDegreeBound
section
open GroundTheory.Heights₂.Heights NumberField TensorProduct ComplexAt GlobalTheory.CompanionTheory.Ar Matrix
open scoped BigOperators ComplexOrder

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PtBoundary

variable {K : Type} [Field K] [NumberField K]

theorem finrank_submodule_of_torsion {R M : Type*} [CommRing R] [IsDomain R] [AddCommGroup M]
    [Module R M] (N : Submodule R M) (h : ∀ x : M, ∃ a : R, a ≠ 0 ∧ a • x ∈ N) :
    Module.finrank R N = Module.finrank R M := by
  have h0 : Module.rank R (M ⧸ N) = 0 := by
    rw [rank_eq_zero_iff]
    intro x
    obtain ⟨x, rfl⟩ := N.mkQ_surjective x
    obtain ⟨a, ha, hax⟩ := h x
    refine ⟨a, ha, ?_⟩
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact hax
  have h1 := rank_quotient_add_rank_of_isDomain N
  rw [h0, zero_add] at h1
  simp only [Module.finrank, h1]

theorem saturated_ker (E E' : HermitianBundle.{0} K) (q : E.carrier →ₗ[𝓞 K] E'.carrier) :
    E.Saturated (LinearMap.ker q) := by
  intro a x ha hx
  rw [LinearMap.mem_ker, map_smul] at hx
  rw [LinearMap.mem_ker]
  have : Module.IsTorsionFree (𝓞 K) E'.carrier := inferInstance
  exact (smul_eq_zero.mp hx).resolve_left ha

def barMap (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier) (hP : E.Saturated P)
    (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) :
    (E.quot P hP).carrier →ₗ[𝓞 K] E'.carrier :=
  P.liftQ q hq

theorem sqAt_barMap_le (E E' : HermitianBundle.{0} K) (P : Submodule (𝓞 K) E.carrier)
    (hP : E.Saturated P) (q : E.carrier →ₗ[𝓞 K] E'.carrier) (hq : P ≤ LinearMap.ker q) (c : ℝ)
    (h : ∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier),
      sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ c * sqAt E σ x)
    (σ : K →+* ℂ) (y : Fibre σ (E.quot P hP).carrier) :
    sqAt E' σ ((barMap E E' P hP q hq).lTensor (ComplexAt σ) y) ≤
      c * sqAt (E.quot P hP) σ y := by
  letI := HermitianBundle.quot_projective hP
  let V := subFibre E.metric σ P
  let y' : Fibre σ (E.carrier ⧸ P) := y
  let s : Fibre σ E.carrier := fibreMap σ (HermitianBundle.quotSection E P hP) y'
  let v : FibreSpace E.metric σ := HermitianBundle.quotFibreMap E P hP σ y
  let x : Fibre σ E.carrier := (FibreSpace.equiv E.metric σ).symm v
  have hvx : FibreSpace.equiv E.metric σ x = v := by simp [x]
  have hdiff : FibreSpace.equiv E.metric σ s - v ∈ V := by
    have hv : v = Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) := rfl
    have e : Vᗮ.starProjection (FibreSpace.equiv E.metric σ s) =
        FibreSpace.equiv E.metric σ s - V.starProjection (FibreSpace.equiv E.metric σ s) := by
      rw [Submodule.starProjection_orthogonal']
      rfl
    rw [hv, e, sub_sub_cancel]
    exact V.starProjection_apply_mem _
  obtain ⟨w, hw⟩ := hdiff
  have hw' : fibreMap σ P.subtype w = s - x := by
    apply (FibreSpace.equiv E.metric σ).injective
    rw [map_sub, hvx]
    exact hw
  have hsub : q ∘ₗ P.subtype = 0 := by
    ext z
    exact hq z.2
  have hsec : q ∘ₗ HermitianBundle.quotSection E P hP = P.liftQ q hq := by
    have h1 : P.liftQ q hq ∘ₗ P.mkQ = q := Submodule.liftQ_mkQ P q hq
    calc q ∘ₗ HermitianBundle.quotSection E P hP
        = P.liftQ q hq ∘ₗ (P.mkQ ∘ₗ HermitianBundle.quotSection E P hP) := by
          rw [← LinearMap.comp_assoc, h1]
      _ = P.liftQ q hq := by
          rw [HermitianBundle.mkQ_comp_quotSection, LinearMap.comp_id]
  have hqx : (barMap E E' P hP q hq).lTensor (ComplexAt σ) y = q.lTensor (ComplexAt σ) x := by
    have h1 : fibreMap σ q s = (barMap E E' P hP q hq).lTensor (ComplexAt σ) y := by
      have h0 : fibreMap σ q s = fibreMap σ (P.liftQ q hq) y' :=
        (fibreMap_fibreMap σ q (HermitianBundle.quotSection E P hP) y').trans
          (congrArg (fun f => fibreMap σ f y') hsec)
      exact h0
    have h2 : fibreMap σ q (s - x) = 0 := by
      rw [← hw', fibreMap_fibreMap, hsub]
      simp [fibreMap]
    rw [map_sub, h1] at h2
    exact sub_eq_zero.mp h2
  have hnorm : sqAt (E.quot P hP) σ y = sqAt E σ x := by
    have h1 : sqAt E σ x = (inner ℂ (FibreSpace.equiv E.metric σ x) (FibreSpace.equiv E.metric σ x)).re := rfl
    rw [h1, hvx]
    rfl
  rw [hqx, hnorm]
  exact h σ x

theorem normDegree_top_eq (E : HermitianBundle.{0} K) :
    E.normDegree ⊤ = E.arithDegree / Module.finrank ℚ K := by
  rw [HermitianBundle.normDegree, HermitianBundle.degree_top_eq_arithDegree]

theorem final_real (C L ρ m x g : ℝ) (hC : 1 ≤ C) (hL : 0 ≤ L) (hρ : 0 ≤ ρ) (hm : 0 ≤ m) (hx : 0 ≤ x) (hg : 0 ≤ g)
    (hρg : ρ ≤ g) (hmx : m ≤ x + g * L) :
    C * Real.log (2 + ρ + m) + L / 2 ≤
      (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + x) + (C + g + g * L + L) := by
  have hgL : 0 ≤ g * L := mul_nonneg hg hL
  set C' := C + g + g * L + L with hC'
  have h1 : 2 + ρ + m ≤ 2 + C' + x := by rw [hC']; linarith
  have h0 : 0 < 2 + ρ + m := by linarith
  have h2 : Real.log (2 + ρ + m) ≤ Real.log (2 + C' + x) := Real.log_le_log h0 h1
  have h3 : 0 ≤ Real.log (2 + ρ + m) := Real.log_nonneg (by linarith)
  have h4 : C ≤ C' := by rw [hC']; linarith
  have h5 : C * Real.log (2 + ρ + m) ≤ C' * Real.log (2 + C' + x) :=
    mul_le_mul h4 h2 h3 (by linarith)
  have h6 : L / 2 ≤ C' := by rw [hC']; linarith
  linarith

theorem slopeMax_le_log : ∀ (g : ℕ) (C : ℝ), 1 ≤ C → ∃ C' : ℝ, 0 ≤ C' ∧ ∀ (K : Type) [Field K] [NumberField K] (E E' : HermitianBundle.{0} K) (r : ℕ) (ε : Fin r → E.carrier) (q : E.carrier →ₗ[𝓞 K] E'.carrier), Module.finrank (𝓞 K) E.carrier = g → LinearIndependent (𝓞 K) ε → LinearMap.ker q = Submodule.span (𝓞 K) (Set.range ε) → (∀ e' : E'.carrier, ∃ (a : 𝓞 K) (e : E.carrier), a ≠ 0 ∧ q e = a • e') → (∀ (σ : K →+* ℂ) (w : Fin r → ℂ), C⁻¹ * ∑ a, ‖w a‖ ^ 2 ≤ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ∧ sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) ≤ C * ∑ a, ‖w a‖ ^ 2) → (∀ (σ : K →+* ℂ) (x : Fibre σ E.carrier), sqAt E' σ (q.lTensor (ComplexAt σ) x) ≤ C * sqAt E σ x) → E'.slopeMax ≤ ((C * Real.log (2 + Module.finrank (𝓞 K) E'.carrier + max (-E'.normDegree ⊤) 0) : ℝ) : EReal) → E.slopeMax ≤ ((C' * Real.log (2 + C' + max (-E.normDegree ⊤) 0) + C' : ℝ) : EReal) := by
  intro g C hC
  have hC0 : 0 < C := by linarith
  have hL : 0 ≤ Real.log C := Real.log_nonneg hC
  refine ⟨C + g + g * Real.log C + Real.log C, by positivity, ?_⟩
  intro K _ _ E E' r ε q hg hli hker hfull hgram hexp hslope
  set L := Real.log C with hLdef
  set P : Submodule (𝓞 K) E.carrier := Submodule.span (𝓞 K) (Set.range ε) with hPdef
  have hP : E.Saturated P := hker ▸ saturated_ker E E' q
  have hPq : P ≤ LinearMap.ker q := hker.ge
  set X := HermitianBundle.subQuotExtension E P hP with hX
  set φ := barMap E E' P hP q hPq with hφ
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hφq : ∀ e, φ (P.mkQ e) = q e := fun e => rfl

  let b : Module.Basis (Fin r) (𝓞 K) (E.sub P).carrier := Module.Basis.span hli
  have hb : ∀ (σ : K →+* ℂ) (w : Fin r → ℂ),
      sqAt (E.sub P) σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        sqAt E σ (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a) := by
    intro σ w
    have h1 : X.incl.lTensor (ComplexAt σ) (∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] b a) =
        ∑ a, ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 K] ε a := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [LinearMap.lTensor_tmul]
      congr 1
      exact congrArg Subtype.val (Module.Basis.span_apply hli a)
    rw [← h1]
    simp only [sqAt]
    rw [X.incl_isometric]
  obtain ⟨hP1, hP2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.basis_slope_degree_bound K (E.sub P) r b C hC (fun σ w => by rw [hb]; exact hgram σ w)

  obtain ⟨hQ1, hQ2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.MapCompare.main K (E.quot P hP) E' φ C hφinj hC0
    (fun σ y => sqAt_barMap_le E E' P hP q hPq C hexp σ y)

  have hrP : Module.finrank (𝓞 K) (E.sub P).carrier = r := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  have hrk := X.finrank_eq
  have hrange : Module.finrank (𝓞 K) ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) =
      Module.finrank (𝓞 K) E'.carrier := by
    apply finrank_submodule_of_torsion
    intro e'
    obtain ⟨a, e, ha, he⟩ := hfull e'
    exact ⟨a, ha, he ▸ ⟨P.mkQ e, trivial, hφq e⟩⟩
  have hrQ : Module.finrank (𝓞 K) (E.quot P hP).carrier = Module.finrank (𝓞 K) E'.carrier := by
    rw [← hrange, Submodule.map_top]
    exact (LinearMap.finrank_range_of_inj hφinj).symm
  have hsum : r + Module.finrank (𝓞 K) E'.carrier = g := by
    rw [← hg, hrk, hrP, hrQ]
  obtain ⟨hI1, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.IndexBound.full_sublattice_normDegree_bounds K E' ((⊤ : Submodule (𝓞 K) (E.quot P hP).carrier).map φ) hrange

  have hdeg : E.normDegree ⊤ = (E.sub P).normDegree ⊤ + (E.quot P hP).normDegree ⊤ := by
    rw [normDegree_top_eq, normDegree_top_eq, normDegree_top_eq, X.arithDegree_eq_add, add_div]
  have hQd := hQ1 ⊤
  have hrkTop : (E.quot P hP).rank ⊤ = Module.finrank (𝓞 K) E'.carrier := by
    rw [HermitianBundle.rank, finrank_top, hrQ]
  rw [hrkTop] at hQd
  set ρ : ℕ := Module.finrank (𝓞 K) E'.carrier with hρ
  have hsumR : (r : ℝ) + ρ = g := by exact_mod_cast hsum
  have hP2' := (abs_le.mp hP2).2
  have hgL : (g : ℝ) * L = r * L + ρ * L := by rw [← hsumR]; ring
  have hrL : 0 ≤ (r : ℝ) * L := by positivity
  have hρL : 0 ≤ (ρ : ℝ) * L := by positivity
  have hm : max (-E'.normDegree ⊤) 0 ≤ max (-E.normDegree ⊤) 0 + g * L := by
    apply max_le
    · have := le_max_left (-E.normDegree ⊤) 0
      nlinarith
    · have := le_max_right (-E.normDegree ⊤) 0
      nlinarith
  have hreal := final_real C L ρ (max (-E'.normDegree ⊤) 0) (max (-E.normDegree ⊤) 0) g hC hL
    (by positivity) (le_max_right _ _) (le_max_right _ _) (by positivity)
    (by have : (0 : ℝ) ≤ r := by positivity
        linarith) hm
  have hfirst : L / 2 ≤ (C + g + g * L + L) * Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) + (C + g + g * L + L) := by
    have h0 : (0 : ℝ) ≤ g := by positivity
    have h1 : 0 ≤ (C + g + g * L + L) := by positivity
    have h2 : 0 ≤ Real.log (2 + (C + g + g * L + L) + max (-E.normDegree ⊤) 0) :=
      Real.log_nonneg (by have := le_max_right (-E.normDegree ⊤) 0; linarith)
    have h3 := mul_nonneg h1 h2
    nlinarith
  refine (SlopeMaxExtension.main K _ _ _ X).trans (max_le ?_ ?_)
  · exact hP1.trans (by exact_mod_cast hfirst)
  · refine hQ2.trans ((add_le_add_left hslope _).trans ?_)
    rw [← EReal.coe_add]
    exact_mod_cast hreal

end GlobalTheory.CompanionTheory.Ar.PtBoundary

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsParabolicTransvection
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

namespace GlobalTheory.CompanionTheory.Ar.PB.Parab

def IsParabolic {N : ℕ} (ca cb : Fin N) (M : Matrix (Fin N) (Fin N) ℂ) : Prop :=
  ∀ a b, b < a → ¬ (a = cb ∧ b = ca) → M a b = 0

theorem IsParabolic.mul {N : ℕ} {ca cb : Fin N} (hc : (cb : ℕ) = ca + 1)
    {A B : Matrix (Fin N) (Fin N) ℂ} (hA : IsParabolic ca cb A) (hB : IsParabolic ca cb B) :
    IsParabolic ca cb (A * B) := by
  intro a b hba hne
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h1 : c < a ∧ ¬ (a = cb ∧ c = ca)
  · rw [hA a c h1.1 h1.2, zero_mul]
  by_cases h2 : b < c ∧ ¬ (c = cb ∧ b = ca)
  · rw [hB c b h2.1 h2.2, mul_zero]
  exfalso
  simp only [Fin.lt_def, Fin.ext_iff] at *
  omega

theorem isParabolic_of_upper {N : ℕ} (ca cb : Fin N) {M : Matrix (Fin N) (Fin N) ℂ}
    (hM : M.BlockTriangular id) : IsParabolic ca cb M := fun _ _ h _ => hM h

theorem isParabolic_transvection {N : ℕ} (ca cb : Fin N) (t : ℂ) :
    IsParabolic ca cb (1 + Matrix.single cb ca t) := by
  intro a b hba hne
  rw [Matrix.add_apply, Matrix.one_apply_ne hba.ne', Matrix.single_apply_of_ne, add_zero]
  intro h
  exact hne ⟨h.1.symm, h.2.symm⟩

theorem eq_transvection {N : ℕ} {ca cb : Fin N} {Y : Matrix (Fin N) (Fin N) ℂ} (hne : cb ≠ ca)
    (hlt : ca < cb) (hY : IsLowerUni Y) (hP : IsParabolic ca cb Y) :
    Y = 1 + Matrix.single cb ca (Y cb ca) := by
  ext a b
  rw [Matrix.add_apply]
  by_cases e : a = cb ∧ b = ca
  · obtain ⟨rfl, rfl⟩ := e
    rw [Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
  · have hs : Matrix.single cb ca (Y cb ca) a b = 0 :=
      Matrix.single_apply_of_ne _ _ _ _ _ (fun h => e ⟨h.1.symm, h.2.symm⟩)
    rw [hs, add_zero]
    rcases lt_trichotomy a b with h | h | h
    · rw [hY.2 a b h, Matrix.one_apply_ne h.ne]
    · subst h
      rw [hY.1 a, Matrix.one_apply_eq]
    · rw [hP a b h e, Matrix.one_apply_ne h.ne']

theorem mul_transvection_eq : ∀ (N : ℕ) (h B₀ B₁ : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ),
    (cb : ℕ) = ca + 1 → B₀.BlockTriangular id → B₁.BlockTriangular id → B₀.det ≠ 0 → B₁.det ≠ 0 →
    IsLowerUni (h * B₀) → IsLowerUni (h * (1 + Matrix.single cb ca t) * B₁) →
    ∃ y : ℂ, h * (1 + Matrix.single cb ca t) * B₁ = h * B₀ * (1 + Matrix.single cb ca y) := by
  intro N h B₀ B₁ ca cb t hc h0 h1 d0 _ L0 L1
  have hlt : ca < cb := by simp only [Fin.lt_def]; omega
  have hL0 : IsUnit (h * B₀).det := by rw [L0.det]; exact isUnit_one
  have hB0 : IsUnit B₀.det := isUnit_iff_ne_zero.mpr d0
  letI := Matrix.invertibleOfIsUnitDet (h * B₀) hL0
  letI := Matrix.invertibleOfIsUnitDet B₀ hB0
  set E : Matrix (Fin N) (Fin N) ℂ := 1 + Matrix.single cb ca t with hE
  set Y : Matrix (Fin N) (Fin N) ℂ := B₀⁻¹ * (E * B₁) with hYdef
  have hY : h * B₀ * Y = h * E * B₁ := by
    rw [hYdef, Matrix.mul_assoc h B₀, Matrix.mul_nonsing_inv_cancel_left _ _ hB0, Matrix.mul_assoc]
  have low : Y.BlockTriangular OrderDual.toDual := by
    have e1 : (h * B₀).BlockTriangular OrderDual.toDual := fun a b e => L0.2 _ _ e
    have e2 : (h * E * B₁).BlockTriangular OrderDual.toDual := fun a b e => L1.2 _ _ e
    have := (blockTriangular_inv_of_blockTriangular e1).mul e2
    rwa [← hY, Matrix.nonsing_inv_mul_cancel_left _ _ hL0] at this
  have hYl : IsLowerUni Y := by
    refine ⟨fun a => ?_, fun a b e => low e⟩
    have := L1.1 a
    rw [← hY, Matrix.mul_apply, Finset.sum_eq_single a
      (fun c _ hc' => by
        rcases lt_or_gt_of_ne hc' with e | e
        · rw [low e, mul_zero]
        · rw [L0.2 a c e, zero_mul]) (by simp), L0.1, one_mul] at this
    exact this
  have hP : IsParabolic ca cb Y :=
    (isParabolic_of_upper ca cb (blockTriangular_inv_of_blockTriangular h0)).mul hc
      ((isParabolic_transvection ca cb t).mul hc (isParabolic_of_upper ca cb h1))
  exact ⟨Y cb ca, by rw [← hY, ← eq_transvection hlt.ne' hlt hYl hP]⟩

end GlobalTheory.CompanionTheory.Ar.PB.Parab
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LiftSystemComplexConjugationStatement
section
open MvPolynomial Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.Cj GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_system_complex_conjugation : ∀ {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] {A : FinHolAtlas e X} {P : Ideal (MRing ι)} {U : X → Set X} {lift : X → X → (Σ k, ι k) → ℂ}, IsLiftSys A P U lift → ∃ c : X → X, (∀ x, SameOrbit (lift (c x) (c x)) (cj (lift x x))) ∧ Continuous c ∧ ∀ x, c (c x) = x := by
  first | exact @GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | exact GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys | (intros; apply GlobalTheory.CompanionTheory.Ar.PB.Cj.exists_conj_of_isLiftSys <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogBlockMetricOffBoundary
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GlobalTheory.CompanionTheory.Ar.PB.StepW GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine

section Values

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem valAt_inv {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {s : Ω} (h0 : s ≠ 0)
    (hs : RegAt x (mCoordIdeal z) s) (hs' : RegAt x (mCoordIdeal z) s⁻¹) :
    valAt x s⁻¹ z = (valAt x s z)⁻¹ ∧ valAt x s z ≠ 0 := by
  obtain ⟨-, -, -, h1, hm⟩ := ValRing.regAt_valAt_ring K ι Ω x z hz
  have h := (hm s s⁻¹ hs hs').2.2.1
  rw [mul_inv_cancel₀ h0, h1] at h
  have hne : valAt x s z ≠ 0 := left_ne_zero_of_mul_eq_one h.symm
  exact ⟨eq_inv_of_mul_eq_one_right h.symm, hne⟩

theorem coord_ne_zero {z : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal z) : z q ≠ 0 :=
  fun h0 => h (by
    show mConeMap z (X q) = 0
    rw [mConeMap, aeval_X, h0, map_zero, zero_mul])

end Values

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n : ℕ) (BM : BaseMetric M n) (p : Ψ × Fin N) (l : Fin BM.q) (x₀ : BM.Rb.X) (z : (Σ k, ι k) → ℂ), M.blk p = none → x₀ ∈ BM.O l \ bdry BM.s → z ∈ mcPts (mCoordIdeal y) → SameOrbit (basePart M.blk z) (BM.Rb.lift x₀ x₀) → Real.log ((BM.hom p).h z) = blockPot j p.2 (BM.G l p.1 x₀) 1 + Real.log ‖baseMono M (BM.F l) p z * valAt M.x ((BM.F l).υ p)⁻¹ (basePart M.blk z)‖ := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n BM p l x₀ z hp hx hz hso
  have hgood : M.GoodAt (BM.F l) (mCoordIdeal (BM.Rb.lift x₀ x₀)) := BM.good l x₀ hx.1
  have hxb : BM.Rb.lift x₀ x₀ ∈ mcPts (mCoordIdeal M.x) := BM.Rb.mem x₀ x₀ (BM.Rb.mem_U x₀)
  obtain ⟨c, hc, hzc⟩ := id hso

  have hI : mCoordIdeal (basePart M.blk z) = mCoordIdeal (BM.Rb.lift x₀ x₀) := by
    rw [hzc]; exact TorusAct.mCoordIdeal_torus c hc _
  have hzb : basePart M.blk z ∈ mcPts (mCoordIdeal M.x) := by
    rw [hzc]
    exact ((TorusAct.main _ _ _ M.x _ c hc).2 hxb).1
  have hgood' : M.GoodAt (BM.F l) (mCoordIdeal (basePart M.blk z)) := by rw [hI]; exact hgood
  have hne : ∀ k : NonPluckerBlocks M.blk, basePart M.blk z ⟨k, (BM.F l).c k⟩ ≠ 0 := fun k => coord_ne_zero (hgood'.1 k)

  let t : K → ℂ := fun k => if h : ∀ p', M.blk p' ≠ some k then (basePart M.blk z ⟨⟨k, h⟩, (BM.F l).c ⟨k, h⟩⟩)⁻¹ else 1
  have htb : ∀ k : NonPluckerBlocks M.blk, t k.1 = (basePart M.blk z ⟨k, (BM.F l).c k⟩)⁻¹ := fun k => dif_pos k.2
  have ht1 : ∀ k, ¬ (∀ p', M.blk p' ≠ some k) → t k = 1 := fun k h => dif_neg h
  have ht : ∀ k, t k ≠ 0 := fun k => by
    by_cases h : ∀ p', M.blk p' ≠ some k
    · rw [htb ⟨k, h⟩]; exact inv_ne_zero (hne _)
    · rw [ht1 k h]; exact one_ne_zero
  let z₁ : (Σ k, ι k) → ℂ := fun q => t q.1 * z q
  have hz₁ : z₁ ∈ mcPts (mCoordIdeal y) := ((TorusAct.main _ _ _ y z t ht).2 hz).1
  have hb₁ : basePart M.blk z₁ = fun q : Σ k, baseIdx ι M.blk k => t q.1.1 * basePart M.blk z q := rfl
  have hval : valAt M.x ((BM.F l).υ p) (basePart M.blk z₁) = valAt M.x ((BM.F l).υ p) (basePart M.blk z) := by
    rw [hb₁]
    exact ((TorusAct.main _ _ _ M.x _ (fun k : NonPluckerBlocks M.blk => t k.1) fun k => ht _).2 hzb).2 _
  have hso₁ : SameOrbit (basePart M.blk z₁) (BM.Rb.lift x₀ x₀) :=
    ⟨fun k => t k.1 * c k, fun k => mul_ne_zero (ht _) (hc k), by
      rw [hb₁, hzc]; funext q; exact (mul_assoc _ _ _).symm⟩
  have hnorm : ∀ k, basePart M.blk z₁ ⟨k, (BM.F l).c k⟩ = 1 := fun k => by
    rw [hb₁]
    show t k.1 * _ = 1
    rw [htb k]
    exact inv_mul_cancel₀ (hne k)
  have hind := (BM.induced l x₀ hx p z₁ hz₁ hso₁ hnorm 1 isBlockDiag_one (by simp)).2 hp
  rw [hval] at hind

  have hscale : (BM.hom p).h z₁ = (∏ k, ‖t k‖ ^ M.dy p k) * (BM.hom p).h z := by
    have := (BM.hom p).smul t z ht
    rw [BM.hom_deg] at this
    exact this
  have hprod : (∏ k, ‖t k‖ ^ M.dy p k) = ‖baseMono M (BM.F l) p z‖⁻¹ := by
    have e := Fintype.prod_subtype_mul_prod_subtype (fun k : K => ∀ p', M.blk p' ≠ some k)
      (fun k : K => (‖t k‖ ^ M.dy p k : ℝ))
    rw [← e, Fintype.prod_eq_one (f := fun k : {k // ¬ ∀ p', M.blk p' ≠ some k} => ‖t k.1‖ ^ M.dy p k.1)
      (fun k => by rw [ht1 _ k.2]; simp), mul_one, baseMono, norm_prod, ← Finset.prod_inv_distrib]
    refine Finset.prod_congr (by ext; simp) fun k _ => ?_
    show ‖t k.1‖ ^ M.dy p k.1 = (‖basePart M.blk z ⟨k, (BM.F l).c k⟩ ^ M.dy p k.1‖)⁻¹
    rw [htb k, norm_inv, norm_zpow, _root_.inv_zpow]

  obtain ⟨hu0, hu1, hu2⟩ := hgood'.2.2 p hp
  obtain ⟨hinv, hv0⟩ := valAt_inv hzb hu0 hu1 hu2
  have hmono : baseMono M (BM.F l) p z ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hne k)
  have hpos : 0 < (BM.hom p).h z := (BM.hom p).pos z hz.1
  rw [hscale, hprod, Real.log_mul (inv_ne_zero (norm_ne_zero_iff.2 hmono)) hpos.ne', Real.log_inv] at hind
  rw [hinv, norm_mul, norm_inv, Real.log_mul (norm_ne_zero_iff.2 hmono) (inv_ne_zero (norm_ne_zero_iff.2 hv0)),
    Real.log_inv]
  linarith

end GlobalTheory.CompanionTheory.Ar.PB.StepW.BaseLine
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormNonvanishingAnalyticHarmonic
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem log_norm_eventually_eq_re_analyticAt :
    ∀ (e : ℕ) (f : (Fin e → ℂ) → ℂ) (z : Fin e → ℂ), AnalyticAt ℂ f z → f z ≠ 0 →
      ∃ Hh : (Fin e → ℂ) → ℂ, AnalyticAt ℂ Hh z ∧ ∀ᶠ z' in 𝓝 z, Real.log ‖f z'‖ = (Hh z').re := by
  intro e f z hf hz
  refine ⟨fun z' => Complex.log (f z' * (f z)⁻¹) + Complex.log (f z), ?_, ?_⟩
  · have h1 : AnalyticAt ℂ (fun z' => f z' * (f z)⁻¹) z := hf.mul analyticAt_const
    have h2 : AnalyticAt ℂ Complex.log (f z * (f z)⁻¹) := by
      apply analyticAt_clog
      rw [mul_inv_cancel₀ hz]
      exact Complex.one_mem_slitPlane
    exact (AnalyticAt.comp (f := fun z' => f z' * (f z)⁻¹) (x := z) h2 h1).add analyticAt_const
  · filter_upwards [hf.continuousAt.eventually_ne hz] with z' hz'
    simp only [Complex.add_re, Complex.log_re, norm_mul, norm_inv]
    rw [Real.log_mul (norm_ne_zero_iff.2 hz') (inv_ne_zero (norm_ne_zero_iff.2 hz)), Real.log_inv]
    ring

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.LogNormProductFormula
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib

theorem log_norm_mul_prod_ite_zpow (N : ℕ) (P : Fin N → Prop) (t : ℂ) (v f : Fin N → ℂ)
    (e : Fin N → ℤ) (ht : t ≠ 0) (h : ∀ i, ¬ P i → v i ≠ 0 ∧ f i ≠ 0) :
    Real.log ‖t * ∏ i : Fin N, (if P i then 1 else v i * f i) ^ e i‖ =
      Real.log ‖t‖ + ∑ i : Fin N, (e i : ℝ) *
        (if P i then 0 else Real.log ‖v i‖ + Real.log ‖f i‖) := by
  have hne : ∀ i, (if P i then (1 : ℂ) else v i * f i) ≠ 0 := by
    intro i
    split_ifs with hp
    · exact one_ne_zero
    · exact mul_ne_zero (h i hp).1 (h i hp).2
  have hfac : ∀ i ∈ (Finset.univ : Finset (Fin N)),
      ‖(if P i then (1 : ℂ) else v i * f i) ^ e i‖ ≠ 0 :=
    fun i _ => norm_ne_zero_iff.mpr (zpow_ne_zero _ (hne i))
  have hprod : ∏ i : Fin N, ‖(if P i then (1 : ℂ) else v i * f i) ^ e i‖ ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr hfac
  rw [norm_mul, norm_prod, Real.log_mul (norm_ne_zero_iff.mpr ht) hprod, Real.log_prod hfac]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [norm_zpow, Real.log_zpow]
  split_ifs with hp
  · simp
  · rw [norm_mul, Real.log_mul (norm_ne_zero_iff.mpr (h i hp).1)
      (norm_ne_zero_iff.mpr (h i hp).2)]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.Fib
end

