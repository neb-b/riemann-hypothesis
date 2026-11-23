module

public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
public import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.InPCommutatorOfInK
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Bundle0001
public import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingBump
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral

@[expose] public section

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.AdmissibleOfFiniteRank
section
open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

variable {n : ℕ} {ε : Fin n → Bool}

theorem exists_elt {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : ∃ g : UJ ε, toM g = m := by
  have : m ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hm
  exact this

theorem conjTranspose_mem {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : mᴴ ∈ UJset ε := by
  have h1 := mul_eq_one_comm.1 (coeMatrix_left_inv ε m hm)
  show mᴴᴴ * Jm ε * mᴴ = Jm ε
  rw [Matrix.conjTranspose_conjTranspose]
  calc m * Jm ε * mᴴ = m * (Jm ε * mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

theorem Kset_sub {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ Kset ε) : m ∈ UJset ε := by
  have h1 : mᴴ * m = 1 := Matrix.mem_unitaryGroup_iff'.1 hm.1
  show mᴴ * Jm ε * m = Jm ε
  rw [Matrix.mul_assoc, ← hm.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem continuous_toM : Continuous (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := continuous_coeMatrix ε

def homUJ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (toM g)
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdU (ε : Fin n → Bool) {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    UJ ε →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * toM g * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (toM a * toM b) * U = _
    calc Uᴴ * (toM a * toM b) * U = Uᴴ * toM a * (U * Uᴴ) * toM b * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

theorem admissible_of_finite_rank (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : Iwa ε) : AdmUJ ε := by
  intro H _ _ _ σ hσ hirr S _ hS v hv
  obtain ⟨U, hU, hiwa⟩ := h5
  let μ : Measure (KG ε) := (Measure.haar : Measure (KG ε)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (KG ε) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homUJ hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homUJ hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_toM fun g => g.2
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := h4 (KG ε) μ H ((homUJ hσ).comp (KG ε).subtype) (fun k u => hiso k u)
    (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ k.2 u hu) v hv
  choose st hst using fun g : UJ ε => exists_elt (conjTranspose_mem (m := toM g) g.2)
  let Tr : Set (UJ ε) := {s | (stdU ε hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdU ε hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * toM (st g) * U = (Uᴴ * toM g * U)ᴴ
    rw [hst]
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdU ε hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : UJ ε, U * stdU ε hU g * Uᴴ = toM g := fun g => by
      show U * (Uᴴ * toM g * U) * Uᴴ = _
      calc U * (Uᴴ * toM g * U) * Uᴴ = (U * Uᴴ) * toM g * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact injective_coeMatrix ε ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : UJ ε, ∃ k ∈ KG ε, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa (toM g) g.2
    obtain ⟨k, rfl⟩ := exists_elt (Kset_sub hk)
    obtain ⟨s, rfl⟩ := exists_elt hs
    exact ⟨k, hk, s, ht, injective_coeMatrix ε hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → UJ ε, stdPoly E (fun i => homUJ hσ (g i)) = 0 := fun g =>
    h3 (UJ ε) (KG ε) μ st Tr (Fin n) (stdU ε hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => h2 (UJ ε) (KG ε) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homUJ hσ) hc E hE
  obtain ⟨hfd, hrk⟩ := h1 (UJ ε) H (homUJ hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu => by
    obtain ⟨g, rfl⟩ := exists_elt hg
    exact hS' g u hu) E _ hPI
  refine ⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ (toMK k) (T u) = T (e k • σ (toMK k) u)
    rw [map_smul, hT _ k.2]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

theorem smooth_of_adm (hA : AdmUJ ε) (hG : GardingFin) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : SmoothOnH (Jm ε) fun g => σ g v := by
  obtain ⟨S, _, hvS, hS⟩ := hv
  obtain ⟨Y, _, -, hvY, hY⟩ := hA H σ hσ hirr S hS v hvS
  exact hG n ε H σ hσ Y hY v hvY

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
theorem smoothOnH_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A B P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) (hAB : Pᴴ * A * P = B) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : SmoothOnH A fun g => f (P⁻¹ * g * P)) : SmoothOnH B f := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hmem : ∀ g, inUH B g → inUH A (P * g * P⁻¹) := by
    intro g hg
    unfold inUH at hg ⊢
    have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * A * (P * g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * A * P) * g) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * A * (P * P⁻¹) := by rw [hAB, hg, ← hAB]; simp only [Matrix.mul_assoc]
      _ = A := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => P * g * P⁻¹
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hL : ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ := (LinearMap.toContinuousLinearMap L).contDiff
  intro g₀ hg₀
  obtain ⟨V, F, hV, hgV, hF, hfF⟩ := h _ (hmem g₀ hg₀)
  refine ⟨(fun g => P * g * P⁻¹) ⁻¹' V, fun g => F (P * g * P⁻¹), hV.preimage hL.continuous, hgV,
    hF.comp hL.contDiffOn fun g hg => hg, fun g hg hgB => ?_⟩
  refine Eq.trans ?_ (hfF _ hg (hmem g hgB))
  show f g = f (P⁻¹ * (P * g * P⁻¹) * P)
  congr 1
  calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

theorem kFinSmooth_of (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : IwaHpk) (h6 : GardingFin) :
    PI.KFinSmooth := by
  intro k r ε lam H _ _ _ σ _ hσ v hv
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨S, hSf, hvS, hS⟩ := hv
  have hPP : Pᴴ * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have hPP' : P * Pᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hPP
  refine smoothOnH_conj hP.1.1 hP.1.2 (smooth_of_adm (admissible_of_finite_rank h1 h2 h3 h4 (h5 k r ε P hP)) h6
    (σ := fun g => σ (P⁻¹ * g * P)) hDS.2.2.1 hDS.2.2.2.1 ⟨S, hSf, hvS, fun g hg x hx => hS _ ⟨?_, ?_⟩ x hx⟩)
  · have hg' : gᴴ * Jm ε * g = Jm ε := Kset_sub hg
    show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
    rw [hinv, ← hP.1.2]
    calc (Pᴴ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (Pᴴ * g * P) = Pᴴ * (gᴴ * (P * Pᴴ) * Jm ε * (P * Pᴴ) * g) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hPP', Matrix.mul_one, Matrix.mul_one, hg']
  · rw [hinv]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hP.2) hg.1) hP.2

end CompanionTheory.D.gk.admitted
end
end

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.ExistsAvg
section
open MeasureTheory
open scoped InnerProductSpace

noncomputable section

namespace CompanionTheory.D.gk.admitted

section

variable {K : Type} [Group K] [TopologicalSpace K] [CompactSpace K] [MeasurableSpace K] [BorelSpace K]
  {μ : Measure K} [IsFiniteMeasure μ]
  {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {σ : K →* (H →L[ℂ] H)}

theorem integrable_cont {F : Type} [NormedAddCommGroup F] {f : K → F} (hf : Continuous f) : Integrable f μ :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem exists_avg (hiso : ∀ g v, ‖σ g v‖ = ‖v‖) (hc : ∀ v, Continuous fun x => σ x v) {e : K → ℂ}
    (he : Continuous e) : ∃ E : H →L[ℂ] H, ∀ u, E u = ∫ k, e k • σ k u ∂μ := by
  let L : H →ₗ[ℂ] H :=
    { toFun := fun u => ∫ k, e k • σ k u ∂μ
      map_add' := fun u w => by
        simp only [map_add (f := _), smul_add]
        exact integral_add (integrable_cont (he.smul (hc u))) (integrable_cont (he.smul (hc w)))
      map_smul' := fun c u => by
        simp only [map_smul, RingHom.id_apply, smul_comm _ c]
        exact integral_smul _ _ }
  refine ⟨L.mkContinuous (∫ k, ‖e k‖ ∂μ) fun u => ?_, fun u => rfl⟩
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_smul, hiso]
  exact integral_mul_const _ _

end

theorem exists_averaging_operator : ExistsAvg := by
  intro K _ _ _ _ _ _ _ _ μ _ _ H _ _ _ σ hiso hc S _ hS v hv
  have hcoef : ∀ a b : H, Continuous fun x => ⟪σ x a, b⟫_ℂ := fun a b => (hc a).inner continuous_const
  have hint : ∀ b : H, Integrable (fun x => ⟪σ x v, b⟫_ℂ • σ x v) μ := fun b =>
    integrable_cont ((hcoef v b).smul (hc v))
  have hScl : CompleteSpace S := FiniteDimensional.complete ℂ S

  let L : H →ₗ[ℂ] H :=
    { toFun := fun b => ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ
      map_add' := fun a b => by
        simp only [inner_add_right, add_smul]
        exact integral_add (hint a) (hint b)
      map_smul' := fun c b => by
        simp only [inner_smul_right, RingHom.id_apply, mul_smul]
        exact integral_smul _ _ }
  have hinner : ∀ w b, ⟪w, L b⟫_ℂ = ∫ x, ⟪σ x v, b⟫_ℂ * ⟪w, σ x v⟫_ℂ ∂μ := by
    intro w b
    change ⟪w, ∫ x, ⟪σ x v, b⟫_ℂ • σ x v ∂μ⟫_ℂ = _
    rw [← integral_inner (hint b)]
    simp only [inner_smul_right]
  have hLS : ∀ b, L b ∈ S := by
    intro b
    rw [← Submodule.orthogonal_orthogonal S, Submodule.mem_orthogonal]
    intro w hw
    rw [hinner]
    have : ∀ x, ⟪w, σ x v⟫_ℂ = 0 := fun x => Submodule.inner_left_of_mem_orthogonal (hS x v hv) hw
    simp [this]
  have hzero : ∀ w, ⟪w, L w⟫_ℂ = 0 → ⟪w, v⟫_ℂ = 0 := by
    intro w hw
    rw [hinner] at hw
    have e1 : ∀ x, ⟪σ x v, w⟫_ℂ * ⟪w, σ x v⟫_ℂ = ((‖⟪σ x v, w⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
      intro x
      rw [← inner_conj_symm w, Complex.mul_conj, Complex.normSq_eq_norm_sq]
    simp only [e1] at hw
    rw [integral_complex_ofReal, Complex.ofReal_eq_zero] at hw
    have hcont : Continuous fun x => ‖⟪σ x v, w⟫_ℂ‖ ^ 2 := (hcoef v w).norm.pow 2
    have h1 := (integral_eq_zero_iff_of_nonneg (fun x => sq_nonneg _) (integrable_cont hcont)).1 hw
    have h2 : ‖⟪σ 1 v, w⟫_ℂ‖ ^ 2 = 0 := congrFun ((hcont.ae_eq_iff_eq μ continuous_const).1 h1) 1
    simp only [map_one, ContinuousLinearMap.one_apply, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
      pow_eq_zero_iff, norm_eq_zero] at h2
    exact inner_eq_zero_symm.1 h2
  set R : Submodule ℂ H := S.map L with hR
  have hRc : CompleteSpace R := FiniteDimensional.complete ℂ R
  have hvR : v ∈ R := by
    set w := v - R.starProjection v with hw
    have hwo : w ∈ Rᗮ := R.sub_starProjection_mem_orthogonal v
    have hp : R.starProjection v ∈ R := R.starProjection_apply_mem v
    have hRS : R ≤ S := by rintro _ ⟨b, -, rfl⟩; exact hLS b
    have hwS : w ∈ S := S.sub_mem hv (hRS hp)
    have h1 : ⟪w, v⟫_ℂ = 0 := hzero w (Submodule.inner_left_of_mem_orthogonal (K := R) (Submodule.mem_map_of_mem hwS) hwo)
    have h2 : ⟪w, R.starProjection v⟫_ℂ = 0 := Submodule.inner_left_of_mem_orthogonal hp hwo
    have h3 : ⟪w, w⟫_ℂ = 0 := by
      conv_lhs => rw [hw, inner_sub_right, ← hw]
      rw [h1, h2, sub_zero]
    rw [inner_self_eq_zero, hw, sub_eq_zero] at h3
    rw [h3]; exact hp
  obtain ⟨b, -, hb⟩ := hvR
  obtain ⟨E, hE⟩ := exists_avg (μ := μ) hiso hc (hcoef v b)
  refine ⟨fun x => ⟪σ x v, b⟫_ℂ, E, hcoef v b, ?_, hE, by rw [hE]; exact hb⟩
  let B := Module.finBasis ℂ S
  refine ⟨fun i x => ⟪σ x (B i), b⟫_ℂ, fun i => hcoef _ b, fun k => ?_⟩
  refine ⟨fun i => (starRingEnd ℂ) (B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i), fun x => ?_⟩
  have e1 : σ k⁻¹ v = ∑ i, B.repr ⟨σ k⁻¹ v, hS _ v hv⟩ i • (B i : H) := by
    have := congrArg Subtype.val (B.sum_repr ⟨σ k⁻¹ v, hS _ v hv⟩)
    rw [Submodule.coe_sum] at this
    exact this.symm
  show ⟪σ (x * k⁻¹) v, b⟫_ℂ = _
  rw [map_mul, ContinuousLinearMap.mul_apply]
  conv_lhs => rw [e1]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, sum_inner, inner_smul_left]

end CompanionTheory.D.gk.admitted
end
end

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.Garding
section
open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Gard

theorem contDiff_integral_comp {P Q E α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (q : α → Q)
    (hq : Continuous q)
    (hsupp : ∀ y₀ : P, ∃ U ∈ 𝓝 y₀, ∃ C : Set α, IsCompact C ∧ ∀ y ∈ U, ∀ a ∉ C, Φ (y, q a) = 0) :
    ContDiff ℝ ∞ fun y => ∫ a, Φ (y, q a) ∂μ := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := μ) (fun y a => Φ (y, q a))
    (fun a => hΦ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_) hsupp
  have h : Continuous fun p : P × α => (p.1, q p.2) := continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iter_partial Φ hΦ k).comp h

variable {n : ℕ} {ε : Fin n → Bool}

theorem toM_mul (x y : UJ ε) : toM (x * y) = toM x * toM y := rfl

theorem toM_one : toM (1 : UJ ε) = 1 := rfl

theorem emb_toM : IsClosedEmbedding (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := (isClosedEmbeddingMatrix n ε).1

theorem toM_mem (x : UJ ε) : toM x ∈ UJset ε := x.2

theorem exists_toM {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ∃ x : UJ ε, toM x = g := by
  have : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact this

theorem inUJ_of_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : inUJ ε k := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  unfold inUJ
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

theorem toM_inv_of_unitary {k : UJ ε} (hk : toM k ∈ Matrix.unitaryGroup (Fin n) ℂ) : toM k⁻¹ = (toM k)ᴴ :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 hk)

theorem contDiff_Phi {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : Matrix (Fin n) (Fin n) ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) • p.2.2 := by
  have h1 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => (p.2.1, p.1) :=
    contDiff_snd.fst.prodMk contDiff_fst
  have h2 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => p.2.1 * p.1 := by
    have := contDiff_mul.comp h1
    simpa only [Function.comp_def] using this
  have h3 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) :=
    hf.comp h2
  exact h3.smul contDiff_snd.snd

theorem supp_local {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) (g₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ 𝓝 g₀, ∃ C : Set (UJ ε), IsCompact C ∧ ∀ g ∈ U, ∀ x ∉ C, f (toM x⁻¹ * g) = 0 := by
  refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
    emb_toM.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd), fun g hg x hx => ?_⟩
  by_contra h
  have hB := hfS _ h
  refine hx ⟨(g, toM x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have hu : IsUnit (toM x⁻¹ * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
  have e : g = toM x * (toM x⁻¹ * g) := by
    rw [← Matrix.mul_assoc, ← toM_mul, mul_inv_cancel, toM_one, Matrix.one_mul]
  show g * (toM x⁻¹ * g)⁻¹ = toM x
  calc g * (toM x⁻¹ * g)⁻¹ = toM x * (toM x⁻¹ * g) * (toM x⁻¹ * g)⁻¹ := by rw [← e]
    _ = toM x := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

theorem contDiff_avg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (v : UJ ε → H) (hv : Continuous v) {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => ∫ x : UJ ε, f (toM x⁻¹ * g) • v x ∂(muG ε) := by
  have hq : Continuous fun x : UJ ε => (toM x⁻¹, v x) := (emb_toM.continuous.comp continuous_inv).prodMk hv
  have key := contDiff_integral_comp (muG ε) _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := supp_local (ε := ε) hS hd hfS g₀
    refine ⟨U, hU, C, hC, fun g hg x hx => ?_⟩
    simp only [h g hg x hx, zero_smul]
  simpa only using key

end Gard


open Gard in
theorem garding_finite_smooth_vectors : GardingFin := by
  open scoped Pointwise in
  intro n ε H _ _ _ σ hσ Y _ hY v hv
  obtain ⟨⟨h1, hm⟩, hiso, hcont⟩ := hσ
  let ρ : UJ ε → H →L[ℂ] H := fun x => σ (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hcont u).comp_continuous emb_toM.continuous toM_mem
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    simp only [ρ, toM_mul, hm _ (toM_mem x) _ (toM_mem y), ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, one_apply_eq_self]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : UJ ε) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : UJ ε → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring (muG ε) ρ hρ (fun x u => hiso _ (toM_mem x) u) hw hc
  have hTK : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (inUJ_of_mem_Kset hk)
    rw [hT, hT]
    refine T_comm (muG ε) ρ hρ hmul hw hc h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.1, hfk _ hk.1]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt (muG ε) ρ hρ hw hc h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  intro g₀ _
  refine ⟨univ, fun g => ∫ x : UJ ε, f (toM x⁻¹ * g) • ρ x u ∂(muG ε), isOpen_univ, mem_univ _,
    (contDiff_avg (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS).contDiffOn, fun g _ hg => ?_⟩
  obtain ⟨g', rfl⟩ := exists_toM (ε := ε) hg
  show ρ g' (T u) = _
  rw [hT, apply_alt (muG ε) ρ hρ hmul hw hc]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]

end CompanionTheory.D.gk.admitted
end
end

-- bundled from CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.SmallPI
section
noncomputable section

namespace CompanionTheory.D.gk.admitted

theorem std_eq_zero {A : Type} [Ring A] [Algebra ℂ A] [Module.Finite ℂ A] {M : ℕ} (hM : Module.finrank ℂ A < M)
    (b : Fin M → A) :
    ∑ π : Equiv.Perm (Fin M), ((Equiv.Perm.sign π : ℤ) : A) * (List.ofFn fun i => b (π i)).prod = 0 := by
  have hdep : ¬ LinearIndependent ℂ b := fun h => by
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin] at this
    omega
  have h := (MultilinearMap.alternatization (MultilinearMap.mkPiAlgebraFin ℂ M A)).map_linearDependent b hdep
  rw [MultilinearMap.alternatization_apply] at h
  rw [← h]
  refine Finset.sum_congr rfl fun π _ => ?_
  rw [MultilinearMap.domDomCongr_apply, MultilinearMap.mkPiAlgebraFin_apply, Units.smul_def, zsmul_eq_mul]

theorem small_irreducible_representation : SmallPI := by
  intro V _ _ W Y _ hYW E hE M hM a ha w hw
  let b : Fin M → Module.End ℂ Y := fun i =>
    (E * a i).restrict (p := Y) (q := Y) fun y hy => hE _ (ha i y (hYW hy))
  have hb : ∀ l : List (Fin M), word E (l.map a) w = (((l.map b).prod ⟨E w, hE w hw⟩ : Y) : V) := by
    intro l
    induction l with
    | nil => rfl
    | cons i l ih =>
      rw [List.map_cons, word_cons, Module.End.mul_apply, ih, List.map_cons, List.prod_cons, Module.End.mul_apply]
      rfl
  have hdim : Module.finrank ℂ (Module.End ℂ Y) < M := by
    rw [Module.finrank_linearMap, ← sq]; exact hM
  have h0 := congrArg (fun T : Module.End ℂ Y => ((T ⟨E w, hE w hw⟩ : Y) : V)) (std_eq_zero hdim b)
  simp only [LinearMap.sum_apply, Submodule.coe_sum, LinearMap.zero_apply, Submodule.coe_zero] at h0
  rw [← h0, stdPoly, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun π _ => ?_
  have e1 : (List.ofFn fun i => a (π i)) = (List.ofFn π).map a := by rw [List.map_ofFn]; rfl
  have e2 : (List.ofFn fun i => b (π i)) = (List.ofFn π).map b := by rw [List.map_ofFn]; rfl
  rw [e1, e2, Module.End.mul_apply, Module.End.mul_apply, hb, Module.End.intCast_apply, Module.End.intCast_apply,
    Submodule.coe_smul_of_tower]

end CompanionTheory.D.gk.admitted
end
end

