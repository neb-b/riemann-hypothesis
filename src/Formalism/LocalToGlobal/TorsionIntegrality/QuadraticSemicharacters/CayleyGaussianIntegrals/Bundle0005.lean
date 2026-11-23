module

public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0003
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0004
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0002
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.Bundle0001
public import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.CayleyPhaseQuadratic

@[expose] public section

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.DiagonalIntegral
section
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory

namespace Formalism.L2.Th1.H

theorem continuous_altE {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (H : Sesq V)
    (hH : IsHerm H) (v : V) : Continuous fun z => altE H v z := by
  have hlin : Continuous fun z => H z v := by
    let f : V →ₗ[ℂ] ℂ :=
      { toFun := fun z => H z v
        map_add' := fun a b => by simp
        map_smul' := fun c a => by simp }
    exact f.continuous_of_finiteDimensional
  have hfun : (fun z => altE H v z) = fun z => -(H z v).im := by
    funext z
    unfold altE
    rw [hH z v, Complex.conj_im]
  rw [hfun]
  exact (Complex.continuous_im.comp hlin).neg

def diagCoef {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (y x : V) : ℂ :=
  α y * α x * Complex.exp (-(Real.pi : ℂ) * Complex.I * (altE H y x : ℂ)) *
    Complex.exp (-(Real.pi : ℂ) * H (y + x) (y + x) / 2)

theorem diag_expansion {V : Type} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (hH : IsHerm H) (α : V → ℂ)
    (Λ : AddSubgroup V) (y z : V) :
    α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ)
      = ∑' x : Λ, diagCoef H α y (x : V) *
          Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) := by
  rw [wt_eq_cexp H hH z]
  simp only [opU, kerP, kerK]
  rw [← tsum_mul_right, ← tsum_mul_left, ← tsum_mul_right]
  refine tsum_congr (fun x => ?_)
  unfold diagCoef
  have hP : (Real.pi : ℂ) * H (z + y + (x : V)) z
      + (-(Real.pi : ℂ) * H (z + y) (x : V) - Real.pi * H (x : V) (x : V) / 2)
      + (-(Real.pi : ℂ) * H z y - Real.pi * H y y / 2)
      + (-(Real.pi : ℂ) * H z z)
      = -(Real.pi : ℂ) * Complex.I * (altE H y (x : V) : ℂ)
        + (-(Real.pi : ℂ) * H (y + (x : V)) (y + (x : V)) / 2)
        + 2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ) := by
    simp only [map_add (f := _), LinearMap.add_apply, altE]
    rw [hH y z, hH (x : V) z, hH y (x : V)]
    apply Complex.ext <;> simp <;> ring
  have e1 := congrArg Complex.exp hP
  simp only [Complex.exp_add] at e1
  linear_combination (α y * α (x : V)) * e1

theorem norm_char (t : ℝ) : ‖Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (t : ℂ))‖ = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * (t : ℂ) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

theorem norm_diagCoef {V : Type*} [AddCommGroup V] [Module ℂ V] (H : Sesq V) (α : V → ℂ) (y x : V)
    (hy : α y = 1 ∨ α y = -1) (hx : α x = 1 ∨ α x = -1) :
    ‖diagCoef H α y x‖ = Real.exp (-(Real.pi / 2) * (H (y + x) (y + x)).re) := by
  have hn : ∀ a : ℂ, (a = 1 ∨ a = -1) → ‖a‖ = 1 := by
    rintro a (rfl | rfl) <;> simp
  unfold diagCoef
  rw [norm_mul, norm_mul, norm_mul, hn _ hy, hn _ hx, Complex.norm_exp, Complex.norm_exp]
  have h1 : (-(Real.pi : ℂ) * Complex.I * (altE H y x : ℂ)).re = 0 := by
    simp
  have h2 : (-(Real.pi : ℂ) * H (y + x) (y + x) / 2).re = -(Real.pi / 2) * (H (y + x) (y + x)).re := by
    simp
    ring
  rw [h1, h2]
  simp

theorem diagonalIntegral : DiagIntegral := by
  classical
  intro V _ _ _ _ _ μ _ H Λ Λ₂ α hH hPos hL hS hS₂ hC hC₂ D' hD' hB y hy
  haveI : DiscreteTopology Λ := hL.1
  haveI : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  set F : Λ → V → ℂ := fun x z => diagCoef H α y (x : V) *
    Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H (y + (x : V)) z : ℂ)) with hF
  have hexp : ∀ z, α y * opU H y (fun v => kerP H α Λ v z) z * (wt H z : ℂ) = ∑' x : Λ, F x z :=
    fun z => diag_expansion H hH α Λ y z
  simp only [hexp]
  have hαy : α y = 1 ∨ α y = -1 := hC₂.1 y hy
  obtain ⟨c, C, hc, hC', hcC⟩ := formNormEquiv V H hH hPos
  have hnorm : ∀ (x : Λ) (z : V), ‖F x z‖ = Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re) := by
    intro x z
    simp only [hF]
    rw [norm_mul, norm_char, mul_one, norm_diagCoef H α y x hαy (hC.1 x x.2)]
  set g : Λ → ℝ := fun x => Real.exp (-(Real.pi / 2) * (H (y + (x : V)) (y + (x : V))).re) with hg_def
  have hg : Summable g := by
    obtain ⟨u, hu, hub⟩ := latticeGaussSummable V Λ hL (Real.pi / 2 * c) ‖y‖ (by positivity)
    refine Summable.of_nonneg_of_le (fun x => (Real.exp_pos _).le) (fun x => ?_) hu
    have h1 := hub x (-y) (by simp)
    refine le_trans ?_ h1
    apply Real.exp_le_exp.mpr
    have h2 := (hcC (y + (x : V))).1
    have h3 : ‖(x : V) - -y‖ = ‖y + (x : V)‖ := by
      rw [sub_neg_eq_add, add_comm]
    rw [h3]
    nlinarith [Real.pi_pos]
  have hfin : μ D' < ⊤ := hB.measure_lt_top
  haveI : IsFiniteMeasure (μ.restrict D') := MeasureTheory.isFiniteMeasure_restrict.mpr hfin.ne
  have hcont : ∀ x : Λ, Continuous (F x) := by
    intro x
    simp only [hF]
    exact continuous_const.mul (Complex.continuous_exp.comp (continuous_const.mul
      (Complex.continuous_ofReal.comp (continuous_altE H hH _))))
  have hint : ∀ x : Λ, Integrable (F x) (μ.restrict D') := by
    intro x
    exact (integrable_const (g x)).mono' (hcont x).aestronglyMeasurable
      (Filter.Eventually.of_forall fun z => (hnorm x z).le)
  have hsum : Summable fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D') := by
    have he : (fun x => ∫ z, ‖F x z‖ ∂(μ.restrict D')) = fun x => (μ D').toReal * g x := by
      funext x
      simp only [hnorm x]
      simp [hg_def, Measure.real]
    rw [he]
    exact hg.mul_left _
  rw [← integral_tsum_of_summable_integral_norm hint hsum]
  have hd : diagCoef H α y (-y) = 1 := by
    have hneg : α (-y) = α y := (semicharacterBasic V H hH Λ₂ α hC₂).2.1 y hy
    have him : altE H y (-y) = 0 := by
      unfold altE
      rw [map_neg, Complex.neg_im, neg_eq_zero]
      have h := congrArg Complex.im (hH y y)
      rw [Complex.conj_im] at h
      linarith
    unfold diagCoef
    rw [hneg, him, add_neg_cancel]
    rcases hαy with h | h <;> simp [h]
  have hterm : ∀ x : Λ, ∫ z in D', F x z ∂μ = if (x : V) = -y then ((μ D').toReal : ℂ) else 0 := by
    intro x
    simp only [hF]
    rw [integral_const_mul]
    split_ifs with hx
    · rw [hx, add_neg_cancel, hd, one_mul]
      simp [altE, Measure.real]
    · have hne : y + (x : V) ≠ 0 := fun h => hx (eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact h))
      have hy' : y ∈ dualLat H Λ₂ := by
        rw [hS₂]
        exact hy
      have hx' : (x : V) ∈ dualLat H Λ := by
        rw [hS]
        exact x.2
      have hmem : y + (x : V) ∈ dualLat H (Λ ⊓ Λ₂) := by
        refine add_mem ?_ ?_
        · exact fun w hw => hy' w (AddSubgroup.mem_inf.mp hw).2
        · exact fun w hw => hx' w (AddSubgroup.mem_inf.mp hw).1
      rw [characterIntegral V μ H hH hPos (Λ ⊓ Λ₂) D' hD' _ hmem hne, mul_zero]
  simp only [hterm]
  split_ifs with hyΛ
  · have hiff : ∀ x : Λ, ((x : V) = -y) ↔ x = ⟨-y, neg_mem hyΛ⟩ := fun x => by
      simp [Subtype.ext_iff]
    simp [hiff]
  · have hno : ∀ x : Λ, (x : V) ≠ -y := fun x h => hyΛ (by
      have hx2 := x.2
      rw [h] at hx2
      simpa using hx2)
    simp [hno]

theorem KerPNonzero_of (hD : DiagIntegral) : KerPNonzero := by
  intro V _ _ _ H Λ α hH hPos hL hS hC
  by_contra hne
  push_neg at hne
  letI : MeasurableSpace V := borel V
  haveI : BorelSpace V := ⟨rfl⟩
  obtain ⟨D, hD1, hD2, hD3, -⟩ :=
    fundamentalDomainExists V MeasureTheory.Measure.addHaar (Λ ⊓ Λ) (by rw [inf_idem]; exact hL)
  have hint := hD V MeasureTheory.Measure.addHaar H Λ Λ α hH hPos hL hS hS hC hC D hD1 hD2 0 (zero_mem _)
  simp [opU, hne] at hint
  have h0 : (MeasureTheory.Measure.addHaar D).toReal = 0 := by
    exact_mod_cast hint.symm
  linarith

end Formalism.L2.Th1.H
end
end

-- bundled from Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.CayleyGaussianIntegrals.UnfoldingIntegral
section
noncomputable section
open scoped BigOperators ComplexConjugate
open MeasureTheory
open scoped Pointwise

namespace Formalism.L2.Th1.H

theorem hasSum_unfold {V E : Type*} [NormedAddCommGroup V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [NormedSpace ℝ E] (μ : Measure V) [μ.IsAddLeftInvariant]
    (G : AddSubgroup V) [Countable G] {D : Set V} (hD : IsAddFundamentalDomain G D μ) {f : V → E}
    (hf : Integrable f μ) :
    HasSum (fun y : G => ∫ z in D, f (z - (y : V)) ∂μ) (∫ z, f z ∂μ) := by
  have h1 : HasSum (fun g : G => ∫ x in g +ᵥ D, f x ∂μ) (∫ z, f z ∂μ) := by
    have h := hasSum_integral_measure (μ := fun g : G => μ.restrict (g +ᵥ D)) (f := f)
      (by rwa [hD.sum_restrict])
    rwa [hD.sum_restrict] at h
  have h2 : ∀ g : G, ∫ x in g +ᵥ D, f x ∂μ = ∫ x in D, f (x - ((-g : G) : V)) ∂μ := by
    intro g
    rw [← Set.image_vadd,
      (measurePreserving_vadd g μ).setIntegral_image_emb (measurableEmbedding_const_vadd g) f D]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp [AddSubgroup.vadd_def, add_comm]
  simp_rw [h2] at h1
  exact (Equiv.neg G).hasSum_iff.mp h1

section Reps

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

def repMap {Λ Λ' : AddSubgroup V} (Ae : V ≃ₗ[ℂ] V) {S : Finset V}
    (hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ) (hS : IsReps (imgLat (Ae : V →ₗ[ℂ] V) Λ') Λ S)
    (p : S × Λ') : Λ :=
  ⟨(p.1 : V) + Ae (p.2 : V), Λ.add_mem (hS.1 _ p.1.2) (hle ⟨p.2, p.2.2, rfl⟩)⟩

theorem repMap_bijective {Λ Λ' : AddSubgroup V} (Ae : V ≃ₗ[ℂ] V) {S : Finset V}
    (hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ) (hS : IsReps (imgLat (Ae : V →ₗ[ℂ] V) Λ') Λ S) :
    Function.Bijective (repMap Ae hle hS) := by
  constructor
  · rintro ⟨⟨s, hs⟩, ⟨y, hy⟩⟩ ⟨⟨s', hs'⟩, ⟨y', hy'⟩⟩ h
    have h0 : s + Ae y = s' + Ae y' := congrArg Subtype.val h
    have h1 : s - s' = Ae (y' - y) := by
      rw [map_sub, sub_eq_sub_iff_add_eq_add, h0, add_comm]
    have h2 : s = s' := hS.2.1 s hs s' hs' (h1 ▸ ⟨y' - y, Λ'.sub_mem hy' hy, rfl⟩)
    subst h2
    have h3 : y = y' := Ae.injective (add_left_cancel h0)
    subst h3
    rfl
  · rintro ⟨x, hx⟩
    obtain ⟨s, hs, y, hy, hxy⟩ := hS.2.2 x hx
    refine ⟨(⟨s, hs⟩, ⟨y, hy⟩), Subtype.ext ?_⟩
    have h : Ae y = x - s := hxy
    change s + Ae y = x
    rw [h]
    abel

end Reps

theorem unfoldingIntegral : UnfoldIntegral := by
  intro V _ _ _ _ _ μ _ H Λ α δ Ae hL hU D' hD' _ S hS
  classical
  set Λ' : AddSubgroup V := Λ ⊓ imgLat (δ : V →ₗ[ℂ] V) Λ with hΛ'
  have : ProperSpace V := FiniteDimensional.proper ℂ V
  have : DiscreteTopology Λ := hL.1
  have hc : Countable Λ := TopologicalSpace.separableSpace_iff_countable.mp inferInstance
  have hc' : Countable Λ' := (AddSubgroup.inclusion_injective (inf_le_left : Λ' ≤ Λ)).countable
  obtain ⟨hT, -⟩ := kernelTermShift V H hU.herm α δ Ae hU.isom hU.cay
  have hgq : Integrable (gq H Ae) μ := (cayleyGaussianIntegral V μ H hU.herm hU.pos δ Ae hU.isom hU.cay).1
  have hle : imgLat (Ae : V →ₗ[ℂ] V) Λ' ≤ Λ := ud_latA_le hU
  let e : S × Λ' ≃ Λ := Equiv.ofBijective _ (repMap_bijective Ae hle hS)
  let f : V → V → ℂ := fun s z => gq H Ae (z - Ae.symm s)
  have hf : ∀ s, Integrable (f s) μ := fun s => hgq.comp_sub_right _
  have hfi : ∀ s, ∫ z, f s z ∂μ = ∫ z, gq H Ae z ∂μ := fun s =>
    integral_sub_right_eq_self (μ := μ) (gq H Ae) (Ae.symm s)
  have hFe : ∀ (p : S × Λ') z,
      termT H α δ ((e p : Λ) : V) z = phiC H α Ae p.1 * f p.1 (z - (p.2 : V)) := by
    intro p z
    rw [hT]
    have h1 : ((e p : Λ) : V) = (p.1 : V) + Ae (p.2 : V) := rfl
    rw [h1, ud_phi_wd hU (hS.1 _ p.1.2) (show Ae (p.2 : V) ∈ latA Λ δ Ae from ⟨p.2, p.2.2, rfl⟩)]
    simp only [f, map_add (f := _), LinearEquiv.symm_apply_apply]
    congr 2
    abel
  have hint : ∀ x : Λ, Integrable (fun z => termT H α δ (x : V) z) (μ.restrict D') := by
    intro x
    simp_rw [hT]
    exact ((hgq.comp_sub_right _).const_mul _).restrict
  have hsumn : Summable fun x : Λ => ∫ z in D', ‖termT H α δ (x : V) z‖ ∂μ := by
    have key : Summable fun p : S × Λ' => ∫ z in D', ‖termT H α δ ((e p : Λ) : V) z‖ ∂μ := by
      refine (summable_prod_of_nonneg (fun p => integral_nonneg fun z => norm_nonneg _)).mpr
        ⟨fun s => ?_, Summable.of_finite⟩
      have h := (hasSum_unfold μ Λ' hD' (hf s).norm).summable.mul_left ‖phiC H α Ae s‖
      refine h.congr fun y => ?_
      simp only [hFe, norm_mul, integral_const_mul]
    exact e.summable_iff.mp key
  have hmain := hasSum_integral_of_summable_integral_norm hint hsumn
  have hker : ∀ z, kerP H α Λ (δ.symm z) z * (wt H z : ℂ) = ∑' x : Λ, termT H α δ (x : V) z := by
    intro z
    simp only [kerP, termT, tsum_mul_right]
  simp_rw [hker]
  have hs2 : Summable fun c : S × Λ' => ∫ a in D', termT H α δ ((e c : Λ) : V) a ∂μ :=
    e.summable_iff.mpr hmain.summable
  rw [← hmain.tsum_eq, ← e.tsum_eq, hs2.tsum_prod, tsum_fintype,
    Finset.sum_mul, ← Finset.sum_coe_sort S]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp_rw [hFe, integral_const_mul]
  rw [tsum_mul_left, (hasSum_unfold μ Λ' hD' (hf s)).tsum_eq, hfi]

end Formalism.L2.Th1.H
end
end

