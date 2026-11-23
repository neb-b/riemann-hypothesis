module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0082
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsPiola
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0056
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0076
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0020
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0010
public import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.Bundle0001

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PLocalDimComponentBound
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial ComplexSets

noncomputable section

variable {n : ℕ}

theorem comap_curveLocalRing_strictMono (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ) :
    StrictMono (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q))) := by
  refine Monotone.strictMono_of_injective (fun P Q h ↦ Ideal.comap_mono h) ?_
  intro P Q h
  apply PrimeSpectrum.comap_injective_of_surjective _ (Ideal.Quotient.mk_surjective (I := I.map
    (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))))))
  apply PrimeSpectrum.localization_comap_injective _ (RingHom.ker (eval q)).primeCompl
  exact h

theorem le_comap_curveLocalRing (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    I ≤ (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal := by
  intro x hx
  have h0 : Ideal.Quotient.mk (I.map (algebraMap (MvPolynomial (Fin n) ℂ)
      (Localization.AtPrime (RingHom.ker (eval q)))))
      (algebraMap (MvPolynomial (Fin n) ℂ) (Localization.AtPrime (RingHom.ker (eval q))) x) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_map_of_mem _ hx)
  change algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x ∈ P.asIdeal
  rw [show algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q) x = 0 from h0]
  exact P.asIdeal.zero_mem

theorem comap_curveLocalRing_le (I : Ideal (MvPolynomial (Fin n) ℂ)) (q : Fin n → ℂ)
    (P : PrimeSpectrum (curveLocalRing I q)) :
    (PrimeSpectrum.comap (algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)) P).asIdeal ≤
      RingHom.ker (eval q) := by
  intro x hx
  by_contra h
  exact P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hx
    (isUnit_algebraMap_curveLocalRing I q x fun h' ↦ h (RingHom.mem_ker.2 h')))

theorem LocalDimComponentBound.proof : LocalDimComponentBound.Statement := by
  intro n I q hq
  rcases subsingleton_or_nontrivial (curveLocalRing I q) with hO | hO
  · refine ⟨RingHom.ker (eval q), inferInstance, fun x hx ↦ RingHom.mem_ker.2 (hq x hx),
      fun x hx ↦ RingHom.mem_ker.1 hx, ?_⟩
    rw [ringKrullDim_eq_bot_of_subsingleton]
    exact bot_le
  have : IsLocalRing (curveLocalRing I q) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  set f := algebraMap (MvPolynomial (Fin n) ℂ) (curveLocalRing I q)
  set p := LTSeries.longestOf (PrimeSpectrum (curveLocalRing I q))
  set W := (PrimeSpectrum.comap f p.head).asIdeal with hW
  have hWle : ∀ i, W ≤ (PrimeSpectrum.comap f (p i)).asIdeal := fun i ↦
    Ideal.comap_mono (p.monotone (Fin.zero_le i))
  let p' : LTSeries (PrimeSpectrum.zeroLocus (R := MvPolynomial (Fin n) ℂ) W) :=
    { length := p.length
      toFun := fun i ↦ ⟨PrimeSpectrum.comap f (p i), hWle i⟩
      step := fun i ↦ comap_curveLocalRing_strictMono I q (p.step i) }
  refine ⟨W, (PrimeSpectrum.comap f p.head).isPrime, le_comap_curveLocalRing I q _,
    fun x hx ↦ RingHom.mem_ker.1 (comap_curveLocalRing_le I q _ hx), ?_⟩
  rw [ringKrullDim, Order.krullDim_eq_length_of_finiteDimensionalOrder, ringKrullDim_quotient]
  exact Order.LTSeries.length_le_krullDim p'

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PMaDensChain
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.AnForm ReciprocityTheory.AnForm.A Filter Topology

noncomputable section

namespace MaDensChain

variable {D : ℕ}

theorem fderiv_comp_real (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    fderiv ℝ (h ∘ g) y = deriv h (g y) • fderiv ℝ g y :=
  (hh.hasDerivAt.comp_hasFDerivAt y hg.hasFDerivAt).fderiv

theorem dz_cplx_comp (j : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dz j (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dz j (cplx g) y := by
  rw [dz_cplx, dz_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem dzb_cplx_comp (k : Fin D) (h : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (y : Fin D → ℂ)
    (hh : DifferentiableAt ℝ h (g y)) (hg : DifferentiableAt ℝ g y) :
    dzb k (cplx (h ∘ g)) y = ((deriv h (g y) : ℝ) : ℂ) * dzb k (cplx g) y := by
  rw [dzb_cplx, dzb_cplx, fderiv_comp_real h g y hh hg]
  simp only [FunLike.coe_smul, Pi.smul_apply, smul_eq_mul]
  push_cast
  ring

theorem hessC_comp_real (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ) (hF : ContDiff ℝ 2 F)
    (hg : ContDiffAt ℝ 2 g z) :
    hessC (F ∘ g) z = ((deriv F (g z) : ℝ) : ℂ) • hessC g z + ((deriv (deriv F) (g z) : ℝ) : ℂ) • gradMat g g z := by
  obtain ⟨U, hU, hzU, hgU, -⟩ := MaDensLeibniz.exists_open_contDiffOn g g z hg hg
  have hF1 : Differentiable ℝ F := hF.differentiable (by norm_num)
  have hF' : Differentiable ℝ (deriv F) :=
    (hF.deriv' (n := 1)).differentiable (by norm_num)
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hessCDz_thm D _ U hU (hF.comp_contDiffOn hgU) z hzU j k, hessCDz_thm D g U hU hgU z hzU j k]
  have hev : dzb k (cplx (F ∘ g)) =ᶠ[𝓝 z] fun y => cplx (deriv F ∘ g) y * dzb k (cplx g) y := by
    filter_upwards [hU.mem_nhds hzU] with y hy
    exact dzb_cplx_comp k F g y (hF1 _)
      ((hgU.contDiffAt (hU.mem_nhds hy)).differentiableAt (by norm_num))
  have hgd : DifferentiableAt ℝ g z := hg.differentiableAt (by norm_num)
  have hA : DifferentiableAt ℝ (cplx (deriv F ∘ g)) z := by
    have h : cplx (deriv F ∘ g) = fun y => Complex.ofRealCLM ((deriv F ∘ g) y) := by
      funext y; simp [cplx]
    rw [h]
    exact Complex.ofRealCLM.differentiableAt.comp z ((hF' _).comp z hgd)
  have hB := differentiableAt_dzb (j := k) (MaDensLeibniz.contDiffAt_cplx hg)
  rw [dz_congr hev, dz_mul hA hB, dz_cplx_comp j (deriv F) g z (hF' _) hgd]
  simp only [gradMat, cplx, Function.comp_apply]
  ring

theorem gradMat_comp (F : ℝ → ℝ) (g : (Fin D → ℂ) → ℝ) (z : Fin D → ℂ)
    (hF : DifferentiableAt ℝ F (g z)) (hg : DifferentiableAt ℝ g z) :
    gradMat (F ∘ g) (F ∘ g) z = ((deriv F (g z) ^ 2 : ℝ) : ℂ) • gradMat g g z := by
  ext j k
  simp only [gradMat, Matrix.smul_apply, smul_eq_mul]
  rw [dz_cplx_comp j F g z hF hg, dzb_cplx_comp k F g z hF hg]
  push_cast
  ring

theorem proof : MaDensChain.Statement := by
  intro D φ F g z hF hg
  have hF1 : DifferentiableAt ℝ F (g z) := (hF.differentiable (by norm_num)) _
  constructor
  · rw [maDens_cons_eq, maDens_cons_eq, hessC_comp_real F g z hF hg]
    unfold gradDens
    rw [mdisc_cons_smul_add]
    simp only [Complex.add_re, Complex.re_ofReal_mul]
    ring
  · unfold gradDens
    rw [gradMat_comp F g z hF1 (hg.differentiableAt (by norm_num)), mdisc_cons_smul_fst]
    simp only [Complex.re_ofReal_mul]
    ring

end MaDensChain

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalCodimOneCompleteIntersection
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial IsLocalRing

noncomputable section

theorem ringKrullDim_quotient_add_height_of_finiteType {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsJacobsonRing A] [Algebra ℂ A] [Algebra.FiniteType ℂ A] (hfin : ringKrullDim A ≠ ⊤) (q : Ideal A)
    [q.IsPrime] : ringKrullDim (A ⧸ q) + (q.height : WithBot ℕ∞) = ringKrullDim A := by
  have : FiniteRingKrullDim A :=
    finiteRingKrullDim_iff_ne_bot_and_top.mpr ⟨fun h => by
      have h0 := ringKrullDim_nonneg_of_nontrivial (R := A)
      rw [h] at h0
      exact absurd h0 (by simp), hfin⟩
  obtain ⟨s, hs⟩ := ReciprocityTheory.ChartRestriction.G.Geo.DimF.exists_height_of_isMaximal_of_field ℂ A
  exact ReciprocityTheory.ChartRestriction.G.Geo.DimF.dim_quot_add_height (fun M N hM hN => (hs M hM).trans (hs N hN).symm) q

theorem isRegularLocalRing_of_height_eq_one {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A]
    [IsIntegrallyClosed A] (q : Ideal A) [q.IsPrime] (hq : q.height = 1) {C : Type*} [CommRing C]
    (eqv : Localization.AtPrime (maximalIdeal (Localization.AtPrime q)) ≃+* C) :
    IsRegularLocalRing C ∧ ringKrullDim C = 1 := by
  have : IsDomain (Localization.AtPrime q) :=
    IsLocalization.isDomain_localization (Ideal.primeCompl_le_nonZeroDivisors q)
  have : IsIntegrallyClosed (Localization.AtPrime q) :=
    isIntegrallyClosed_of_isLocalization _ q.primeCompl (Ideal.primeCompl_le_nonZeroDivisors q)
  have hdB : ringKrullDim (Localization.AtPrime q) = 1 := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height q, hq]
    rfl
  have : Ring.KrullDimLE 1 (Localization.AtPrime q) := Ring.krullDimLE_iff.mpr (by rw [hdB]; rfl)
  have h3 : IsIntegrallyClosed (Localization.AtPrime q) ∧
      ∀ p : Ideal (Localization.AtPrime q), p ≠ ⊥ → p.IsPrime → p = maximalIdeal (Localization.AtPrime q) :=
    ⟨inferInstance, fun p hp0 hpp => eq_maximalIdeal (hpp.isMaximal_of_ne_bot hp0)⟩
  have : IsDedekindDomain (Localization.AtPrime q) :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain (Localization.AtPrime q)).out 4 3).mp h3
  refine ⟨IsRegularLocalRing.of_ringEquiv eqv, ?_⟩
  rw [← ringKrullDim_eq_of_ringEquiv eqv,
    IsLocalization.AtPrime.ringKrullDim_eq_height (maximalIdeal (Localization.AtPrime q))
      (Localization.AtPrime (maximalIdeal (Localization.AtPrime q))),
    IsLocalRing.maximalIdeal_height_eq_ringKrullDim, hdB]

theorem NormalCodimOneCompleteIntersection.proof : NormalCodimOneCompleteIntersection.Statement := by
  classical
  intro σ _ P Q e hP hQ hPQ hint hdP hdQ
  have hdS : ringKrullDim (MvPolynomial σ ℂ) = (Fintype.card σ : ℕ) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field, Nat.card_eq_fintype_card,
      zero_add]

  obtain ⟨hgt, hhgt⟩ : ∃ k : ℕ, Q.height = k :=
    ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm
  have hQh : hgt + e = Fintype.card σ := by
    have h := ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ)
      (by rw [hdS]; exact ne_of_beq_false rfl) Q
    rw [hdQ, hdS, hhgt] at h
    have h' : e + hgt = Fintype.card σ := by exact_mod_cast h
    omega

  obtain ⟨Qb, hQb_def⟩ : ∃ Qb, Qb = Q.map (Ideal.Quotient.mk P) := ⟨_, rfl⟩
  have hQbp : Qb.IsPrime := hQb_def ▸ Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  have : Algebra.FiniteType ℂ (MvPolynomial σ ℂ ⧸ P) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ ℂ P) (Ideal.Quotient.mkₐ_surjective ℂ P)
  have : IsDomain (MvPolynomial σ ℂ ⧸ P) := Ideal.Quotient.isDomain P
  have hQb : Qb.height = 1 := by
    obtain ⟨k, hk⟩ : ∃ k : ℕ, Qb.height = k :=
      ENat.ne_top_iff_exists.mp Ideal.height_ne_top_of_isPrime |>.imp fun _ h => h.symm
    have h := ringKrullDim_quotient_add_height_of_finiteType (A := MvPolynomial σ ℂ ⧸ P)
      (by rw [hdP]; exact ne_of_beq_false rfl) Qb
    have hq : ringKrullDim ((MvPolynomial σ ℂ ⧸ P) ⧸ Qb) = ringKrullDim (MvPolynomial σ ℂ ⧸ Q) := by
      rw [hQb_def]
      exact ringKrullDim_eq_of_ringEquiv (DoubleQuot.quotQuotEquivQuotOfLE hPQ)
    rw [hq, hdQ, hdP, hk] at h
    have h' : e + k = e + 1 := by exact_mod_cast h
    rw [hk]
    exact_mod_cast (by omega : k = 1)

  have hdR : ringKrullDim (Localization.AtPrime Q) = (hgt : WithBot ℕ∞) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height Q (Localization.AtPrime Q), hhgt]
    rfl

  have hcomap : (maximalIdeal (Localization.AtPrime Qb)).comap
      ((algebraMap (MvPolynomial σ ℂ ⧸ P) (Localization.AtPrime Qb)).comp (Ideal.Quotient.mk P)) = Q := by
    rw [← Ideal.comap_comap]
    change (Ideal.under _ (maximalIdeal (Localization.AtPrime Qb))).comap (Ideal.Quotient.mk P) = Q
    rw [Localization.AtPrime.under_maximalIdeal, hQb_def,
      Ideal.comap_map_of_surjective' _ Ideal.Quotient.mk_surjective, Ideal.mk_ker, sup_eq_left.mpr hPQ]
  obtain ⟨eqv, -⟩ := LocalizationAtPrimeQuotient.proof (MvPolynomial σ ℂ) P Qb.primeCompl
    (maximalIdeal (Localization.AtPrime Qb)) Q hcomap
  obtain ⟨hregRI, hdRI⟩ := isRegularLocalRing_of_height_eq_one Qb hQb eqv
  have hgt1 : 1 ≤ hgt := by
    have h := ringKrullDim_quotient_le (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)))
    rw [hdRI, hdR] at h
    exact_mod_cast h
  obtain ⟨f, hfI, hfspan⟩ := exists_span_eq_of_isRegularLocalRing_quotient (hgt - 1) (Localization.AtPrime Q)
    (P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q))) (by
      rw [hdR, hdRI]
      have : hgt = 1 + (hgt - 1) := by omega
      exact_mod_cast this)

  have hnum : ∀ j, ∃ a ∈ P, ∃ s ∈ Q.primeCompl,
      f j * algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) s =
        algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) a := by
    intro j
    obtain ⟨⟨a, s⟩, h⟩ :=
      (IsLocalization.mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q)).mp (hfI j)
    exact ⟨a, a.2, s, s.2, h⟩
  choose a haP s hsQ hfa using hnum
  have hIa : P.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)) =
      (Ideal.span (Set.range a)).map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q)) := by
    apply le_antisymm
    · rw [hfspan, Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      have hu : IsUnit (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (s j)) :=
        IsLocalization.map_units (Localization.AtPrime Q) ⟨s j, hsQ j⟩
      have hf : f j = algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) (a j) * ↑hu.unit⁻¹ := by
        rw [← hfa j, mul_assoc, IsUnit.mul_val_inv, mul_one]
      rw [hf]
      exact Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨j, rfl⟩))
    · exact Ideal.map_mono (Ideal.span_le.mpr (by rintro _ ⟨j, rfl⟩; exact haP j))
  obtain ⟨t, ht⟩ := (IsNoetherian.noetherian P : P.FG)
  have hgen : ∀ p ∈ t, ∃ u ∈ Q.primeCompl, u * p ∈ Ideal.span (Set.range a) := by
    intro p hp
    have hp' : algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime Q) p ∈
        (Ideal.span (Set.range a)).map (algebraMap _ (Localization.AtPrime Q)) :=
      hIa ▸ Ideal.mem_map_of_mem _ (ht ▸ Ideal.subset_span hp)
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff (M := Q.primeCompl) (S := Localization.AtPrime Q) _ p).mp
      hp'
  choose! u hu hup using hgen
  refine ⟨hgt - 1, a, ∏ p ∈ t, u p, by omega, haP, ?_, ?_⟩
  · intro hmem
    obtain ⟨p, hp, hpQ⟩ := Ideal.IsPrime.prod_mem_iff.mp hmem
    exact hu p hp hpQ
  · intro p hp
    refine ⟨1, ?_⟩
    rw [pow_one]
    rw [← ht] at hp
    induction hp using Submodule.span_induction with
    | mem x hx =>
      rw [← Finset.mul_prod_erase t u hx, mul_comm (u x), mul_assoc]
      exact Ideal.mul_mem_left _ _ (hup x hx)
    | zero => simp
    | add x y _ _ hx hy =>
      rw [mul_add]
      exact Ideal.add_mem _ hx hy
    | smul r x _ hx =>
      rw [smul_eq_mul, mul_left_comm]
      exact Ideal.mul_mem_left _ _ hx

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.PNormalModelGoodPointChart
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial Topology ComplexSets

noncomputable section

theorem NormalModelGoodPointChart.proof : NormalModelGoodPointChart.Statement := by
  classical
  intro n d J u M w hgood
  obtain ⟨hw, c, f, h, g, a, b, k, hc, hfJ, hh, hsat, hg, hli, hk, ha, hb, hrel, himm⟩ := hgood

  let Φ : ((Fin n ⊕ Fin M.m → ℂ) →L[ℂ] ℂ) →ₗ[ℂ] (Fin n ⊕ Fin M.m → ℂ) :=
    { toFun := fun L s => L (Pi.single s 1), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  let D : Fin (c + 1) → (Fin n ⊕ Fin M.m → ℂ) →L[ℂ] ℂ :=
    Fin.cons (fderiv ℂ (fun z => eval z g) w) (fun j => fderiv ℂ (fun z => eval z (f j)) w)
  have hDli : LinearIndependent ℂ D := by
    refine LinearIndependent.of_comp Φ ?_
    convert hli using 1
    funext i s
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [D, Φ, NormalModelGoodPointChart.fderiv_eval_apply, Pi.single_apply]
    · simp [D, Φ, NormalModelGoodPointChart.fderiv_eval_apply, Pi.single_apply]
  obtain ⟨A, hA⟩ := NormalModelGoodPointChart.exists_clm_ker_inf
    (LinearMap.pi fun i => (D i : (Fin n ⊕ Fin M.m → ℂ) →ₗ[ℂ] ℂ))
    (IndefiniteRowSideFullHecke.ComplexSets.AnalyticImplicitChart.pi_surjective_of_linearIndependent hDli) d
    (by simp [Module.finrank_fintype_fun_eq_card]; omega)

  let q : Fin (d + 1) ⊕ Fin c → (Fin n ⊕ Fin M.m → ℂ) → ℂ :=
    Sum.elim (Fin.cons (fun z => eval z g) (fun i z => A (z - w) i)) (fun j z => eval z (f j))
  have hq0 : q (Sum.inl 0) = fun z => eval z g := by simp [q]
  have hqs : ∀ i : Fin d, q (Sum.inl i.succ) = fun z => A (z - w) i := fun i => by simp [q]
  have hAd : ∀ (i : Fin d) x, HasFDerivAt (fun z => A (z - w) i)
      ((ContinuousLinearMap.proj i).comp A) x := fun i x => by
    have e : (fun z => A (z - w) i) = fun z => ((ContinuousLinearMap.proj i).comp A) z - A w i := by
      funext z; simp [map_sub]
    rw [e]
    exact ((ContinuousLinearMap.proj i).comp A).hasFDerivAt.sub_const _
  have hqan : ∀ k x, AnalyticAt ℂ (q k) x := by
    intro k x
    rcases k with i | j
    · refine Fin.cases ?_ (fun i => ?_) i
      · rw [hq0]; exact AnalyticOnNhd.eval_mvPolynomial g x trivial
      · rw [hqs]
        have e : (fun z => A (z - w) i) = fun z => ((ContinuousLinearMap.proj i).comp A) z - A w i := by
          funext z; simp [map_sub]
        rw [e]
        exact (((ContinuousLinearMap.proj i).comp A).analyticAt x).sub analyticAt_const
    · exact AnalyticOnNhd.eval_mvPolynomial (f j) x trivial
  set W : Set (Fin n ⊕ Fin M.m → ℂ) := {z | eval z h ≠ 0 ∧ eval z a ≠ 0 ∧ eval z b ≠ 0} with hWdef
  have hWo : IsOpen W :=
    (isOpen_ne_fun (continuous_eval h) continuous_const).inter
      ((isOpen_ne_fun (continuous_eval a) continuous_const).inter
        (isOpen_ne_fun (continuous_eval b) continuous_const))
  obtain ⟨V, O, φ, hVo, hwV, hVW, hOo, hφan, hφV, hφl, hφr, hback, hder⟩ :=
    NormalModelGoodPointChart.exists_coordChart q w W (fun k => hqan k w) (by
      intro v hv
      refine hA v ?_ ?_
      · funext i
        have := hv (Sum.inl i.succ)
        rw [hqs, (hAd i w).fderiv] at this
        simpa using this
      · funext i
        refine Fin.cases ?_ (fun j => ?_) i
        · have := hv (Sum.inl 0)
          rw [hq0] at this
          simpa [D] using this
        · have := hv (Sum.inr j)
          change fderiv ℂ (fun z => eval z (f j)) w v = 0 at this
          simpa [D] using this)
      (by simp; omega) (hWo.mem_nhds ⟨hh, ha, hb⟩)

  have hZf : ∀ z ∈ V, (∀ j, eval z (f j) = 0) → z ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := by
    intro z hz hfz p hp
    obtain ⟨e, he⟩ := hsat p hp
    have hker : Ideal.span (Set.range f) ≤ RingHom.ker (eval z) :=
      Ideal.span_le.2 (by rintro _ ⟨j, rfl⟩; exact RingHom.mem_ker.2 (hfz j))
    have h0 := RingHom.mem_ker.1 (hker he)
    rw [map_mul, map_pow] at h0
    exact (mul_eq_zero.1 h0).resolve_left (pow_ne_zero _ (hVW hz).1)
  have hφZ : ∀ t ∈ O, φ t ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn M.ideal := fun t ht => hZf _ (hφV t ht) (hφr t ht)

  have hp0 : (fun i => q (Sum.inl i) w) = 0 := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simpa [hq0] using hg
    · simp [hqs]
  obtain ⟨hO0, hφ0⟩ := hback w hwV (fun j => hw _ (hfJ j))
  rw [hp0] at hO0 hφ0
  obtain ⟨r, hr, hrO⟩ := Metric.isOpen_iff.1 hOo 0 hO0
  have hpc : Continuous fun z i => q (Sum.inl i) z :=
    continuous_pi fun i => continuous_iff_continuousAt.2 fun x => (hqan _ x).continuousAt
  refine ⟨r, φ, k, hr, fun t ht => (hφan t (hrO ht)).differentiableAt.differentiableWithinAt,
    fun x hx y hy hxy => funext fun i => by rw [← hφl x (hrO hx) i, ← hφl y (hrO hy) i, hxy],
    hφ0, fun t ht => hφZ t (hrO ht), ?_, ?_, ?_⟩
  ·
    intro s hs
    refine ⟨V ∩ (fun z i => q (Sum.inl i) z) ⁻¹' Metric.ball 0 s,
      Filter.inter_mem (hVo.mem_nhds hwV) (hpc.continuousAt.preimage_mem_nhds (by
        rw [hp0]; exact Metric.ball_mem_nhds 0 hs)), ?_⟩
    rintro z ⟨hzZ, hzV, hzs⟩
    exact ⟨_, hzs, (hback z hzV fun j => hzZ _ (hfJ j)).2⟩
  ·
    refine ⟨fun t => eval (φ t) a / eval (φ t) b, ?_, ?_, ?_⟩
    · intro t ht
      have hφt := (hφan t (hrO ht)).differentiableAt
      have h1 : DifferentiableAt ℂ (fun t => eval (φ t) a) t :=
        (AnalyticOnNhd.eval_mvPolynomial a (φ t) trivial).differentiableAt.comp t hφt
      have h2 : DifferentiableAt ℂ (fun t => eval (φ t) b) t :=
        (AnalyticOnNhd.eval_mvPolynomial b (φ t) trivial).differentiableAt.comp t hφt
      have h3 : DifferentiableAt ℂ (fun t => eval (φ t) a * (eval (φ t) b)⁻¹) t :=
        h1.mul (h2.inv (hVW (hφV t (hrO ht))).2.2)
      simpa only [div_eq_mul_inv] using h3.differentiableWithinAt
    · intro t ht
      have hW' := hVW (hφV t (hrO ht))
      exact div_ne_zero hW'.2.1 hW'.2.2
    · intro t ht
      have hW' := hVW (hφV t (hrO ht))
      have hz := hφZ t (hrO ht) _ hrel
      have hgt : eval (φ t) g = t 0 := by simpa [hq0] using hφl t (hrO ht) 0
      have hl : eval (φ t) (rename (Sum.inl : Fin n → Fin n ⊕ Fin M.m) (linForm u)) =
          linEval u (IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp [linForm, linEval, IndefiniteRowSideFullHecke.ComplexSets.firstCoords, map_sum]
      simp only [map_sub, map_mul, map_pow, hl, hgt] at hz
      field_simp [hW'.2.2]
      linear_combination hz
  ·
    intro v hv0 hν
    have hDd := hder 0 hO0 v
    rw [hφ0] at hDd
    set x := fderiv ℂ φ 0 v with hx
    let πL : (Fin n ⊕ Fin M.m → ℂ) →L[ℂ] (Fin n → ℂ) :=
      ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin n ⊕ Fin M.m => ℂ) (Sum.inl i)
    have hπ : HasFDerivAt (fun t => IndefiniteRowSideFullHecke.ComplexSets.firstCoords (φ t)) (πL.comp (fderiv ℂ φ 0)) 0 :=
      πL.hasFDerivAt.comp 0 (hφan 0 hO0).differentiableAt.hasFDerivAt
    rw [hπ.fderiv] at hν
    have hx0 : x = 0 := by
      refine himm x (fun i => by simpa [πL, hx] using congrFun hν i) ?_ ?_
      · have := hDd.1 0
        rw [hq0, NormalModelGoodPointChart.fderiv_eval_apply] at this
        rw [this, hv0]
      · intro j
        have := hDd.2 j
        rwa [show q (Sum.inr j) = fun z => eval z (f j) from rfl,
          NormalModelGoodPointChart.fderiv_eval_apply] at this
    funext i
    have := hDd.1 i
    rw [hx0, map_zero] at this
    simpa using this.symm

end

end GroundTheory.Heights₂.Heights
end

