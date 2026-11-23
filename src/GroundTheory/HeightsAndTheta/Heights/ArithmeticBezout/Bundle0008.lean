module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.IsSemipositiveOn
public import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.Bundle0001
public import GroundTheory.ArithmeticGeometry.AbelianVarieties.JacobianSmoothness.RingKrullDimLeRingKrullDimQuotientAddOne

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChartGramMA
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

open scoped InnerProductSpace
open Filter Topology
open ReciprocityTheory.ChartRestriction.G.Geo (maDensity cxHessian)

theorem ChartGramMA.proof : ChartGramMA.Statement := by
  intro e n v y hv h0

  obtain ⟨t, ht, hto, hyt⟩ := eventually_nhds_iff.1 hv
  have han : AnalyticOnNhd ℂ v t := by
    have hd : DifferentiableOn ℂ v t := fun y' hy' => (ht y' hy').differentiableWithinAt
    exact AnalyticOnNhd.pi fun j =>
      ReciprocityTheory.AnForm.Osgood.osgood e t _ hto (differentiableOn_pi.mp hd j)
  set L := (PiLp.continuousLinearEquiv 2 ℂ (fun _ : Fin n => ℂ)).symm with hL
  set u : (Fin e → ℂ) → EuclideanSpace ℂ (Fin n) := fun y' => L (v y') with hu_def
  have hu : ∀ᶠ y' in 𝓝 y, AnalyticAt ℂ u y' := by
    filter_upwards [hto.mem_nhds hyt] with y' hy'
    exact (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).analyticAt _ |>.comp (han y' hy')
  have hu0 : u y ≠ 0 := by
    simpa [hu_def, hL, PiLp.coe_symm_continuousLinearEquiv] using h0
  have hDu : ∀ b, fderiv ℂ u y b = L (fderiv ℂ v y b) := fun b => by
    have hc := (L : (Fin n → ℂ) →L[ℂ] EuclideanSpace ℂ (Fin n)).hasFDerivAt.comp y
      (hv.self_of_nhds).hasFDerivAt
    have hc' : HasFDerivAt u _ y := hc
    rw [hc'.fderiv]
    rfl

  have hφ : (fun (_ : Fin e) (y' : Fin e → ℂ) => Real.log ‖WithLp.toLp 2 (v y')‖) =
      fun _ y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re := by
    funext _ y'
    have h := inner_self_eq_norm_sq (𝕜 := ℂ) (u y')
    have h' : (⟪u y', u y'⟫_ℂ).re = ‖u y'‖ ^ 2 := h
    rw [h', Real.log_pow]
    simp [hu_def, hL]

  set w : Fin (e + 1) → EuclideanSpace ℂ (Fin n) :=
    Fin.cons (u y) fun j => fderiv ℂ u y (Pi.single j 1) with hw
  set G : Matrix (Fin (e + 1)) (Fin (e + 1)) ℂ := Matrix.of fun a b => ⟪w a, w b⟫_ℂ with hG_def
  have hmat : G = Matrix.of fun a b => ∑ i,
      star ((Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) a i) *
        (Fin.cons (v y) fun j => fderiv ℂ v y (Pi.single j 1) : Fin (e + 1) → Fin n → ℂ) b i := by
    ext a b
    refine Fin.cases ?_ (fun a => ?_) a <;> refine Fin.cases ?_ (fun b => ?_) b <;>
      simp only [hG_def, hw, Matrix.of_apply, Fin.cons_zero, Fin.cons_succ, hDu] <;>
      simp only [PiLp.inner_apply, RCLike.inner_apply'] <;>
      simp [hu_def, hL]
  have hgram : gramVol v y = G.det.re := by
    rw [hmat]; rfl
  have hG00 : G 0 0 ≠ 0 := by
    simpa [hG_def, hw] using hu0
  have hcx : cxHessian (fun y' => 2⁻¹ * Real.log (⟪u y', u y'⟫_ℂ).re) y =
      (2 * G 0 0)⁻¹ • Matrix.transpose (Matrix.of fun i j : Fin e =>
        G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0) := by
    ext i j
    rw [ChartGram.cxHessian_half_log hu hu0]
    simp only [hG_def, hw, Matrix.smul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Fin.cons_zero, Fin.cons_succ, smul_eq_mul]
    have : ⟪u y, u y⟫_ℂ ≠ 0 := by simpa [hG_def, hw] using hG00
    field_simp
  have hS := ChartGram.det_eq_corner_mul_schur G hG00
  have hN : G 0 0 = ((‖u y‖ ^ 2 : ℝ) : ℂ) := by
    simp [hG_def, hw]
  have hNpos : 0 < ‖u y‖ := norm_pos_iff.2 hu0
  unfold maDensity
  rw [hφ, ChartGram.mixedDisc_const, hcx, Matrix.det_smul, Matrix.det_transpose, Fintype.card_fin,
    hgram, hS]
  generalize (Matrix.of fun i j : Fin e => G i.succ j.succ - G i.succ 0 * G 0 j.succ / G 0 0).det = Z
  rw [hN]
  have hnorm : ‖WithLp.toLp 2 (v y)‖ = ‖u y‖ := rfl
  rw [hnorm]
  generalize ‖u y‖ = r at hNpos ⊢
  rw [show ((2 : ℂ) * ((r ^ 2 : ℝ) : ℂ))⁻¹ ^ e = (((2 * r ^ 2)⁻¹ ^ e : ℝ) : ℂ) by push_cast; ring,
    Complex.re_ofReal_mul, Complex.re_ofReal_mul, pow_mul]
  have hpi : Real.pi ^ e * Real.pi⁻¹ ^ e = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ Real.pi_ne_zero, one_pow]
  have hr : r ^ (e * 2) * r⁻¹ ^ (e * 2) = 1 := by
    rw [← mul_pow, mul_inv_cancel₀ hNpos.ne', one_pow]
  have h2 : (1 / 2 : ℝ) ^ e * 2 ^ e = 1 := by
    rw [← mul_pow]; norm_num
  field_simp
  linear_combination (r ^ 2 * Z.re * r ^ (e * 2) * r⁻¹ ^ (e * 2) * (1 / 2) ^ e * 2 ^ e) * hpi +
    (r ^ 2 * Z.re * (1 / 2) ^ e * 2 ^ e) * hr + (r ^ 2 * Z.re) * h2

end GroundTheory.Heights₂.Heights
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormDimLe
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormDimLe

theorem coeff_zero_eq_zero_of_mem {F : Type} [Field F] {n : ℕ} {I : Ideal (MvPolynomial (Fin n) F)}
    (hI : IsProjPrime I) {g : MvPolynomial (Fin n) F} (hg : g ∈ I) : AddMonoidAlgebra.coeff g 0 = 0 := by
  by_contra h
  have h0 := hI.isHomog g hg 0
  rw [homogeneousComponent_zero] at h0
  exact hI.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h0 ((Ne.isUnit h).map C))

theorem exists_prime_liesOver {F : Type} [Field F] (K : Type) [Field K] [Algebra F K] {n : ℕ}
    (I : Ideal (MvPolynomial (Fin n) F)) [I.IsPrime] (hI : ∀ g ∈ I, AddMonoidAlgebra.coeff g 0 = 0) :
    ∃ P : Ideal (MvPolynomial (Fin n) K), P.IsPrime ∧
      P ≤ RingHom.ker (eval (0 : Fin n → K)) ∧
      P.comap (MvPolynomial.map (algebraMap F K)) = I := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : Module.Flat (MvPolynomial (Fin n) F) (MvPolynomial (Fin n) K) :=
    Module.Flat.isBaseChange F (MvPolynomial (Fin n) F) K (MvPolynomial (Fin n) K)
      (Algebra.IsPushout.out (R := F) (S := MvPolynomial (Fin n) F) (R' := K)
        (S' := MvPolynomial (Fin n) K))
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K))
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  have hle : I ≤ Q.under (MvPolynomial (Fin n) F) := by
    intro g hg
    rw [Ideal.under, Ideal.mem_comap, MvPolynomial.algebraMap_def, RingHom.mem_ker, eval_map,
      eval₂_zero_apply, constantCoeff_eq, hI g hg, map_zero]
  obtain ⟨P, hPQ, hP, hPI⟩ := Ideal.exists_ideal_le_liesOver_of_le Q hle
  refine ⟨P, hP, hPQ, ?_⟩
  rw [P.over_def I]
  rfl

theorem ringKrullDim_eq_of_comap {F : Type} [Field F] (K : Type) [Field K] [Algebra F K]
    [Algebra.IsAlgebraic F K] {n : ℕ} (I : Ideal (MvPolynomial (Fin n) F))
    (P : Ideal (MvPolynomial (Fin n) K)) (hPI : P.comap (MvPolynomial.map (algebraMap F K)) = I) :
    ringKrullDim (MvPolynomial (Fin n) K ⧸ P) = ringKrullDim (MvPolynomial (Fin n) F ⧸ I) := by
  let _ := MvPolynomial.algebraMvPolynomial (σ := Fin n) (R := F) (S := K)
  have : P.LiesOver I := ⟨hPI.symm⟩
  exact GroundTheory.Arith.Toric.ringKrullDim_eq_of_isIntegral
    (FaithfulSMul.algebraMap_injective (MvPolynomial (Fin n) F ⧸ I) (MvPolynomial (Fin n) K ⧸ P))

theorem exists_ne_zero_common_zero {K : Type} [Field K] [IsAlgClosed K] {n k : ℕ}
    (P : Ideal (MvPolynomial (Fin n) K)) [P.IsPrime] (hPQ : P ≤ RingHom.ker (eval (0 : Fin n → K)))
    (hdim : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) K ⧸ P))
    (u : Fin k × Fin n → K) :
    ∃ x : Fin n → K, x ≠ 0 ∧ (∀ g ∈ P, eval x g = 0) ∧ ∀ i, ∑ j, u (i, j) * x j = 0 := by
  classical
  set Q : Ideal (MvPolynomial (Fin n) K) := RingHom.ker (eval (0 : Fin n → K)) with hQdef
  have : Q.IsMaximal := RingHom.ker_isMaximal_of_surjective _ (fun c => ⟨C c, eval_C c⟩)
  let mk := Ideal.Quotient.mk P
  let ℓ : Fin k → MvPolynomial (Fin n) K := fun i => ∑ j, C (u (i, j)) * X j
  have hℓQ : ∀ i, ℓ i ∈ Q := by
    intro i
    simp [Q, ℓ, RingHom.mem_ker]
  set Mb : Ideal (MvPolynomial (Fin n) K ⧸ P) := Q.map mk
  have : Mb.IsMaximal := Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective
    (by rw [Ideal.mk_ker]; exact hPQ)
  let s : Finset (MvPolynomial (Fin n) K ⧸ P) := Finset.univ.image (fun i => mk (ℓ i))
  have hsM : Ideal.span (s : Set (MvPolynomial (Fin n) K ⧸ P)) ≤ Mb := by
    rw [Ideal.span_le]
    intro y hy
    simp only [s, Finset.coe_image, Finset.coe_univ, Set.image_univ, Set.mem_range] at hy
    obtain ⟨i, rfl⟩ := hy
    exact Ideal.mem_map_of_mem _ (hℓQ i)
  obtain ⟨q, hqmin, hqM⟩ := Ideal.exists_minimalPrimes_le hsM
  have : q.IsPrime := hqmin.1.1
  have hqht : q.height ≤ k := by
    refine (Ideal.height_le_card_of_mem_minimalPrimes_span_finset hqmin).trans ?_
    exact_mod_cast Finset.card_image_le.trans (by simp)
  have hMht : (Mb.height : WithBot ℕ∞) = ringKrullDim (MvPolynomial (Fin n) K ⧸ P) := by
    have h := GroundTheory.Arith.Abelian.Jacobian.height_add_ringKrullDim_quotient (k := K) Mb
    have hF : IsField ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) :=
      (Ideal.Quotient.maximal_ideal_iff_isField_quotient Mb).mp inferInstance
    have h0 : ringKrullDim ((MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) = 0 := by
      have h00 := ringKrullDim_eq_zero_of_isField (F := (MvPolynomial (Fin n) K ⧸ P) ⧸ Mb) hF
      convert h00 using 2
    rwa [h0, add_zero] at h
  have hqne : q ≠ Mb := by
    intro hq
    rw [hq] at hqht
    have h1 : ((Mb.height : ℕ∞) : WithBot ℕ∞) ≤ ((k : ℕ∞) : WithBot ℕ∞) := by exact_mod_cast hqht
    rw [hMht] at h1
    exact absurd h1 (not_le.mpr (by exact_mod_cast hdim))
  set Q' := q.comap mk
  have : Q'.IsPrime := Ideal.comap_isPrime mk q
  have hQQ' : ¬ Q ≤ Q' := by
    intro h
    apply hqne
    refine le_antisymm hqM ?_
    calc Mb = Q.map mk := rfl
      _ ≤ Q'.map mk := Ideal.map_mono h
      _ = q := Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective q
  have hnull := MvPolynomial.IsPrime.vanishingIdeal_zeroLocus (K := K) Q'
  obtain ⟨x, hx, hx0⟩ : ∃ x ∈ zeroLocus K Q', x ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, not_not] at hcon
    apply hQQ'
    intro g hg
    rw [← hnull, mem_vanishingIdeal_iff]
    intro x hx
    rw [hcon x hx]
    simpa [Q, RingHom.mem_ker] using hg
  refine ⟨x, hx0, fun g hg => ?_, fun i => ?_⟩
  · have hgQ' : g ∈ Q' := by
      show mk g ∈ q
      rw [Ideal.Quotient.eq_zero_iff_mem.mpr hg]
      exact q.zero_mem
    simpa using (mem_zeroLocus_iff.mp hx) g hgQ'
  · have hmem : ℓ i ∈ Q' := by
      show mk (ℓ i) ∈ q
      exact hqmin.1.2 (Ideal.subset_span (by simp [s]))
    simpa [ℓ] using (mem_zeroLocus_iff.mp hx) _ hmem

theorem proof : ChowFormDimLe.Statement := by
  intro F _ n k I f hI hf
  by_contra hdim
  rw [not_le] at hdim
  have := hI.isPrime
  obtain ⟨P, hP, hPQ, hPI⟩ := exists_prime_liesOver (AlgebraicClosure F) I
    (fun g hg => coeff_zero_eq_zero_of_mem hI hg)
  have hdimP : (k : WithBot ℕ∞) < ringKrullDim (MvPolynomial (Fin n) (AlgebraicClosure F) ⧸ P) := by
    rw [ringKrullDim_eq_of_comap (AlgebraicClosure F) I P hPI]
    exact_mod_cast hdim
  have hall : ∀ u : Fin k × Fin n → AlgebraicClosure F, u ∈ incidence I k := by
    intro u
    obtain ⟨x, hx0, hxP, hxu⟩ := exists_ne_zero_common_zero P hPQ hdimP u
    refine ⟨x, hx0, fun g hg => ?_, hxu⟩
    have hgP : MvPolynomial.map (algebraMap F (AlgebraicClosure F)) g ∈ P := by
      rw [← hPI] at hg
      exact hg
    have := hxP _ hgP
    rwa [eval_map, ← aeval_def] at this
  apply hf.1
  apply map_injective (algebraMap F (AlgebraicClosure F)) (algebraMap F (AlgebraicClosure F)).injective
  apply MvPolynomial.funext
  intro u
  rw [eval_map, ← aeval_def, ((hf.2 f).mpr dvd_rfl) u (hall u), map_zero, map_zero]

end ChowFormDimLe

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.PChowFormExtend
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

namespace ChowFormExtend

section Incidence

variable {F : Type*} [Field F] {n : ℕ}

def incidenceIdeal (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) :
    Ideal (MvPolynomial ((Fin k × Fin n) ⊕ Fin n) F) :=
  I.map (rename Sum.inr) ⊔
    Ideal.span (Set.range fun i : Fin k => ∑ j, X (Sum.inl (i, j)) * X (Sum.inr j))

theorem mem_zeroLocus_incidenceIdeal {E : Type*} [Field E] [Algebra F E]
    (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ) (z : (Fin k × Fin n) ⊕ Fin n → E) :
    z ∈ zeroLocus E (incidenceIdeal I k) ↔
      (∀ g ∈ I, aeval (z ∘ Sum.inr) g = 0) ∧ ∀ i, ∑ j, z (Sum.inl (i, j)) * z (Sum.inr j) = 0 := by
  have key : z ∈ zeroLocus E (incidenceIdeal I k) ↔ incidenceIdeal I k ≤ vanishingIdeal F {z} :=
    ⟨fun h p hp => (mem_vanishingIdeal_singleton_iff z p).2 (h p hp),
      fun h p hp => (mem_vanishingIdeal_singleton_iff z p).1 (h hp)⟩
  rw [key, incidenceIdeal, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.span_le, Set.range_subset_iff]
  refine and_congr ⟨fun h g hg => ?_, fun h g hg => ?_⟩ (forall_congr' fun i => ?_)
  · have := h hg
    rwa [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename] at this
  · rw [Ideal.mem_comap, mem_vanishingIdeal_singleton_iff, aeval_rename]
    exact h g hg
  · rw [SetLike.mem_coe, mem_vanishingIdeal_singleton_iff]
    simp

theorem vanishes_incidence_iff (I : Ideal (MvPolynomial (Fin n) F)) (k : ℕ)
    (g : MvPolynomial (Fin k × Fin n) F) :
    (∀ u ∈ incidence I k, aeval u g = 0) ↔
      ∀ j, X (Sum.inr j) * rename Sum.inl g ∈ (incidenceIdeal I k).radical := by
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := AlgebraicClosure F) (incidenceIdeal I k)]
  simp only [mem_vanishingIdeal_iff, mem_zeroLocus_incidenceIdeal]
  constructor
  · rintro h j z ⟨hI, hlin⟩
    rw [map_mul, aeval_X, aeval_rename]
    by_cases hx : z ∘ Sum.inr = 0
    · rw [show z (Sum.inr j) = 0 from congrFun hx j, zero_mul]
    · rw [h (z ∘ Sum.inl) ⟨z ∘ Sum.inr, hx, hI, hlin⟩, mul_zero]
  · rintro h u ⟨x, hx, hI, hlin⟩
    obtain ⟨j, hj⟩ : ∃ j, x j ≠ 0 := Function.ne_iff.1 hx
    have := h j (Sum.elim u x) ⟨by simpa using hI, by simpa using hlin⟩
    rw [map_mul, aeval_X, aeval_rename] at this
    simpa [hj] using this

theorem incidenceIdeal_map {K L : Type*} [Field K] [Field L] (σ : K →+* L)
    (I : Ideal (MvPolynomial (Fin n) K)) (k : ℕ) :
    incidenceIdeal (I.map (MvPolynomial.map σ)) k =
      (incidenceIdeal I k).map (MvPolynomial.map σ) := by
  rw [incidenceIdeal, incidenceIdeal, Ideal.map_sup, Ideal.map_span]
  congr 1
  · rw [← Ideal.map_coe (rename Sum.inr), ← Ideal.map_coe (rename Sum.inr), Ideal.map_map, Ideal.map_map]
    congr 1
    apply ringHom_ext <;> intro <;> simp
  · congr 1
    ext p
    simp

theorem radical_map_eq (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] (σ : K →+* L) {ι : Type} (J : Ideal (MvPolynomial ι K)) :
    (J.map (MvPolynomial.map σ)).radical = J.radical.map (MvPolynomial.map σ) :=
  le_antisymm
    ((h K L σ ι J.radical (Ideal.radical_isRadical J)).radical_le_iff.2
      (Ideal.map_mono Ideal.le_radical))
    (Ideal.map_radical_le _)

end Incidence

section Coord

variable {K L : Type*} [Field K] [Field L] [Algebra K L] {Y : Type*}

def coordPoly (φ : L →ₗ[K] K) : MvPolynomial Y L →+ MvPolynomial Y K where
  toFun p := AddMonoidAlgebra.map φ.toAddMonoidHom p
  map_zero' := by
    ext m
    simp [coeff_addMonoidAlgebraMap]
  map_add' p q := by
    ext m
    simp only [coeff_addMonoidAlgebraMap, MvPolynomial.coeff_add, map_add (f := _)]

theorem coeff_coordPoly (φ : L →ₗ[K] K) (p : MvPolynomial Y L) (m : Y →₀ ℕ) :
    AddMonoidAlgebra.coeff (coordPoly φ p) m = φ (AddMonoidAlgebra.coeff p m) :=
  rfl

theorem coordPoly_C_mul_map (φ : L →ₗ[K] K) (a : L) (q : MvPolynomial Y K) :
    coordPoly φ (C a * map (algebraMap K L) q) = C (φ a) * q := by
  ext m
  rw [coeff_coordPoly, coeff_C_mul, coeff_C_mul, coeff_map, mul_comm, ← Algebra.smul_def, map_smul,
    smul_eq_mul, mul_comm]

variable {β : Type*} [DecidableEq β]

def coordSupport (b : Module.Basis β K L) (p : MvPolynomial Y L) : Finset β :=
  p.support.biUnion fun m => (b.repr (AddMonoidAlgebra.coeff p m)).support

theorem sum_coordPoly (b : Module.Basis β K L) (p : MvPolynomial Y L) :
    ∑ c ∈ coordSupport b p, C (b c) * map (algebraMap K L) (coordPoly (b.coord c) p) = p := by
  ext m
  rw [coeff_sum]
  simp_rw [coeff_C_mul, coeff_map, coeff_coordPoly, Module.Basis.coord_apply, mul_comm (b _),
    ← Algebra.smul_def]
  conv_rhs => rw [← b.linearCombination_repr (AddMonoidAlgebra.coeff p m)]
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  symm
  apply Finset.sum_subset
  · intro c hc
    have hm : m ∈ p.support := by
      rw [mem_support_iff]
      intro h0
      rw [h0, map_zero] at hc
      simp at hc
    exact Finset.mem_biUnion.2 ⟨m, hm, hc⟩
  · intro c _ hc
    rw [Finsupp.notMem_support_iff.1 hc, zero_smul]

theorem coordPoly_sum (b : Module.Basis β K L) (S : Finset β) (h : β → MvPolynomial Y K) (c : β) :
    coordPoly (b.coord c) (∑ c' ∈ S, C (b c') * map (algebraMap K L) (h c')) =
      if c ∈ S then h c else 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  simp_rw [coordPoly_C_mul_map, Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  simp [apply_ite C, ite_mul]

theorem coordPoly_mem_of_mem_map (b : Module.Basis β K L) (T : Ideal (MvPolynomial Y K))
    {p : MvPolynomial Y L} (hp : p ∈ T.map (map (algebraMap K L))) (c : β) :
    coordPoly (b.coord c) p ∈ T := by
  have hp' : p ∈ Submodule.span (MvPolynomial Y L) ((map (algebraMap K L)) '' T) := hp
  clear hp
  revert c
  induction hp' using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨t, ht, rfl⟩ := hx
    intro c
    have e := coordPoly_C_mul_map (b.coord c) (1 : L) t
    rw [C_1, one_mul] at e
    rw [e]
    exact T.mul_mem_left _ ht
  | zero => intro c; rw [map_zero]; exact T.zero_mem
  | add x y _ _ hx hy => intro c; rw [map_add (f := _)]; exact T.add_mem (hx c) (hy c)
  | smul r x _ hx =>
    intro c
    have e : r * x = ∑ c₁ ∈ coordSupport b r, ∑ c₂ ∈ coordSupport b x,
        C (b c₁ * b c₂) * map (algebraMap K L) (coordPoly (b.coord c₁) r * coordPoly (b.coord c₂) x) := by
      conv_lhs => rw [← sum_coordPoly b r, ← sum_coordPoly b x]
      rw [Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
      rw [C_mul, map_mul]
      ring
    set_option synthInstance.maxHeartbeats 100000 in
      rw [smul_eq_mul, e, map_sum]
    refine T.sum_mem fun c₁ _ => ?_
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    refine T.sum_mem fun c₂ _ => ?_
    rw [coordPoly_C_mul_map]
    exact T.mul_mem_left _ (T.mul_mem_left _ (hx c₂))

end Coord

theorem isChowForm_map (h : RadicalBaseChange.Statement) {K L : Type} [Field K] [PerfectField K]
    [Field L] [Algebra K L] {n k : ℕ} (I : Ideal (MvPolynomial (Fin n) K))
    (f : MvPolynomial (Fin k × Fin n) K) (hf : IsChowForm I k f) :
    IsChowForm (I.map (map (algebraMap K L))) k (map (algebraMap K L) f) := by
  obtain ⟨hf0, hf⟩ := hf
  set R := (incidenceIdeal I k).radical
  have hK := fun g => vanishes_incidence_iff I k g
  have hrad : (incidenceIdeal (I.map (map (algebraMap K L))) k).radical = R.map (map (algebraMap K L)) := by
    rw [incidenceIdeal_map, radical_map_eq h]
  have hmapX : ∀ (j : Fin n) (p : MvPolynomial (Fin k × Fin n) K),
      map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl p) =
        X (Sum.inr j) * rename Sum.inl (map (algebraMap K L) p) := by
    intro j p
    rw [map_mul, map_X, map_rename]
  refine ⟨fun h0 => hf0 (map_injective _ (algebraMap K L).injective (by rw [h0, map_zero])), fun g => ?_⟩
  rw [vanishes_incidence_iff, hrad]
  constructor
  · intro hg
    classical
    let b := Module.Basis.ofVectorSpace K L
    set S := coordSupport b g
    set hc := fun c => coordPoly (b.coord c) g
    have hsum : ∑ c ∈ S, C (b c) * map (algebraMap K L) (hc c) = g := sum_coordPoly b g
    have hdiv : ∀ c ∈ S, ∃ q, hc c = f * q := by
      intro c hcS
      refine (hf _).1 ((hK _).2 fun j => ?_)
      have e : X (Sum.inr j) * rename Sum.inl g = ∑ c' ∈ S,
          C (b c') * map (algebraMap K L) (X (Sum.inr j) * rename Sum.inl (hc c')) := by
        conv_lhs => rw [← hsum]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [map_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun c' _ => ?_
        rw [map_mul, rename_C, hmapX]
        ring
      have hmem := coordPoly_mem_of_mem_map b R (e ▸ hg j) c
      rwa [coordPoly_sum, if_pos hcS] at hmem
    choose! q hq using hdiv
    refine ⟨∑ c ∈ S, C (b c) * map (algebraMap K L) (q c), ?_⟩
    conv_lhs => rw [← hsum]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun c hcS => ?_
    rw [hq c hcS, map_mul]
    ring
  · rintro ⟨q, rfl⟩ j
    have hfR : X (Sum.inr j) * rename Sum.inl f ∈ R := (hK f).1 ((hf f).2 dvd_rfl) j
    have hmem := Ideal.mem_map_of_mem (map (algebraMap K L)) hfR
    rw [hmapX] at hmem
    rw [map_mul (rename Sum.inl), ← mul_assoc]
    exact Ideal.mul_mem_right _ _ hmem

theorem proof (h : RadicalBaseChange.Statement) : ChowFormExtend.Statement := by
  intro K L _ _ _ σ n k I f hf
  let _ : Algebra K L := σ.toAlgebra
  exact isChowForm_map h I f hf

end ChowFormExtend

end

end GroundTheory.Heights₂.Heights
end

