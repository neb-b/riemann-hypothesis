module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.PrimeComplMapLeNonZeroDivisorsQuot
public import GroundTheory.HeightsAndTheta.Heights.FieldsOfNumbers.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsLast
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section

theorem regularityDehomogenization_holds.proof (h₁ : GroundTheory.Heights₂.Heights.FieldNumbers.LocalizedQuotientLength.Statement.{0, 0})
    (h₂ : regularityLocalFlat_holds.Statement) : regularityDehomogenization_holds.Statement := by
  intro K _ ι _ P s t a W y hP hs hsP hW ht htW hy
  have hWp : W.IsPrime := hW.1.1.1
  have hPW : P ≤ W := le_sup_left.trans hW.1.1.2
  have := hP.1
  have := hWp
  have hWm : IsMultiProjPrime W := ⟨hWp, isMultiHomogIdeal_of_mem_minimalPrimes hP.2.1 hs hW.1, hW.2⟩

  have htnz : Ideal.Quotient.mk P t ∈ nonZeroDivisors (MRing ι ⧸ P) := by
    refine mem_nonZeroDivisors_of_ne_zero ?_
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun h => htW (hPW h)
  have hyO : y ∈ locRing P W := by
    refine Subring.subset_closure ⟨s, t, a, htnz, htW, hs, ht, ?_⟩
    rw [IsLocalization.eq_mk'_iff_mul_eq]
    exact hy
  refine ⟨hyO, ?_⟩
  obtain ⟨_, _, _, hmax⟩ := h₂ K ι P W hP hWm hPW
  have : IsLocalHom (algebraMap (locRing P W) (coneLocRing P W hPW)) :=
    ((local_hom_tfae _).out 3 1).mp hmax.le

  have hu : IsUnit (algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t)) :=
    IsLocalization.map_units (coneLocRing P W hPW)
      (⟨_, ⟨t, htW, rfl⟩⟩ : W.primeCompl.map (Ideal.Quotient.mk P))
  have hs' : algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s) =
      algebraMap (locRing P W) (coneLocRing P W hPW) ⟨y, hyO⟩ *
        algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P t) := by
    apply Subtype.ext
    rw [Subalgebra.coe_mul, locRing.algebraMap_cone_coe, Subalgebra.coe_algebraMap,
      Subalgebra.coe_algebraMap, hy]
  have hspan : Ideal.span {algebraMap (MRing ι ⧸ P) (coneLocRing P W hPW) (Ideal.Quotient.mk P s)} =
      (Ideal.span {(⟨y, hyO⟩ : locRing P W)}).map (algebraMap (locRing P W) (coneLocRing P W hPW)) := by
    rw [Ideal.map_span, Set.image_singleton, hs', Ideal.span_singleton_mul_right_unit hu]

  have key : ∀ (A B : Type) [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
      [Algebra A B] [IsLocalHom (algebraMap A B)] [Module.Flat A B],
      (maximalIdeal A).map (algebraMap A B) = maximalIdeal B → ∀ x : A,
        Module.length B (B ⧸ (Ideal.span {x}).map (algebraMap A B)) = Module.length A (A ⧸ Ideal.span {x}) := by
    intro A B _ _ _ _ _ _ _ hm x
    have hres : Module.length B (B ⧸ maximalIdeal B) = 1 := Module.length_eq_one_iff.mpr
      (isSimpleModule_iff_quot_maximal.mpr ⟨_, maximalIdeal.isMaximal _, ⟨LinearEquiv.refl _ _⟩⟩)
    rw [(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B (Ideal.span {x})).toLinearEquiv.length_eq,
      IsLocalRing.length_baseChange, hm, hres, mul_one]
  unfold multAt
  rw [dite_eq_left hWp, h₁ (MRing ι) P W s (coneLocRing P W hPW) inferInstance, hspan, locIdeal_eq_span hyO,
    key (locRing P W) (coneLocRing P W hPW) hmax]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsTerTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityLocalFinite.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι))
    (s : MRing ι) (a : K → ℕ) (W : Ideal (MRing ι)) (y : FractionRing (MRing ι ⧸ P)),
    IsArithVar P 1 → IsMultiHomog s a → s ∉ P → W ∈ divSupp P s → y ∈ locRing P W → y ≠ 0 →
    Finite (locRing P W ⧸ locIdeal P W y)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsFieldIntersectionNoBlockFam
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def GenDegAt (I : AllFam) (d : ℕ) : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin d → HermLine ι) (L' : Fin d → HermLine ι'),
    IsBlockMap κ v → IsArithVar P' d → IsArithVar (imageZ v P') d → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
    I K' ι' P' d L' = (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * I K ι (imageZ v P') d L

def ArithmeticIntersectionCycle.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ n : ℕ, GenDegAt I n →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
      (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
      (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (s : MRing ι) (α : K → ℕ),
      IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      IsMultiHomog s α → s ∉ imageZ v P' →
      cycR (I K' ι') P' L' (rename v s) =
        (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * cycR (I K ι) (imageZ v P') L s

def ArithmeticIntersectionIntegral.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (n : ℕ)
    (G : GenFibre v P') (J : IFamily G.Φ (fibreIdx ι' κ))
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (A : HermLine ι) (A' : HermLine ι') (f g : MRing ι),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) → IsFieldIntersection J →
    (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) → IsSmoothHerm A → IsPullHerm κ v A A' →
    IsRatSectionOn (imageZ v P') A f g →
    ptsIntegral P' (pot L') (logNormRat A' (rename v f) (rename v g)) =
      (J (fibreIdeal κ G) 0 Fin.elim0 : ℝ) * ptsIntegral (imageZ v P') (pot L) (logNormRat A f g)

section Inhabitants

open IndefiniteRowSideFullHecke.Inter

variable {F : Type} [Field F] {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsMultiHomogFirstCoordinate
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4

def ProjectivePointVertical.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
    (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
    (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι')) (d n : ℕ)
    (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (t : MRing ι) (a : K → ℕ),
    IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') d → d < n + 1 →
    (∀ j, IsPullHerm κ v (L j) (L' j)) → IsMultiHomog t a → t ∉ imageZ v P' →
    vertR P' L' (rename v t) = 0

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LeOfHeightMapEqZero
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityDivisorSupportClosed.le_of_height_map_eq_zero {A : Type*} [CommRing A] {P Q : Ideal A} [P.IsPrime]
    (h : (Q.map (Ideal.Quotient.mk P)).height = 0) : Q ≤ P := by
  intro x hx
  rw [Ideal.height_eq_zero_iff_eq_bot] at h
  have : Ideal.Quotient.mk P x ∈ Q.map (Ideal.Quotient.mk P) := Ideal.mem_map_of_mem _ hx
  rwa [h, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at this

theorem RegularityDivisorSupportClosed.not_add_add {m : ℕ} {a b : ℕ∞} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : ((m : WithBot ℕ∞) + (a : WithBot ℕ∞)) + (b : WithBot ℕ∞) = ((m + 1 : ℕ) : WithBot ℕ∞)) :
    False := by
  have h' : (m : ℕ∞) + a + b = ((m + 1 : ℕ) : ℕ∞) := by exact_mod_cast h
  induction a using ENat.recTopCoe with
  | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
  | coe a =>
    induction b using ENat.recTopCoe with
    | top => simp at h'; exact ENat.natCast_ne_top (m + 1) (by exact_mod_cast h'.symm)
    | coe b =>
      have : m + a + b = m + 1 := by exact_mod_cast h'
      have : a ≠ 0 := by exact_mod_cast ha
      have : b ≠ 0 := by exact_mod_cast hb
      omega

theorem RegularityDivisorSupportClosed.proof : RegularityDivisorSupportClosed.Statement := by
  intro K _ ι _ P s a W hP hs hsP
  obtain ⟨-, ⟨hPp, hPh, -⟩, -, hPdim⟩ := hP
  have := hPp
  have hsW' : ∀ {Q : Ideal (MRing ι)}, P ⊔ Ideal.span {s} ≤ Q → s ∈ Q := fun h =>
    h (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))
  constructor
  · rintro ⟨hWmin, hWrel⟩
    have h1 := dim_quot_minimal_add_one P W s hsP hWmin
    rw [hPdim] at h1
    refine ⟨⟨⟨hWmin.1.1, isMultiHomogIdeal_of_mem_minimalPrimes hPh hs hWmin, hWrel⟩,
      withBot_eq_of_add_one (by rw [h1, Nat.add_comm])⟩, le_sup_left.trans hWmin.1.2, hsW' hWmin.1.2⟩
  · rintro ⟨⟨⟨hWp, -, hWrel⟩, hWdim⟩, hPW, hsW⟩
    have hle : P ⊔ Ideal.span {s} ≤ W := sup_le hPW ((Ideal.span_singleton_le_iff_mem _).mpr hsW)
    refine ⟨⟨⟨hWp, hle⟩, fun Q hQ hQW => ?_⟩, hWrel⟩
    have := hQ.1
    have hPQ : P ≤ Q := le_sup_left.trans hQ.2
    have e1 := mvPolynomialInt_dimFormula P Q hPQ
    have e2 := mvPolynomialInt_dimFormula Q W hQW
    rw [hPdim] at e1
    rw [hWdim] at e2
    by_contra hWQ
    have ha : (W.map (Ideal.Quotient.mk Q)).height ≠ 0 := fun h0 =>
      hWQ (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0)
    have hb : (Q.map (Ideal.Quotient.mk P)).height ≠ 0 := fun h0 =>
      hsP (RegularityDivisorSupportClosed.le_of_height_map_eq_zero h0 (hsW' hQ.2))
    rw [← e2] at e1
    exact RegularityDivisorSupportClosed.not_add_add ha hb (by rw [e1, Nat.add_comm])

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.LeviOfRealSmulRight
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo

namespace pointFormEuler_holds

section Levi

variable {n : ℕ}

def leviOf (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) : ℂ :=
  ((H u v + H (Complex.I • u) (Complex.I • v) : ℝ) +
    Complex.I * ((H u (Complex.I • v) - H (Complex.I • u) v : ℝ))) / 4

theorem leviOf_add_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v w : Fin n → ℂ) :
    leviOf H u (v + w) = leviOf H u v + leviOf H u w := by
  simp only [leviOf, smul_add, map_add (f := _)]
  push_cast
  ring

theorem leviOf_real_smul_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) (r : ℝ) :
    leviOf H u (r • v) = r * leviOf H u v := by
  simp only [leviOf, smul_comm Complex.I r v, map_smul, smul_eq_mul]
  push_cast
  ring

theorem leviOf_I_smul_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u v : Fin n → ℂ) :
    leviOf H u (Complex.I • v) = -Complex.I * leviOf H u v := by
  have h : Complex.I • Complex.I • v = -v := by rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  simp only [leviOf, h, map_neg]
  push_cast
  ring_nf
  rw [Complex.I_sq]
  ring

theorem leviOf_sum_right (H : (Fin n → ℂ) →L[ℝ] (Fin n → ℂ) →L[ℝ] ℝ) (u : Fin n → ℂ) (v : Fin n → Fin n → ℂ) :
    leviOf H u (∑ j, v j) = ∑ j, leviOf H u (v j) := by
  classical
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty =>
    have h0 : leviOf H u 0 = 0 := by simp [leviOf]
    simpa using h0
  | insert j s hj ih => rw [Finset.sum_insert hj, Finset.sum_insert hj, leviOf_add_right, ih]

theorem cxHessian_mulVec_star (f : (Fin n → ℂ) → ℝ) (y x : Fin n → ℂ) (i : Fin n) :
    (cxHessian f y *ᵥ star x) i = leviOf (fderiv ℝ (fderiv ℝ f) y) (Pi.single i 1) x := by
  set H := fderiv ℝ (fderiv ℝ f) y
  have hx : x = ∑ j, ((x j).re • (Pi.single j 1 : Fin n → ℂ) +
      (x j).im • (Complex.I • (Pi.single j 1 : Fin n → ℂ))) := by
    funext p
    simp only [Finset.sum_apply, Pi.add_apply, Pi.smul_apply, Pi.single_apply, Complex.real_smul, smul_eq_mul,
      mul_ite, mul_one, mul_zero, Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    conv_lhs => rw [← Complex.re_add_im (x p)]
  have hent : ∀ j, cxHessian f y i j = leviOf H (Pi.single i 1) (Pi.single j 1) := fun j => rfl
  conv_rhs => rw [hx]
  rw [leviOf_sum_right]
  simp only [mulVec, dotProduct, hent]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [leviOf_add_right, leviOf_real_smul_right, leviOf_real_smul_right, leviOf_I_smul_right]
  have hs : star (x j) = ((x j).re : ℂ) - (x j).im * Complex.I := by
    apply Complex.ext <;> simp
  simp only [Pi.star_apply, hs]
  ring

end Levi

section Ambient

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem logh_contDiffAt {A : HermLine ι} (hA : IsSmoothHerm A) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) z :=
  ((hA.contDiffAt (isOpen_blockNonzero.mem_nhds hz)).of_le (WithTop.coe_le_coe.mpr le_top)).log
    (A.pos z hz).ne'

def bsmulCLM (d : K → ℂ) : ((Σ k, ι k) → ℂ) →L[ℂ] ((Σ k, ι k) → ℂ) :=
  ContinuousLinearMap.pi fun p => d p.1 • ContinuousLinearMap.proj p

omit [Fintype K] [∀ k, Fintype (ι k)] in
theorem bsmulCLM_apply (d : K → ℂ) (z : (Σ k, ι k) → ℂ) : bsmulCLM d z = bsmul d z := by
  funext p
  simp [bsmulCLM, bsmul]

theorem fderiv_logh_bsmul (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) :
    fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d z) =
      deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  have hφ : HasFDerivAt φ (fderiv ℝ φ z) z :=
    ((logh_contDiffAt hA hz).differentiableAt (by norm_num)).hasFDerivAt
  have hpath : HasDerivAt (fun s : ℝ => z + s • bsmul d z) (bsmul d z) 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).smul_const (bsmul d z)).const_add z
  have h1 : HasDerivAt (fun s : ℝ => φ (z + s • bsmul d z)) (fderiv ℝ φ z (bsmul d z)) 0 := by
    exact hφ.comp_hasDerivAt_of_eq (0 : ℝ) hpath (by simp)
  have hne : ∀ᶠ s : ℝ in 𝓝 0, ∀ k, 1 + (s : ℂ) * d k ≠ 0 :=
    eventually_all.mpr fun k => ContinuousAt.eventually_ne (by fun_prop) (by simp)
  have heq : (fun s : ℝ => φ (z + s • bsmul d z)) =ᶠ[𝓝 0]
      fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k) + φ z := by
    filter_upwards [hne] with s hs
    have hp : z + s • bsmul d z = fun p => (1 + (s : ℂ) * d p.1) * z p := by
      funext p
      simp only [Pi.add_apply, Pi.smul_apply, bsmul, Complex.real_smul]
      ring
    have hpos : 0 < ∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k :=
      Finset.prod_pos fun k _ => zpow_pos (norm_pos_iff.mpr (hs k)) _
    simp only [φ]
    rw [hp, A.smul (fun k => 1 + (s : ℂ) * d k) z hs, Real.log_mul hpos.ne' (A.pos z hz).ne']
  rw [(h1.congr_of_eventuallyEq heq.symm).deriv.symm, deriv_add_const]

theorem hess_logh_bsmul (A : HermLine ι) (hA : IsSmoothHerm A) (d : K → ℂ) {z : (Σ k, ι k) → ℂ}
    (hz : ∀ k, ∃ i, z ⟨k, i⟩ ≠ 0) (w : (Σ k, ι k) → ℂ) :
    fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) z w (bsmul d z) =
      -fderiv ℝ (fun z' => Real.log (A.h z')) z (bsmul d w) := by
  set φ : ((Σ k, ι k) → ℂ) → ℝ := fun z' => Real.log (A.h z')
  set L : ((Σ k, ι k) → ℂ) →L[ℝ] ((Σ k, ι k) → ℂ) := (bsmulCLM d).restrictScalars ℝ
  have hL : ∀ v, L v = bsmul d v := fun v => bsmulCLM_apply d v
  have hconst : (fun z' => fderiv ℝ φ z' (L z')) =ᶠ[𝓝 z]
      fun _ => deriv (fun s : ℝ => Real.log (∏ k, ‖1 + (s : ℂ) * d k‖ ^ A.a k)) 0 := by
    filter_upwards [isOpen_blockNonzero.mem_nhds hz] with z' hz'
    rw [hL]
    exact fderiv_logh_bsmul A hA d hz'
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) z :=
    ((logh_contDiffAt hA hz).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have h0 : fderiv ℝ (fun z' => fderiv ℝ φ z' (L z')) z w = 0 := by
    rw [hconst.fderiv_eq]
    simp
  rw [fderiv_clm_apply hd1 L.differentiableAt, L.fderiv] at h0
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, hL] at h0
  linarith

end Ambient

section Chain

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {n : ℕ}

theorem hess_comp_holo {φ : ((Σ k, ι k) → ℂ) → ℝ} {F : (Fin n → ℂ) → (Σ k, ι k) → ℂ} {y : Fin n → ℂ}
    (hφ : ContDiffAt ℝ 2 φ (F y)) (hF : AnalyticAt ℂ F y) (u v : Fin n → ℂ) :
    fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fderiv ℝ φ) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ φ (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) := by
  have hψ : ContDiffAt ℝ 2 (fun y' => φ (F y')) y := hφ.comp y (hF.contDiffAt.restrict_scalars ℝ)
  have hψ1 : DifferentiableAt ℝ (fderiv ℝ (fun y' => φ (F y'))) y :=
    (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hφev : ∀ᶠ y' in 𝓝 y, ContDiffAt ℝ 2 φ (F y') :=
    hF.continuousAt.tendsto.eventually (hφ.eventually (by simp))
  have hFev := hF.eventually_analyticAt
  have hcw : fderiv ℝ (fderiv ℝ (fun y' => φ (F y'))) y u v =
      fderiv ℝ (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) y u := by
    rw [fderiv_clm_apply hψ1 (differentiableAt_const v)]
    simp
  have hev : (fun y' => fderiv ℝ (fun y'' => φ (F y'')) y' v) =ᶠ[𝓝 y]
      fun y' => fderiv ℝ φ (F y') (fderiv ℂ F y' v) := by
    filter_upwards [hφev, hFev] with y' h1 h2
    rw [fderiv_fun_comp y' (h1.differentiableAt (by norm_num)) (h2.differentiableAt.restrictScalars ℝ),
      h2.differentiableAt.fderiv_restrictScalars ℝ]
    rfl
  have hd1 : DifferentiableAt ℝ (fderiv ℝ φ) (F y) :=
    (hφ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hc : DifferentiableAt ℝ (fun y' => fderiv ℝ φ (F y')) y :=
    hd1.comp y (hF.differentiableAt.restrictScalars ℝ)
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' v) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const v)
  rw [hcw, hev.fderiv_eq, fderiv_clm_apply hc (hG.restrictScalars ℝ),
    fderiv_fun_comp y hd1 (hF.differentiableAt.restrictScalars ℝ),
    hG.fderiv_restrictScalars ℝ, hF.differentiableAt.fderiv_restrictScalars ℝ]
  simp only [_root_.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    ContinuousLinearMap.coe_restrictScalars']
  ring

end Chain

theorem proof : pointFormEuler_holds.Statement := by
  intro K _ ι _ A n F y x c hA hF hblk hx
  have hφ : ContDiffAt ℝ 2 (fun z' => Real.log (A.h z')) (F y) := logh_contDiffAt hA hblk
  have hchain : ∀ u v, fderiv ℝ (fderiv ℝ (fun y' => Real.log (A.h (F y')))) y u v =
      fderiv ℝ (fderiv ℝ (fun z' => Real.log (A.h z'))) (F y) (fderiv ℂ F y u) (fderiv ℂ F y v) +
        fderiv ℝ (fun z' => Real.log (A.h z')) (F y) (fderiv ℂ (fun y' => fderiv ℂ F y' v) y u) :=
    fun u v => hess_comp_holo (φ := fun z' => Real.log (A.h z')) hφ hF u v
  have hG : DifferentiableAt ℂ (fun y' => fderiv ℂ F y' x) y :=
    hF.fderiv.differentiableAt.clm_apply (differentiableAt_const x)
  have hGI : fderiv ℂ (fun y' => fderiv ℂ F y' (Complex.I • x)) y =
      Complex.I • fderiv ℂ (fun y' => fderiv ℂ F y' x) y := by
    have : (fun y' => fderiv ℂ F y' (Complex.I • x)) = fun y' => Complex.I • fderiv ℂ F y' x := by
      funext y'
      exact map_smul _ _ _
    rw [this, fderiv_fun_const_smul hG]
  have hJIx : fderiv ℂ F y (Complex.I • x) = bsmul (fun k => Complex.I * c k) (F y) := by
    rw [map_smul, hx]
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbI : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul d (Complex.I • w) = bsmul (fun k => Complex.I * d k) w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, bsmul, smul_eq_mul]
    ring
  have hbII : ∀ (d : K → ℂ) (w : (Σ k, ι k) → ℂ),
      bsmul (fun k => Complex.I * d k) (Complex.I • w) = -bsmul d w := by
    intro d w
    funext p
    simp only [Pi.smul_apply, Pi.neg_apply, bsmul, smul_eq_mul]
    linear_combination (d p.1 * w p) * Complex.I_sq
  have hII : ∀ w : (Σ k, ι k) → ℂ, Complex.I • Complex.I • w = -w := fun w => by
    rw [smul_smul, Complex.I_mul_I, neg_one_smul]
  have heul := fun d w => hess_logh_bsmul A hA d hblk w
  funext i
  rw [cxHessian_mulVec_star, Pi.zero_apply]
  unfold leviOf
  rw [hchain, hchain, hchain, hchain, hJIx, hx, hGI]
  simp only [map_smul, _root_.smul_apply]
  rw [heul, heul, heul, heul, hbII, hbI, hII]
  simp only [map_neg]
  push_cast
  ring

end pointFormEuler_holds

end GroundTheory.Heights₂.Heights.Inter
end
end

