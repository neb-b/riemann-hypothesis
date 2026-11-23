module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.LinearIndependentSumElimOfExact
public import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Bundle0003

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.DegreeTopEqArithDegree
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open NumberField

noncomputable section

theorem HermitianBundle.degree_top_eq_arithDegree {K : Type*} [Field K] [NumberField K]
    (E : HermitianBundle K) : E.degree ⊤ = E.arithDegree := by
  obtain ⟨s, hs⟩ := exists_linearIndependent_fin (K := K) (E := E.carrier)
  let s' : Fin (Module.finrank (𝓞 K) E.carrier) → (⊤ : Submodule (𝓞 K) E.carrier) :=
    fun i ↦ ⟨s i, Submodule.mem_top⟩
  have hs' : LinearIndependent (𝓞 K) s' :=
    LinearIndependent.of_comp (⊤ : Submodule (𝓞 K) E.carrier).subtype hs
  have hcard : Fintype.card (Fin (Module.finrank (𝓞 K) E.carrier)) = E.rank ⊤ := by
    rw [Fintype.card_fin, HermitianBundle.rank, finrank_top]
  rw [E.degree_eq_of_linearIndependent ⊤ hs' hcard, HermitianBundle.arithDegree,
    arithDegree_eq E.metric hs (Fintype.card_fin _), GroundTheory.Heights₂.Heights.degreeWith]
  have hmap : (Submodule.span (𝓞 K) (Set.range s')).map
      (Submodule.topEquiv : (⊤ : Submodule (𝓞 K) E.carrier) ≃ₗ[𝓞 K] E.carrier).toLinearMap =
      Submodule.span (𝓞 K) (Set.range s) := by
    rw [Submodule.map_span, ← Set.range_comp]
    rfl
  rw [Nat.card_congr (Submodule.Quotient.equiv _ _ Submodule.topEquiv hmap).toEquiv]

theorem HermitianBundle.normDegree_le_rank_mul {K : Type} [Field K] [NumberField K]
    (E : HermitianBundle.{0} K) (G : Submodule (𝓞 K) E.carrier) (m : ℝ)
    (hm : E.slopeMax ≤ (m : EReal)) : E.normDegree G ≤ E.rank G * m := by
  by_cases hr : E.rank G = 0
  · have hbot : G = ⊥ := (Submodule.finrank_eq_zero (R := 𝓞 K) (S := G)).mp hr
    rw [hr, HermitianBundle.normDegree, hbot, HermitianBundle.degree_bot]
    simp
  · have hne : G ≠ ⊥ := by
      rintro rfl
      apply hr
      simp [HermitianBundle.rank]
    have hle : ((E.slope G : ℝ) : EReal) ≤ E.slopeMax := le_iSup₂_of_le G hne le_rfl
    have hs : E.slope G ≤ m := EReal.coe_le_coe_iff.mp (hle.trans hm)
    have hrpos : (0 : ℝ) < E.rank G := by exact_mod_cast Nat.pos_of_ne_zero hr
    have heq : E.normDegree G = E.rank G * E.slope G := by
      unfold HermitianBundle.slope
      field_simp
    rw [heq]
    exact mul_le_mul_of_nonneg_left hs hrpos.le

theorem slopeMaxExtension : SlopeMaxExtension.Statement := by
  intro K _ _ E' E E'' X
  show (⨆ (F : Submodule (𝓞 K) E.carrier) (_ : F ≠ ⊥), ((E.slope F : ℝ) : EReal)) ≤ _
  refine iSup₂_le fun F hF ↦ ?_
  rcases eq_or_ne (max E'.slopeMax E''.slopeMax) ⊤ with hM | hM
  · rw [hM]
    exact le_top
  have hrank := X.rank_sub_eq F
  have hpos : 0 < E.rank F := by
    rcases Nat.eq_zero_or_pos (E.rank F) with h | h
    · exact absurd ((Submodule.finrank_eq_zero (R := 𝓞 K) (S := F)).mp h) hF
    · exact h
  have hMbot : max E'.slopeMax E''.slopeMax ≠ ⊥ := by
    have : 0 < E'.rank (F.comap X.incl) ∨ 0 < E''.rank (F.map X.proj) := by omega
    rcases this with h | h
    · have hne : F.comap X.incl ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E'.slope (F.comap X.incl) : ℝ) : EReal) ≤ E'.slopeMax :=
        le_iSup₂_of_le (F.comap X.incl) hne le_rfl
      have hle := h0.trans (le_max_left _ E''.slopeMax)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
    · have hne : F.map X.proj ≠ ⊥ := by
        intro h0
        rw [h0] at h
        simp [HermitianBundle.rank] at h
      have h0 : ((E''.slope (F.map X.proj) : ℝ) : EReal) ≤ E''.slopeMax :=
        le_iSup₂_of_le (F.map X.proj) hne le_rfl
      have hle := h0.trans (le_max_right E'.slopeMax _)
      exact ne_bot_of_le_ne_bot (EReal.coe_ne_bot _) hle
  set m := (max E'.slopeMax E''.slopeMax).toReal
  have hMm : max E'.slopeMax E''.slopeMax = (m : EReal) := (EReal.coe_toReal hM hMbot).symm
  have h1 := E'.normDegree_le_rank_mul (F.comap X.incl) m ((le_max_left _ _).trans_eq hMm)
  have h2 := E''.normDegree_le_rank_mul (F.map X.proj) m ((le_max_right _ _).trans_eq hMm)
  have hdeg := X.degree_submodule_le F
  have hd : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hnd : E.normDegree F ≤ E'.normDegree (F.comap X.incl) + E''.normDegree (F.map X.proj) := by
    simp only [HermitianBundle.normDegree]
    rw [← add_div]
    exact div_le_div_of_nonneg_right hdeg hd.le
  have hrpos : (0 : ℝ) < E.rank F := by exact_mod_cast hpos
  have hr : (E.rank F : ℝ) = E'.rank (F.comap X.incl) + E''.rank (F.map X.proj) := by
    exact_mod_cast hrank
  have hs : E.slope F ≤ m := by
    unfold HermitianBundle.slope
    rw [div_le_iff₀ hrpos, hr]
    calc E.normDegree F ≤ E'.rank (F.comap X.incl) * m + E''.rank (F.map X.proj) * m := by linarith
      _ = m * (E'.rank (F.comap X.incl) + E''.rank (F.map X.proj)) := by ring
  rw [hMm]
  exact EReal.coe_le_coe_iff.mpr hs

end

end GroundTheory.Heights₂.Heights
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveComplexPoint
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

namespace CurveComplexPoint

theorem eval₂_smul_homog {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {F : Type*} [CommRing F] (f : MRing ι) (a : K → ℕ) (hf : IsMultiHomog f a)
    (c : K → F) (y : (Σ k, ι k) → F) :
    eval₂ (Int.castRingHom F) (fun p => c p.1 * y p) f =
      (∏ k, c k ^ a k) * eval₂ (Int.castRingHom F) y f := by
  rw [eval₂_eq', eval₂_eq', Finset.mul_sum]
  refine Finset.sum_congr rfl fun d hd => ?_
  have hc : (∏ i : (Σ k, ι k), c i.1 ^ d i) = ∏ k, c k ^ a k := by
    rw [Fintype.prod_sigma]
    refine Finset.prod_congr rfl fun k _ => ?_
    show ∏ y, c k ^ d ⟨k, y⟩ = _
    rw [Finset.prod_pow_eq_pow_sum, hf d hd k]
  simp only [mul_pow, Finset.prod_mul_distrib, hc]
  ring

theorem full : CurveComplexPoint.Statement := by
  intro K _ ι _ W hW
  classical
  obtain ⟨_, ⟨hprime, ⟨S, hS, hWS⟩, hrel⟩, hhor, _⟩ := hW
  choose c hc using hrel
  let R := MRing ι ⧸ W
  let F := FractionRing R
  let x : (Σ k, ι k) → F := fun p => algebraMap R F (Ideal.Quotient.mk W (X p))
  have hx : ∀ k, x ⟨k, c k⟩ ≠ 0 := fun k h => hc k
    (Ideal.Quotient.eq_zero_iff_mem.mp (IsFractionRing.injective R F (h.trans (map_zero _).symm)))
  have hxeval : ∀ f : MRing ι,
      eval₂ (Int.castRingHom F) x f = algebraMap R F (Ideal.Quotient.mk W f) := by
    intro f
    have h : eval₂Hom (Int.castRingHom F) x = (algebraMap R F).comp (Ideal.Quotient.mk W) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [x])
    exact RingHom.congr_fun h f
  have : CharZero F := charZero_of_inj_zero fun n hn => by
    have h1 : Ideal.Quotient.mk W (C (n : ℤ)) = 0 :=
      IsFractionRing.injective R F (by simpa using hn)
    have h2 : (n : ℤ) ∈ W.comap (C : ℤ →+* MRing ι) :=
      Ideal.mem_comap.mpr (Ideal.Quotient.eq_zero_iff_mem.mp h1)
    rw [hhor, Ideal.mem_bot] at h2
    exact_mod_cast h2
  let y : (Σ k, ι k) → F := fun p => (x ⟨p.1, c p.1⟩)⁻¹ * x p
  let ψ : MvPolynomial (Σ k, ι k) ℚ →+* F := eval₂Hom (Rat.castHom F) y
  have hψmap : ∀ f : MRing ι,
      ψ (map (Int.castRingHom ℚ) f) = eval₂ (Int.castRingHom F) y f := by
    intro f
    simp only [ψ, coe_eval₂Hom, eval₂_map]
    congr 1
    exact RingHom.ext_int _ _
  have hWker : ∀ f ∈ W, map (Int.castRingHom ℚ) f ∈ RingHom.ker ψ := by
    intro f hf
    rw [hWS] at hf
    have hle : Ideal.span S ≤ (RingHom.ker ψ).comap (map (Int.castRingHom ℚ)) := by
      refine Ideal.span_le.mpr fun s hs => ?_
      obtain ⟨a, ha⟩ := hS s hs
      have hsW : s ∈ W := hWS ▸ Ideal.subset_span hs
      show ψ (map (Int.castRingHom ℚ) s) = 0
      rw [hψmap]
      refine (eval₂_smul_homog s a ha (fun k => (x ⟨k, c k⟩)⁻¹) x).trans ?_
      rw [hxeval, Ideal.Quotient.eq_zero_iff_mem.mpr hsW, map_zero, mul_zero]
    exact hle hf
  have hXker : ∀ k, (X ⟨k, c k⟩ - 1 : MvPolynomial (Σ k, ι k) ℚ) ∈ RingHom.ker ψ := by
    intro k
    rw [RingHom.mem_ker, map_sub, map_one]
    simp only [ψ, coe_eval₂Hom, eval₂_X, y]
    rw [inv_mul_cancel₀ (hx k), sub_self]
  obtain ⟨m, hm, hkm⟩ := Ideal.exists_le_maximal (RingHom.ker ψ) (RingHom.ker_ne_top ψ)
  let L := MvPolynomial (Σ k, ι k) ℚ ⧸ m
  let : Field L := Ideal.Quotient.field m
  have : Module.Finite ℚ L := finite_of_finite_type_of_isJacobsonRing ℚ L
  have : Algebra.IsAlgebraic ℚ L := Algebra.IsAlgebraic.of_finite ℚ L
  let φ : L →ₐ[ℚ] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let z : (Σ k, ι k) → ℂ := fun p => φ (Ideal.Quotient.mk m (X p))
  have hz : ∀ f : MRing ι, eval z (map (Int.castRingHom ℂ) f) =
      φ (Ideal.Quotient.mk m (map (Int.castRingHom ℚ) f)) := by
    intro f
    have h : eval₂Hom (Int.castRingHom ℂ) z =
        (φ : L →+* ℂ).comp ((Ideal.Quotient.mk m).comp (map (Int.castRingHom ℚ))) :=
      ringHom_ext (fun n => by simp) (fun p => by simp [z])
    rw [eval_map]
    exact RingHom.congr_fun h f
  refine ⟨z, fun k => ⟨c k, ?_⟩, fun f hf => ?_⟩
  · have h1 : Ideal.Quotient.mk m (X ⟨k, c k⟩) = Ideal.Quotient.mk m 1 :=
      Ideal.Quotient.eq.mpr (hkm (hXker k))
    simp only [z, h1, map_one]
    exact one_ne_zero
  · rw [hz, Ideal.Quotient.eq_zero_iff_mem.mpr (hkm (hWker f hf)), map_zero]

end CurveComplexPoint

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.PCurveDivVertical
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace CurveDivVertical

attribute [local instance] MvPolynomial.weightedGradedAlgebra

open Classical

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]


open Classical in
def wt (T : Finset K) : (Σ k, ι k) → ℕ := fun p ↦ if p.1 ∈ T then 1 else 0

def proj (T : Finset K) : MRing ι →+* MRing ι :=
  GradedRing.projZeroRingHom (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T))

theorem proj_apply (T : Finset K) (f : MRing ι) :
    proj T f = weightedHomogeneousComponent (wt T) 0 f := by
  rw [proj, GradedRing.projZeroRingHom_apply]
  exact weightedDecomposition.decompose'_apply ℤ (wt T) f 0

theorem weight_eq_zero_iff {σ : Type*} (w : σ → ℕ) (d : σ →₀ ℕ) :
    Finsupp.weight w d = 0 ↔ ∀ p, d p ≠ 0 → w p = 0 := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]
  constructor
  · intro h p hp
    exact (mul_eq_zero.mp (h p (Finsupp.mem_support_iff.mpr hp))).resolve_left hp
  · intro h p hp
    rw [smul_eq_mul, h p (Finsupp.mem_support_iff.mp hp), mul_zero]

theorem coeff_proj (T : Finset K) (f : MRing ι) (d : (Σ k, ι k) →₀ ℕ) :
    AddMonoidAlgebra.coeff (proj T f) d = if ∀ p, d p ≠ 0 → p.1 ∉ T then AddMonoidAlgebra.coeff f d else 0 := by
  classical
  rw [proj_apply, coeff_weightedHomogeneousComponent]
  have : Finsupp.weight (wt T) d = 0 ↔ ∀ p, d p ≠ 0 → p.1 ∉ T := by
    rw [weight_eq_zero_iff]
    refine forall_congr' fun p ↦ imp_congr_right fun _ ↦ ?_
    unfold wt
    split_ifs with h <;> simp [h]
  by_cases h : ∀ p, d p ≠ 0 → p.1 ∉ T
  · rw [if_pos (this.mpr h), if_pos h]
  · rw [if_neg (mt this.mp h), if_neg h]

theorem proj_empty (f : MRing ι) : proj ∅ f = f := by
  ext d
  rw [coeff_proj, if_pos (fun _ _ ↦ Finset.notMem_empty _)]

theorem proj_proj {S T : Finset K} (hST : S ⊆ T) (f : MRing ι) : proj T (proj S f) = proj T f := by
  ext d
  rw [coeff_proj, coeff_proj, coeff_proj]
  by_cases h : ∀ p, d p ≠ 0 → p.1 ∉ T
  · rw [if_pos h, if_pos h, if_pos fun p hp hS ↦ h p hp (hST hS)]
  · rw [if_neg h, if_neg h]

theorem proj_univ (f : MRing ι) : proj Finset.univ f = C (constantCoeff f) := by
  ext d
  rw [coeff_proj, coeff_C, constantCoeff_eq]
  by_cases hd : d = 0
  · subst hd
    simp
  · rw [if_neg (Ne.symm hd), if_neg]
    intro h
    apply hd
    ext p
    by_contra hp
    exact h p hp (Finset.mem_univ _)

theorem proj_X_of_mem {T : Finset K} {k : K} (hk : k ∈ T) (i : ι k) :
    proj T (X ⟨k, i⟩ : MRing ι) = 0 := by
  ext d
  rw [coeff_proj, coeff_X]
  simp only [AddMonoidAlgebra.coeff_zero, Finsupp.zero_apply]
  split_ifs with h1 h2
  · subst h2
    exact absurd hk (h1 ⟨k, i⟩ (by simp))
  · rfl
  · rfl

theorem proj_X_of_notMem {T : Finset K} {k : K} (hk : k ∉ T) (i : ι k) :
    proj T (X ⟨k, i⟩ : MRing ι) = X ⟨k, i⟩ := by
  ext d
  rw [coeff_proj, coeff_X]
  split_ifs with h1 h2 h2
  · rfl
  · rfl
  · subst h2
    exact absurd (fun p hp ↦ by
      rw [Finsupp.single_apply] at hp
      split_ifs at hp with hq
      · subst hq; exact hk
      · exact absurd rfl hp) h1
  · rfl

theorem isWeightedHomogeneous_of_isMultiHomog (T : Finset K) {f : MRing ι} {a : K → ℕ}
    (hf : IsMultiHomog f a) :
    IsWeightedHomogeneous (wt T) f (∑ k, if k ∈ T then a k else 0) := by
  classical
  intro d hd
  have hmon := hf d (mem_support_iff.mpr hd)
  rw [Finsupp.weight_apply, Finsupp.sum_fintype _ _ (by intros; simp), Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  unfold wt
  by_cases hk : k ∈ T
  · simp only [hk, if_true, smul_eq_mul, mul_one]
    exact hmon k
  · simp [hk]

theorem isHomogeneous_sup (T : Finset K) {W : Ideal (MRing ι)} (hW : IsMultiHomogIdeal W)
    {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a) :
    (W ⊔ Ideal.span {s}).IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)) := by
  obtain ⟨G, hG, rfl⟩ := hW
  rw [← Ideal.span_union]
  apply Ideal.homogeneous_span
  rintro x (hx | hx)
  · obtain ⟨b, hb⟩ := hG x hx
    exact ⟨_, isWeightedHomogeneous_of_isMultiHomog T hb⟩
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨_, isWeightedHomogeneous_of_isMultiHomog T hs⟩

theorem isHomogeneous_of_mem_minimalPrimes (T : Finset K) {J V : Ideal (MRing ι)}
    (hJ : J.IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)))
    (hV : V ∈ J.minimalPrimes) :
    V.IsHomogeneous (weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)) := by
  set 𝒜 := weightedHomogeneousSubmodule ℤ (wt (ι := ι) T)
  replace hV : Minimal (fun q : Ideal (MRing ι) ↦ q.IsPrime ∧ J ≤ q) V := hV
  have hcore : (V.homogeneousCore 𝒜).toIdeal.IsPrime := hV.prop.1.homogeneousCore
  have hJc : J ≤ (V.homogeneousCore 𝒜).toIdeal :=
    hJ.toIdeal_homogeneousCore_eq_self.symm.trans_le (Ideal.homogeneousCore_mono _ hV.prop.2)
  have heq := hV.eq_of_le ⟨hcore, hJc⟩ (Ideal.toIdeal_homogeneousCore_le 𝒜 V)
  rw [← heq]
  exact (V.homogeneousCore 𝒜).isHomogeneous

end CurveDivVertical


open CurveDivVertical in
theorem CurveDivVertical.full : CurveDivVertical.Statement := by
  classical
  intro K _ ι _ W s a hW hs hsW V hV hhor
  obtain ⟨_, ⟨hWp, hWh, -⟩, -, hdim⟩ := hW
  obtain ⟨hVmin', hVrel⟩ := hV
  have hVmin : Minimal (fun q : Ideal (MRing ι) ↦ q.IsPrime ∧ W ⊔ Ideal.span {s} ≤ q) V := hVmin'
  have hVp : V.IsPrime := hVmin.prop.1
  have hWV : W ≤ V := le_trans le_sup_left hVmin.prop.2
  have hsV : s ∈ V := hVmin.prop.2 (Ideal.mem_sup_right (Ideal.mem_span_singleton_self s))

  have hproj : ∀ (T : Finset K) f, f ∈ V → proj T f ∈ V := by
    intro T f hf
    rw [proj_apply]
    exact weightedHomogeneousComponent_mem_of_mem ℤ (wt T)
      (isHomogeneous_of_mem_minimalPrimes T (isHomogeneous_sup T hWh hs) hVmin') hf 0

  let Z := PrimeSpectrum.zeroLocus (R := MRing ι) (W : Set (MRing ι))
  let pt : (I : Ideal (MRing ι)) → I.IsPrime → W ≤ I → Z := fun I hI hWI ↦
    ⟨⟨I, hI⟩, (PrimeSpectrum.mem_zeroLocus _ _).mpr hWI⟩
  have pt_lt : ∀ (I J : Ideal (MRing ι)) hI hJ hWI hWJ, I < J → pt I hI hWI < pt J hJ hWJ :=
    fun _ _ _ _ _ _ h ↦ h
  have hPp : ∀ T : Finset K, (V.comap (proj T)).IsPrime := fun T ↦ hVp.comap _
  have hVP : ∀ T : Finset K, V ≤ V.comap (proj T) := fun T f hf ↦ hproj T f hf
  let P : Finset K → Z := fun T ↦ pt _ (hPp T) (hWV.trans (hVP T))

  have hstep : ∀ (T : Finset K) (k : K), k ∉ T → P T < P (insert k T) := by
    intro T k hk
    suffices key : V.comap (proj T) < V.comap (proj (insert k T)) from
      pt_lt _ _ (hPp T) (hPp _) (hWV.trans (hVP T)) (hWV.trans (hVP _)) key
    refine lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_
    · change proj _ f ∈ V
      rw [← proj_proj (Finset.subset_insert k T)]
      exact hproj _ _ hf
    · obtain ⟨i, hi⟩ := hVrel k
      have h1 : (X ⟨k, i⟩ : MRing ι) ∈ V.comap (proj (insert k T)) := by
        change proj _ _ ∈ V
        rw [proj_X_of_mem (Finset.mem_insert_self k T)]
        exact V.zero_mem
      rw [← h] at h1
      change proj _ _ ∈ V at h1
      rw [proj_X_of_notMem hk] at h1
      exact hi h1
  have hbot : pt W hWp le_rfl < P ∅ := by
    suffices key : W < V.comap (proj ∅) from
      pt_lt _ _ hWp (hPp ∅) le_rfl (hWV.trans (hVP ∅)) key
    refine lt_of_le_of_ne (hWV.trans (hVP ∅)) fun h ↦ hsW ?_
    rw [h]
    change proj ∅ s ∈ V
    rw [proj_empty]
    exact hsV
  have hchain : ∀ T : Finset K, ∃ l : LTSeries Z, l.last = P T ∧ l.length = T.card + 1 := by
    intro T
    induction T using Finset.induction_on with
    | empty => exact ⟨(RelSeries.singleton _ (pt W hWp le_rfl)).snoc (P ∅) hbot, RelSeries.last_snoc _ _ _, rfl⟩
    | insert k T hk ih =>
      obtain ⟨l, hl, hlen⟩ := ih
      refine ⟨l.snoc (P (insert k T)) (hl ▸ hstep T k hk), RelSeries.last_snoc _ _ _, ?_⟩
      show l.length + 1 = _
      rw [hlen, Finset.card_insert_of_notMem hk]

  have hQp : (Ideal.comap (constantCoeff : MRing ι →+* ℤ) (Ideal.span {(2 : ℤ)})).IsPrime :=
    ((Ideal.span_singleton_prime two_ne_zero).mpr Int.prime_two).comap _
  have hPQ : V.comap (proj Finset.univ) <
      Ideal.comap (constantCoeff : MRing ι →+* ℤ) (Ideal.span {(2 : ℤ)}) := by
    have hc : ∀ c : ℤ, C c ∈ V → c = 0 := fun c hc ↦ by
      have : c ∈ V.comap (C : ℤ →+* MRing ι) := hc
      rw [hhor] at this
      exact this
    refine lt_of_le_of_ne (fun f hf ↦ ?_) fun h ↦ ?_
    · change proj _ f ∈ V at hf
      rw [proj_univ] at hf
      rw [Ideal.mem_comap, hc _ hf]
      exact Ideal.zero_mem _
    · have h2 : (C 2 : MRing ι) ∈ Ideal.comap (constantCoeff : MRing ι →+* ℤ)
          (Ideal.span {(2 : ℤ)}) := by
        rw [Ideal.mem_comap, constantCoeff_C]
        exact Ideal.mem_span_singleton_self 2
      rw [← h] at h2
      change proj _ _ ∈ V at h2
      rw [proj_univ, constantCoeff_C] at h2
      exact two_ne_zero (hc 2 h2)
  let Q : Z := pt _ hQp ((hWV.trans (hVP Finset.univ)).trans hPQ.le)
  obtain ⟨l, hl, hlen⟩ := hchain Finset.univ
  have hlen' := Order.LTSeries.length_le_krullDim (l.snoc Q (by
    rw [hl]
    exact pt_lt _ _ (hPp _) hQp (hWV.trans (hVP _)) ((hWV.trans (hVP Finset.univ)).trans hPQ.le) hPQ))
  change ((l.length + 1 : ℕ) : WithBot ℕ∞) ≤ _ at hlen'
  rw [hlen, Finset.card_univ, ← ringKrullDim_quotient, hdim] at hlen'
  have : Fintype.card K + 1 + 1 ≤ 1 + Fintype.card K := by exact_mod_cast hlen'
  omega

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HeightsSet
end

