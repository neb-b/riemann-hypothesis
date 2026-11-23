module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0019
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0023
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0017
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0022
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0001
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0021
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.Intersections.IsLocalizationConeVarMap
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.Intersections.TableDegreeThreeBase
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0012
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0015

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisAlt
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityDenominator.isMultiHomog_C {K : Type*} [Fintype K] {ι : K → Type*} [∀ k, Fintype (ι k)] (n : ℤ) :
    IsMultiHomog (C n : MRing ι) 0 := by
  intro m hm k
  rw [C_apply] at hm
  have : m = 0 := by simpa using support_monomial_subset hm
  simp [this]

theorem RegularityDenominator.proof (hD : RegularityDivisorSupportClosed.Statement) (hPow : LocRingPow.Statement) :
    RegularityDenominator.Statement := by
  intro K _ ι _ P x hP
  have hPp : P.IsPrime := hP.2.1.1
  have hFL : (x : FractionRing (MRing ι ⧸ P)) ∈ locRing P P := by
    have hx := x.2
    unfold funField at hx
    unfold locRing
    refine Subring.closure_mono ?_ hx
    rintro _ ⟨u, v, a, hv, hu, hva, rfl⟩
    refine ⟨u, v, a, hv, fun h => ?_, hu, hva, rfl⟩
    have h0 : Ideal.Quotient.mk P v = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr h
    exact zero_notMem_nonZeroDivisors (h0 ▸ hv)
  obtain ⟨u, v, a, hu, hva, hvP, hxv⟩ := LocRingFrac.proof K ι P P hPp hPp le_rfl _ hFL

  have key : ∀ W ∈ divSupp P v, ∃ m : ℤ, m ≠ 0 ∧
      (x : FractionRing (MRing ι ⧸ P)) * (m : FractionRing (MRing ι ⧸ P)) ∈ locRing P W := by
    intro W hW
    obtain ⟨hWc, hPW, -⟩ := (hD K ι P v a W hP hva hvP).1 hW
    have hWp : W.IsPrime := hWc.1.1
    have hvert : W.comap (C : ℤ →+* MRing ι) ≠ ⊥ := fun hh =>
      arithVarZero K ι W ⟨hP.1, hWc.1, hh, by rw [zero_add]; exact hWc.2⟩
    obtain ⟨n, hnW, hn0⟩ := (Submodule.ne_bot_iff _).mp hvert
    choose c hc using hW.2
    set t : MRing ι := ∏ k, (X ⟨k, c k⟩ : MRing ι) ^ a k
    have ht : IsMultiHomog t a := AvoidRing.isMultiHomog_coordProd c a
    have htW : t ∉ W := AvoidRing.coordProd_not_mem hWp c hc a
    have ht0 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ≠ 0 := by
      rw [Ne, IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem]
      exact fun h => htW (hPW h)
    have h1W : (1 : MRing ι) ∉ W := fun h => hWp.ne_top ((Ideal.eq_top_iff_one _).mpr h)
    obtain ⟨N, z, hz, hNz⟩ := hPow K ι P v t a W _ (C n) 1 0 (n : FractionRing (MRing ι ⧸ P)) hPp hP.2.1.2.1 hva
      hvP hW ht htW (div_mul_cancel₀ _ ht0) (RegularityDenominator.isMultiHomog_C n) AvoidRing.isMultiHomog_one hnW h1W
      (by rw [map_one, map_one, mul_one, eq_intCast C n, map_intCast, map_intCast])
    refine ⟨n ^ N, pow_ne_zero _ hn0, ?_⟩
    have hut : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P u) /
        algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P t) ∈ locRing P W :=
      frac_mem_locRing hPW hu ht htW (div_mul_cancel₀ _ ht0)
    rw [Int.cast_pow, hNz, ← mul_assoc, mul_div_assoc', hxv]
    exact mul_mem hut hz
  classical
  have hfin := divSupp_finite P v
  let mW : Ideal (MRing ι) → ℤ := fun W => if h : W ∈ divSupp P v then (key W h).choose else 1
  let M : ℤ := ∏ W ∈ hfin.toFinset, mW W
  have hM0 : M ≠ 0 := Finset.prod_ne_zero_iff.mpr fun W hW => by
    have hW' := hfin.mem_toFinset.mp hW
    simp only [mW, dif_pos hW']
    exact (key W hW').choose_spec.1
  refine ⟨(M : funField P), fun h => hM0 ?_, fun W hWc hPW => ⟨?_, ?_⟩⟩
  · have h' : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = 0 := by rw [h]; rfl
    have h2 : algebraMap (MRing ι ⧸ P) (FractionRing (MRing ι ⧸ P)) (Ideal.Quotient.mk P (C M)) = 0 := by
      rw [eq_intCast C M, map_intCast, map_intCast]
      simp at h'
      exact h'
    rw [IsFractionRing.to_map_eq_zero_iff, Ideal.Quotient.eq_zero_iff_mem] at h2
    have h3 : M ∈ P.comap (C : ℤ →+* MRing ι) := h2
    rw [hP.2.2.1] at h3
    exact Ideal.mem_bot.mp h3
  · have hc : ((M : funField P) : FractionRing (MRing ι ⧸ P)) = (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    exact intCast_mem (locRing P W) M
  · have hc : ((x * (M : funField P) : funField P) : FractionRing (MRing ι ⧸ P)) =
        (x : FractionRing (MRing ι ⧸ P)) * (M : FractionRing (MRing ι ⧸ P)) := by simp
    rw [hc]
    by_cases hvW : v ∈ W
    · have hW : W ∈ divSupp P v := (hD K ι P v a W hP hva hvP).2 ⟨hWc, hPW, hvW⟩
      obtain ⟨r, hr⟩ := Finset.dvd_prod_of_mem mW (hfin.mem_toFinset.mpr hW)
      have hm := (key W hW).choose_spec.2
      rw [show M = mW W * r from hr, Int.cast_mul, ← mul_assoc]
      simp only [mW, dif_pos hW]
      exact mul_mem hm (intCast_mem _ r)
    · exact mul_mem (frac_mem_locRing hPW hu hva hvW hxv) (intCast_mem _ M)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section


set_option maxHeartbeats 1000000 in
theorem RegularityLocal.proof (hO : RegularityOrder.Statement) (hE : RegularityMaximalSpectrum.Statement) :
    RegularityLocal.Statement := by
  classical
  intro K _ ι _ P b hP hb
  have : P.IsPrime := hP.2.1.1
  obtain ⟨e, he⟩ := hE K ι P hP
  obtain ⟨hfree, hfinite, -⟩ := hO K ι P hP
  let φ : regRing P →+* FractionRing (MRing ι ⧸ P) := (funField P).subtype.comp (regRing P).subtype
  have hφ : Function.Injective φ := Subtype.val_injective.comp Subtype.val_injective
  let ψ : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, regRing P →+* locRing P W.1 :=
    fun W => φ.codRestrict (locRing P W.1) fun x => x.2 W.1 W.2.1 W.2.2
  have hcard : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W},
      locIdeal P W.1 (φ b) = Ideal.span {ψ W b} := fun W => locIdeal_eq_span (b.2 W.1 W.2.1 W.2.2)
  have hloc : ∀ W, @IsLocalization (regRing P) _ (e W).asIdeal.primeCompl (locRing P W.1) _ (ψ W).toAlgebra :=
    fun W => by
      let _ := (ψ W).toAlgebra
      have := (e W).isMaximal
      have hL : ∀ x : regRing P, ((algebraMap (regRing P) (locRing P W.1) x : locRing P W.1) : FractionRing (MRing ι ⧸ P)) = φ x := fun _ => rfl
      refine (isLocalization_iff (e W).asIdeal.primeCompl (locRing P W.1)).2 ⟨?_, ?_, ?_⟩
      · rintro ⟨s, hs⟩
        have hs0 : φ s ≠ 0 := fun h0 => hs (by rw [(map_eq_zero_iff φ hφ).1 h0]; exact (e W).asIdeal.zero_mem)
        refine IsUnit.of_mul_eq_one ⟨(φ s)⁻¹, (he W _).2 ⟨1, s, hs, by change (φ s)⁻¹ * φ s = φ 1; rw [map_one, inv_mul_cancel₀ hs0]⟩⟩ ?_
        apply Subtype.ext
        simp only [Subring.coe_mul, hL, Subring.coe_one]
        exact mul_inv_cancel₀ hs0
      · intro z
        obtain ⟨x, s, hs, hxs⟩ := (he W z).1 z.2
        change (z : FractionRing (MRing ι ⧸ P)) * φ s = φ x at hxs
        exact ⟨⟨x, ⟨s, hs⟩⟩, Subtype.ext (by simp only [Subring.coe_mul, hL]; exact hxs)⟩
      · intro x y hxy
        have h1 := congrArg Subtype.val hxy
        rw [hL, hL] at h1
        exact ⟨1, by rw [hφ h1]⟩

  have hone : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∉ (e W).asIdeal →
      Nat.card (locRing P W.1 ⧸ locIdeal P W.1 (φ b)) = 1 := fun W hbW => by
    let _ := (ψ W).toAlgebra
    have := hloc W
    have hu : IsUnit (ψ W b) :=
      IsLocalization.map_units (M := (e W).asIdeal.primeCompl) (locRing P W.1) ⟨b, hbW⟩
    rw [hcard, Ideal.span_singleton_eq_top.2 hu]
    exact Nat.card_eq_one_iff_unique.2 ⟨Ideal.Quotient.subsingleton_iff.2 rfl, ⟨0⟩⟩

  set I : Ideal (regRing P) := Ideal.span {b} with hI
  have : Finite (regRing P ⧸ I) :=
    Ideal.finiteQuotientOfFreeOfNeBot I (by rwa [hI, Ne, Ideal.span_singleton_eq_bot])
  have : Fintype (PrimeSpectrum (regRing P ⧸ I)) := by
    set_option synthInstance.maxHeartbeats 200000 in
      exact Fintype.ofFinite _
  let m : PrimeSpectrum (regRing P ⧸ I) → MaximalSpectrum (regRing P) := fun p =>
    ⟨p.asIdeal.comap (Ideal.Quotient.mk I),
      Ideal.comap_isMaximal_of_surjective _ Ideal.Quotient.mk_surjective (K := p.asIdeal)⟩
  let g : PrimeSpectrum (regRing P ⧸ I) → {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W} := fun p => e.symm (m p)
  have heg : ∀ p, (e (g p)).asIdeal = p.asIdeal.comap (Ideal.Quotient.mk I) := fun p =>
    congrArg MaximalSpectrum.asIdeal (e.apply_symm_apply (m p))
  have hg : Function.Injective g := fun p q hpq => by
    have h1 := congrArg (fun W => (e W).asIdeal) hpq
    simp only [heg] at h1
    exact PrimeSpectrum.ext (Ideal.comap_injective_of_surjective _ Ideal.Quotient.mk_surjective h1)
  clear_value g m

  have hgp : ∀ p : PrimeSpectrum (regRing P ⧸ I),
      Nat.card (locRing P (g p).1 ⧸ locIdeal P (g p).1 (φ b)) = Nat.card (Localization.AtPrime p.asIdeal) :=
    fun p => by
      have := (e (g p)).isMaximal
      rw [hcard]
      exact card_quot_span_eq_card_localization (ψ (g p)) b (e (g p)).asIdeal p.asIdeal (heg p) (hloc (g p))

  have hsupp : ∀ W : {W : Ideal (MRing ι) // IsClosedPt W ∧ P ≤ W}, b ∈ (e W).asIdeal → ∃ p, g p = W :=
    fun W hbW => by
      have := (e W).isMaximal
      have hker : RingHom.ker (Ideal.Quotient.mk I) ≤ (e W).asIdeal := by
        rw [Ideal.mk_ker, hI, Ideal.span_le, Set.singleton_subset_iff]
        exact hbW
      refine ⟨⟨(e W).asIdeal.map (Ideal.Quotient.mk I),
        Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective hker⟩, ?_⟩
      apply e.injective
      apply MaximalSpectrum.ext
      rw [heg, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, sup_eq_left,
        ← RingHom.ker_eq_comap_bot]
      exact hker
  have hfin : {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W ∧ Nat.card (locRing P W ⧸ locIdeal P W (φ b)) ≠ 1} ⊆
      Set.range (fun p => (g p).1) := by
    rintro W ⟨h1, h2, h3⟩
    obtain ⟨p, hp⟩ := hsupp ⟨W, h1, h2⟩ (by_contra fun hn => h3 (hone ⟨W, h1, h2⟩ hn))
    exact ⟨p, congrArg Subtype.val hp⟩
  refine ⟨(Set.finite_range _).subset hfin, ?_⟩

  refine (finsum_mem_eq_sum_of_injective {W : Ideal (MRing ι) | IsClosedPt W ∧ P ≤ W}
    (fun W => Real.log (Nat.card (locRing P W ⧸ locIdeal P W (φ b)))) (fun p => (g p).1)
    (Subtype.val_injective.comp hg) (fun p => (g p).2)
    fun W hW h0 => hfin ⟨hW.1, hW.2, fun h1 => h0 (by rw [h1, Nat.cast_one, Real.log_one])⟩).trans ?_
  rw [log_card_eq_sum_log_card_localization (regRing P ⧸ I)]
  exact Finset.sum_congr rfl fun p _ => congrArg (fun n : ℕ => Real.log n) (hgp p)

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisSide
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

theorem RegularityFormula.proof (hN : RegularityFunctionFieldNumber.Statement) (hO : RegularityOrder.Statement)
    (hL : RegularityLocal.Statement) : RegularityFormula.Statement := by
  classical
  intro K _ ι _ P b hP hb hbW
  obtain ⟨hF, hNF⟩ := hN K ι P hP
  let _ := hF.toField
  have := hNF
  obtain ⟨hfree, hfin, hrank⟩ := hO K ι P hP
  let b' : regRing P := ⟨b, hbW⟩
  have hb' : b' ≠ 0 := fun h => hb (congrArg Subtype.val h)
  obtain ⟨hfs, hsum⟩ := hL K ι P b' hP hb'
  refine ⟨hfs, hsum.trans ?_⟩
  have hI := (ReciprocityTheory.ChartRestriction.G.AI.index_thm (funField P) (regRing P) hfree hfin (hrank hF) b' hb').2
  exact hI.trans (finsum_eq_sum_of_fintype _).symm

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsBisTer
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo IsLocalRing

noncomputable section


set_option maxHeartbeats 400000 in
theorem regularityLocalFlat_holds.proof : regularityLocalFlat_holds.Statement := by
  intro K _ ι _ P W hP hW hPW
  have := hP.1
  have := hW.1
  choose v hv using hW.2.2
  have hA := regularityLocalFlat_holds.isLocalRing (P := P) (W := W) hPW
  have hloc := regularityLocalFlat_holds.isLocalization_coneVarMap hPW hP.2.1 hW.2.1 v hv
  let _ := (regularityLocalFlat_holds.coneVarMap P W hPW v).toRingHom.toAlgebra
  have := regularityLocalFlat_holds.isPrime_map_C K (maximalIdeal (locRing P W))
  have : IsScalarTower (locRing P W) (MvPolynomial K (locRing P W)) (coneLocRing P W hPW) :=
    IsScalarTower.of_algebraMap_eq fun x => ((regularityLocalFlat_holds.coneVarMap P W hPW v).commutes x).symm
  have hR : IsLocalRing (coneLocRing P W hPW) :=
    IsLocalization.AtPrime.isLocalRing (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
  refine ⟨hA, hR, ?_, ?_⟩
  · have := IsLocalization.flat (coneLocRing P W hPW)
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _)).primeCompl
    have : Module.Free (locRing P W) (MvPolynomial K (locRing P W)) :=
      Module.Free.of_basis (MvPolynomial.basisMonomials K (locRing P W))
    have : Module.Flat (locRing P W) (MvPolynomial K (locRing P W)) := Module.Flat.of_free
    exact Module.Flat.trans _ (MvPolynomial K (locRing P W)) _
  · rw [← IsLocalization.AtPrime.map_eq_maximalIdeal
      ((maximalIdeal (locRing P W)).map (C : locRing P W →+* MvPolynomial K _))
      (coneLocRing P W hPW), Ideal.map_map, ← MvPolynomial.algebraMap_eq,
      ← IsScalarTower.algebraMap_eq]

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.ImportsMoreExtra
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

def RegularityRelativeClosedPoint.Statement : Prop :=
  ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P W : Ideal (MRing ι)),
    IsArithVar P 1 → IsMultiProjPrime W → P ≤ W → W ≠ P → IsClosedPt W

end

end GroundTheory.Heights₂.Heights.Inter
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.IsHorizontalSpanXb
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 IndefiniteRowSideFullHecke.Inter

def ArithmeticIntersectionHorizontal.Statement : Prop :=
  ∀ (I : AllFam), I.IsFamily → ∀ n : ℕ, GenDegAt I n →
    ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)]
      (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)]
      (κ : K → K') (v : (Σ k, ι k) → (Σ k', ι' k')) (P' : Ideal (MRing ι'))
      (L : Fin n → HermLine ι) (L' : Fin n → HermLine ι') (s : MRing ι) (α : K → ℕ) (W' : Ideal (MRing ι')),
      IsBlockMap κ v → IsArithVar P' (n + 1) → IsArithVar (imageZ v P') (n + 1) →
      (∀ j, IsSmoothHerm (L j)) → (∀ j, IsPullHerm κ v (L j) (L' j)) →
      IsMultiHomog s α → s ∉ imageZ v P' → W' ∈ divSupp P' (rename v s) → IsHorizontal W' →
      (imageZ v W' ∈ divSupp (imageZ v P') s ∧
          ∀ (G' : GenFibre v W') (J' : IFamily G'.Φ (fibreIdx ι' κ)), IsFieldIntersection J' →
            I K' ι' W' n L' = (J' (fibreIdeal κ G') 0 Fin.elim0 : ℝ) * I K ι (imageZ v W') n L) ∨
        (imageZ v W' ∉ divSupp (imageZ v P') s ∧ I K' ι' W' n L' = 0)

section Inhabitants

end Inhabitants

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.MixedDiscEqZeroOfMulVec
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.Inter

open MvPolynomial Matrix Filter Topology ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I4

theorem mixedDisc_eq_zero_of_mulVec {D : ℕ} {A : Fin D → Matrix (Fin D) (Fin D) ℂ} {u : Fin D → ℂ} (hu : u ≠ 0)
    (hA : ∀ k, A k *ᵥ u = 0) : mixedDisc A = 0 := by
  unfold mixedDisc
  rw [Finset.sum_eq_zero, mul_zero]
  intro S _
  have hS : (∑ k ∈ S, A k) *ᵥ u = 0 :=
    Finset.sum_induction _ (fun M => M *ᵥ u = 0) (fun M N hM hN => by rw [add_mulVec, hM, hN, add_zero])
      (zero_mulVec u) fun k _ => hA k
  rw [Matrix.exists_mulVec_eq_zero_iff.mp ⟨u, hu, hS⟩, mul_zero]

theorem pointForm_holds.maDensity_eq_zero (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement)
    {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]
    {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)]
    {κ : K → K'} {v : (Σ k, ι k) → (Σ k', ι' k')} {P' : Ideal (MRing ι')} {d n : ℕ}
    {L : Fin n → HermLine ι} {L' : Fin n → HermLine ι'} (hv : IsBlockMap κ v)
    (hQ : IsArithVar (imageZ v P') d) (hdn : d < n + 1) (hL : ∀ j, IsSmoothHerm (L j))
    (hLL : ∀ j, IsPullHerm κ v (L j) (L' j))
    {Ψ : (((k : K') → ι' k) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ)} {y : Fin n → ℂ} {w : ((k : K') → ι' k) → ℂ}
    {γ : (Fin n → ℂ) → (Σ k', ι' k') → ℂ} (hγ : IsSheet P' Ψ y w γ) :
    maDensity (fun j y' => Real.log ((L' j).h (γ y'))) y = 0 := by
  set F : (Fin n → ℂ) → (Σ k, ι k) → ℂ := fun y' p => γ y' (v p) with hF
  have hγa : AnalyticAt ℂ γ y := sheet_analyticAt osgood hγ
  have hFa : AnalyticAt ℂ F y := analyticAt_pi_iff.mpr fun p => analyticAt_coord hγa (v p)
  have hFy : ∀ k, ∃ i, F y ⟨k, i⟩ ≠ 0 := blocks_ne_zero_restrict hv hγ.2.self_of_nhds.2.1.1
  have hFQ : ∀ᶠ y' in 𝓝 y, F y' ∈ mcPts (imageZ v P') := by
    filter_upwards [hγ.2] with y' h
    refine ⟨blocks_ne_zero_restrict hv h.2.1.1, fun f hf => ?_⟩
    have h0 := h.2.1.2 _ (Ideal.mem_comap.mp hf)
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, map_rename, eval_rename] at h0
    exact h0
  obtain ⟨x, hx, c, hxc⟩ := hR K ι (imageZ v P') d n F y hQ (by omega) hFa hFQ
  have hpot : ∀ j, (fun y' => Real.log ((L' j).h (γ y'))) = fun y' => Real.log ((L j).h (F y')) :=
    fun j => funext fun y' => by rw [(hLL j).2]
  simp only [maDensity, hpot]
  rw [mixedDisc_eq_zero_of_mulVec (u := star x) (star_ne_zero.mpr hx)
    fun j => hE K ι (L j) n F y x c (hL j) hFa hFy hxc]
  simp

theorem pointForm_holds.proof (hR : pointFormRank_holds.Statement) (hE : pointFormEuler_holds.Statement) : pointForm_holds.Statement := by
  intro K _ ι _ K' _ ι' _ κ v P' d n L L' g hv _ hQ hdn hL hLL
  classical
  unfold ptsIntegral
  split_ifs with hΨ
  · unfold ptsIntegralAt
    have h0 : ∀ y w, sheetDensity P' hΨ.choose (fun j z => Real.log ((L' j).h z)) g y w = 0 := by
      intro y w
      unfold sheetDensity
      split_ifs with hγ
      · exact mul_eq_zero_of_right _ (pointForm_holds.maDensity_eq_zero hR hE hv hQ hdn hL hLL hγ.choose_spec)
      · rfl
    simp [h0]
  · rfl

end GroundTheory.Heights₂.Heights.Inter
end
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.Intersections.PFlagMinorsTrdeg
section
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

open MvPolynomial

section

variable (F : Type) [Field F] (n : ℕ)

abbrev PivotIdx := Σ a : Fin (n - 1), {b : Fin n // (a : ℕ) ≤ b}

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter
end
end

