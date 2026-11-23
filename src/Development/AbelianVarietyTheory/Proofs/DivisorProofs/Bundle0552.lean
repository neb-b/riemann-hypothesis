module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSchemeOfThickenings
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0536
public import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
public import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.Bundle0002
public import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0243
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0317
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardNonempty

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowerIntegralValuationLowerBoundIffForallEmbeddi
section
noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.LatVal Polynomial IntermediateField

namespace GlobalTheory.LadicDenom

theorem norm_natCast_padicComplex (l : ℕ) [Fact l.Prime] (n : ℕ) : ‖(n : ℂ_[l])‖ = ‖(n : ℚ_[l])‖ := by
  have h : (n : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (n : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_ratCast_padicComplex (l : ℕ) [Fact l.Prime] (q : ℚ) : ‖(q : ℂ_[l])‖ = ‖(q : ℚ_[l])‖ := by
  have h : (q : ℂ_[l]) = algebraMap ℚ_[l] ℂ_[l] (q : ℚ_[l]) := by simp
  rw [h, norm_algebraMap']

theorem norm_prime_padicComplex (l : ℕ) [Fact l.Prime] : ‖(l : ℂ_[l])‖ = (l : ℝ)⁻¹ := by
  rw [norm_natCast_padicComplex, Padic.norm_p]

theorem norm_le_one_of_isIntegral {C : Type} [NormedField C] [IsUltrametricDist C] {x : C} (hx : IsIntegral ℤ x) :
    ‖x‖ ≤ 1 := by
  have h : x ∈ (NormedField.valuation (K := C)).integer :=
    (Valuation.integer.integers (NormedField.valuation (K := C))).mem_of_integral hx.tower_top
  rw [Valuation.mem_integer_iff, NormedField.valuation_apply] at h
  exact_mod_cast h

theorem not_dvd_den_of_norm_le_one (l : ℕ) [hl : Fact l.Prime] (q : ℚ) (h : ‖(q : ℚ_[l])‖ ≤ 1) : ¬ l ∣ q.den := by
  intro hd
  have hnum : ‖(q.num : ℚ_[l])‖ = 1 := by
    have hc : l.Coprime q.num.natAbs := (Nat.Prime.coprime_iff_not_dvd hl.out).2 fun hn =>
      hl.out.one_lt.ne' (Nat.eq_one_of_dvd_coprimes q.reduced hn hd)
    rcases Int.natAbs_eq q.num with e | e
    · rw [e, Int.cast_natCast]; exact Padic.norm_natCast_eq_one_iff.2 hc
    · rw [e, Int.cast_neg, Int.cast_natCast, norm_neg]; exact Padic.norm_natCast_eq_one_iff.2 hc
  have hden : ‖(q.den : ℚ_[l])‖ < 1 := by
    refine lt_of_le_of_ne ?_ fun e => ?_
    · exact_mod_cast Padic.norm_int_le_one (q.den : ℤ)
    · have := Padic.norm_natCast_eq_one_iff.1 e
      exact hl.out.one_lt.ne' (Nat.Coprime.eq_one_of_dvd this hd)
  have e : (q : ℚ_[l]) * (q.den : ℚ_[l]) = q.num := by exact_mod_cast Rat.mul_den_eq_num q
  have e2 := congrArg norm e
  rw [norm_mul, hnum] at e2
  have : ‖(q : ℚ_[l])‖ * ‖(q.den : ℚ_[l])‖ < 1 :=
    (mul_le_of_le_one_left (norm_nonneg _) h).trans_lt hden
  exact this.ne e2


set_option synthInstance.maxHeartbeats 400000 in
theorem norm_root_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (β : ℂ_[l]) (hβ : β ∈ (minpoly ℚ α).aroots ℂ_[l]) :
    ‖β‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  let φ := (algHomAdjoinIntegralEquiv ℚ hα).symm ⟨β, hβ⟩
  letI : Algebra ℚ⟮α⟯ ℂ_[l] := φ.toRingHom.toAlgebra
  haveI : Algebra.IsAlgebraic ℚ⟮α⟯ (algebraicClosure ℚ ℂ) := Algebra.IsAlgebraic.tower_top (K := ℚ) _
  let ψ : algebraicClosure ℚ ℂ →ₐ[ℚ⟮α⟯] ℂ_[l] := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  have e : ψ α = β := by
    have h1 := ψ.commutes (AdjoinSimple.gen ℚ α)
    rw [AdjoinSimple.algebraMap_gen] at h1
    rw [h1]
    exact algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hα ⟨β, hβ⟩
  rw [← e]
  exact h ψ.toRingHom

theorem coeff_norm_le_one (l : ℕ) [Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) (i : ℕ) :
    ‖(((minpoly ℚ α).coeff i : ℚ) : ℂ_[l])‖ ≤ 1 := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set P := (minpoly ℚ α).map (algebraMap ℚ ℂ_[l]) with hP
  let S := (NormedField.valuation (K := ℂ_[l])).integer
  have memS : ∀ z : ℂ_[l], z ∈ S ↔ ‖z‖ ≤ 1 := by
    intro z
    rw [Valuation.mem_integer_iff, NormedField.valuation_apply]
    exact_mod_cast Iff.rfl
  have hmon : P.Monic := (minpoly.monic hα).map _
  have hroots : ∀ β ∈ P.roots, β ∈ S := fun β hβ => (memS β).2 (norm_root_le_one l α h β hβ)
  have hc : (((minpoly ℚ α).coeff i : ℚ) : ℂ_[l]) = P.coeff i := by
    rw [hP, coeff_map, eq_ratCast]
  rw [hc, ← memS]
  by_cases hi : i ≤ P.natDegree
  · rw [coeff_eq_esymm_roots_of_card IsAlgClosed.card_roots_eq_natDegree hi, hmon.leadingCoeff, one_mul]
    refine S.mul_mem (S.pow_mem (S.neg_mem S.one_mem) _) ?_
    unfold Multiset.esymm
    refine S.multiset_sum_mem _ fun z hz => ?_
    obtain ⟨t, ht, rfl⟩ := Multiset.mem_map.1 hz
    exact S.multiset_prod_mem _ fun w hw => hroots w (Multiset.mem_of_le (Multiset.mem_powersetCard.1 ht).1 hw)
  · rw [coeff_eq_zero_of_natDegree_lt (not_le.1 hi)]
    exact S.zero_mem

theorem intAt_of_forall_norm_le_one (l : ℕ) [hl : Fact l.Prime] (α : algebraicClosure ℚ ℂ)
    (h : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], ‖lam α‖ ≤ 1) : IntAt l (α : ℂ) := by
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  have hα : IsIntegral ℚ α := (Algebra.IsAlgebraic.isAlgebraic α).isIntegral
  set p := minpoly ℚ α with hp
  have hmon : p.Monic := minpoly.monic hα
  have hden : ∀ i, ¬ l ∣ (p.coeff i).den := fun i =>
    not_dvd_den_of_norm_le_one l _ (by rw [← norm_ratCast_padicComplex]; exact coeff_norm_le_one l α h i)
  set D : ℕ := ∏ i ∈ Finset.range p.natDegree, (p.coeff i).den with hD
  have hDc : D.Coprime l := Nat.Coprime.prod_left fun i _ =>
    ((Nat.Prime.coprime_iff_not_dvd hl.out).2 (hden i)).symm
  refine ⟨D, hDc, ?_⟩
  set q := p.scaleRoots (D : ℚ) with hq
  have hql : q ∈ lifts (Int.castRingHom ℚ) := by
    rw [lifts_iff_coeff_lifts]
    intro n
    rw [hq, coeff_scaleRoots]
    rcases lt_trichotomy n p.natDegree with hn | hn | hn
    · obtain ⟨e, he⟩ : (p.coeff n).den ∣ D := Finset.dvd_prod_of_mem _ (Finset.mem_range.2 hn)
      obtain ⟨k, hk⟩ : ∃ k, p.natDegree - n = k + 1 := ⟨p.natDegree - n - 1, by omega⟩
      have h1 : p.coeff n * ((p.coeff n).den : ℚ) = (p.coeff n).num := Rat.mul_den_eq_num _
      refine ⟨(p.coeff n).num * e * D ^ k, ?_⟩
      simp only [eq_intCast, Int.cast_mul, Int.cast_pow, Int.cast_natCast]
      rw [hk, pow_succ, ← h1]
      have h2 : (D : ℚ) = (p.coeff n).den * e := by exact_mod_cast he
      rw [h2]
      ring
    · refine ⟨1, ?_⟩
      rw [hn, hmon.coeff_natDegree, Nat.sub_self, pow_zero, mul_one, map_one]
    · refine ⟨0, ?_⟩
      rw [coeff_eq_zero_of_natDegree_lt hn, zero_mul, map_zero]
  have hqm : q.Monic := by
    rw [Monic, hq, leadingCoeff_scaleRoots]; exact hmon
  obtain ⟨Q, hQ, -, hQm⟩ := lifts_and_natDegree_eq_and_monic hql hqm
  have hroot : aeval ((D : algebraicClosure ℚ ℂ) * α) q = 0 := by
    have := scaleRoots_aeval_eq_zero (r := (D : ℚ)) (minpoly.aeval ℚ α)
    simpa using this
  have hint : IsIntegral ℤ ((D : algebraicClosure ℚ ℂ) * α) := by
    refine ⟨Q, hQm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap ℚ, algebraMap_int_eq, hQ]
    exact hroot
  have := map_isIntegral_int (algebraicClosure ℚ ℂ).val.toRingHom hint
  simpa using this

theorem valGe_iff_forall_sz (l : ℕ) [hl : Fact l.Prime] (r : ℝ) (x : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.ClassZetaValuationBounds.ValGe_vp l r x ↔ ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l], Sz l lam r x := by
  have hl1 : (1 : ℝ) < l := by exact_mod_cast hl.out.one_lt
  have hl0 : (0 : ℝ) < l := by linarith
  haveI : Algebra.IsAlgebraic ℚ (algebraicClosure ℚ ℂ) := algebraicClosure.isAlgebraic ℚ ℂ
  constructor
  · intro hv lam
    obtain ⟨N, hN, hi⟩ := hv ⌈r⌉ 1 one_pos (by simpa using Int.le_ceil r)
    have hN0 : N ≠ 0 := by
      rintro rfl
      rw [Nat.coprime_zero_left] at hN
      exact hl.out.one_lt.ne' hN
    have hmem : x ∈ algebraicClosure ℚ ℂ := by
      have h1 : (N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1) ∈ algebraicClosure ℚ ℂ :=
        mem_algebraicClosure_iff.2 (hi.tower_top (A := ℚ)).isAlgebraic
      have h2 : ((N : ℂ) * (l : ℂ) ^ ⌈r⌉) ≠ 0 :=
        mul_ne_zero (Nat.cast_ne_zero.2 hN0) (zpow_ne_zero _ (Nat.cast_ne_zero.2 hl.out.ne_zero))
      have h3 : x = ((N : ℂ) * ((l : ℂ) ^ ⌈r⌉ * x ^ 1)) * ((N : ℂ) * (l : ℂ) ^ ⌈r⌉)⁻¹ := by
        rw [pow_one, ← mul_assoc, mul_right_comm, mul_inv_cancel₀ h2, one_mul]
      rw [h3]
      exact mul_mem h1 (inv_mem (mul_mem (IntermediateField.natCast_mem _ _) (zpow_mem (IntermediateField.natCast_mem _ _) _)))
    refine ⟨hmem, ?_⟩
    set t := ‖lam ⟨x, hmem⟩‖ with ht
    have key : ∀ (m : ℤ) (n : ℕ), 0 < n → r ≤ (m : ℝ) / n → t ^ n ≤ (l : ℝ) ^ m := by
      intro m n hn hmn
      obtain ⟨N, hN, hi⟩ := hv m n hn hmn
      set β : algebraicClosure ℚ ℂ := (N : algebraicClosure ℚ ℂ) * ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)
      have hiβ : IsIntegral ℤ β := by
        refine (isIntegral_algHom_iff ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) Subtype.val_injective).1 ?_
        have e : ((algebraicClosure ℚ ℂ).val.restrictScalars ℤ) β = (N : ℂ) * ((l : ℂ) ^ m * x ^ n) :=
          Complex.ext rfl rfl
        rw [e]; exact hi
      have h1 := norm_le_one_of_isIntegral (map_isIntegral_int lam hiβ)
      simp only [β, map_mul, map_pow, map_zpow₀, map_natCast, norm_mul, norm_pow, norm_zpow] at h1
      rw [norm_natCast_padicComplex, Padic.norm_natCast_eq_one_iff.2 hN.symm, norm_prime_padicComplex, one_mul,
        inv_zpow', zpow_neg, inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one] at h1
      exact h1
    by_contra hgt
    rw [not_le] at hgt
    have htp : 0 < t := (Real.rpow_pos_of_pos hl0 r).trans hgt
    have hr : r < Real.logb l t := (Real.lt_logb_iff_rpow_lt hl1 htp).2 hgt
    obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn hr
    have hq3 : (l : ℝ) ^ (q : ℝ) < t := (Real.lt_logb_iff_rpow_lt hl1 htp).1 hq2
    have hqe : (q : ℝ) = (q.num : ℝ) / (q.den : ℕ) := by exact_mod_cast (Rat.num_div_den q).symm
    have hk := key q.num q.den q.den_pos (by rw [← hqe]; exact hq1.le)
    have h4 : ((l : ℝ) ^ (q : ℝ)) ^ q.den < t ^ q.den :=
      pow_lt_pow_left₀ hq3 (Real.rpow_nonneg hl0.le _) q.den_pos.ne'
    have h5 : ((l : ℝ) ^ (q : ℝ)) ^ q.den = (l : ℝ) ^ q.num := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le, ← Real.rpow_intCast, hqe,
        div_mul_cancel₀ _ (Nat.cast_ne_zero.2 q.den_pos.ne')]
    rw [h5] at h4
    exact absurd hk (not_le.2 h4)
  · intro h
    let lam₀ : algebraicClosure ℚ ℂ →+* ℂ_[l] := (IsAlgClosed.lift : algebraicClosure ℚ ℂ →ₐ[ℚ] ℂ_[l]).toRingHom
    obtain ⟨hmem, -⟩ := h lam₀
    intro m n hn hmn
    have hmn' : r * n ≤ m := by rwa [le_div_iff₀ (Nat.cast_pos.2 hn)] at hmn
    have hb : ∀ lam : algebraicClosure ℚ ℂ →+* ℂ_[l],
        ‖lam ((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n)‖ ≤ 1 := by
      intro lam
      obtain ⟨h', hle⟩ := h lam
      rw [map_mul, map_zpow₀, map_pow, map_natCast, norm_mul, norm_zpow, norm_pow, norm_prime_padicComplex,
        inv_zpow', zpow_neg]
      have h2 : ‖lam ⟨x, hmem⟩‖ ^ n ≤ (l : ℝ) ^ m := by
        calc ‖lam ⟨x, hmem⟩‖ ^ n ≤ ((l : ℝ) ^ r) ^ n := pow_le_pow_left₀ (norm_nonneg _) hle n
          _ = (l : ℝ) ^ (r * n) := by rw [← Real.rpow_natCast, ← Real.rpow_mul hl0.le]
          _ ≤ (l : ℝ) ^ (m : ℝ) := Real.rpow_le_rpow_of_exponent_le hl1.le hmn'
          _ = (l : ℝ) ^ m := Real.rpow_intCast _ _
      rw [inv_mul_le_iff₀ (zpow_pos hl0 m), mul_one]
      exact h2
    have := intAt_of_forall_norm_le_one l _ hb
    have e : (((l : algebraicClosure ℚ ℂ) ^ m * ⟨x, hmem⟩ ^ n : algebraicClosure ℚ ℂ) : ℂ) = (l : ℂ) ^ m * x ^ n :=
      Complex.ext rfl rfl
    rwa [e] at this

end GlobalTheory.LadicDenom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullbackConeFstSndRingNilpotent
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace GlobalTheory

theorem pullbackCone_ker_fst_inf_ker_snd {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ⊓
      RingHom.ker (CommRingCat.pullbackCone f g).snd.hom = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  rw [Ideal.mem_inf, RingHom.mem_ker, RingHom.mem_ker] at hx
  rw [Ideal.mem_bot]
  exact Subtype.ext (Prod.ext hx.1 hx.2)

theorem pow_le_ker_of_le_comap {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S)
    (I : Ideal R) (J : Ideal S) (k : ℕ) (hIJ : I ≤ Ideal.comap φ J) (hJ : J ^ k = 0) :
    I ^ k ≤ RingHom.ker φ :=
  calc I ^ k ≤ (Ideal.comap φ J) ^ k := Ideal.pow_right_mono hIJ k
    _ ≤ Ideal.comap φ (J ^ k) := Ideal.le_comap_pow φ k
    _ = RingHom.ker φ := by rw [hJ, Ideal.zero_eq_bot, ← RingHom.ker_eq_comap_bot]

theorem pullbackCone_fst_snd_ring_nilpotent {A B C : CommRingCat.{0}} (f : A ⟶ C) (g : B ⟶ C) :
    Function.Surjective f.hom → IsNilpotent (RingHom.ker f.hom) → Function.Surjective g.hom →
    IsNilpotent (RingHom.ker g.hom) →
    (Function.Surjective (CommRingCat.pullbackCone f g).fst.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).fst.hom)) ∧
      (Function.Surjective (CommRingCat.pullbackCone f g).snd.hom ∧
        IsNilpotent (RingHom.ker (CommRingCat.pullbackCone f g).snd.hom)) ∧
      (Function.Surjective ((CommRingCat.pullbackCone f g).fst ≫ f).hom ∧
        IsNilpotent (RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom)) := by
  rintro hf ⟨n, hn⟩ hg ⟨m, hm⟩
  have hbot := pullbackCone_ker_fst_inf_ker_snd f g
  have hcomm : ∀ x : (CommRingCat.pullbackCone f g).pt,
      f.hom ((CommRingCat.pullbackCone f g).fst.hom x) =
        g.hom ((CommRingCat.pullbackCone f g).snd.hom x) := fun x => x.2
  have k1 : RingHom.ker (CommRingCat.pullbackCone f g).fst.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm, hx, map_zero]
  have k2 : RingHom.ker (CommRingCat.pullbackCone f g).snd.hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, hcomm, hx, map_zero]
  have k3 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).fst.hom (RingHom.ker f.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker]
    simpa using hx
  have k4 : RingHom.ker ((CommRingCat.pullbackCone f g).fst ≫ f).hom ≤
      Ideal.comap (CommRingCat.pullbackCone f g).snd.hom (RingHom.ker g.hom) := by
    intro x hx
    rw [RingHom.mem_ker] at hx
    rw [Ideal.mem_comap, RingHom.mem_ker, ← hcomm]
    simpa using hx
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · intro a
    obtain ⟨b, hb⟩ := hg (f.hom a)
    exact ⟨⟨(a, b), hb.symm⟩, rfl⟩
  · refine ⟨m + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf inf_le_right ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ m k1 hm)))
  · intro b
    obtain ⟨a, ha⟩ := hf (g.hom b)
    exact ⟨⟨(a, b), ha⟩, rfl⟩
  · refine ⟨n + 1, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_succ]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k2 hn)) inf_le_right)
  · intro c
    obtain ⟨a, ha⟩ := hf c
    obtain ⟨b, hb⟩ := hg c
    exact ⟨⟨(a, b), ha.trans hb.symm⟩, ha⟩
  · refine ⟨n + m, ?_⟩
    rw [Ideal.zero_eq_bot, eq_bot_iff, ← hbot, pow_add]
    exact (Ideal.mul_le_inf).trans
      (le_inf ((inf_le_left).trans (pow_le_ker_of_le_comap _ _ _ n k3 hn))
        ((inf_le_right).trans (pow_le_ker_of_le_comap _ _ _ m k4 hm)))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionIsAlgebraicWeierstrassTorsion
section
open scoped UpperHalfPlane MatrixGroups Matrix ModularForm ComplexConjugate
open GlobalTheory.QFam GlobalTheory.WpFam

namespace GlobalTheory.WpFam

theorem isAlgebraic_of_isIntegral_natCast_mul (n : ℕ) (hn : n ≠ 0) (z : ℂ)
    (h : IsIntegral ℤ ((n : ℂ) * z)) : IsAlgebraic ℚ z := by
  have h1 : IsIntegral ℚ ((n : ℂ) * z) := h.tower_top
  have h2 : IsIntegral ℚ (algebraMap ℚ ℂ ((n : ℚ)⁻¹)) := isIntegral_algebraMap
  have h3 := h2.mul h1
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
  have : algebraMap ℚ ℂ ((n : ℚ)⁻¹) * ((n : ℂ) * z) = z := by
    rw [map_inv₀, map_natCast, ← mul_assoc, inv_mul_cancel₀ hn', one_mul]
  rw [this] at h3
  exact h3.isAlgebraic

theorem qAll_isAlgebraic_torsion : ∀ (N : ℕ) [NeZero N] (x : Fin 2 → ZMod N),
    QAll (IsAlgebraic ℚ) N (wp N x) ∧ QAll (IsAlgebraic ℚ) N (wpd N x) ∧
      (x ≠ 0 → QAll (IsAlgebraic ℚ) N (wB N x)) := by
  intro N _ x
  have hN : N ≠ 0 := NeZero.ne N
  have hx : N • x = 0 := by
    funext i
    simp [nsmul_eq_mul]
  have hc := fun k => _root_.GlobalTheory.WpFam.isIntegral_coefficients N N x k (Nat.pos_of_ne_zero hN) hx
  refine ⟨⟨cP N x, _root_.GlobalTheory.WpFam.ExpP.main N x, fun k => ?_⟩, ⟨cD N x, _root_.GlobalTheory.WpFam.DerivExpansion.main N x, fun k => ?_⟩,
    fun h0 => ⟨cB N x, _root_.GlobalTheory.WpFam.ExpansionB.main N x h0, fun k => ?_⟩⟩
  · refine isAlgebraic_of_isIntegral_natCast_mul (12 * N ^ 2) (by positivity) _ ?_
    have := (hc k).2.2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 3) (by positivity) _ ?_
    have := (hc k).2.1
    push_cast
    exact this
  · refine isAlgebraic_of_isIntegral_natCast_mul (N ^ 2) (by positivity) _ ?_
    have := (hc k).1
    push_cast
    exact this

end GlobalTheory.WpFam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrictCompatibleFamilyToIntersectionsBijective
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.AbCoh
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CechPoset

set_option autoImplicit false

noncomputable section

open Opposite

namespace GlobalTheory.CechPoset

section Bij

variable {R : Type} [CommRing R] {X : Scheme.{0}}

theorem sec_res_self (s : X ⟶ Sp R) {U : X.Opens} (h : U ≤ U) (c : Sec s U) : Sec.res s h c = c :=
  congrArg (fun q ↦ q.hom c) (X.presheaf.map_id (op U))

theorem ker_res (s : X ⟶ Sp R) (g : LinearMap.ker (d0 (OAff s))) {U V : X.affineOpens}
    (h : V.1 ≤ U.1) : g.1 (op V) = Sec.res s h (g.1 (op U)) := by
  have := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (op U)) (op V))
    (homOfLE (show V ≤ U from h)).op
  rw [amitsur_d0_apply] at this
  exact sub_eq_zero.1 this

variable {κ : Type} [LinearOrder κ]

theorem kerF_res (s : X ⟶ Sp R) (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i))
    (g : LinearMap.ker (d0 (covF s D hD))) {I J : Finset κ} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) {U : X.Opens} (hU : U ≤ ⨅ k ∈ J, D k) (hU' : U ≤ ⨅ k ∈ I, D k) :
    Sec.res s hU' (g.1 (ne I hI)) = Sec.res s hU (g.1 (ne J hJ)) := by
  have e := congrFun (congrFun (congrFun (LinearMap.mem_ker.1 g.2) (ne I hI)) (ne J hJ))
    (homOf (a := ne I hI) (b := ne J hJ) h)
  rw [amitsur_d0_apply] at e
  have e' : g.1 (ne J hJ) = Sec.res s (show (⨅ k ∈ J, D k) ≤ ⨅ k ∈ I, D k from
      biInf_mono fun _ hk ↦ h hk) (g.1 (ne I hI)) := sub_eq_zero.1 e
  rw [e']
  exact Sec.res_res s _ hU _

end Bij

theorem restrictCompatibleFamilyToIntersections_bijective {R : Type} [CommRing R] {X : Scheme.{0}} (s : X ⟶ Sp R) {κ : Type}
    [LinearOrder κ] [Fintype κ] (D : κ → X.Opens)
    (hD : ∀ I : Finset κ, I.Nonempty → IsAffineOpen (⨅ i ∈ I, D i)) :
    ⨆ i, D i = ⊤ → Function.Bijective (res0 s D hD) := by
  intro hcov
  have hle1 : ∀ i : κ, D i ≤ ⨅ k ∈ ({i} : Finset κ), D k := fun i ↦
    le_iInf₂ fun k hk ↦ by rw [Finset.mem_singleton.1 hk]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro g hg
    have h0 : ∀ i : κ, g.1 (op (cov D hD (OrderDual.toDual ⟨{i}, Finset.singleton_nonempty i⟩))) = 0 :=
      fun i ↦ congrFun (congrArg Subtype.val hg) (ne {i} (Finset.singleton_nonempty i))
    apply Subtype.ext
    funext V
    show g.1 V = 0
    let Idx := {p : X.affineOpens × κ // p.1.1 ≤ V.unop.1 ⊓ D p.2}
    refine TopCat.Sheaf.eq_of_locally_eq' X.sheaf (fun j : Idx ↦ j.1.1.1) V.unop.1
      (fun j ↦ homOfLE (j.2.trans inf_le_left)) ?_ _ _ ?_
    · intro x hx
      have hx' : x ∈ ⨆ i, D i := by rw [hcov]; trivial
      obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hx'
      obtain ⟨W, hWB, hxW, hWle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens)
        (show x ∈ V.unop.1 ⊓ D i from ⟨hx, hi⟩)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨(⟨W, hWB⟩, i), hWle⟩, hxW⟩
    · intro j
      have hW : j.1.1.1 ≤ V.unop.1 := j.2.trans inf_le_left
      have hWi : j.1.1.1 ≤ (cov D hD (OrderDual.toDual ⟨{j.1.2}, Finset.singleton_nonempty _⟩)).1 :=
        (j.2.trans inf_le_right).trans (hle1 j.1.2)
      have e1 := ker_res s g (U := V.unop) (V := j.1.1) hW
      have e2 := ker_res s g (V := j.1.1) hWi
      rw [h0, map_zero] at e2
      show Sec.res s hW (g.1 V) = Sec.res s hW 0
      rw [map_zero, ← e1, e2]
  · intro g'
    let sf : ∀ i : κ, Sec s (D i) := fun i ↦ Sec.res s (hle1 i) (g'.1 (ne {i} (Finset.singleton_nonempty i)))
    have hcomp : TopCat.Presheaf.IsCompatible X.sheaf.1 D sf := by
      intro i j
      show Sec.res s inf_le_left (sf i) = Sec.res s inf_le_right (sf j)
      have hij : D i ⊓ D j ≤ ⨅ k ∈ ({i, j} : Finset κ), D k := le_iInf₂ fun k hk ↦ by
        obtain hk | hk := Finset.mem_insert.1 hk
        · rw [hk]; exact inf_le_left
        · rw [Finset.mem_singleton.1 hk]; exact inf_le_right
      exact (Sec.res_res s (hle1 i) inf_le_left _).symm.trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty i) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_left.trans (hle1 i))).trans
        ((kerF_res s D hD g' (Finset.singleton_nonempty j) (Finset.insert_nonempty _ _)
          (by simp) hij (inf_le_right.trans (hle1 j))).symm.trans
        (Sec.res_res s (hle1 j) inf_le_right _)))
    obtain ⟨G, hG, -⟩ := X.sheaf.existsUnique_gluing' D ⊤ (fun i ↦ homOfLE le_top) hcov.symm.le sf hcomp
    let g : LinearMap.ker (d0 (OAff s)) := ⟨fun V ↦ Sec.res s le_top (G : Γ(X, ⊤)), by
      rw [LinearMap.mem_ker]
      funext U U' φ
      rw [amitsur_d0_apply]
      show Sec.res s le_top (G : Γ(X, ⊤)) - Sec.res s _ (Sec.res s le_top (G : Γ(X, ⊤))) = 0
      exact sub_eq_zero.2 (Sec.res_res s _ _ _)⟩
    refine ⟨g, Subtype.ext (funext fun I ↦ ?_)⟩
    show Sec.res s le_top (G : Γ(X, ⊤)) = g'.1 I
    have hm := mn_mem I
    have hi : (cov D hD I.unop).1 ≤ D (mn I) := iInf₂_le (mn I) hm
    have hGi : Sec.res s (le_top : D (mn I) ≤ ⊤) (G : Γ(X, ⊤)) = sf (mn I) := hG (mn I)
    refine (Sec.res_res s le_top hi _).trans ?_
    rw [hGi]
    exact (Sec.res_res s (hle1 (mn I)) hi _).symm.trans
      ((kerF_res s D hD g' (Finset.singleton_nonempty (mn I)) (sub_nonempty I)
        (Finset.singleton_subset_iff.2 hm) le_rfl _).trans (sec_res_self s _ _))

end GlobalTheory.CechPoset
end
end

