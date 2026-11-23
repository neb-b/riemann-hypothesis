module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.GdEndOf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.LocalConditionRankThreeEvenLevel
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0014
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0064
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.AutEnd2
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0067
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.AutomorphyDescent.AutNewformW

@[expose] public section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
attribute [-instance] UpperTheory.V.Pr.IsCD.toIsDiscreteValuationRing
open NumberField IsLocalRing Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.GalOfCusp UpperTheory.V.HV UpperTheory.V.U3 UpperTheory.V.Aut UpperTheory.V.Pr UpperTheory.V
open UpperTheory.V.Z.Win
open Formalism.GaloisCohomology UpperTheory.V.Base in
theorem UpperTheory.V.Z.Win.Dn.gdEnd_of_frame_linkedEnd_downCsdK_descent (H : _root_.UpperTheory.V.Af.HypothesesH') (h3 : Dn.Loc3) (hK3 : Dn.LocalConditionRankThreeEvenLevel) (hPot : Dn.PotTwo) (hIne : Dn.Ine2) :
    GdFrameEx → _root_.UpperTheory.V.Z.Sym.Pl.LinkedEndEAlt → _root_.UpperTheory.V.Z.Win.Dn.DownCsdKAlt → RankTwoAutomorphyDescendsFromAbelianCMToRat → _root_.UpperTheory.V.Z.Win.RR.AutNewformA → Sd.TwC → Sd.AlgCyc → _root_.UpperTheory.V.Pr.GdEndAlt := by
  intro hF hL hD hQ hN hT hC Ω _ _ _ K _ _ _ aK l hl c N _ e ψ D ι B hB
  have hσ : Sd.IsCC D.cc := D.conj
  haveI : IsLocalHom (algebraMap ℤ_[l] c.O) := (dvrFacts l c.O).2.2.1
  haveI : CharP (ResidueField c.O) l := by
    rw [CharP.charP_iff_prime_eq_zero hl.out, ← map_natCast (residue c.O), residue_eq_zero_iff,
      mem_maximalIdeal, mem_nonunits_iff, ← map_natCast (algebraMap ℤ_[l] c.O)]
    intro hu
    exact PadicInt.prime_p.not_unit (isUnit_of_map_unit _ _ hu)
  obtain ⟨L, _, _, _, _, g₁, Φ, C₀, ⟨k⟩, ok, big, sc⟩ := hF Ω K l c N e ψ D B hB
  have hσ' : IsConjOm D.cc.toRingEquiv := hσ
  have hsq : D.cc * D.cc = 1 := by
    obtain ⟨j, hj⟩ := hσ'
    exact AlgEquiv.ext fun x => j.injective (by
      have h1 : j (D.cc (D.cc x)) = starRingEnd ℂ (j (D.cc x)) := hj (D.cc x)
      have h2 : j (D.cc x) = starRingEnd ℂ (j x) := hj x
      rw [AlgEquiv.mul_apply, h1, h2, Complex.conj_conj, AlgEquiv.one_apply])
  have hΨ : Chr.Psi l e (Chr.dirG ℚ Ω ψ) D.cc = 1 := by
    have h1 : cycZ ℚ Ω l D.cc = -1 := hσ'.cyc (E := ℚ)
    have h2 : chiO ℚ Ω l c.O D.cc = -1 := by
      show Units.map (algebraMap ℤ_[l] c.O).toMonoidHom (cycZ ℚ Ω l D.cc) = -1
      rw [h1]
      apply Units.ext
      simp
    have h3 : (Chr.dirG ℚ Ω ψ D.cc : c.O) = (-1) ^ e := by
      rw [Chr.dirG, MonoidHom.comp_apply, (Chr.clsFacts ℚ Ω N).2.2.2.1 D.cc hσ', MulChar.coe_toUnitHom]
      exact D.gd.par
    apply Units.ext
    show ((chiO ℚ Ω l c.O D.cc ^ (e : ℤ) * Chr.dirG ℚ Ω ψ D.cc : c.Oˣ) : c.O) = 1
    rw [h2, zpow_natCast, Units.val_mul, h3, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one, ← mul_pow]
    simp
  have hram : ∀ B' : ValuationSubring Ω, ¬ Ine (F := ℚ) B' ≤ D.η.ker →
      B'.valuation ((l * N * (discr K).natAbs : ℕ) : Ω) < 1 := by
    intro B' h
    haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
    have hd : B'.valuation ((discr K : ℤ) : Ω) < 1 := by
      by_contra h4
      refine h fun s hs => ?_
      rw [D.η_ker]
      have key := GlobalTheory.UnramDiscr.embedding_eq B' h4 ((s : Ω →+* Ω).comp (algebraMap K Ω)) (algebraMap K Ω) (fun x => by
        refine hs.2 _ ((B'.valuation_le_one_iff _).mpr (GlobalTheory.UnramDiscr.mem_of_isIntegral B' ?_))
        exact (RingOfIntegers.isIntegral_coe x).map (algebraMap K Ω).toIntAlgHom)
      exact fun x => DFunLike.congr_fun key x
    have hd' : B'.valuation (((discr K).natAbs : ℕ) : Ω) < 1 := by
      rcases Int.natAbs_eq (discr K) with h1 | h1
      · rw [h1, Int.cast_natCast] at hd; exact hd
      · rw [h1, Int.cast_neg, Int.cast_natCast, Valuation.map_neg] at hd; exact hd
    rw [Nat.cast_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((B'.valuation_le_one_iff _).2 (natCast_mem B' _))) hd'
  have hlM : l ∣ l * N * (discr K).natAbs := (dvd_mul_right l N).mul_right _
  obtain ⟨hfin, haut, ka, hka, haut2⟩ := hL Ω l ι c N e ψ D.gd.e_pos D.gd.N_even D.η D.cc g₁ B _ (dvd_mul_right _ _) hram L Φ C₀ k hB ok big sc
  haveI : IsAlgClosure L Ω := Th.Db.algClo L Ω
  have hLk : LinkHyp c N e D.η D.cc B (l * N * (discr K).natAbs) := ⟨D.gd.e_pos, dvd_mul_right _ _,
    mul_ne_zero (mul_ne_zero hl.out.ne_zero (NeZero.ne N)) (Int.natAbs_ne_zero.2 (discr_ne_zero K)), hram, hB, hσ⟩
  have h3' := h3 Ω l c N e ψ _ _ g₁ B _ hLk L Φ C₀ k ok
  have hK3' := hK3 Ω l c N e ψ D.gd.N_even _ _ g₁ B _ hLk L Φ C₀ k ok big sc
  have h2' := _root_.UpperTheory.V.Z.Win.Dn.end2' (_root_.UpperTheory.V.Z.Win.Dn.autEnd2_alt H hPot hIne hQ hN hT hC D k ok hlM hB hLk ι ka hka haut2)
  have h1' := _root_.UpperTheory.V.Z.Win.Dn.autEnd3_alt hD k ok hlM hσ ι K
  have hk := D.η_ker
  have hquad := D.gd.quad
  refine ⟨g₁, marks_of_link k ok hlM hsq hΨ, finEnd_of_finPt k ok hlM hsq hfin, ?_, h2'⟩
  have h0 := fun a b => h1' a b haut
  clear h1' h2' haut haut2
  generalize D.η = η₀ at h0 h3' hK3' hk ⊢
  have fix_iff (f g : K →+* Ω) (s : Ω ≃ₐ[ℚ] Ω)
      (h : ∀ x, s (f x) = f x) (x : K) : s (g x) = g x := by
    by_cases hq : ∃ q : ℚ, (q : K) = x
    · obtain ⟨q, rfl⟩ := hq
      simp only [map_ratCast]
    · have hli : LinearIndependent ℚ ![(1 : K), x] := by
        rw [LinearIndependent.pair_iff]
        intro a b hab
        by_cases hb : b = 0
        · subst hb
          simp at hab
          exact ⟨hab, rfl⟩
        · exfalso
          apply hq
          refine ⟨-a / b, ?_⟩
          rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
          have hb' : (b : K) ≠ 0 := by exact_mod_cast hb
          push_cast
          rw [div_eq_iff hb']
          linear_combination -hab
      have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hquad])
      have hmem : x * x ∈ Submodule.span ℚ (Set.range ![(1 : K), x]) := by
        rw [hspan]
        exact Submodule.mem_top
      rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
        Set.singleton_union, Submodule.mem_span_pair] at hmem
      obtain ⟨a, b, hab⟩ := hmem
      rw [Rat.smul_def, Rat.smul_def, mul_one] at hab
      have hg : g x * g x = a + b * g x := by
        rw [← map_mul, ← hab, map_add (f := _), map_mul, map_ratCast, map_ratCast]
      have hf : f x * f x = a + b * f x := by
        rw [← map_mul, ← hab, map_add (f := _), map_mul, map_ratCast, map_ratCast]
      have hprod : (g x - f x) * (g x - ((b : Ω) - f x)) = 0 := by
        linear_combination hg - hf
      rcases mul_eq_zero.mp hprod with h1 | h1
      · rw [sub_eq_zero.mp h1, h x]
      · have h2 : g x = f ((b : K) - x) := by
          rw [sub_eq_zero.mp h1, map_sub, map_ratCast]
        rw [h2, h]
  have hker : ∀ [Algebra K Ω], Base.galOf ℚ K Ω = η₀.ker := by
    rw [hk]
    intro a
    ext s
    have fixes_other_embedding (f g : K →+* Ω) (h : ∀ x, s (f x) = f x) (x : K) :
        s (g x) = g x := by
      by_cases hx : ∃ q : ℚ, (q : K) = x
      · obtain ⟨q, rfl⟩ := hx
        simp only [map_ratCast]
      · have hli : LinearIndependent ℚ ![(1 : K), x] := by
          rw [LinearIndependent.pair_iff]
          intro u v huv
          by_cases hv : v = 0
          · subst hv
            simp at huv
            exact ⟨huv, rfl⟩
          · exfalso
            apply hx
            refine ⟨-u / v, ?_⟩
            rw [Rat.smul_def, Rat.smul_def, mul_one] at huv
            have hv' : (v : K) ≠ 0 := by exact_mod_cast hv
            push_cast
            rw [div_eq_iff hv']
            linear_combination -huv
        have hspan := hli.span_eq_top_of_card_eq_finrank' (by simp [hquad])
        have hmem : x * x ∈ Submodule.span ℚ (Set.range ![(1 : K), x]) := by
          rw [hspan]
          exact Submodule.mem_top
        rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
          Set.singleton_union, Submodule.mem_span_pair] at hmem
        obtain ⟨u, v, huv⟩ := hmem
        rw [Rat.smul_def, Rat.smul_def, mul_one] at huv
        have hg : g x * g x = u + v * g x := by
          rw [← map_mul, ← huv, map_add (f := _), map_mul, map_ratCast, map_ratCast]
        have hf : f x * f x = u + v * f x := by
          rw [← map_mul, ← huv, map_add (f := _), map_mul, map_ratCast, map_ratCast]
        have hprod : (g x - f x) * (g x - ((v : Ω) - f x)) = 0 := by
          linear_combination hg - hf
        rcases mul_eq_zero.mp hprod with h1 | h1
        · rw [sub_eq_zero.mp h1, h x]
        · have h2 : g x = f ((v : K) - x) := by
            rw [sub_eq_zero.mp h1, map_sub, map_ratCast]
          rw [h2, h]
    exact ⟨fixes_other_embedding a.algebraMap aK.algebraMap,
      fixes_other_embedding aK.algebraMap a.algebraMap⟩
  exact h0 hker fun A _ _ r hr hi _ _ _ ρ hρ => by
    haveI : IsAlgClosure K Ω := Th.Db.algClo K Ω
    have t := h3' A r hr K hker.symm ρ hρ
    exact ⟨t.1, t.2, hK3' A r hr hi K hker.symm ρ hρ⟩
end
