module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.Bundle0003
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.AuxiliaryPrimeFunction
public import GroundTheory.AutomorphicForms.AffineBruhat
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0353

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsLevelSubgroupCentralScalarOfPos
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Gam0 Plc comp mat rat mem_Sim)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

theorem UpperTheory.exists_levelSubgroup_central_scalar_of_pos :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (c : ℕ), 0 < c →
      ∃ y : Gam0 E n, y.1.1.val = (c : E) • (1 : Matrix (Fin n) (Fin n) E) ∧ ((y.1.2 : ℚˣ) : ℚ) = (c : ℚ) ^ 2 ∧
        (∀ w : Plc E, (comp w (rat y)).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) ∧
        (∀ g : GUf E n, rat y * g = g * rat y) ∧
        (∀ h : S.G.GAf, F.j (rat y) * h = h * F.j (rat y)) ∧
        ∀ v, S.L.actG (F.j (rat y)) v = c • v := by
  intro E _ _ _ A n p _ S F c hc
  have hcE : (c : E) ≠ 0 := Nat.cast_ne_zero.2 hc.ne'
  have hcQ : (c : ℚ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hc.ne')
  let u : GL (Fin n) E := ⟨(c : E) • 1, (c : E)⁻¹ • 1, by simp [smul_smul, hcE], by simp [smul_smul, hcE]⟩
  let s : ℚˣ := Units.mk0 ((c : ℚ) ^ 2) hcQ
  have hm : (u, s) ∈ Gam0 E n := by
    refine ⟨mem_Sim.2 ?_, ?_⟩
    · show (((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (GlobalTheory.SplitPts.conjE E).toRingHom)ᵀ * ((c : E) • (1 : Matrix (Fin n) (Fin n) E)) = algebraMap ℚ E ((c : ℚ) ^ 2) • 1
      ext i k
      by_cases hik : i = k
      · simp [hik, Matrix.one_apply, Matrix.mul_apply, pow_two]
      · simp [hik, Ne.symm hik, Matrix.one_apply, Matrix.mul_apply]
    · show (0 : ℚ) < (c : ℚ) ^ 2
      positivity
  let y : Gam0 E n := ⟨(u, s), hm⟩
  have hmat : (mat (rat y)).val = ((c : FiniteAdeleRing (𝓞 E) E)) • (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 E) E)) := by
    show ((c : E) • (1 : Matrix (Fin n) (Fin n) E)).map (algebraMap E (FiniteAdeleRing (𝓞 E) E)) = _
    ext i k
    by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
  have hcomp : ∀ w : Plc E, (comp w (rat y)).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
    intro w
    show ((mat (rat y)).val).map (pLoc E w) = _
    rw [hmat]
    ext i k
    by_cases hik : i = k <;> simp [hik, Matrix.one_apply]
  have hcen : ∀ g : GUf E n, rat y * g = g * rat y := by
    intro g
    refine Subtype.ext (Prod.ext (Units.ext ?_) (mul_comm _ _))
    show (mat (rat y)).val * (mat g).val = (mat g).val * (mat (rat y)).val
    rw [hmat]
    simp
  refine ⟨y, rfl, rfl, hcomp, hcen, ?_, ?_⟩
  · intro h
    obtain ⟨g, rfl⟩ := F.surj h
    rw [← map_mul, ← map_mul, hcen]
  · intro v
    refine sub_eq_zero.1 (F.vec_inj (S.L.actG (F.j (rat y)) v - c • v) fun w hw => ?_)
    rw [map_sub, map_nsmul, F.vec_act w hw, sub_eq_zero]
    have e : (F.a w * comp w (rat y) * (F.a w)⁻¹).val = (c : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := by
      rw [Units.val_mul, Units.val_mul, hcomp w]
      simp
    rw [e, Matrix.smul_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul]
end

-- bundled from Development.AutomorphicArithmetic.IwahoriCommensurability.ExistsPrimePowScalarIntegralOfGoodPrime
section
open NumberField IsDedekindDomain Matrix GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc comp)
open UpperTheory.Gal.W2.Seed UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl

private theorem val_natCast_lt_one {E : Type} [Field E] [NumberField E] (u : Plc E) (r : ℕ)
    (hu : (r : 𝓞 E) ∈ u.asIdeal) : Valued.v (r : u.adicCompletion E) < 1 := by
  have h := (u.valuation_lt_one_iff_mem (K := E) (r : 𝓞 E)).2 hu
  have e : ((r : ℕ) : u.adicCompletion E) = algebraMap E (u.adicCompletion E) (r : E) :=
    (map_natCast _ r).symm
  have e2 : Valued.v (algebraMap E (u.adicCompletion E) (r : E)) = u.valuation E (r : E) :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' u _
  rw [e, e2]
  simpa using h

private theorem eventually_integral {E : Type} [Field E] [NumberField E] (u : Plc E) (r : ℕ)
    (hu : (r : 𝓞 E) ∈ u.asIdeal) (x : u.adicCompletion E) :
    ∀ᶠ M : ℕ in Filter.atTop, ((r ^ M : ℕ) : u.adicCompletion E) * x ∈ u.adicCompletionIntegers E := by
  have h1 := val_natCast_lt_one u r hu
  by_cases hx : x = 0
  · simp [hx]
  have hv : Valued.v x ≠ 0 := by simpa using hx
  obtain ⟨M₀, hM₀⟩ := exists_pow_lt₀ h1 (Units.mk0 _ (inv_ne_zero hv))
  filter_upwards [Filter.eventually_ge_atTop M₀] with M hM
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers, map_mul, Nat.cast_pow, map_pow]
  have h2 : Valued.v (r : u.adicCompletion E) ^ M ≤ (Valued.v x)⁻¹ :=
    (pow_le_pow_of_le_one zero_le' h1.le hM).trans hM₀.le
  calc _ ≤ (Valued.v x)⁻¹ * Valued.v x := mul_le_mul' h2 le_rfl
    _ = 1 := inv_mul_cancel₀ hv

theorem UpperTheory.exists_primePow_scalar_integral_of_good_prime :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (A : Arith E) (n p : ℕ) [Fact p.Prime] (S : Setup A n p) (F : Frame S) (r : ℕ), r.Prime → A.Good r → ∀ g : GUf E n, (∀ u : Plc E, (r : 𝓞 E) ∉ u.asIdeal → comp u g = 1) → ∃ M : ℕ, ∀ d : GUf E n, (∀ w : Plc E, (comp w d).val = ((r ^ M : ℕ) : w.adicCompletion E) • (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) → Integ S.L (F.j (g * d)) := by
  intro E _ _ _ A n p _ S F r hr _ g hg
  have hr0 : (r : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hr.ne_zero
  have hT : {u : Plc E | (r : 𝓞 E) ∈ u.asIdeal}.Finite := by
    refine (Ideal.finite_factors (I := Ideal.span {(r : 𝓞 E)}) (by simpa using hr0)).subset fun u hu => ?_
    exact Ideal.dvd_iff_le.2 ((Ideal.span_singleton_le_iff_mem _).2 hu)
  have hev : ∀ᶠ M : ℕ in Filter.atTop, ∀ u ∈ {u : Plc E | (r : 𝓞 E) ∈ u.asIdeal}, ∀ i k,
      ((r ^ M : ℕ) : u.adicCompletion E) * F.cmp u g i k ∈ u.adicCompletionIntegers E := by
    rw [Filter.eventually_all_finite hT]
    intro u hu
    rw [Filter.eventually_all]
    intro i
    rw [Filter.eventually_all]
    intro k
    exact eventually_integral u r hu _
  obtain ⟨M, hM⟩ := hev.exists
  refine ⟨M, fun d hd => (integ_iff F _).2 fun w _ i k => ?_⟩
  have e : F.cmp w (g * d) = ((r ^ M : ℕ) : w.adicCompletion E) • F.cmp w g := by
    unfold Frame.cmp
    simp only [map_mul, Units.val_mul, hd w]
    simp [Matrix.mul_assoc]
  rw [e, Matrix.smul_apply, smul_eq_mul]
  by_cases hw : (r : 𝓞 E) ∈ w.asIdeal
  · exact hM w hw i k
  · have h1 : F.cmp w g = 1 := by
      unfold Frame.cmp
      simp [hg w hw]
    rw [h1, Matrix.one_apply]
    split_ifs
    · simpa using natCast_mem (w.adicCompletionIntegers E) (r ^ M)
    · simp
end

-- bundled from Development.AutomorphicArithmetic.IwahoriCommensurability.IsCommensuratedIwahoriGl
section
open Formalism.UG GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal Matrix

theorem UpperTheory.isCommensurated_iwahori_gl :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : ℕ), IsCommensurated (iwahori k n) := by
  intro k _ _ _ _ n g
  have hO : IsOpen (iwahori k n : Set (GL (Fin n) k)) := isOpen_iwahori k n
  have hC : IsCompact (iwahori k n : Set (GL (Fin n) k)) := isCompact_iwahori k n
  have hset : (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) = (fun x => g⁻¹ * x * g) ⁻¹' (iwahori k n : Set (GL (Fin n) k)) := by
    ext x
    simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [mul_assoc] using hy
    · intro hx
      exact ⟨_, hx, by simp [mul_assoc]⟩
  have hOc : IsOpen (((iwahori k n).map (MulAut.conj g).toMonoidHom : Subgroup (GL (Fin n) k)) :
      Set (GL (Fin n) k)) := by
    rw [hset]
    exact hO.preimage (by fun_prop)
  haveI : CompactSpace (iwahori k n) := isCompact_iff_compactSpace.mp hC
  have hU : IsOpen ((((iwahori k n).map (MulAut.conj g).toMonoidHom).subgroupOf (iwahori k n) :
      Subgroup (iwahori k n)) : Set (iwahori k n)) :=
    hOc.preimage continuous_subtype_val
  haveI := Subgroup.quotient_finite_of_isOpen _ hU
  exact Subgroup.index_ne_zero_of_finite
end

