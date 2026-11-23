module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes
public import Development.AutomorphicArithmetic.AutomorphicVarieties.NumberFieldTowers.XTwApplyApply
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.GenOfRk
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.genOfRk :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (N r : ℕ) (U : Subgroup (G F Ω)), IsClosed (U : Set (G F Ω)) → XRk l N (cycU l U) r → Tower.GenLE ℤ_[l] (Xinf l N U) r := by
  intro F Ω _ _ _ _ _ l _ N rk U hU hrk
  classical
  have hQ : ∀ q : QZ l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0 := by
    intro q
    revert q
    show ∀ q : ℚ_[l] ⧸ ZlSub l, ∃ r : ℕ, (l : ℤ_[l]) ^ r • q = 0
    intro q
    induction q using Submodule.Quotient.induction_on with
    | _ x =>
      have hl : (1 : ℝ) < l := by exact_mod_cast (Fact.out : l.Prime).one_lt
      obtain ⟨r, hr⟩ := pow_unbounded_of_one_lt ‖x‖ hl
      refine ⟨r, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      have hn : ‖(l : ℚ_[l]) ^ r * x‖ ≤ 1 := by
        rw [norm_mul, norm_pow, Padic.norm_p]
        have hp : (0 : ℝ) < (l : ℝ) ^ r := by positivity
        rw [inv_pow, inv_mul_le_iff₀ hp, mul_one]
        exact hr.le
      refine ⟨⟨(l : ℚ_[l]) ^ r * x, hn⟩, ?_⟩
      simp [Algebra.smul_def]
      rfl
  have hC : IsClosed ((cycU l U : Subgroup (G F Ω)) : Set (G F Ω)) :=
    hU.inter (isClosed_singleton.preimage (continuous_cycZ F Ω l))
  haveI : CompactSpace (cycU l U) := isCompact_iff_compactSpace.mp hC.isCompact
  have htors : ∀ φ : Dinf l N U, ∃ k : ℕ, (l : ℤ_[l]) ^ k • φ = 0 := by
    intro φ
    have hfin := IsLocallyConstant.range_finite φ.2.1
    choose r hr using hQ
    refine ⟨∑ q ∈ hfin.toFinset, r q, ?_⟩
    apply Subtype.ext
    funext u
    have hq : (φ : cycU l U → QZ l) u ∈ hfin.toFinset := by simp
    change (l : ℤ_[l]) ^ (∑ q ∈ hfin.toFinset, r q) • (φ : cycU l U → QZ l) u = 0
    rw [← Finset.add_sum_erase _ _ hq, pow_add, mul_comm, mul_smul, hr, smul_zero]
  obtain ⟨ι, hι, hιr, -⟩ := zmodToQZ l 1
  let κ : ZMod l →+ QZ l := ι.comp (ZMod.ringEquivCongr (pow_one l).symm).toAddMonoidHom
  have hκ : Function.Injective κ := hι.comp (ZMod.ringEquivCongr (pow_one l).symm).injective
  have hκr : ∀ q : QZ l, (l : ℤ_[l]) • q = 0 → κ (Function.invFun κ q) = q := by
    intro q hq
    apply Function.invFun_eq
    obtain ⟨a, ha⟩ := (hιr q).2 (by rw [pow_one]; exact hq)
    exact ⟨(ZMod.ringEquivCongr (pow_one l).symm).symm a, by simp [κ, ha]⟩
  have hval : ∀ φ : Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]), ∀ u : cycU l U,
      (l : ℤ_[l]) • ((φ : Dinf l N U) : cycU l U → QZ l) u = 0 := by
    intro φ u
    have h := (Submodule.mem_torsionBy_iff _ _).1 φ.2
    have h2 := congrArg (fun ψ : Dinf l N U => (ψ : cycU l U → QZ l) u) h
    exact h2
  let f : Submodule.torsionBy ℤ_[l] (Dinf l N U) (l : ℤ_[l]) → XDual N (cycU l U) (ZMod l) (ZMod l) :=
    fun φ => ⟨fun u => Function.invFun κ (((φ : Dinf l N U) : cycU l U → QZ l) u), by
      have hφ := (φ : Dinf l N U).2
      refine ⟨by exact hφ.1.comp (Function.invFun κ), ?_, ?_, ?_⟩
      · intro a b
        apply hκ
        rw [map_add (f := _), hκr _ (hval φ _), hκr _ (hval φ _), hκr _ (hval φ _), hφ.2.1]
      · intro A u hu
        apply hκ
        rw [hκr _ (hval φ _), hφ.2.2.1 A u hu, map_zero]
      · intro A hA u hu
        apply hκ
        rw [hκr _ (hval φ _), hφ.2.2.2 A hA u hu, map_zero]⟩
  have hf : Function.Injective f := by
    intro φ ψ h
    apply Subtype.ext
    apply Subtype.ext
    funext u
    have h1 := congrArg (fun χ : XDual N (cycU l U) (ZMod l) (ZMod l) => κ ((χ : cycU l U → ZMod l) u)) h
    simp only [f] at h1
    rwa [hκr _ (hval φ u), hκr _ (hval ψ u)] at h1
  exact dualGen l (Dinf l N U) rk htors (hrk.of_injective f hf)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.QuadStep
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

theorem UpperTheory.V.Two.quadStep :
    ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : AbF) (p N n : ℕ), p.Prime → p ∣ N → CardLe (CharOff (cycU 2 (abU Ω A)) (ineOff ℚ Ω N) 2) n → CardLe (CharOff (cycU 2 (abU Ω (A.sup (AbF.quad p)))) (ineOff ℚ Ω N) 2) (n ^ 2) := by
  intro Ω _ _ _ A p N n hp hpN h
  have hsup := (abBasic Ω).1 A (AbF.quad p)
  have hq := (abBasic Ω).2.1 (AbF.quad p)
  have key : cycU 2 (abU Ω (A.sup (AbF.quad p))) = abU Ω (AbF.quad p) ⊓ cycU 2 (abU Ω A) := by
    ext g
    simp only [cycU, hsup, Subgroup.mem_inf]
    tauto
  rw [key]
  have hidx : (abU Ω (AbF.quad p)).index ∣ 2 := by
    rw [hq.1]
    exact degBasic.2.2.1 p hp
  have hnorm : (abU Ω (AbF.quad p)).Normal := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hidx with h1 | h2
    · rw [Subgroup.index_eq_one] at h1
      rw [h1]
      infer_instance
    · exact Subgroup.normal_of_index_eq_two h2
  refine idxTwo (G ℚ Ω) _ (cycU 2 (abU Ω A)) (ineOff ℚ Ω N) n inf_le_right ?_ ?_ ?_ ?_ h
  · rw [Subgroup.inf_subgroupOf_right, Subgroup.coe_subgroupOf]
    exact hq.2.2.1.preimage continuous_subtype_val
  · rw [Subgroup.inf_relIndex_right]
    exact (Subgroup.relIndex_dvd_index_of_normal _ _).trans hidx
  · intro v _ s hs
    exact (ineConj ℚ Ω v).2.2 N s hs
  · intro s hs hsV
    refine Subgroup.mem_inf.2 ⟨?_, hsV⟩
    obtain ⟨B, hB, hsB⟩ := hs
    haveI : NeZero (AbF.quad p).m := ⟨by simp [AbF.quad]⟩
    have hv : ¬ B.valuation ((AbF.quad p).m : Ω) < 1 := by
      intro hlt
      apply hB
      obtain ⟨k, rfl⟩ := hpN
      have hm : (AbF.quad p).m = p := max_eq_left hp.one_lt.le
      rw [hm] at hlt
      rw [Nat.cast_mul, map_mul]
      have hk : B.valuation (k : Ω) ≤ 1 := (B.valuation_le_one_iff _).2 (natCast_mem B k)
      exact lt_of_le_of_lt (mul_le_of_le_one_right' hk) hlt
    exact hq.2.2.2 (ineChar Ω (AbF.quad p).m B hv hsB)
end

