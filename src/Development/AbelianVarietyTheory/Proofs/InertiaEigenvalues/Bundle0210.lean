module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.TraceFormulas.LatDefs
public import Formalism.GaloisCohomology.LocalTateDualityK
public import Formalism.CharacterColumnKernels.StatementRho
public import ReciprocityTheory.Hypotheses.GalCohDefs
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LevRepZApply
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0158
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0089
public import Formalism.WachLatticeTwists.LatticeDualFibres.FibreDualStable
public import Formalism.GaloisCohomology.StatementLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulEqZeroOfMul
section
open ReciprocityTheory.Gal

noncomputable section

namespace GlobalTheory.UnramifiedH2Bound

open GlobalTheory.ShapeNeg GlobalTheory.CyclotomicH2Bound

theorem pow_mul_eq_zero_of_mul {p : ℕ} (hp : p.Prime) {n m : ℕ} {b : ℤ} (hb : ¬ ((p : ℤ) ^ m ∣ b))
    {x : ZMod (p ^ n)} (hx : (b : ZMod (p ^ n)) * x = 0) : ((p ^ m : ℕ) : ZMod (p ^ n)) * x = 0 := by
  have : NeZero (p ^ n) := ⟨pow_ne_zero _ hp.ne_zero⟩

  have hbx : b • x = 0 := by rwa [zsmul_eq_mul]
  have h1 : (addOrderOf x : ℤ) ∣ b := addOrderOf_dvd_iff_zsmul_eq_zero.mpr hbx
  have h2 : addOrderOf x ∣ p ^ n := by
    have := addOrderOf_dvd_card (x := x)
    rwa [ZMod.card] at this
  obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow hp).mp h2
  have hjm : j < m := by
    by_contra hcon
    push Not at hcon
    apply hb
    rw [hjx] at h1
    exact (pow_dvd_pow (p : ℤ) hcon).trans (by exact_mod_cast h1)
  have h3 : addOrderOf x ∣ p ^ m := by
    rw [hjx]; exact pow_dvd_pow _ hjm.le
  have h4 : (p ^ m : ℕ) • x = 0 := addOrderOf_dvd_iff_nsmul_eq_zero.mp h3
  rwa [nsmul_eq_mul] at h4

theorem h2_bounded_of_trivial_action : Formalism.GaloisCohomology.LocalTateDualityK → ∀ {p : ℕ} [Fact p.Prime] {K : IntermediateField ℚ_[p] (PadicAlgCl p)},
    FiniteDimensional ℚ_[p] K → ∀ {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [Finite (IsLocalRing.ResidueField O)] {ϖ : O}, Irreducible ϖ → (p : O) ∈ Ideal.span {ϖ} → (p : O) ≠ 0 →
    ∀ {M : Type} [AddCommGroup M] [Module O M], (M ≃ₗ[O] Formalism.NG.KO O) →
    ∀ (ρ : Representation O (Formalism.GaloisCohomology.GK p K) M), (∀ g m, ρ g m = m) →
    (∀ (n : ℕ) (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      ReciprocityTheory.Gal.ContAction (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) →
    ∃ C : ℕ, ∀ (n : ℕ), 0 < n → ∀ (h : ((p : O) ^ n) ∈ Ideal.span {ϖ ^ n}),
      letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
      Nat.card (ReciprocityTheory.Gal.H2 (GlobalTheory.ShapeNeg.levRepZ p n h ρ)) ≤ C := by
  intro hTD p _ K hK O _ _ _ _ ϖ hϖ hpϖ hp0 M _ _ eM ρ hρ hcont
  have hp : p.Prime := Fact.out

  obtain ⟨σ, N, ζ', hζ'1, hσζ'⟩ :=
    GlobalTheory.ShapeNeg.exists_pow_ne_rootOfUnity (p := p) (K := K) hK 1 Nat.one_pos
  rw [pow_one] at hσζ'

  obtain ⟨k, hk⟩ := IsDiscreteValuationRing.ideal_eq_span_pow_irreducible
    (s := Ideal.span {(p : O) ^ N}) (by rw [Ne, Ideal.span_singleton_eq_bot]; exact pow_ne_zero N hp0) hϖ
  have hfinQ : Finite (O ⧸ Ideal.span {(p : O) ^ N}) := by
    rw [hk]; exact finite_quot hϖ k
  refine ⟨(p ^ N) ^ ((p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N})), ?_⟩
  intro n hn h
  letI := GlobalTheory.ShapeNeg.levZ (M := M) p n h
  have htriv : ∀ (g : Formalism.GaloisCohomology.GK p K) (m : Lev M (ϖ ^ n)), levRepZ p n h ρ g m = m := by
    intro g m
    rw [levRepZ_apply]
    exact Lev.ext (by rw [levRep_val, hρ])

  obtain ⟨x₀, hx₀⟩ := lev_cyclic eM hϖ n
  have hx₀k : (ϖ ^ n) • x₀ = 0 := Lev.ext (by rw [Lev.val_smul, Lev.smul_val, Lev.val_zero])
  have hfinL : Finite (Lev M (ϖ ^ n)) := by
    have := finite_quot hϖ n
    refine Finite.of_surjective (fun q : O ⧸ Ideal.span {ϖ ^ n} => q.out • x₀) ?_
    intro y
    obtain ⟨t, rfl⟩ := hx₀ y
    exact ⟨Ideal.Quotient.mk _ t, out_smul n hx₀k t⟩
  obtain ⟨⟨e⟩, -, -, -, hcup⟩ :=
    hTD p K hK n (Lev M (ϖ ^ n)) (levRepZ p n h ρ) hn (hcont n h)

  have hkill : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (m : Lev M (ϖ ^ n)), ((p ^ N : ℕ) : ZMod (p ^ n)) * φ.1 m = 0 := by
    intro φ m
    by_cases hnN : n ≤ N
    · rw [(ZMod.natCast_eq_zero_iff _ _).mpr (pow_dvd_pow p hnN), zero_mul]
    push Not at hnN
    obtain ⟨ζ, hζ⟩ := exists_prim p n
    have hσζn : (σ ζ) ^ (p ^ n) = 1 := by rw [← map_pow, hζ.pow_eq_one, map_one]
    obtain ⟨a, -, ha⟩ := hζ.eq_pow_of_pow_eq_one hσζn
    have hcyc := cycK_eq_of_prim n σ hζ a ha.symm
    have hfixm : ((Formalism.GaloisCohomology.cycK p K n σ : (ZMod (p ^ n))ˣ) : ZMod (p ^ n)) *
        φ.1 (levRepZ p n h ρ σ⁻¹ m) = φ.1 m := by
      rw [← twDual_apply]
      exact DFunLike.congr_fun ((mem_riemannRochSpace_iff_regularAt_everywhere _ _).mp φ.2 σ) m
    rw [htriv, hcyc] at hfixm
    have hnd : ¬ ((p : ℤ) ^ N ∣ (a : ℤ) - 1) := by
      rintro ⟨d, hd⟩
      apply hσζ'
      have hζ'n : ζ' ^ (p ^ n) = 1 := by
        obtain ⟨c, hc⟩ := pow_dvd_pow p hnN.le
        rw [hc, pow_mul, hζ'1, one_pow]
      obtain ⟨j, -, hj⟩ := hζ.eq_pow_of_pow_eq_one hζ'n
      have hσ' : σ ζ' = ζ' ^ a := by
        rw [← hj, map_pow, ← ha, ← pow_mul, ← pow_mul, mul_comm]
      have hne : ζ' ≠ 0 := by
        rintro rfl
        rw [zero_pow (pow_ne_zero N hp.ne_zero)] at hζ'1
        exact zero_ne_one hζ'1
      have ha' : (a : ℤ) = 1 + ((p ^ N : ℕ) : ℤ) * d := by push_cast; linarith
      rw [hσ', ← zpow_natCast, ha', zpow_add₀ hne, zpow_one, zpow_mul, zpow_natCast, hζ'1,
        one_zpow, mul_one]
    have hb : (((a : ℤ) - 1 : ℤ) : ZMod (p ^ n)) * φ.1 m = 0 := by
      push_cast
      rw [sub_mul, one_mul, hfixm, sub_self]
    exact pow_mul_eq_zero_of_mul hp hnd hb

  have hTcard : Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ≤ p ^ N := by
    have key : ∀ z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0},
        z.1.val = p ^ (n - N) * (z.1.val / p ^ (n - N)) ∧ z.1.val / p ^ (n - N) < p ^ N := by
      intro z
      have hlt : z.1.val < p ^ (n - N) * p ^ N := by
        calc z.1.val < p ^ n := ZMod.val_lt _
          _ ≤ p ^ (n - N + N) := Nat.pow_le_pow_right hp.pos (by omega)
          _ = _ := pow_add _ _ _
      have hdvd : p ^ (n - N) ∣ z.1.val := by
        by_cases hnN : n ≤ N
        · rw [Nat.sub_eq_zero_of_le hnN, pow_zero]; exact one_dvd _
        · push Not at hnN
          have h1 : ((p ^ N * z.1.val : ℕ) : ZMod (p ^ n)) = 0 := by
            rw [Nat.cast_mul, ZMod.natCast_zmod_val]; exact z.2
          rw [ZMod.natCast_eq_zero_iff] at h1
          have h2 : p ^ n = p ^ N * p ^ (n - N) := by rw [← pow_add]; congr 1; omega
          have h1' : p ^ N * p ^ (n - N) ∣ p ^ N * z.1.val := by rw [← h2]; exact h1
          exact Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos N) h1'
      exact ⟨(Nat.mul_div_cancel' hdvd).symm, Nat.div_lt_of_lt_mul hlt⟩
    have hinj : Function.Injective
        (fun z : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} => ((z.1.val / p ^ (n - N) : ℕ) : ZMod (p ^ N))) := by
      intro z w hzw
      have hz := key z
      have hw := key w
      have hv := congrArg ZMod.val hzw
      simp only [ZMod.val_cast_of_lt hz.2, ZMod.val_cast_of_lt hw.2] at hv
      apply Subtype.ext
      apply ZMod.val_injective
      rw [hz.1, hw.1, hv]
    have : NeZero (p ^ N) := ⟨pow_ne_zero _ hp.ne_zero⟩
    calc _ ≤ Nat.card (ZMod (p ^ N)) := Nat.card_le_card_of_injective _ hinj
      _ = p ^ N := Nat.card_zmod _

  have hval : ∀ (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (t : O),
      φ.1 (t • x₀) = φ.1 ((Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out • x₀) := by
    intro φ t
    have hmem : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out - t ∈
        Ideal.span {(p : O) ^ N} :=
      Ideal.Quotient.eq.mp (by rw [Ideal.Quotient.mk_out])
    obtain ⟨s, hs⟩ := Ideal.mem_span_singleton'.mp hmem
    have hout : (Ideal.Quotient.mk (Ideal.span {(p : O) ^ N}) t).out = t + ((p ^ N : ℕ) : O) * s := by
      rw [Nat.cast_pow]; linear_combination -hs
    rw [hout, add_smul, mul_smul, Nat.cast_smul_eq_nsmul, td_add, td_nsmul, nsmul_eq_mul,
      hkill φ, add_zero]
  have hΦ : Function.Injective (fun (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) (q : O ⧸ Ideal.span {(p : O) ^ N}) =>
      (⟨φ.1 (q.out • x₀), hkill φ _⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro φ ψ hφψ
    apply Subtype.ext
    refine DFunLike.ext _ _ fun m => ?_
    obtain ⟨t, rfl⟩ := hx₀ m
    rw [hval φ t, hval ψ t]
    exact congrArg Subtype.val (congrFun hφψ (Ideal.Quotient.mk _ t))
  have hfinH0 : Finite (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Finite.of_injective _ hΦ
  have hH0card : Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) ≤ (p ^ N) ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := by
    calc _ ≤ Nat.card (O ⧸ Ideal.span {(p : O) ^ N} → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) :=
          Nat.card_le_card_of_injective _ hΦ
      _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (O ⧸ Ideal.span {(p : O) ^ N}) := Nat.card_fun
      _ ≤ _ := Nat.pow_le_pow_left hTcard _

  have hsmul0 : ∀ φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))), ((p ^ N : ℕ) : ZMod (p ^ n)) • φ = 0 := by
    intro φ
    apply Subtype.ext
    refine DFunLike.ext _ _ fun m => ?_
    rw [Submodule.coe_smul, TDual.smul_apply, hkill φ m]
    rfl
  have hΨ : Function.Injective (fun (x : H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))))
      (φ : H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) =>
      (⟨e (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x φ), by
        have h0 := congrArg e (congrArg
          (cup20 (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ) (MonoidHom.id _) x) (hsmul0 φ))
        rw [LinearMap.map_smul, LinearEquiv.map_smul, LinearMap.map_zero, LinearEquiv.map_zero,
          smul_eq_mul] at h0
        exact h0⟩ : {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0})) := by
    intro x y hxy
    apply hcup.1
    apply LinearMap.ext
    intro φ
    apply e.injective
    exact congrArg Subtype.val (congrFun hxy φ)
  calc Nat.card (H2 (levRepZ p n h ρ))
      = Nat.card (H2 ((levRepZ p n h ρ).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := rfl
    _ ≤ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K))) → {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0}) := Nat.card_le_card_of_injective _ hΨ
    _ = Nat.card {z : ZMod (p ^ n) // ((p ^ N : ℕ) : ZMod (p ^ n)) * z = 0} ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.card_fun
    _ ≤ (p ^ N) ^ Nat.card (H0 ((twDual (Formalism.GaloisCohomology.cycK p K n) (levRepZ p n h ρ)).comp (MonoidHom.id (Formalism.GaloisCohomology.GK p K)))) := Nat.pow_le_pow_left hTcard _
    _ ≤ _ := Nat.pow_le_pow_right (pow_pos hp.pos N) hH0card

end GlobalTheory.UnramifiedH2Bound
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SenMultiplicitySubquotientLatticeLe
section
open GlobalTheory.PhiGam GlobalTheory.AdmLoc GlobalTheory.Models
open scoped LaurentSeries PowerSeries

namespace GlobalTheory.Models

theorem senle_exists_coker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (j : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hj : IsHom A B j) :
    ∃ (C : Ob k G) (q : (Fin B.m → k) →ₗ[k] (Fin C.m → k)),
      IsHom B C q ∧ Function.Surjective q ∧ Function.Exact j q := by
  have hle : ∀ g, LinearMap.range j ≤ (LinearMap.range j).comap (B.ρ g) := by
    rintro g _ ⟨x, rfl⟩
    exact ⟨A.ρ g x, hj g x⟩
  obtain ⟨C, e, he⟩ := exists_ob (B.ρ.quotient (LinearMap.range j) hle)
  refine ⟨C, e.toLinearMap ∘ₗ (LinearMap.range j).mkQ, fun g x => ?_,
    e.surjective.comp (Submodule.mkQ_surjective _), fun y => ?_⟩
  · simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he]
    rfl
  · simp [Submodule.Quotient.mk_eq_zero]

theorem senle_exists_ker {k G : Type} [Field k] [Group G] (A B : Ob k G)
    (p : (Fin A.m → k) →ₗ[k] (Fin B.m → k)) (hp : IsHom A B p) :
    ∃ (C : Ob k G) (s : (Fin C.m → k) →ₗ[k] (Fin A.m → k)),
      IsHom C A s ∧ Function.Injective s ∧ Function.Exact s p := by
  have hle : ∀ g, LinearMap.ker p ≤ (LinearMap.ker p).comap (A.ρ g) := by
    intro g x hx
    rw [LinearMap.mem_ker] at hx
    simp only [Submodule.mem_comap, LinearMap.mem_ker]
    rw [hp g x, hx, map_zero]
  obtain ⟨C, e, he⟩ := exists_ob (A.ρ.subrepresentation (LinearMap.ker p) hle)
  refine ⟨C, (LinearMap.ker p).subtype ∘ₗ e.symm.toLinearMap, fun g x => ?_,
    (Submodule.injective_subtype _).comp e.symm.injective, fun y => ?_⟩
  · obtain ⟨y, rfl⟩ := e.surjective x
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [← he, e.symm_apply_apply, e.symm_apply_apply]
    rfl
  · constructor
    · intro hy
      exact ⟨e ⟨y, hy⟩, by simp⟩
    · rintro ⟨x, rfl⟩
      exact (e.symm x).2

theorem sen_push_pre_le : ∀ {k G : Type} [Field k] [Group G] {l n : ℕ} [Fact l.Prime] [CharP k l] [NeZero n] {R : RingPG k l} (F : DFun R n G) (B A₁ A : Ob k G) (j : (Fin A₁.m → k) →ₗ[k] (Fin B.m → k)) (p : (Fin A₁.m → k) →ₗ[k] (Fin A.m → k)) (w w' : ZMod n → ℤ) (N : Lats k n B.m), F.Obj B → IsHom A₁ B j → Function.Injective j → IsHom A₁ A p → Function.Surjective p → ABC (F.D B) w w' N → ∀ i x, sen ((F.D A).γ i) (F.push A₁ A p (F.pre A₁ B j N) i) x ≤ sen ((F.D B).γ i) (N i) x := by
  intro k G _ _ l n _ _ _ R F B A₁ A j p w w' N hB hj hji hp hps hN i x
  have hA₁ : F.Obj A₁ := F.obj_sub A₁ B j hj hji hB
  obtain ⟨C, q, hq, hqs, hex⟩ := senle_exists_coker A₁ B j hj
  obtain ⟨K, s, hs, hsi, hex'⟩ := senle_exists_ker A₁ A p hp
  have h1 := _root_.GlobalTheory.Models.sen_eq_sen_pre_add_sen_push F A₁ B C j q N hB hj hq hji hqs hex i (hN.1 i) (hN.2.2 i) x
  have hsat := GlobalTheory.PhiGam.Sat.main R (F.D B) (F.D A₁) (F.map A₁ B j) (F.map_inj A₁ B j hA₁ hB hj hji)
    (F.map_φ A₁ B j hA₁ hB hj) (F.map_γ A₁ B j hA₁ hB hj) w w' N hN.1 hN.2.1 hN.2.2
  have h2 := _root_.GlobalTheory.Models.sen_eq_sen_pre_add_sen_push F K A₁ A s p (F.pre A₁ B j N) hA₁ hs hp hsi hps hex' i (hsat.1 i) (hsat.2.2 i) x
  omega

end GlobalTheory.Models
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpanOfLocalCohomologyShape
section
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

namespace GlobalTheory.ContCocycleDualLattice

universe u

section

variable {O G VT VT' : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    [TopologicalSpace O] [TopologicalSpace (FractionRing O)]
    [IsTopologicalAddGroup (FractionRing O)] [ContinuousSMul O (FractionRing O)]
    [Group G] [TopologicalSpace G]
    [AddCommGroup VT] [Module O VT] [TopologicalSpace VT] [IsTopologicalAddGroup VT]
    [ContinuousSMul O VT]
    [AddCommGroup VT'] [Module O VT'] [TopologicalSpace VT'] [IsTopologicalAddGroup VT']
    [ContinuousSMul O VT'] (D : LatData O G VT VT')

theorem mem_dualLat_iff_of_span (s : Finset VT) (hs : Submodule.span O (s : Set VT) = D.T) (f : VT') :
    f ∈ D.T' ↔ ∀ x ∈ s, D.bT x f ∈ Set.range (algebraMap O (FractionRing O)) := by
  constructor
  · intro hf x hx
    have := hf x (hs ▸ Submodule.subset_span hx)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 this
    exact ⟨y, hy⟩
  · intro hf x hx
    rw [← hs] at hx
    have hle : Submodule.span O (s : Set VT) ≤
        (1 : Submodule O (FractionRing O)).comap (D.bT.flip f) := by
      rw [Submodule.span_le]
      intro x hx
      obtain ⟨y, hy⟩ := hf x hx
      exact Submodule.mem_one.2 ⟨y, hy⟩
    exact hle hx

theorem isOpen_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) :
    IsOpen (D.T' : Set VT') := by
  obtain ⟨s, hs⟩ := hT
  have e : (D.T' : Set VT') = ⋂ x ∈ s, (fun f => D.bT x f) ⁻¹' Set.range (algebraMap O (FractionRing O)) := by
    ext f
    simp only [SetLike.mem_coe, Set.mem_iInter, Set.mem_preimage]
    exact mem_dualLat_iff_of_span D s hs f
  rw [e]
  refine isOpen_biInter_finset fun x _ => hO.preimage ?_
  exact D.contbT.comp (continuous_const.prodMk continuous_id)

theorem exists_smul_mem_dualLat (hT : D.T.FG) (f : VT') : ∃ c : O, c ≠ 0 ∧ c • f ∈ D.T' := by
  obtain ⟨s, hs⟩ := hT
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors O) s (fun x => D.bT x f)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, (mem_dualLat_iff_of_span D s hs _).2 fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := hb x hx
  refine ⟨y, ?_⟩
  rw [map_smul]
  exact hy

theorem exists_smul_subset_dualLat (hO : IsOpen (Set.range (algebraMap O (FractionRing O))))
    (hT : D.T.FG) {S : Set VT'} (hS : IsCompact S) : ∃ c : O, c ≠ 0 ∧ ∀ f ∈ S, c • f ∈ D.T' := by
  classical
  choose c hc0 hc using exists_smul_mem_dualLat D hT
  have hopen : IsOpen (D.T' : Set VT') := isOpen_dualLat D hO hT
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun v => (fun w : VT' => c v • w) ⁻¹' (D.T' : Set VT'))
    (fun v => hopen.preimage (continuous_const_smul (c v))) (fun f _ => Set.mem_iUnion.2 ⟨f, hc f⟩)
  refine ⟨∏ v ∈ t, c v, Finset.prod_ne_zero_iff.2 fun v _ => hc0 v, fun f hf => ?_⟩
  obtain ⟨v, hv, hfv⟩ := Set.mem_iUnion₂.1 (ht hf)
  rw [← Finset.mul_prod_erase t c hv, mul_comm, mul_smul]
  exact D.T'.smul_mem _ hfv

theorem exists_smul_mem_range_j' [CompactSpace G]
    (hO : IsOpen (Set.range (algebraMap O (FractionRing O)))) (hT : D.T.FG) (y : H1 D.ρT') :
    ∃ c : O, c ≠ 0 ∧ c • y ∈ LinearMap.range D.j' := by
  induction y using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨c, hc0, hc⟩ := exists_smul_subset_dualLat D hO hT (isCompact_range z.2.1)
    let z' : Z1 D.ρTl' := ⟨fun g => ⟨c • z.1 g, hc _ ⟨g, rfl⟩⟩,
      Continuous.subtype_mk (z.2.1.const_smul c) _, fun g h => by
        apply Subtype.ext
        show c • z.1 (g * h) = c • z.1 g + D.ρT' g (c • z.1 h)
        rw [z.2.2 g h, map_smul, smul_add]⟩
    refine ⟨c, hc0, Submodule.Quotient.mk z', ?_⟩
    rw [← Submodule.Quotient.mk_smul]
    rfl

end

end GlobalTheory.ContCocycleDualLattice

namespace GlobalTheory

open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC

theorem jSpan_holds : ReciprocityTheory.ChartRestriction.T2.JSpan := by
  intro p _ K O _ _ _ _ _ _ _ VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ G _ _ _ hF i D hD y
  haveI : IsGalois K (PadicAlgCl p) := by
    have : IsGalois ℚ_[p] (PadicAlgCl p) := inferInstance
    infer_instance
  haveI : CompactSpace (Formalism.GaloisCohomology.GK p K) := inferInstance
  haveI : CompactSpace G := i.symm.surjective.compactSpace i.symm.continuous
  exact ContCocycleDualLattice.exists_smul_mem_range_j' D hF.emb.isOpen_range hD.lat.1 y

end GlobalTheory
end

