module

public import ReciprocityTheory.GroupCohomology.Bundle0003
public import ReciprocityTheory.GroupCohomology.ConnNatHolds
public import ReciprocityTheory.GroupCohomology.FinGen
public import ReciprocityTheory.GroupCohomology.Bundle0002
public import Mathlib
public import ReciprocityTheory.GroupCohomology.Bundle0001
public import ReciprocityTheory.GroupCohomology.Bundle0004
public import ReciprocityTheory.GroupCohomology.PrismOpZeroEval
public import ReciprocityTheory.GroupCohomology.Bundle0006
public import ReciprocityTheory.GroupCohomology.PartialProdCoe

@[expose] public section

-- bundled from ReciprocityTheory.GroupCohomology.RankLen
section
namespace ReciprocityTheory.Coh

open Cx Function TorsionRankLength
open scoped Pointwise

universe u

theorem alt_sum_telescope (a : ℕ → ℤ) (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), (-1 : ℤ) ^ n * (a n + a (n + 1)) = a 0 + (-1) ^ N * a (N + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, ih, pow_succ]
    ring

theorem rankLen_holds : RankLenStatement.{u} := by
  intro R _ _ _ t ht L C i p m N hi hses hfg
  obtain ⟨⟨δ, hconn, hles⟩, -⟩ := lES_holds R L L C i p hses
  have hiH : ∀ n, i.H n = (t ^ m) • (LinearMap.id : L.H n →ₗ[R] L.H n) := by
    intro n
    refine LinearMap.ext fun x => ?_
    obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    simp only [LinearMap.smul_apply, LinearMap.id_apply]
    rw [Cx.Hom.H, Submodule.mapQ_apply, ← Submodule.Quotient.mk_smul]
    congr 1
    apply Subtype.ext
    exact hi n z.1
  have hrange : ∀ n, LinearMap.range (i.H n) = (t ^ m) • (⊤ : Submodule R (L.H n)) := by
    intro n
    ext x
    rw [hiH, LinearMap.mem_range, Submodule.mem_smul_pointwise_iff_exists]
    simp
  have hlen : ∀ n, Module.length R (C.H n) =
      Module.length R (QuotSMulTop (t ^ m) (L.H n)) + Module.length R (K (L.H (n + 1)) (t ^ m)) := by
    intro n
    have hexs : Function.Exact (LinearMap.ker (δ n)).subtype (δ n).rangeRestrict := by
      intro y
      constructor
      · intro hy
        refine ⟨⟨y, ?_⟩, rfl⟩
        rw [LinearMap.mem_ker]
        have := congrArg Subtype.val hy
        simpa using this
      · rintro ⟨z, rfl⟩
        apply Subtype.ext
        simpa using z.2
    rw [Module.length_eq_add_of_exact _ _ (LinearMap.ker (δ n)).injective_subtype
      (LinearMap.surjective_rangeRestrict _) hexs]
    congr 1
    · rw [LinearMap.exact_iff.1 (hles.exC n), ← (LinearMap.quotKerEquivRange (p.H n)).length_eq,
        LinearMap.exact_iff.1 (hles.exB n), hrange]
      try rfl
    · rw [← LinearMap.exact_iff.1 (hles.exA n), hiH]
  have hfin : ∀ n, Module.Finite R (L.H n) := hfg.1
  have hq := fun n => @len_quot_eq R _ _ _ (L.H n) _ _ (hfin n) t ht m
  have hKfin : ∀ n, Module.length R (K (L.H n) (t ^ m)) ≠ ⊤ :=
    fun n => ne_top_of_le_ne_top (hq n).2.2 (hq n).2.1
  obtain ⟨kk, hkk⟩ : ∃ kk : ℕ → ℕ, kk = fun n => (Module.length R (K (L.H n) (t ^ m))).toNat := ⟨_, rfl⟩
  obtain ⟨rr, hrr⟩ : ∃ rr : ℕ → ℕ, rr = fun n => Module.finrank R (L.H n) := ⟨_, rfl⟩
  have hKn : ∀ n, Module.length R (K (L.H n) (t ^ m)) = (kk n : ℕ∞) := by
    intro n; rw [hkk]; exact (ENat.coe_toNat (hKfin n)).symm
  have hCn : ∀ n, Module.length R (C.H n) = ((m * rr n + kk n + kk (n + 1) : ℕ) : ℕ∞) := by
    intro n
    rw [hlen, (hq n).1, hKn, hKn, hrr]
    push_cast
    ring
  have hCnat : ∀ n, (Module.length R (C.H n)).toNat = m * rr n + kk n + kk (n + 1) := by
    intro n; rw [hCn, ENat.toNat_coe]
  have hzero : ∀ n, N < n → kk n = 0 ∧ rr n = 0 := by
    intro n hn
    haveI := hfg.2 n hn
    refine ⟨?_, ?_⟩
    · have h0 : Module.length R (K (L.H n) (t ^ m)) = 0 := Module.length_eq_zero_iff.2 inferInstance
      rw [hKn] at h0
      exact_mod_cast h0
    · rw [hrr]; exact Module.finrank_zero_of_subsingleton
  have hk0 : kk 0 = 0 := by
    have hker : K (L.H 0) (t ^ m) = ⊥ := by
      show LinearMap.ker ((t ^ m) • (LinearMap.id : L.H 0 →ₗ[R] L.H 0)) = ⊥
      rw [← hiH]
      exact LinearMap.ker_eq_bot.2 hles.inj
    have h0 : Module.length R (K (L.H 0) (t ^ m)) = 0 := by
      rw [hker]; exact Module.length_eq_zero_iff.2 inferInstance
    rw [hKn] at h0
    exact_mod_cast h0
  refine ⟨⟨fun n => Module.length_ne_top_iff.1 (by rw [hCn]; exact ENat.coe_ne_top _), fun n hn => ?_⟩,
    ?_, fun n => ⟨?_, ?_⟩⟩
  · apply (Module.length_eq_zero_iff (R := R)).1
    rw [hCn, (hzero n hn).1, (hzero n hn).2, (hzero (n + 1) (by omega)).1]
    simp
  · unfold Cx.chi Cx.chiRk
    simp_rw [hCnat]
    have hterm : ∀ n, (-1 : ℤ) ^ n * ((m * rr n + kk n + kk (n + 1) : ℕ) : ℤ) =
        (m : ℤ) * ((-1) ^ n * (Module.finrank R (L.H n) : ℤ)) + (-1) ^ n * ((kk n : ℤ) + kk (n + 1)) := by
      intro n; rw [hrr]; push_cast; ring
    rw [Finset.sum_congr rfl (fun n _ => hterm n), Finset.sum_add_distrib, ← Finset.mul_sum,
      alt_sum_telescope (fun n => (kk n : ℤ)) N, hk0, (hzero (N + 1) (by omega)).1]
    simp
  · rw [hCnat]
    have h1 : kk n ≤ (Module.length R (Submodule.torsion R (L.H n))).toNat := by
      rw [hkk]; exact ENat.toNat_le_toNat (hq n).2.1 (hq n).2.2
    have h2 : kk (n + 1) ≤ (Module.length R (Submodule.torsion R (L.H (n + 1)))).toNat := by
      rw [hkk]; exact ENat.toNat_le_toNat (hq (n + 1)).2.1 (hq (n + 1)).2.2
    rw [hrr] at *
    simp only at h1 h2 ⊢
    omega
  · rw [hCnat, hrr]
    simp only
    omega

end ReciprocityTheory.Coh
end

-- bundled from ReciprocityTheory.GroupCohomology.ResNormalHolds
section
namespace ReciprocityTheory.Coh

open ReciprocityTheory.Gal Cx Function CohomologyFunctoriality₂

universe u

theorem cor_holds : CorStatement.{u} := by
  intro R _ G _ _ _ M U _ hU
  obtain ⟨A, eA, hA⟩ := homogExists_holds R U (M.resSub U) G
  obtain ⟨eG, hG, hG1, hG2⟩ := homogIso_holds R G M
  obtain ⟨eU, hU0, hU1, hU2⟩ := homogIso_holds R U (M.resSub U)
  have P1 := prism_holds R U (M.resSub U) G U A (M.resSub U).coch eA eU hA hU0
  obtain ⟨φr, hφr⟩ := P1.1 (retr U) (continuous_retr U hU) (fun g x => retr_mul U g x)
  have P2 := prism_holds R U (M.resSub U) G G A A eA eA hA hA
  have ha : Continuous fun g : G => (retr U g : G) := continuous_subtype_val.comp (continuous_retr U hU)
  have hae : ∀ (g : U) (x : G), (retr U (g • x) : G) = g • (retr U x : G) := fun g x => by
    show (retr U ((g : G) * x) : G) = (g : G) * (retr U x : G)
    rw [retr_mul]; rfl
  obtain ⟨T, hT⟩ := P2.1 _ ha hae
  have hTid : ∀ n, T.H n = (Hom.id A).H n :=
    P2.2 _ id T (Hom.id A) ha continuous_id hae (fun _ _ => rfl) hT (fun _ _ _ => rfl)
  set N := normCx A eA hA eG hG
  set ι := inclCx A eA hA eG hG
  refine ⟨N.comp φr, ?_, ?_⟩
  · intro n f
    funext g
    rw [hG2 n _ g]
    show (eG n (N.f n (φr.f n f))).1 _ = _
    rw [normCx_spec]
    unfold normF corFun
    refine finsum_congr fun c => ?_
    congr 1
    rw [hφr, hU1]
    simp only [Fin.partialProd_zero, mul_one, retr_out, map_one, Module.End.one_apply]
    rfl
  · have hcomp : ∀ n f, (N.comp φr).f n ((Pair.res M U.subtype continuous_subtype_val).hom.f n f) =
        (N.comp (T.comp ι)).f n f := by
      intro n f
      apply (eG n).injective
      apply Subtype.ext
      show (eG n (N.f n _)).1 = (eG n (N.f n _)).1
      rw [normCx_spec, normCx_spec]
      funext x
      unfold normF
      refine finsum_congr fun c => ?_
      congr 1
      show (eA n (φr.f n _)).1 _ = (eA n (T.f n (ι.f n f))).1 _
      rw [hφr, hT, inclCx_spec, hU1, hG1]
      rfl
    have hNι : ∀ n f, (N.comp ι).f n f = U.index • f := by
      intro n f
      classical
      haveI : Fintype (Quotient (QuotientGroup.rightRel U)) := Fintype.ofFinite _
      apply (eG n).injective
      apply Subtype.ext
      rw [map_nsmul]
      show (eG n (N.f n (ι.f n f))).1 = _
      rw [normCx_spec]
      funext x
      refine (normF_eq M U n _ x).trans ?_
      have h1 : ∀ c : Quotient (QuotientGroup.rightRel U),
          M.rho c.out⁻¹ ((eA n (ι.f n f)).1 fun i => c.out * x i) = (eG n f).1 x := by
        intro c
        rw [inclCx_spec]
        have := (eG n f).2.2 c.out x
        simp only [smul_eq_mul] at this
        rw [this, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      simp only [h1, Finset.sum_const, Finset.card_univ, card_rightRel]
      rfl
    intro n x
    calc (N.comp φr).H n ((Pair.res M U.subtype continuous_subtype_val).hom.H n x)
        = ((N.comp φr).comp (Pair.res M U.subtype continuous_subtype_val).hom).H n x :=
          (Hom.H_comp _ _ n x).symm
      _ = (N.comp (T.comp ι)).H n x := by
          rw [Hom.H_congr _ _ (fun n f => hcomp n f)]
      _ = N.H n (T.H n (ι.H n x)) := by rw [Hom.H_comp, Hom.H_comp]
      _ = N.H n (ι.H n x) := by rw [hTid, Hom.H_id]
      _ = (N.comp ι).H n x := (Hom.H_comp _ _ n x).symm
      _ = U.index • x := Hom.H_nsmul _ _ n (hNι n) x

end ReciprocityTheory.Coh
end

