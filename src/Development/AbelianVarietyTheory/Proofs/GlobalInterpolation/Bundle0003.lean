module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsEquivariantProjOfLeSumIrreducible
section
open CategoryTheory
open scoped ContDiff Matrix

namespace GlobalTheory.BorelCoh

theorem exists_equivariant_proj_of_le_sum_irreducible {M O : Type} [AddCommGroup M] [Module ℂ M]
    (act : O → Module.End ℂ M) (V : Submodule ℂ M) (hVst : ∀ o, ∀ x ∈ V, act o x ∈ V)
    (hV : V ≤ ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) :
    ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧
      (∀ x, p x ∈ V) ∧ (∀ x ∈ V, p x = x) := by
  set Wt := ⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W with hWt
  have hst_sup : ∀ A B : Submodule ℂ M, (∀ o, ∀ x ∈ A, act o x ∈ A) → (∀ o, ∀ x ∈ B, act o x ∈ B) →
      ∀ o, ∀ x ∈ A ⊔ B, act o x ∈ A ⊔ B := by
    intro A B hA hB o x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hA o y hy) (hB o z hz)

  let s : Set (Submodule ℂ M) := {C | (∀ o, ∀ x ∈ C, act o x ∈ C) ∧ C ≤ Wt ∧ Disjoint V C}
  obtain ⟨C, -, ⟨hCst, hCW, hCd⟩, hCmax⟩ := zorn_le_nonempty₀ s (by
    intro c hcs hc y hy
    have hne : c.Nonempty := ⟨y, hy⟩
    have hdir : DirectedOn (· ≤ ·) c := hc.directedOn
    refine ⟨sSup c, ⟨?_, sSup_le fun z hz => (hcs hz).2.1, ?_⟩, fun z hz => le_sSup hz⟩
    · intro o x hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.mem_sSup_of_directed hne hdir).2 ⟨z, hz, (hcs hz).1 o x hxz⟩
    · rw [Submodule.disjoint_def]
      intro x hxV hx
      obtain ⟨z, hz, hxz⟩ := (Submodule.mem_sSup_of_directed hne hdir).1 hx
      exact (Submodule.disjoint_def.1 (hcs hz).2.2) x hxV hxz) ⊥
    ⟨fun o x hx => by rw [Submodule.mem_bot] at hx ⊢; rw [hx, map_zero], bot_le, disjoint_bot_right⟩

  have hWle : Wt ≤ V ⊔ C := by
    refine iSup₂_le fun S hS => ?_
    obtain ⟨hSst, hSne, hSmin⟩ := hS
    have hinst : ∀ o, ∀ x ∈ S ⊓ (V ⊔ C), act o x ∈ S ⊓ (V ⊔ C) := fun o x hx =>
      ⟨hSst o x hx.1, hst_sup V C hVst hCst o x hx.2⟩
    rcases hSmin _ inf_le_left hinst with h | h
    · have hSW : S ≤ Wt := le_iSup₂_of_le S ⟨hSst, hSne, hSmin⟩ le_rfl
      have hmem : C ⊔ S ∈ s := ⟨hst_sup C S hCst hSst, sup_le hCW hSW,
        Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (by rw [disjoint_comm, disjoint_iff]; exact h)⟩
      exact (le_sup_right.trans (hCmax hmem le_sup_left)).trans le_sup_right
    · exact h ▸ inf_le_right
  have hW : Wt = V ⊔ C := le_antisymm hWle (sup_le hV hCW)
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl Wt
  have hc : IsCompl V (C ⊔ D) := by
    constructor
    · exact Disjoint.disjoint_sup_right_of_disjoint_sup_left hCd (hW ▸ hD.disjoint)
    · rw [codisjoint_iff, ← sup_assoc, ← hW, hD.sup_eq_top]
  have hl : ∀ v ∈ V, (V.linearProjOfIsCompl (C ⊔ D) hc v : M) = v := fun v hv =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨v, hv⟩)
  have hr : ∀ w ∈ C ⊔ D, V.linearProjOfIsCompl (C ⊔ D) hc w = 0 := fun w hw =>
    Submodule.linearProjOfIsCompl_apply_right hc ⟨w, hw⟩
  refine ⟨V.subtype ∘ₗ V.linearProjOfIsCompl (C ⊔ D) hc, ?_, fun x => (V.linearProjOfIsCompl _ hc x).2, hl⟩
  intro o x hx
  rw [hW] at hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  have hz' : z ∈ C ⊔ D := Submodule.mem_sup_left hz
  have hz'' : act o z ∈ C ⊔ D := Submodule.mem_sup_left (hCst o z hz)
  show (V.linearProjOfIsCompl _ hc (act o (y + z)) : M) = act o (V.linearProjOfIsCompl _ hc (y + z))
  rw [map_add (f := _), map_add (f := _), map_add (f := _), hr _ hz'', hr _ hz', add_zero, add_zero, hl _ (hVst o y hy), hl _ hy]

theorem exists_equivariant_proj_of_irreducible_family : ∀ (M O ι : Type) [AddCommGroup M] [Module ℂ M] [Fintype ι] [DecidableEq ι] (act : O → Module.End ℂ M) (V : ι → Submodule ℂ M), (∀ i o, ∀ x ∈ V i, act o x ∈ V i) → (∀ i, V i ≠ ⊥) → (∀ i (W : Submodule ℂ M), W ≤ V i → (∀ o, ∀ x ∈ W, act o x ∈ W) → W = ⊥ ∨ W = V i) → (∀ i j, i ≠ j → ∀ f : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ V i, f (act o x) = act o (f x)) → (∀ x ∈ V i, f x ∈ V j) → ∀ x ∈ V i, f x = 0) → ∀ i, ∃ p : M →ₗ[ℂ] M, (∀ o, ∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p (act o x) = act o (p x)) ∧ (∀ x ∈ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W), p x ∈ V i) ∧ (∀ x ∈ V i, p x = x) ∧ ∀ j, j ≠ i → ∀ x ∈ V j, p x = 0 := by
  intro M O ι _ _ _ _ act V h1 h2 h3 h4 i
  have hirr : ∀ j, V j ≤ (⨆ (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧ ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W), W) := fun j =>
    le_iSup₂_of_le (f := fun (W : Submodule ℂ M) (_ : (∀ o, ∀ x ∈ W, act o x ∈ W) ∧ W ≠ ⊥ ∧
      ∀ W' ≤ W, (∀ o, ∀ x ∈ W', act o x ∈ W') → W' = ⊥ ∨ W' = W) => W) (V j) ⟨h1 j, h2 j, h3 j⟩ le_rfl
  obtain ⟨p, hpe, hpV, hpid⟩ := exists_equivariant_proj_of_le_sum_irreducible act (V i) (h1 i) (hirr i)
  exact ⟨p, hpe, fun x _ => hpV x, hpid,
    fun j hji x hx => h4 j i hji p (fun o y hy => hpe o y (hirr j hy)) (fun y _ => hpV y) x hx⟩

end GlobalTheory.BorelCoh
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfAddCharNeOne
section
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_addChar_ne_one :
    ∀ (R K : Type) [CommRing R] [Field K] (p : ℕ), p.Prime → (p : R) = 0 →
      ∀ ψ : AddChar R K, ψ ≠ 1 → ∃ ζ : K, IsPrimitiveRoot ζ p := by
  intro R K _ _ p hp hpR ψ hψ
  obtain ⟨x, hx⟩ := AddChar.ne_one_iff.mp hψ
  have hpow : ψ x ^ p = 1 := by
    rw [← AddChar.map_nsmul_eq_pow, nsmul_eq_mul, hpR, zero_mul, AddChar.map_zero_eq_one]
  haveI : Fact p.Prime := ⟨hp⟩
  have hord : orderOf (ψ x) = p := orderOf_eq_prime hpow hx
  exact ⟨ψ x, hord ▸ IsPrimitiveRoot.orderOf (ψ x)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsIsPrimitiveRootOfInjectiveCharacter
section
namespace GlobalTheory

theorem exists_isPrimitiveRoot_of_injective_character (K : Type) [Field K] (p : ℕ) (hp : p.Prime)
    (om : (ZMod p)ˣ →* Kˣ) (hom : Function.Injective om) :
    ∃ ζ : K, IsPrimitiveRoot ζ (p - 1) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod p)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  refine ⟨(om g : K), ?_⟩
  rw [IsPrimitiveRoot.coe_units_iff, ← hg, ← orderOf_injective om hom g]
  exact IsPrimitiveRoot.orderOf _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsMultiplicativeLiftCharZero
section
namespace GlobalTheory

theorem charZero_wittVector_of_field (p : ℕ) [hp : Fact p.Prime] (K : Type) [Field K] [CharP K p] :
    CharZero (WittVector p K) := by
  obtain ⟨l, hl⟩ := CharP.exists (WittVector p K)
  rcases CharP.char_is_prime_or_zero (WittVector p K) l with h | h
  · exfalso
    have h1 : ((l : ℕ) : WittVector p K) = 0 := CharP.cast_eq_zero _ l
    have h2 : ((l : ℕ) : K) = 0 := by
      have := congrArg (WittVector.constantCoeff : WittVector p K →+* K) h1
      rwa [map_natCast, map_zero] at this
    have h3 : p ∣ l := (CharP.cast_eq_zero_iff K p l).1 h2
    have h4 : p = l := (Nat.prime_dvd_prime_iff_eq hp.out h).1 h3
    subst h4
    exact WittVector.p_nonzero p K h1
  · subst h
    exact CharP.charP_to_charZero _

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsProdAbsSubGeOnSegment
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology Polynomial

namespace GlobalTheory


open Polynomial in
theorem exists_prod_abs_sub_ge_on_segment : ∀ (N : ℕ) (x : Fin N → ℝ) (a δ : ℝ), 0 < δ →
    ∃ r : ℝ, a ≤ r ∧ r ≤ a + δ ∧ (δ / (2 * Real.exp 1)) ^ N ≤ ∏ i, |r - x i| := by
  intro N x a δ hδ
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · exact ⟨a, le_rfl, by linarith, by simp⟩
  by_contra hcon
  push Not at hcon
  have he : (2 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
  have he0 : (0 : ℝ) < Real.exp 1 := by linarith
  set m : ℝ := δ / (2 * Real.exp 1) with hm
  have hm0 : 0 < m := by positivity
  let P : ℝ[X] := ∏ i : Fin N, (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
  have hlc : P.leadingCoeff = Real.exp 1 ^ N := by
    simp only [P, leadingCoeff_prod, leadingCoeff_linear he0.ne']
    simp
  have hdeg : P.degree ≤ N := by
    have : P.degree = ∑ _i : Fin N, (1 : WithBot ℕ) := by
      simp only [P, degree_prod, degree_linear he0.ne']
    rw [this]; simp
  have hb : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |P.eval t| ≤ 1 := by
    intro t ht
    have h1 := hcon (a + δ / 2 + δ / 2 * t) (by nlinarith [ht.1]) (by nlinarith [ht.2])
    have h2 : |P.eval t| = (∏ i, |a + δ / 2 + δ / 2 * t - x i|) / m ^ N := by
      simp only [P, eval_prod, Finset.abs_prod]
      have : ∀ i : Fin N, |eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))|
          = |a + δ / 2 + δ / 2 * t - x i| / m := by
        intro i
        have : eval t (C (Real.exp 1) * X + C ((a + δ / 2 - x i) / m))
            = (a + δ / 2 + δ / 2 * t - x i) / m := by
          simp only [eval_add, eval_mul, eval_C, eval_X, hm]
          field_simp
          ring
        rw [this, abs_div, abs_of_pos hm0]
      simp only [this, Finset.prod_div_distrib]
      simp
    rw [h2, div_le_one (by positivity)]
    exact h1.le
  have h3 := Polynomial.Chebyshev.leadingCoeff_le_of_forall_abs_le_one hdeg hb
  rw [hlc] at h3
  have h4 : (2 : ℝ) ^ (N - 1) ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (Nat.sub_le _ _)
  have h5 : (2 : ℝ) ^ N < Real.exp 1 ^ N := pow_lt_pow_left₀ he (by norm_num) hN.ne'
  linarith

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteOfFiniteQuotMapOfIsPrecomplete
section
open IsLocalRing

namespace GlobalTheory

theorem nak_mem_smul_top_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (J : Ideal R) (x : ι → R) :
    x ∈ J • (⊤ : Submodule R (ι → R)) ↔ ∀ i, x i ∈ J := by
  constructor
  · intro hx
    refine Submodule.smul_induction_on (p := fun x => ∀ i, x i ∈ J) hx ?_ ?_
    · intro a ha m _ i; exact J.mul_mem_right _ ha
    · intro a b ha hb i; exact J.add_mem (ha i) (hb i)
  · intro hx
    rw [show x = ∑ i, x i • Pi.single i (1 : R) by
      ext j; simp [Finset.sum_apply, Pi.single_apply]]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hx i) Submodule.mem_top

theorem nak_isPrecomplete_pi {R : Type} [CommRing R] {ι : Type} [Fintype ι] [DecidableEq ι]
    (I : Ideal R) [IsPrecomplete I R] : IsPrecomplete I (ι → R) := by
  have key : ∀ k (x : ι → R), x ∈ I ^ k • (⊤ : Submodule R (ι → R)) ↔
      ∀ i, x i ∈ I ^ k • (⊤ : Submodule R R) := by
    intro k x
    rw [nak_mem_smul_top_pi]
    simp only [smul_eq_mul, Ideal.mul_top]
  refine ⟨fun f hf => ?_⟩
  have hc : ∀ i, ∃ l : R, ∀ n, f n i ≡ l [SMOD (I ^ n • ⊤ : Submodule R R)] := by
    intro i
    refine IsPrecomplete.prec' (fun n => f n i) fun {m n} hmn => ?_
    have := (hf hmn)
    rw [SModEq.sub_mem] at this ⊢
    exact (key m _).1 this i
  choose l hl using hc
  refine ⟨l, fun n => ?_⟩
  rw [SModEq.sub_mem, key]
  intro i
  exact SModEq.sub_mem.1 (hl i n)

theorem finite_of_finite_quot_map_of_isPrecomplete :
    ∀ (O A : Type) [CommRing O] [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [Algebra O A]
      (J : Ideal O) [IsPrecomplete J O], J.map (algebraMap O A) ≠ ⊤ →
      Module.Finite O (A ⧸ J.map (algebraMap O A)) → Module.Finite O A := by
  intro O A _ _ _ _ _ J _ hJ hfin
  have hsm : ∀ n : ℕ, (J ^ n • (⊤ : Submodule O A)) =
      Submodule.restrictScalars O ((J.map (algebraMap O A)) ^ n) := by
    intro n
    rw [Ideal.smul_top_eq_map, Ideal.map_pow]
  have hH : IsHausdorff J A := by
    refine ⟨fun x hx => ?_⟩
    have : x ∈ ⨅ n : ℕ, (J.map (algebraMap O A)) ^ n := by
      rw [Submodule.mem_iInf]
      intro n
      have h1 := SModEq.sub_mem.1 (hx n)
      rw [sub_zero, hsm n] at h1
      exact h1
    rw [Ideal.iInf_pow_eq_bot_of_isLocalRing _ hJ] at this
    exact this
  set I := J.map (algebraMap O A) with hI
  obtain ⟨r, s, hs⟩ := Module.Finite.exists_fin (R := O) (M := A ⧸ I)
  choose s' hs' using fun i => Ideal.Quotient.mk_surjective (s i)
  have : IsPrecomplete J (Fin r → O) := nak_isPrecomplete_pi _
  have hsurj : Function.Surjective ((J • (⊤ : Submodule O A)).mkQ ∘ₗ
      Fintype.linearCombination O s') := by
    intro y
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    have hx : (Ideal.Quotient.mk I x) ∈ Submodule.span O (Set.range s) := by
      rw [hs]; exact Submodule.mem_top
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun O).1 hx
    refine ⟨c, ?_⟩
    have hq : Ideal.Quotient.mk I (Fintype.linearCombination O s' c) = Ideal.Quotient.mk I x := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [Fintype.linearCombination_apply, map_sum, ← hc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Algebra.smul_def, map_mul, ← hs' i, Algebra.smul_def]
      rfl
    have hmem : Fintype.linearCombination O s' c - x ∈ I := by
      rw [← Ideal.Quotient.eq]; exact hq
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply]
    rw [Submodule.Quotient.eq]
    have h1 := hsm 1
    simp only [pow_one] at h1
    rw [h1]
    exact hmem
  exact Module.Finite.of_surjective _ (surjective_of_mkQ_comp_surjective hsurj)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FinitePointsDetect
section
namespace GlobalTheory.FinitePointsDetect

theorem finite_points_detect : ∀ {X : Type} (W : Submodule ℂ (X → ℂ)) [FiniteDimensional ℂ ↥W],
    ∃ (s : Finset X), ∀ (v : ↥W), (∀ x ∈ s, (↑v : X → ℂ) x = (0 : ℂ)) → v = (0 : ↥W) := by
  intro X W _
  classical
  let ev : X → (W →ₗ[ℂ] ℂ) := fun x => (LinearMap.proj x).comp W.subtype
  let K : Finset X → Submodule ℂ W := fun s => ⨅ x ∈ s, LinearMap.ker (ev x)
  obtain ⟨_, ⟨s, rfl⟩, hs⟩ :=
    (wellFounded_lt (α := Submodule ℂ W)).has_min (Set.range K) ⟨K ∅, ∅, rfl⟩
  have key : ∀ v ∈ K s, ∀ y : X, (↑v : X → ℂ) y = 0 := by
    intro v hv y
    have hle : K (insert y s) ≤ K s := by
      intro w hw
      simp only [K, Submodule.mem_iInf] at hw ⊢
      intro x hx
      exact hw x (Finset.mem_insert_of_mem hx)
    have heq : K (insert y s) = K s := eq_of_le_of_not_lt hle (hs _ ⟨_, rfl⟩)
    rw [← heq] at hv
    simp only [K, Submodule.mem_iInf] at hv
    have := hv y (Finset.mem_insert_self y s)
    simpa [ev] using this
  refine ⟨s, fun v hv => ?_⟩
  have hvK : v ∈ K s := by
    simp only [K, Submodule.mem_iInf]
    intro x hx
    simpa [ev] using hv x hx
  apply Subtype.ext
  funext y
  simpa using key v hvK y

end GlobalTheory.FinitePointsDetect
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmForm
section
open MeasureTheory FourierTransform

namespace GlobalTheory


open MeasureTheory FourierTransform in
theorem _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (T : V ≃L[ℝ] E) (μ : Measure V) [μ.IsAddHaarMeasure] :
    ∃ a : ℝ, 0 < a ∧ (∀ g : E → ℂ, ∫ x, g (T x) ∂μ = (a : ℂ) * ∫ w, g w) ∧
      ∀ g : E → ℂ, Integrable (fun x => g (T x)) μ ↔ Integrable g := by
  let e : V ≃ᵐ E := T.toHomeomorph.toMeasurableEquiv
  have : (μ.map e).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  set c := (μ.map e).addHaarScalarFactor volume
  have hpos : 0 < c := Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _
  have hmap : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, hpos, fun g => ?_, fun g => ?_⟩
  · change ∫ x, g (e x) ∂μ = _
    rw [← integral_map_equiv e, hmap, integral_smul_nnreal_measure]
    simp [NNReal.smul_def, Complex.real_smul]
  · change Integrable (g ∘ e) μ ↔ _
    rw [← integrable_map_equiv e, hmap,
      show c • (volume : Measure E) = (c : ENNReal) • volume from rfl, integrable_smul_measure]
    · simpa using hpos.ne'
    · simp


open MeasureTheory FourierTransform in
theorem _root_.GlobalTheory.exists_equiv_inner_eq_form {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (T : V ≃L[ℝ] E) (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ)
    (hs : ∀ x y, B x y = B y x) (hn : ∀ x, (∀ y, B x y = 0) → x = 0) :
    ∃ R : V ≃L[ℝ] E, ∀ x y, B x y = inner ℝ (T x) (R y) := by
  let φ : V → StrongDual ℝ E := fun y =>
    LinearMap.toContinuousLinearMap ((B.flip y).comp (T.symm : E →L[ℝ] V).toLinearMap)
  have hφ : ∀ y e, φ y e = B (T.symm e) y := fun _ _ => rfl
  let L : V →ₗ[ℝ] E :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ E).symm (φ y)
      map_add' := fun y z => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ]
      map_smul' := fun r y => by
        apply (InnerProductSpace.toDual ℝ E).injective
        ext e
        simp [hφ] }
  have hL : ∀ x y, inner ℝ (T x) (L y) = B x y := by
    intro x y
    rw [real_inner_comm]
    change inner ℝ ((InnerProductSpace.toDual ℝ E).symm (φ y)) (T x) = _
    rw [InnerProductSpace.toDual_symm_apply, hφ, T.symm_apply_apply]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hn y
    intro x
    rw [hs, ← hL, hy, inner_zero_right]
  have hdim : Module.finrank ℝ V = Module.finrank ℝ E := T.toLinearEquiv.finrank_eq
  refine ⟨(LinearMap.linearEquivOfInjective L hinj hdim).toContinuousLinearEquiv, fun x y => ?_⟩
  rw [← hL]
  rfl


open MeasureTheory FourierTransform in
theorem _root_.GlobalTheory.fourier_inversion_haar_symm_form :
    ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] (B : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ x y, B x y = B y x) → (∀ x, (∀ y, B x y = 0) → x = 0) → ∀ μ : Measure V, μ.IsAddHaarMeasure → (∃ c : ℝ, 0 < c ∧ ∀ Φ : V → ℂ, Continuous Φ → Integrable Φ μ → Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ → ∀ z, ∫ y, (∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) * Complex.exp (2 * Real.pi * Complex.I * ((B y z : ℝ) : ℂ)) ∂μ = (c : ℂ) * Φ (-z)) ∧ ∀ Φ : SchwartzMap V ℂ, Integrable (⇑Φ) μ ∧ Integrable (fun y => ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ) μ := by
  intro V _ _ _ _ _ B hs hn μ hμ
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  let T : V ≃L[ℝ] E := (LinearEquiv.ofFinrankEq V E (by simp [E])).toContinuousLinearEquiv
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.exists_equiv_inner_eq_form T B hs hn
  obtain ⟨a, ha, hint, hintg⟩ := _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar T μ
  obtain ⟨b, hb, hint', hintg'⟩ := _root_.GlobalTheory.exists_pos_integral_comp_equiv_haar R μ
  have hF : ∀ (g : E → ℂ) w, 𝓕⁻ g w =
      ∫ v, g v * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ v w : ℝ) : ℂ)) := by
    intro g w
    rw [Real.fourierInv_eq']
    congr 1
    ext v
    rw [smul_eq_mul, mul_comm]
    congr 2
    push_cast
    ring
  have key : ∀ (Φ : V → ℂ) y, ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ
      = a * 𝓕⁻ (fun w => Φ (T.symm w)) (R y) := by
    intro Φ y
    rw [hF, ← hint]
    simp only [hR, ContinuousLinearEquiv.symm_apply_apply]
  have hFF : ∀ g : E → ℂ, Continuous g → Integrable g → Integrable (𝓕⁻ g) → ∀ w,
      𝓕⁻ (𝓕⁻ g) w = g (-w) := by
    intro g hc hg hg' w
    have h1 : 𝓕 g = fun w => 𝓕⁻ g (-w) := by
      ext w
      rw [Real.fourierInv_eq_fourier_neg, neg_neg]
    have h2 : Integrable (𝓕 g) := by
      rw [h1]
      exact hg'.comp_neg
    rw [Real.fourierInv_eq_fourier_neg, hc.fourier_fourierInv_eq hg h2]
  refine ⟨⟨a * b, mul_pos ha hb, fun Φ hc hΦ hI z => ?_⟩, fun Φ => ?_⟩
  · set g : E → ℂ := fun w => Φ (T.symm w) with hg
    have hgc : Continuous g := hc.comp T.symm.continuous
    have hgi : Integrable g := by
      rw [← hintg]
      simpa [g] using hΦ
    have hgi' : Integrable (𝓕⁻ g) := by
      rw [← hintg']
      have := hI.const_mul ((a : ℂ)⁻¹)
      refine this.congr (Filter.Eventually.of_forall fun y => ?_)
      dsimp only
      rw [key, ← hg, ← mul_assoc, inv_mul_cancel₀ (by exact_mod_cast ha.ne'), one_mul]
    simp only [key Φ, ← hg]
    have hB : ∀ y, B y z = inner ℝ (R y) (T z) := fun y => by rw [hs, hR, real_inner_comm]
    simp only [hB]
    rw [hint' (fun u => (a : ℂ) * 𝓕⁻ g u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ)))]
    simp only [mul_assoc (a : ℂ)]
    rw [integral_const_mul, ← hF, hFF g hgc hgi hgi', hg]
    beta_reduce
    rw [← map_neg T z, ContinuousLinearEquiv.symm_apply_apply]
    push_cast
    ring
  · refine ⟨Φ.integrable, ?_⟩
    let ψ := SchwartzMap.compCLMOfContinuousLinearEquiv ℂ T.symm Φ
    have hψ : (fun w => Φ (T.symm w)) = ⇑ψ := by
      ext w
      simp [ψ]
    simp only [key, hψ, ← SchwartzMap.fourierInv_coe]
    refine Integrable.const_mul ?_ _
    rw [hintg' (⇑(𝓕⁻ ψ : SchwartzMap E ℂ))]
    exact (𝓕⁻ ψ : SchwartzMap E ℂ).integrable

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Imports
section
namespace GlobalTheory.MaximalIdealMembership

theorem mem_maximalIdeal_iff {O : Type} [CommRing O] [IsLocalRing O] {a : ℕ}
    (f : MvPowerSeries (Fin a) O) :
    f ∈ IsLocalRing.maximalIdeal (MvPowerSeries (Fin a) O) ↔
      (MvPowerSeries.constantCoeff : MvPowerSeries (Fin a) O → O) f ∈ IsLocalRing.maximalIdeal O := by
  rw [IsLocalRing.mem_maximalIdeal, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    mem_nonunits_iff, MvPowerSeries.isUnit_iff_constantCoeff]

end GlobalTheory.MaximalIdealMembership
end

