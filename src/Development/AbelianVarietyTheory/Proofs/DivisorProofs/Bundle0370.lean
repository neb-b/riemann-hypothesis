module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0005
public import GroundTheory.AutomorphicForms.GKModules.Casimir
public import GroundTheory.AutomorphicForms.HarishChandraRegularity.ExpHaar
public import GroundTheory.AutomorphicForms.HarishChandraInvariance.Compact
public import GroundTheory.AutomorphicForms.Bundle0015
public import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral
public import GroundTheory.TateCohomology.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0126
public import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RingCocone
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import ReciprocityTheory.ReductiveGroups.Lattices.LatUnrCharA
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0113

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BoundedDerivFunctionalTsumReplicate
section
open GlobalTheory.HCA MeasureTheory GroundTheory.Automorphic
open scoped ContDiff

namespace GlobalTheory.HCA

theorem smFn_tsum_replicate : ∀ (𝔸 : Type) [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸] (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) (h : IsExpLieAlgebra G 𝔤) (d : ℕ) (b : Module.Basis (Fin d) ℝ 𝔤) [MeasurableSpace G] [BorelSpace G] (μ : Measure G), μ.IsHaarMeasure → ∀ (S : Submodule ℂ (G → ℂ)), (∀ f ∈ S, Continuous f) → (∀ f ∈ S, ∀ g, (fun y => f (g * y)) ∈ S) → ∀ K : Set G, IsCompact K → ∀ Λ : List (Fin d) → (G → ℂ) → ℂ, SmFn h b μ S K Λ → ∀ i, ∃ M : ℕ → ℝ, (∀ p, 0 ≤ M p) ∧ (∀ p, ∀ f ∈ S, ‖Λ (List.replicate p i) f‖ ≤ M p * ∫ x in K, ‖f x‖ ∂μ) ∧ ∀ c : ℕ → ℝ, Summable (fun p => |c p| * M p) → SmFn h b μ S K fun l f => ∑' p, (c p : ℂ) * Λ (l ++ List.replicate p i) f := by
  intro 𝔸 _ _ _ _ G 𝔤 h d b _ _ μ hμ S hSc hSL K hK Λ hΛ i
  classical
  haveI := hμ
  choose C0 hC0 using hΛ.bdd
  let C : List (Fin d) → ℝ := fun l => max 0 (C0 l)
  have hC0' : ∀ l, 0 ≤ C l := fun l => le_max_left _ _
  have hC : ∀ l, ∀ f ∈ S, ‖Λ l f‖ ≤ C l * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf
    have hI : 0 ≤ ∫ x in K, ‖f x‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
    exact (hC0 l f hf).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hI)
  let D : ℕ → ℕ → ℝ := fun p k =>
    C (((Encodable.decode k : Option (List (Fin d))).getD []) ++ List.replicate p i)
  let M : ℕ → ℝ := fun p => C (List.replicate p i) + ∑ k ∈ Finset.range (p + 1), D p k
  have hD0 : ∀ p k, 0 ≤ D p k := fun p k => hC0' _
  have hM0 : ∀ p, 0 ≤ M p := fun p => add_nonneg (hC0' _) (Finset.sum_nonneg fun k _ => hD0 p k)
  have hMl : ∀ l : List (Fin d), ∀ p, Encodable.encode l ≤ p → C (l ++ List.replicate p i) ≤ M p := by
    intro l p hp
    have h1 : D p (Encodable.encode l) ≤ ∑ k ∈ Finset.range (p + 1), D p k :=
      Finset.single_le_sum (f := D p) (fun k _ => hD0 p k) (Finset.mem_range.2 (Nat.lt_succ_of_le hp))
    have h2 : D p (Encodable.encode l) = C (l ++ List.replicate p i) := by
      simp only [D, Encodable.encodek, Option.getD_some]
    have h3 := hC0' (List.replicate p i)
    simp only [M]
    linarith
  refine ⟨M, hM0, ?_, ?_⟩
  · intro p f hf
    refine (hC _ f hf).trans (mul_le_mul_of_nonneg_right ?_ (integral_nonneg fun _ => norm_nonneg _))
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun k _ => hD0 p k)
  intro c hc
  have hsum : ∀ l, Summable (fun p => |c p| * C (l ++ List.replicate p i)) := by
    intro l
    refine Summable.of_norm_bounded_eventually_nat hc ?_
    filter_upwards [Filter.eventually_ge_atTop (Encodable.encode l)] with p hp
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (abs_nonneg _) (hC0' _))]
    exact mul_le_mul_of_nonneg_left (hMl l p hp) (abs_nonneg _)
  have hterm : ∀ l, ∀ f ∈ S, ∀ p, ‖(c p : ℂ) * Λ (l ++ List.replicate p i) f‖ ≤
      |c p| * C (l ++ List.replicate p i) * ∫ x in K, ‖f x‖ ∂μ := by
    intro l f hf p
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hC _ f hf) (abs_nonneg _)
  have hsumm : ∀ l, ∀ f ∈ S, Summable (fun p => (c p : ℂ) * Λ (l ++ List.replicate p i) f) :=
    fun l f hf => Summable.of_norm_bounded ((hsum l).mul_right _) (hterm l f hf)
  have hexp0 : h.expG 0 = 1 := by
    apply Subtype.ext; apply Units.ext; simp
  refine ⟨?_, ?_, ?_⟩
  · intro l f hf f' hf' a
    have e : ∀ p, (c p : ℂ) * Λ (l ++ List.replicate p i) (a • f + f') =
        a * ((c p : ℂ) * Λ (l ++ List.replicate p i) f) + (c p : ℂ) * Λ (l ++ List.replicate p i) f' := by
      intro p; rw [hΛ.lin _ f hf f' hf' a]; ring
    simp_rw [e]
    rw [Summable.tsum_add ((hsumm l f hf).mul_left a) (hsumm l f' hf'), tsum_mul_left]
  · intro l
    refine ⟨∑' p, |c p| * C (l ++ List.replicate p i), fun f hf => ?_⟩
    rw [← tsum_mul_right]
    exact tsum_of_norm_bounded ((hsum l).mul_right _).hasSum (hterm l f hf)
  · intro l j f hf
    have hft : ∀ t : ℝ, (fun y => f (h.expG (t • b j) * y)) ∈ S := fun t => hSL f hf _
    have hcont : Continuous fun q : ℝ × G => f (h.expG (q.1 • b j) * q.2) :=
      (hSc f hf).comp ((h.continuous_expG.comp (continuous_fst.smul continuous_const)).mul continuous_snd)
    obtain ⟨A, hA⟩ := ((isCompact_Icc (a := (-1 : ℝ)) (b := 1)).prod hK).exists_bound_of_continuousOn
      hcont.continuousOn
    have hB : ∀ t ∈ Set.Icc (-1 : ℝ) 1, ∫ x in K, ‖f (h.expG (t • b j) * x)‖ ∂μ ≤ max 0 A * μ.real K := by
      intro t ht
      have h1 := norm_setIntegral_le_of_norm_le_const (μ := μ) (C := max 0 A)
        (f := fun x => ‖f (h.expG (t • b j) * x)‖) hK.measure_lt_top (fun x hx => by
          rw [norm_norm]; exact (hA (t, x) ⟨ht, hx⟩).trans (le_max_right _ _))
      exact (Real.le_norm_self _).trans h1
    have hderiv : ∀ (m : List (Fin d)) (t : ℝ), HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG (s • b j) * y))
        (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) t := by
      intro m t
      have h0 := hΛ.der m j _ (hft t)
      have e1 : (fun s : ℝ => Λ m fun y => f (h.expG (t • b j) * (h.expG (s • b j) * y))) =
          fun s => Λ m fun y => f (h.expG ((t + s) • b j) * y) := by
        funext s; congr 1; funext y; rw [h.expG_add_smul, mul_assoc]
      rw [e1] at h0
      have h1 : HasDerivAt (fun s : ℝ => Λ m fun y => f (h.expG ((t + s) • b j) * y))
          (Λ (j :: m) fun y => f (h.expG (t • b j) * y)) (t - t) := by rw [sub_self]; exact h0
      have h2 := h1.comp_sub_const t t
      have e2 : ∀ u : ℝ, t + (u - t) = u := fun u => by ring
      simp only [e2] at h2
      exact h2
    have key := hasDerivAt_tsum_of_isPreconnected (t := Set.Ioo (-1 : ℝ) 1) (y₀ := 0) (y := 0)
      (g := fun p s => (c p : ℂ) * Λ (l ++ List.replicate p i) fun y => f (h.expG (s • b j) * y))
      (g' := fun p s => (c p : ℂ) * Λ (j :: (l ++ List.replicate p i)) fun y => f (h.expG (s • b j) * y))
      (u := fun p => |c p| * C ((j :: l) ++ List.replicate p i) * (max 0 A * μ.real K))
      ((hsum (j :: l)).mul_right _) isOpen_Ioo isPreconnected_Ioo
      (fun p s _ => (hderiv _ s).const_mul _)
      (fun p s hs => (hterm (j :: l) _ (hft s) p).trans
        (mul_le_mul_of_nonneg_left (hB s (Set.Ioo_subset_Icc_self hs)) (mul_nonneg (abs_nonneg _) (hC0' _))))
      (by norm_num) (hsumm l _ (hft 0)) (by norm_num)
    simp only [zero_smul, hexp0, one_mul] at key
    exact key

end GlobalTheory.HCA
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.COneH2UnitsSubsingleton
section
open IsLocalRing

open CategoryTheory Limits groupCohomology GroundTheory.GroupCoh IntermediateField

namespace GlobalTheory

theorem c_one_h2_units_subsingleton : ∀ (K L : Type) [Field K] [Field L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L], (∀ (n d : ℕ) (f : MvPolynomial (Fin n) K), f.IsHomogeneous d → 0 < d → d < n → ∃ x : Fin n → K, x ≠ 0 ∧ MvPolynomial.eval x f = 0) → Subsingleton (groupCohomology (Rep.ofAlgebraAutOnUnits K L) 2) := by
  intro K L _ _ _ _ _ hC
  classical
  let A := Rep.ofAlgebraAutOnUnits K L
  have h0 : ∀ (S : Subgroup (L ≃ₐ[K] L)) [Fintype S],
      IsZero (tateCohomology (Rep.res S.subtype A) 0) := by
    intro S _
    refine isZero_tateCohomology_zero_of_forall _ fun m hm => ?_
    let u : Lˣ := Additive.toMul m
    have hu : (u : L) ∈ fixedField S := fun s => congrArg Units.val (hm s)
    have hCF := _root_.GlobalTheory.c_one_of_finite_extension K (fixedField S) hC
    have hne : (⟨(u : L), hu⟩ : fixedField S) ≠ 0 := fun h => u.ne_zero (congrArg Subtype.val h)
    obtain ⟨x, hx⟩ := _root_.GlobalTheory.norm_surjective_of_is_c1 (fixedField S) L hCF _ hne
    have hx0 : x ≠ 0 := by
      rintro rfl
      rw [Algebra.norm_zero] at hx
      exact hne hx.symm
    let y : Rep.res S.subtype A := Additive.ofMul (Units.mk0 x hx0)
    refine ⟨y, ?_⟩
    have e1 : (Rep.res S.subtype A).ρ.norm y = ∑ s : S, (Rep.res S.subtype A).ρ s y := by
      first
        | rw [Representation.norm, LinearMap.coeFn_sum, Finset.sum_apply]
        | simp [Representation.norm]
    have e2 : (Additive.ofMul (∏ s : S, (s : L ≃ₐ[K] L) • Units.mk0 x hx0) : Additive Lˣ) =
        ∑ s : S, (Rep.res S.subtype A).ρ s y := ofMul_prod _ _
    rw [e1, ← e2]
    change Additive.ofMul _ = Additive.ofMul u
    congr 1
    apply Units.ext
    rw [Units.coe_prod]
    have h := Algebra.norm_eq_prod_automorphisms (fixedField S) x
    rw [hx] at h
    refine Eq.trans ?_ h.symm
    exact Fintype.prod_equiv (subgroupEquivAlgEquiv S).toEquiv _ _ (fun s => rfl)
  have h1 : ∀ (S : Subgroup (L ≃ₐ[K] L)) [Fintype S],
      IsZero (tateCohomology (Rep.res S.subtype A) (0 + 1)) := by
    intro S _
    have hz : ∀ z : groupCohomology (Rep.res S.subtype A) 1, z = 0 := fun z =>
      H1_induction_on z fun f => by
        rw [H1π_eq_zero_iff]
        have hf := (mem_cocycles₁_iff (A := Rep.res S.subtype A) f).1 f.2
        let e := subgroupEquivAlgEquiv S
        let g : Gal(L/fixedField S) → Lˣ := fun σ => Additive.toMul (f (e.symm σ))
        have hg : IsMulCocycle₁ g := by
          intro σ τ
          obtain ⟨s, rfl⟩ := e.surjective σ
          obtain ⟨t, rfl⟩ := e.surjective τ
          have h := congrArg (Additive.toMul (α := Lˣ)) (hf s t)
          simp only [g, ← map_mul, MulEquiv.symm_apply_apply]
          exact h
        obtain ⟨β, hβ⟩ := isMulCoboundary₁_of_isMulCocycle₁_of_aut_to_units g hg
        refine ⟨Additive.ofMul β, funext fun s => ?_⟩
        have h := congrArg (Additive.ofMul (α := Lˣ)) (hβ (e s))
        rw [show g (e s) = Additive.toMul (f s) by simp only [g, MulEquiv.symm_apply_apply]; rfl] at h
        exact h
    have hs : Subsingleton (groupCohomology (Rep.res S.subtype A) 1) :=
      ⟨fun a b => by rw [hz a, hz b]⟩
    have e : (0 + 1 : ℤ) = ((1 : ℕ) : ℤ) := by norm_num
    rw [e]
    exact (ModuleCat.isZero_of_subsingleton (groupCohomology (Rep.res S.subtype A) 1)).of_iso ((TateCohomology.isoGroupCohomology 1).app _)
  have hCT : CohTrivial A := cohTrivial_of_forall_subgroup A 0 fun S _ => ⟨h0 S, h1 S⟩
  have h2 : IsZero (tateCohomology A ((2 : ℕ) : ℤ)) :=
    isZero_tateCohomology_of_index A _ fun p hp _ =>
      ⟨⊤, by simpa [Subgroup.index_top] using hp.one_lt.ne', fun {_} => hCT ⊤ _⟩
  have h2' : IsZero (groupCohomology A 2) :=
    h2.of_iso ((TateCohomology.isoGroupCohomology 2).app A).symm
  exact (ModuleCat.isZero_iff_subsingleton).1 h2'

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardLTorsionEqPowOfTateSimilitude
section
open scoped NumberField

namespace GlobalTheory.TateTorsion

theorem natCard_eq_of_surj_fibres {α β γ : Type*} (g : α → β) (f : α → γ)
    (hg : Function.Surjective g) (hf : Function.Surjective f)
    (h : ∀ x y, g x = g y ↔ f x = f y) : Nat.card β = Nat.card γ := by
  refine Nat.card_congr
    { toFun := fun b => f (Function.surjInv hg b)
      invFun := fun c => g (Function.surjInv hf c)
      left_inv := ?_
      right_inv := ?_ }
  · intro b
    have h1 := Function.surjInv_eq hf (f (Function.surjInv hg b))
    show g (Function.surjInv hf (f (Function.surjInv hg b))) = b
    rw [(h _ _).mpr h1, Function.surjInv_eq hg]
  · intro c
    have h1 := Function.surjInv_eq hg (g (Function.surjInv hf c))
    show f (Function.surjInv hg (g (Function.surjInv hf c))) = c
    rw [(h _ _).mp h1, Function.surjInv_eq hf]

theorem repr_mod_eq_zero_iff {M : Type*} [AddCommGroup M] {r : ℕ} (b : Module.Basis (Fin r) ℤ M) (l : ℕ)
    (z : M) : (∀ i, ((b.equivFun z i : ℤ) : ZMod l) = 0) ↔ ∃ y, z = l • y := by
  constructor
  · intro hz
    refine ⟨b.equivFun.symm (fun i => b.equivFun z i / (l : ℤ)), ?_⟩
    apply b.equivFun.injective
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul, LinearEquiv.apply_symm_apply]
    funext i
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Int.mul_ediv_cancel' ((ZMod.intCast_zmod_eq_zero_iff_dvd _ _).mp (hz i))]
  · rintro ⟨y, rfl⟩ i
    rw [← Nat.cast_smul_eq_nsmul ℤ, map_zsmul]
    simp

end GlobalTheory.TateTorsion

open GlobalTheory.TateTorsion in
theorem GlobalTheory.UPel.HT.TateIsoO.card_pow_eq_one : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (k : Type) [Field k] (Q : Type) [Group Q]
    (act : D.O → Q → Q) (e : ℕ → Q → Q → kˣ → Prop) (I : GlobalTheory.UPel.HT.TateIsoO D k Q act e) (l : ℕ),
    l.Prime → l ≠ p → Nat.card {q : Q // q ^ l = 1} = l ^ (D.m * D.n * Module.finrank ℚ D.F) := by
  intro p hp D k _ Q _ act e I l hl hne
  haveI := D.freeLa
  haveI := D.finLa
  haveI : NeZero l := ⟨hl.ne_zero⟩
  have hl0 : 0 < l := hl.pos
  have hcop : l.Coprime p := (Nat.coprime_primes hl hp.out).mpr hne
  let b := Module.finBasisOfFinrankEq ℤ D.La D.rankLa
  let g : D.La → {q : Q // q ^ l = 1} := fun x => ⟨I.ev l x, (I.onto l hl0 hcop _).mpr ⟨x, rfl⟩⟩
  let f : D.La → (Fin (D.m * D.n * Module.finrank ℚ D.F) → ZMod l) :=
    fun x i => ((b.equivFun x i : ℤ) : ZMod l)
  have hg : Function.Surjective g := by
    rintro ⟨q, hq⟩
    obtain ⟨x, hx⟩ := (I.onto l hl0 hcop q).mp hq
    exact ⟨x, Subtype.ext hx⟩
  have hf : Function.Surjective f := by
    intro c
    refine ⟨b.equivFun.symm (fun i => ((c i).val : ℤ)), ?_⟩
    funext i
    simp only [f, LinearEquiv.apply_symm_apply, Int.cast_natCast, ZMod.natCast_val, ZMod.intCast_cast, ZMod.cast_id', id]
  have hgf : ∀ x y, g x = g y ↔ f x = f y := by
    intro x y
    have e1 : g x = g y ↔ I.ev l (x - y) = 1 := by
      rw [Subtype.ext_iff]
      show I.ev l x = I.ev l y ↔ _
      have : I.ev l x = I.ev l (x - y) * I.ev l y := by rw [← I.add, sub_add_cancel]
      rw [this]
      constructor
      · intro h; simpa using h
      · intro h; simp [h]
    have e2 : f x = f y ↔ ∀ i, ((b.equivFun (x - y) i : ℤ) : ZMod l) = 0 := by
      simp only [f, map_sub, Pi.sub_apply, Int.cast_sub, sub_eq_zero, funext_iff]
    rw [e1, e2, repr_mod_eq_zero_iff, I.ker l hl0 hcop]
  rw [natCard_eq_of_surj_fibres g f hg hf hgf, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardTwistedNormOneMulCardFixedUnits
section
open Polynomial GlobalTheory.CuspGL GlobalTheory.BI GlobalTheory.Shin SemidirectProduct
open scoped Classical

namespace GlobalTheory.Shin

theorem card_nrm_one_mul_card_fixed (F F' : Type) [Field F] [Field F'] [Algebra F F'] [Finite F']
    (s : F' ≃ₐ[F] F') (hs : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s) (n : ℕ)
    (B : Subalgebra F' (Matrix (Fin n) (Fin n) F')) (hB : ∀ x ∈ B, x.map s ∈ B) :
    Nat.card {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1} *
      Nat.card {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B} =
      Nat.card {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B} := by
  obtain ⟨hfix, hinj, hconj, -, -⟩ := GlobalTheory.T.galoisTwistedNormGL_basic_properties F F' s hs n
  have h90 := GlobalTheory.T.exists_coboundary_of_norm_one_in_subalgebra F F' s hs n B hB
  have hsB : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((galAct F F' n s x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := fun x hx => hB _ hx
  have hinv : ∀ x : GL (Fin n) F', (x : Matrix (Fin n) (Fin n) F') ∈ B →
      ((x⁻¹ : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro x hx
    obtain ⟨k, hk, hxk⟩ := (isOfFinOrder_of_finite x).exists_pow_eq_one
    have hx' : x⁻¹ = x ^ (k - 1) := by
      rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, Nat.sub_add_cancel hk, hxk]
    rw [hx', Units.val_pow_eq_pow_val]
    exact pow_mem hx _
  have hmul : ∀ a b : GL (Fin n) F', (a : Matrix (Fin n) (Fin n) F') ∈ B → (b : Matrix (Fin n) (Fin n) F') ∈ B →
      ((a * b : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
    intro a b ha hb
    rw [Units.val_mul]
    exact mul_mem ha hb
  have hn1 : nrm s (1 : GL (Fin n) F') = 1 := by
    unfold nrm nrmG
    apply List.prod_eq_one
    intro y hy
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact map_one _
  have hnorm : ∀ x : GL (Fin n) F', nrm s (x⁻¹ * galAct F F' n s x) = 1 := by
    intro x
    have h := hconj 1 x
    rw [mul_one, hn1, mul_one, inv_mul_cancel] at h
    exact h
  let U := {x : GL (Fin n) F' // (x : Matrix (Fin n) (Fin n) F') ∈ B}
  let N := {ε : GL (Fin n) F' // (ε : Matrix (Fin n) (Fin n) F') ∈ B ∧ nrm s ε = 1}
  let U₀ := {x : GL (Fin n) F // ((incl F F' n x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B}
  let φ : U → N := fun x =>
    ⟨x.1⁻¹ * galAct F F' n s x.1, hmul _ _ (hinv _ x.2) (hsB _ x.2), hnorm _⟩
  have hsec : ∀ ε : N, ∃ x : U, φ x = ε := by
    intro ε
    obtain ⟨x, hx, he⟩ := h90 ε.1 ε.2.1 ε.2.2
    exact ⟨⟨x, hx⟩, Subtype.ext he.symm⟩
  choose sec hsec using hsec
  have hfixI : ∀ z : GL (Fin n) F, galAct F F' n s (incl F F' n z) = incl F F' n z :=
    fun z => (hfix _).2 ⟨z, rfl⟩
  let f : ∀ ε : N, U₀ → {x : U // φ x = ε} := fun ε z =>
    ⟨⟨incl F F' n z.1 * (sec ε).1, hmul _ _ z.2 (sec ε).2⟩, by
      refine Eq.trans ?_ (hsec ε)
      apply Subtype.ext
      show (incl F F' n z.1 * (sec ε).1)⁻¹ * galAct F F' n s (incl F F' n z.1 * (sec ε).1) =
        (sec ε).1⁻¹ * galAct F F' n s (sec ε).1
      rw [map_mul, hfixI]
      group⟩
  have hbij : ∀ ε : N, Function.Bijective (f ε) := by
    intro ε
    constructor
    · intro z w h
      have h' : incl F F' n z.1 * (sec ε).1 = incl F F' n w.1 * (sec ε).1 :=
        congrArg (fun u : {x : U // φ x = ε} => u.1.1) h
      exact Subtype.ext (hinj (mul_right_cancel h'))
    · rintro ⟨y, hy⟩
      set x := sec ε with hxdef
      have hyx : φ y = φ x := by rw [hy, hsec ε]
      have h1 : y.1⁻¹ * galAct F F' n s y.1 = x.1⁻¹ * galAct F F' n s x.1 :=
        congrArg Subtype.val hyx
      have h2 : galAct F F' n s (y.1 * x.1⁻¹) = y.1 * x.1⁻¹ := by
        rw [map_mul, map_inv]
        calc galAct F F' n s y.1 * (galAct F F' n s x.1)⁻¹
            = y.1 * (y.1⁻¹ * galAct F F' n s y.1) * (galAct F F' n s x.1)⁻¹ := by group
          _ = y.1 * (x.1⁻¹ * galAct F F' n s x.1) * (galAct F F' n s x.1)⁻¹ := by rw [h1]
          _ = y.1 * x.1⁻¹ := by group
      obtain ⟨z, hz⟩ := (hfix _).1 h2
      have hzB : ((incl F F' n z : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') ∈ B := by
        rw [hz]; exact hmul _ _ y.2 (hinv _ x.2)
      refine ⟨⟨z, hzB⟩, ?_⟩
      apply Subtype.ext; apply Subtype.ext
      show incl F F' n z * x.1 = y.1
      rw [hz]; group
  let E : U ≃ N × U₀ := (Equiv.sigmaFiberEquiv φ).symm.trans
    (Equiv.sigmaEquivProdOfEquiv fun ε => (Equiv.ofBijective (f ε) (hbij ε)).symm)
  rw [← Nat.card_prod]
  exact (Nat.card_congr E).symm

end GlobalTheory.Shin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDifferentialAdjointCupProductPairingStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechDifferential_adjoint_cupProductPairing : ∀ (k : Type) [Field k] (d : ℕ) (E : Type) [AddCommGroup E] [Module k E] (E' : Type) [AddCommGroup E'] [Module k E'] (A : Finset (Fin (d + 1)) → Submodule k E) (B : Finset (Fin (d + 1)) → Submodule k E') (β : E →ₗ[k] E' →ₗ[k] k), (∀ s t, s.Nonempty → s ⊆ t → A s ≤ A t) → (∀ s t, s.Nonempty → s ⊆ t → B s ≤ B t) → (∀ i, (Finset.univ.erase i).Nonempty → ∀ a ∈ A (Finset.univ.erase i), ∀ b ∈ B (Finset.univ.erase i), β a b = 0) → Adj (cech A) (cech B) (cupPair β) d := by
  first | (exact @GlobalTheory.PD.CupAdj.cech_adj) | (exact GlobalTheory.PD.CupAdj.cech_adj) | (intros; apply GlobalTheory.PD.CupAdj.cech_adj  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechNerveLevelPreservesCofilteredLimitStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cechNerve_level_preserves_cofiltered_limit : ∀ (I : Type) [SmallCategory I] [IsCofiltered I] (A : I ⥤ Arrow PSh) (cA : Cone A), IsLimit (Arrow.leftFunc.mapCone cA) → (∀ ⦃i j : I⦄ (f : i ⟶ j), IsIso (A.map f).right) → (∀ i, IsIso (cA.π.app i).right) → ∀ k : SimplexCategoryᵒᵖ, Nonempty (IsLimit (((evaluation _ PSh).obj k).mapCone (SimplicialObject.cechNerve.mapCone cA))) := by
  first | exact @GlobalTheory.cech_level_limit | exact GlobalTheory.cech_level_limit | (intros; apply GlobalTheory.cech_level_limit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainComplexExactSquare
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chain_complex_exact_square : ∀ (R : Type) [CommRing R] {X₁ X₂ X₃ X₄ : Scheme.{0}} (a : X₁ ⟶ X₂) (b : X₁ ⟶ X₃) (c : X₂ ⟶ X₄) (d : X₃ ⟶ X₄) (w₁ : biprod.lift ((free R).map (yoneda.map a)) (-(free R).map (yoneda.map b)) ≫ biprod.desc ((free R).map (yoneda.map c)) ((free R).map (yoneda.map d)) = 0) (w₂ : biprod.lift ((chains R).map (sch.map a)) (-(chains R).map (sch.map b)) ≫ biprod.desc ((chains R).map (sch.map c)) ((chains R).map (sch.map d)) = 0), (ShortComplex.mk _ _ w₁).ShortExact → (ShortComplex.mk _ _ w₂).ShortExact := by
  first | (exact @GlobalTheory.EtC.chains_shortExact_of_free) | (exact GlobalTheory.EtC.chains_shortExact_of_free) | (intros; apply GlobalTheory.EtC.chains_shortExact_of_free <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChainsCechNerveQuasiIsoOfSurjectiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.quasiIso_chains_cechNerve_of_surjective : ∀ (R : Type) [CommRing R] {P Q : PSh} (φ : P ⟶ Q), (∀ U, Function.Surjective (φ.app U)) → QuasiIso ((chains R).map (show (Arrow.mk φ).cechNerve ⟶ disc.obj Q from (Arrow.mk φ).augmentedCechNerve.hom)) := by
  first | (exact @GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective) | (exact GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective) | (intros; apply GlobalTheory.EtC.chains_cechNerve_quasiIso_of_surjective  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharpolyLaEqPow
section
open NumberField Polynomial

namespace GlobalTheory.UPel.HT

theorem charpoly_eq_pow_of_aeval_irreducible {M : Type*} [AddCommGroup M] [Module.Free ℤ M] [Module.Finite ℤ M]
    (f : Module.End ℤ M) (μ : ℤ[X]) (hm : μ.Monic) (hi : Irreducible μ) (h : aeval f μ = 0) :
    ∃ s : ℕ, f.charpoly = μ ^ s := by
  classical
  let b := Module.Free.chooseBasis ℤ M
  have hA : aeval (LinearMap.toMatrixAlgEquiv b f) μ = 0 := by
    have := Polynomial.aeval_algHom_apply (LinearMap.toMatrixAlgEquiv b).toAlgHom f μ
    simpa [h] using this
  have hd := GlobalTheory.UnitLemma.Centraliser.charpoly_dvd_pow_of_aeval_eq_zero _ μ hA
  have hc : (LinearMap.toMatrixAlgEquiv b f).charpoly = f.charpoly := LinearMap.charpoly_toMatrix f b
  rw [hc] at hd
  obtain ⟨i, -, hi'⟩ := (dvd_prime_pow hi.prime _).1 hd
  exact ⟨i, eq_of_monic_of_associated (LinearMap.charpoly_monic f) (hm.pow i) hi'⟩

theorem Datum.charpoly_La_eq_pow (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (c : 𝓞 D.F) :
    haveI := D.freeLa; haveI := D.finLa
    LinearMap.charpoly (DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c)) =
      (LinearMap.charpoly (LinearMap.mulLeft ℤ c)) ^ (D.m * D.n) := by
  haveI := D.freeLa; haveI := D.finLa
  have hint : IsIntegral ℤ c := RingOfIntegers.isIntegral c
  have hm : (minpoly ℤ c).Monic := minpoly.monic hint
  have hirr : Irreducible (minpoly ℤ c) := minpoly.irreducible hint
  have hpos : 0 < (minpoly ℤ c).natDegree := minpoly.natDegree_pos hint
  obtain ⟨r, -, hr⟩ := ReciprocityTheory.ChartRestriction.T1.lat_cp_eq_minpoly_pow c
  have hR : LinearMap.charpoly (LinearMap.mulLeft ℤ c) = minpoly ℤ c ^ r := hr
  let ψ : 𝓞 D.F →+* Module.End ℤ D.La :=
    (Module.toModuleEnd ℤ (S := D.O) D.La).comp (algebraMap (𝓞 D.F) D.O)
  have hf : DistribSMul.toLinearMap ℤ D.La (algebraMap (𝓞 D.F) D.O c) = ψ.toIntAlgHom c := rfl
  have h0 : aeval (ψ.toIntAlgHom c) (minpoly ℤ c) = 0 := by
    rw [Polynomial.aeval_algHom_apply, minpoly.aeval, map_zero]
  obtain ⟨s, hs⟩ := charpoly_eq_pow_of_aeval_irreducible _ _ hm hirr h0
  have h1 := LinearMap.charpoly_natDegree (ψ.toIntAlgHom c)
  rw [hs, hm.natDegree_pow, D.rankLa] at h1
  have h2 := LinearMap.charpoly_natDegree (LinearMap.mulLeft ℤ c)
  rw [hR, hm.natDegree_pow, RingOfIntegers.rank] at h2
  have hsr : s = r * (D.m * D.n) := by
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [h1, ← h2]
    ring
  rw [hf, hs, hR, ← pow_mul, hsr]

end GlobalTheory.UPel.HT
end

