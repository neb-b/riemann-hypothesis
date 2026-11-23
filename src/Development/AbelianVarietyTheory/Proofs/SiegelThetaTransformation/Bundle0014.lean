module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CardKerMatrixFiniteField
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real Classical

namespace GlobalTheory.SW

theorem card_lines_le_submodule (F V : Type) [Field F] [AddCommGroup V] [Module F V] [Finite V]
    (K : Submodule F V) :
    Nat.card {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K} * (Nat.card F - 1) + 1
      = Nat.card K := by
  classical
  have e : {l : Submodule F V // Module.finrank F l = 1 ∧ l ≤ K}
      ≃ {H : Submodule F K // Module.finrank F H = 1} :=
    { toFun := fun l => ⟨l.1.comap K.subtype, by
        rw [← Submodule.finrank_map_subtype_eq, Submodule.map_comap_subtype,
          inf_eq_right.mpr l.2.2]
        exact l.2.1⟩
      invFun := fun H => ⟨H.1.map K.subtype,
        by rw [Submodule.finrank_map_subtype_eq]; exact H.2,
        Submodule.map_subtype_le K H.1⟩
      left_inv := fun l => by
        apply Subtype.ext
        simp only [Submodule.map_comap_subtype]
        exact inf_eq_right.mpr l.2.2
      right_inv := fun H => by
        apply Subtype.ext
        exact Submodule.comap_map_eq_of_injective K.injective_subtype H.1 }
  rw [Nat.card_congr e, ← Nat.card_congr (Projectivization.equivSubmodule F K)]
  exact (Projectivization.card' F K).symm

end GlobalTheory.SW
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CycOfPrime
section
open scoped TensorProduct LinearAlgebra.Projectivization

namespace GlobalTheory.SW.Hyper

variable {O M : Type} [CommRing O] [AddCommGroup M] [Module O M]

theorem exists_fun (P : Ideal O) [hP : P.IsMaximal] (N : Submodule O M) (v : M) (hv : v ∉ N)
    (hPv : ∀ c ∈ P, c • v ∈ N) (hc : ∀ x, ∃ r : O, x - r • v ∈ N) :
    ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N := by
  classical
  let g : O →ₗ[O] M ⧸ N := LinearMap.toSpanSingleton O (M ⧸ N) (N.mkQ v)
  have hker : LinearMap.ker g = P := by
    ext r
    simp only [LinearMap.mem_ker, g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
    constructor
    · intro h
      by_contra hr
      obtain ⟨y, i, hi, hyi⟩ := hP.exists_inv hr
      apply hv
      have hv' : v = y • (r • v) + i • v := by rw [smul_smul, ← add_smul, hyi, one_smul]
      rw [hv']
      exact N.add_mem (N.smul_mem y h) (hPv i hi)
    · exact hPv r
  have hs : Function.Surjective g := by
    intro z
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective N z
    obtain ⟨r, hr⟩ := hc x
    refine ⟨r, ?_⟩
    simp only [g, LinearMap.toSpanSingleton_apply, Submodule.mkQ_apply]
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.eq, ← neg_sub]
    exact N.neg_mem hr
  let e : (O ⧸ P) ≃ₗ[O] M ⧸ N :=
    (Submodule.quotEquivOfEq _ _ hker.symm).trans (g.quotKerEquivOfSurjective hs)
  refine ⟨e.symm.toLinearMap ∘ₗ N.mkQ, ?_, ?_⟩
  · intro h0
    apply hv
    have h1 : (e.symm.toLinearMap ∘ₗ N.mkQ) v = 0 := by rw [h0]; rfl
    simpa only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.map_eq_zero_iff,
      Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] using h1
  · rw [LinearEquiv.ker_comp, Submodule.ker_mkQ]

theorem surj_of_ne (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    ∃ v, f v = 1 := by
  obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
    by_contra h
    push Not at h
    exact hf (LinearMap.ext fun x => by simpa using h x)
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv hw
  obtain ⟨c, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨c • w, ?_⟩
  rw [map_smul, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, mul_comm, hb]

theorem index_ker (P : Ideal O) [hP : P.IsMaximal] (f : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) :
    (LinearMap.ker f).toAddSubgroup.index = Nat.card (O ⧸ P) := by
  obtain ⟨v, hv⟩ := surj_of_ne P f hf
  have hs : Function.Surjective f := by
    intro y
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective y
    refine ⟨r • v, ?_⟩
    rw [map_smul, hv, Algebra.smul_def, mul_one, Ideal.Quotient.algebraMap_eq]
  have h := AddSubgroup.index_ker f.toAddMonoidHom
  rw [AddMonoidHom.range_eq_top.mpr hs, AddSubgroup.card_top] at h
  exact h

theorem cyc_of_prime (N : Submodule O M) {q : ℕ} (hq : q.Prime)
    (h : N.toAddSubgroup.index = q) : ∃ v, v ∉ N ∧ ∀ x, ∃ r : O, x - r • v ∈ N := by
  classical
  have : Fact q.Prime := ⟨hq⟩
  have hcard : Nat.card (M ⧸ N.toAddSubgroup) = q := by
    rw [← AddSubgroup.index_eq_card]; exact h
  have hne : N.toAddSubgroup ≠ ⊤ := by
    intro ht
    rw [ht, AddSubgroup.index_top] at h
    exact hq.one_lt.ne h
  obtain ⟨v, hv⟩ : ∃ v, v ∉ N := by
    by_contra hn
    push Not at hn
    exact hne (eq_top_iff.mpr fun x _ => hn x)
  refine ⟨v, hv, fun x => ?_⟩
  have hv0 : (QuotientAddGroup.mk v : M ⧸ N.toAddSubgroup) ≠ 0 := by
    rw [Ne, QuotientAddGroup.eq_zero_iff]; exact hv
  have hx : (QuotientAddGroup.mk x : M ⧸ N.toAddSubgroup) ∈
      AddSubgroup.zmultiples (QuotientAddGroup.mk v) := mem_zmultiples_of_prime_card hcard hv0
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
  refine ⟨(n : O), ?_⟩
  rw [Int.cast_smul_eq_zsmul]
  have h2 : (QuotientAddGroup.mk (n • v) : M ⧸ N.toAddSubgroup) = QuotientAddGroup.mk x := by
    rw [QuotientAddGroup.mk_zsmul]; exact hn
  rw [QuotientAddGroup.eq] at h2
  rw [sub_eq_neg_add]
  exact h2

theorem finrank_fibre (O M k : Type) [CommRing O] [IsDomain O] [AddCommGroup M] [Module O M]
    [Module.Finite O M] [Module.Projective O M] [Field k] [Algebra O k] :
    Module.finrank k (k ⊗[O] M) = Module.finrank O M := by
  have : Module.FinitePresentation O M := Module.finitePresentation_of_projective O M
  have hlc := Module.isLocallyConstant_rankAtStalk (R := O) (M := M)
  let q0 : PrimeSpectrum k := ⟨⊥, Ideal.isPrime_bot⟩
  let p0 : PrimeSpectrum O := ⟨⊥, Ideal.isPrime_bot⟩
  have h1 : Module.finrank k (k ⊗[O] M) = Module.rankAtStalk (R := k) (k ⊗[O] M) q0 := by
    rw [Module.rankAtStalk_eq_finrank_of_free]; rfl
  have hp : p0.asIdeal.primeCompl ≤ nonZeroDivisors O := by
    intro x hx
    have hx0 : x ≠ 0 := fun h0 => hx (h0 ▸ Ideal.zero_mem _)
    exact mem_nonZeroDivisors_of_ne_zero hx0
  have h2 : Module.rankAtStalk (R := O) M p0 = Module.finrank O M := by
    rw [Module.rankAtStalk,
      IsLocalization.finrank_eq (Localization.AtPrime p0.asIdeal) p0.asIdeal.primeCompl hp,
      IsLocalizedModule.finrank_eq p0.asIdeal.primeCompl
        (LocalizedModule.mkLinearMap p0.asIdeal.primeCompl M) hp]
  rw [h1, Module.rankAtStalk_baseChange, hlc.apply_eq_of_preconnectedSpace _ p0, h2]


attribute [local instance] Ideal.Quotient.field in
theorem count [IsDomain O] [Module.Finite O M] [Module.Projective O M] (P : Ideal O)
    [hP : P.IsMaximal] [Finite (O ⧸ P)] :
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.Finite ∧
    {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}.ncard *
      (Nat.card (O ⧸ P) - 1) = Nat.card (O ⧸ P) ^ Module.finrank O M - 1 := by
  classical
  have hcard : Nat.card (M →ₗ[O] O ⧸ P) = Nat.card (O ⧸ P) ^ Module.finrank O M := by
    rw [Nat.card_congr (LinearMap.liftBaseChangeEquiv (M := M) (N := O ⧸ P) (O ⧸ P)).toEquiv,
      Module.natCard_eq_pow_finrank (K := O ⧸ P)]
    congr 1
    rw [← finrank_fibre O M (O ⧸ P)]
    exact Subspace.dual_finrank_eq
  have : Finite (M →ₗ[O] O ⧸ P) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ Nat.card_pos.ne')
  let φ : ℙ (O ⧸ P) (M →ₗ[O] O ⧸ P) → Submodule O M :=
    Projectivization.lift (K := O ⧸ P) (V := M →ₗ[O] O ⧸ P)
      (fun f => LinearMap.ker f.1) (by
      rintro ⟨a, ha⟩ ⟨b, hb⟩ t (hab : a = t • b)
      have ht : t ≠ 0 := by
        rintro rfl
        apply ha
        rw [hab, zero_smul]
      ext x
      simp only [LinearMap.mem_ker, hab, LinearMap.smul_apply, smul_eq_zero, ht, false_or])
  have key : ∀ (f g : M →ₗ[O] O ⧸ P) (hf : f ≠ 0) (hg : g ≠ 0),
      LinearMap.ker f = LinearMap.ker g →
      Projectivization.mk (O ⧸ P) g hg = Projectivization.mk (O ⧸ P) f hf := by
    intro f g hf hg hfg
    obtain ⟨w, hw⟩ := surj_of_ne P f hf
    rw [Projectivization.mk_eq_mk_iff']
    refine ⟨g w, ?_⟩
    ext x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective (f x)
    have hmem : x - r • w ∈ LinearMap.ker g := by
      rw [← hfg, LinearMap.mem_ker, map_sub, map_smul, hw, ← hr, Algebra.smul_def,
        Ideal.Quotient.algebraMap_eq, mul_one, sub_self]
    rw [LinearMap.mem_ker, map_sub, map_smul, sub_eq_zero] at hmem
    rw [LinearMap.smul_apply, hmem, smul_eq_mul, ← hr, Algebra.smul_def,
      Ideal.Quotient.algebraMap_eq, mul_comm]
  have hφ : Function.Injective φ := by
    intro x y hxy
    rw [← Projectivization.mk_rep x, ← Projectivization.mk_rep y] at hxy ⊢
    exact (key _ _ _ _ hxy).symm
  have hS : {N : Submodule O M | ∃ f : M →ₗ[O] O ⧸ P, f ≠ 0 ∧ LinearMap.ker f = N}
      = Set.range φ := by
    ext N
    constructor
    · rintro ⟨f, hf, rfl⟩
      exact ⟨Projectivization.mk _ f hf, rfl⟩
    · rintro ⟨x, rfl⟩
      refine ⟨x.rep, x.rep_nonzero, ?_⟩
      have h1 : φ (Projectivization.mk _ x.rep x.rep_nonzero) = LinearMap.ker x.rep := rfl
      rw [Projectivization.mk_rep] at h1
      exact h1.symm
  rw [hS]
  refine ⟨Set.finite_range φ, ?_⟩
  rw [Set.ncard_range_of_injective hφ]
  have h' := Projectivization.card' (O ⧸ P) (M →ₗ[O] O ⧸ P)
  rw [hcard] at h'
  rw [h', Nat.add_sub_cancel]

end GlobalTheory.SW.Hyper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLinearIndependentOfRatIndependent
section
open Matrix Complex NumberField GlobalTheory.SW Filter Topology
open ReciprocityTheory.ChartRestriction.G.FD (cc herm)
open scoped ComplexConjugate ComplexOrder Real

namespace GlobalTheory.SW

theorem exists_linearIndependent_of_rat_independent {E U : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] (S : ℕ → Set U) (N : ℕ)
    (h : ∀ i < N, ∃ u : Fin (Module.finrank ℚ E * i + 1) → U,
      LinearIndependent ℚ u ∧ ∀ k, u k ∈ S i) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ ∀ i : Fin N, w i ∈ S i := by
  induction N with
  | zero => exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => i.elim0⟩
  | succ N ih =>
    obtain ⟨w, hw, hS⟩ := ih fun i hi => h i (by omega)
    obtain ⟨u, hu, huS⟩ := h N (by omega)
    obtain ⟨k, hk⟩ : ∃ k, u k ∉ Submodule.span E (Set.range w) := by
      by_contra! hc
      have : Module.Finite E (Submodule.span E (Set.range w)) :=
        Module.Finite.span_of_finite E (Set.finite_range w)
      have : Module.Finite ℚ (Submodule.span E (Set.range w)) := Module.Finite.trans E _
      have h1 : LinearIndependent ℚ (fun k => (⟨u k, hc k⟩ : Submodule.span E (Set.range w))) :=
        LinearIndependent.of_comp
          ((Submodule.span E (Set.range w)).subtype.restrictScalars ℚ) hu
      have h2 := h1.fintype_card_le_finrank
      rw [← Module.finrank_mul_finrank ℚ E (Submodule.span E (Set.range w)),
        finrank_span_eq_card hw] at h2
      simp at h2
    refine ⟨Fin.snoc w (u k), linearIndependent_finSnoc.2 ⟨hw, hk⟩, fun i => ?_⟩
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa using huS k
    · simpa using hS j

theorem prod_pow_le_prod_of_mono (l : ℕ → ℝ) (hl : ∀ i, 0 ≤ l i) (d N : ℕ)
    (hm : ∀ i j, i ≤ j → j ≤ d * N → l i ≤ l j) :
    ∏ i ∈ Finset.range N, l (d * i + 1) ^ d ≤ ∏ j ∈ Finset.range (d * N), l (j + 1) := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.prod_range_succ, mul_add, mul_one, Finset.prod_range_add]
    refine mul_le_mul (ih fun i j hij hj => hm i j hij (by nlinarith)) ?_ (pow_nonneg (hl _) _)
      (Finset.prod_nonneg fun _ _ => hl _)
    calc l (d * N + 1) ^ d = ∏ _j ∈ Finset.range d, l (d * N + 1) := by simp
      _ ≤ _ := Finset.prod_le_prod₀ (fun _ _ => hl _) fun j hj => hm _ _ (by omega) (by
          have := Finset.mem_range.1 hj
          rw [mul_add]; omega)

theorem IsType.prod_univ {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) {M : Type} [CommMonoid M] (g : (E →+* ℂ) → M) :
    ∏ σ, g σ = ∏ τ : Ψ, (g τ * g (ComplexEmbedding.conjugate τ.1)) := by
  classical
  rw [Finset.prod_coe_sort Ψ (fun τ => g τ * g (ComplexEmbedding.conjugate τ)),
    Finset.prod_mul_distrib, ← Finset.prod_mul_prod_compl Ψ]
  congr 1
  symm
  refine Finset.prod_bij' (fun τ _ => ComplexEmbedding.conjugate τ)
    (fun τ _ => ComplexEmbedding.conjugate τ) ?_ ?_ ?_ ?_ ?_
  · intro τ hτ; exact Finset.mem_compl.2 ((hΨ τ).1 hτ)
  · intro τ hτ
    by_contra hc
    exact Finset.mem_compl.1 hτ ((hΨ τ).2 hc)
  · intro τ _; exact star_star τ
  · intro τ _; exact star_star τ
  · intro τ _; rfl

theorem IsType.finrank_eq {E : Type} [Field E] [NumberField E] [IsCMField E]
    {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) : Module.finrank ℚ E = 2 * Ψ.card := by
  have h := hΨ.prod_univ (fun _ => Multiplicative.ofAdd (1 : ℕ))
  have h2 := congrArg Multiplicative.toAdd h
  simp only [Finset.prod_const, toAdd_pow, toAdd_mul, toAdd_ofAdd, smul_eq_mul, Finset.card_univ,
    Embeddings.card, Fintype.card_coe] at h2
  omega

theorem exists_linearIndependent_prod_norm_le {E U V ι : Type} [Field E] [NumberField E]
    [AddCommGroup U] [Module E U] [Module ℚ U] [IsScalarTower ℚ E U] [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [Fintype ι] [DecidableEq ι] {N : ℕ}
    (hι : Fintype.card ι = Module.finrank ℚ E * N) (φ : U →ₗ[ℤ] V) (u : ι → U)
    (hu : LinearIndependent ℝ fun k => φ (u k)) :
    ∃ w : Fin N → U, LinearIndependent E w ∧ (∀ i, w i ∈ Submodule.span ℤ (Set.range u)) ∧
      ∏ i, ‖φ (w i)‖ ^ Module.finrank ℚ E ≤
        (Fintype.card ι : ℝ) ^ ((Fintype.card ι : ℝ) / 2) * √(gram ℝ fun k => φ (u k)).det := by
  set d := Module.finrank ℚ E with hd
  have hd0 : 0 < d := Module.finrank_pos
  set L := Submodule.span ℤ (Set.range fun k => φ (u k)) with hL
  have : DiscreteTopology L := discreteTopology_span_of_linearIndependent hu
  have huZ : LinearIndependent ℤ fun k => φ (u k) := hu.restrict_scalars' ℤ
  have hr : Module.finrank ℤ L = Fintype.card ι := finrank_span_eq_card huZ
  have hrR : Module.finrank ℝ (Submodule.span ℝ (L : Set V)) = d * N := by
    rw [finrank_span_eq_finrank_int, hr, hι]
  have hLm : L = (Submodule.span ℤ (Set.range u)).map φ := by
    rw [Submodule.map_span, ← Set.range_comp]; rfl
  obtain ⟨w, hw, hS⟩ := exists_linearIndependent_of_rat_independent (E := E)
    (fun i => {t | t ∈ Submodule.span ℤ (Set.range u) ∧ ‖φ t‖ ≤ succMin L (d * i + 1)}) N (by
      intro i hi
      obtain ⟨v, hv, hvL⟩ := exists_linearIndependent_norm_le_succMin (L := L) (i := d * i + 1)
        (by rw [hrR]; nlinarith)
      have : ∀ k, ∃ t ∈ Submodule.span ℤ (Set.range u), φ t = v k := fun k => by
        have := (hvL k).1
        rwa [hLm] at this
      choose t ht htv using this
      refine ⟨t, (LinearIndependent.iff_fractionRing ℤ ℚ).1 (LinearIndependent.of_comp φ ?_),
        fun k => ⟨ht k, ?_⟩⟩
      · have : φ ∘ t = v := funext htv
        rw [this]; exact hv.restrict_scalars' ℤ
      · rw [htv]; exact (hvL k).2)
  refine ⟨w, hw, fun i => (hS i).1, ?_⟩
  have h1 := prod_succMin_le_rpow_mul_spanCovol L
  rw [spanCovol_span huZ, Fin.prod_univ_eq_prod_range (fun i => succMin L (i + 1)), hr] at h1
  refine le_trans ?_ h1
  rw [hι]
  refine le_trans ?_ (prod_pow_le_prod_of_mono (succMin L) (succMin_nonneg L) d N
    fun i j hij hj => succMin_mono hij (by rwa [hrR]))
  rw [← Fin.prod_univ_eq_prod_range (fun i => succMin L (d * i + 1) ^ d)]
  exact Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ =>
    pow_le_pow_left₀ (norm_nonneg _) (hS i).2 _

theorem posDef_map_mul_conjTranspose {E m n : Type} [Field E] [Fintype m] [Fintype n]
    {W : Matrix n m E} (hW : LinearIndependent E fun i => W i) (σ : E →+* ℂ) :
    (W.map σ * (W.map σ)ᴴ).PosDef := by
  let _ := σ.toAlgebra
  exact PosDef.mul_conjTranspose_self _
    (vecMul_injective_iff.2 ((linearIndependent_algebraMap_comp_iff (S := ℂ)).2 hW))

noncomputable def rowEmb {E m n : Type} [Field E] [Fintype n] (W : Matrix n m E) :
    (n → E) →ₗ[ℤ] EuclideanSpace ℂ ((E →+* ℂ) × m) :=
  AddMonoidHom.toIntLinearMap
    { toFun := fun t => WithLp.toLp 2 fun p => p.1 ((t ᵥ* W) p.2)
      map_zero' := by ext p; simp
      map_add' := fun s t => by ext p; simp [add_vecMul] }

open scoped Classical in
open Classical in
theorem det_gram_rowEmb {E m : Type} [Field E] [NumberField E] [Fintype m] {N : ℕ}
    (W : Matrix (Fin N) m E) (ω : (E →+* ℂ) → E) :
    (((gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det : ℝ) : ℂ) =
      (normSq (Matrix.of fun k σ : E →+* ℂ => σ (ω k)).det : ℂ) ^ N *
        ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det := by
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  set P : Matrix (Fin N × (E →+* ℂ)) (Fin N × (E →+* ℂ)) ℂ :=
    kroneckerMap (· * ·) (1 : Matrix (Fin N) (Fin N) ℂ) A with hP
  have hdP : P.det = A.det ^ N := by simp [hP, det_kronecker]
  have key : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).map ofRealHom
      = (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ := by
    ext ⟨i, k⟩ ⟨i', k'⟩
    have hR : (P * blockDiagonal (fun σ : E →+* ℂ => W.map σ * (W.map σ)ᴴ) * Pᴴ)ᵀ (i, k) (i', k')
        = ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      simp only [transpose_apply, Matrix.mul_apply, Fintype.sum_prod_type, hP, hA, kroneckerMap_apply,
        Matrix.one_apply, blockDiagonal_apply, conjTranspose_apply, of_apply, map_apply]
      simp [Finset.mul_sum, Finset.sum_mul, apply_ite]
      refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
    rw [hR]
    have hreal : conj (∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j))) =
        ∑ σ : E →+* ℂ, ∑ j, σ (ω k' * W i' j) * conj (σ (ω k * W i j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Fintype.sum_equiv (Function.Involutive.toPerm _
        (ComplexEmbedding.involutive_conjugate E)) _ _ fun σ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum]
    rw [← conj_eq_iff_re.1 hreal]
    simp [gram_apply, PiLp.inner_apply, Fintype.sum_prod_type, Complex.inner, rowEmb]
  rw [← ofRealHom_eq_coe, RingHom.map_det, RingHom.mapMatrix_apply, key, det_transpose, det_mul,
    det_mul, det_conjTranspose, hdP, det_blockDiagonal, normSq_eq_conj_mul_self]
  simp only [star_pow, RCLike.star_def]
  ring

theorem IsType.prod_det_eq_sq {E m n : Type} [Field E] [NumberField E] [IsCMField E] [Fintype m]
    [Fintype n] [DecidableEq n] {Ψ : Finset (E →+* ℂ)} (hΨ : IsType Ψ) (W : Matrix n m E) :
    ∏ σ : E →+* ℂ, (W.map σ * (W.map σ)ᴴ).det =
      (((∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 : ℝ) : ℂ) := by
  rw [hΨ.prod_univ, ← Finset.prod_pow, ofReal_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  have h1 : W.map (ComplexEmbedding.conjugate τ.1) * (W.map (ComplexEmbedding.conjugate τ.1))ᴴ =
      (W.map τ.1 * (W.map τ.1)ᴴ)ᵀ := by
    ext i j
    simp [Matrix.mul_apply, mul_comm]
  have h2 : (((W.map τ.1 * (W.map τ.1)ᴴ).det.re : ℝ) : ℂ) = (W.map τ.1 * (W.map τ.1)ᴴ).det :=
    conj_eq_iff_re.1 (by
      rw [← RCLike.star_def, ← det_conjTranspose, conjTranspose_mul, conjTranspose_conjTranspose])
  rw [h1, det_transpose, ofReal_pow, h2, sq]

theorem exists_short_independent_rows :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (Ψ : Finset (E →+* ℂ)), IsType Ψ →
      ∀ N : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ (m : Type) [Fintype m] (W : Matrix (Fin N) m E),
        LinearIndependent E (fun i => W i) → ∃ a : Matrix (Fin N) (Fin N) E, IntM a ∧ a.det ≠ 0 ∧
          ∏ i, (∑ τ : Ψ, ∑ j, ‖τ.1 ((a * W) i j)‖ ^ 2) ^ Ψ.card ≤
            C * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re := by
  classical
  intro E _ _ _ Ψ hΨ N
  set ω : (E →+* ℂ) → E := fun k => integralBasis E (equivReindex E k) with hω
  have hωi : ∀ k, IsIntegral ℤ (ω k) := fun k => by
    rw [hω]; simp only [integralBasis_apply]; exact RingOfIntegers.isIntegral_coe _
  set A : Matrix (E →+* ℂ) (E →+* ℂ) ℂ := Matrix.of fun k σ : E →+* ℂ => σ (ω k) with hA
  have hA0 : A.det ≠ 0 := by
    have : A = basisMatrix E := by
      ext k σ
      simp only [hA, hω, basisMatrix, of_apply, canonicalEmbedding.latticeBasis_apply,
        canonicalEmbedding.apply_at]
    rw [this]; exact det_of_basisMatrix_non_zero E
  set n : ℕ := Fintype.card (Fin N × (E →+* ℂ)) with hn
  have hc : 0 < (n : ℝ) ^ ((n : ℝ) / 2) := by
    rcases Nat.eq_zero_or_pos n with h | h
    · simp [h]
    · positivity
  have hA1 : 0 < ‖A.det‖ := norm_pos_iff.2 hA0
  refine ⟨(n : ℝ) ^ ((n : ℝ) / 2) * ‖A.det‖ ^ N, by positivity, fun m _ W hW => ?_⟩
  have hpos : 0 < ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re :=
    Finset.prod_pos fun τ _ => (Complex.pos_iff.1 (posDef_map_mul_conjTranspose hW τ.1).det_pos).1
  have hdet : (gram ℝ fun p : Fin N × (E →+* ℂ) => rowEmb W (Pi.single p.1 (ω p.2))).det =
      (‖A.det‖ ^ N * ∏ τ : Ψ, (W.map τ.1 * (W.map τ.1)ᴴ).det.re) ^ 2 := by
    have h := det_gram_rowEmb W ω
    rw [hΨ.prod_det_eq_sq, normSq_eq_norm_sq] at h
    rw [mul_pow, ← pow_mul, mul_comm N, pow_mul]
    exact_mod_cast h
  obtain ⟨a, ha, hai, hle⟩ := exists_linearIndependent_prod_norm_le (E := E) (N := N)
    (by rw [Fintype.card_prod, Fintype.card_fin, Embeddings.card, mul_comm]) (rowEmb W) (fun p : Fin N × (E →+* ℂ) => Pi.single p.1 (ω p.2))
    (det_gram_ne_zero_iff_linearIndependent.1 (by rw [hdet]; positivity))
  refine ⟨Matrix.of a, fun i => ?_, ?_, ?_⟩
  · show ∀ j, IsIntegral ℤ (a i j)
    refine Submodule.span_induction (p := fun t _ => ∀ j, IsIntegral ℤ (t j)) ?_ ?_ ?_ ?_ (hai i)
    · rintro _ ⟨p, rfl⟩ j
      simp only [Pi.single_apply]
      split_ifs
      · exact hωi _
      · exact isIntegral_zero
    · exact fun _ => isIntegral_zero
    · exact fun x y _ _ hx hy j => (hx j).add (hy j)
    · exact fun c x _ hx j => (hx j).smul c
  · exact ((Matrix.isUnit_iff_isUnit_det _).1
      (linearIndependent_row_iff_isUnit.1 (show LinearIndependent E (Matrix.of a).row from ha))).ne_zero
  · rw [hdet, Real.sqrt_sq (by positivity), ← mul_assoc, hΨ.finrank_eq] at hle
    refine le_trans (Finset.prod_le_prod₀ (fun _ _ => by positivity) fun i _ => ?_) hle
    rw [pow_mul, EuclideanSpace.norm_sq_eq, Fintype.sum_prod_type]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    rw [Finset.sum_coe_sort Ψ (fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2)]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ Ψ)
      (f := fun τ => ∑ j, ‖τ ((Matrix.of a * W) i j)‖ ^ 2) fun _ _ _ => by positivity

end GlobalTheory.SW
end

