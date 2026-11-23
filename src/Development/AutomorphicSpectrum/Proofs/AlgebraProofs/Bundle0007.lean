module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ExtensionEmbeddings.ExtEmb
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.ExistsUniformDenominator
section
namespace GlobalTheory.CompanionTheory.Ar.Num.Reflexive

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem mem_of_locally_mem (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {k : ℕ} (f c : Fin k → Ω) (hf : ∀ l, f l ∈ R)
    (hc : ∀ l, c l ∈ R) (h1 : ∑ l, c l * f l = 1) (v : E) (hv : ∀ l, ∃ n : ℕ, f l ^ n • v ∈ L) :
    v ∈ L := by
  let I : Ideal R :=
    { carrier := {a | (a : Ω) • v ∈ L}
      add_mem' := fun {a b} ha hb => by
        simp only [Set.mem_ofPred_eq, AddMemClass.coe_add, add_smul] at *
        exact L.add_mem ha hb
      zero_mem' := by simp
      smul_mem' := fun a b hb => by
        simp only [Set.mem_ofPred_eq, smul_eq_mul, MulMemClass.coe_mul, mul_smul] at *
        exact hL _ a.2 _ hb }
  have hrad : ∀ l, (⟨f l, hf l⟩ : R) ∈ I.radical := fun l => by
    obtain ⟨n, hn⟩ := hv l
    exact ⟨n, by simpa [I] using hn⟩
  have hone : (1 : R) ∈ I.radical := by
    have : (1 : R) = ∑ l, (⟨c l, hc l⟩ : R) * ⟨f l, hf l⟩ := by
      apply Subtype.ext
      simp [h1]
    rw [this]
    exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (hrad l)
  obtain ⟨n, hn⟩ := hone
  simpa [I] using hn

theorem exists_uniform_pow (R : Subalgebra o Ω) (L : AddSubgroup E)
    (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L) {ι : Type*} [Finite ι] (g : Ω) (hg : g ∈ R) (x : ι → E)
    (hx : ∀ i, ∃ n : ℕ, g ^ n • x i ∈ L) : ∃ n : ℕ, ∀ i, g ^ n • x i ∈ L := by
  classical
  have := Fintype.ofFinite ι
  choose n hn using hx
  refine ⟨∑ i, n i, fun i => ?_⟩
  obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le'
    (Finset.single_le_sum (f := n) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  rw [hd, pow_add, mul_smul]
  exact hL _ (R.pow_mem hg d) _ (hn i)

theorem exists_uniform_denominator (R : Subalgebra o Ω) (r : ℕ) (L : AddSubgroup E)
    (h : LocFree R r L) (g : Ω) (hg : g ∈ R) (ψ : Module.Dual Ω E)
    (hψ : ∀ e ∈ L, ∃ n : ℕ, g ^ n * ψ e ∈ R) : ∃ m : ℕ, ∀ e ∈ L, g ^ m * ψ e ∈ R := by
  classical
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h
  choose b _ _ hb using hb
  let R' : AddSubgroup Ω := R.toSubring.toAddSubgroup
  have hR' : ∀ a ∈ R, ∀ e ∈ R', a • e ∈ R' := fun a ha e he => R.mul_mem ha he
  have hbL : ∀ j q, ∃ n : ℕ, f j ^ n • b j q ∈ L := fun j q => by
    refine (hb j (b j q)).2 ⟨Pi.single q 1, fun q' => ⟨0, ?_⟩, ?_⟩
    · by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]
    · simp [Pi.single_apply]
  choose N hN using hbL
  obtain ⟨m, hm⟩ := exists_uniform_pow R R' hR' g hg
    (fun p : Fin k × Fin r => ψ (f p.1 ^ N p.1 p.2 • b p.1 p.2)) (fun p => hψ _ (hN p.1 p.2))
  refine ⟨m, fun e he => ?_⟩
  refine mem_of_locally_mem R R' hR' f c hf hc h1 _ fun j => ?_
  obtain ⟨a, ha, rfl⟩ := (hb j e).1 ⟨0, by simpa using he⟩
  have key : ∀ q, ∃ n : ℕ, f j ^ n • (g ^ m * (a q * ψ (b j q))) ∈ R' := fun q => by
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + N j q, ?_⟩
    have h2 : g ^ m * ψ (f j ^ N j q • b j q) ∈ R := hm (j, q)
    have h3 := R.mul_mem hn h2
    have h4 : f j ^ (n + N j q) • (g ^ m * (a q * ψ (b j q)))
        = f j ^ n * a q * (g ^ m * ψ (f j ^ N j q • b j q)) := by
      simp only [map_smul, smul_eq_mul]; ring
    rw [h4]; exact h3
  obtain ⟨n, hn⟩ := exists_uniform_pow R R' hR' (f j) (hf j) _ key
  refine ⟨n, ?_⟩
  have h5 : f j ^ n • (g ^ m * ψ (∑ q, a q • b j q))
      = ∑ q, f j ^ n • (g ^ m * (a q * ψ (b j q))) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, smul_eq_mul, Finset.mul_sum]
  rw [h5]
  exact R'.sum_mem fun q _ => hn q

theorem locFree_reflexive : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : AddSubgroup E), LocFree R r L → ∀ v : E, (∀ ψ : Module.Dual Ω E, (∀ e ∈ L, ψ e ∈ R) → ψ v ∈ R) → v ∈ L := by
  intro o Ω _ _ _ R E _ _ r L h v hv
  have h' := h
  obtain ⟨hL, k, f, c, hf, hc, h1, hb⟩ := h'
  refine mem_of_locally_mem R L hL f c hf hc h1 v fun l => ?_
  obtain ⟨b, hli, hsp, hb⟩ := hb l
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  have hB : ∀ q, B q = b q := fun q => Module.Basis.mk_apply _ _ q
  refine (hb v).2 ⟨fun q => B.coord q v, fun q => ?_, ?_⟩
  · obtain ⟨m, hm⟩ := exists_uniform_denominator R r L h (f l) (hf l) (B.coord q) fun e he => by
      obtain ⟨a, ha, rfl⟩ := (hb e).1 ⟨0, by simpa using he⟩
      have : B.coord q (∑ q, a q • b q) = a q := by
        simp only [← hB, Module.Basis.coord_apply]
        exact congrFun (B.repr_sum_self a) q
      rw [this]; exact ha q
    exact ⟨m, by simpa using hv (f l ^ m • B.coord q) (by simpa using hm)⟩
  · simp only [← hB, Module.Basis.coord_apply]
    exact (B.sum_repr v).symm

end GlobalTheory.CompanionTheory.Ar.Num.Reflexive
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FinitePresentationOfFaithfullyFlat
section
namespace GlobalTheory.CompanionTheory.FinPresDescent

theorem finiteType_of_finite_projective (R C D : Type*) [CommRing R] [CommRing C] [CommRing D]
    [Algebra R C] [Algebra C D] [Algebra R D] [IsScalarTower R C D]
    [Module.Finite C D] [Module.Projective C D] (hinj : Function.Injective (algebraMap C D))
    [Algebra.FiniteType R D] : Algebra.FiniteType R C :=
  _root_.UpperTheory.Reformulated.B.FiniteTypeDescent.main R C D hinj

theorem ker_fg_of_projective {P C M : Type*} [CommRing P] [CommRing C] [Algebra P C]
    [AddCommGroup M] [Module P M] [Module C M] [IsScalarTower P C M]
    (hsurj : Function.Surjective (algebraMap P C))
    [Module.FinitePresentation P M] [Module.Projective C M]
    (faith : ∀ c : C, (∀ m : M, c • m = 0) → c = 0) :
    (RingHom.ker (algebraMap P C)).FG := by
  classical
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' P M
  have hker : (LinearMap.ker π).FG := Module.FinitePresentation.fg_ker π hπ
  let b : Fin n → M := fun i => π (Pi.single i 1)
  have hπb : ∀ x, π x = ∑ i, x i • b i := fun x => by
    rw [LinearMap.pi_apply_eq_sum_univ π x]
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 2
    ext j
    simp [b, Pi.single_apply, eq_comm]
  have hπC : ∀ x, π x = ∑ i, algebraMap P C (x i) • b i := fun x => by
    rw [hπb]
    simp only [algebraMap_smul]
  let πC : (Fin n → C) →ₗ[C] M := Fintype.linearCombination C b
  have hπCs : Function.Surjective πC := by
    intro m
    obtain ⟨x, rfl⟩ := hπ m
    refine ⟨fun i => algebraMap P C (x i), ?_⟩
    rw [hπC, Fintype.linearCombination_apply]
  obtain ⟨s, hs⟩ := Module.projective_lifting_property πC LinearMap.id hπCs
  have hs' : ∀ m, ∑ i, s m i • b i = m := fun m => by
    have := LinearMap.congr_fun hs m
    simpa [πC, Fintype.linearCombination_apply] using this
  choose v hv using fun (p : Fin n × Fin n) => hsurj (s (b p.1) p.2)
  let E : (Fin n → P) → Fin n → P := fun x j => ∑ i, x i * v (i, j)
  have key1 : ∀ x j, algebraMap P C (E x j) = s (π x) j := fun x j => by
    have hsx : s (π x) = ∑ i, algebraMap P C (x i) • s (b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hπC, map_sum]
      simp only [map_smul]
    rw [hsx, Finset.sum_apply]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [E, map_sum, map_mul, hv, Pi.smul_apply, smul_eq_mul]
  have key2 : ∀ x, π (fun j => E x j) = π x := fun x => by
    rw [hπC]
    simp only [key1]
    exact hs' _
  obtain ⟨G, hG⟩ := hker
  let I₀ : Ideal P := Ideal.span ((fun q : (Fin n → P) × Fin n => E q.1 q.2) ''
    ((G : Set (Fin n → P)) ×ˢ Set.univ))
  have hI₀ : I₀.FG := ⟨(G ×ˢ Finset.univ).image (fun q : (Fin n → P) × Fin n => E q.1 q.2), by
    simp [I₀]⟩
  have key3 : ∀ x ∈ LinearMap.ker π, ∀ j, E x j ∈ I₀ := by
    intro x hx j
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Ideal.subset_span ⟨(x, j), ⟨hx, trivial⟩, rfl⟩
    | zero => simp [E]
    | add x y _ _ hx hy =>
      have : E (x + y) j = E x j + E y j := by simp [E, add_mul, Finset.sum_add_distrib]
      rw [this]; exact I₀.add_mem hx hy
    | smul t x _ hx =>
      have : E (t • x) j = t * E x j := by simp [E, Finset.mul_sum, mul_assoc]
      rw [this]; exact I₀.mul_mem_left t hx
  let T : Ideal P := Ideal.span (Set.range v)
  have hET : ∀ x j, E x j ∈ T := fun x j =>
    T.sum_mem fun i _ => T.mul_mem_left _ (Ideal.subset_span ⟨(i, j), rfl⟩)
  have hle : (⊤ : Submodule P M) ≤ T • (⊤ : Submodule P M) := by
    intro m _
    obtain ⟨x, rfl⟩ := hπ m
    rw [← key2, hπb]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul (hET x i) trivial
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul T ⊤
    Module.Finite.fg_top hle
  have hrI : r ∈ RingHom.ker (algebraMap P C) := by
    rw [RingHom.mem_ker]
    refine faith _ fun m => ?_
    rw [algebraMap_smul]
    exact hr0 m trivial
  have key5 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ p, a * v p ∈ I₀ := by
    rintro a ha ⟨i, j⟩
    have hx : (Pi.single i a : Fin n → P) ∈ LinearMap.ker π := by
      rw [LinearMap.mem_ker, hπC]
      refine Finset.sum_eq_zero fun k _ => ?_
      by_cases hk : k = i
      · subst hk
        rw [Pi.single_eq_same, RingHom.mem_ker.1 ha, zero_smul]
      · rw [Pi.single_eq_of_ne hk, map_zero, zero_smul]
    have := key3 _ hx j
    simpa [E, Pi.single_apply] using this
  have key6 : ∀ a ∈ RingHom.ker (algebraMap P C), ∀ t ∈ T, a * t ∈ I₀ := by
    intro a ha t ht
    induction ht using Submodule.span_induction with
    | mem t ht => obtain ⟨p, rfl⟩ := ht; exact key5 a ha p
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add]; exact I₀.add_mem hx hy
    | smul c x _ hx =>
      rw [smul_eq_mul, mul_left_comm]; exact I₀.mul_mem_left c hx
  have hI₀le : I₀ ≤ RingHom.ker (algebraMap P C) := by
    refine Ideal.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, ⟨hg, -⟩, rfl⟩
    have hgk : g ∈ LinearMap.ker π := by
      rw [← hG]; exact Submodule.subset_span hg
    change algebraMap P C (E g j) = 0
    rw [key1, LinearMap.mem_ker.1 hgk, map_zero]
    rfl
  have heq : RingHom.ker (algebraMap P C) = I₀ ⊔ Ideal.span {r} := by
    apply le_antisymm
    · intro a ha
      have h1 : a * (r - 1) ∈ I₀ := key6 a ha _ hr
      have h2 : a * r ∈ Ideal.span {r} := Ideal.mul_mem_left _ a (Ideal.mem_span_singleton_self r)
      have : a = a * r + -(a * (r - 1)) := by ring
      rw [this]
      exact Submodule.add_mem_sup h2 (I₀.neg_mem h1) |> fun h => by
        rw [sup_comm]; exact h
    · refine sup_le hI₀le ?_
      rw [Ideal.span_singleton_le_iff_mem]
      exact hrI
  rw [heq]
  exact Submodule.FG.sup hI₀ (Submodule.fg_span_singleton r)

end GlobalTheory.CompanionTheory.FinPresDescent


open GlobalTheory.CompanionTheory.FinPresDescent in
theorem GlobalTheory.CompanionTheory.FinPresDescent.finitePresentation_of_finite_projective_faithfullyFlat :
    ∀ (R C D : Type) [CommRing R] [CommRing C] [CommRing D] [Algebra R C] [Algebra C D]
      [Algebra R D] [IsScalarTower R C D], Module.Finite C D → Module.Projective C D →
      Module.FaithfullyFlat C D → Algebra.FinitePresentation R D →
      Algebra.FinitePresentation R C := by
  intro R C D _ _ _ _ _ _ _ hfin hproj hff hfp
  have hinj : Function.Injective (algebraMap C D) := FaithfulSMul.algebraMap_injective C D
  haveI : Algebra.FiniteType R D := inferInstance
  haveI : Algebra.FiniteType R C := finiteType_of_finite_projective R C D hinj
  obtain ⟨k, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.1 ‹Algebra.FiniteType R C›
  letI : Algebra (MvPolynomial (Fin k) R) C := f.toRingHom.toAlgebra
  letI : Algebra (MvPolynomial (Fin k) R) D := ((algebraMap C D).comp f.toRingHom).toAlgebra
  haveI : IsScalarTower (MvPolynomial (Fin k) R) C D := .of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R (MvPolynomial (Fin k) R) D := .of_algebraMap_eq fun r => by
    change algebraMap R D r = algebraMap C D (f (algebraMap R _ r))
    rw [f.commutes, ← IsScalarTower.algebraMap_apply]
  haveI : Algebra.FinitePresentation (MvPolynomial (Fin k) R) D :=
    Algebra.FinitePresentation.of_restrict_scalars_finitePresentation R _ D
  haveI : Module.Finite (MvPolynomial (Fin k) R) C :=
    Module.Finite.of_surjective (Algebra.linearMap _ C) hf
  haveI : Module.Finite (MvPolynomial (Fin k) R) D := Module.Finite.trans C D
  haveI : Module.FinitePresentation (MvPolynomial (Fin k) R) D :=
    Module.FinitePresentation.of_finite_of_finitePresentation _ D
  have hker := ker_fg_of_projective (P := MvPolynomial (Fin k) R) (C := C) (M := D) hf
    (fun c hc => hinj (by simpa [Algebra.smul_def] using hc 1))
  exact ⟨k, f, hf, hker⟩
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FixedByAutomorphismsMemField
section
open NumberField IsDedekindDomain
open scoped Cardinal Polynomial IntermediateField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem mk_le_aleph0_of_finite (F : IntermediateField ℚ ℂ) (hF : FiniteDimensional ℚ F) :
    Cardinal.mk F ≤ Cardinal.aleph0 := by
  have h := Algebra.IsAlgebraic.cardinalMk_le_max ℚ F
  simpa using h

theorem mk_ratFunc_le_aleph0 (F : Type) [Field F] (hF : Cardinal.mk F ≤ Cardinal.aleph0) :
    Cardinal.mk (RatFunc F) ≤ Cardinal.aleph0 := by
  have : Countable F[X] :=
    Cardinal.mk_le_aleph0_iff.1 (Polynomial.cardinalMk_le_max.trans (max_le hF le_rfl))
  have hs : Function.Surjective (fun p : F[X] × F[X] =>
      algebraMap F[X] (RatFunc F) p.1 / algebraMap F[X] (RatFunc F) p.2) := by
    intro x
    obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective (A := F[X]) x
    exact ⟨(a, b), rfl⟩
  have : Countable (RatFunc F) := hs.countable
  exact Cardinal.mk_le_aleph0

theorem exists_moved_of_transcendental (F : IntermediateField ℚ ℂ)
    (hF : Cardinal.mk F ≤ Cardinal.aleph0) (c : ℂ) (hc : Transcendental F c) :
    ∃ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) ∧ g c ≠ c := by
  have hc1 : Transcendental F (c + 1) := fun h =>
    hc (by simpa using h.sub (isAlgebraic_one (R := F) (A := ℂ)))
  have i0 : Function.Injective (Polynomial.aeval (R := F) c).toRingHom :=
    transcendental_iff_injective.1 hc
  have i1 : Function.Injective (Polynomial.aeval (R := F) (c + 1)).toRingHom :=
    transcendental_iff_injective.1 hc1
  let f : RatFunc F →+* ℂ := IsFractionRing.lift i0
  let g : RatFunc F →+* ℂ := IsFractionRing.lift i1
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.ChartRestriction.B3.iop_extEmb f g (mk_ratFunc_le_aleph0 F hF)
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl
  have hfa : ∀ p : F[X], f (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval c p := fun p =>
    IsFractionRing.lift_algebraMap i0 p
  have hga : ∀ p : F[X], g (algebraMap F[X] (RatFunc F) p) = Polynomial.aeval (c + 1) p := fun p =>
    IsFractionRing.lift_algebraMap i1 p
  refine ⟨σ, fun a ha => ?_, fun h => ?_⟩
  · have := hσ (algebraMap F[X] (RatFunc F) (Polynomial.C ⟨a, ha⟩))
    rw [hfa, hga] at this
    simpa using this
  · have := hσ (algebraMap F[X] (RatFunc F) Polynomial.X)
    rw [hfa, hga] at this
    simp only [Polynomial.aeval_X] at this
    rw [h] at this
    simpa using this

theorem exists_moved_of_isAlgebraic (F : IntermediateField ℚ ℂ)
    (hF : Cardinal.mk F ≤ Cardinal.aleph0) (c : ℂ) (hc : IsAlgebraic F c) (hcF : c ∉ F) :
    ∃ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) ∧ g c ≠ c := by
  have hi : IsIntegral F c := hc.isIntegral
  have hsep : (minpoly F c).Separable := (minpoly.irreducible hi).separable
  have hsplit : ((minpoly F c).map (algebraMap F ℂ)).Splits := IsAlgClosed.splits _
  have hdeg : (minpoly F c).natDegree ≠ 1 := by
    intro h1
    have : (minpoly F c).degree = 1 := by
      rw [Polynomial.degree_eq_natDegree (minpoly.ne_zero hi), h1]; rfl
    obtain ⟨a, rfl⟩ := minpoly.mem_range_of_degree_eq_one F c this
    exact hcF a.2
  have hpos := minpoly.natDegree_pos hi
  have hcard := Polynomial.card_rootSet_eq_natDegree (K := ℂ) hsep hsplit
  have hmem : c ∈ (minpoly F c).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    exact ⟨minpoly.ne_zero hi, minpoly.aeval F c⟩
  obtain ⟨⟨c', hc'⟩, hne⟩ := Fintype.exists_ne_of_one_lt_card
    (by rw [hcard]; omega) (⟨c, hmem⟩ : (minpoly F c).rootSet ℂ)
  have hne' : c' ≠ c := fun h => hne (Subtype.ext h)
  have hroot : c' ∈ (minpoly F c).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    exact (Polynomial.mem_rootSet.1 hc')
  let g0 : F⟮c⟯ →ₐ[F] ℂ := (IntermediateField.algHomAdjoinIntegralEquiv F hi).symm ⟨c', hroot⟩
  have hg0 : g0 (IntermediateField.AdjoinSimple.gen F c) = c' :=
    IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen F hi ⟨c', hroot⟩
  have hfin : FiniteDimensional F F⟮c⟯ := IntermediateField.adjoin.finiteDimensional hi
  have hE : Cardinal.mk F⟮c⟯ ≤ Cardinal.aleph0 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max F F⟮c⟯).trans (max_le hF le_rfl)
  obtain ⟨σ, hσ⟩ := ReciprocityTheory.ChartRestriction.B3.iop_extEmb (algebraMap F⟮c⟯ ℂ) g0.toRingHom hE
    (by simp [Cardinal.mk_complex, Cardinal.aleph0_lt_continuum]) rfl
  refine ⟨σ, fun a ha => ?_, fun h => ?_⟩
  · have := hσ (algebraMap F F⟮c⟯ ⟨a, ha⟩)
    have h2 : g0.toRingHom (algebraMap F F⟮c⟯ ⟨a, ha⟩) = a := by
      simpa using g0.commutes ⟨a, ha⟩
    rw [h2] at this
    simpa using this
  · have := hσ (IntermediateField.AdjoinSimple.gen F c)
    have h2 : algebraMap F⟮c⟯ ℂ (IntermediateField.AdjoinSimple.gen F c) = c := rfl
    rw [h2, h] at this
    exact hne' (hg0.symm.trans this.symm)

theorem mem_of_fixed_aut : ∀ (F : IntermediateField ℚ ℂ) (c : ℂ), FiniteDimensional ℚ F →
    (∀ g : ℂ ≃+* ℂ, (∀ a ∈ F, g a = a) → g c = c) → c ∈ F := by
  intro F c hF h
  by_contra hcF
  have hcount := mk_le_aleph0_of_finite F hF
  by_cases hc : IsAlgebraic F c
  · obtain ⟨g, hg, hne⟩ := exists_moved_of_isAlgebraic F hcount c hc hcF
    exact hne (h g hg)
  · obtain ⟨g, hg, hne⟩ := exists_moved_of_transcendental F hcount c hc
    exact hne (h g hg)

end GlobalTheory.CompanionTheory.Ar.Flat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FrobeniusChainCarry
section
open scoped Matrix TensorProduct
open Matrix

namespace GlobalTheory.CompanionTheory.Ar.GR

theorem frobeniusChain_carry : ∀ (p f : ℕ), 2 ≤ p → 0 < f → ∀ (y : ℕ → NNReal), (∀ n, y (n + f) = y n) → (∀ n, y n ≤ 1) → (∀ n, y n ^ p ≤ y (n + 1)) → ∀ (e : Fin f → ℕ) (j : ℕ), 2 ≤ ∑ n, e n → (∑ n : Fin f, e n * p ^ (n : ℕ)) ≡ p ^ (j + 1) [MOD (p ^ f - 1)] → ∏ n : Fin f, y n ^ e n ≤ y j ^ p :=
  PositivityTheory.HtPt.Ra.carry

end GlobalTheory.CompanionTheory.Ar.GR
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderTranslationInvariant
section
open GlobalTheory.CompanionTheory.Ar.BT TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate

theorem translate_mem_of_isHopfOrder : ∀ (R : Type) [CommRing R] (T : Type) [CommGroup T] (A : Subalgebra R (T → R)),
    IsHopfOrder A → ∀ f ∈ A, ∀ t, (fun h => f (t * h)) ∈ A := by
  intro R _ T _ A hA f hf t
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨a, -, b, hb, rfl⟩ := hg
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

end GlobalTheory.CompanionTheory.Ar.BT.HopfTranslate
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.IsSplitInjectiveAndExists
section
open TensorProduct

namespace GlobalTheory.CompanionTheory.Ar.Crv

theorem isSplit_injective_and_exists (O k S : Type) [CommRing O] [Field k] [Fintype S]
    (χ : S → (O →+* k)) (h : IsSplit χ) :
    Function.Injective χ ∧ ∀ ψ : O →+* k, ∃ s, χ s = ψ := by
  classical
  unfold IsSplit at h
  set F := Algebra.TensorProduct.lift (Algebra.ofId k (S → k))
    (Pi.algHom ℤ (fun _ : S => k) fun s => (χ s).toIntAlgHom)
    (fun _ _ => Commute.all _ _) with hF
  have hv : ∀ (a : k) (x : O) (s : S), F (a ⊗ₜ[ℤ] x) s = a * χ s x := by
    intro a x s
    simp [hF, Algebra.ofId_apply]
  constructor
  · intro s t hst
    by_contra hne
    obtain ⟨y, hy⟩ := h.2 (Pi.single s 1)
    have key : ∀ y : TensorProduct ℤ k O, F y s = F y t := by
      intro y
      induction y using TensorProduct.induction_on with
      | zero => simp
      | tmul a x => rw [hv, hv, hst]
      | add u v hu hv' => simp [map_add (f := _), hu, hv']
    have h1 := key y
    rw [hy] at h1
    simp [Pi.single_apply, Ne.symm hne] at h1
  · intro ψ
    let Ψ : TensorProduct ℤ k O →ₐ[k] k :=
      Algebra.TensorProduct.lift (AlgHom.id k k) ψ.toIntAlgHom (fun _ _ => Commute.all _ _)
    choose y hy using fun s => h.2 (Pi.single s (1 : k))
    have hsum : ∑ s, y s = 1 := by
      apply h.1
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, map_one]
      simp only [hy]
      ext t
      simp [Finset.sum_apply, Pi.single_apply]
    have hne : ∑ s, Ψ (y s) ≠ 0 := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← map_sum, hsum, map_one]
      exact one_ne_zero
    obtain ⟨s, -, hs⟩ := Finset.exists_ne_zero_of_sum_ne_zero hne
    refine ⟨s, ?_⟩
    have hmul : ∀ z, z * y s = (F z s) • y s := by
      intro z
      apply h.1
      rw [map_mul, map_smul, hy]
      ext t
      by_cases hts : t = s
      · subst hts
        simp
      · simp [Pi.single_apply, hts]
    ext o
    have h1 := congrArg Ψ (hmul ((1 : k) ⊗ₜ[ℤ] o))
    have h2 : Ψ ((1 : k) ⊗ₜ[ℤ] o) = ψ o := by
      simp [Ψ]
    rw [map_mul, map_smul, hv, h2, smul_eq_mul, one_mul] at h1
    exact (mul_right_cancel₀ hs h1).symm

end GlobalTheory.CompanionTheory.Ar.Crv
end

