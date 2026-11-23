module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.AdelicLattices.FactPrimes
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.LocallyFreeOfFiniteProjective
section
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj

open GlobalTheory.CompanionTheory.Ar.Num TensorProduct

theorem exists_local_basis {R L : Type} [CommRing R] [IsDomain R] [AddCommGroup L] [Module R L]
    [Module.Finite R L] [Module.Projective R L] (p : Ideal R) [p.IsPrime] :
    ∃ (n : ℕ) (m : Fin n → L) (s : R), s ∉ p ∧ LinearIndependent R m ∧
      ∀ x : L, s • x ∈ Submodule.span R (Set.range m) := by
  classical
  let Rp := Localization.AtPrime p
  let Lp := LocalizedModule p.primeCompl L
  let f : L →ₗ[R] Lp := LocalizedModule.mkLinearMap p.primeCompl L
  haveI : Module.Free Rp Lp := Module.free_of_flat_of_isLocalRing
  let β := Module.finBasis Rp Lp
  choose ms hms using fun i => IsLocalizedModule.mk'_surjective p.primeCompl f (β i)
  let m : Fin (Module.finrank Rp Lp) → L := fun i => (ms i).1
  let u : Fin (Module.finrank Rp Lp) → Rpˣ := fun i => (IsLocalization.map_units Rp (ms i).2).unit
  have hβ : ∀ i, β.unitsSMul u i = f (m i) := by
    intro i
    rw [Module.Basis.unitsSMul_apply, ← hms i, Units.smul_def]
    simp only [u, IsUnit.unit_spec, algebraMap_smul, Function.uncurry]
    exact IsLocalizedModule.mk'_cancel' f _ _
  have hfun : (β.unitsSMul u : _ → Lp) = f ∘ m := funext hβ
  have hli : LinearIndependent R m := by
    have h1 : LinearIndependent Rp (f ∘ m) := hfun ▸ (β.unitsSMul u).linearIndependent
    have h2 : LinearIndependent R (f ∘ m) := h1.restrict_scalars' R
    exact h2.of_comp f
  have hsp : ∀ x : L, ∃ s : R, s ∉ p ∧ s • x ∈ Submodule.span R (Set.range m) := by
    intro x
    have h1 : f x ∈ (Submodule.span R (Set.range m)).localized' Rp p.primeCompl f := by
      rw [Submodule.localized'_span, ← Set.range_comp, ← hfun, (β.unitsSMul u).span_eq]
      trivial
    obtain ⟨y, hy, s, hs⟩ := (Submodule.mem_localized' _ _ _ _ _).1 h1
    rw [IsLocalizedModule.mk'_eq_iff, Submonoid.smul_def, ← map_smul] at hs
    obtain ⟨c, hc⟩ := IsLocalizedModule.exists_of_eq (S := p.primeCompl) hs
    refine ⟨(c * s : p.primeCompl), (c * s).2, ?_⟩
    rw [Submonoid.coe_mul, mul_smul, ← Submonoid.smul_def, ← hc]
    exact Submodule.smul_mem _ _ hy
  choose s hs hs' using hsp
  obtain ⟨T, hT⟩ := Module.Finite.fg_top (R := R) (M := L)
  refine ⟨_, m, ∏ t ∈ T, s t, ?_, hli, ?_⟩
  · exact Submonoid.prod_mem p.primeCompl (fun t _ => hs t)
  · intro x
    have hx : x ∈ Submodule.span R (T : Set L) := hT ▸ Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem t ht =>
      rw [← Finset.prod_erase_mul T s ht, mul_smul]
      exact Submodule.smul_mem _ _ (hs' t)
    | zero => simp
    | add a b _ _ ha hb => rw [smul_add]; exact Submodule.add_mem _ ha hb
    | smul a b _ hb => rw [smul_comm]; exact Submodule.smul_mem _ _ hb

theorem flat_field {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) :
    Module.Flat R Ω := by
  letI : Algebra (FractionRing R) Ω := FractionRing.liftAlgebra R Ω
  haveI : Module.Flat R (FractionRing R) := IsLocalization.flat _ (nonZeroDivisors R)
  haveI : Module.Free (FractionRing R) Ω := Module.Free.of_divisionRing _ _
  haveI : Module.Flat (FractionRing R) Ω := Module.Flat.of_free
  exact Module.Flat.trans R (FractionRing R) Ω

theorem exists_chart {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type}
    [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E) [Module.Finite R L] [Module.Projective R L]
    (hr : Module.finrank Ω E = r) (hb : IsBaseChange Ω L.subtype) (p : Ideal R) [p.IsPrime] :
    ∃ s : R, s ∉ p ∧ ∃ b : Fin r → E, LinearIndependent Ω b ∧ Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q := by
  classical
  obtain ⟨n, m, s, hs, hli, hsp⟩ := exists_local_basis (L := L) p
  haveI := flat_field R
  have hs0 : (s : Ω) ≠ 0 := fun h => hs (by
    have : s = 0 := Subtype.ext h
    rw [this]; exact p.zero_mem)
  let b : Fin n → E := fun i => (m i : E)
  have hli' : LinearIndependent Ω b := by
    have h1 := (Module.Flat.linearIndependent_one_tmul (S := Ω) hli).map' hb.equiv.toLinearMap
      (LinearEquiv.ker _)
    have hfun : b = (⇑hb.equiv.toLinearMap ∘ fun x => (1 : Ω) ⊗ₜ[R] m x) := by
      funext i
      simp [b, IsBaseChange.equiv_tmul]
    rw [hfun]
    exact h1
  have key : ∀ x : L, ∃ a : Fin n → R, (s : Ω) • (x : E) = ∑ q, (a q : Ω) • b q := by
    intro x
    obtain ⟨a, ha⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 (hsp x)
    refine ⟨a, ?_⟩
    have := congrArg (fun z : L => (z : E)) ha
    simp only [Submodule.coe_sum, Submodule.coe_smul] at this
    exact this.symm
  have hspan : Submodule.span Ω (Set.range b) = ⊤ := by
    rw [eq_top_iff]
    intro e _
    induction e using hb.inductionOn with
    | tmul x =>
      obtain ⟨a, ha⟩ := key x
      rw [← Submodule.smul_mem_iff _ hs0]
      simp only [Submodule.subtype_apply]
      rw [ha]
      exact Submodule.sum_mem _ fun q _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨q, rfl⟩)
    | smul c x hx => exact Submodule.smul_mem _ _ (hx trivial)
    | add x y hx hy => exact Submodule.add_mem _ (hx trivial) (hy trivial)
  have hn : n = r := by
    rw [← hr, Module.finrank_eq_card_basis (Module.Basis.mk hli' hspan.ge), Fintype.card_fin]
  subst hn
  refine ⟨s, hs, b, hli', hspan, fun e => ⟨?_, ?_⟩⟩
  · rintro ⟨k, hk⟩
    obtain ⟨a, ha⟩ := key ⟨_, hk⟩
    refine ⟨fun q => ((s : Ω) ^ (k + 1))⁻¹ * a q, fun q => ⟨k + 1, ?_⟩, ?_⟩
    · rw [mul_inv_cancel_left₀ (pow_ne_zero _ hs0)]; exact (a q).2
    · simp only [mul_smul]
      rw [← Finset.smul_sum, ← ha, smul_smul, smul_smul, mul_assoc, ← pow_succ',
        inv_mul_cancel₀ (pow_ne_zero _ hs0), one_smul]
  · rintro ⟨a, ha, rfl⟩
    choose k hk using ha
    refine ⟨∑ q, k q, ?_⟩
    rw [Finset.smul_sum]
    refine L.toAddSubgroup.sum_mem fun q _ => ?_
    have h1 : (s : Ω) ^ (∑ q, k q) * a q ∈ R := by
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ q), pow_add, mul_assoc]
      exact R.mul_mem (R.pow_mem s.2 _) (hk q)
    rw [smul_smul]
    exact L.smul_mem (⟨_, h1⟩ : R) (m q).2

theorem locFree_of_projective : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] (R : Subalgebra o Ω) {E : Type} [AddCommGroup E] [Module Ω E] (r : ℕ) (L : Submodule R E), Module.Finite R L → Module.Projective R L → Module.finrank Ω E = r → IsBaseChange Ω L.subtype → LocFree R r L.toAddSubgroup := by
  intro o Ω _ _ _ R E _ _ r L _ _ hr hb
  classical
  refine ⟨fun a ha e he => L.smul_mem (⟨a, ha⟩ : R) he, ?_⟩
  let P : R → Prop := fun s => ∃ b : Fin r → E, LinearIndependent Ω b ∧
      Submodule.span Ω (Set.range b) = ⊤ ∧
      ∀ e, (∃ n : ℕ, (s : Ω) ^ n • e ∈ L.toAddSubgroup) ↔
        ∃ a : Fin r → Ω, (∀ q, ∃ n : ℕ, (s : Ω) ^ n * a q ∈ R) ∧ e = ∑ q, a q • b q
  have htop : Ideal.span {s | P s} = ⊤ := by
    by_contra h
    obtain ⟨p, hp, hle⟩ := Ideal.exists_le_maximal _ h
    obtain ⟨s, hs, hP⟩ := exists_chart R r L hr hb p
    exact hs (hle (Ideal.subset_span hP))
  have h1 : (1 : R) ∈ Submodule.span R {s | P s} := by
    change (1 : R) ∈ Ideal.span {s | P s}
    rw [htop]; trivial
  obtain ⟨k, c, g, hg⟩ := Submodule.mem_span_set'.1 h1
  refine ⟨k, fun l => ((g l : R) : Ω), fun l => (c l : Ω), fun l => (g l : R).2, fun l => (c l).2, ?_,
    fun l => (g l).2⟩
  have := congrArg (fun z : R => (z : Ω)) hg
  simpa using this

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeProj
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.MemSpanOverOfMem
section
namespace GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC

open GlobalTheory.CompanionTheory.Ar.Num

variable {o Ω : Type*} [CommRing o] [Field Ω] [Algebra o Ω] {E : Type*} [AddCommGroup E] [Module Ω E]

theorem smul_mem_spanOver (R : Subalgebra o Ω) (S : Set E) {a : Ω} (ha : a ∈ R) {e : E}
    (he : e ∈ spanOver R S) : a • e ∈ spanOver R S := by
  unfold spanOver at he ⊢
  induction he using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, y, hy, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨a * c, R.mul_mem ha hc, y, hy, by rw [mul_smul]⟩
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem mem_spanOver_of_mem (R : Subalgebra o Ω) {S : Set E} {e : E} (he : e ∈ S) :
    e ∈ spanOver R S :=
  AddSubgroup.subset_closure ⟨1, R.one_mem, e, he, (one_smul _ _).symm⟩

theorem frac_add (R : Subalgebra o Ω) {f a b : Ω} (hf : f ∈ R) (ha : ∃ n : ℕ, f ^ n * a ∈ R)
    (hb : ∃ n : ℕ, f ^ n * b ∈ R) : ∃ n : ℕ, f ^ n * (a + b) ∈ R := by
  obtain ⟨n, hn⟩ := ha
  obtain ⟨m, hm⟩ := hb
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) * (a + b) = f ^ m * (f ^ n * a) + f ^ n * (f ^ m * b) := by ring
  rw [this]
  exact R.add_mem (R.mul_mem (R.pow_mem hf _) hn) (R.mul_mem (R.pow_mem hf _) hm)

theorem loc_add (R : Subalgebra o Ω) (L : AddSubgroup E) (hL : ∀ a ∈ R, ∀ e ∈ L, a • e ∈ L)
    {f : Ω} (hf : f ∈ R) {x y : E} (hx : ∃ n : ℕ, f ^ n • x ∈ L) (hy : ∃ n : ℕ, f ^ n • y ∈ L) :
    ∃ n : ℕ, f ^ n • (x + y) ∈ L := by
  obtain ⟨n, hn⟩ := hx
  obtain ⟨m, hm⟩ := hy
  refine ⟨n + m, ?_⟩
  have : f ^ (n + m) • (x + y) = f ^ m • (f ^ n • x) + f ^ n • (f ^ m • y) := by
    rw [smul_add, ← mul_smul, ← mul_smul, ← pow_add, ← pow_add, add_comm m n]
  rw [this]
  exact L.add_mem (hL _ (R.pow_mem hf _) _ hn) (hL _ (R.pow_mem hf _) _ hm)

theorem locFree_baseChange {o Ω Ω₁ : Type} [CommRing o] [Field Ω] [Field Ω₁] [Algebra o Ω]
    [Algebra o Ω₁] [Algebra Ω Ω₁] [IsScalarTower o Ω Ω₁] (R : Subalgebra o Ω)
    (R₁ : Subalgebra o Ω₁) (hR : ∀ a ∈ R, algebraMap Ω Ω₁ a ∈ R₁)
    {E E₁ : Type} [AddCommGroup E] [Module Ω E] [AddCommGroup E₁] [Module Ω₁ E₁] [Module Ω E₁]
    [IsScalarTower Ω Ω₁ E₁] (bc : E →ₗ[Ω] E₁) (hbc : IsBaseChange Ω₁ bc) (r : ℕ)
    (L : AddSubgroup E) (h : LocFree R r L) :
    LocFree R₁ r (spanOver R₁ (bc '' (L : Set E))) := by
  classical
  obtain ⟨hst, k, f, c, hf, hc, hsum, hloc⟩ := h
  have hst₁ : ∀ a ∈ R₁, ∀ e ∈ spanOver R₁ (bc '' (L : Set E)),
      a • e ∈ spanOver R₁ (bc '' (L : Set E)) := fun a ha e he => smul_mem_spanOver R₁ _ ha he
  refine ⟨hst₁, k, fun l => algebraMap Ω Ω₁ (f l), fun l => algebraMap Ω Ω₁ (c l),
    fun l => hR _ (hf l), fun l => hR _ (hc l), ?_, fun l => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · simp only [← map_mul, ← map_sum, hsum, map_one]
  obtain ⟨b, hli, hsp, hb⟩ := hloc l
  beta_reduce
  set F : Ω₁ := algebraMap Ω Ω₁ (f l) with hF
  have hF₁ : F ∈ R₁ := hR _ (hf l)
  let B : Module.Basis (Fin r) Ω E := Module.Basis.mk hli hsp.ge
  let B₁ : Module.Basis (Fin r) Ω₁ E₁ := IsBaseChange.basis B hbc
  have hB₁ : (fun q => bc (b q)) = B₁ := by
    funext q
    simp [B₁, B, IsBaseChange.basis_apply]
  have hB₁' : ∀ q, bc (b q) = B₁ q := fun q => congrFun hB₁ q
  refine ⟨B₁, B₁.linearIndependent, B₁.span_eq, fun e => ⟨?_, ?_⟩⟩
  · have key : ∀ x ∈ spanOver R₁ (bc '' (L : Set E)), ∃ a : Fin r → Ω₁,
        (∀ q, ∃ n : ℕ, F ^ n * a q ∈ R₁) ∧ x = ∑ q, a q • B₁ q := by
      intro x hx
      unfold spanOver at hx
      induction hx using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨t, ht, _, ⟨y, hy, rfl⟩, rfl⟩ := hx
        obtain ⟨a, ha, rfl⟩ := (hb y).1 ⟨0, by simpa using hy⟩
        refine ⟨fun q => t * algebraMap Ω Ω₁ (a q), fun q => ?_, ?_⟩
        · obtain ⟨n, hn⟩ := ha q
          refine ⟨n, ?_⟩
          have := R₁.mul_mem ht (hR _ hn)
          rw [map_mul, map_pow] at this
          convert this using 1
          rw [hF]; ring
        set_option synthInstance.maxHeartbeats 100000 in
          · simp only [map_sum, map_smul, Finset.smul_sum, hB₁', mul_smul, algebraMap_smul]
      | zero => exact ⟨0, fun q => ⟨0, by simp⟩, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨a, ha, rfl⟩ := hx
        obtain ⟨a', ha', rfl⟩ := hy
        exact ⟨a + a', fun q => frac_add R₁ hF₁ (ha q) (ha' q),
          by simp [add_smul, Finset.sum_add_distrib]⟩
      | neg x _ hx =>
        obtain ⟨a, ha, rfl⟩ := hx
        refine ⟨-a, fun q => ?_, by simp⟩
        obtain ⟨n, hn⟩ := ha q
        exact ⟨n, by simpa using R₁.neg_mem hn⟩
    rintro ⟨n, hn⟩
    by_cases h0 : F = 0
    · exact ⟨B₁.repr e, fun q => ⟨1, by simp [h0]⟩, (B₁.sum_repr e).symm⟩
    obtain ⟨a, ha, hea⟩ := key _ hn
    have hFn : F ^ n ≠ 0 := pow_ne_zero _ h0
    refine ⟨fun q => (F ^ n)⁻¹ * a q, fun q => ?_, ?_⟩
    · obtain ⟨m, hm⟩ := ha q
      refine ⟨m + n, ?_⟩
      convert hm using 1
      rw [pow_add]; field_simp
    · simp only [mul_smul, ← Finset.smul_sum]
      rw [← hea, inv_smul_smul₀ hFn]
  · rintro ⟨a, ha, rfl⟩
    refine Finset.sum_induction _
      (fun x : E₁ => ∃ n : ℕ, F ^ n • x ∈ spanOver R₁ (bc '' (L : Set E)))
      (fun x y hx hy => loc_add R₁ _ hst₁ hF₁ hx hy) ⟨0, by simp⟩ (fun q _ => ?_)
    obtain ⟨m, hm⟩ := (hb (b q)).2 ⟨Pi.single q 1, fun q' => ⟨0, by
      by_cases hq : q' = q
      · subst hq; simp
      · simp [hq]⟩, by simp [Pi.single_apply]⟩
    obtain ⟨n, hn⟩ := ha q
    refine ⟨n + m, ?_⟩
    have h1 : bc (f l ^ m • b q) ∈ spanOver R₁ (bc '' (L : Set E)) :=
      mem_spanOver_of_mem R₁ ⟨_, hm, rfl⟩
    have h2 := hst₁ _ hn _ h1
    rw [map_smul, hB₁', ← algebraMap_smul Ω₁ (f l ^ m), map_pow, ← hF, ← mul_smul] at h2
    rw [← mul_smul]
    convert h2 using 2
    ring

end GlobalTheory.CompanionTheory.Ar.Num.LocFreeBC
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.PadicEmbeddingsConjugateOfUnits
section
open NumberField IsDedekindDomain GlobalTheory.CompanionTheory.Ar.Fl

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Br.Conj

open UniformSpace Polynomial

variable {p : ℕ} [Fact p.Prime]

theorem exists_padicAlgCl_factor {K : Type} [Field K] [NumberField K] (κ : K →+* ℂ_[p]) :
    ∃ φ : K →+* PadicAlgCl p, ∀ a, ((φ a : PadicAlgCl p) : ℂ_[p]) = κ a := by
  let j : PadicAlgCl p →+* ℂ_[p] := UniformSpace.Completion.coeRingHom
  have hjinj : Function.Injective j := j.injective
  let _ : Algebra (PadicAlgCl p) ℂ_[p] := j.toAlgebra
  have hmem : ∀ a : K, ∃ y, j y = κ a := by
    intro a
    have ha : IsIntegral ℚ a := IsIntegral.of_finite ℚ a
    have hκ : aeval (κ a) (minpoly ℚ a) = κ (aeval a (minpoly ℚ a)) :=
      Polynomial.aeval_algHom_apply κ.toRatAlgHom a _
    have hint : IsIntegral (PadicAlgCl p) (κ a) := by
      refine ⟨(minpoly ℚ a).map (algebraMap ℚ (PadicAlgCl p)), (minpoly.monic ha).map _, ?_⟩
      rw [eval₂_map]
      have hc : (algebraMap (PadicAlgCl p) ℂ_[p]).comp (algebraMap ℚ (PadicAlgCl p)) =
          algebraMap ℚ ℂ_[p] := RingHom.ext_rat _ _
      rw [hc, ← aeval_def, hκ, minpoly.aeval, map_zero]
    exact RingHom.mem_range.mp (minpoly.mem_range_of_degree_eq_one (PadicAlgCl p) (κ a)
      (IsAlgClosed.degree_eq_one_of_irreducible (PadicAlgCl p) (minpoly.irreducible hint)))
  choose f hf using hmem
  refine ⟨{ toFun := f
            map_one' := hjinj (by rw [hf, map_one, map_one])
            map_mul' := fun a b => hjinj (by rw [hf, map_mul, map_mul, hf, hf])
            map_zero' := hjinj (by rw [hf, map_zero, map_zero])
            map_add' := fun a b => hjinj (by rw [hf, map_add (f := _), map_add (f := _), hf, hf]) }, fun a => hf a⟩

theorem norm_aeval_monomial_sub (x : PadicAlgCl p) (n : ℕ) (r : ℚ) (c : ℚ_[p]) :
    ‖aeval x (monomial n r) - aeval x (monomial n c)‖ = ‖(r : ℚ_[p]) - c‖ * ‖x‖ ^ n := by
  rw [aeval_monomial, aeval_monomial, ← sub_mul, norm_mul, norm_pow,
    eq_ratCast (algebraMap ℚ (PadicAlgCl p)) r,
    ← map_ratCast (algebraMap ℚ_[p] (PadicAlgCl p)) r, ← map_sub, PadicAlgCl.norm_extends]

theorem exists_rat_poly_approx (x y : PadicAlgCl p) (e : ℚ_[p][X]) {ε : ℝ} (hε : 0 < ε) :
    ∃ u : ℚ[X], ‖aeval x u - aeval x e‖ < ε ∧ ‖aeval y u - aeval y e‖ < ε := by
  obtain ⟨N, hN⟩ : ∃ N, e.natDegree < N := ⟨_, Nat.lt_succ_self _⟩
  have hSx : 0 ≤ ∑ i ∈ Finset.range N, ‖x‖ ^ i := Finset.sum_nonneg fun i _ => by positivity
  have hSy : 0 ≤ ∑ i ∈ Finset.range N, ‖y‖ ^ i := Finset.sum_nonneg fun i _ => by positivity
  obtain ⟨δ, hδ0, hδx, hδy⟩ : ∃ δ : ℝ, 0 < δ ∧ δ * ∑ i ∈ Finset.range N, ‖x‖ ^ i < ε ∧
      δ * ∑ i ∈ Finset.range N, ‖y‖ ^ i < ε := by
    have hD : 0 < ∑ i ∈ Finset.range N, ‖x‖ ^ i + ∑ i ∈ Finset.range N, ‖y‖ ^ i + 1 := by linarith
    refine ⟨ε / (∑ i ∈ Finset.range N, ‖x‖ ^ i + ∑ i ∈ Finset.range N, ‖y‖ ^ i + 1),
      div_pos hε hD, ?_, ?_⟩
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      nlinarith [mul_nonneg hε.le hSy]
    · rw [div_mul_eq_mul_div, div_lt_iff₀ hD]
      nlinarith [mul_nonneg hε.le hSx]
  have hr' : ∀ i, ∃ r : ℚ, ‖e.coeff i - (r : ℚ_[p])‖ < δ := fun i => Padic.rat_dense p (e.coeff i) hδ0
  choose r hr using hr'
  have key : ∀ z : PadicAlgCl p, ‖aeval z (∑ i ∈ Finset.range N, monomial i (r i)) - aeval z e‖ ≤
      δ * ∑ i ∈ Finset.range N, ‖z‖ ^ i := by
    intro z
    conv_lhs => rw [e.as_sum_range' N hN]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [norm_aeval_monomial_sub, norm_sub_rev]
    exact mul_le_mul_of_nonneg_right (hr i).le (by positivity)
  exact ⟨_, (key x).trans_lt hδx, (key y).trans_lt hδy⟩

theorem norm_natCast_prime : ‖(p : PadicAlgCl p)‖ = (p : ℝ)⁻¹ := by
  rw [← map_natCast (algebraMap ℚ_[p] (PadicAlgCl p)) p, PadicAlgCl.norm_extends, Padic.norm_p]

theorem minpoly_eq_of_unit_ball {K : Type} [Field K] [NumberField K] (φ ψ : K →+* PadicAlgCl p)
    (h : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1) (θ : K) :
    minpoly ℚ_[p] (φ θ) = minpoly ℚ_[p] (ψ θ) := by
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have hnorm : ∀ (χ : K →+* PadicAlgCl p) (j : ℕ), ‖χ ((p : K) ^ j)⁻¹‖ = ((p : ℝ)⁻¹ ^ j)⁻¹ := by
    intro χ j
    rw [map_inv₀, map_pow, map_natCast, norm_inv, norm_pow, norm_natCast_prime]
  have core : ∀ φ₁ ψ₁ : K →+* PadicAlgCl p, (∀ a, ‖φ₁ a‖ ≤ 1 → ‖ψ₁ a‖ ≤ 1) →
      aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) = 0 := by
    intro φ₁ ψ₁ h₁
    have hφ : ∀ v : ℚ[X], aeval (φ₁ θ) v = φ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply φ₁.toRatAlgHom θ v
    have hψ : ∀ v : ℚ[X], aeval (ψ₁ θ) v = ψ₁ (aeval θ v) := fun v =>
      Polynomial.aeval_algHom_apply ψ₁.toRatAlgHom θ v
    by_contra hne
    have hz : 0 < ‖aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ))‖ := norm_pos_iff.mpr hne
    obtain ⟨j, hj⟩ := exists_pow_lt_of_lt_one (half_pos hz) (inv_lt_one_of_one_lt₀ hp1)
    have ht : 0 < (p : ℝ)⁻¹ ^ j := pow_pos (inv_pos.mpr (by linarith)) j
    obtain ⟨u, hux, huy⟩ := exists_rat_poly_approx (φ₁ θ) (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)) ht
    rw [minpoly.aeval, sub_zero, hφ] at hux
    have h1 : ‖φ₁ (((p : K) ^ j)⁻¹ * aeval θ u)‖ ≤ 1 := by
      rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one]
      exact hux.le
    have h2 := h₁ _ h1
    rw [map_mul, norm_mul, hnorm, inv_mul_le_iff₀ ht, mul_one, ← hψ] at h2
    have h4 := norm_sub_le (aeval (ψ₁ θ) u) (aeval (ψ₁ θ) u - aeval (ψ₁ θ) (minpoly ℚ_[p] (φ₁ θ)))
    rw [sub_sub_cancel] at h4
    linarith
  have hx : IsIntegral ℚ_[p] (φ θ) := Algebra.IsIntegral.isIntegral _
  have hy : IsIntegral ℚ_[p] (ψ θ) := Algebra.IsIntegral.isIntegral _
  have hPQ : minpoly ℚ_[p] (φ θ) ∣ minpoly ℚ_[p] (ψ θ) :=
    minpoly.dvd _ _ (core ψ φ fun a => (h a).mpr)
  refine minpoly.unique' ℚ_[p] (ψ θ) (minpoly.monic hx) (core φ ψ fun a => (h a).mp) fun q hq => ?_
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  · refine Or.inr fun hqy => ?_
    have h3 := Polynomial.natDegree_le_of_dvd (minpoly.dvd _ _ hqy) hq0
    have h4 := Polynomial.natDegree_le_of_dvd hPQ (minpoly.ne_zero hy)
    have h5 := Polynomial.natDegree_lt_natDegree hq0 hq
    omega

theorem exists_extension (σ : PadicAlgCl p ≃+* PadicAlgCl p) (hσ : ∀ x, ‖σ x‖ = ‖x‖) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧
      ∀ x : PadicAlgCl p, g (x : ℂ_[p]) = ((σ x : PadicAlgCl p) : ℂ_[p]) := by
  have hσs : ∀ x, ‖σ.symm x‖ = ‖x‖ := fun x => by rw [← hσ, RingEquiv.apply_symm_apply]
  have hσi : Isometry σ := AddMonoidHomClass.isometry_of_norm σ hσ
  have hτi : Isometry σ.symm := AddMonoidHomClass.isometry_of_norm σ.symm hσs
  let F : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ : PadicAlgCl p →+* PadicAlgCl p) hσi.continuous
  let G : ℂ_[p] →+* ℂ_[p] :=
    UniformSpace.Completion.mapRingHom (σ.symm : PadicAlgCl p →+* PadicAlgCl p) hτi.continuous
  have hF : ∀ x : PadicAlgCl p, F x = (σ x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hσi.continuous x
  have hG : ∀ x : PadicAlgCl p, G x = (σ.symm x : ℂ_[p]) := fun x =>
    UniformSpace.Completion.mapRingHom_coe hτi.continuous x
  have hFc : Continuous F := UniformSpace.Completion.continuous_extension
  have hGc : Continuous G := UniformSpace.Completion.continuous_extension
  have hGF : ∀ z, G (F z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hGc.comp hFc) continuous_id) fun x => ?_
    rw [hF, hG, RingEquiv.symm_apply_apply]
  have hFG : ∀ z, F (G z) = z := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (hFc.comp hGc) continuous_id) fun x => ?_
    rw [hG, hF, RingEquiv.apply_symm_apply]
  have hFn : ∀ z, ‖F z‖ = ‖z‖ := fun z => by
    refine UniformSpace.Completion.induction_on (α := PadicAlgCl p) z
      (isClosed_eq (continuous_norm.comp hFc) continuous_norm) fun x => ?_
    rw [hF, PadicComplex.norm_extends, PadicComplex.norm_extends, hσ]
  refine ⟨{ toFun := fun z => F z
            invFun := fun z => G z
            left_inv := hGF
            right_inv := hFG
            map_mul' := map_mul F
            map_add' := map_add F }, hFn, hF⟩

theorem exists_isometry_conj_of_unit_ball (K : Type) [Field K] [NumberField K] (p : Nat.Primes)
    (κ κ' : K →+* ℂ_[p]) (h : ∀ a : K, ‖κ a‖ ≤ 1 ↔ ‖κ' a‖ ≤ 1) :
    ∃ g : ℂ_[p] ≃+* ℂ_[p], (∀ z, ‖g z‖ = ‖z‖) ∧ ∀ a, g (κ a) = κ' a := by
  obtain ⟨φ, hφ⟩ := exists_padicAlgCl_factor κ
  obtain ⟨ψ, hψ⟩ := exists_padicAlgCl_factor κ'
  have hb : ∀ a, ‖φ a‖ ≤ 1 ↔ ‖ψ a‖ ≤ 1 := fun a => by
    rw [← PadicComplex.norm_extends, ← PadicComplex.norm_extends, hφ, hψ]
    exact h a
  obtain ⟨θ, hθ⟩ := Field.exists_primitive_element ℚ K
  have hm := minpoly_eq_of_unit_ball φ ψ hb θ
  have : Normal ℚ_[p] (PadicAlgCl p) := IsAlgClosure.normal _ _
  obtain ⟨τ, hτ⟩ := MulAction.mem_orbit_iff.mp
    ((Normal.minpoly_eq_iff_mem_orbit (PadicAlgCl p)).mp hm.symm)
  have hτ' : τ (φ θ) = ψ θ := by rw [← AlgEquiv.smul_def]; exact hτ
  have hτn : ∀ x, ‖τ.toRingEquiv x‖ = ‖x‖ := fun x => by
    rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq]
    unfold spectralNorm
    rw [AlgEquiv.coe_ringEquiv, minpoly.algEquiv_eq]
  obtain ⟨g, hgn, hg⟩ := exists_extension τ.toRingEquiv hτn
  have hv : ∀ v : ℚ[X], τ (φ (aeval θ v)) = ψ (aeval θ v) := by
    intro v
    have e1 : φ (aeval θ v) = aeval (φ θ) v := (Polynomial.aeval_algHom_apply φ.toRatAlgHom θ v).symm
    have e2 : ψ (aeval θ v) = aeval (ψ θ) v := (Polynomial.aeval_algHom_apply ψ.toRatAlgHom θ v).symm
    have e3 : τ (aeval (φ θ) v) = aeval (τ (φ θ)) v :=
      (Polynomial.aeval_algHom_apply (τ.toRingEquiv : PadicAlgCl p →+* PadicAlgCl p).toRatAlgHom
        (φ θ) v).symm
    rw [e1, e2, e3, hτ']
  refine ⟨g, hgn, fun a => ?_⟩
  have ha : a ∈ IntermediateField.adjoin ℚ {θ} := by
    rw [hθ]
    exact IntermediateField.mem_top
  obtain ⟨r, s, hrs⟩ := (IntermediateField.mem_adjoin_simple_iff ℚ a).mp ha
  have key : τ (φ a) = ψ a := by
    rw [hrs, map_div₀, map_div₀, map_div₀, hv, hv]
  rw [← hφ, ← hψ, hg]
  exact congrArg _ key

end GlobalTheory.CompanionTheory.Ar.Br.Conj
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.AlgebraProofs.RepresentationBasisLinearIndependent
section
open NumberField

namespace GlobalTheory.CompanionTheory.Ar.Flat

theorem free_of_free_over_field : ∀ (E : Type) [Field E] [NumberField E] (R k : Type) [CommRing R] [IsLocalRing R] [Field k] (f : R →+* k) [IsLocalHom f] (n : Type) [Fintype n] [DecidableEq n] (r : ℕ) (ρ : 𝓞 E →+* Matrix n n R), (∃ x : Fin r → n → k, LinearIndependent k (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) ∧ Submodule.span k (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => ((ρ (RingOfIntegers.basis E q.2)).map f).mulVec (x q.1)) = ⊤) → ∃ x : Fin r → n → R, LinearIndependent R (fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) ∧ Submodule.span R (Set.range fun q : Fin r × Module.Free.ChooseBasisIndex ℤ (𝓞 E) => (ρ (RingOfIntegers.basis E q.2)).mulVec (x q.1)) = ⊤ :=
  @PositivityTheory.Xgn.free_module_nakayama_descent

end GlobalTheory.CompanionTheory.Ar.Flat
end

