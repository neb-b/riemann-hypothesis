module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemSaturatedOrderIsoSubspaceSpanSymmApply
public import ReciprocityTheory.SemistableReduction.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001

@[expose] public section

open IsDedekindDomain IsDedekindDomain.HeightOneSpectrum Matrix
open scoped nonZeroDivisors

noncomputable section

namespace GlobalTheory.LocalLattice

set_option linter.unusedSectionVars false

section Denominators

variable {O K : Type*} [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K]
  {A : Type*} [CommRing A] [Algebra O A] [Algebra A K] [IsScalarTower O A K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [Module A V] [IsScalarTower O K V]
  [IsScalarTower A K V] [IsScalarTower O A V]


omit [IsDomain O] [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in
theorem exists_smul_mem {N : Submodule A V} (hN : Submodule.span K (N : Set V) = ⊤) (x : V) :
    ∃ d ∈ O⁰, d • x ∈ N :=
  (mem_span_localization_iff K O⁰ (N.restrictScalars O) x).1 (by
    rw [Submodule.coe_restrictScalars, hN]; trivial)


omit [IsDomain O] [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in
theorem exists_smul_mem_of_finite {N : Submodule A V} (hN : Submodule.span K (N : Set V) = ⊤)
    {s : Set V} (hs : s.Finite) : ∃ d ∈ O⁰, ∀ x ∈ s, d • x ∈ N := by
  induction s, hs using Set.Finite.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | @insert a s _ _ ih =>
    obtain ⟨d, hd, h⟩ := ih
    obtain ⟨e, he, h'⟩ := exists_smul_mem (O := O) hN a
    refine ⟨d * e, mul_mem hd he, ?_⟩
    rintro x (rfl | hx)
    · rw [mul_smul]; exact N.smul_of_tower_mem d h'
    · rw [mul_comm, mul_smul]; exact N.smul_of_tower_mem e (h x hx)


omit [IsDomain O] [IsScalarTower O A K] [IsScalarTower A K V] [Algebra A K] in
theorem exists_smul_le {M N : Submodule A V} (hM : M.FG)
    (hN : Submodule.span K (N : Set V) = ⊤) : ∃ d ∈ O⁰, ∀ x ∈ M, d • x ∈ N := by
  obtain ⟨s, rfl⟩ := hM
  obtain ⟨d, hd, h⟩ := exists_smul_mem_of_finite (O := O) hN s.finite_toSet
  refine ⟨d, hd, fun x hx => ?_⟩
  induction hx using Submodule.span_induction with
  | mem x hx => exact h x hx
  | zero => simp
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | smul a x _ hx => rw [smul_comm]; exact N.smul_mem a hx



end Denominators

section Localize

variable {O : Type*} (K : Type*) [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]
  {V : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]

instance instIsScalarTowerLocalRing (v : HeightOneSpectrum O) :
    IsScalarTower O (v.valuationSubringAtPrime K) V :=
  IsScalarTower.to₁₂₄ O (v.valuationSubringAtPrime K) K V

def localize (v : HeightOneSpectrum O) (L : Submodule O V) :
    Submodule (v.valuationSubringAtPrime K) V :=
  Submodule.span _ (L : Set V)

variable {K}

theorem localize_def (v : HeightOneSpectrum O) (L : Submodule O V) :
    localize K v L = Submodule.span (v.valuationSubringAtPrime K) (L : Set V) := rfl

theorem mem_localRing_iff_valuation (v : HeightOneSpectrum O) (x : K) :
    x ∈ v.valuationSubringAtPrime K ↔ v.valuation K x ≤ 1 := by
  rw [valuationSubringAtPrime_eq_valuationSubring]; rfl

theorem mem_localize_iff (v : HeightOneSpectrum O) (L : Submodule O V) (x : V) :
    x ∈ localize K v L ↔ ∃ s ∉ v.asIdeal, s • x ∈ L :=
  mem_span_localization_iff _ v.asIdeal.primeCompl L x

theorem mem_localize_of_mem (v : HeightOneSpectrum O) {L : Submodule O V} {x : V} (hx : x ∈ L) :
    x ∈ localize K v L := Submodule.subset_span hx

theorem mem_localRing_iff (v : HeightOneSpectrum O) (x : K) :
    x ∈ v.valuationSubringAtPrime K ↔ ∃ s ∉ v.asIdeal, s • x ∈ (1 : Submodule O K) := by
  rw [← mem_localize_iff (K := K), localize_def, Submodule.one_eq_span,
    Submodule.span_span_of_tower, Submodule.mem_span_singleton]
  constructor
  · intro hx; exact ⟨⟨x, hx⟩, mul_one x⟩
  · rintro ⟨a, rfl⟩
    have : a • (1 : K) = a := mul_one (a : K)
    rw [this]; exact a.2

theorem mem_of_forall_mem_localize {L : Submodule O V} {x : V}
    (hx : x ∈ Submodule.span K (L : Set V)) (h : ∀ v : HeightOneSpectrum O, x ∈ localize K v L) :
    x ∈ L := by
  obtain ⟨d, hd, hdx⟩ := (mem_span_localization_iff K O⁰ L x).1 hx
  by_contra hxL
  let J : Ideal O := L.comap (LinearMap.toSpanSingleton O V x)
  have hJ : J ≠ ⊤ := fun hJ => hxL (by simpa [J] using (Ideal.eq_top_iff_one J).1 hJ)
  obtain ⟨m, hm, hJm⟩ := Ideal.exists_le_maximal J hJ
  have hm0 : m ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero hd (by
    simpa [h0] using hJm (show d ∈ J from hdx))
  obtain ⟨s, hs, hsx⟩ := (mem_localize_iff _ L x).1 (h ⟨m, hm.isPrime, hm0⟩)
  exact hs (hJm (show s ∈ J from hsx))

theorem mem_of_forall_mem_localize_of_not_isField (hO : ¬ IsField O) {L : Submodule O V} {x : V}
    (h : ∀ v : HeightOneSpectrum O, x ∈ localize K v L) : x ∈ L := by
  obtain ⟨m, hm0, hm⟩ := Ring.not_isField_iff_exists_prime.1 hO
  refine mem_of_forall_mem_localize ?_ h
  exact Submodule.span_le_restrictScalars
    ((⟨m, hm, hm0⟩ : HeightOneSpectrum O).valuationSubringAtPrime K) K _ (h ⟨m, hm, hm0⟩)

theorem eventually_notMem {d : O} (hd : d ∈ O⁰) :
    ∀ᶠ v : HeightOneSpectrum O in Filter.cofinite, d ∉ v.asIdeal := by
  have := Ideal.finite_factors (I := Ideal.span {d}) (by simpa using nonZeroDivisors.ne_zero hd)
  simpa [Filter.eventually_cofinite, Ideal.dvd_span_singleton] using this

omit [IsDedekindDomain O] in
theorem exists_mem_submonoid_forall {ι : Type*} {T : Set ι} (hT : T.Finite) (S : Submonoid O)
    (P : ι → O → Prop) (hP : ∀ i s t, P i s → P i (t * s)) (h : ∀ i ∈ T, ∃ s ∈ S, P i s) :
    ∃ s ∈ S, ∀ i ∈ T, P i s := by
  induction T, hT using Set.Finite.induction_on with
  | empty => exact ⟨1, one_mem _, by simp⟩
  | @insert a T _ _ ih =>
    obtain ⟨d, hd, h₁⟩ := ih fun i hi => h i (Set.mem_insert_of_mem _ hi)
    obtain ⟨e, he, h₂⟩ := h a (Set.mem_insert _ _)
    refine ⟨d * e, mul_mem hd he, ?_⟩
    rintro x (rfl | hx)
    · exact hP _ _ _ h₂
    · rw [mul_comm]; exact hP _ _ _ (h₁ x hx)

end Localize

section Frame

variable (A : Type*) {K : Type*} [CommRing A] [Field K] [Algebra A K]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def frameLattice (g : GL ι K) : Submodule A (ι → K) :=
  Submodule.span A (Set.range (g : Matrix ι ι K).col)

variable {A}

theorem mem_frameLattice_iff (g : GL ι K) (x : ι → K) :
    x ∈ frameLattice A g ↔
      ∃ a : ι → A, (g : Matrix ι ι K) *ᵥ (fun i => algebraMap A K (a i)) = x := by
  rw [frameLattice, Submodule.mem_span_range_iff_exists_fun]
  refine exists_congr fun a => ?_
  have : (g : Matrix ι ι K) *ᵥ (fun i => algebraMap A K (a i)) =
      ∑ i, a i • (g : Matrix ι ι K).col i := by
    ext j
    simp [Matrix.mulVec, dotProduct, Algebra.smul_def, mul_comm]
  rw [this]

theorem mem_frameLattice_iff_inv (g : GL ι K) (x : ι → K) :
    x ∈ frameLattice A g ↔
      ∀ i, (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ x) i ∈ (1 : Submodule A K) := by
  rw [mem_frameLattice_iff]
  constructor
  · rintro ⟨a, rfl⟩ i
    rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
    exact Submodule.mem_one.2 ⟨a i, rfl⟩
  · intro h
    simp only [Submodule.mem_one] at h
    choose a ha using h
    refine ⟨a, ?_⟩
    rw [funext ha, Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]

instance isLattice_frameLattice [IsFractionRing A K] (g : GL ι K) : Submodule.IsFullLattice K (frameLattice A g) where
  toIsLattice := Submodule.IsLattice.of_fg K <| Submodule.fg_span (Set.finite_range _)
  span_eq_top := by
    rw [frameLattice, Submodule.span_span_of_tower, eq_top_iff]
    intro x _
    exact (mem_frameLattice_iff_inv (A := K) g x).2 fun i => Submodule.mem_one.2 ⟨_, rfl⟩

theorem exists_eq_frameLattice [IsDomain A] [IsPrincipalIdealRing A] [IsFractionRing A K]
    (M : Submodule A (ι → K)) [Submodule.IsFullLattice K M] : ∃ g : GL ι K, M = frameLattice A g := by
  letI := Submodule.IsLattice.finite K M
  letI := Submodule.IsLattice.free K M
  have hcard : Fintype.card (Module.Free.ChooseBasisIndex A M) = Fintype.card ι := by
    rw [← Module.finrank_eq_card_chooseBasisIndex, Submodule.IsFullLattice.finrank_eq K M,
      Module.finrank_fintype_fun_eq_card]
  let b : Module.Basis ι A M := (Module.Free.chooseBasis A M).reindex (Fintype.equivOfCardEq hcard)
  let c : Module.Basis ι K (ι → K) := b.extendOfIsFullLattice K
  let := (Pi.basisFun K ι).invertibleToMatrix c
  refine ⟨unitOfInvertible ((Pi.basisFun K ι).toMatrix c), ?_⟩
  have hc : ((Pi.basisFun K ι).toMatrix c).col = fun i => M.subtype (b i) := by
    ext i j
    simp [Module.Basis.toMatrix_apply, c]
  rw [frameLattice, val_unitOfInvertible, hc]
  change M = Submodule.span A (Set.range (M.subtype ∘ b))
  rw [Set.range_comp, ← Submodule.map_span, b.span_eq, Submodule.map_subtype_top]

end Frame

section Dual

variable (A : Type*) {K : Type*} [CommRing A] [Field K] [Algebra A K]
  {V W : Type*} [AddCommGroup V] [Module K V] [Module A V] [IsScalarTower A K V]
  [AddCommGroup W] [Module K W] {σ : K →+* K}

variable {A}

end Dual

section LocalDual

variable {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K]
  {V W : Type*} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  [AddCommGroup W] [Module K W] [Module O W] [IsScalarTower O K W]

end LocalDual

section Completion

variable {O K : Type*} [CommRing O] [IsDedekindDomain O] [Field K] [Algebra O K]
  [IsFractionRing O K] {ι : Type*} (v : HeightOneSpectrum O)

theorem algebraMap_mem_adicCompletionIntegers_iff (x : K) :
    algebraMap K (v.adicCompletion K) x ∈ v.adicCompletionIntegers K ↔
      x ∈ v.valuationSubringAtPrime K := by
  rw [mem_localRing_iff_valuation, mem_adicCompletionIntegers,
    ← valuedAdicCompletion_eq_valuation' v x]
  rfl

variable [Fintype ι] [DecidableEq ι]



variable {v}

end Completion

section NumberField

open NumberField

theorem isLattice_iff {K : Type} [Field K] [NumberField K] {r : ℕ}
    (L : Submodule (𝓞 K) (Fin r → K)) : ReciprocityTheory.MultiplicativeHeights.IsLattice L ↔ Submodule.IsFullLattice K L :=
  ⟨fun h => { toIsLattice := Submodule.IsLattice.of_fg K h.1, span_eq_top := h.2 },
    fun h => ⟨h.fg, h.span_eq_top⟩⟩

theorem mem_one_ringOfIntegers_iff {K : Type*} [Field K] [NumberField K] (x : K) :
    x ∈ (1 : Submodule (𝓞 K) K) ↔ IsIntegral ℤ x :=
  Submodule.mem_one.trans
    ⟨fun ⟨a, ha⟩ => ha ▸ a.isIntegral_coe, fun h => ⟨⟨x, h⟩, rfl⟩⟩

theorem mem_iff_forall_mem_localize_ringOfIntegers {K V : Type*} [Field K] [NumberField K]
    [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (L : Submodule (𝓞 K) V) (x : V) :
    x ∈ L ↔ ∀ v : HeightOneSpectrum (𝓞 K), x ∈ localize K v L :=
  ⟨fun hx v => mem_localize_of_mem v hx,
    mem_of_forall_mem_localize_of_not_isField (RingOfIntegers.not_isField K)⟩

open ReciprocityTheory.ChartRestriction.G.FD

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

def conjPlace (v : HeightOneSpectrum (𝓞 E)) : HeightOneSpectrum (𝓞 E) :=
  v.comap (IsCMField.ringOfIntegersComplexConj E : 𝓞 E →+* 𝓞 E)
    (IsCMField.ringOfIntegersComplexConj E).surjective

def hermPairing (G : Matrix (Fin r) (Fin r) E) :
    (Fin r → E) →ₗ[E] (Fin r → E) →ₛₗ[(IsCMField.complexConj E : E →+* E)] E :=
  LinearMap.mk₂'ₛₗ (RingHom.id E) (IsCMField.complexConj E : E →+* E) (herm G)
    (fun x y z => by simp [herm, add_mul, Finset.sum_add_distrib])
    (fun c x y => by simp [herm, Finset.mul_sum, mul_assoc])
    (fun x y z => by simp [herm, cc, mul_add, Finset.sum_add_distrib])
    (fun c x y => by simp [herm, cc, Finset.mul_sum, mul_left_comm])

@[simp] theorem hermPairing_apply (G : Matrix (Fin r) (Fin r) E) (x y : Fin r → E) :
    hermPairing G x y = herm G x y := rfl

theorem hermPairing_separating {G : Matrix (Fin r) (Fin r) E} (hG : G.det ≠ 0) (x : Fin r → E)
    (hx : ∀ y, hermPairing G x y = 0) : x = 0 := by
  refine Matrix.eq_zero_of_vecMul_eq_zero hG (funext fun b => ?_)
  have := hx (Pi.single b 1)
  simpa [herm, cc, Pi.single_apply, apply_ite, Matrix.vecMul, dotProduct] using this

end NumberField

end GlobalTheory.LocalLattice

namespace GlobalTheory

open LocalLattice

end GlobalTheory
