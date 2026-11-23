module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsValuationSubringLiftOfSpecialFibre
section
open IsLocalRing

namespace GlobalTheory

universe u

section Algebra

theorem height_le_one_of_forall_mem {B : Type*} [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (m : Ideal B) [m.IsPrime] {f : B} (hf : f ≠ 0)
    (h : ∀ p : Ideal B, p.IsPrime → p ≠ ⊥ → p ≤ m → f ∈ p) : m.height ≤ 1 := by
  by_cases hm : m = ⊥
  · subst hm
    simp
  have hfin := (Ideal.span {f}).finite_minimalPrimes_of_isNoetherianRing
  have hsub : (m : Set B) ⊆ ⋃ P ∈ (Ideal.span {f}).minimalPrimes, ((id P : Ideal B) : Set B) := by
    intro x hx
    simp only [Set.mem_iUnion, id, SetLike.mem_coe]
    by_cases hx0 : x = 0
    · obtain ⟨P, hP, -⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr (h m inferInstance hm le_rfl))
      exact ⟨P, hP, hx0 ▸ P.zero_mem⟩
    obtain ⟨P, hP, hPm⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {x}) (J := m)
        ((Ideal.span_singleton_le_iff_mem _).mpr hx)
    have hPp : P.IsPrime := hP.1.1
    have hxP : x ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
    have hP1 := Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP
    have hfP : f ∈ P := h P hPp (fun e => hx0 (by simpa [e] using hxP)) hPm
    obtain ⟨Q, hQ, hQP⟩ := Ideal.exists_minimalPrimes_le (I := Ideal.span {f}) (J := P)
        ((Ideal.span_singleton_le_iff_mem _).mpr hfP)
    have hQp : Q.IsPrime := hQ.1.1
    have hfQ : f ∈ Q := (Ideal.span_singleton_le_iff_mem _).mp hQ.1.2
    have hQ0 : ⊥ < Q := bot_lt_iff_ne_bot.mpr fun e => hf (by simpa [e] using hfQ)
    refine ⟨Q, hQ, ?_⟩
    rcases hQP.eq_or_lt with e | hlt
    · exact e ▸ hxP
    · exfalso
      have h1 := Ideal.height_add_one_le_of_lt_of_isPrime hQ0
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hlt
      have h3 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h1 le_rfl).trans (h2.trans hP1)
      simp at h3
      exact absurd h3 (by decide)
  obtain ⟨P, hP, hmP⟩ := (Ideal.subset_union_prime_finite hfin (f := id) ⊥ ⊥
    (fun i hi _ _ => hi.1.1)).mp hsub
  have hPp : P.IsPrime := hP.1.1
  exact (Ideal.height_mono hmP).trans
    (Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ P hP)

theorem exists_notMem_forall_mem_minimalPrimes {B : Type*} [CommRing B] [IsNoetherianRing B]
    (I p : Ideal B) [p.IsPrime] (hp : ∀ P ∈ I.minimalPrimes, P ≤ p → P = p) :
    ∃ s ∉ p, ∀ P ∈ I.minimalPrimes, P ≠ p → s ∈ P := by
  classical
  have hfin : (I.minimalPrimes \ {p}).Finite :=
    I.finite_minimalPrimes_of_isNoetherianRing.subset Set.sdiff_subset
  have : ¬ hfin.toFinset.inf id ≤ p := by
    rw [Ideal.IsPrime.inf_le' inferInstance]
    rintro ⟨P, hP, hle⟩
    rw [Set.Finite.mem_toFinset] at hP
    exact hP.2 (hp P hP.1 hle)
  obtain ⟨s, hs, hsp⟩ := SetLike.not_le_iff_exists.mp this
  refine ⟨s, hsp, fun P hP hne => ?_⟩
  exact (Finset.inf_le (f := id) (hfin.mem_toFinset.mpr ⟨hP, hne⟩) : _ ≤ P) hs

theorem quasiFiniteAt_of_height_le_one {O B : Type*} [CommRing O] [IsNoetherianRing O]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : algebraMap O B π ≠ 0)
    (hπm : algebraMap O B π ∈ m) : Algebra.QuasiFiniteAt O m := by
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing O B
  obtain ⟨s, hsm, hs⟩ := exists_notMem_forall_mem_minimalPrimes
    (Ideal.span {algebraMap O B π}) m (fun P hP hle => by
      have hPp : P.IsPrime := hP.1.1
      have hfP : algebraMap O B π ∈ P := (Ideal.span_singleton_le_iff_mem _).mp hP.1.2
      have hP0 : ⊥ < P := bot_lt_iff_ne_bot.mpr fun e => hπ (by simpa [e] using hfP)
      by_contra hne
      have h2 := Ideal.height_add_one_le_of_lt_of_isPrime hP0
      have h3 := Ideal.height_add_one_le_of_lt_of_isPrime (lt_of_le_of_ne hle hne)
      have h4 : (⊥ : Ideal B).height + 1 + 1 ≤ 1 := (add_le_add h2 le_rfl).trans (h3.trans h1)
      simp at h4
      exact absurd h4 (by decide))
  refine Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := O) ⟨m, inferInstance⟩ ?_
  refine isOpen_induced_iff.mpr ⟨PrimeSpectrum.basicOpen s, (PrimeSpectrum.basicOpen s).isOpen, ?_⟩
  ext ⟨q, hq⟩
  simp only [Set.mem_preimage, SetLike.mem_coe, PrimeSpectrum.mem_basicOpen,
    Set.mem_singleton_iff]
  constructor
  · intro hsq
    have hπq : algebraMap O B π ∈ q.asIdeal := by
      have : π ∈ (PrimeSpectrum.comap (algebraMap O B) q).asIdeal := by
        rw [Set.mem_preimage, Set.mem_singleton_iff] at hq
        rw [hq]
        exact hπm
      exact this
    obtain ⟨P, hP, hPq⟩ := Ideal.exists_minimalPrimes_le (J := q.asIdeal)
      ((Ideal.span_singleton_le_iff_mem _).mpr hπq)
    have hPm : P = m := by
      by_contra hne
      exact hsq (hPq (hs P hP hne))
    subst hPm
    exact Subtype.ext <| PrimeSpectrum.ext (hm.eq_of_le q.isPrime.ne_top hPq).symm
  · intro e
    obtain rfl : q = ⟨m, inferInstance⟩ := congrArg Subtype.val e
    exact hsm

theorem exists_valuationSubring_of_height_le_one {O K : Type*} {B : Type u} [CommRing O]
    [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K]
    [CommRing B] [IsDomain B] [Algebra O B] [Algebra.FiniteType O B]
    (hinj : Function.Injective (algebraMap O B))
    (m : Ideal B) [hm : m.IsMaximal] (h1 : m.height ≤ 1) (π : O) (hπ : π ≠ 0)
    (hπm : algebraMap O B π ∈ m) :
    ∃ (K' : Type u) (_ : Field K') (_ : Algebra K K') (_ : Module.Finite K K')
      (O' : ValuationSubring K') (φ : B →+* O'),
      (∀ a : O, (φ (algebraMap O B a) : K') = algebraMap K K' (algebraMap O K a)) ∧
      Function.Injective φ ∧ (maximalIdeal O').comap φ = m := by
  have hq : Algebra.QuasiFiniteAt O m := quasiFiniteAt_of_height_le_one m h1 π
    (fun e => hπ (hinj (by simpa using e))) hπm
  let K' := FractionRing B
  let L := Localization.AtPrime m
  let g : L →ₐ[B] K' := IsLocalization.liftAlgHom (M := m.primeCompl) (f := Algebra.ofId B K')
    (fun y => by
      have : (y : B) ≠ 0 := fun e => y.2 (e ▸ m.zero_mem)
      exact IsUnit.mk0 _ (by simpa [K'] using this))
  have hqK : Algebra.QuasiFinite O K' := by
    refine .of_forall_exists_mul_mem_range (g.restrictScalars O) fun x => ?_
    obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := B) x
    have hb' : algebraMap B K' b ≠ 0 := by
      simpa [K'] using nonZeroDivisors.ne_zero hb
    refine ⟨algebraMap B L b, ?_, algebraMap B L a, ?_⟩
    · have : (g.restrictScalars O) (algebraMap B L b) = algebraMap B K' b := g.commutes b
      rw [this]
      exact IsUnit.mk0 _ hb'
    · simp [div_mul_cancel₀ _ hb']
  have hOK' : Function.Injective (algebraMap O K') := by
    rw [IsScalarTower.algebraMap_eq O B K']
    exact (IsFractionRing.injective B K').comp hinj
  let _ : Algebra K K' := (IsFractionRing.lift (K := K) hOK').toAlgebra
  have hst : IsScalarTower O K K' := .of_algebraMap_eq fun a => by
    simp [RingHom.algebraMap_toAlgebra]
  have : Algebra.QuasiFinite K K' := .of_restrictScalars O K K'
  obtain ⟨O', hO', hloc⟩ := IsLocalRing.exists_factor_valuationRing (g : L →+* K')
  let ψ : L →+* O' := (g : L →+* K').codRestrict O'.toSubring hO'
  have hψ : IsLocalHom ψ := hloc
  have hval : ∀ b : B, ((ψ.comp (algebraMap B L)) b : K') = algebraMap B K' b := fun b =>
    g.commutes b
  refine ⟨K', inferInstance, inferInstance, .of_quasiFinite, O', ψ.comp (algebraMap B L),
    fun a => ?_, fun a b hab => ?_, ?_⟩
  · rw [hval, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply]
  · apply IsFractionRing.injective B K'
    rw [← hval, ← hval, hab]
  · rw [← Ideal.comap_comap, maximalIdeal_comap ψ]
    exact IsLocalization.AtPrime.under_maximalIdeal L m

theorem exists_mem_height_map_le_one {A : Type*} [CommRing A] [IsNoetherianRing A]
    (m : Ideal A) [m.IsPrime] {U : Set (PrimeSpectrum A)} (hU : IsOpen U)
    (h : ∃ p ∈ U, p.asIdeal ≤ m) :
    ∃ q ∈ U, q.asIdeal ≤ m ∧ (m.map (Ideal.Quotient.mk q.asIdeal)).height ≤ 1 := by
  obtain ⟨p₀, hp₀, hp₀m⟩ := h
  obtain ⟨I, ⟨q, ⟨hqU, hqm⟩, rfl⟩, hmax⟩ := set_has_maximal_iff_noetherian.mpr
    (inferInstance : IsNoetherian A A)
    (PrimeSpectrum.asIdeal '' {p | p ∈ U ∧ p.asIdeal ≤ m}) ⟨_, p₀, ⟨hp₀, hp₀m⟩, rfl⟩
  refine ⟨q, hqU, hqm, ?_⟩
  obtain ⟨_, ⟨f, rfl⟩, hfq, hfU⟩ :=
    PrimeSpectrum.isTopologicalBasis_basic_opens.exists_subset_of_mem_open hqU hU
  have hsurj := Ideal.Quotient.mk_surjective (I := q.asIdeal)
  have : (m.map (Ideal.Quotient.mk q.asIdeal)).IsPrime :=
    Ideal.map_isPrime_of_surjective hsurj (by simpa using hqm)
  refine height_le_one_of_forall_mem _ (f := Ideal.Quotient.mk q.asIdeal f)
    (fun e => hfq (Ideal.Quotient.eq_zero_iff_mem.mp e)) fun p hp hp0 hpm => ?_
  by_contra hfp
  let p' : PrimeSpectrum A := ⟨p.comap (Ideal.Quotient.mk q.asIdeal), inferInstance⟩
  have hle : q.asIdeal ≤ p'.asIdeal := fun x hx => by
    change Ideal.Quotient.mk q.asIdeal x ∈ p
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr hx]
    exact p.zero_mem
  have hp'm : p'.asIdeal ≤ m := by
    refine (Ideal.comap_mono hpm).trans ?_
    rw [Ideal.comap_map_of_surjective _ hsurj, ← RingHom.ker_eq_comap_bot, Ideal.mk_ker]
    exact sup_le le_rfl hqm
  refine hmax p'.asIdeal ⟨p', ⟨hfU hfp, hp'm⟩, rfl⟩ (lt_of_le_of_ne hle fun e => hp0 ?_)
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨x, rfl⟩ := hsurj x
  have : x ∈ q.asIdeal := e ▸ hx
  simpa using Ideal.Quotient.eq_zero_iff_mem.mpr this

end Algebra

section Scheme

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

variable {O K : Type u} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K]
  [Algebra O K] [IsFractionRing O K]


end Scheme

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedRingOfIntegers
section
set_option autoImplicit false

noncomputable section

open TensorProduct

namespace GlobalTheory.Serre

section Eigen

variable {R O O' : Type*} [CommRing R] [CommRing O] [CommRing O'] [Algebra O O'] [Algebra O R]
  [Algebra O' R] [IsScalarTower O O' R]


variable (R O O') in
def mulChar : R ⊗[O] O' →ₐ[R] R :=
  Algebra.TensorProduct.lift (AlgHom.id R R) (IsScalarTower.toAlgHom O O' R) fun _ _ ↦ .all _ _

@[simp] theorem mulChar_tmul (r : R) (x : O') :
    mulChar (R := R) (O := O) (O' := O') (r ⊗ₜ x) = r * algebraMap O' R x := rfl

theorem exists_elem_of_unramified {A : Type*} [CommRing A] [Algebra R A]
    [Algebra.FormallyUnramified R A] [Algebra.EssFiniteType R A] (χ : A →ₐ[R] R) :
    ∃ e : A, χ e = 1 ∧ ∀ x, x * e = χ x • e := by
  let f : A ⊗[R] A →ₐ[R] A :=
    Algebra.TensorProduct.lift ((Algebra.ofId R A).comp χ) (AlgHom.id R A) fun _ _ ↦ .all _ _
  refine ⟨f (Algebra.FormallyUnramified.elem R A), ?_, fun x ↦ ?_⟩
  · have : ∀ z, χ (f z) = χ (Algebra.TensorProduct.lmul' R z) := fun z ↦ by
      induction z with
      | tmul x y => simp [f]
      | add z w hz hw => simp only [map_add (f := _), hz, hw]
    rw [this, Algebra.FormallyUnramified.lmul_elem, map_one]
  · simpa [f, Algebra.smul_def] using
      congrArg f (Algebra.FormallyUnramified.one_tmul_mul_elem (R := R) x)

variable {M : Type*} [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem exists_eigen_of_unramified (N : Type*) [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')] :
    ∃ s : N ⊗[O'] M →ₗ[R] N ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor N z = algebraMap O' R x • z := by
  obtain ⟨e, he₁, he₂⟩ := exists_elem_of_unramified (mulChar (R := R) (O := O) (O' := O'))
  let g : O' →ₐ[O] Module.End R (N ⊗[O] M) :=
    { toFun x := AlgebraTensorModule.lTensor R N (Algebra.lsmul O O M x)
      map_one' := by ext; simp
      map_mul' x y := by ext; simp
      map_zero' := by ext; simp
      map_add' x y := by ext; simp
      commutes' x := by ext; simp }
  let ρ : R ⊗[O] O' →ₐ[R] Module.End R (N ⊗[O] M) :=
    Algebra.TensorProduct.lift (Algebra.ofId R _) g fun r x ↦ Algebra.commute_algebraMap_left _ _
  have hρ : ∀ (r : R) (x : O') z, ρ (r ⊗ₜ x) z = r • (Algebra.lsmul O O M x).lTensor N z :=
    fun r x z ↦ rfl
  have hρe : ∀ (x : O') z, (Algebra.lsmul O O M x).lTensor N (ρ e z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) (he₂ (1 ⊗ₜ x))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  have hρe' : ∀ (x : O') z, ρ e ((Algebra.lsmul O O M x).lTensor N z) = algebraMap O' R x • ρ e z :=
    fun x z ↦ by
      have := congrArg (fun y ↦ ρ y z) ((mul_comm _ _).trans (he₂ (1 ⊗ₜ x)))
      simpa only [map_mul, map_smul, Module.End.mul_apply, hρ, one_smul, mulChar_tmul, one_mul,
        LinearMap.smul_apply] using this
  let s : N ⊗[O'] M →ₗ[R] N ⊗[O] M := AlgebraTensorModule.lift
    { toFun n :=
        { toFun m := ρ e (n ⊗ₜ m)
          map_add' m m' := by rw [tmul_add, map_add (f := _)]
          map_smul' x m := (hρe' x (n ⊗ₜ m)).trans (algebraMap_smul R x _) }
      map_add' n n' := LinearMap.ext fun m ↦ (congrArg (ρ e) (add_tmul n n' m)).trans (map_add _ _ _)
      map_smul' r n := LinearMap.ext fun m ↦ map_smul (ρ e) r (n ⊗ₜ m) }
  let q : N ⊗[O] M →ₗ[R] N ⊗[O'] M := mapOfCompatibleSMul O' O R N M
  have hq : ∀ y z, q (ρ y z) = mulChar (R := R) (O := O) (O' := O') y • q z := fun y z ↦ by
    induction y with
    | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy', add_smul]
    | tmul r x =>
      induction z with
      | add z z' hz hz' => simp only [map_add (f := _), hz, hz', smul_add]
      | tmul n m => simp [hρ, q, mul_smul]
  have hqs : ∀ z, q (s z) = z := fun z ↦ by
    induction z with
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul n m => exact (hq e (n ⊗ₜ m)).trans (by rw [he₁, one_smul]; rfl)
  have hsq : ∀ z, s (q z) = ρ e z := fun z ↦ by
    induction z with
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul n m => rfl
  refine ⟨s, Function.LeftInverse.injective hqs, fun z ↦ ⟨?_, fun hz ↦ ⟨q z, ?_⟩⟩⟩
  · rintro ⟨z, rfl⟩ x
    rw [← hqs z, hsq, hρe]
  · have : ∀ y, ρ y z = mulChar (R := R) (O := O) (O' := O') y • z := fun y ↦ by
      induction y with
      | add y y' hy hy' => simp only [map_add (f := _), LinearMap.add_apply, hy, hy', add_smul]
      | tmul r x => rw [hρ, hz, mulChar_tmul, mul_smul]
    rw [hsq, this, he₁, one_smul]


omit [Algebra O R] in
theorem exists_eigen_of_projective (M : Type*) [AddCommGroup M] [Module O M] [Module.Finite O M]
    [Module.Projective O M] {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [SMulCommClass O R N] [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (τ : O → R) (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hlin : ∀ (x : O) n, i (x • n) = x • i n)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = τ x • l) :
    ∃ j : N ⊗[O] M →ₗ[R] L ⊗[O] M, (∀ n m, j (n ⊗ₜ m) = i n ⊗ₜ m) ∧ Function.Injective j ∧
      ∀ z, z ∈ LinearMap.range j ↔ ∀ x : O, x • z = τ x • z := by
  let i' : N →ₗ[O] L := { i.toAddHom with map_smul' := hlin }
  let j : N ⊗[O] M →ₗ[R] L ⊗[O] M :=
    { (i'.rTensor M).toAddHom with
      map_smul' := fun r z ↦ by
        change i'.rTensor M (r • z) = r • i'.rTensor M z
        induction z with
        | add z z' hz hz' => simp only [smul_add, map_add (f := _), hz, hz']
        | tmul n m => simp [smul_tmul', i'] }
  refine ⟨j, fun _ _ ↦ rfl, Module.Flat.rTensor_preserves_injective_linearMap i' hi,
    fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨z, rfl⟩ x
    induction z with
    | add z z' hz hz' => simp only [smul_add, map_add (f := _), hz, hz']
    | tmul n m =>
      change (x • i n) ⊗ₜ[O] m = (τ x • i n) ⊗ₜ[O] m
      rw [(hr _).mp ⟨n, rfl⟩]
  · obtain ⟨n, t, s, -, -, hst⟩ := Module.Finite.exists_comp_eq_id_of_projective O M
    let c (k : Fin n) : L ⊗[O] M →ₗ[O] L :=
      (TensorProduct.rid O L).toLinearMap ∘ₗ (LinearMap.proj k ∘ₗ s).lTensor L
    have hc : ∀ k (r : R) z, c k (r • z) = r • c k z := fun k r z ↦ by
      induction z with
      | add z z' hz hz' => simp only [smul_add, map_add (f := _), hz, hz']
      | tmul l m => simpa [smul_tmul', c] using smul_comm _ r l
    have hsum : ∀ z, ∑ k, c k z ⊗ₜ[O] t (Pi.single k 1) = z := fun z ↦ by
      induction z with
      | add z z' hz hz' => simp only [map_add (f := _), add_tmul, Finset.sum_add_distrib, hz, hz']
      | tmul l m =>
        have hm : t (s m) = m := congr($hst m)
        conv_rhs => rw [← hm, pi_eq_sum_univ' (s m)]
        simp [c, smul_tmul, tmul_sum]
    choose u hu using fun k ↦ (hr (c k z)).mpr fun x ↦ by rw [← map_smul, hz, hc]
    refine ⟨∑ k, u k ⊗ₜ t (Pi.single k 1), ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← hsum z]
    exact Finset.sum_congr rfl fun k _ ↦ by rw [← hu]; rfl

theorem exists_eigen_tensor [Module.Finite O M] [Module.Projective O M]
    {N L : Type*} [AddCommGroup N] [Module R N] [Module O N]
    [Module O' N] [IsScalarTower O R N] [IsScalarTower O' R N] [IsScalarTower O O' N]
    [Algebra.FormallyUnramified R (R ⊗[O] O')] [Algebra.EssFiniteType R (R ⊗[O] O')]
    [AddCommGroup L] [Module R L] [Module O L] [SMulCommClass O R L]
    (i : N →ₗ[R] L) (hi : Function.Injective i)
    (hr : ∀ l, l ∈ LinearMap.range i ↔ ∀ x : O, x • l = algebraMap O R x • l) :
    ∃ s : N ⊗[O'] M →ₗ[R] L ⊗[O] M, Function.Injective s ∧ ∀ z, z ∈ LinearMap.range s ↔
      ∀ x : O', (Algebra.lsmul O O M x).lTensor L z = algebraMap O' R x • z := by
  obtain ⟨s, hs₁, hs₂⟩ := exists_eigen_of_unramified (R := R) (O := O) (O' := O') (M := M) N
  obtain ⟨j, hj₀, hj₁, hj₂⟩ := exists_eigen_of_projective M (algebraMap O R) i hi
    (fun x n ↦ by rw [(hr _).mp ⟨n, rfl⟩, ← map_smul, algebraMap_smul]) hr
  have hj : ∀ (x : O') z, j ((Algebra.lsmul O O M x).lTensor N z) =
      (Algebra.lsmul O O M x).lTensor L (j z) := fun x z ↦ by
    induction z with
    | add z z' hz hz' => simp only [map_add (f := _), hz, hz']
    | tmul n m => simp [hj₀]
  refine ⟨j ∘ₗ s, hj₁.comp hs₁, fun z ↦ ⟨?_, fun hz ↦ ?_⟩⟩
  · rintro ⟨w, rfl⟩ x
    rw [LinearMap.comp_apply, ← hj, (hs₂ _).mp ⟨w, rfl⟩, map_smul]
  · obtain ⟨w, rfl⟩ := (hj₂ z).mpr fun x ↦ by
      rw [IsScalarTower.algebraMap_apply O O' R, ← hz, AlgHom.commutes]
      simp [Module.algebraMap_end_eq_smul_id]
    obtain ⟨v, rfl⟩ := (hs₂ w).mpr fun x ↦ hj₁ (by rw [hj, hz, map_smul])
    exact ⟨v, rfl⟩

end Eigen

section Integers

open NumberField

variable (k K E : Type*) [Field k] [CharZero k] [Field K] [Field E] [NumberField K] [NumberField E]
  [Algebra K E]


omit [NumberField K] in
theorem ringOfIntegers_injective (τ : 𝓞 K →+* k) : Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot]
  refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
  rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
  exact RingHom.injective_int _

theorem formallyUnramified_ringOfIntegers [Algebra (𝓞 K) k] :
    Algebra.FormallyUnramified k (k ⊗[𝓞 K] 𝓞 E) := by
  have hinj := ringOfIntegers_injective k K (algebraMap (𝓞 K) k)
  let : Algebra K k := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower (𝓞 K) K k :=
    .of_algebraMap_eq fun x ↦ (IsFractionRing.lift_algebraMap hinj x).symm
  have : IsLocalization (Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors (𝓞 K))) E :=
    IsIntegralClosure.isLocalization (𝓞 K) K E (𝓞 E)
  have : Algebra.IsPushout (𝓞 K) K (𝓞 E) E :=
    (Algebra.isPushout_of_isLocalization (nonZeroDivisors (𝓞 K)) K (𝓞 E) E).symm
  have : Algebra.FormallyUnramified K E := Algebra.FormallyUnramified.of_isSeparable K E
  have : Algebra.FormallyUnramified K (K ⊗[𝓞 K] 𝓞 E) :=
    .of_equiv (Algebra.IsPushout.equiv (𝓞 K) K (𝓞 E) E).symm
  exact .of_equiv (Algebra.TensorProduct.cancelBaseChange (𝓞 K) K k k (𝓞 E))



end Integers

theorem iSupIndep_eigen {k V I : Type*} [Field k] [AddCommGroup V] [Module k V]
    (f : I → Module.End k V) (hf : ∀ i j, Commute (f i) (f j)) :
    iSupIndep fun χ : I → k ↦ ⨅ i, (f i).eigenspace (χ i) :=
  (Module.End.independent_iInf_maxGenEigenspace_of_forall_mapsTo f fun i j φ ↦
    Module.End.mapsTo_maxGenEigenspace_of_comm (hf j i) φ).mono fun _ ↦
      iInf_mono fun i ↦ ((f i).genEigenspace _).monotone le_top

end GlobalTheory.Serre
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.PowLeComapMapPow
section
universe u_1 u_2

namespace GlobalTheory.PowerExtensionEvaluation

theorem pow_le_comap_map_pow {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) (n : ℕ) : I ^ n ≤ ((I.map f) ^ n).comap f :=
  Ideal.map_le_iff_le_comap.mp (le_of_eq (Ideal.map_pow f I n))

theorem factorPow_evalₐ {A : Type u_1} [CommRing A] (I : Ideal A) {m n : ℕ} (hle : m ≤ n)
    (x : AdicCompletion I A) :
    Ideal.Quotient.factorPow I hle (AdicCompletion.evalₐ I n x) = AdicCompletion.evalₐ I m x := by
  obtain ⟨s, rfl⟩ := AdicCompletion.mk_surjective I A x
  rw [AdicCompletion.evalₐ_mk, AdicCompletion.evalₐ_mk]
  change Ideal.Quotient.mk (I ^ m) (s.val n) = Ideal.Quotient.mk (I ^ m) (s.val m)
  rw [Ideal.Quotient.eq]
  have h := s.property hle
  rw [SModEq.sub_mem] at h
  have h2 : s.val m - s.val n ∈ I ^ m := by simpa [smul_eq_mul, Ideal.mul_top] using h
  have h3 := (I ^ m).neg_mem h2
  rwa [neg_sub] at h3

theorem exists_extension {A : Type u_1} {B : Type u_2} [CommRing A] [CommRing B]
    (I : Ideal A) (f : A →+* B) [IsAdicComplete (Ideal.map f I) B] :
    ∃ g : AdicCompletion I A →+* B, g.comp (algebraMap A (AdicCompletion I A)) = f := by
  let F : (n : ℕ) → AdicCompletion I A →+* B ⧸ (Ideal.map f I) ^ n := fun n =>
    (Ideal.quotientMap ((Ideal.map f I) ^ n) f (pow_le_comap_map_pow I f n)).comp
      (AdicCompletion.evalₐ I n : AdicCompletion I A →+* A ⧸ I ^ n)
  have hF : ∀ {m n : ℕ} (hle : m ≤ n),
      (Ideal.Quotient.factorPow (Ideal.map f I) hle).comp (F n) = F m := by
    intro m n hle
    ext x
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
    have hm : AdicCompletion.evalₐ I m x = Ideal.Quotient.mk (I ^ m) a := by
      rw [← factorPow_evalₐ I hle x, ← ha]
      rfl
    change Ideal.Quotient.factorPow (Ideal.map f I) hle
        (Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n x)) =
      Ideal.quotientMap _ f (pow_le_comap_map_pow I f m) (AdicCompletion.evalₐ I m x)
    rw [← ha, hm, Ideal.quotientMap_mk, Ideal.quotientMap_mk]
    rfl
  refine ⟨IsAdicComplete.liftRingHom (Ideal.map f I) F hF, ?_⟩
  apply DFunLike.coe_injective
  apply IsHausdorff.funext' (Ideal.map f I)
  intro n a
  rw [RingHom.coe_comp, Function.comp_apply, IsAdicComplete.mk_liftRingHom]
  change Ideal.quotientMap _ f (pow_le_comap_map_pow I f n) (AdicCompletion.evalₐ I n (AdicCompletion.of I A a)) = _
  rw [AdicCompletion.evalₐ_of, Ideal.quotientMap_mk]

end GlobalTheory.PowerExtensionEvaluation
end

