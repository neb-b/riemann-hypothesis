module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyStatement
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0008
public import ReciprocityTheory.CommutativeAlgebra.MaximalIdealSquares.RingKrullDimQuotientSpanSingletonAddOne
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0001

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolyDerivRenameOfConvex
section
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)

namespace GlobalTheory.ConvexCutOff

theorem exists_support {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    {K : Set V} (hK : Convex ℝ K) (hne : K.Nonempty) {x : V} (hx : x ∉ interior K) :
    ∃ f : V →L[ℝ] ℝ, f ≠ 0 ∧ ∀ y ∈ K, f y ≤ f x := by
  by_cases hi : (interior K).Nonempty
  · obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hK.interior isOpen_interior hx
    refine ⟨f, ?_, ?_⟩
    · rintro rfl
      obtain ⟨a, ha⟩ := hi
      simpa using hf a ha
    · intro y hy
      have h1 : y ∈ closure (interior K) := by
        rw [hK.closure_interior_eq_closure_of_nonempty_interior hi]
        exact subset_closure hy
      have h2 : IsClosed {z | f z ≤ f x} := isClosed_le f.continuous continuous_const
      exact closure_minimal (fun a ha => (hf a ha).le) h2 h1
  · rw [hK.interior_nonempty_iff_affineSpan_eq_top] at hi
    obtain ⟨k, hk⟩ := hne
    have hd : (affineSpan ℝ K).direction < ⊤ := by
      rw [lt_top_iff_ne_top]
      intro h
      exact hi ((AffineSubspace.direction_eq_top_iff_of_nonempty
        ⟨k, subset_affineSpan ℝ K hk⟩).1 h)
    obtain ⟨g, hg0, hg⟩ := Submodule.exists_le_ker_of_lt_top _ hd
    have hc : ∀ y ∈ K, g y = g k := by
      intro y hy
      have := hg (AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ K hy)
        (subset_affineSpan ℝ K hk))
      simpa [sub_eq_zero] using this
    have hg1 : LinearMap.toContinuousLinearMap g ≠ 0 := by
      intro h
      apply hg0
      ext z
      simpa using congrArg (fun φ : V →L[ℝ] ℝ => φ z) h
    rcases le_total (g k) (g x) with h | h
    · exact ⟨LinearMap.toContinuousLinearMap g, hg1, fun y hy => by simpa [hc y hy] using h⟩
    · exact ⟨-LinearMap.toContinuousLinearMap g, neg_ne_zero.2 hg1,
        fun y hy => by simpa [hc y hy] using h⟩

theorem uniqueDiffWithinAt_compl {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] {K : Set V} (hK : Convex ℝ K) {x : V} (hx : x ∉ interior K) :
    UniqueDiffWithinAt ℝ Kᶜ x := by
  rcases K.eq_empty_or_nonempty with rfl | hne
  · simpa using uniqueDiffWithinAt_univ
  obtain ⟨f, hf0, hf⟩ := exists_support hK hne hx
  obtain ⟨v, hv⟩ : ∃ v, 0 < f v := by
    obtain ⟨w, hw⟩ : ∃ w, f w ≠ 0 := by
      by_contra h
      push_neg at h
      exact hf0 (ContinuousLinearMap.ext h)
    rcases lt_or_gt_of_ne hw with h | h
    · exact ⟨-w, by simpa using h⟩
    · exact ⟨w, h⟩
  have hH : Convex ℝ {y | f x < f y} := convex_halfSpace_gt f.toLinearMap.isLinear (f x)
  have hO : IsOpen {y | f x < f y} := isOpen_lt continuous_const f.continuous
  have hcl : x ∈ closure {y | f x < f y} := by
    have ht : Filter.Tendsto (fun t : ℝ => x + t • v) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
      have : Continuous (fun t : ℝ => x + t • v) := by fun_prop
      have h2 := this.tendsto 0
      simp only [zero_smul, add_zero] at h2
      exact h2.mono_left nhdsWithin_le_nhds
    refine mem_closure_of_tendsto ht ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have ht' : (0 : ℝ) < t := ht
    simp only [Set.mem_setOf_eq, map_add (f := _), map_smul, smul_eq_mul]
    nlinarith [mul_pos ht' hv]
  have hU := uniqueDiffWithinAt_convex hH (by
    rw [hO.interior_eq]
    exact ⟨x + v, by simpa using hv⟩) hcl
  exact hU.mono fun y hy hyK => absurd (hf y hyK) (not_le.2 hy)

theorem fderiv_eq_zero {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [NormedSpace ℂ W] {K : Set V} (hK : Convex ℝ K) {G : V → W}
    (hG : ∀ z, z ∉ K → G z = 0) {x : V} (hx : x ∉ interior K) : fderiv ℂ G x = 0 := by
  by_cases hd : DifferentiableAt ℂ G x
  swap
  · exact fderiv_zero_of_not_differentiableAt hd
  have hU := uniqueDiffWithinAt_compl hK hx
  have hx0 : G x = 0 := by
    have := hd.continuousAt.continuousWithinAt.mem_closure_image hU.mem_closure
    have hs : G '' Kᶜ ⊆ {0} := by
      rintro _ ⟨z, hz, rfl⟩
      exact hG z hz
    exact closure_minimal hs isClosed_singleton this
  have h1 : HasFDerivWithinAt G ((fderiv ℂ G x).restrictScalars ℝ) Kᶜ x :=
    (hd.hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt
  have h2 : HasFDerivWithinAt G (0 : V →L[ℝ] W) Kᶜ x :=
    (hasFDerivWithinAt_const (0 : W) x Kᶜ).congr (fun z hz => hG z hz) hx0
  have h3 := hU.eq h1 h2
  ext z
  simpa using congrArg (fun φ : V →L[ℝ] W => φ z) h3

theorem iteratedFDeriv_eq_zero_off {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (n : ℕ) : ∀ z, z ∉ K → iteratedFDeriv ℂ n F z = 0 := by
  induction n with
  | zero =>
    intro z hz
    ext m
    simp [hF z hz]
  | succ n ih =>
    intro z hz
    rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
      fderiv_eq_zero hK ih (fun h => hz (interior_subset h))]
    exact map_zero _

theorem iteratedFDeriv_symm {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
    [FiniteDimensional ℂ V] {K : Set V} (hK : Convex ℝ K) {F : V → ℂ}
    (hF : ∀ z, z ∉ K → F z = 0) (hd : DifferentiableOn ℂ F (interior K)) (x : V) (n : ℕ)
    (v : Fin n → V) (σ : Equiv.Perm (Fin n)) :
    iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v := by
  by_cases hx : x ∈ interior K
  · exact (GlobalTheory.SCV.analyticOnNhd_of_differentiableOn isOpen_interior hd x
      hx).contDiffAt.iteratedFDeriv_comp_perm v σ
  · cases n with
    | zero => simp
    | succ n =>
      have : iteratedFDeriv ℂ (n + 1) F x = 0 := by
        rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply,
          fderiv_eq_zero hK (iteratedFDeriv_eq_zero_off hK hF n) hx]
        exact map_zero _
      simp [this]

theorem exists_perm_of_ofFn_perm {α : Type} {n : ℕ} (v w : Fin n → α)
    (h : (List.ofFn v).Perm (List.ofFn w)) : ∃ σ : Equiv.Perm (Fin n), v = w ∘ σ := by
  first
  | exact @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm
  | (apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FiberCardPermutation.exists_perm_of_ofFn_perm ..)

theorem term_eq {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] {F : V → ℂ} {x : V}
    (hs : ∀ (n : ℕ) (v : Fin n → V) (σ : Equiv.Perm (Fin n)),
      iteratedFDeriv ℂ n F x (v ∘ σ) = iteratedFDeriv ℂ n F x v)
    {n m : ℕ} (v : Fin n → V) (w : Fin m → V) (h : (List.ofFn v).Perm (List.ofFn w)) :
    iteratedFDeriv ℂ n F x v = iteratedFDeriv ℂ m F x w := by
  have hnm : n = m := by simpa using h.length_eq
  subst hnm
  obtain ⟨σ, rfl⟩ := exists_perm_of_ofFn_perm v w h
  exact hs n w σ

theorem ofFn_get_cast {α β : Type} (l : List α) {n : ℕ} (u : α → β) (h : n = l.length) :
    List.ofFn (fun k : Fin n => u (l.get (Fin.cast h k))) = l.map u := by
  subst h
  apply List.ext_getElem <;> simp

theorem polyDeriv_rename_of_convex : ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [FiniteDimensional ℂ V] (K : Set V) (F : V → ℂ), Convex ℝ K → (∀ z, z ∉ K → F z = 0) → DifferentiableOn ℂ F (interior K) → ∀ (x : V) (ι κ : Type) (ρ : ι → κ), Function.Injective ρ → ∀ (Q : MvPolynomial ι ℂ) (u : κ → V), polyDeriv (MvPolynomial.rename ρ Q) u F x = polyDeriv Q (u ∘ ρ) F x := by
  intro V _ _ _ K F hK hF hd x ι κ ρ hρ Q u
  classical
  unfold polyDeriv
  rw [MvPolynomial.support_rename_of_injective hρ,
    Finset.sum_image (fun a _ b _ h => Finsupp.mapDomain_injective hρ h)]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [MvPolynomial.coeff_rename_mapDomain ρ hρ]
  congr 1
  apply term_eq (iteratedFDeriv_symm hK hF hd x)
  rw [ofFn_get_cast, ofFn_get_cast, ← List.map_map]
  apply List.Perm.map
  rw [← Multiset.coe_eq_coe, ← Multiset.map_coe, Multiset.coe_toList, Multiset.coe_toList,
    Finsupp.toMultiset_map]

end GlobalTheory.ConvexCutOff
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RegularLocalRingNormalDomain
section
open IsLocalRing

namespace GlobalTheory

namespace RegularNormal

def StableDvd (A : Type*) [CommRing A] : Prop :=
  ∀ (a b : A) (I : Ideal A), b ≠ 0 → I ≠ ⊥ → (∀ r ∈ I, ∃ s ∈ I, a * r = b * s) → b ∣ a

theorem StableDvd.isIntegrallyClosed {A : Type*} [CommRing A] [IsDomain A] (h : StableDvd A) :
    IsIntegrallyClosed A := by
  rw [isIntegrallyClosed_iff (FractionRing A)]
  intro y hy
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := A) y
  set K := FractionRing A
  set y : K := algebraMap A K a / algebraMap A K b with hydef
  have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
  have hbK : algebraMap A K b ≠ 0 := by
    simpa using hb0
  have hinj : Function.Injective (algebraMap A K) := IsFractionRing.injective A K
  obtain ⟨d, hd, hdN⟩ := FractionalIdeal.isFractional_of_fg (S := nonZeroDivisors A)
    hy.fg_adjoin_singleton
  let I : Ideal A :=
    { carrier := {r | ∀ z ∈ Algebra.adjoin A {y}, ∃ s : A, algebraMap A K s = r • z}
      zero_mem' := fun z _ => ⟨0, by simp⟩
      add_mem' := by
        intro r r' hr hr' z hz
        obtain ⟨s, hs⟩ := hr z hz
        obtain ⟨s', hs'⟩ := hr' z hz
        exact ⟨s + s', by rw [map_add (f := _), hs, hs', add_smul]⟩
      smul_mem' := by
        intro c r hr z hz
        obtain ⟨s, hs⟩ := hr z hz
        exact ⟨c * s, by rw [map_mul, hs, smul_eq_mul, mul_smul, Algebra.smul_def c]⟩ }
  have hyN : y ∈ Algebra.adjoin A {y} := Algebra.self_mem_adjoin_singleton A y
  have hdI : d ∈ I := fun z hz => hdN z hz
  have hI : I ≠ ⊥ := fun h0 => nonZeroDivisors.ne_zero hd (by simpa [h0] using hdI)
  obtain ⟨c, hc⟩ := h a b I hb0 hI (by
    intro r hr
    obtain ⟨s, hs⟩ := hr y hyN
    refine ⟨s, fun z hz => ?_, hinj ?_⟩
    · obtain ⟨t, ht⟩ := hr (y * z) (mul_mem hyN hz)
      refine ⟨t, ?_⟩
      rw [ht, Algebra.smul_def s, hs, smul_mul_assoc]
    · rw [map_mul, map_mul, hs, Algebra.smul_def, hydef, mul_left_comm, mul_div_cancel₀ _ hbK, mul_comm])
  refine ⟨c, ?_⟩
  rw [hydef, hc, map_mul, mul_div_cancel_left₀ _ hbK]

section Step

variable {A : Type*} [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A] {x : A}

theorem dvd_of_not_dvd (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) {a b : A}
    (hb : ¬ x ∣ b) {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = b * s) : b ∣ a := by
  first
  | exact @_root_.GlobalTheory.SaturatedNotDvd.main
  | exact _root_.GlobalTheory.SaturatedNotDvd.main
  | (apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.SaturatedNotDvd.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SaturatedNotDvd.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SaturatedNotDvd.main ..)


omit [IsLocalRing A] in
theorem prime_dvd_of_stable (hx : Prime x) {a b : A} {I : Ideal A} (hI : I ≠ ⊥)
    (hst : ∀ r ∈ I, ∃ s ∈ I, a * r = x * b * s) : x ∣ a := by
  by_contra ha
  have key : ∀ k : ℕ, ∀ r ∈ I, x ^ k ∣ r := by
    intro k
    induction k with
    | zero => intro r _; simp
    | succ k ih =>
      intro r hr
      obtain ⟨s, hs, e⟩ := hst r hr
      obtain ⟨v, rfl⟩ := ih s hs
      exact hx.pow_dvd_of_dvd_mul_left (k + 1) ha ⟨b * v, by linear_combination e⟩
  obtain ⟨r, hr, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hI
  obtain ⟨n, c, hc, e⟩ := WfDvdMonoid.max_power_factor' hr0 hx.not_unit
  obtain ⟨v, hv⟩ := key (n + 1) r hr
  refine hc ⟨v, mul_left_cancel₀ (pow_ne_zero n hx.ne_zero) ?_⟩
  linear_combination hv - e

theorem StableDvd.of_quotient (hx : Prime x) (h : StableDvd (A ⧸ Ideal.span {x})) :
    StableDvd A := by
  intro a b I hb hI hst
  obtain ⟨n, c, hc, rfl⟩ := WfDvdMonoid.max_power_factor' hb hx.not_unit
  clear hb
  induction n generalizing a with
  | zero =>
    rw [pow_zero, one_mul] at hst ⊢
    exact dvd_of_not_dvd hx h hc hI hst
  | succ n ih =>
    obtain ⟨a, rfl⟩ := prime_dvd_of_stable hx (a := a) (b := x ^ n * c) hI (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, by linear_combination e⟩)
    obtain ⟨v, hv⟩ := ih a (fun r hr => by
      obtain ⟨s, hs, e⟩ := hst r hr
      exact ⟨s, hs, mul_left_cancel₀ hx.ne_zero (by linear_combination e)⟩)
    exact ⟨v, by rw [hv]; ring⟩

end Step

open ReciprocityTheory.CA.AB.RegA in
theorem stableDvd_of_spanFinrank_eq (n : ℕ) :
    ∀ (R : Type) [CommRing R] [IsRegularLocalRing R],
      Submodule.spanFinrank (maximalIdeal R) = n → StableDvd R := by
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro R _ _ hn
  have : IsDomain R := IsRegularLocalRing.isDomain R
  by_cases hsq : maximalIdeal R ≤ maximalIdeal R ^ 2
  · have h0 := IsRegularLocalRing.maximalIdeal_eq_bot_of_le_sq R hsq
    intro a b I hb _ _
    refine IsUnit.dvd ?_
    by_contra hu
    have : b ∈ maximalIdeal R := hu
    rw [h0] at this
    exact hb this
  obtain ⟨x, hx, hx2⟩ := SetLike.not_le_iff_exists.mp hsq
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact hx2 (zero_mem _)
  have hquot := IsRegularLocalRing.quotient_span_singleton hx hx2
  have hxp : Prime x := by
    rw [← Ideal.span_singleton_prime hx0, ← Ideal.Quotient.isDomain_iff_prime]
    exact IsRegularLocalRing.isDomain _
  refine StableDvd.of_quotient hxp (IH _ ?_ _ rfl)
  have h1 := IsRegularLocalRing.spanFinrank_maximalIdeal_quotient_succ_le R hx hx2
  have h2 : Submodule.spanFinrank (maximalIdeal R)
      = Module.finrank (ResidueField R) (CotangentSpace R) := by
    rw [IsLocalRing.spanFinrank_maximalIdeal_eq_finrank_cotangentSpace]
  omega

end RegularNormal

theorem isDomain_and_isIntegrallyClosed_of_isRegularLocalRing :
    ∀ (T : Type) [CommRing T] [IsRegularLocalRing T], IsDomain T ∧ IsIntegrallyClosed T := by
  intro T _ _
  have hd : IsDomain T := ReciprocityTheory.CA.AB.RegA.IsRegularLocalRing.isDomain T
  exact ⟨hd, (RegularNormal.stableDvd_of_spanFinrank_eq _ T rfl).isIntegrallyClosed⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReversedCharpolyCoeffInDomainMul
section
noncomputable section

open CategoryTheory Polynomial TensorProduct

namespace GlobalTheory.NormalDescent

theorem charpoly_reverse_coeff_smul {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (f : Module.End K V) (c : K) (k : ℕ) :
    (c • f).charpoly.reverse.coeff k = c ^ k * f.charpoly.reverse.coeff k := by
  classical
  let e := Module.finBasis K V
  rw [← LinearMap.charpoly_toMatrix _ e, ← LinearMap.charpoly_toMatrix _ e, Matrix.reverse_charpoly,
    Matrix.reverse_charpoly, map_smul, mul_comm, ← comp_C_mul_X_coeff]
  generalize LinearMap.toMatrix e e f = M
  congr 1
  rw [Matrix.charpolyRev, Matrix.charpolyRev, ← coe_compRingHom_apply, RingHom.map_det]
  apply congrArg (fun p : K[X] => p.coeff)
  apply congrArg Matrix.det
  refine Matrix.ext fun i j => ?_
  by_cases hij : i = j <;> simp [hij] <;> ring

theorem exists_charK_coeff {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B]
    (φ : A →+* B) (hφ : φ.Finite) (b : B) (n : ℕ) :
    ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b).coeff n := by
  classical
  letI := φ.toAlgebra
  haveI : Module.Finite A B := hφ
  let K := FractionRing A
  let Ω := AlgebraicClosure K
  let ι := algebraMap K Ω
  let V := K ⊗[A] B
  haveI : Module.Free K V := Module.Free.of_divisionRing _ _
  let e := Module.finBasis K V
  let Mx := Algebra.leftMulMatrix e ((1 : K) ⊗ₜ[A] b)
  have hg : charK φ hφ K b = Mx.charpoly := by
    show (Algebra.lmul K V ((1 : K) ⊗ₜ[A] b)).charpoly = _
    show _ = (Algebra.leftMulMatrix e _).charpoly
    rw [Algebra.leftMulMatrix_apply, LinearMap.charpoly_toMatrix]
  have hb : IsIntegral A b := Algebra.IsIntegral.isIntegral b
  have h1 : IsIntegral A ((1 : K) ⊗ₜ[A] b) :=
    hb.map (Algebra.TensorProduct.includeRight : B →ₐ[A] K ⊗[A] B)
  have h2 : IsIntegral A Mx := h1.map ((Algebra.leftMulMatrix e).restrictScalars A)
  have h3 : IsIntegral A (Mx.map ι) := h2.map (AlgHom.mapMatrix (IsScalarTower.toAlgHom A K Ω))
  obtain ⟨p, hpm, hp⟩ := h3
  have hroot : ∀ μ ∈ (Mx.charpoly.map ι).roots, IsIntegral A μ := by
    intro μ hμ
    have hs : μ ∈ spectrum Ω (Mx.map ι) := by
      rw [Matrix.mem_spectrum_iff_isRoot_charpoly, Matrix.charpoly_map]
      exact isRoot_of_mem_roots hμ
    have h4 := spectrum.subset_polynomial_aeval (Mx.map ι) (p.map (algebraMap A Ω)) ⟨μ, hs, rfl⟩
    have h5 : aeval (Mx.map ι) (p.map (algebraMap A Ω)) = 0 := by
      rw [aeval_map_algebraMap, aeval_def]; exact hp
    rw [h5] at h4
    refine ⟨p, hpm, ?_⟩
    rw [← aeval_def, ← aeval_map_algebraMap Ω]
    by_contra hne
    exact (spectrum.mem_iff.1 h4) (by
      simpa using (IsUnit.mk0 _ hne).map (algebraMap Ω (Matrix (Fin (Module.finrank K V)) (Fin (Module.finrank K V)) Ω)))
  have hl : Mx.charpoly.map ι ∈ Polynomial.lifts (integralClosure A Ω).val.toRingHom :=
    (IsAlgClosed.splits _).mem_lift_of_roots_mem_range ((Matrix.charpoly_monic _).map _) _
      fun μ hμ => ⟨⟨μ, hroot μ hμ⟩, rfl⟩
  rw [lifts_iff_coeff_lifts] at hl
  obtain ⟨s, hs⟩ := hl n
  have hc : IsIntegral A (Mx.charpoly.coeff n) := by
    refine (isIntegral_algHom_iff (IsScalarTower.toAlgHom A K Ω) ι.injective).1 ?_
    show IsIntegral A (ι _)
    rw [← coeff_map, ← hs]
    exact s.2
  rw [hg]
  exact IsIntegrallyClosed.isIntegral_iff.1 hc

theorem normCoeff_mul : ∀ {A B : Type} [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] (φ : A →+* B)
    (hφ : φ.Finite) (u : A) (b : B) (k : ℕ), normCoeff φ hφ (φ u * b) k = u ^ k * normCoeff φ hφ b k := by
  intro A B _ _ _ _ φ hφ u b k
  have hrev : ∀ b' : B, ∃ a : A, algebraMap A (FractionRing A) a = (charK φ hφ (FractionRing A) b').reverse.coeff k :=
    fun b' => by rw [coeff_reverse]; exact exists_charK_coeff φ hφ b' _
  have key : (charK φ hφ (FractionRing A) (φ u * b)).reverse.coeff k
      = (algebraMap A (FractionRing A) u) ^ k * (charK φ hφ (FractionRing A) b).reverse.coeff k := by
    letI := φ.toAlgebra
    haveI : Module.Finite A B := hφ
    haveI : Module.Free (FractionRing A) (FractionRing A ⊗[A] B) := Module.Free.of_divisionRing _ _
    have e1 : (1 : FractionRing A) ⊗ₜ[A] (φ u * b)
        = algebraMap A (FractionRing A) u • ((1 : FractionRing A) ⊗ₜ[A] b) := by
      rw [algebraMap_smul, ← tmul_smul, Algebra.smul_def]; rfl
    show (Algebra.lmul _ _ ((1 : FractionRing A) ⊗ₜ[A] (φ u * b))).charpoly.reverse.coeff k = _
    rw [e1, map_smul]
    exact charpoly_reverse_coeff_smul _ _ _
  apply IsFractionRing.injective A (FractionRing A)
  rw [map_mul, map_pow, algebraMap_normCoeff _ _ _ _ (hrev _), algebraMap_normCoeff _ _ _ _ (hrev _), key]

end GlobalTheory.NormalDescent
end
end

