module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsNsmulMemClosure
section
theorem UpperTheory.Reformulated.B.ExistsNsmulMemClosure.exists_nsmul_mem_closure.{u_1} :
    ∀ {V : Type u_1} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℚ V] (s : Set V),
    ∀ w ∈ Submodule.span ℚ s, ∃ (k : ℕ), (0 : ℕ) < k ∧ k • w ∈ AddSubgroup.closure s := by
  intro V _ _ s w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using AddSubgroup.subset_closure hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hx⟩ := hx
    obtain ⟨b, hb, hy⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have h : (a * b) • (x + y) = b • (a • x) + a • (b • y) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm b a]
    rw [h]
    exact add_mem (nsmul_mem hx b) (nsmul_mem hy a)
  | smul q x _ hx =>
    obtain ⟨a, ha, hx⟩ := hx
    refine ⟨q.den * a, Nat.mul_pos q.den_pos ha, ?_⟩
    have h : (q.den * a) • (q • x) = q.num • (a • x) := by
      rw [← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ a x,
        ← Int.cast_smul_eq_zsmul ℚ, smul_smul, smul_smul]
      congr 1
      rw [← Rat.mul_den_eq_num q]
      push_cast
      ring
    rw [h]
    exact zsmul_mem hx _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOfLi
section
theorem UpperTheory.Reformulated.B.Qe54.exists_of_li :
    ∀ {Q ι : Type} [inst : AddCommGroup Q]
    [inst_1 : _root_.Module ℂ Q] [Finite ι] (f : ι → Q →ₗ[ℂ] ℂ),
    LinearIndependent ℂ f → ∀ (v : ι → ℂ), ∃ (q : Q), ∀ (i : ι), (f i : Q → ℂ) q = v i := by
  intro Q ι _ _ _ f hf v
  classical
  have := Fintype.ofFinite ι
  have hs : Function.Surjective (LinearMap.pi f : Q →ₗ[ℂ] (ι → ℂ)) := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro φ hφ
    have hsum : ∑ i, φ (fun j => if i = j then 1 else 0) • f i = 0 := by
      ext q
      have h1 : φ (LinearMap.pi f q) = 0 := LinearMap.congr_fun hφ q
      rw [LinearMap.pi_apply_eq_sum_univ] at h1
      simpa [LinearMap.sum_apply, mul_comm] using h1
    have h0 := Fintype.linearIndependent_iff.1 hf _ hsum
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ]
    simp [h0]
  obtain ⟨q, hq⟩ := hs v
  exact ⟨q, fun i => congrFun hq i⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsOrthonormalBasisSesquilinear
section
theorem UpperTheory.Reformulated.B.Qh52.exists_orthonormal_basis_sesquilinear :
    ∀ {V : Type} [inst : AddCommGroup V] [inst_1 : _root_.Module ℂ V]
    [FiniteDimensional ℂ V] (B : V →ₗ[ℂ] V →ₗ⋆[ℂ] ℂ),
    (∀ (a b : V), ((B : V → V →ₗ⋆[ℂ] ℂ) b : V → ℂ) a = Star.star (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) b)) →
      (∀ (a : V), a ≠ (0 : V) → (0 : ℝ) < (((B : V → V →ₗ⋆[ℂ] ℂ) a : V → ℂ) a).re) →
        ∃ (e : Fin (Module.finrank ℂ V) → V),
          (∀ (i : Fin (Module.finrank ℂ V)), ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) (e i) = (1 : ℂ)) ∧
            (∀ (x y : V),
                ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y =
                  ∑ i : Fin (Module.finrank ℂ V),
                    ((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) (e i) * ((B : V → V →ₗ⋆[ℂ] ℂ) (e i) : V → ℂ) y) ∧
              ∀ (x y : V),
                ‖((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) y‖ ^ (2 : ℕ) ≤
                  (((B : V → V →ₗ⋆[ℂ] ℂ) x : V → ℂ) x).re * (((B : V → V →ₗ⋆[ℂ] ℂ) y : V → ℂ) y).re := by
  intro V _ _ _ B hs hp
  let c : InnerProductSpace.Core ℂ V :=
    { inner := fun x y => B y x
      conj_inner_symm := fun x y => (hs x y).symm
      re_inner_nonneg := fun x => by
        by_cases h : x = 0
        · simp [h]
        · exact (hp x h).le
      add_left := fun x y z => map_add (B z) x y
      smul_left := fun x y r => by simp
      definite := fun x h => by
        by_contra hx
        have h1 := hp x hx
        have h2 : B x x = 0 := h
        rw [h2] at h1
        simp at h1 }
  letI : NormedAddCommGroup V := c.toNormedAddCommGroup
  letI : InnerProductSpace ℂ V := InnerProductSpace.ofCore c.toCore
  have hB : ∀ x y : V, B x y = inner ℂ y x := fun _ _ => rfl
  let b := stdOrthonormalBasis ℂ V
  refine ⟨b, fun i => ?_, fun x y => ?_, fun x y => ?_⟩
  · rw [hB]
    exact b.inner_eq_one i
  · simp only [hB]
    rw [← b.sum_inner_mul_inner y x]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [hB]
    have h := inner_mul_inner_self_le (𝕜 := ℂ) y x
    rw [norm_inner_symm x y] at h
    rw [sq, mul_comm (inner ℂ x x).re]
    exact h
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPermOfMapEq
section
theorem UpperTheory.Reformulated.B.Qh57.exists_perm_of_map_eq :
    ∀ {n : ℕ} (a b : Fin n → ℂ),
    Multiset.map a Finset.univ.val = Multiset.map b Finset.univ.val →
      ∃ (e : Equiv.Perm (Fin n)), ∀ (i : Fin n), b ((e : Fin n → Fin n) i) = a i := by
  intro n a b h
  classical
  have key : ∀ (f : Fin n → ℂ) (c : ℂ),
      Fintype.card {i // f i = c} = Multiset.count c (Multiset.map f Finset.univ.val) := by
    intro f c
    rw [Fintype.card_subtype, Multiset.count_map, Finset.card_def, Finset.filter_val]
    congr 1
    exact Multiset.filter_congr (fun _ _ => eq_comm)
  have hc : ∀ c : ℂ, Fintype.card {i // a i = c} = Fintype.card {i // b i = c} := by
    intro c
    rw [key a c, key b c, h]
  exact ⟨Equiv.ofFiberEquiv (fun c => Fintype.equivOfCardEq (hc c)),
    fun i => Equiv.ofFiberEquiv_map _ i⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPlace
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.ExistsPlace.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.ExistsPlace.exists_place :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (q : ℕ),
      Nat.Prime q → ∃ (w : UpperTheory.Reformulated.B.ExistsPlace.Plc E), (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ q hq
  have hne : (q : NumberField.RingOfIntegers E) ≠ 0 := by
    exact_mod_cast hq.ne_zero
  have hnu : ¬ IsUnit (q : NumberField.RingOfIntegers E) := by
    intro h
    have h1 := h.map (Algebra.norm ℤ (S := NumberField.RingOfIntegers E))
    have h2 : Algebra.norm ℤ (q : NumberField.RingOfIntegers E) =
        (q : ℤ) ^ Module.finrank ℤ (NumberField.RingOfIntegers E) := by
      have := Algebra.norm_algebraMap (R := ℤ) (S := NumberField.RingOfIntegers E) (q : ℤ)
      simpa using this
    rw [h2] at h1
    have hpos : Module.finrank ℤ (NumberField.RingOfIntegers E) ≠ 0 := Module.finrank_pos.ne'
    have h3 : IsUnit (q : ℤ) := (isUnit_pow_iff hpos).1 h1
    exact hq.not_isUnit (Int.ofNat_isUnit.1 h3)
  obtain ⟨M, hM, hqM⟩ := exists_max_ideal_of_mem_nonunits hnu
  refine ⟨⟨M, hM.isPrime, ?_⟩, hqM⟩
  intro h
  rw [h] at hqM
  exact hne (by simpa using hqM)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPowSmulMemAlt
section
private theorem UpperTheory.pow_mul_isIntegral {l : ℕ} [Fact l.Prime] {K : Type} [Field K]
    [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K]
    [FiniteDimensional ℚ_[l] K] (c : K) :
    ∃ n : ℕ, IsIntegral ℤ_[l] ((l : K) ^ n * c) := by
  have h1 : IsAlgebraic ℚ_[l] c := Algebra.IsAlgebraic.isAlgebraic c
  have h2 : IsAlgebraic ℤ_[l] c :=
    (IsFractionRing.isAlgebraic_iff ℤ_[l] ℚ_[l] K).mpr h1
  obtain ⟨y, hy, hint⟩ := h2.exists_integral_multiple
  refine ⟨y.valuation, ?_⟩
  have hspec := PadicInt.unitCoeff_spec hy
  set u := PadicInt.unitCoeff hy
  have h3 : ((l : ℤ_[l]) ^ y.valuation) = (↑u⁻¹ : ℤ_[l]) * y := by
    rw [Units.eq_inv_mul_iff_mul_eq]
    exact hspec.symm
  have h4 : (l : K) ^ y.valuation * c = (↑u⁻¹ : ℤ_[l]) • (y • c) := by
    rw [← mul_smul, ← h3, Algebra.smul_def, map_pow, map_natCast]
  rw [h4]
  exact hint.smul _

theorem UpperTheory.exists_pow_smul_mem_alt :
    ∀ {l : ℕ} [Fact l.Prime] {K : Type} [Field K] [Algebra ℚ_[l] K] [Algebra ℤ_[l] K] [IsScalarTower ℤ_[l] ℚ_[l] K] [FiniteDimensional ℚ_[l] K] {O : Type} [CommRing O] [Algebra O K] {V : Type} [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] (T : Submodule O V), (∀ c : K, IsIntegral ℤ_[l] c → ∃ o : O, algebraMap O K o = c) → Submodule.span K (T : Set V) = ⊤ → ∀ v : V, ∃ n : ℕ, (l : K) ^ n • v ∈ T := by
  intro l _ K _ _ _ _ _ O _ _ V _ _ _ _ T hO hT v
  have hpow : ∀ (m : ℕ) (w : V), w ∈ T → (l : K) ^ m • w ∈ T := by
    intro m w hw
    have h : (l : K) ^ m = algebraMap O K ((l : O) ^ m) := by
      rw [map_pow, map_natCast]
    rw [h, algebraMap_smul]
    exact T.smul_mem _ hw
  have hv : v ∈ Submodule.span K (T : Set V) := hT ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨0, by simpa using hx⟩
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    refine ⟨a + b, ?_⟩
    rw [smul_add]
    refine T.add_mem ?_ ?_
    · rw [add_comm, pow_add, mul_smul]
      exact hpow _ _ ha
    · rw [pow_add, mul_smul]
      exact hpow _ _ hb
  | smul c x _ hx =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨n, hn⟩ := UpperTheory.pow_mul_isIntegral (l := l) c
    obtain ⟨o, ho⟩ := hO _ hn
    refine ⟨n + a, ?_⟩
    have h : (l : K) ^ (n + a) • c • x = o • ((l : K) ^ a • x) := by
      rw [← algebraMap_smul K o, ho, smul_smul, smul_smul]
      congr 1
      ring
    rw [h]
    exact T.smul_mem _ ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPrimeMem
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qk68.Plc :
    (E : Type) → [Field E] → Type :=
    fun (E : Type) [Field E] ↦ IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E)

theorem UpperTheory.Reformulated.B.Qk68.exists_prime_mem :
    ∀ {E : Type} [inst : Field E] [inst_1 : NumberField E] [NumberField.IsCMField E] (w : UpperTheory.Reformulated.B.Qk68.Plc E),
      ∃ (q : ℕ), Nat.Prime q ∧ (↑q : NumberField.RingOfIntegers E) ∈ w.asIdeal := by
  intro E _ _ _ w
  haveI : w.asIdeal.IsPrime := w.isPrime
  haveI : Finite (NumberField.RingOfIntegers E ⧸ w.asIdeal) :=
    Ideal.finiteQuotientOfFreeOfNeBot w.asIdeal w.ne_bot
  refine ⟨ringChar (NumberField.RingOfIntegers E ⧸ w.asIdeal), ?_, ?_⟩
  · exact (CharP.char_is_prime_or_zero (NumberField.RingOfIntegers E ⧸ w.asIdeal) _).resolve_right
      (CharP.ringChar_ne_zero_of_finite _)
  · rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    exact CharP.cast_eq_zero _ _
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsPsi
section
theorem UpperTheory.Reformulated.B.Qi48.exists_psi :
    ∀ (L T : Type) [inst : Field L] [IsAlgClosed L] [inst_2 : CommRing T]
    [inst_3 : Algebra L T] [Algebra.FiniteType L T] (m : Ideal T),
    m.IsMaximal → ∃ (ψ : T →ₐ[L] L), ∀ (x : T), (ψ : T → L) x = (0 : L) ↔ x ∈ m := by
  intro L T _ _ _ _ _ m hm
  letI : Field (T ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite L (T ⧸ m) := finite_of_finite_type_of_isJacobsonRing L (T ⧸ m)
  have hb : Function.Bijective (Algebra.ofId L (T ⧸ m)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  let e : L ≃ₐ[L] (T ⧸ m) := AlgEquiv.ofBijective (Algebra.ofId L (T ⧸ m)) hb
  refine ⟨(e.symm : (T ⧸ m) →ₐ[L] L).comp (Ideal.Quotient.mkₐ L m), fun x => ?_⟩
  change e.symm (Ideal.Quotient.mk m x) = 0 ↔ x ∈ m
  rw [map_eq_zero_iff e.symm e.symm.injective, Ideal.Quotient.eq_zero_iff_mem]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRetr
section
namespace FiniteTypeOfFiniteProjectiveExtension

private lemma exists_retr {C D : Type*} [CommRing C] [CommRing D] [Algebra C D] [Module.Finite C D]
    [Module.Projective C D] (h : Function.Injective (algebraMap C D)) :
    ∃ π : D →ₗ[C] C, π 1 = 1 := by
  let J : Ideal C := LinearMap.range (LinearMap.applyₗ (R := C) (M := D) (M₂ := C) (1 : D))
  obtain ⟨n, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective C D
  have key : ∀ d : D, d ∈ J • (⊤ : Submodule C D) := by
    intro d
    have hd : d = ∑ i, g d i • f (Pi.single i 1) := by
      have e1 : d = f (g d) := by
        have := LinearMap.congr_fun hfg d
        simpa using this.symm
      conv_lhs => rw [e1, ← Finset.univ_sum_single (g d)]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← map_smul]
      congr 1
      ext j
      simp [Pi.single_apply]
    rw [hd]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem_smul ?_ trivial
    refine LinearMap.mem_range.2 ⟨(LinearMap.proj i).comp (g.comp (LinearMap.mulLeft C d)), ?_⟩
    simp
  obtain ⟨r, hr1, hr0⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤
    (Module.Finite.fg_top) (fun d _ => key d)
  have hr : r = 0 := h (by simpa [Algebra.smul_def] using hr0 1 trivial)
  have h1 : (1 : C) ∈ J := by
    have := J.neg_mem hr1
    simpa [hr] using this
  obtain ⟨π, hπ⟩ := LinearMap.mem_range.1 h1
  exact ⟨π, by simpa using hπ⟩

end FiniteTypeOfFiniteProjectiveExtension

theorem UpperTheory.Reformulated.B.FiniteTypeDescent.main.{u_1, u_2, u_3} :
    ∀ (R : Type u_1) (C : Type u_2) (D : Type u_3) [inst : CommRing R] [inst_1 : CommRing C] [inst_2 : CommRing D]
      [inst_3 : Algebra R C] [inst_4 : Algebra C D] [inst_5 : Algebra R D] [IsScalarTower R C D] [Module.Finite C D]
      [Module.Projective C D],
      Function.Injective (⇑(Algebra.algebraMap C D) : C → D) → ∀ [Algebra.FiniteType R D], Algebra.FiniteType R C := by
  intro R C D _ _ _ _ _ _ _ _ _ hinj hft
  obtain ⟨π, hπ⟩ := FiniteTypeOfFiniteProjectiveExtension.exists_retr (C := C) (D := D) hinj
  obtain ⟨B₀, hB₀, hB₀D⟩ := exists_subalgebra_of_fg R C D hft.out (Module.Finite.fg_top)
  haveI : Module.Finite B₀ D := ⟨hB₀D⟩
  let π' : D →ₗ[B₀] C := π.restrictScalars B₀
  have hsurj : Function.Surjective π' := fun c =>
    ⟨algebraMap C D c, by
      show π (algebraMap C D c) = c
      rw [Algebra.algebraMap_eq_smul_one, map_smul, hπ, smul_eq_mul, mul_one]⟩
  haveI : Module.Finite B₀ C := Module.Finite.of_surjective π' hsurj
  haveI : Algebra.FiniteType R B₀ := ⟨B₀.fg_top.2 hB₀⟩
  exact Algebra.FiniteType.trans (S := B₀) inferInstance inferInstance
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRingHomExtendOfIsIntegral
section
theorem UpperTheory.Reformulated.B.RingHomExtensionOfIntegral.exists_ringHom_extend_of_isIntegral.{u_1, u_2, u_3} :
    ∀ {R : Type u_1} {S : Type u_2} {K : Type u_3} [inst : CommRing R] [inst_1 : CommRing S] [inst_2 : Field K]
      [IsAlgClosed K] [inst_4 : Algebra R S] [Algebra.IsIntegral R S],
      Function.Injective (⇑(Algebra.algebraMap R S) : R → S) →
        ∀ (f : R →+* K), ∃ (g : S →+* K), ∀ (r : R), (g : S → K) ((Algebra.algebraMap R S : R → S) r) = (f : R → K) r := by
  intro R S K _ _ _ _ _ _ hinj f
  have hP : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
  have hle : Ideal.comap (algebraMap R S) (⊥ : Ideal S) ≤ RingHom.ker f := by
    intro a ha
    have h0 : algebraMap R S a = 0 := by simpa using ha
    have : a = 0 := hinj (by rw [map_zero]; exact h0)
    simp [this]
  obtain ⟨Q, -, hQ, hQc⟩ := Ideal.exists_ideal_over_prime_of_isIntegral (RingHom.ker f) ⊥ hle
  have hlies : Q.LiesOver (RingHom.ker f) := (Ideal.liesOver_iff _ _).2 hQc.symm
  letI : Algebra (R ⧸ RingHom.ker f) K := (RingHom.kerLift f).toAlgebra
  have hK : Module.IsTorsionFree (R ⧸ RingHom.ker f) K :=
    Module.isTorsionFree_iff_algebraMap_injective.2 (RingHom.kerLift_injective f)
  have hS : Module.IsTorsionFree (R ⧸ RingHom.ker f) (S ⧸ Q) := by
    refine Module.isTorsionFree_iff_algebraMap_injective.2
      ((injective_iff_map_eq_zero _).2 fun x hx => ?_)
    obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective x
    have h2 : Ideal.Quotient.mk Q (algebraMap R S r) = 0 := hx
    rw [Ideal.Quotient.eq_zero_iff_mem] at h2
    rw [Ideal.Quotient.eq_zero_iff_mem, ← hQc]
    exact h2
  have hint : Algebra.IsIntegral (R ⧸ RingHom.ker f) (S ⧸ Q) :=
    Ideal.Quotient.algebra_isIntegral_of_liesOver Q (RingHom.ker f)
  have halg : Algebra.IsAlgebraic (R ⧸ RingHom.ker f) (S ⧸ Q) :=
    Algebra.IsIntegral.isAlgebraic
  let φ : (S ⧸ Q) →ₐ[R ⧸ RingHom.ker f] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨φ.toRingHom.comp (Ideal.Quotient.mk Q), fun r => ?_⟩
  have h1 : φ (algebraMap (R ⧸ RingHom.ker f) (S ⧸ Q) (Ideal.Quotient.mk _ r)) =
      algebraMap (R ⧸ RingHom.ker f) K (Ideal.Quotient.mk _ r) := φ.commutes _
  exact h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRootCongruence
section
open Polynomial

private theorem pow_congr {l : ℕ} [Fact (Nat.Prime l)] {x : PadicAlgCl l} (hx : ‖x‖ = 1) :
    ∃ n : ℕ, 0 < n ∧ ‖x ^ n - 1‖ < 1 := by
  have hint : IsIntegral ℚ_[l] x := (Algebra.IsAlgebraic.isAlgebraic x).isIntegral
  let F := IntermediateField.adjoin ℚ_[l] {x}
  have hF : FiniteDimensional ℚ_[l] F := IntermediateField.adjoin.finiteDimensional hint
  let V : Submodule ℚ_[l] (PadicAlgCl l) := F.toSubalgebra.toSubmodule
  have hV : FiniteDimensional ℚ_[l] V := hF
  have hP : ProperSpace V := FiniteDimensional.proper ℚ_[l] V
  have hxF : x ∈ F := IntermediateField.mem_adjoin_simple_self ℚ_[l] x
  let u : ℕ → V := fun n => ⟨x ^ n, pow_mem hxF n⟩
  have hu : ∀ n, u n ∈ Metric.closedBall (0 : V) 1 := by
    intro n
    rw [mem_closedBall_zero_iff]
    change ‖x ^ n‖ ≤ 1
    rw [norm_pow, hx, one_pow]
  obtain ⟨a, -, φ, hφ, ha⟩ := (isCompact_closedBall (0 : V) 1).tendsto_subseq hu
  obtain ⟨N, hN⟩ := Metric.cauchySeq_iff'.1 ha.cauchySeq 1 one_pos
  have h1 := hN (N + 1) (Nat.le_succ N)
  have hlt : φ N < φ (N + 1) := hφ (Nat.lt_succ_self N)
  refine ⟨φ (N + 1) - φ N, Nat.sub_pos_of_lt hlt, ?_⟩
  have h2 : ‖x ^ φ (N + 1) - x ^ φ N‖ < 1 := by
    rw [dist_eq_norm] at h1
    exact h1
  have h3 : x ^ φ (N + 1) - x ^ φ N = x ^ φ N * (x ^ (φ (N + 1) - φ N) - 1) := by
    rw [mul_sub, ← pow_add, Nat.add_sub_cancel' hlt.le, mul_one]
  rwa [h3, norm_mul, norm_pow, hx, one_pow, one_mul] at h2

private theorem descend {l : ℕ} [hl : Fact (Nat.Prime l)] {y : PadicAlgCl l} (hy : ‖y‖ = 1)
    (h : ‖y ^ l - 1‖ < 1) : ‖y - 1‖ < 1 := by
  have hp : ‖(l : PadicAlgCl l)‖ < 1 := by
    rw [← map_natCast (algebraMap ℚ_[l] (PadicAlgCl l)), norm_algebraMap']
    exact Padic.norm_p_lt_one
  set z := y - 1 with hz
  have hz1 : ‖z‖ ≤ 1 := by
    have := IsUltrametricDist.norm_add_le_max y (-1)
    rw [norm_neg, norm_one, hy, max_self, ← sub_eq_add_neg] at this
    exact this
  have hyz : y = z + 1 := by rw [hz]; ring
  have e := add_pow_prime_eq' hl.out z 1
  set S := ∑ k ∈ Finset.Ioo 0 l, z ^ k * 1 ^ (l - k) * ((l.choose k / l : ℕ) : PadicAlgCl l)
    with hS
  have hS1 : ‖S‖ ≤ 1 := by
    apply IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one
    intro k _
    rw [one_pow, mul_one, norm_mul, norm_pow]
    exact mul_le_one₀ (pow_le_one₀ (norm_nonneg _) hz1) (norm_nonneg _)
      (IsUltrametricDist.norm_natCast_le_one _ _)
  have e2 : z ^ l = (y ^ l - 1) + -((l : PadicAlgCl l) * S) := by
    rw [hyz, e]; ring
  have h4 : ‖z ^ l‖ < 1 := by
    rw [e2]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt h ?_)
    rw [norm_neg, norm_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_left (norm_nonneg _) hp hS1
  rw [norm_pow] at h4
  exact (pow_lt_one_iff_of_nonneg (norm_nonneg _) hl.out.ne_zero).1 h4

private theorem coprime_pow_congr {l : ℕ} [hl : Fact (Nat.Prime l)] {x : PadicAlgCl l}
    (hx : ‖x‖ = 1) : ∃ m : ℕ, ¬l ∣ m ∧ ‖x ^ m - 1‖ < 1 := by
  obtain ⟨n, hn, h⟩ := pow_congr hx
  obtain ⟨k, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hn.ne' l hl.out.ne_one
  refine ⟨m, hm, ?_⟩
  clear hn
  induction k with
  | zero => simpa using h
  | succ k ih =>
    apply ih
    apply descend (by rw [norm_pow, hx, one_pow])
    rwa [← pow_mul, mul_right_comm, ← pow_succ]

theorem UpperTheory.Reformulated.B.ExistsRootCongruence.exists_root_congr :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {x : PadicAlgCl l},
    ‖x‖ = (1 : ℝ) → ∃ (m : ℕ) (ζ : PadicAlgCl l), ¬l ∣ m ∧ ζ ^ m = (1 : PadicAlgCl l) ∧ ‖x - ζ‖ < (1 : ℝ) := by
  intro l _ x hx
  obtain ⟨m, hm, h⟩ := coprime_pow_congr hx
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; exact hm (dvd_zero l))
  haveI : NeZero m := ⟨hm0.ne'⟩
  obtain ⟨μ, hμ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot (PadicAlgCl l) m
  have e := congrArg (eval x) (X_pow_sub_one_eq_prod hm0 hμ)
  simp only [eval_sub, eval_pow, eval_X, eval_one, eval_prod, eval_C] at e
  by_contra hcon
  push Not at hcon
  rw [e, norm_prod] at h
  refine absurd h (not_lt.2 ?_)
  refine Finset.prod_induction _ (fun r : ℝ => 1 ≤ r)
    (fun a b ha hb => one_le_mul_of_one_le_of_one_le ha hb) le_rfl ?_
  intro ζ hζ
  exact hcon m ζ hm ((mem_nthRootsFinset hm0 1).1 hζ)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ExistsRowsLinearIndependent
section
theorem UpperTheory.Reformulated.B.Qm10.exists_rows_linearIndependent.{u, u_1, u_2} :
    ∀ {K : Type u_1} [inst : Field K] {r : Type u} {c : Type u_2} [Fintype r] [inst_2 : Fintype c]
    (P : Matrix r c K) {k : ℕ}, k ≤ P.rank → ∃ (I : Fin k → r), LinearIndependent K fun (p : Fin k) ↦ P (I p) := by
  intro K _ r c _ _ P k hk
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' K P.row
  haveI : Finite κ := Finite.of_injective a ha
  haveI : Fintype κ := Fintype.ofFinite κ
  have hcard : Fintype.card (Fin k) ≤ Fintype.card κ := by
    rw [Fintype.card_fin, ← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row]
    exact hk
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le hcard
  exact ⟨fun p ↦ a (e p), hli.comp e e.injective⟩
end

