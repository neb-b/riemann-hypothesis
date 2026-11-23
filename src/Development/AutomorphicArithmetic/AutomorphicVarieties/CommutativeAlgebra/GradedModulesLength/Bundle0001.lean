module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.DehHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.deh_holds :
    ∀ (O A : Type) [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] (I : Ideal A),
      I.IsHomogeneous 𝒜 → ∀ (d w : ℤ) (f h : A), d ≠ 0 → f ∈ 𝒜 d → h ∈ 𝒜 w → h ∈ I ⊔ Ideal.span {f - 1} → ∃ n : ℕ, f ^ n * h ∈ I := by
  classical
  intro O A _ _ _ 𝒜 _ I hI d w f h hd hf hh hmem
  obtain ⟨i, hi, y, hy, hsum⟩ := Submodule.mem_sup.mp hmem
  obtain ⟨u, rfl⟩ := Ideal.mem_span_singleton'.mp hy
  set c : ℤ → A := fun j => (DirectSum.decompose 𝒜 u j : A) with hc
  have hcomp : ∀ j : ℤ, (DirectSum.decompose 𝒜 h (j + d) : A) - c j * f + c (j + d) ∈ I := by
    intro j
    have h1 : (DirectSum.decompose 𝒜 i (j + d) : A) ∈ I := hI (j + d) hi
    have h2 : i = h - u * f + u := by rw [← hsum]; ring
    have h3 : (DirectSum.decompose 𝒜 (u * f) (j + d) : A) = c j * f :=
      DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hf
    rw [h2, DirectSum.decompose_add, DirectSum.decompose_sub, DirectSum.add_apply,
      DirectSum.sub_apply, Submodule.coe_add, Submodule.coe_sub, h3] at h1
    exact h1
  let q := Ideal.Quotient.mk I
  have hne : ∀ j : ℤ, j + d ≠ w → q (c (j + d)) = q (c j) * q f := by
    intro j hj
    have h1 := hcomp j
    rw [DirectSum.decompose_of_mem_ne 𝒜 hh (Ne.symm hj)] at h1
    have h2 := (Ideal.Quotient.eq_zero_iff_mem).mpr h1
    simp only [map_add (f := _), map_sub, map_mul, map_zero] at h2
    linear_combination h2
  have heq : q (c w) = q (c (w - d)) * q f - q h := by
    have h1 := hcomp (w - d)
    rw [sub_add_cancel, DirectSum.decompose_of_mem_same 𝒜 hh] at h1
    have h2 := (Ideal.Quotient.eq_zero_iff_mem).mpr h1
    simp only [map_add (f := _), map_sub, map_mul] at h2
    linear_combination h2
  have hfin : ∀ e : ℤ, e ≠ 0 → ∀ a : ℤ, ∃ n : ℕ, c (a + n * e) = 0 := by
    intro e he a
    by_contra hcon
    push Not at hcon
    have hinj : Function.Injective (fun n : ℕ => a + (n : ℤ) * e) := by
      intro m n hmn
      have h1 : (m : ℤ) * e = n * e := add_left_cancel hmn
      exact_mod_cast mul_right_cancel₀ he h1
    refine Set.infinite_of_injective_forall_mem hinj
      (s := ((DirectSum.decompose 𝒜 u).support : Set ℤ)) ?_ (Finset.finite_toSet _)
    intro n
    rw [Finset.mem_coe, DFinsupp.mem_support_iff]
    intro h0
    apply hcon n
    simp only [hc]
    rw [h0]; rfl
  have hA : ∀ k : ℕ, q (c (w - d)) = q (c (w - d + k * (-d))) * q f ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have e1 : w - d + (k : ℤ) * (-d) = (w - d + ((k + 1 : ℕ) : ℤ) * (-d)) + d := by
        push_cast; ring
      have e2 : (w - d + ((k + 1 : ℕ) : ℤ) * (-d)) + d ≠ w := by
        rw [← e1]
        intro h0
        have h1 : ((k : ℤ) + 1) * d = 0 := by linear_combination -h0
        rcases mul_eq_zero.mp h1 with h2 | h2
        · omega
        · exact hd h2
      rw [ih, e1, hne _ e2]; ring
  have h0 : q (c (w - d)) = 0 := by
    obtain ⟨n, hn⟩ := hfin (-d) (neg_ne_zero.mpr hd) (w - d)
    rw [hA n, hn]; simp
  have hB : ∀ k : ℕ, q (c (w + k * d)) = - (q f ^ k * q h) := by
    intro k
    induction k with
    | zero => simp [heq, h0]
    | succ k ih =>
      have e1 : w + ((k + 1 : ℕ) : ℤ) * d = (w + (k : ℤ) * d) + d := by
        push_cast; ring
      have e2 : (w + (k : ℤ) * d) + d ≠ w := by
        intro h0
        have h1 : ((k : ℤ) + 1) * d = 0 := by linear_combination h0
        rcases mul_eq_zero.mp h1 with h2 | h2
        · omega
        · exact hd h2
      rw [e1, hne _ e2, ih]; ring
  obtain ⟨n, hn⟩ := hfin d hd w
  refine ⟨n, Ideal.Quotient.eq_zero_iff_mem.mp ?_⟩
  have h1 := hB n
  rw [hn, map_zero] at h1
  rw [map_mul, map_pow]
  exact neg_eq_zero.mp h1.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.EtHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

private theorem et_point (E K C : Type) [Field E] [Field K] [Algebra E K] [IsAlgClosed K] [CommRing C] [Algebra E C]
    [Algebra.FiniteType E C] (m : Ideal C) [m.IsMaximal] :
    ∃ ι : (C ⧸ m) →ₐ[E] K, Function.Injective ι := by
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite E (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing E (C ⧸ m)
  let ι : (C ⧸ m) →ₐ[E] K := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  exact ⟨ι, ι.toRingHom.injective⟩

private theorem et_unram (O K C : Type) [CommRing O] [Field K] [Algebra O K] [CommRing C] [Algebra O C]
    [Algebra.FiniteType O C]
    (hp : ∀ m : Ideal C, m.IsMaximal → ∃ ι : (C ⧸ m) →ₐ[O] K, Function.Injective ι)
    (hD : ∀ ξ : C →ₐ[O] K, PtDer ξ K = ⊥) : Algebra.FormallyUnramified O C := by
  have key : ∀ m : Ideal C, m.IsMaximal → (⊤ : Submodule C Ω[C⁄O]) ≤ m • ⊤ := by
    intro m hm x _
    by_contra hx
    letI : Field (C ⧸ m) := Ideal.Quotient.field m
    obtain ⟨ι, hι⟩ := hp m hm
    have hq : Submodule.Quotient.mk (p := m • (⊤ : Submodule C Ω[C⁄O])) x ≠ 0 := by
      rwa [Ne, Submodule.Quotient.mk_eq_zero]
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual (C ⧸ m) (Ω[C⁄O] ⧸ m • (⊤ : Submodule C Ω[C⁄O])),
        φ (Submodule.Quotient.mk x) ≠ 0 := by
      by_contra hall
      push_neg at hall
      exact hq ((Module.forall_dual_apply_eq_zero_iff (C ⧸ m) _).mp hall)
    let f : Ω[C⁄O] →ₗ[C] C ⧸ m := (φ.restrictScalars C).comp (m • (⊤ : Submodule C Ω[C⁄O])).mkQ
    let D : Derivation O C (C ⧸ m) := f.compDer (KaehlerDifferential.D O C)
    let ξ : C →ₐ[O] K := ι.comp (Ideal.Quotient.mkₐ O m)
    let L : C →ₗ[O] K := ι.toLinearMap.comp (D : C →ₗ[O] C ⧸ m)
    have hL : L ∈ PtDer ξ K := by
      intro a b
      show ι (D (a * b)) = ι (Ideal.Quotient.mk m a) • ι (D b) + ι (Ideal.Quotient.mk m b) • ι (D a)
      rw [Derivation.leibniz, Algebra.smul_def, Algebra.smul_def, map_add (f := _), map_mul, map_mul,
        smul_eq_mul, smul_eq_mul]
      rfl
    rw [hD ξ, Submodule.mem_bot] at hL
    have hDz : ∀ c, D c = 0 := by
      intro c
      apply hι
      rw [map_zero]
      exact LinearMap.congr_fun hL c
    have hf : f = 0 := by
      apply LinearMap.ext_on_range (KaehlerDifferential.span_range_derivation O C)
      intro c
      simpa [D] using hDz c
    apply hφ
    have h2 := LinearMap.congr_fun hf x
    simpa [f] using h2
  have hfg : (⊤ : Submodule C Ω[C⁄O]).FG := Module.finite_def.mp inferInstance
  have hann : Module.annihilator C Ω[C⁄O] = ⊤ := by
    by_contra hne
    obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
    obtain ⟨r, hr1, hr⟩ :=
      Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul m ⊤ hfg (key m hm)
    have hrJ : r ∈ Module.annihilator C Ω[C⁄O] := Module.mem_annihilator.mpr (fun n => hr n trivial)
    have h3 := m.sub_mem (hle hrJ) hr1
    rw [sub_sub_cancel] at h3
    exact hm.ne_top ((Ideal.eq_top_iff_one m).mpr h3)
  have h1 : (1 : C) ∈ Module.annihilator C Ω[C⁄O] := by
    rw [hann]
    exact Submodule.mem_top
  have h0 : ∀ n : Ω[C⁄O], n = 0 := by
    intro n
    rw [← one_smul C n]
    exact Module.mem_annihilator.mp h1 n
  exact ⟨⟨fun a b => (h0 a).trans (h0 b).symm⟩⟩

theorem UpperTheory.V.Alg.M.et_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (K : Type) [Field K] [Algebra O K] [IsAlgClosed K] [FaithfulSMul O K]
      (C : Type) [CommRing C] [Algebra O C] [Algebra.FiniteType O C], (∀ c : O, c ≠ 0 → IsUnit (algebraMap O C c)) →
      (∀ ξ : C →ₐ[O] K, PtDer ξ K = ⊥) → Finite (C →ₐ[O] K) ∧ ∀ h : C, (∀ ξ : C →ₐ[O] K, ξ h = 0) → h = 0 := by
  intro O _ _ _ _ _ K _ _ _ _ C _ _ _ hunit hD
  have huC : ∀ y : nonZeroDivisors O, IsUnit (algebraMap O C y) :=
    fun y => hunit y (nonZeroDivisors.ne_zero y.2)
  have hinjK : Function.Injective (algebraMap O K) := FaithfulSMul.algebraMap_injective O K
  have huK : ∀ y : nonZeroDivisors O, IsUnit (algebraMap O K y) := by
    intro y
    refine isUnit_iff_ne_zero.mpr (fun h0 => nonZeroDivisors.ne_zero y.2 (hinjK ?_))
    rw [h0, map_zero]
  letI : Algebra (FractionRing O) C :=
    (IsLocalization.lift (M := nonZeroDivisors O) (S := FractionRing O) huC).toAlgebra
  letI : Algebra (FractionRing O) K :=
    (IsLocalization.lift (M := nonZeroDivisors O) (S := FractionRing O) huK).toAlgebra
  haveI : IsScalarTower O (FractionRing O) C := IsScalarTower.of_algebraMap_eq
    (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors O) (S := FractionRing O) huC r).symm)
  haveI : IsScalarTower O (FractionRing O) K := IsScalarTower.of_algebraMap_eq
    (fun r => (IsLocalization.lift_eq (M := nonZeroDivisors O) (S := FractionRing O) huK r).symm)
  haveI : Algebra.FiniteType (FractionRing O) C :=
    Algebra.FiniteType.of_restrictScalars_finiteType O (FractionRing O) C
  have hpt : ∀ m : Ideal C, m.IsMaximal → ∃ ι : (C ⧸ m) →ₐ[O] K, Function.Injective ι := by
    intro m hm
    haveI := hm
    obtain ⟨ι, hι⟩ := et_point (FractionRing O) K C m
    exact ⟨ι.restrictScalars O, hι⟩
  haveI : Algebra.FormallyUnramified O C := et_unram O K C hpt hD
  haveI : Algebra.FormallyUnramified (FractionRing O) C :=
    Algebra.FormallyUnramified.of_restrictScalars O (FractionRing O) C
  haveI : Module.Finite (FractionRing O) C := Algebra.FormallyUnramified.finite_of_free (FractionRing O) C
  haveI : IsReduced C := Algebra.FormallyUnramified.isReduced_of_field (FractionRing O) C
  refine ⟨?_, ?_⟩
  · have hcompat : ∀ ξ : C →ₐ[O] K, ∀ r : FractionRing O,
        ξ (algebraMap (FractionRing O) C r) = algebraMap (FractionRing O) K r := by
      intro ξ r
      have hc : ξ.toRingHom.comp (algebraMap (FractionRing O) C) = algebraMap (FractionRing O) K := by
        apply IsLocalization.ringHom_ext (nonZeroDivisors O)
        apply RingHom.ext
        intro a
        rw [RingHom.comp_apply, RingHom.comp_apply, RingHom.comp_apply, ← IsScalarTower.algebraMap_apply,
          ← IsScalarTower.algebraMap_apply]
        exact ξ.commutes a
      exact RingHom.congr_fun hc r
    let up : (C →ₐ[O] K) → (C →ₐ[FractionRing O] K) := fun ξ => { ξ.toRingHom with commutes' := hcompat ξ }
    have hup : Function.Injective up := by
      intro ξ₁ ξ₂ h
      ext c
      exact AlgHom.congr_fun h c
    haveI : Finite (C →ₐ[FractionRing O] K) := (linearIndependent_toLinearMap (FractionRing O) C K).finite
    exact Finite.of_injective up hup
  · intro h hh
    haveI : IsJacobsonRing C := isJacobsonRing_of_finiteType (A := FractionRing O)
    have hrad : (⊥ : Ideal C).IsRadical := by
      intro x hx
      obtain ⟨n, hn⟩ := hx
      rw [Ideal.mem_bot] at hn ⊢
      exact IsNilpotent.eq_zero ⟨n, hn⟩
    have hj := IsJacobsonRing.out' (⊥ : Ideal C) hrad
    rw [← Ideal.mem_bot, ← hj, Ideal.jacobson, Ideal.mem_sInf]
    rintro J ⟨-, hJ⟩
    haveI := hJ
    obtain ⟨ι, hι⟩ := hpt J hJ
    have h5 := hh (ι.comp (Ideal.Quotient.mkₐ O J))
    rw [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← map_zero ι] at h5
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hι h5)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ExistsSecNotMem
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

section SlopeTestRemainingChoices

variable {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ} (N : Fin k → Submodule B A)

private theorem coe_sec_eq_monomial_single (i : Fin k) (f : A) (hf : f ∈ N i) :
    (sec N i f hf : MvPolynomial (Fin k) A) = MvPolynomial.monomial (Finsupp.single i 1) f := rfl

private theorem toDeg_single_one (i : Fin k) : toDeg (Finsupp.single i 1) = e i := by
  funext j
  by_cases h : j = i
  · subst h
    simp [toDeg, e]
  · simp [toDeg, e, h, Finsupp.single_apply, Ne.symm h]

private theorem exists_sec_notMem {p : Ideal (rees N)} (hp : ¬ Irr (reesGr N) ≤ p) (i : Fin k) :
    ∃ (f : A) (hf : f ∈ N i), sec N i f hf ∉ p := by
  by_contra hcon
  push_neg at hcon
  apply hp
  have hle : Ideal.span (reesGr N (e i) : Set (rees N)) ≤ p := by
    rw [Ideal.span_le]
    intro q hq
    have hc : AddMonoidAlgebra.coeff (q : MvPolynomial (Fin k) A) (Finsupp.single i 1) ∈ N i := by
      have := q.2 (Finsupp.single i 1)
      rwa [lat_single] at this
    have hq' : q = sec N i _ hc := by
      apply Subtype.ext
      rw [coe_sec_eq_monomial_single]
      ext m
      rw [MvPolynomial.coeff_monomial]
      split_ifs with hm
      · rw [hm]
      · apply hq m
        intro hd
        apply hm
        apply toDeg_injective
        rw [hd, toDeg_single_one]
    rw [hq']
    exact hcon _ hc
  exact le_trans (le_trans Ideal.prod_le_inf (Finset.inf_le (Finset.mem_univ i))) hle

private theorem sec_mul_sec (i j : Fin k) {f g : A} (hf : f ∈ N i) (hg : g ∈ N i) (hf' : f ∈ N j) (hg' : g ∈ N j) :
    sec N i f hf * sec N j g hg' = sec N i g hg * sec N j f hf' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, coe_sec_eq_monomial_single, MvPolynomial.monomial_mul]
  rw [mul_comm f g]

end SlopeTestRemainingChoices

private theorem algebraMap_mul_sec_mul_sec_eq_of_mul_eq {B A : Type} [CommRing B] [CommRing A] [Algebra B A] {k : ℕ}
    (N : Fin k → Submodule B A) (c : B) (i j : Fin k) {x y x' y' : A} (hx : x ∈ N i) (hy : y ∈ N j)
    (hx' : x' ∈ N i) (hy' : y' ∈ N j) (h : algebraMap B A c * x * y = x' * y') :
    algebraMap B (rees N) c * (sec N i x hx * sec N j y hy) = sec N i x' hx' * sec N j y' hy' := by
  apply Subtype.ext
  simp only [Subalgebra.coe_mul, Subalgebra.coe_algebraMap, coe_sec_eq_monomial_single, MvPolynomial.algebraMap_apply,
    MvPolynomial.monomial_mul, MvPolynomial.C_mul_monomial]
  rw [← h, mul_assoc]

theorem UpperTheory.V.Alg.M.zi_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (r s r' s' m : ℕ) (Q : Eqns 𝒜 x r s r' s' m),
    ∀ p : Ideal (mR Q), p.IsPrime → ¬ Irr (mGr Q) ≤ p → secs (ts Q) ≤ p → (∀ i, algebraMap (𝒜 0) (mR Q) ⟨Q.Z i, (Q.hZ i).1⟩ ∈ p) →
      (∀ b : 𝒜 0, (b : A) ∈ Q.ideal → algebraMap (𝒜 0) (mR Q) b ∈ p) ∧
      ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ p := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ r s r' s' m Q P hP hIrr hts hZ
  have hmul : ∀ {i j l : ℤ} {a b : A}, i + j = l → a ∈ 𝒜 i → b ∈ 𝒜 j → a * b ∈ 𝒜 l := by
    rintro i j l a b rfl ha hb
    exact SetLike.mul_mem_graded ha hb
  have m0 : ∀ {a : A}, a ∈ 𝒜 (-2) → a ∈ mN 𝒜 (Q.F (Fin.last r)) 0 := fun h => h
  have m1 : ∀ {a : A}, a ∈ 𝒜 2 → a ∈ mN 𝒜 (Q.F (Fin.last r)) 1 := fun h => h
  have m2 : ∀ {a : A}, a ∈ mN 𝒜 (Q.F (Fin.last r)) 2 → a ∈ 𝒜 (-2) := by
    intro a ha
    have hle : ((𝒜 0) ∙ Q.F (Fin.last r) ^ 2 ⊔ oz 𝒜 (-2) * oz 𝒜 (-2) * oz 𝒜 2 : Submodule (𝒜 0) A)
        ≤ oz 𝒜 (-2) := by
      apply sup_le
      · rw [Submodule.span_le, Set.singleton_subset_iff]
        exact sq_mem_neg 𝒜 (Q.hF _)
      · apply Submodule.mul_le.2
        intro u hu v hv
        have hu' : u ∈ oz 𝒜 (-4) :=
          (Submodule.mul_le.2 (fun a ha b hb => hmul (i := -2) (j := -2) (by norm_num) ha hb) :
            oz 𝒜 (-2) * oz 𝒜 (-2) ≤ oz 𝒜 (-4)) hu
        exact hmul (i := -4) (j := 2) (by norm_num) hu' hv
    exact hle ha
  have hF2 : Q.F (Fin.last r) ^ 2 ∈ mN 𝒜 (Q.F (Fin.last r)) 2 :=
    Submodule.mem_sup_left (Submodule.mem_span_singleton_self _)
  have hmem : ∀ {d : Deg 3} {u : mR Q}, (d, u) ∈ ts Q → u ∈ P := fun h => hts (Ideal.subset_span ⟨_, h⟩)
  obtain ⟨g0, hg0, hg0P⟩ := exists_sec_notMem _ hIrr 0
  obtain ⟨f1, hf1, hf1P⟩ := exists_sec_notMem _ hIrr 1
  obtain ⟨h2, hh2, hh2P⟩ := exists_sec_notMem _ hIrr 2
  have hFlast : sec (mN 𝒜 (Q.F (Fin.last r))) 2 (Q.F (Fin.last r) ^ 2) hF2 ∈ P :=
    hmem (d := e 2) (by simp [ts, tsR])
  have hsq : ∀ i, sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F i ^ 2) (sq_mem_neg 𝒜 (Q.hF i)) ∈ P := by
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · have heq := sec_mul_sec (mN 𝒜 (Q.F (Fin.last r))) 0 2 (sq_mem_neg 𝒜 (Q.hF (Fin.last r)))
        (m0 (m2 hh2)) hF2 hh2
      have hin : sec (mN 𝒜 (Q.F (Fin.last r))) 0 (Q.F (Fin.last r) ^ 2) (sq_mem_neg 𝒜 (Q.hF (Fin.last r))) *
          sec (mN 𝒜 (Q.F (Fin.last r))) 2 h2 hh2 ∈ P := by
        rw [heq]
        exact P.mul_mem_left _ hFlast
      exact (hP.mem_or_mem hin).resolve_right hh2P
    · exact hmem (d := e 0) (by simp [ts, tsF, List.mem_ofFn])
  refine ⟨?_, hsq⟩
  set u := sec (mN 𝒜 (Q.F (Fin.last r))) 0 g0 hg0 * sec (mN 𝒜 (Q.F (Fin.last r))) 1 f1 hf1 with hu_def
  have hu : u ∉ P := fun h => (hP.mem_or_mem h).elim hg0P hf1P
  have key : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) w * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P :=
    fun w h => (hP.mem_or_mem h).resolve_right hu
  have keysq : ∀ w : 𝒜 0, algebraMap (𝒜 0) (mR Q) (w * w) * u ∈ P → algebraMap (𝒜 0) (mR Q) w ∈ P := by
    intro w h
    have := key _ h
    rw [map_mul] at this
    exact (hP.mem_or_mem this).elim id id
  have hgen : ∀ (d : ℤ) (g : A) (hg : g ∈ 𝒜 d),
      (∀ (j : ℤ) (hj : j + d = 0) (c : A) (hc : c ∈ 𝒜 j),
        algebraMap (𝒜 0) (mR Q) ⟨c * g, hmul hj hc hg⟩ ∈ P) →
      ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * g) 0) ∈ P := by
    intro d g hg hc a
    induction a using DirectSum.Decomposition.inductionOn 𝒜 with
    | zero => simp
    | @homogeneous j a =>
      by_cases hj : j + d = 0
      · have h0 := hc j hj a a.2
        convert h0 using 2
        apply Subtype.ext
        exact DirectSum.decompose_of_mem_same 𝒜 (hmul hj a.2 hg)
      · have h0 : DirectSum.decompose 𝒜 ((a : A) * g) 0 = 0 :=
          Subtype.ext (DirectSum.decompose_of_mem_ne 𝒜 (hmul rfl a.2 hg) hj)
        rw [h0, map_zero]
        exact P.zero_mem
    | add a a' ha ha' =>
      rw [add_mul, DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      exact P.add_mem ha ha'
  intro b hb
  have hall : ∀ y ∈ Q.ideal, ∀ a : A, algebraMap (𝒜 0) (mR Q) (DirectSum.decompose 𝒜 (a * y) 0) ∈ P := by
    intro y hy
    unfold Eqns.ideal at hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      rcases hy with ((((⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩)
      · refine hgen (-1) _ (Q.hF i) ?_
        intro j hj c hc
        obtain rfl : j = 1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (sq_mem_neg 𝒜 (Q.hF i))
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num)
            (hmul (i := 1) (j := 1) (by norm_num) hc hc) hg0) hf1)) (by change c * Q.F i * (c * Q.F i) * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hsq i)
      · refine hgen (-2) _ (Q.hG i) ?_
        intro j hj c hc
        obtain rfl : j = 2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1 (Q.hG i)
          (m1 (hmul (i := 0) (j := 2) (by norm_num) (hmul (i := 2) (j := -2) (by norm_num) hc hg0) hf1))
          (by change c * Q.G i * g0 * f1 = _; ring)]
        exact P.mul_mem_right _ (hmem (d := e 0) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 1 _ (Q.hE i) ?_
        intro j hj c hc
        obtain rfl : j = -1 := by omega
        apply keysq
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num)
            (hmul (i := -1) (j := -1) (by norm_num) hc hc) hg0) hf1)) (sq_mem_pos 𝒜 (Q.hE i))
          (by change c * Q.E i * (c * Q.E i) * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 2 _ (Q.hE' i) ?_
        intro j hj c hc
        obtain rfl : j = -2 := by omega
        apply key
        rw [algebraMap_mul_sec_mul_sec_eq_of_mul_eq _ _ 0 1 hg0 hf1
          (m0 (hmul (i := -4) (j := 2) (by norm_num) (hmul (i := -2) (j := -2) (by norm_num) hc hg0) hf1))
          (Q.hE' i) (by change c * Q.E' i * g0 * f1 = _; ring)]
        exact P.mul_mem_left _ (hmem (d := e 1) (by simp [ts, tsR, List.mem_ofFn]))
      · refine hgen 0 _ (Q.hZ i).1 ?_
        intro j hj c hc
        obtain rfl : j = 0 := by omega
        have : (⟨c * Q.Z i, hmul hj hc (Q.hZ i).1⟩ : 𝒜 0) = ⟨c, hc⟩ * ⟨Q.Z i, (Q.hZ i).1⟩ := rfl
        rw [this, map_mul]
        exact P.mul_mem_left _ (hZ i)
    | zero => intro a; simp
    | add y z _ _ hy hz =>
      intro a
      rw [mul_add, DirectSum.decompose_add, DirectSum.add_apply, map_add (f := _)]
      exact P.add_mem (hy a) (hz a)
    | smul c y _ hy =>
      intro a
      rw [smul_eq_mul, ← mul_assoc]
      exact hy (a * c)
  have h1 := hall _ hb 1
  rw [one_mul] at h1
  convert h1 using 2
  apply Subtype.ext
  exact (DirectSum.decompose_of_mem_same 𝒜 b.2).symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.FgHolds
section
open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

theorem UpperTheory.V.Alg.M.fg_holds :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ j, (oz 𝒜 j).FG := by
  classical
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x hx j
  obtain ⟨s, -, hadj⟩ := hx.gen
  have hadj' : Algebra.adjoin (𝒜 0) (s : Set A) = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y ∈ Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) := by rw [hadj]; trivial
    have hle : Algebra.adjoin O ((𝒜 0 : Set A) ∪ ↑s) ≤
        (Algebra.adjoin (𝒜 0) (s : Set A)).restrictScalars O := by
      rw [Algebra.adjoin_le_iff]
      rintro z (hz | hz)
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact (Algebra.adjoin (𝒜 0) (s : Set A)).algebraMap_mem ⟨z, hz⟩
      · rw [SetLike.mem_coe, Subalgebra.mem_restrictScalars]
        exact Algebra.subset_adjoin hz
    exact (Subalgebra.mem_restrictScalars O).1 (hle hy)
  haveI : Algebra.FiniteType (𝒜 0) A := ⟨⟨s, hadj'⟩⟩
  haveI : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing (𝒜 0) A
  have hI : (Ideal.span (𝒜 j : Set A)).FG := IsNoetherian.noetherian _
  obtain ⟨t, ht, hspan⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hI
  refine ⟨t, le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    exact ht
  · intro y hy
    have hyA : y ∈ 𝒜 j := hy
    have hy' : y ∈ Submodule.span A (t : Set A) := by
      rw [← hspan]
      exact Submodule.subset_span hyA
    obtain ⟨f, -, hf⟩ := Submodule.mem_span_finset.1 hy'
    have hyj : y = (DirectSum.decompose 𝒜 y j : A) := (DirectSum.decompose_of_mem_same 𝒜 hyA).symm
    rw [hyj, ← hf, DirectSum.decompose_sum, DFinsupp.finsetSum_apply, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have e : (DirectSum.decompose 𝒜 (f i • i) j : A) = (DirectSum.decompose 𝒜 (f i) 0 : A) * i := by
      have := DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 (a := f i) (i := 0) (ht hi)
      rw [zero_add] at this
      exact this
    rw [e]
    exact Submodule.smul_mem _ (DirectSum.decompose 𝒜 (f i) 0) (Submodule.subset_span hi)
end

