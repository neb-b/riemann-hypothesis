module

public import Mathlib

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GroupAlgebraSingleOneMemOfSpan
section
namespace GlobalTheory

theorem groupAlgebra_single_one_mem_of_span {A X : Type} [CommRing A] [AddCommGroup X]
    (R : Subring (AddMonoidAlgebra A X)) (h0 : ∀ a : A, AddMonoidAlgebra.single 0 a ∈ R) (α : X)
    (h : Ideal.span {a : A | AddMonoidAlgebra.single α a ∈ R} = ⊤) :
    AddMonoidAlgebra.single α (1 : A) ∈ R := by
  have key : ∀ a ∈ Ideal.span {a : A | AddMonoidAlgebra.single α a ∈ R},
      AddMonoidAlgebra.single α a ∈ R := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem x hx => exact hx
    | zero => rw [AddMonoidAlgebra.single_zero]; exact R.zero_mem
    | add x y _ _ hx hy => rw [AddMonoidAlgebra.single_add]; exact R.add_mem hx hy
    | smul c x _ hx =>
      have := R.mul_mem (h0 c) hx
      rwa [AddMonoidAlgebra.single_mul_single, zero_add] at this
  exact key 1 (h ▸ Submodule.mem_top)

theorem groupAlgebra_subring_eq_top :
    (∀ (A X : Type) [CommRing A] [AddCommGroup X] (I : Type) (e : Module.Basis I ℤ X) (R : Subring (AddMonoidAlgebra A X)), (∀ a : A, AddMonoidAlgebra.single 0 a ∈ R) → (∀ i, Ideal.span {a : A | AddMonoidAlgebra.single (e i) a ∈ R} = ⊤ ∧ Ideal.span {a : A | AddMonoidAlgebra.single (-e i) a ∈ R} = ⊤) → R = ⊤) := by
  intro A X _ _ I e R h0 h
  have hadd : ∀ x y : X, AddMonoidAlgebra.single x (1 : A) ∈ R →
      AddMonoidAlgebra.single y (1 : A) ∈ R → AddMonoidAlgebra.single (x + y) (1 : A) ∈ R := by
    intro x y hx hy
    have := R.mul_mem hx hy
    rwa [AddMonoidAlgebra.single_mul_single, one_mul] at this
  let S : AddSubgroup X :=
    { carrier := {x | AddMonoidAlgebra.single x (1 : A) ∈ R ∧
        AddMonoidAlgebra.single (-x) (1 : A) ∈ R}
      zero_mem' := ⟨h0 1, by rw [neg_zero]; exact h0 1⟩
      add_mem' := fun {x y} hx hy => ⟨hadd _ _ hx.1 hy.1, by
        rw [neg_add]; exact hadd _ _ hx.2 hy.2⟩
      neg_mem' := fun {x} hx => ⟨hx.2, by rw [neg_neg]; exact hx.1⟩ }
  have hall : ∀ x : X, x ∈ S := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range e) := by rw [e.span_eq]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact ⟨groupAlgebra_single_one_mem_of_span R h0 _ (h i).1,
        groupAlgebra_single_one_mem_of_span R h0 _ (h i).2⟩
    | zero => exact S.zero_mem
    | add x y _ _ hx hy => exact S.add_mem hx hy
    | smul c x _ hx => exact S.zsmul_mem hx c
  have hs : ∀ (x : X) (a : A), AddMonoidAlgebra.single x a ∈ R := by
    intro x a
    have := R.mul_mem (h0 a) (hall x).1
    rwa [AddMonoidAlgebra.single_mul_single, zero_add, mul_one] at this
  rw [eq_top_iff]
  intro f hf
  clear hf
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => exact R.zero_mem
  | add f g hf hg => exact R.add_mem hf hg
  | single x a => exact hs x a

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumGradedOfMulDegree
section
open scoped BigOperators

namespace GlobalTheory

theorem hasSum_conv_of_ultrametric {C : Type} [NormedField C] [IsUltrametricDist C]
    {X : Type} [AddCommGroup X] {a a' a'' : X → C} {S S' : C}
    (h : HasSum a S) (h' : HasSum a' S')
    (hc : ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) : HasSum a'' (S * S') := by
  have : NonarchimedeanRing C := ⟨fun U hU => NonarchimedeanAddGroup.is_nonarchimedean U hU⟩
  have hp : HasSum (fun i : X × X => a i.1 * a' i.2) (S * S') := h.mul_of_nonarchimedean h'
  let e : X × X ≃ X × X :=
    { toFun := fun p => (p.2, p.1 - p.2)
      invFun := fun q => (q.1 + q.2, q.1)
      left_inv := by rintro ⟨x, y⟩; simp
      right_inv := by rintro ⟨x, y⟩; simp }
  have hq : HasSum (fun p : X × X => a p.2 * a' (p.1 - p.2)) (S * S') := e.hasSum_iff.2 hp
  exact hq.prod_fiberwise hc

theorem hasSum_graded_of_mul_degree :
    ∀ (C : Type) [NormedField C] [IsUltrametricDist C] [CompleteSpace C] (X : Type) [AddCommGroup X] (Rel : ℕ → (X → C) → C → Prop) (n k : ℕ), 1 ≤ n → 1 ≤ k → (∀ (l l' : ℕ) (a a' : X → C) (c c' : C), 1 ≤ l → 1 ≤ l' → Rel l a c → Rel l' a' c' → ∃ a'', Rel (l + l') a'' (c * c') ∧ ∀ α, HasSum (fun χ => a χ * a' (α - χ)) (a'' α)) → (∃ κ : C, κ ≠ 0 ∧ ∀ a c, Rel (n * k) a c → HasSum a (κ * c)) → ∃ u : C, u ≠ 0 ∧ ∀ a c, Rel k a c → Summable a → HasSum a (u * c) := by
  intro C _ _ _ X _ Rel n k hn hk hmul hkap
  obtain ⟨κ, hκ, hkap⟩ := hkap
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩

  have key : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T →
      ∀ j : ℕ, ∃ e, Rel ((j + 1) * k) e (c ^ j * d) ∧ HasSum e (S ^ j * T) := by
    intro a c S hac hS b d T hbd hT j
    induction j with
    | zero => exact ⟨b, by simpa using hbd, by simpa using hT⟩
    | succ j ih =>
      obtain ⟨e, he, heT⟩ := ih
      have hjk : 1 ≤ (j + 1) * k := le_trans hk (Nat.le_mul_of_pos_left k (Nat.succ_pos j))
      obtain ⟨e', he', hconv⟩ := hmul ((j + 1) * k) k e a (c ^ j * d) c hjk hk he hac
      refine ⟨e', ?_, ?_⟩
      · have h2 : (j + 1) * k + k = (j + 1 + 1) * k := by ring
        have h3 : c ^ j * d * c = c ^ (j + 1) * d := by ring
        rw [h2, h3] at he'
        exact he'
      · have h4 := hasSum_conv_of_ultrametric heT hS hconv
        have h5 : S ^ j * T * S = S ^ (j + 1) * T := by ring
        rw [h5] at h4
        exact h4
  have eqn : ∀ a c S, Rel k a c → HasSum a S → ∀ b d T, Rel k b d → HasSum b T →
      S ^ m * T = κ * (c ^ m * d) := by
    intro a c S hac hS b d T hbd hT
    obtain ⟨e, he, heT⟩ := key a c S hac hS b d T hbd hT m
    exact heT.unique (hkap e _ he)
  by_cases hex : ∃ a c, Rel k a c ∧ Summable a ∧ c ≠ 0
  · obtain ⟨a, c, hac, hsa, hc0⟩ := hex
    set S := ∑' x, a x with hSdef
    have h0 := eqn a c S hac hsa.hasSum a c S hac hsa.hasSum
    have hSn : S ^ (m + 1) = κ * c ^ (m + 1) := by linear_combination h0
    have hS0 : S ≠ 0 := by
      intro hz
      rw [hz, zero_pow (Nat.succ_ne_zero m)] at hSn
      exact (mul_ne_zero hκ (pow_ne_zero _ hc0)) hSn.symm
    refine ⟨S / c, div_ne_zero hS0 hc0, ?_⟩
    intro b d hbd hsb
    have h1 := eqn a c S hac hsa.hasSum b d (∑' x, b x) hbd hsb.hasSum
    have hT : ∑' x, b x = S / c * d := by
      rw [div_mul_eq_mul_div, eq_div_iff hc0]
      apply mul_left_cancel₀ (pow_ne_zero m hS0)
      linear_combination c * h1 - d * hSn
    rw [← hT]
    exact hsb.hasSum
  · push Not at hex
    refine ⟨1, one_ne_zero, ?_⟩
    intro b d hbd hsb
    have hd := hex b d hbd hsb
    subst hd
    have h1 := eqn b 0 _ hbd hsb.hasSum b 0 _ hbd hsb.hasSum
    have hpow : (∑' x, b x) ^ (m + 1) = 0 := by
      rw [pow_succ, h1]
      simp
    have hT : ∑' x, b x = 0 := pow_eq_zero_iff (Nat.succ_ne_zero m) |>.1 hpow
    rw [one_mul, ← hT]
    exact hsb.hasSum

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HasSumMapPowerSeriesMkFinsum
section
open Module

namespace GlobalTheory

theorem hasSum_map_powerSeries_mk_finsum : ∀ (O K Z : Type) [CommRing O] [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K] (φ : PowerSeries O →+* K), (∀ f, ‖φ f‖ ≤ 1) → ‖φ PowerSeries.X‖ < 1 → ∀ (deg : Z → ℕ), (∀ n, {z | deg z = n}.Finite) → ∀ a : Z → O, HasSum (fun z => φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) (φ (PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z)) := by
  intro O K Z _ _ _ _ φ h1 hX deg hfin a
  classical
  set F : PowerSeries O := PowerSeries.mk fun n => ∑ᶠ (z : Z) (_ : deg z = n), a z with hF
  have key : ∀ (n : ℕ) (s : Finset Z), (∀ z, deg z < n → z ∈ s) →
      ‖(∑ z ∈ s, φ (PowerSeries.C (a z)) * φ PowerSeries.X ^ deg z) - φ F‖
        ≤ ‖φ PowerSeries.X‖ ^ n := by
    intro n s hs
    have hdvd : (PowerSeries.X : PowerSeries O) ^ n ∣
        (∑ z ∈ s, PowerSeries.C (a z) * PowerSeries.X ^ deg z) - F := by
      rw [PowerSeries.X_pow_dvd_iff]
      intro m hm
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, map_sum, hF, PowerSeries.coeff_mk, sub_eq_zero]
      have : (∑ᶠ (z : Z) (_ : deg z = m), a z) = ∑ z ∈ s.filter (fun z => deg z = m), a z := by
        rw [← finsum_mem_coe_finset]
        refine finsum_congr fun z => ?_
        refine finsum_congr_Prop ?_ (fun _ => rfl)
        apply propext
        simp only [Finset.coe_filter, Set.mem_setOf_eq]
        exact ⟨fun h => ⟨hs z (h ▸ hm), h⟩, fun h => h.2⟩
      rw [this, Finset.sum_filter]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow]
      by_cases h : deg z = m
      · simp [h]
      · simp [h, Ne.symm h]
    obtain ⟨g, hg⟩ := hdvd
    have h2 := congrArg φ hg
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sub, map_sum, map_mul, map_pow] at h2
    rw [h2, norm_mul, norm_pow]
    exact mul_le_of_le_one_right (by positivity) (h1 g)
  rw [HasSum, Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hε hX
  have hfn : {z | deg z < n}.Finite := by
    refine ((Set.finite_Iio n).biUnion (fun m _ => hfin m)).subset ?_
    intro z hz
    simp only [Set.mem_iUnion, Set.mem_setOf_eq, Set.mem_Iio]
    exact ⟨deg z, hz, rfl⟩
  simp only [SummationFilter.unconditional_filter]
  filter_upwards [Filter.eventually_ge_atTop hfn.toFinset] with s hs
  rw [dist_eq_norm]
  exact (key n s fun z hz => hs (hfn.mem_toFinset.2 hz)).trans_lt hn

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Imports
section
namespace GlobalTheory.FiniteFieldCountEstimate

theorem main (R : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] (π : R)
    (hπ : Irreducible π) (B : Type) [CommRing B] [Algebra R B] [Algebra.FiniteType R B]
    [Module.Flat R B] (I : Ideal B) :
    ∃ (B' : Type) (_ : CommRing B') (_ : Algebra R B') (φ : B →ₐ[R] B'),
      Algebra.FiniteType R B' ∧ Module.Flat R B' ∧ Function.Injective φ ∧
      (∀ b' : B', ∃ (n : ℕ) (b : B), algebraMap R B' π ^ n * b' = φ b) ∧
      (∀ x : B', algebraMap R B' π * x = 0 → x = 0) ∧
      (∀ g ∈ I, ∃ b' : B', algebraMap R B' π * b' = φ g) ∧
      ∀ Q : B' → Prop, (∀ b, Q (φ b)) →
        (∀ g ∈ I, ∀ b' : B', algebraMap R B' π * b' = φ g → Q b') →
        (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x := by
  classical

  let K := FractionRing R
  let L := TensorProduct R B K
  let f : B →ₐ[R] L := Algebra.TensorProduct.includeLeft
  let iR : K →ₐ[R] L := Algebra.TensorProduct.includeRight
  have hf : Function.Injective f :=
    Algebra.TensorProduct.includeLeft_injective (S := R) (IsFractionRing.injective R K)
  have hfa : ∀ b, algebraMap B L b = f b := fun b => rfl
  have hK : algebraMap R K π ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hπ.ne_zero
  let u : L := iR (algebraMap R K π)⁻¹
  have hcu : algebraMap R L π * u = 1 := by
    rw [← iR.commutes π, ← map_mul, mul_inv_cancel₀ hK, map_one]

  have htfL : Module.IsTorsionFree R L := by
    refine Module.IsTorsionFree.of_smul_eq_zero fun r x hrx => ?_
    by_cases hr : r = 0
    · exact Or.inl hr
    right
    have hrK : algebraMap R K r ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hr
    calc x = iR ((algebraMap R K r)⁻¹ * algebraMap R K r) * x := by
          rw [inv_mul_cancel₀ hrK, map_one, one_mul]
      _ = iR (algebraMap R K r)⁻¹ * (r • x) := by
          rw [map_mul, iR.commutes, Algebra.smul_def, mul_assoc]
      _ = 0 := by rw [hrx, mul_zero]

  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing R B
  obtain ⟨k, gs, hgs⟩ := Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian I)
  let t : Fin k → L := fun i => u * f (gs i)
  have hπt : ∀ i, algebraMap R L π * t i = f (gs i) := fun i => by
    simp only [t]
    rw [← mul_assoc, hcu, one_mul]

  let A : MvPolynomial (Fin k) B →ₐ[R] L := (MvPolynomial.aeval t).restrictScalars R
  let S : Subalgebra R L := A.range
  have hAC : ∀ b, A (MvPolynomial.C b) = f b := fun b => by simp [A, hfa]
  have hAX : ∀ i, A (MvPolynomial.X i) = t i := fun i => by simp [A]
  have hmemf : ∀ b, f b ∈ S := fun b => ⟨MvPolynomial.C b, hAC b⟩
  let φ : B →ₐ[R] S := f.codRestrict S hmemf
  have htfS : Module.IsTorsionFree R S :=
    Function.Injective.moduleIsTorsionFree (fun x : S => (x : L)) Subtype.val_injective (fun r x => rfl)
  have hind : ∀ Q : S → Prop, (∀ b, Q (φ b)) →
      (∀ g ∈ I, ∀ b' : S, algebraMap R S π * b' = φ g → Q b') →
      (∀ x y, Q x → Q y → Q (x + y)) → (∀ x y, Q x → Q y → Q (x * y)) → ∀ x, Q x := by
    intro Q hB hI hadd hmul x
    have key : ∀ P, Q ⟨A P, P, rfl⟩ := by
      intro P
      induction P using MvPolynomial.induction_on with
      | C b =>
        have e : (⟨A (MvPolynomial.C b), _, rfl⟩ : S) = φ b := Subtype.ext (hAC b)
        rw [e]
        exact hB b
      | add p q hp hq =>
        have e : (⟨A (p + q), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ + ⟨A q, q, rfl⟩ := Subtype.ext (map_add A p q)
        rw [e]
        exact hadd _ _ hp hq
      | mul_X p i hp =>
        have e : (⟨A (p * MvPolynomial.X i), _, rfl⟩ : S) = ⟨A p, p, rfl⟩ * ⟨A (MvPolynomial.X i), _, rfl⟩ :=
          Subtype.ext (map_mul A _ _)
        rw [e]
        refine hmul _ _ hp (hI (gs i) (by rw [← hgs]; exact Submodule.subset_span ⟨i, rfl⟩) _ ?_)
        apply Subtype.ext
        show algebraMap R L π * A (MvPolynomial.X i) = f (gs i)
        rw [hAX]
        exact hπt i
    obtain ⟨P, hP⟩ := x.prop
    have e : x = ⟨A P, P, rfl⟩ := Subtype.ext hP.symm
    rw [e]
    exact key P
  refine ⟨↥S, inferInstance, inferInstance, φ, ?_, ?_, ?_, ?_, ?_, ?_, hind⟩
  · have : Algebra.FiniteType R (MvPolynomial (Fin k) B) :=
      Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType R B) inferInstance
    exact Algebra.FiniteType.of_surjective A.rangeRestrict A.rangeRestrict_surjective
  · infer_instance
  · intro a b h
    exact hf (congrArg Subtype.val h)
  · intro b'
    refine hind (fun b' => ∃ n b, algebraMap R S π ^ n * b' = φ b) (fun b => ⟨0, b, by simp⟩)
      (fun g _ b' h => ⟨1, g, by simpa using h⟩) ?_ ?_ b'
    · rintro x y ⟨n, b, hb⟩ ⟨m, c, hc⟩
      refine ⟨n + m, algebraMap R B π ^ m * b + algebraMap R B π ^ n * c, ?_⟩
      rw [map_add (f := _), map_mul, map_mul, map_pow, map_pow, AlgHom.commutes, ← hb, ← hc]
      ring
    · rintro x y ⟨n, b, hb⟩ ⟨m, c, hc⟩
      refine ⟨n + m, b * c, ?_⟩
      rw [map_mul, ← hb, ← hc]
      ring
  · intro x hx
    exact (Module.isTorsionFree_iff_smul_eq_zero.mp htfS π x (by rw [Algebra.smul_def]; exact hx)).resolve_left
      hπ.ne_zero
  · intro g hg
    rw [← hgs] at hg
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun B).mp hg
    refine ⟨⟨A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i), _, rfl⟩, Subtype.ext ?_⟩
    show algebraMap R L π * A (∑ i, MvPolynomial.C (c i) * MvPolynomial.X i) = f g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hc, map_sum, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, hAC, hAX, smul_eq_mul, map_mul, ← hπt i]
    ring

end GlobalTheory.FiniteFieldCountEstimate
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.InfinitePowCharEqOneOfAdditiveFamily
section
namespace GlobalTheory

theorem exists_forall_eval_add_ne_zero {k : Type} [Field k] [Infinite k] {Q : Polynomial k}
    (hQ : Q ≠ 0) (S : Finset k) : ∃ β : k, ∀ c ∈ S, Q.eval (c + β) ≠ 0 := by
  classical
  obtain ⟨β, hβ⟩ := Infinite.exists_notMem_finset
    ((S ×ˢ Q.roots.toFinset).image (fun x : k × k => x.2 - x.1))
  refine ⟨β, fun c hc h => hβ ?_⟩
  refine Finset.mem_image.2 ⟨(c, c + β), ?_, by simp⟩
  simp [hc, hQ, h]

theorem infinite_pow_char_eq_one_of_additive_family :
    ∀ (k : Type) [Field k] [Infinite k] (p : ℕ) [CharP k p] (M : Type) [Group M] (A : Type)
      [CommRing A] [Algebra k A] (r : ℕ) (f : Fin r → A) (ε : A →ₐ[k] k)
      (em : (A →ₐ[k] k) → M) (Pd : Polynomial k) (P : Fin r → Polynomial k)
      (ψ : k → (A →ₐ[k] k)), Algebra.adjoin k (Set.range f) = ⊤ → (∀ i, ε (f i) = 0) →
      Function.Injective em → em ε = 1 → Pd ≠ 0 → (∃ i, P i ≠ 0) →
      (∀ t, Pd.eval t ≠ 0 → ∀ i, ψ t (f i) * Pd.eval t = (P i).eval t) →
      (∀ t t', Pd.eval t ≠ 0 → Pd.eval t' ≠ 0 → Pd.eval (t + t') ≠ 0 →
        em (ψ t) * em (ψ t') = em (ψ (t + t'))) → Infinite {x : M // x ^ p = 1} := by
  intro k _ _ p _ M _ A _ _ r f ε em Pd P ψ hgen hε hinj hem hPd hP hval hadd
  classical
  have hpow : ∀ α, Pd.eval α ≠ 0 → em (ψ α) ^ p = 1 := by
    intro α hα
    obtain ⟨β, hβ⟩ := exists_forall_eval_add_ne_zero hPd
      ((Finset.range (p + 1)).image (fun n : ℕ => (n : k) * α))
    have hβ' : ∀ n : ℕ, n ≤ p → Pd.eval ((n : k) * α + β) ≠ 0 := fun n hn =>
      hβ _ (Finset.mem_image.2 ⟨n, Finset.mem_range.2 (by omega), rfl⟩)
    have key : ∀ n : ℕ, n ≤ p → em (ψ α) ^ n * em (ψ β) = em (ψ ((n : k) * α + β)) := by
      intro n
      induction n with
      | zero => intro _; simp
      | succ n ih =>
        intro hn
        have e : ((n + 1 : ℕ) : k) * α + β = α + ((n : k) * α + β) := by push_cast; ring
        have h1 := hβ' (n + 1) hn
        rw [e] at h1
        rw [pow_succ', mul_assoc, ih (by omega), hadd _ _ hα (hβ' n (by omega)) h1, e]
    have h := key p le_rfl
    rw [CharP.cast_eq_zero, zero_mul, zero_add] at h
    exact mul_eq_right.1 h
  by_contra hfin
  rw [not_infinite_iff_finite] at hfin
  have hU : Set.Infinite {t : k | Pd.eval t ≠ 0} := by
    have : {t : k | Pd.eval t ≠ 0} = {t : k | Pd.IsRoot t}ᶜ := by
      ext t; simp
    rw [this]
    exact (Polynomial.finite_setOf_isRoot hPd).infinite_compl
  haveI : Infinite {t : k | Pd.eval t ≠ 0} := hU.to_subtype
  let g : {t : k | Pd.eval t ≠ 0} → {x : M // x ^ p = 1} := fun t => ⟨em (ψ t.1), hpow t.1 t.2⟩
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  obtain ⟨⟨t₀, ht₀⟩⟩ : Nonempty (g ⁻¹' {y}) := inferInstance
  have hy' : (g ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  have hy'' : (Subtype.val '' (g ⁻¹' {y})).Infinite :=
    hy'.image Subtype.val_injective.injOn
  set χ := ψ t₀.1 with hχ
  have hpoly : ∀ i, P i = Polynomial.C (χ (f i)) * Pd := by
    intro i
    apply Polynomial.eq_of_infinite_eval_eq
    refine hy''.mono ?_
    rintro _ ⟨t, ht, rfl⟩
    have h1 : g t = g t₀ := by
      rw [Set.mem_preimage, Set.mem_singleton_iff] at ht ht₀
      rw [ht, ht₀]
    have h2 : ψ t.1 = χ := hinj (congrArg Subtype.val h1)
    have h3 := hval t.1 t.2 i
    simp only [Set.mem_setOf_eq, Polynomial.eval_mul, Polynomial.eval_C]
    rw [← h3, h2]
  have hconst : ∀ t, Pd.eval t ≠ 0 → ψ t = χ := by
    intro t ht
    apply AlgHom.ext_of_adjoin_eq_top hgen
    rintro _ ⟨i, rfl⟩
    have h3 := hval t ht i
    rw [hpoly i, Polynomial.eval_mul, Polynomial.eval_C] at h3
    exact mul_right_cancel₀ ht h3
  obtain ⟨β, hβ⟩ := exists_forall_eval_add_ne_zero hPd {0, t₀.1}
  have hb0 : Pd.eval β ≠ 0 := by simpa using hβ 0 (by simp)
  have hb1 : Pd.eval (t₀.1 + β) ≠ 0 := hβ _ (by simp)
  have h4 := hadd _ _ t₀.2 hb0 hb1
  rw [hconst _ hb0, hconst _ hb1, ← hχ] at h4
  have h5 : χ = ε := hinj (by rw [hem]; exact mul_eq_right.1 h4)
  obtain ⟨i, hi⟩ := hP
  apply hi
  rw [hpoly i, h5, hε i]
  simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.PowerSeriesGenericRelationChain
section
namespace GlobalTheory

theorem powerSeries_generic_relation_chain :
    ∀ (k : Type) [Field k] [Infinite k] (ρ : PowerSeries k → PowerSeries k → Prop) (Gen : ℕ → ℕ → Prop), (∀ z w, ρ z w → ρ w z) → (∀ x y z, ρ x y → ρ y z → ρ x z) → (∀ m n, Gen m n → ∀ z : PowerSeries k, z.order = (m : ℕ∞) → ∃ S : Set k, S.Finite ∧ ∀ t, t ∉ S → ρ z (PowerSeries.C t * PowerSeries.X ^ n)) → (∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) → w.order = (m : ℕ∞) → ρ z w) ∧ ∀ m₀, (∀ m, m₀ ≤ m → Gen m (m + 1)) → ∀ (m n : ℕ) (z w : PowerSeries k), m₀ ≤ m → m₀ ≤ n → z.order = (m : ℕ∞) → w.order = (n : ℕ∞) → ρ z w := by
  intro k _ _ ρ Gen hs ht hg
  have h1 : ∀ m n, Gen m n → ∀ z w : PowerSeries k, z.order = (m : ℕ∞) →
      w.order = (m : ℕ∞) → ρ z w := by
    intro m n hmn z w hz hw
    obtain ⟨S, hS, hzS⟩ := hg m n hmn z hz
    obtain ⟨T, hT, hwT⟩ := hg m n hmn w hw
    obtain ⟨t, htt⟩ := (hS.union hT).exists_notMem
    simp only [Set.mem_union, not_or] at htt
    exact ht _ _ _ (hzS t htt.1) (hs _ _ (hwT t htt.2))
  refine ⟨h1, fun m₀ hG => ?_⟩
  have h2 : ∀ m, m₀ ≤ m → ∀ z : PowerSeries k, z.order = (m : ℕ∞) →
      ρ z (PowerSeries.X ^ m₀) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base => exact fun z hz => h1 _ _ (hG _ le_rfl) _ _ hz (PowerSeries.order_X_pow _)
    | succ m hm ih =>
      intro z hz
      obtain ⟨S, hS, hXS⟩ := hg m _ (hG m hm) (PowerSeries.X ^ m) (PowerSeries.order_X_pow _)
      obtain ⟨t, htt⟩ := (hS.insert 0).exists_notMem
      simp only [Set.mem_insert_iff, not_or] at htt
      have ho : (PowerSeries.C t * PowerSeries.X ^ (m + 1) : PowerSeries k).order
          = ((m + 1 : ℕ) : ℕ∞) := by
        rw [PowerSeries.X_pow_eq, ← PowerSeries.monomial_zero_eq_C_apply,
          PowerSeries.monomial_mul_monomial, zero_add, mul_one]
        exact PowerSeries.order_monomial_of_ne_zero _ _ htt.1
      exact ht _ _ _ (h1 _ _ (hG _ (Nat.le_succ_of_le hm)) _ _ hz ho)
        (ht _ _ _ (hs _ _ (hXS t htt.2)) (ih _ (PowerSeries.order_X_pow _)))
  intro m n z w hm hn hz hw
  exact ht _ _ _ (h2 m hm z hz) (hs _ _ (h2 n hn w hw))

end GlobalTheory
end

