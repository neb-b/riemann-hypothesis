module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0029

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtalePolynomialModelOfDirectedUnion
section
open IsLocalRing Polynomial

namespace GlobalTheory.EtaleDescent

open TensorProduct

theorem exists_etale_polynomial_model_of_directed_union :
    ∀ (T : Type) [CommRing T] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
    (𝒜 : ι → Subring T), Monotone 𝒜 → (∀ x : T, ∃ i, x ∈ 𝒜 i) →
    ∀ (E : Type) [CommRing E] [Algebra (Polynomial T) E] [Algebra.Etale (Polynomial T) E],
    ∃ (i : ι) (E₀ : Type) (_ : CommRing E₀) (_ : Algebra (Polynomial (𝒜 i)) E₀),
      Algebra.Etale (Polynomial (𝒜 i)) E₀ ∧
      (letI : Algebra (Polynomial (𝒜 i)) (Polynomial T) :=
        (Polynomial.mapRingHom (𝒜 i).subtype).toAlgebra
       Nonempty (TensorProduct (Polynomial (𝒜 i)) (Polynomial T) E₀ ≃ₐ[Polynomial T] E)) := by
  intro T _ ι _ _ _ 𝒜 hmono hcov E _ _ _
  let S : ι → Subring (Polynomial T) := fun i ↦ (Polynomial.mapRingHom (𝒜 i).subtype).range
  have hSmono : Monotone S := by
    intro i j hij p hp
    obtain ⟨q, rfl⟩ := RingHom.mem_range.mp hp
    refine RingHom.mem_range.mpr ⟨q.map (Subring.inclusion (hmono hij)), ?_⟩
    simp only [coe_mapRingHom, Polynomial.map_map]
    rfl
  have hScov : ∀ p, ∃ i, p ∈ S i := by
    classical
    intro p
    choose j hj using hcov
    obtain ⟨i, hi⟩ := Finset.exists_le (p.support.image (fun n ↦ j (p.coeff n)))
    refine ⟨i, ?_⟩
    have : p ∈ Polynomial.lifts (𝒜 i).subtype := by
      rw [Polynomial.lifts_iff_coeff_lifts]
      intro n
      by_cases hn : n ∈ p.support
      · exact ⟨⟨p.coeff n, hmono (hi _ (Finset.mem_image_of_mem _ hn)) (hj _)⟩, rfl⟩
      · rw [Polynomial.notMem_support_iff.mp hn]
        exact ⟨0, map_zero _⟩
    obtain ⟨q, hq⟩ := this
    exact RingHom.mem_range.mpr ⟨q, hq⟩
  obtain ⟨i, E₀, _, _, hE₀, ⟨φ⟩⟩ :=
    exists_etale_model_of_directed_union (Polynomial T) ι S hSmono hScov E
  let f : Polynomial (𝒜 i) →+* Polynomial T := Polynomial.mapRingHom (𝒜 i).subtype
  have hf : Function.Injective f := Polynomial.map_injective _ Subtype.val_injective
  let e : Polynomial (𝒜 i) ≃+* S i := RingEquiv.ofBijective f.rangeRestrict
    ⟨fun a b h ↦ hf (congrArg Subtype.val h), f.rangeRestrict_surjective⟩
  have he : ∀ p, ((e p : S i) : Polynomial T) = f p := fun _ ↦ rfl
  letI alg₀ : Algebra (Polynomial (𝒜 i)) E₀ := ((algebraMap (S i) E₀).comp e.toRingHom).toAlgebra
  letI algT : Algebra (Polynomial (𝒜 i)) (Polynomial T) := f.toAlgebra
  have hEt : Algebra.Etale (Polynomial (𝒜 i)) E₀ := by
    rw [← RingHom.etale_algebraMap]
    exact RingHom.Etale.respectsIso.2 (algebraMap (S i) E₀) e
      (RingHom.etale_algebraMap.mpr hE₀)
  have hmapT : ∀ p, algebraMap (S i) (Polynomial T) (e p) = algebraMap (Polynomial (𝒜 i)) (Polynomial T) p :=
    fun _ ↦ rfl
  have hmapE : ∀ p, algebraMap (S i) E₀ (e p) = algebraMap (Polynomial (𝒜 i)) E₀ p := fun _ ↦ rfl
  haveI c1 : SMulCommClass (S i) (Polynomial (𝒜 i)) (Polynomial T) :=
    ⟨fun a b x ↦ by simp only [Algebra.smul_def]; ring⟩
  haveI c2 : TensorProduct.CompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T) E₀ :=
    ⟨fun p m n ↦ by
      rw [Algebra.smul_def, Algebra.smul_def, ← hmapT, ← hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  haveI c3 : TensorProduct.CompatibleSMul (Polynomial (𝒜 i)) (S i) (Polynomial T) E₀ :=
    ⟨fun s m n ↦ by
      obtain ⟨p, rfl⟩ := e.surjective s
      rw [Algebra.smul_def, Algebra.smul_def, hmapT, hmapE, ← Algebra.smul_def, ← Algebra.smul_def,
        TensorProduct.smul_tmul]⟩
  refine ⟨i, E₀, inferInstance, alg₀, hEt, ⟨?_⟩⟩
  exact (Algebra.TensorProduct.equivOfCompatibleSMul (S i) (Polynomial (𝒜 i)) (Polynomial T)
    (Polynomial T) E₀).trans φ

end GlobalTheory.EtaleDescent
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEvaluationExtensionClosureRepresentatives
section
open MeasureTheory Filter Topology
open scoped ContDiff

namespace GlobalTheory.LocRep


open MeasureTheory Filter Topology in
open scoped ContDiff in
theorem _root_.GlobalTheory.LocRep.exists_eval_closure (G : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (μ : Measure G) [μ.IsHaarMeasure] (K : Type) [NormedAddCommGroup K] [InnerProductSpace ℂ K]
    [CompleteSpace K] (ι : K → G → ℂ)
    (hloc : ∀ C, IsCompact C → ∃ M : ℝ, ∀ v, IntegrableOn (ι v) C μ ∧ ∫ x in C, ‖ι v x‖ ∂μ ≤ M * ‖v‖)
    (hlin : ∀ (a : ℂ) v w, ι (a • v + w) =ᵐ[μ] fun x => a * ι v x + ι w x)
    (A : K →L[ℂ] K) (E : Submodule ℂ K)
    (hE : ∀ v ∈ E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A v) =ᵐ[μ] φ)
    (hB : ∀ B, IsCompact B → ∃ C : ℝ, ∀ v ∈ E, ∀ φ : G → ℂ, Continuous φ → ι (A v) =ᵐ[μ] φ →
      ∀ x ∈ B, ‖φ x‖ ≤ C * ‖v‖) :
    ∃ Λ : G → (K →L[ℂ] ℂ), ∀ v ∈ closure (E : Set K),
      (Continuous fun x => Λ x v) ∧ ι (A v) =ᵐ[μ] fun x => Λ x v := by
  have hE' : ∀ w : E, ∃ φ : G → ℂ, Continuous φ ∧ ι (A w) =ᵐ[μ] φ := fun w => hE w w.2
  choose ψ hψc hψae using hE'
  have hadd : ∀ w w' : E, ψ (w + w') = fun x => ψ w x + ψ w' x := fun w w' =>
    (Continuous.ae_eq_iff_eq μ (hψc _) ((hψc w).add (hψc w'))).1 (by
      filter_upwards [hψae (w + w'), _root_.GlobalTheory.LocRep.rep_add hlin (A w) (A w'), hψae w, hψae w']
        with x h0 h1 h2 h3
      show ψ (w + w') x = ψ w x + ψ w' x
      rw [← h0, ← h2, ← h3, ← h1]
      simp)
  have hsmul : ∀ (a : ℂ) (w : E), ψ (a • w) = fun x => a * ψ w x := fun a w =>
    (Continuous.ae_eq_iff_eq μ (hψc _) (continuous_const.mul (hψc w))).1 (by
      filter_upwards [hψae (a • w), _root_.GlobalTheory.LocRep.rep_smul hlin a (A w), hψae w] with x h0 h1 h2
      show ψ (a • w) x = a * ψ w x
      rw [← h0, ← h2, ← h1]
      simp)
  let L : G → E →L[ℂ] ℂ := fun x => LinearMap.mkContinuousOfExistsBound
    { toFun := fun w => ψ w x
      map_add' := fun w w' => congrFun (hadd w w') x
      map_smul' := fun a w => by simpa using congrFun (hsmul a w) x } (by
      obtain ⟨c, hc⟩ := hB {x} isCompact_singleton
      exact ⟨c, fun w => hc w w.2 _ (hψc w) (hψae w) x rfl⟩)
  have hext : ∀ x, ∃ g : K →L[ℂ] ℂ, (∀ w : E, g w = L x w) ∧ ‖g‖ = ‖L x‖ :=
    fun x => exists_extension_norm_eq E (L x)
  choose Λ hΛext hΛnorm using hext
  have hbound : ∀ B, IsCompact B → ∃ c : ℝ, 0 ≤ c ∧ ∀ x ∈ B, ‖Λ x‖ ≤ c := by
    intro B hBc
    obtain ⟨c, hc⟩ := hB B hBc
    refine ⟨max c 0, le_max_right _ _, fun x hx => ?_⟩
    rw [hΛnorm]
    refine ContinuousLinearMap.opNorm_le_bound _ (le_max_right _ _) fun w => ?_
    exact (hc w w.2 _ (hψc w) (hψae w) x hx).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  refine ⟨Λ, fun v hv => ?_⟩
  obtain ⟨u, hun, hu⟩ := mem_closure_iff_seq_limit.1 hv
  have hcont : ∀ n, Continuous fun x => Λ x (u n) := fun n => by
    have h : (fun x => Λ x (u n)) = ψ ⟨u n, hun n⟩ := funext fun x => hΛext x ⟨u n, hun n⟩
    rw [h]
    exact hψc _
  have hunif : ∀ B, IsCompact B →
      TendstoUniformlyOn (fun n x => Λ x (u n)) (fun x => Λ x v) atTop B := by
    intro B hBc
    obtain ⟨c, hc0, hc⟩ := hbound B hBc
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hu' := (Metric.tendsto_nhds.1 hu) (ε / (c + 1)) (by positivity)
    filter_upwards [hu'] with n hn x hx
    rw [dist_eq_norm, ← map_sub]
    calc ‖Λ x (v - u n)‖ ≤ ‖Λ x‖ * ‖v - u n‖ := (Λ x).le_opNorm _
      _ ≤ c * (ε / (c + 1)) := by
          refine mul_le_mul (hc x hx) ?_ (norm_nonneg _) hc0
          rw [← dist_eq_norm, dist_comm]
          exact hn.le
      _ < ε := by
          rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
          nlinarith
  have hcontv : Continuous fun x => Λ x v :=
    (tendstoLocallyUniformly_iff_forall_isCompact.2 hunif).continuous
      (Eventually.of_forall hcont).frequently
  have hint : ∀ C, IsCompact C → ∫ x in C, ι (A v) x ∂μ = ∫ x in C, Λ x v ∂μ := by
    intro C hC
    obtain ⟨Pr, hPr⟩ := _root_.GlobalTheory.LocRep.exists_pairing hloc hlin hC
    obtain ⟨c, hc0, hc⟩ := hbound C hC
    have h1 : Tendsto (fun n => Pr (A (u n))) atTop (𝓝 (Pr (A v))) :=
      ((Pr.continuous.comp A.continuous).tendsto v).comp hu
    have h2 : ∀ n, Pr (A (u n)) = ∫ x in C, Λ x (u n) ∂μ := fun n => by
      rw [hPr]
      refine integral_congr_ae (ae_restrict_of_ae ?_)
      filter_upwards [hψae ⟨u n, hun n⟩] with x hx
      rw [hx]
      exact (hΛext x ⟨u n, hun n⟩).symm
    have h3 : Tendsto (fun n => ∫ x in C, Λ x (u n) ∂μ) atTop (𝓝 (∫ x in C, Λ x v ∂μ)) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (g := fun n => c * ‖u n - v‖ * (μ C).toReal)
        (fun n => ?_) ?_
      · rw [← integral_sub ((hcont n).locallyIntegrable.integrableOn_isCompact hC)
          (hcontv.locallyIntegrable.integrableOn_isCompact hC)]
        refine norm_setIntegral_le_of_norm_le_const hC.measure_lt_top fun x hx => ?_
        rw [← map_sub]
        exact ((Λ x).le_opNorm _).trans (mul_le_mul_of_nonneg_right (hc x hx) (norm_nonneg _))
      · have h4 : Tendsto (fun n => ‖u n - v‖) atTop (𝓝 0) :=
          tendsto_iff_norm_sub_tendsto_zero.1 hu
        simpa using (h4.const_mul c).mul_const (μ C).toReal
    rw [← hPr]
    exact tendsto_nhds_unique (h1.congr h2) h3
  exact ⟨hcontv, _root_.GlobalTheory.LocRep.rep_of_pairing hloc hcontv.locallyIntegrable hint⟩

end GlobalTheory.LocRep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsExcisionNbhdAdjoinRoot
section
open GlobalTheory.EtC Polynomial

namespace GlobalTheory.EtC

theorem exists_excisionNbhd_adjoin_root : ∀ (A : Type) [CommRing A] (h : A) (q : ℕ), IsUnit (q : A) →
    ∀ ε r : A, IsUnit ε → ε - r ^ q ∈ Ideal.span {h} → ∃ (A' : Type) (_ : CommRing A') (_ : Algebra A A'),
      IsExcisionNbhd A A' h ∧ ∃ x : A', algebraMap A A' ε = x ^ q := by
  intro A _ h q hq ε r hε hr
  rcases Nat.eq_zero_or_pos q with hq0 | hq0
  · subst hq0
    have : Subsingleton A := by
      simp only [Nat.cast_zero, isUnit_zero_iff] at hq
      exact subsingleton_of_zero_eq_one hq
    exact ⟨A, inferInstance, inferInstance, isExcisionNbhd_self A h, 1, Subsingleton.elim _ _⟩
  obtain ⟨m, rfl⟩ : ∃ m, q = m + 1 := ⟨q - 1, by omega⟩
  set qi : A := ↑hq.unit⁻¹
  set ei : A := ↑hε.unit⁻¹
  have hq1 : ((m + 1 : ℕ) : A) * qi = 1 := hq.mul_val_inv
  have he1 : ε * ei = 1 := hε.mul_val_inv
  let g : A[X] := ∑ i ∈ Finset.range (m + 1), X ^ i * C r ^ (m + 1 - 1 - i)
  let P : StandardEtalePair A :=
    { f := X ^ (m + 1) - C ε
      monic_f := monic_X_pow_sub_C ε (by omega)
      g := g
      cond := ⟨C (qi * ei) * X, - C ei, 0, by
        have a1 : C ((m + 1 : ℕ) : A) * C qi = 1 := by rw [← C_mul, hq1, C_1]
        have a2 : C ε * C ei = 1 := by rw [← C_mul, he1, C_1]
        simp only [derivative_sub, derivative_X_pow, derivative_C, sub_zero, pow_zero, C_mul,
          Nat.add_sub_cancel]
        linear_combination (X ^ (m + 1) * C ei) * a1 + a2⟩ }
  let I : Ideal A := Ideal.span {h}
  have hmap : P.HasMap (Ideal.Quotient.mk I r) := by
    constructor
    · show aeval _ (X ^ (m + 1) - C ε) = 0
      rw [map_sub, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq, ← map_pow, ← map_sub,
        Ideal.Quotient.eq_zero_iff_mem]
      simpa using I.neg_mem hr
    · show IsUnit (aeval _ g)
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C, Ideal.Quotient.algebraMap_eq]
      rw [geom_sum₂_self]
      refine IsUnit.mul ?_ (IsUnit.pow _ ?_)
      · simpa using hq.map (Ideal.Quotient.mk I)
      · rw [← isUnit_pow_iff (n := m + 1) (by omega), ← map_pow]
        have : Ideal.Quotient.mk I (r ^ (m + 1)) = Ideal.Quotient.mk I ε := by
          rw [Ideal.Quotient.eq]; simpa using I.neg_mem hr
        rw [this]; exact hε.map _
  let φ : P.Ring →ₐ[A] A ⧸ I := P.lift _ hmap
  let J : Ideal P.Ring := Ideal.span {algebraMap A P.Ring h}
  have hgu : IsUnit (aeval P.X g) := P.hasMap_X.2
  have e2 : P.X ^ (m + 1) = algebraMap A P.Ring ε := by
    have : aeval P.X (X ^ (m + 1) - C ε) = 0 := P.hasMap_X.1
    simpa [sub_eq_zero] using this
  have hX : P.X - algebraMap A P.Ring r ∈ J := by
    obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hr
    have key : (P.X - algebraMap A P.Ring r) * aeval P.X g =
        algebraMap A P.Ring c * algebraMap A P.Ring h := by
      have e1 : aeval P.X g * (P.X - algebraMap A P.Ring r) =
          P.X ^ (m + 1) - (algebraMap A P.Ring r) ^ (m + 1) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [g, map_sum, map_mul, map_pow, aeval_X, aeval_C]
        exact geom_sum₂_mul _ _ _
      rw [mul_comm, e1, e2, ← map_pow, ← map_sub, ← hc, map_mul]
    rw [Ideal.mem_span_singleton']
    refine ⟨algebraMap A P.Ring c * ↑hgu.unit⁻¹, ?_⟩
    calc _ = (P.X - algebraMap A P.Ring r) * aeval P.X g * ↑hgu.unit⁻¹ := by rw [key]; ring
      _ = _ := by rw [mul_assoc, hgu.mul_val_inv, mul_one]
  let ψ : A ⧸ I →ₐ[A] P.Ring ⧸ J := Ideal.Quotient.liftₐ I (Algebra.ofId A (P.Ring ⧸ J)) (by
    intro a ha
    obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp ha
    rw [Algebra.ofId_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J),
      Ideal.Quotient.algebraMap_eq, Ideal.Quotient.eq_zero_iff_mem, map_mul]
    exact J.mul_mem_left _ (Ideal.mem_span_singleton_self _))
  have hψ : ∀ a : A, ψ (Ideal.Quotient.mk I a) = Ideal.Quotient.mk J (algebraMap A P.Ring a) := by
    intro a
    first
      | rfl
      | simp [ψ, Ideal.Quotient.liftₐ_apply, IsScalarTower.algebraMap_apply A P.Ring (P.Ring ⧸ J)]
  have hcomp : ψ.comp φ = Ideal.Quotient.mkₐ A J := by
    apply P.hom_ext
    simp only [AlgHom.comp_apply, φ, StandardEtalePair.lift_X, Ideal.Quotient.mkₐ_eq_mk]
    show ψ (Ideal.Quotient.mk I r) = _
    rw [hψ, Ideal.Quotient.eq]
    first
      | exact hX
      | (have := J.neg_mem hX; rwa [neg_sub] at this)
  refine ⟨P.Ring, inferInstance, inferInstance, ⟨inferInstance, ?_, ?_⟩, P.X, e2.symm⟩
  · intro a'
    obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective (φ a')
    refine ⟨a, ?_⟩
    have h1 := congrArg (fun F => F a') hcomp
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk, ← ha] at h1
    rw [hψ] at h1
    exact Ideal.Quotient.eq.mp h1.symm
  · intro a ha
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton'.mp ha
    have h1 := congrArg φ hy
    have hh0 : Ideal.Quotient.mk I h = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self _)
    simp only [map_mul, AlgHom.commutes, Ideal.Quotient.algebraMap_eq] at h1
    rw [hh0, mul_zero] at h1
    exact Ideal.Quotient.eq_zero_iff_mem.mp h1.symm

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteRelIndexStabilizerCommensurableLatti
section
open NumberField ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.LatticeCongr

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

def sqMul (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) : Submodule (𝓞 E) (Fin r → E) :=
  Λ.map ((((n : E) ^ 2) • LinearMap.id : (Fin r → E) →ₗ[E] (Fin r → E)).restrictScalars (𝓞 E))

theorem mem_sqMul {Λ : Submodule (𝓞 E) (Fin r → E)} {n : ℕ} {x : Fin r → E} :
    x ∈ sqMul Λ n ↔ ∃ y ∈ Λ, ((n : E) ^ 2) • y = x := by
  simp [sqMul]

def sqSub (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) : Submodule (𝓞 E) Λ :=
  Submodule.comap Λ.subtype (sqMul Λ n)

def act (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) : Λ →ₗ[𝓞 E] Λ :=
  ((Matrix.mulVecLin (γ : Matrix (Fin r) (Fin r) E)).restrictScalars (𝓞 E)).restrict
    fun x hx => (h x).1 hx

@[simp] theorem act_apply (Λ : Submodule (𝓞 E) (Fin r → E)) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) (x : Λ) :
    ((act Λ γ h x : Λ) : Fin r → E) = (γ : Matrix (Fin r) (Fin r) E).mulVec x := rfl

theorem act_sqSub (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) (γ : GL (Fin r) E)
    (h : ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) :
    sqSub Λ n ≤ (sqSub Λ n).comap (act Λ γ h) := by
  intro x hx
  simp only [sqSub, Submodule.mem_comap, Submodule.subtype_apply, act_apply] at hx ⊢
  obtain ⟨y, hy, hxy⟩ := mem_sqMul.1 hx
  exact mem_sqMul.2 ⟨_, (h y).1 hy, by rw [← hxy, Matrix.mulVec_smul]⟩

def rep (Λ : Submodule (𝓞 E) (Fin r → E)) (n : ℕ) (G : Subgroup (GL (Fin r) E))
    (hG : ∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) :
    G →* Module.End (𝓞 E) (Λ ⧸ sqSub Λ n) where
  toFun g := (sqSub Λ n).mapQ (sqSub Λ n) (act Λ g (hG g g.2)) (act_sqSub Λ n _ _)
  map_one' := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.id_comp]
    congr 1
    ext
    simp
  map_mul' g g' := by
    apply Submodule.linearMap_qext
    ext x
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      Module.End.mul_apply]
    congr 1
    ext
    simp [Matrix.mulVec_mulVec]

end GlobalTheory.LatticeCongr

namespace GlobalTheory.LatticeCongr

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem mulVec_mem_of_rep_eq_one {Λ Λ' : Submodule (𝓞 E) (Fin r → E)} {n : ℕ} (hn : 0 < n)
    (h1 : ∀ v ∈ Λ', (n : E) • v ∈ Λ) (h2 : ∀ v ∈ Λ, (n : E) • v ∈ Λ')
    {G : Subgroup (GL (Fin r) E)}
    (hG : ∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ)
    (g : G) (hg : rep Λ n G hG g = 1) (x : Fin r → E) (hx : x ∈ Λ') :
    ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
  have hu : (Submodule.Quotient.mk (act Λ g (hG g g.2) ⟨(n : E) • x, h1 x hx⟩) : Λ ⧸ sqSub Λ n) =
      Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩ :=
    LinearMap.congr_fun hg (Submodule.Quotient.mk ⟨(n : E) • x, h1 x hx⟩)
  rw [Submodule.Quotient.eq] at hu
  obtain ⟨y, hy, hyx⟩ := mem_sqMul.1 hu
  change ((n : E) ^ 2) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec ((n : E) • x) -
    (n : E) • x at hyx
  rw [Matrix.mulVec_smul] at hyx
  have hn' : (n : E) ≠ 0 := by exact_mod_cast hn.ne'
  have hy' : (n : E) • y = ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x - x := by
    apply smul_right_injective _ hn'
    simp only [smul_smul, smul_sub, ← pow_two]
    exact hyx
  have : ((g : GL (Fin r) E) : Matrix (Fin r) (Fin r) E).mulVec x = x + (n : E) • y := by
    rw [hy']; abel
  rw [this]
  exact Λ'.add_mem hx (h2 y hy)

theorem exists_relIndex_ne_zero_stab : ∀ {E : Type} [Field E] [NumberField E] {r : ℕ} (Λ Λ' : Submodule (𝓞 E) (Fin r → E)) (n : ℕ), 0 < n → Λ.FG → (∀ v ∈ Λ', (n : E) • v ∈ Λ) → (∀ v ∈ Λ, (n : E) • v ∈ Λ') → ∀ G : Subgroup (GL (Fin r) E), (∀ γ ∈ G, ∀ x, x ∈ Λ ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ) → ∃ K : Subgroup (GL (Fin r) E), K.relIndex G ≠ 0 ∧ ∀ γ ∈ K, ∀ x, x ∈ Λ' ↔ (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
  intro E _ _ r Λ Λ' n hn hfg h1 h2 G hG
  haveI : Module.Finite (𝓞 E) Λ := Module.Finite.iff_fg.2 hfg
  haveI : Module.Finite ℤ (Λ ⧸ sqSub Λ n) := Module.Finite.trans (𝓞 E) _
  haveI : Finite (Λ ⧸ sqSub Λ n) := Module.finite_of_fg_torsion _ fun z => by
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ z
    refine ⟨⟨((n : ℤ) ^ 2), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change ((n : ℤ) ^ 2) • (Submodule.mkQ (sqSub Λ n) y) = 0
    rw [← map_zsmul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    show (((((n : ℤ) ^ 2) • y : Λ)) : Fin r → E) ∈ sqMul Λ n
    refine mem_sqMul.2 ⟨y, y.2, ?_⟩
    rw [AddSubgroupClass.coe_zsmul, ← Int.cast_smul_eq_zsmul E]
    push_cast
    rfl
  haveI : Finite (Module.End (𝓞 E) (Λ ⧸ sqSub Λ n)) :=
    Finite.of_injective _ DFunLike.coe_injective
  set φ := (rep Λ n G hG).toHomUnits with hφ
  have key : ∀ γ ∈ φ.ker.map G.subtype, ∀ x ∈ Λ',
      (γ : Matrix (Fin r) (Fin r) E).mulVec x ∈ Λ' := by
    rintro γ ⟨g, hg, rfl⟩ x hx
    refine mulVec_mem_of_rep_eq_one hn h1 h2 hG g ?_ x hx
    have := congrArg Units.val (MonoidHom.mem_ker.1 hg)
    simpa [hφ] using this
  refine ⟨φ.ker.map G.subtype, ?_, ?_⟩
  · show (Subgroup.comap G.subtype (φ.ker.map G.subtype)).index ≠ 0
    rw [Subgroup.comap_map_eq_self_of_injective G.subtype_injective]
    exact Subgroup.FiniteIndex.index_ne_zero
  · intro γ hγ x
    refine ⟨key γ hγ x, fun h => ?_⟩
    have := key γ⁻¹ (inv_mem hγ) _ h
    rwa [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec] at this

end GlobalTheory.LatticeCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinsetMemTensorPowerFirstFactorAdjoinFinse
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC

theorem firstAndFinite_mono (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    {F G : Finset A} (h : F ⊆ G) : firstAndFinite R A k F ≤ firstAndFinite R A k G := by
  unfold firstAndFinite
  apply Algebra.adjoin_mono
  apply Set.union_subset_union_right
  apply Set.iUnion_mono
  intro i
  exact Set.image_mono (by exact_mod_cast h)

theorem tprod_eq_prod_singleAlgHom (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (f : Fin (k + 1) → A) :
    PiTensorProduct.tprod R f = ∏ i, PiTensorProduct.singleAlgHom (R := R) (A := fun _ : Fin (k + 1) => A) i (f i) := by
  classical
  simp only [PiTensorProduct.singleAlgHom_apply]
  have := map_prod (PiTensorProduct.tprodMonoidHom R (A := fun _ : Fin (k + 1) => A))
    (fun u => MonoidHom.mulSingle (fun _ : Fin (k + 1) => A) u (f u)) Finset.univ
  refine Eq.trans ?_ this
  simp only [MonoidHom.mulSingle_apply]
  rw [Finset.univ_prod_mulSingle]
  rfl

theorem exists_finset_mem_firstAndFinite (R A : Type) [CommRing R] [CommRing A] [Algebra R A] (k : ℕ)
    (x : PiTensorProduct R (fun _ : Fin (k + 1) => A)) : ∃ F : Finset A, x ∈ firstAndFinite R A k F := by
  classical
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    refine ⟨Finset.univ.image f, ?_⟩
    refine Subalgebra.smul_mem _ ?_ r
    rw [tprod_eq_prod_singleAlgHom]
    refine Subalgebra.prod_mem _ fun i _ => ?_
    apply Algebra.subset_adjoin
    refine Or.inr (Set.mem_iUnion.2 ⟨i, f i, by simp, rfl⟩)
  | add x y hx hy =>
    obtain ⟨F, hF⟩ := hx
    obtain ⟨G, hG⟩ := hy
    exact ⟨F ∪ G, Subalgebra.add_mem _ (firstAndFinite_mono R A k Finset.subset_union_left hF)
      (firstAndFinite_mono R A k Finset.subset_union_right hG)⟩

end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIdempotentLocalOfCharacterStatement
section
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_idempotent_local_of_character : ∀ (k : Type) [Field k] (A : Type) [CommRing A] [Algebra k A] [FiniteDimensional k A] (φ : A →ₐ[k] k), ∃ e : A, IsIdempotentElem e ∧ φ e = 1 ∧ ∀ a, φ a = 0 → IsNilpotent (e * a) := by
  first | (exact @GlobalTheory.exists_idem_local_of_character) | (exact GlobalTheory.exists_idem_local_of_character) | (intros; apply GlobalTheory.exists_idem_local_of_character <;> assumption)
end

