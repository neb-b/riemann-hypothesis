module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsRestRest
section
namespace ZbYhc5Helpers

private lemma key {g : ℕ} (c : ℂ) (u u' : Fin g → ℂ) :
    c • (u + Complex.I • u') = (c.re • u - c.im • u') + Complex.I • (c.im • u + c.re • u') := by
  funext i
  apply Complex.ext <;> simp [Complex.real_smul] <;> ring

end ZbYhc5Helpers

theorem UpperTheory.Reformulated.B.Yhc5.main :
    ∀ {g : ℕ} {T : Set (Fin g → ℂ)} {w : Fin g → ℂ},
      w ∈ Submodule.span ℂ T → ∃ u ∈ Submodule.span ℝ T, ∃ u' ∈ Submodule.span ℝ T, w = u + Complex.I • u' := by
  intro g T w hw
  induction hw using Submodule.span_induction with
  | mem x hx => exact ⟨x, Submodule.subset_span hx, 0, Submodule.zero_mem _, by simp⟩
  | zero => exact ⟨0, Submodule.zero_mem _, 0, Submodule.zero_mem _, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    obtain ⟨b, hb, b', hb', rfl⟩ := hy
    exact ⟨a + b, Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', by
      rw [smul_add]; abel⟩
  | smul c x _ hx =>
    obtain ⟨a, ha, a', ha', rfl⟩ := hx
    refine ⟨c.re • a - c.im • a', ?_, c.im • a + c.re • a', ?_, ZbYhc5Helpers.key c a a'⟩
    · exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
    · exact Submodule.add_mem _ (Submodule.smul_mem _ _ ha) (Submodule.smul_mem _ _ ha')
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailMore
section
theorem UpperTheory.Reformulated.B.Yra8.main.{u_1, u_2} :
    ∀ {R : Type u_1} {ι : Type u_2} [inst : CommRing R] (s : Finset ι) (e : ι → ℕ) (g : ι → Polynomial R) (c : ι → R),
      (∀ (i : ι), (g i).natDegree ≤ (1 : ℕ)) →
        (∀ (i : ι), (g i).coeff (1 : ℕ) = c i) →
          (∏ i ∈ s, g i ^ e i).natDegree ≤ ∑ i ∈ s, e i ∧ (∏ i ∈ s, g i ^ e i).coeff (∑ i ∈ s, e i) = ∏ i ∈ s, c i ^ e i := by
  intro R ι _ s e g c hd hc
  classical
  have hp : ∀ i, (g i ^ e i).natDegree ≤ e i ∧ (g i ^ e i).coeff (e i) = c i ^ e i := by
    intro i
    refine ⟨?_, ?_⟩
    · calc (g i ^ e i).natDegree ≤ e i * (g i).natDegree := Polynomial.natDegree_pow_le
        _ ≤ e i * 1 := Nat.mul_le_mul_left _ (hd i)
        _ = e i := by simp
    · have := Polynomial.coeff_pow_of_natDegree_le (m := e i) (hd i)
      simpa [hc i] using this
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, Finset.prod_insert ha]
    refine ⟨?_, ?_⟩
    · exact (Polynomial.natDegree_mul_le).trans (Nat.add_le_add (hp a).1 ih.1)
    · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le (hp a).1 ih.1, (hp a).2, ih.2]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTailRest
section
theorem UpperTheory.Reformulated.B.Yxa1.main :
    ∀ {α : Type} [inst : MeasurableSpace α] {ν : MeasureTheory.Measure α} {ι : Type} (s : Finset ι)
      (g : ι → ↥(MeasureTheory.Lp ℂ (2 : ENNReal) ν)),
      (↑(↑(∑ j ∈ s, g j) : α →ₘ[ν] ℂ) : α → ℂ) =ᵐ[ν] fun (x : α) ↦ ∑ j ∈ s, (↑(↑(g j) : α →ₘ[ν] ℂ) : α → ℂ) x := by
  intro α _ ν ι s g
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact MeasureTheory.Lp.coeFn_zero ℂ 2 ν
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    filter_upwards [MeasureTheory.Lp.coeFn_add (g a) (∑ j ∈ s, g j), ih] with x hx hx'
    rw [hx, Pi.add_apply, hx']
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTer
section
theorem UpperTheory.Reformulated.B.DYdc5.main.{u_1} :
    ∀ {R : Type u_1} [inst : CommRing R] (P : Ideal R) [hP : P.IsPrime] (t : ℕ),
      t ≠ (0 : ℕ) → (↑t : R) ∈ P → ∃ (p : ℕ), Nat.Prime p ∧ p ∣ t ∧ (↑p : R) ∈ P := by
  intro R _ P hP t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro ht hmem
    have h1 : t ≠ 1 := by
      rintro rfl
      exact hP.ne_top ((Ideal.eq_top_iff_one P).2 (by simpa using hmem))
    obtain ⟨p, hp, k, rfl⟩ := Nat.exists_prime_and_dvd h1
    rw [Nat.cast_mul] at hmem
    rcases hP.mem_or_mem hmem with h | h
    · exact ⟨p, hp, dvd_mul_right p k, h⟩
    · have hk : k ≠ 0 := by
        rintro rfl
        simp at ht
      have hlt : k < p * k :=
        lt_mul_of_one_lt_left (Nat.pos_of_ne_zero hk) hp.one_lt
      obtain ⟨q, hq, hqk, hqP⟩ := ih k hlt hk h
      exact ⟨q, hq, hqk.mul_left p, hqP⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerBis
section
noncomputable def UpperTheory.Reformulated.B.PadicComplexRingOfIntegers.intRing :
    (p : ℕ) → [inst : Fact (Nat.Prime p)] → Subring ℂ_[p] :=
  fun p _ =>
    { carrier := {x : ℂ_[p] | ‖x‖ ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a * b‖ ≤ 1
        rw [norm_mul]
        exact mul_le_one₀ ha' (norm_nonneg b) hb'
      one_mem' := by
        show ‖(1 : ℂ_[p])‖ ≤ 1
        exact norm_one.le
      add_mem' := fun {a b} ha hb => by
        have ha' : ‖a‖ ≤ 1 := ha
        have hb' : ‖b‖ ≤ 1 := hb
        show ‖a + b‖ ≤ 1
        exact (IsUltrametricDist.norm_add_le_max a b).trans (max_le ha' hb')
      zero_mem' := by
        show ‖(0 : ℂ_[p])‖ ≤ 1
        rw [norm_zero]
        exact zero_le_one
      neg_mem' := fun {a} ha => by
        have ha' : ‖a‖ ≤ 1 := ha
        show ‖-a‖ ≤ 1
        rwa [norm_neg] }
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerLast
section
theorem UpperTheory.Reformulated.B.Qf31.isCompact_box :
    ∀ {L : Type} [inst : NontriviallyNormedField L] [IsUltrametricDist L] {m : ℕ}
    [ProperSpace L] (c : Matrix (Fin m) (Fin m) L) (r : ℝ),
    IsCompact
      {g : GL (Fin m) L |
        (∀ (i j : Fin m), ‖(↑g : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r) ∧
          ∀ (i j : Fin m), ‖(↑g⁻¹ : Matrix (Fin m) (Fin m) L) i j - c i j‖ ≤ r} := by
  intro L _ _ m _ c r
  have hK : IsCompact {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} := by
    have h : IsCompact (Set.univ.pi fun i : Fin m =>
        Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) :=
      isCompact_univ_pi fun i => isCompact_univ_pi fun j => isCompact_closedBall (c i j) r
    have e : {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r} =
        (Set.univ.pi fun i : Fin m =>
          Set.univ.pi fun j : Fin m => Metric.closedBall (c i j) r) := by
      ext A
      constructor
      · intro hA i _ j _
        exact mem_closedBall_iff_norm.2 (hA i j)
      · intro hA i j
        exact mem_closedBall_iff_norm.1 (hA i (Set.mem_univ i) j (Set.mem_univ j))
    rw [e]
    exact h
  have hK' : IsCompact (MulOpposite.unop ⁻¹'
      {A : Matrix (Fin m) (Fin m) L | ∀ i j, ‖A i j - c i j‖ ≤ r}) :=
    (MulOpposite.opHomeomorph (M := Matrix (Fin m) (Fin m) L)).symm.isCompact_preimage.2 hK
  exact (Units.isClosedEmbedding_embedProduct
    (α := Matrix (Fin m) (Fin m) L)).isCompact_preimage (hK.prod hK')
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerRest
section
noncomputable def UpperTheory.Reformulated.B.Qe31.Statement :
    Prop :=
    ∀ (T : Type) [inst : CommRing T] [IsNoetherianRing T] (P : Ideal T) [inst_2 : P.IsPrime] (h : ℕ) (f : Fin h → T),
      (∀ (i : Fin h), f i ∈ P) →
        IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
            Ideal.span
                (Set.range fun (i : Fin h) ↦
                  (Algebra.algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) ⊔
              IsLocalRing.maximalIdeal (Localization.AtPrime P) ^ (2 : ℕ) →
          ∃ s ∉ P, ∀ x ∈ P, s * x ∈ Ideal.span (Set.range f)

theorem UpperTheory.Reformulated.B.Qe31.proof :
    UpperTheory.Reformulated.B.Qe31.Statement := by
  intro T _ _ P _ h f _ hle
  have hm : IsLocalRing.maximalIdeal (Localization.AtPrime P) ≤
      Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) := by
    refine Submodule.le_of_le_smul_of_le_jacobson_bot
      (I := IsLocalRing.maximalIdeal (Localization.AtPrime P))
      (IsNoetherian.noetherian _) (IsLocalRing.maximalIdeal_le_jacobson _) ?_
    rwa [smul_eq_mul, ← pow_two]
  have hI : Ideal.span (Set.range fun (i : Fin h) ↦
        (algebraMap T (Localization.AtPrime P) : T → Localization.AtPrime P) (f i)) =
      (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
    rw [Ideal.map_span, ← Set.range_comp]
    rfl
  have key : ∀ x ∈ P, ∃ s ∉ P, s * x ∈ Ideal.span (Set.range f) := by
    intro x hx
    have h1 : algebraMap T (Localization.AtPrime P) x ∈
        (Ideal.span (Set.range f)).map (algebraMap T (Localization.AtPrime P)) := by
      rw [← hI]
      apply hm
      rw [← Localization.AtPrime.map_eq_maximalIdeal]
      exact Ideal.mem_map_of_mem _ hx
    obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, hab⟩ :=
      (IsLocalization.mem_map_algebraMap_iff P.primeCompl _).1 h1
    rw [← map_mul, IsLocalization.eq_iff_exists P.primeCompl] at hab
    obtain ⟨⟨c, hc⟩, hcab⟩ := hab
    refine ⟨c * b, P.primeCompl.mul_mem hc hb, ?_⟩
    have : c * b * x = c * a := by
      simp only at hcab
      rw [← hcab]; ring
    rw [this]
    exact Ideal.mul_mem_left _ _ ha
  obtain ⟨S, hS⟩ := IsNoetherian.noetherian P
  have hSP : ∀ x ∈ S, x ∈ P := fun x hx ↦ hS ▸ Submodule.subset_span hx
  choose! g hg1 hg2 using key
  refine ⟨∏ y ∈ S, g y, P.primeCompl.prod_mem (fun y hy ↦ hg1 y (hSP y hy)), ?_⟩
  intro x hx
  rw [← hS] at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem g hy
    rw [hc, mul_comm (g y) c, mul_assoc]
    exact Ideal.mul_mem_left _ _ (hg2 y (hSP y hy))
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact Ideal.add_mem _ ha hb
  | smul c a _ ha =>
    rw [smul_eq_mul, mul_left_comm]
    exact Ideal.mul_mem_left _ _ ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerSide
section
theorem UpperTheory.Reformulated.B.Qf12.lift_ex :
    ∀ {A M Q Q' : Type} [inst : CommRing A] [inst_1 : AddCommGroup M]
    [inst_2 : AddCommGroup Q] [inst_3 : AddCommGroup Q'] [inst_4 : _root_.Module A M] [inst_5 : _root_.Module A Q]
    [inst_6 : _root_.Module A Q'] (π : M →ₗ[A] Q),
    Function.Surjective (⇑π : M → Q) →
      ∀ (g : M →ₗ[A] Q'),
        (∀ (m : M), (π : M → Q) m = (0 : Q) → (g : M → Q') m = (0 : Q')) →
          ∃ (q : Q →ₗ[A] Q'), ∀ (m : M), (q : Q → Q') ((π : M → Q) m) = (g : M → Q') m := by
  intro A M Q Q' _ _ _ _ _ _ _ π hπ g hg
  have hle : LinearMap.ker π ≤ LinearMap.ker g := fun m hm =>
    LinearMap.mem_ker.mpr (hg m (LinearMap.mem_ker.mp hm))
  refine ⟨((LinearMap.ker π).liftQ g hle).comp
    (π.quotKerEquivOfSurjective hπ).symm.toLinearMap, fun m => ?_⟩
  have h : (π.quotKerEquivOfSurjective hπ).symm (π m) = Submodule.Quotient.mk m := by
    rw [LinearEquiv.symm_apply_eq]
    rfl
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, h, Submodule.liftQ_apply]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ImportsTerTail
section
theorem UpperTheory.Reformulated.B.Qf13.pow_cong :
    ∀ {Ω : Type} [inst : Field Ω] (A : ValuationSubring Ω) {a b : Ω},
    (A.valuation : Ω → A.ValueGroup) a ≤ (1 : A.ValueGroup) →
      (A.valuation : Ω → A.ValueGroup) b ≤ (1 : A.ValueGroup) →
        (A.valuation : Ω → A.ValueGroup) (a - b) < (1 : A.ValueGroup) →
          ∀ (m : ℕ), (A.valuation : Ω → A.ValueGroup) (a ^ m - b ^ m) < (1 : A.ValueGroup) := by
  intro Ω _ A a b ha hb hab m
  induction m with
  | zero => simp
  | succ n ih =>
    have e : a ^ (n + 1) - b ^ (n + 1) = (a ^ n - b ^ n) * a + (a - b) * b ^ n := by ring
    rw [e]
    refine A.valuation.map_add_lt ?_ ?_
    · rw [map_mul]
      calc A.valuation (a ^ n - b ^ n) * A.valuation a
          ≤ A.valuation (a ^ n - b ^ n) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
    · rw [map_mul, map_pow]
      have hb' : A.valuation b ^ n ≤ 1 := pow_le_one' hb n
      calc A.valuation (a - b) * A.valuation b ^ n
          ≤ A.valuation (a - b) * 1 := by gcongr
        _ < 1 := by rwa [mul_one]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InPApplyEqZero
section
noncomputable def UpperTheory.Reformulated.B.Qh16.Jm :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ :=
    fun {n : ℕ} (ε : Fin n → Bool) ↦ Matrix.diagonal fun (a : Fin n) ↦ if ε a = Bool.true then (1 : ℂ) else (-1 : ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inG :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      X.conjTranspose * UpperTheory.Reformulated.B.Qh16.Jm ε + UpperTheory.Reformulated.B.Qh16.Jm ε * X = (0 : Matrix (Fin n) (Fin n) ℂ)

noncomputable def UpperTheory.Reformulated.B.Qh16.inP :
    {n : ℕ} → (Fin n → Bool) → Matrix (Fin n) (Fin n) ℂ → Prop :=
    fun {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) ↦
      UpperTheory.Reformulated.B.Qh16.inG ε X ∧ X * UpperTheory.Reformulated.B.Qh16.Jm ε = -(UpperTheory.Reformulated.B.Qh16.Jm ε * X)

theorem UpperTheory.Reformulated.B.Qh16.inP_apply_eq_zero :
    ∀ {n : ℕ} {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ},
      UpperTheory.Reformulated.B.Qh16.inP ε X → ∀ {a b : Fin n}, ε a = ε b → X a b = (0 : ℂ) := by
  intro n ε X h a b hab
  have h1 := congrFun (congrFun h.2 a) b
  unfold UpperTheory.Reformulated.B.Qh16.Jm at h1
  rw [Matrix.neg_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, hab] at h1
  split_ifs at h1
  · linear_combination (1 / 2 : ℂ) * h1
  · linear_combination (-1 / 2 : ℂ) * h1
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.InclR
section
@[reducible] noncomputable def UpperTheory.Reformulated.B.Qh24.Fv :
    (F : Type) →
      [inst : Field F] → [NumberField F] → IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F) → Type :=
    fun (F : Type) [Field F] [NumberField F] (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      IsDedekindDomain.HeightOneSpectrum.adicCompletion F v

noncomputable def UpperTheory.Reformulated.B.Qh24.inclR :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : Field E] →
          [inst_2 : Algebra F E] → (R : Type) → [inst_3 : CommRing R] → [inst_4 : Algebra F R] → E →+* TensorProduct F R E :=
    fun {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] ↦
      Algebra.TensorProduct.includeRight.toRingHom

noncomputable def UpperTheory.Reformulated.B.Qh24.OEv :
    {F E : Type} →
      [inst : Field F] →
        [inst_1 : NumberField F] →
          [inst_2 : Field E] →
            [inst_3 : Algebra F E] →
              (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) →
                Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E) :=
    fun {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
        (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)) ↦
      (↑(Submodule.span (↥(IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers F v))
            ((fun (x : NumberField.RingOfIntegers E) ↦
                (UpperTheory.Reformulated.B.Qh24.inclR (UpperTheory.Reformulated.B.Qh24.Fv F v) : E → TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E)
                  (↑x : E)) ''
              Set.univ)) :
        Set (TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E))

theorem UpperTheory.Reformulated.B.Qh24.oev_mul :
    ∀ {F E : Type} [inst : Field F] [inst_1 : NumberField F] [inst_2 : Field E] [NumberField E] [inst_4 : Algebra F E]
      (v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F))
      {s t : TensorProduct F (UpperTheory.Reformulated.B.Qh24.Fv F v) E},
      s ∈ UpperTheory.Reformulated.B.Qh24.OEv v → t ∈ UpperTheory.Reformulated.B.Qh24.OEv v → s * t ∈ UpperTheory.Reformulated.B.Qh24.OEv v := by
  intro F E _ _ _ _ _ v s t hs ht
  unfold UpperTheory.Reformulated.B.Qh24.OEv at *
  simp only [SetLike.mem_coe] at *
  induction hs using Submodule.span_induction with
  | zero => rw [zero_mul]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [add_mul]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c ha
  | mem a ha =>
    induction ht using Submodule.span_induction with
    | zero => rw [mul_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [mul_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [mul_smul_comm]; exact Submodule.smul_mem _ c hx
    | mem b hb =>
      obtain ⟨x, -, rfl⟩ := ha
      obtain ⟨y, -, rfl⟩ := hb
      refine Submodule.subset_span ⟨x * y, Set.mem_univ _, ?_⟩
      beta_reduce
      rw [← map_mul]
      rfl
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.IndependenceEigenvectors
section
theorem UpperTheory.Reformulated.B.IndependenceEigenvectors.indep :
    ∀ {V I J : Type} [inst : AddCommGroup V]
    [inst_1 : _root_.Module ℂ V] (T : I → Module.End ℂ V) (v : J → V) (lam : J → I → ℂ),
    (∀ (j : J), v j ≠ (0 : V)) →
      (∀ (j : J) (i : I), (T i : V → V) (v j) = lam j i • v j) → Function.Injective lam → LinearIndependent ℂ v := by
  intro V I J _ _ T v lam hv hT hinj
  classical
  rw [linearIndependent_iff']
  intro s
  induction s using Finset.induction_on with
  | empty => intro g _ j hj; simp at hj
  | insert a s ha ih =>
    intro g hg
    rw [Finset.sum_insert ha] at hg
    have hs : ∀ j ∈ s, g j = 0 := by
      intro j hj
      have hne : lam j ≠ lam a := fun h => ha (hinj h ▸ hj)
      obtain ⟨i, hi⟩ := Function.ne_iff.mp hne
      have h1 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam k i) • v k = 0 := by
        have h := congrArg (T i) hg
        set_option synthInstance.maxHeartbeats 100000 in
          simpa only [map_add (f := _), map_sum, map_smul, map_zero, hT, smul_smul] using h
      have h2 : (g a * lam a i) • v a + ∑ k ∈ s, (g k * lam a i) • v k = 0 := by
        have h := congrArg (fun x => lam a i • x) hg
        simpa only [smul_add, Finset.smul_sum, smul_zero, smul_smul, mul_comm (lam a i)] using h
      have h3 : ∑ k ∈ s, (g k * (lam k i - lam a i)) • v k = 0 := by
        simp only [mul_sub, sub_smul, Finset.sum_sub_distrib]
        exact sub_eq_zero.mpr (add_left_cancel (h1.trans h2.symm))
      have h4 := ih (fun k => g k * (lam k i - lam a i)) h3 j hj
      exact (mul_eq_zero.mp h4).resolve_right (sub_ne_zero.mpr hi)
    have hz : ∑ k ∈ s, g k • v k = 0 :=
      Finset.sum_eq_zero fun k hk => by rw [hs k hk, zero_smul]
    rw [hz, add_zero] at hg
    intro j hj
    rcases Finset.mem_insert.mp hj with rfl | hj
    · exact (smul_eq_zero.mp hg).resolve_right (hv _)
    · exact hs j hj
end

