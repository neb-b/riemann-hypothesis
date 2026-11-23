module

public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.PzIffPos
section
noncomputable def UpperTheory.Reformulated.B.Qh60.Pz :
    {R : Type} → [inst : Ring R] → [Algebra ℝ R] → R → Prop :=
    fun {R : Type} [Ring R] [Algebra ℝ R] (t : R) ↦
      ∃ (s : Finset ℝ),
        (∀ l ∈ s, (0 : ℝ) < l) ∧
          (Polynomial.aeval t : Polynomial ℝ → R) (∏ l ∈ s, (Polynomial.X - (Polynomial.C : ℝ → Polynomial ℝ) l)) = (0 : R)

private theorem UpperTheory.Reformulated.B.Qh60.aux {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] (T : Module.End ℝ W) (hT : LinearMap.IsSymmetric T) :
    UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ x : W, x ≠ 0 → 0 < inner ℝ (T x) x := by
  classical
  have hn : Module.finrank ℝ W = Module.finrank ℝ W := rfl
  set b := hT.eigenvectorBasis hn with hb
  set μ := hT.eigenvalues hn with hμ
  have hev : ∀ i, Module.End.HasEigenvector T (μ i) (b i) := fun i => by
    simpa using hT.hasEigenvector_eigenvectorBasis hn i
  have happ : ∀ i, T (b i) = μ i • b i := fun i => (hev i).apply_eq_smul
  have hne : ∀ i, b i ≠ 0 := fun i => (hev i).2
  have haev : ∀ (s : Finset ℝ) i,
      (Polynomial.aeval T (∏ l ∈ s, (Polynomial.X - Polynomial.C l))) (b i)
        = (∏ l ∈ s, (μ i - l)) • b i := fun s i => by
    rw [Module.End.aeval_apply_of_hasEigenvector (hev i)]
    simp [Polynomial.eval_prod]
  constructor
  · rintro ⟨s, hs, h0⟩ x hx
    have hpos : ∀ i, 0 < μ i := fun i => by
      have h1 := haev s i
      rw [h0, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h1
      obtain ⟨l, hl, h2⟩ := Finset.prod_eq_zero_iff.1 (h1.resolve_right (hne i))
      rw [sub_eq_zero.1 h2]
      exact hs l hl
    have hsum : inner ℝ (T x) x = ∑ i, μ i * (inner ℝ (b i) x) ^ 2 := by
      rw [← b.sum_inner_mul_inner (T x) x]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hT x (b i), happ i, real_inner_smul_right, real_inner_comm (b i) x]
      ring
    have hex : ∃ i, inner ℝ (b i) x ≠ 0 := by
      by_contra hc
      push Not at hc
      apply hx
      rw [← b.sum_repr' x]
      simp [hc]
    obtain ⟨i, hi⟩ := hex
    rw [hsum]
    exact Finset.sum_pos' (fun j _ => mul_nonneg (hpos j).le (sq_nonneg _))
      ⟨i, Finset.mem_univ i, mul_pos (hpos i) (by positivity)⟩
  · intro h
    refine ⟨Finset.univ.image μ, ?_, ?_⟩
    · intro l hl
      obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hl
      have h1 := h (b i) (hne i)
      rw [happ i, real_inner_smul_left] at h1
      exact (pos_iff_pos_of_mul_pos h1).2 (real_inner_self_pos.2 (hne i))
    · refine b.toBasis.ext fun i => ?_
      rw [OrthonormalBasis.coe_toBasis, haev, LinearMap.zero_apply,
        Finset.prod_eq_zero (Finset.mem_image_of_mem μ (Finset.mem_univ i)) (sub_self _), zero_smul]

theorem UpperTheory.Reformulated.B.Qh60.Pz_iff_pos :
    ∀ {W : Type} [inst : AddCommGroup W] [inst_1 : _root_.Module ℝ W] [FiniteDimensional ℝ W] (Q : W →ₗ[ℝ] W →ₗ[ℝ] ℝ),
      (∀ (x y : W), ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) y : W → ℝ) x) →
        (∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) x) →
          ∀ (T : Module.End ℝ W),
            (∀ (x y : W),
                ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) y = ((Q : W → W →ₗ[ℝ] ℝ) x : W → ℝ) ((T : W → W) y)) →
              (UpperTheory.Reformulated.B.Qh60.Pz T ↔ ∀ (x : W), x ≠ (0 : W) → (0 : ℝ) < ((Q : W → W →ₗ[ℝ] ℝ) ((T : W → W) x) : W → ℝ) x) := by
  intro W _ _ _ Q hsymm hpos T hT
  let c : InnerProductSpace.Core ℝ W :=
    { inner := fun x y => Q x y
      conj_inner_symm := fun x y => by simpa using hsymm y x
      re_inner_nonneg := fun x => by
        by_cases hx : x = 0
        · simp [hx]
        · simpa using (hpos x hx).le
      add_left := fun x y z => by simp
      smul_left := fun x y r => by simp
      definite := fun x hx => by
        by_contra h
        exact (hpos x h).ne' hx }
  letI : NormedAddCommGroup W := @InnerProductSpace.Core.toNormedAddCommGroup ℝ W _ _ _ c
  letI : InnerProductSpace ℝ W := InnerProductSpace.ofCore c.toCore
  exact UpperTheory.Reformulated.B.Qh60.aux T (fun x y => hT x y)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.QuotientBasisFiniteModule
section
theorem UpperTheory.Reformulated.B.FiniteModuleImageInFiniteExtension.qb_fdmod :
    ∀ {l : ℕ} [inst : Fact (Nat.Prime l)] {M : Type}
    [inst_1 : AddCommGroup M] [inst_2 : _root_.Module ℤ_[l] M] [Module.Finite ℤ_[l] M] (f : M →ₗ[ℤ_[l]] PadicAlgCl l),
    ∃ (K : IntermediateField ℚ_[l] (PadicAlgCl l)),
      FiniteDimensional ℚ_[l] ↥K ∧ ∀ (x : M), (f : M → PadicAlgCl l) x ∈ K := by
  intro l _ M _ _ hM f
  obtain ⟨S, hS⟩ := hM.fg_top
  have hfin : (f '' (S : Set M)).Finite := S.finite_toSet.image _
  haveI : Finite (f '' (S : Set M)) := hfin.to_subtype
  refine ⟨IntermediateField.adjoin ℚ_[l] (f '' (S : Set M)), ?_, ?_⟩
  · exact IntermediateField.finiteDimensional_adjoin
      (fun x _ => Algebra.IsIntegral.isIntegral x)
  · intro x
    have hx : x ∈ Submodule.span ℤ_[l] (S : Set M) := by
      rw [hS]; exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem y hy => exact IntermediateField.subset_adjoin _ _ ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha =>
      rw [map_smul, ← IsScalarTower.algebraMap_smul ℚ_[l] c (f a)]
      exact IntermediateField.smul_mem _ ha
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RadFinAdjoinStable
section
noncomputable def UpperTheory.Reformulated.B.Qj9.Stable :
    {M : Type} → [inst : AddCommGroup M] → [inst_1 : _root_.Module ℂ M] → Set (Module.End ℂ M) → Submodule ℂ M → Prop :=
    fun {M : Type} [AddCommGroup M] [_root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M) ↦
      ∀ g ∈ Op, ∀ x ∈ P, (g : M → M) x ∈ P

theorem UpperTheory.Reformulated.B.Qj9.radFin_adjoin_stable :
    ∀ {M : Type} [inst : AddCommGroup M] [inst_1 : _root_.Module ℂ M] (Op : Set (Module.End ℂ M)) (P : Submodule ℂ M),
      UpperTheory.Reformulated.B.Qj9.Stable Op P → ∀ e ∈ Algebra.adjoin ℂ Op, ∀ x ∈ P, (e : M → M) x ∈ P := by
  intro M _ _ Op P h e he
  induction he using Algebra.adjoin_induction with
  | mem g hg => exact h g hg
  | algebraMap r =>
    intro x hx
    rw [Module.algebraMap_end_apply]
    exact P.smul_mem r hx
  | add a b _ _ ha hb =>
    intro x hx
    rw [LinearMap.add_apply]
    exact P.add_mem (ha x hx) (hb x hx)
  | mul a b _ _ ha hb =>
    intro x hx
    rw [Module.End.mul_apply]
    exact ha _ (hb x hx)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RealDiff
section
open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.one_side {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) :
    ∫ x, G x ∂Measure.map X (ν.withDensity fun ω ↦ ENNReal.ofReal (f ω)) =
      ∫ ω, G (X ω) * ((max (f ω) 0 : ℝ) : ℂ) ∂ν := by
  rw [integral_map hX.aemeasurable hG.aestronglyMeasurable]
  have h : AEMeasurable (fun ω ↦ (f ω).toNNReal) ν := hf.aemeasurable.real_toNNReal
  have h2 := integral_withDensity_eq_integral_smul₀ h (fun ω ↦ G (X ω))
  refine Eq.trans h2 ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  simp only [NNReal.smul_def, Real.coe_toNNReal', Complex.real_smul, mul_comm]

open MeasureTheory in
private theorem UpperTheory.Reformulated.B.Qh3.int_mul {Ω ι : Type} [MeasurableSpace Ω] [Fintype ι]
    (ν : Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ) (hX : Measurable X) (hf : Integrable f ν)
    (G : (ι → ℝ) → ℂ) (hG : Measurable G) (hb : ∀ x, ‖G x‖ ≤ (1 : ℝ)) :
    Integrable (fun ω ↦ G (X ω) * ((max (f ω) 0 : ℝ) : ℂ)) ν := by
  have h1 : Integrable (fun ω ↦ ((max (f ω) 0 : ℝ) : ℂ)) ν := hf.pos_part.ofReal
  exact h1.bdd_mul (c := 1) (hG.comp hX).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ω ↦ hb _)

theorem UpperTheory.Reformulated.B.Qh3.real_diff :
    ∀ {Ω ι : Type} [inst : MeasurableSpace Ω] [Fintype ι]
    (ν : MeasureTheory.Measure Ω) (X : Ω → ι → ℝ) (f : Ω → ℝ),
    Measurable X →
      MeasureTheory.Integrable f ν →
        ∀ (G : (ι → ℝ) → ℂ),
          Measurable G →
            (∀ (x : ι → ℝ), ‖G x‖ ≤ (1 : ℝ)) →
              ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (f ω)) -
                  ∫ (x : ι → ℝ), G x ∂MeasureTheory.Measure.map X (ν.withDensity fun (ω : Ω) ↦ ENNReal.ofReal (-f ω)) =
                ∫ (ω : Ω), G (X ω) * (↑(f ω) : ℂ) ∂ν := by
  intro Ω ι _ _ ν X f hX hf G hG hb
  have hn : MeasureTheory.Integrable (fun ω ↦ -f ω) ν := hf.neg
  rw [UpperTheory.Reformulated.B.Qh3.one_side ν X f hX hf G hG,
    UpperTheory.Reformulated.B.Qh3.one_side ν X (fun ω ↦ -f ω) hX hn G hG,
    ← MeasureTheory.integral_sub (UpperTheory.Reformulated.B.Qh3.int_mul ν X f hX hf G hG hb)
      (UpperTheory.Reformulated.B.Qh3.int_mul ν X (fun ω ↦ -f ω) hX hn G hG hb)]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun ω ↦ ?_)
  have h : max (f ω) 0 - max (-f ω) 0 = f ω := max_zero_sub_max_neg_zero_eq_self (f ω)
  simp only
  rw [← mul_sub, ← Complex.ofReal_sub, h]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ReprMem
section
open scoped IntermediateField TensorProduct Matrix Pointwise NumberField Topology ContDiff NNReal ENNReal Polynomial DirectSum BigOperators InnerProductSpace Manifold

theorem UpperTheory.Reformulated.B.ReprMem.repr_mem :
    ∀ {F E : Type} [inst : Field F] [inst_1 : Field E]
    [inst_2 : Algebra F E] (t : E) (c : F),
    t ^ (2 : ℕ) = (Algebra.algebraMap F E : F → E) c →
      ∀ x ∈ F⟮t⟯, ∃ (a : F) (b : F), x = (Algebra.algebraMap F E : F → E) a + (Algebra.algebraMap F E : F → E) b * t := by
  intro F E _ _ _ t c h x hx
  have hint : IsIntegral F t := by
    apply IsIntegral.of_pow (n := 2) (by norm_num)
    rw [h]
    exact isIntegral_algebraMap
  have hx' : x ∈ Algebra.adjoin F {t} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic hint.isAlgebraic]
    exact hx
  clear hx
  induction hx' using Algebra.adjoin_induction with
  | mem y hy =>
    rw [Set.mem_singleton_iff] at hy
    exact ⟨0, 1, by simp [hy]⟩
  | algebraMap r => exact ⟨r, 0, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    exact ⟨a + a', b + b', by rw [map_add (f := _), map_add (f := _)]; ring⟩
  | mul y z _ _ hy hz =>
    obtain ⟨a, b, rfl⟩ := hy
    obtain ⟨a', b', rfl⟩ := hz
    refine ⟨a * a' + b * b' * c, a * b' + b * a', ?_⟩
    simp only [map_add (f := _), map_mul]
    rw [← h]
    ring
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Reps
section
theorem UpperTheory.Reformulated.B.Qh68.reps.{u_1} :
    ∀ {α : Type u_1} (r : α → α → Prop),
    Equivalence r → ∀ (A : Finset α), ∃ T ⊆ A, (∀ t ∈ T, ∀ t' ∈ T, r t t' → t = t') ∧ ∀ a ∈ A, ∃ t ∈ T, r a t := by
  intro α r hr A
  classical
  induction A using Finset.induction_on with
  | empty => exact ⟨∅, Finset.Subset.refl _, by simp, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T, hTs, hinj, hcov⟩ := ih
    by_cases h : ∃ t ∈ T, r a t
    · refine ⟨T, hTs.trans (Finset.subset_insert a s), hinj, ?_⟩
      intro b hb
      rcases Finset.mem_insert.mp hb with rfl | hb
      · exact h
      · exact hcov b hb
    · refine ⟨insert a T, Finset.insert_subset_insert a hTs, ?_, ?_⟩
      · intro t ht t' ht' htt
        rcases Finset.mem_insert.mp ht with h1 | h1
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · rw [h1, h2]
          · exact absurd ⟨t', h2, h1 ▸ htt⟩ h
        · rcases Finset.mem_insert.mp ht' with h2 | h2
          · exact absurd ⟨t, h1, h2 ▸ hr.symm htt⟩ h
          · exact hinj t h1 t' h2 htt
      · intro b hb
        rcases Finset.mem_insert.mp hb with h1 | h1
        · exact ⟨b, Finset.mem_insert.mpr (Or.inl h1), hr.refl b⟩
        · obtain ⟨t, ht, hbt⟩ := hcov b h1
          exact ⟨t, Finset.mem_insert_of_mem ht, hbt⟩
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RepsProd
section
open scoped Classical

noncomputable def UpperTheory.Reformulated.B.P9.IsReps.{u_1} :
    {V : Type u_1} → [inst : AddCommGroup V] → AddSubgroup V → AddSubgroup V → Finset V → Prop :=
    fun {V : Type u_1} [AddCommGroup V] (Λ₁ Λ₂ : AddSubgroup V) (S : Finset V) ↦
      (∀ x ∈ S, x ∈ Λ₂) ∧ (∀ x ∈ S, ∀ y ∈ S, x - y ∈ Λ₁ → x = y) ∧ ∀ y ∈ Λ₂, ∃ x ∈ S, y - x ∈ Λ₁

theorem UpperTheory.Reformulated.B.P9.aux2 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → a + b ∈ Λ ∧ (p : V → V) (a + b) = a + b := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2]⟩

theorem UpperTheory.Reformulated.B.P9.aux3 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux4 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = x} → -a ∈ Λ ∧ (p : V → V) (-a) = -a := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partP :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = x}, add_mem' := @UpperTheory.Reformulated.B.P9.aux2 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux3 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux4 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.aux6 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a b : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} →
        b ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → a + b ∈ Λ ∧ (p : V → V) (a + b) = (0 : V) := by
  intro V _ p Λ a b ha hb
  exact ⟨Λ.add_mem ha.1 hb.1, by rw [map_add (f := _), ha.2, hb.2, add_zero]⟩

theorem UpperTheory.Reformulated.B.P9.aux7 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V), (0 : V) ∈ Λ ∧ (p : V → V) (0 : V) = (0 : V) := by
  intro V _ p Λ
  exact ⟨Λ.zero_mem, map_zero p⟩

theorem UpperTheory.Reformulated.B.P9.aux8 :
    ∀ {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) {a : V},
      a ∈ {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)} → -a ∈ Λ ∧ (p : V → V) (-a) = (0 : V) := by
  intro V _ p Λ a ha
  exact ⟨Λ.neg_mem ha.1, by rw [map_neg, ha.2, neg_zero]⟩

noncomputable def UpperTheory.Reformulated.B.P9.partQ :
    {V : Type} → [inst : AddCommGroup V] → (V →+ V) → AddSubgroup V → AddSubgroup V :=
    fun {V : Type} [inst : AddCommGroup V] (p : V →+ V) (Λ : AddSubgroup V) ↦
      { carrier := {x : V | x ∈ Λ ∧ (p : V → V) x = (0 : V)}, add_mem' := @UpperTheory.Reformulated.B.P9.aux6 V inst p Λ,
        zero_mem' := UpperTheory.Reformulated.B.P9.aux7 p Λ, neg_mem' := @UpperTheory.Reformulated.B.P9.aux8 V inst p Λ : AddSubgroup V }

theorem UpperTheory.Reformulated.B.P9.reps_prod :
    ∀ {V : Type} [inst : AddCommGroup V] [_root_.Module ℂ V] {M Λ : AddSubgroup V} (p : V →+ V),
      (∀ (x : V), (p : V → V) ((p : V → V) x) = (p : V → V) x) →
        (∀ x ∈ Λ, (p : V → V) x ∈ Λ) →
          (∀ x ∈ M, (p : V → V) x ∈ M) →
            ∀ {A B : Finset V},
              UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partP p Λ) A →
                UpperTheory.Reformulated.B.P9.IsReps M (UpperTheory.Reformulated.B.P9.partQ p Λ) B →
                  UpperTheory.Reformulated.B.P9.IsReps M Λ (Finset.image (fun (w : V × V) ↦ w.1 + w.2) (A ×ˢ B)) := by
  intro V _ _ M Λ p hpp hΛ hM A B hA hB
  obtain ⟨hA1, hA2, hA3⟩ := hA
  obtain ⟨hB1, hB2, hB3⟩ := hB
  have hA1' : ∀ x ∈ A, x ∈ Λ ∧ p x = x := hA1
  have hB1' : ∀ x ∈ B, x ∈ Λ ∧ p x = 0 := hB1
  have hA3' : ∀ y, (y ∈ Λ ∧ p y = y) → ∃ x ∈ A, y - x ∈ M := hA3
  have hB3' : ∀ y, (y ∈ Λ ∧ p y = 0) → ∃ x ∈ B, y - x ∈ M := hB3
  refine ⟨?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    exact Λ.add_mem (hA1' a ha).1 (hB1' b hb).1
  · intro x hx y hy hxy
    obtain ⟨⟨a, b⟩, hw, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨ha, hb⟩ := Finset.mem_product.1 hw
    obtain ⟨⟨a', b'⟩, hw', rfl⟩ := Finset.mem_image.1 hy
    obtain ⟨ha', hb'⟩ := Finset.mem_product.1 hw'
    change a + b - (a' + b') ∈ M at hxy
    change a + b = a' + b'
    have h1 : p (a + b - (a' + b')) = a - a' := by
      rw [map_sub, map_add (f := _), map_add (f := _), (hA1' a ha).2, (hA1' a' ha').2, (hB1' b hb).2,
        (hB1' b' hb').2, add_zero, add_zero]
    have h2 : a = a' := hA2 a ha a' ha' (h1 ▸ hM _ hxy)
    have h3 : b = b' := by
      refine hB2 b hb b' hb' ?_
      rwa [h2, add_sub_add_left_eq_sub] at hxy
    rw [h2, h3]
  · intro y hy
    obtain ⟨a, ha, hya⟩ := hA3' (p y) ⟨hΛ y hy, hpp y⟩
    obtain ⟨b, hb, hyb⟩ := hB3' (y - p y)
      ⟨Λ.sub_mem hy (hΛ y hy), by rw [map_sub, hpp, sub_self]⟩
    refine ⟨a + b, Finset.mem_image.2 ⟨(a, b), Finset.mem_product.2 ⟨ha, hb⟩, rfl⟩, ?_⟩
    have h : y - (a + b) = (p y - a) + (y - p y - b) := by abel
    rw [h]
    exact M.add_mem hya hyb
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResAlgClosed
section
theorem UpperTheory.Reformulated.B.Qk69.res_algClosed :
    ∀ {Ω : Type} [inst : Field Ω] [IsAlgClosed Ω]
    (A : ValuationSubring Ω), IsAlgClosed (IsLocalRing.ResidueField ↥A) := by
  intro Ω _ _ A
  refine IsAlgClosed.of_exists_root _ fun p hp hirr => ?_
  have hsurj : Function.Surjective (IsLocalRing.residue A) := IsLocalRing.residue_surjective
  have hl : p ∈ Polynomial.lifts (IsLocalRing.residue A) :=
    (Polynomial.mem_lifts _).2 (Polynomial.map_surjective _ hsurj p)
  obtain ⟨q, hq, hdeg, hm⟩ := Polynomial.lifts_and_degree_eq_and_monic hl hp
  have hd : q.degree ≠ 0 := by
    rw [hdeg]
    exact (Polynomial.degree_pos_of_irreducible hirr).ne'
  have hinj : Function.Injective (algebraMap A Ω) := Subtype.val_injective
  have hd' : (q.map (algebraMap A Ω)).degree ≠ 0 := by
    rwa [hm.degree_map]
  obtain ⟨x, hx⟩ := IsAlgClosed.exists_root _ hd'
  have hx' : Polynomial.eval₂ (algebraMap A Ω) x q = 0 := by
    rw [← Polynomial.eval_map]
    exact hx
  have hint : IsIntegral A x := ⟨q, hm, hx'⟩
  obtain ⟨y, rfl⟩ := IsIntegrallyClosed.algebraMap_eq_of_integral hint
  have hy : q.eval y = 0 := by
    apply hinj
    rw [Polynomial.eval₂_at_apply] at hx'
    rw [hx', map_zero]
  refine ⟨IsLocalRing.residue A y, ?_⟩
  rw [← hq, Polynomial.eval_map, Polynomial.eval₂_at_apply, hy, map_zero]
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.ResidueHomNorm
section
theorem UpperTheory.residue_hom_norm :
    ∀ {O R Ω : Type} [CommRing O] [CommRing R] [IsLocalRing R] [Algebra O R] [NormedField Ω]
        [IsUltrametricDist Ω] [Algebra O Ω]
        (hres : ∀ x : R, ∃ a : O, x - algebraMap O R a ∈ IsLocalRing.maximalIdeal R)
        (hO : ∀ a : O, ‖algebraMap O Ω a‖ ≤ 1) (hint : ∀ x : Ω, ‖x‖ ≤ 1 → IsIntegral O x)
        (y : R →ₐ[O] Ω),
        (∀ a, ‖y a‖ ≤ 1) ∧ ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
  intro O R Ω _ _ _ _ _ _ _ hres hO hint y
  have hm : ∀ a ∈ IsLocalRing.maximalIdeal R, ‖y a‖ < 1 := by
    intro m hmem
    by_contra hge
    have hge' : 1 ≤ ‖y m‖ := not_lt.mp hge
    have hne : y m ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hge'
      linarith
    have hu : ‖(y m)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact inv_le_one_of_one_le₀ hge'
    obtain ⟨p, hp, hev⟩ := hint _ hu
    have hrev : Polynomial.eval₂ (algebraMap O Ω) (y m) p.reverse = 0 := by
      haveI : Invertible (y m)⁻¹ := invertibleOfNonzero (inv_ne_zero hne)
      have h := Polynomial.eval₂_reverse_mul_pow (algebraMap O Ω) (y m)⁻¹ p
      rw [invOf_eq_inv, inv_inv, hev] at h
      exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ (inv_ne_zero hne))
    have hq : y (Polynomial.aeval m p.reverse) = 0 := by
      rw [Polynomial.aeval_algHom_apply y m p.reverse |>.symm]
      simpa [Polynomial.aeval_def] using hrev
    have hdvd : m ∣ Polynomial.aeval m p.reverse - 1 := by
      have h := Polynomial.sub_dvd_eval_sub m 0 (p.reverse.map (algebraMap O R))
      have h0 : (p.reverse.map (algebraMap O R)).eval 0 = 1 := by
        rw [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_map,
          Polynomial.coeff_zero_reverse, hp.leadingCoeff, map_one]
      rw [h0, sub_zero, Polynomial.eval_map_algebraMap] at h
      exact h
    have hunit : IsUnit (Polynomial.aeval m p.reverse : R) := by
      by_contra hnu
      have h1 : (Polynomial.aeval m p.reverse : R) ∈ IsLocalRing.maximalIdeal R :=
        (IsLocalRing.mem_maximalIdeal _).mpr hnu
      have h2 : Polynomial.aeval m p.reverse - 1 ∈ IsLocalRing.maximalIdeal R :=
        Ideal.mem_of_dvd _ hdvd hmem
      have h3 : (1 : R) ∈ IsLocalRing.maximalIdeal R := by
        have := Ideal.sub_mem _ h1 h2
        simpa using this
      exact (Ideal.ne_top_iff_one _).mp (IsLocalRing.maximalIdeal.isMaximal R).ne_top h3
    have := hunit.map y
    rw [hq] at this
    exact not_isUnit_zero this
  refine ⟨fun x => ?_, hm⟩
  obtain ⟨a, ha⟩ := hres x
  have hx : y x = algebraMap O Ω a + y (x - algebraMap O R a) := by
    rw [map_sub, AlgHom.commutes]
    ring
  rw [hx]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans
    (max_le (hO a) (hm _ ha).le)
end

-- bundled from Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.RingSec
section
theorem UpperTheory.Reformulated.B.Qh66.ring_sec :
    ∀ (Ω C : Type) [inst : Field Ω] [IsAlgClosed Ω]
    [inst_2 : CommRing C] [Nontrivial C] (φ : Ω →+* C), φ.FiniteType → ∃ (ρ : C →+* Ω), ρ.comp φ = RingHom.id Ω := by
  intro Ω C _ _ _ _ φ hφ
  letI : Algebra Ω C := φ.toAlgebra
  haveI : Algebra.FiniteType Ω C := hφ
  obtain ⟨m, hm⟩ := Ideal.exists_maximal C
  letI : Field (C ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite Ω (C ⧸ m) := finite_of_finite_type_of_isJacobsonRing Ω (C ⧸ m)
  let f : (C ⧸ m) →ₐ[Ω] Ω := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  refine ⟨(f.comp (Ideal.Quotient.mkₐ Ω m)).toRingHom, ?_⟩
  ext x
  exact (f.comp (Ideal.Quotient.mkₐ Ω m)).commutes x
end

