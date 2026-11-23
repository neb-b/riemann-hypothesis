module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.IsCoreMod
public import Development.WeilBound.RepresentationTheoryGL.HolomorphicDiscreteSeries.SchurEigenProjections.EigA
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0338
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.MirabolicDerivatives.CuspGenericWhittaker.CuspGeneric
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0337
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ZelevinskyJacquet.FineJacquetModules.SegDefs
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsKFiniteSubmoduleContaining
section
noncomputable section

open PositivityTheory.RgBcC.RealD (alg kF)

namespace GlobalTheory.CompanionTheory.ModelS.LocFin

section Abstract

variable {V : Type} [AddCommGroup V] [Module ℂ V] {ι κ : Type}

def stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : Submodule ℂ V := S ⊔ ⨆ i, S.map (L i)

def fil (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) : Submodule ℂ V := (stp L)^[k] S₀

theorem fil_succ (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) (k : ℕ) :
    fil L S₀ (k + 1) = stp L (fil L S₀ k) :=
  Function.iterate_succ_apply' _ _ _

theorem le_stp (L : ι → Module.End ℂ V) (S : Submodule ℂ V) : S ≤ stp L S := le_sup_left

theorem letter_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S) (i : ι) :
    L i u ∈ stp L S :=
  Submodule.mem_sup_right (Submodule.mem_iSup_of_mem i (Submodule.mem_map_of_mem hu))

theorem span_mem_stp (L : ι → Module.End ℂ V) {S : Submodule ℂ V} {u : V} (hu : u ∈ S)
    {C : Module.End ℂ V} (hC : C ∈ Submodule.span ℂ (Set.range L)) : C u ∈ stp L S := by
  induction hC using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    exact letter_mem_stp L hu i
  | zero => simp
  | add x y _ _ hx hy => simpa using add_mem hx hy
  | smul c x _ hx => simpa using Submodule.smul_mem _ c hx

theorem fil_mono (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) : Monotone (fil L S₀) :=
  monotone_nat_of_le_succ fun k => by
    rw [fil_succ]
    exact le_stp L _

theorem fil_finite [Finite ι] (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) [h₀ : FiniteDimensional ℂ S₀] (k : ℕ) :
    FiniteDimensional ℂ (fil L S₀ k) := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    have : ∀ i, FiniteDimensional ℂ ((fil L S₀ k).map (L i)) := fun i => inferInstance
    have : FiniteDimensional ℂ ↥(⨆ i, (fil L S₀ k).map (L i) : Submodule ℂ V) := Submodule.finiteDimensional_iSup _
    exact Submodule.finiteDimensional_sup _ _

theorem stp_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S : Submodule ℂ V}
    (hS : ∀ w ∈ S, K w ∈ S) : ∀ w ∈ stp L S, K w ∈ stp L S := by
  have key : stp L S ≤ (stp L S).comap K := by
    refine sup_le (fun w hw => le_stp L S (hS w hw)) (iSup_le fun i => ?_)
    rintro _ ⟨u, hu, rfl⟩
    have h1 : L i (K u) ∈ stp L S := letter_mem_stp L (hS u hu) i
    have h2 : (K * L i - L i * K) u ∈ stp L S := span_mem_stp L hu (hK i)
    have h3 : K (L i u) = (K * L i - L i * K) u + L i (K u) := by simp
    change K (L i u) ∈ stp L S
    rw [h3]
    exact add_mem h2 h1
  exact fun w hw => key hw

theorem fil_stable (L : ι → Module.End ℂ V) (K : Module.End ℂ V)
    (hK : ∀ i, K * L i - L i * K ∈ Submodule.span ℂ (Set.range L)) {S₀ : Submodule ℂ V}
    (h₀ : ∀ w ∈ S₀, K w ∈ S₀) (k : ℕ) : ∀ w ∈ fil L S₀ k, K w ∈ fil L S₀ k := by
  induction k with
  | zero => exact h₀
  | succ k ih =>
    rw [fil_succ]
    exact stp_stable L K hK ih

theorem mem_fil_of_adjoin (L : ι → Module.End ℂ V) (S₀ : Submodule ℂ V) {T : Module.End ℂ V}
    (hT : T ∈ Algebra.adjoin ℂ (Set.range L)) {f : V} (hf : f ∈ S₀) : ∃ k, T f ∈ fil L S₀ k := by
  have key : ∀ w, (∃ k, w ∈ fil L S₀ k) → ∃ k, T w ∈ fil L S₀ k := by
    induction hT using Algebra.adjoin_induction with
    | mem x hx =>
      obtain ⟨i, rfl⟩ := hx
      rintro w ⟨k, hk⟩
      exact ⟨k + 1, by rw [fil_succ]; exact letter_mem_stp L hk i⟩
    | algebraMap r =>
      rintro w ⟨k, hk⟩
      refine ⟨k, ?_⟩
      simpa [Module.algebraMap_end_apply] using Submodule.smul_mem _ r hk
    | add x y _ _ hx hy =>
      intro w hw
      obtain ⟨k, hk⟩ := hx w hw
      obtain ⟨m, hm⟩ := hy w hw
      refine ⟨max k m, ?_⟩
      simpa using add_mem (fil_mono L S₀ (le_max_left k m) hk) (fil_mono L S₀ (le_max_right k m) hm)
    | mul x y _ _ hx hy =>
      intro w hw
      simpa using hx (y w) (hy w hw)
  exact key f ⟨0, hf⟩

end Abstract

section Pair

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) : Bool × Fin n × Fin n → Module.End ℂ V
  | (true, a, b) => F1 a b
  | (false, a, b) => F2 a b

theorem range_letters (F1 F2 : Fin n → Fin n → Module.End ℂ V) :
    Set.range (letters F1 F2) = {x | ∃ a b, x = F1 a b ∨ x = F2 a b} := by
  ext x
  constructor
  · rintro ⟨⟨_ | _, a, b⟩, rfl⟩
    · exact ⟨a, b, Or.inr rfl⟩
    · exact ⟨a, b, Or.inl rfl⟩
  · rintro ⟨a, b, rfl | rfl⟩
    · exact ⟨(true, a, b), rfl⟩
    · exact ⟨(false, a, b), rfl⟩

theorem gl_span (F1 F2 : Fin n → Fin n → Module.End ℂ V) (e : Bool) (E : Fin n → Fin n → Module.End ℂ V)
    (hE : ∀ a b, E a b = letters F1 F2 (e, a, b)) (a b c d : Fin n) :
    (if b = c then E a d else 0) - (if d = a then E c b else 0) ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  have hm : ∀ a b, E a b ∈ Submodule.span ℂ (Set.range (letters F1 F2)) := fun a b =>
    Submodule.subset_span ⟨(e, a, b), (hE a b).symm⟩
  refine sub_mem ?_ ?_
  · split_ifs
    · exact hm _ _
    · exact zero_mem _
  · split_ifs
    · exact hm _ _
    · exact zero_mem _

theorem comm_letters {F1 F2 : Fin n → Fin n → Module.End ℂ V} (h1 : Formalism.REAL.GlRel F1) (h2 : Formalism.REAL.GlRel F2)
    (hc : ∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) (a b : Fin n) (i : Bool × Fin n × Fin n) :
    kF F1 F2 a b * letters F1 F2 i - letters F1 F2 i * kF F1 F2 a b ∈
      Submodule.span ℂ (Set.range (letters F1 F2)) := by
  obtain ⟨_ | _, c, d⟩ := i
  · have h : kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b =
        (if b = c then F2 a d else 0) - (if d = a then F2 c b else 0) := by
      rw [← h2 a b c d]
      delta kF
      simp only [add_mul, mul_add, hc a b c d]
      abel
    change kF F1 F2 a b * F2 c d - F2 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 false F2 (fun _ _ => rfl) a b c d
  · have h : kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b =
        (if b = c then F1 a d else 0) - (if d = a then F1 c b else 0) := by
      rw [← h1 a b c d]
      delta kF
      simp only [add_mul, mul_add, hc c d a b]
      abel
    change kF F1 F2 a b * F1 c d - F1 c d * kF F1 F2 a b ∈ _
    rw [h]
    exact gl_span F1 F2 true F1 (fun _ _ => rfl) a b c d

end Pair

theorem cyclic_locFin : ∀ (n : ℕ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (F1 F2 : Fin n → Fin n → Module.End ℂ V), Formalism.REAL.GlRel F1 → Formalism.REAL.GlRel F2 →
    (∀ a b c d, F1 a b * F2 c d = F2 c d * F1 a b) → ∀ f : V, (∀ x : V, ∃ T ∈ alg F1 F2, T f = x) →
    ∀ S₀ : Submodule ℂ V, FiniteDimensional ℂ S₀ → f ∈ S₀ → (∀ a b, ∀ w ∈ S₀, kF F1 F2 a b w ∈ S₀) →
    ∀ x : V, ∃ S : Submodule ℂ V, FiniteDimensional ℂ S ∧ x ∈ S ∧ ∀ a b, ∀ w ∈ S, kF F1 F2 a b w ∈ S := by
  intro n V _ _ F1 F2 h1 h2 hc f hgen S₀ hfin hf hst x
  obtain ⟨T, hT, rfl⟩ := hgen x
  have hT' : T ∈ Algebra.adjoin ℂ (Set.range (letters F1 F2)) := by
    rw [range_letters]
    exact hT
  obtain ⟨k, hk⟩ := mem_fil_of_adjoin (letters F1 F2) S₀ hT' hf
  exact ⟨fil (letters F1 F2) S₀ k, fil_finite _ _ k, hk, fun a b =>
    fil_stable _ _ (comm_letters h1 h2 hc a b) (hst a b) k⟩

end GlobalTheory.CompanionTheory.ModelS.LocFin
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsMatrixCoefficientIntertwiner
section
noncomputable section

open MeasureTheory GlobalTheory.CompanionTheory.UnitaryFramesMetricPeriods PositivityTheory.RgHe.A
open scoped InnerProductSpace ComplexConjugate

namespace GlobalTheory.CompanionTheory.RgHeA.TMapPf

section Unitary

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] {A : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A]
  {ρ : Γ → (A →L[ℂ] A)}

theorem isU_inner (hU : IsU ρ) (g : Γ) (x y : A) : ⟪ρ g x, ρ g y⟫_ℂ = ⟪x, y⟫_ℂ :=
  (LinearIsometry.mk (ρ g).toLinearMap (hU.norm g)).inner_map_map x y

theorem isU_apply_inv (hU : IsU ρ) (g : Γ) (x : A) : ρ g (ρ g⁻¹ x) = x := by
  have h := hU.mul g g⁻¹
  rw [mul_inv_cancel, hU.one] at h
  have h2 := congrArg (fun T : A →L[ℂ] A => T x) h
  simpa using h2.symm

theorem isU_inner_left (hU : IsU ρ) (k : Γ) (x y : A) : ⟪ρ k x, y⟫_ℂ = ⟪x, ρ k⁻¹ y⟫_ℂ := by
  conv_lhs => rw [← isU_apply_inv hU k y]
  exact isU_inner hU k x _

end Unitary

theorem norm_integral_mul_sq_le {Γ : Type} [MeasurableSpace Γ] (ν : Measure Γ) (f g : Γ → ℂ) (hf : MemLp f 2 ν)
    (hg : MemLp g 2 ν) : ‖∫ x, f x * g x ∂ν‖ ^ 2 ≤ (∫ x, ‖f x‖ ^ 2 ∂ν) * ∫ x, ‖g x‖ ^ 2 ∂ν := by
  have h1 := integral_mul_norm_le_Lp_mul_Lq (μ := ν) (f := f) (g := g) (p := 2) (q := 2)
    Real.HolderConjugate.two_two (by simpa using hf) (by simpa using hg)
  have h0 : ‖∫ x, f x * g x ∂ν‖ ≤ ∫ x, ‖f x‖ * ‖g x‖ ∂ν := by
    simpa using norm_integral_le_integral_norm (μ := ν) (fun x => f x * g x)
  simp only [Real.rpow_two] at h1
  have hP : 0 ≤ ∫ x, ‖f x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  have hQ : 0 ≤ ∫ x, ‖g x‖ ^ 2 ∂ν := integral_nonneg fun _ => by positivity
  calc ‖∫ x, f x * g x ∂ν‖ ^ 2
      ≤ ((∫ x, ‖f x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ)) * (∫ x, ‖g x‖ ^ 2 ∂ν) ^ (1 / (2 : ℝ))) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (h0.trans h1) 2
    _ = _ := by
        rw [mul_pow, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow, Real.sq_sqrt hP, Real.sq_sqrt hQ]

section Main

variable {Γ : Type} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [LocallyCompactSpace Γ]
  [SecondCountableTopology Γ] [MeasurableSpace Γ] [BorelSpace Γ] (ν : Measure Γ) [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {A B : Type} [NormedAddCommGroup A] [InnerProductSpace ℂ A] [CompleteSpace A] [NormedAddCommGroup B]
  [InnerProductSpace ℂ B] [CompleteSpace B] {σ : Γ → (A →L[ℂ] A)} {ρ : Γ → (B →L[ℂ] B)} {d : ℝ}


omit [IsTopologicalGroup Γ] [LocallyCompactSpace Γ] [SecondCountableTopology Γ] [ν.IsHaarMeasure] [ν.IsMulRightInvariant] [CompleteSpace A] in
theorem coeff_sq (hσ : IsU σ) (hF : IsFd ν σ d) (w a : A) :
    MemLp (fun g => ⟪σ g w, a⟫_ℂ) 2 ν ∧ ∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν = ‖a‖ ^ 2 * ‖w‖ ^ 2 / d := by
  have key : ∀ g, ⟪a, σ g w⟫_ℂ * star ⟪a, σ g w⟫_ℂ = ((‖⟪σ g w, a⟫_ℂ‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_inner_symm]
  obtain ⟨h1, h2⟩ := hF.2 w a w a
  simp only [key] at h1 h2
  have h3 : Integrable (fun g => ‖⟪σ g w, a⟫_ℂ‖ ^ 2) ν := by
    exact h1.re.congr (ae_of_all _ fun g => Complex.ofReal_re _)
  have hc : Continuous fun g => ⟪σ g w, a⟫_ℂ := (hσ.cont w).inner continuous_const
  refine ⟨(memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 h3, ?_⟩
  have e : ∀ x : A, ⟪x, x⟫_ℂ = ((‖x‖ ^ 2 : ℝ) : ℂ) := fun x => by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [integral_complex_ofReal, e, e] at h2
  have h4 : ((∫ g, ‖⟪σ g w, a⟫_ℂ‖ ^ 2 ∂ν : ℝ) : ℂ) = ((‖a‖ ^ 2 * ‖w‖ ^ 2 / d : ℝ) : ℂ) := by
    rw [h2]; push_cast; ring
  exact_mod_cast h4

omit [CompleteSpace A] in
theorem form_facts (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) (b : B) (a : A) :
    Integrable (fun g => ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) ν ∧
      ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ^ 2 ≤
        ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖b‖ ^ 2) * (‖a‖ ^ 2 * ‖w‖ ^ 2 / d) := by
  obtain ⟨hb1, hb2⟩ := GlobalTheory.T.matrix_coefficient_integrable_square ν ρ hρ v hv b
  have hc : Continuous fun g => ⟪b, ρ g v⟫_ℂ := continuous_const.inner (hρ.cont v)
  have hφ : MemLp (fun g => ⟪b, ρ g v⟫_ℂ) 2 ν := (memLp_two_iff_integrable_sq_norm hc.aestronglyMeasurable).2 hb1
  obtain ⟨hψ, hψ2⟩ := coeff_sq ν hσ hF w a
  refine ⟨hφ.integrable_mul hψ, ?_⟩
  refine (norm_integral_mul_sq_le ν _ _ hφ hψ).trans ?_
  rw [hψ2]
  exact mul_le_mul_of_nonneg_right hb2 (div_nonneg (by positivity) hF.1.le)

theorem exists_matrix_coefficient_intertwiner (hρ : IsU ρ) (hσ : IsU σ) (hF : IsFd ν σ d) {v : B}
    (hv : Integrable (fun g => ⟪v, ρ g v⟫_ℂ) ν) (w : A) :
    ∃ T : B →L[ℂ] A, ∀ b a, ⟪T b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := by
  have hint := fun b a => (form_facts ν hρ hσ hF hv w b a).1
  have hM : 0 ≤ ∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν := integral_nonneg fun _ => norm_nonneg _
  obtain ⟨K, hK0, hbd⟩ : ∃ K : ℝ, 0 ≤ K ∧ ∀ b a, ‖∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν‖ ≤ K * ‖b‖ * ‖a‖ := by
    refine ⟨Real.sqrt ((∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d), Real.sqrt_nonneg _, fun b a => ?_⟩
    have hq : 0 ≤ (∫ g, ‖⟪v, ρ g v⟫_ℂ‖ ∂ν) * ‖w‖ ^ 2 / d := div_nonneg (by positivity) hF.1.le
    refine (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 ?_
    refine (form_facts ν hρ hσ hF hv w b a).2.trans (le_of_eq ?_)
    rw [mul_pow, mul_pow, Real.sq_sqrt hq]
    ring
  let L : B → (A →L[ℂ] ℂ) := fun b => LinearMap.mkContinuous
    { toFun := fun a => ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν
      map_add' := fun a a' => by
        rw [← integral_add (hint b a) (hint b a')]
        congr 1; ext g; rw [inner_add_right, mul_add]
      map_smul' := fun t a => by
        simp only [RingHom.id_apply, smul_eq_mul]
        rw [← integral_const_mul]
        congr 1; ext g; rw [inner_smul_right]; ring } (K * ‖b‖) (fun a => hbd b a)
  let Tf : B → A := fun b => (InnerProductSpace.toDual ℂ A).symm (L b)
  have hT : ∀ b a, ⟪Tf b, a⟫_ℂ = ∫ g, ⟪b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ ∂ν := fun b a => by
    simp only [Tf, InnerProductSpace.toDual_symm_apply]
    rfl
  have hTb : ∀ b, ‖Tf b‖ ≤ K * ‖b‖ := fun b => by
    have h1 := hbd b (Tf b)
    rw [← hT, inner_self_eq_norm_sq_to_K] at h1
    by_cases h0 : ‖Tf b‖ = 0
    · rw [h0]; positivity
    · have h2 : 0 < ‖Tf b‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      have h3 : ‖Tf b‖ * ‖Tf b‖ ≤ (K * ‖b‖) * ‖Tf b‖ := by
        simpa [sq] using h1
      exact le_of_mul_le_mul_right h3 h2
  refine ⟨LinearMap.mkContinuous
    { toFun := Tf
      map_add' := fun b b' => ext_inner_right ℂ fun a => by
        rw [inner_add_left, hT, hT, hT, ← integral_add (hint b a) (hint b' a)]
        congr 1; ext g; rw [inner_add_left, add_mul]
      map_smul' := fun t b => ext_inner_right ℂ fun a => by
        simp only [RingHom.id_apply]
        rw [inner_smul_left, hT, hT, ← integral_const_mul]
        congr 1; ext g; rw [inner_smul_left]; ring } K hTb, fun b a => ?_⟩
  exact hT b a

end Main

theorem tMap : TMap := by
  intro Γ _ _ _ _ _ _ _ ν _ _ A B _ _ _ _ _ _ σ ρ d hσ hρ hF v hv w c hc h
  obtain ⟨T, hT⟩ := exists_matrix_coefficient_intertwiner ν hρ hσ hF hv w
  have hk : ∀ k b, T (ρ k b) = σ k (T b) := fun k b => ext_inner_right ℂ fun a => by
    rw [hT, isU_inner_left hσ k, hT]
    refine (integral_mul_left_eq_self (μ := ν) (fun g => ⟪ρ k b, ρ g v⟫_ℂ * ⟪σ g w, a⟫_ℂ) k).symm.trans
      (integral_congr_ae (ae_of_all _ fun g => ?_))
    simp only [hρ.mul, hσ.mul, ContinuousLinearMap.mul_apply]
    rw [isU_inner hρ, isU_inner_left hσ]
  have hv' : T v = (c : ℂ) • w := ext_inner_right ℂ fun a => by
    rw [hT, inner_smul_left, Complex.conj_ofReal]
    have h1 := congrArg (starRingEnd ℂ) (h a)
    rw [← integral_conj] at h1
    simp only [map_mul, inner_conj_symm, Complex.conj_ofReal, Complex.star_def] at h1
    exact h1
  refine ⟨(c : ℂ)⁻¹ • T, fun g x => ?_, ?_⟩
  · simp [hk]
  · have hc' : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    rw [ContinuousLinearMap.smul_apply, hv', smul_smul, inv_mul_cancel₀ hc', one_smul]

end GlobalTheory.CompanionTheory.RgHeA.TMapPf
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsPermOfCntEq
section
open MvPolynomial

namespace GlobalTheory.CompanionTheory.Polarisation

noncomputable def cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : ι →₀ ℕ :=
  ∑ j, Finsupp.single (f j) 1

open Classical in
theorem cnt_apply {ι : Type} {m : ℕ} (f : Fin m → ι) (i : ι) :
    cnt f i = Fintype.card {j // f j = i} := by
  simp [cnt, Finsupp.finsetSum_apply, Finsupp.single_apply, Fintype.card_subtype]

theorem degree_cnt {ι : Type} {m : ℕ} (f : Fin m → ι) : (cnt f).degree = m := by
  classical
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cnt, map_sum]

theorem exists_perm_of_cnt_eq {ι : Type} {m : ℕ} {f g : Fin m → ι} (h : cnt f = cnt g) :
    ∃ σ : Equiv.Perm (Fin m), g = f ∘ σ := by
  classical
  have hc : ∀ i, Nonempty ({j // g j = i} ≃ {j // f j = i}) := fun i => by
    refine Fintype.card_eq.1 ?_
    rw [← cnt_apply, ← cnt_apply, h]
  let e : ∀ i, {j // g j = i} ≃ {j // f j = i} := fun i => (hc i).some
  refine ⟨Equiv.ofFiberEquiv e, ?_⟩
  funext j
  exact (Equiv.ofFiberEquiv_map e j).symm

theorem prod_X_eq {ι : Type} {m : ℕ} (f : Fin m → ι) (a : Fin m → ℝ) :
    ∏ j, (C (a j) * X (f j) : MvPolynomial ι ℝ) = monomial (cnt f) (∏ j, a j) := by
  classical
  have key : ∀ s : Finset (Fin m), ∏ j ∈ s, (C (a j) * X (f j) : MvPolynomial ι ℝ)
      = monomial (∑ j ∈ s, Finsupp.single (f j) 1) (∏ j ∈ s, a j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | insert x s hx ih =>
      rw [Finset.prod_insert hx, Finset.prod_insert hx, Finset.sum_insert hx, ih, X,
        C_mul_monomial, monomial_mul]
      simp
  exact key Finset.univ

theorem lin_pow {ι : Type} [Fintype ι] (n : ι → ℝ) (m : ℕ) :
    GlobalTheory.ArInt.lin n ^ m = ∑ f : Fin m → ι, monomial (cnt f) (∏ j, n (f j)) := by
  classical
  have h := Finset.prod_univ_sum (fun _ : Fin m => (Finset.univ : Finset ι))
    (fun _ i => (C (n i) * X i : MvPolynomial ι ℝ))
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.piFinset_univ] at h
  rw [GlobalTheory.ArInt.lin, h]
  exact Finset.sum_congr rfl fun f _ => prod_X_eq f (fun j => n (f j))


open Classical in
noncomputable def coef {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) : ℝ :=
  if h : ∃ f : Fin m → ι, cnt f = k then F h.choose else 0

theorem coef_cnt {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ)
    (hF : ∀ (f : Fin m → ι) (σ : Equiv.Perm (Fin m)), F (f ∘ σ) = F f) (f : Fin m → ι) :
    coef F (cnt f) = F f := by
  have h : ∃ g : Fin m → ι, cnt g = cnt f := ⟨f, rfl⟩
  obtain ⟨σ, hσ⟩ := exists_perm_of_cnt_eq h.choose_spec.symm
  rw [coef, dite_eq_left h, hσ, hF]

theorem coef_of_degree_ne {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) {k : ι →₀ ℕ}
    (hk : k.degree ≠ m) : coef F k = 0 := by
  refine dif_neg ?_
  rintro ⟨f, rfl⟩
  exact hk (degree_cnt f)

noncomputable def form {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) : MvPolynomial ι ℝ →ₗ[ℝ] ℝ :=
  (basisMonomials ι ℝ).constr ℝ (coef F)

theorem form_monomial {ι : Type} {m : ℕ} (F : (Fin m → ι) → ℝ) (k : ι →₀ ℕ) (a : ℝ) :
    form F (monomial k a) = a * coef F k := by
  have h1 : (monomial k a : MvPolynomial ι ℝ) = a • basisMonomials ι ℝ k := by
    simp [coe_basisMonomials, smul_monomial]
  rw [h1, map_smul, form, Module.Basis.constr_basis, smul_eq_mul]

theorem exists_form (ι : Type) [Fintype ι] (D : ℕ) (F : (Fin (D + 1) → ι) → ℝ)
    (hF : ∀ (f : Fin (D + 1) → ι) (σ : Equiv.Perm (Fin (D + 1))), F (f ∘ σ) = F f) :
    ∃ Φ : MvPolynomial ι ℝ →ₗ[ℝ] ℝ,
      (∀ n : ι → ℝ, Φ (GlobalTheory.ArInt.lin n ^ (D + 1)) = ∑ f : Fin (D + 1) → ι, (∏ j, n (f j)) * F f) ∧
      ∀ (P : MvPolynomial ι ℝ) (d : ℕ), d ≠ D + 1 → P.IsHomogeneous d → Φ P = 0 := by
  refine ⟨form F, fun n => ?_, fun P d hd hP => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [lin_pow, map_sum]
      exact Finset.sum_congr rfl fun f _ => by rw [form_monomial, coef_cnt F hF]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [P.as_sum, map_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hdeg : k.degree = d := by
        have := hP (mem_support_iff.1 hk)
        rw [Finsupp.degree_eq_weight_one]; exact this
      rw [form_monomial, coef_of_degree_ne F (by rw [hdeg]; exact hd), mul_zero]

end GlobalTheory.CompanionTheory.Polarisation
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FixedEqFixedVectors
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.BZMir.Whit

namespace GlobalTheory.CompanionTheory.AdmDict

theorem fixed_eq_fixedVectors {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (K : Subgroup G) :
    GlobalTheory.PRep.fixed ρ K = GroundTheory.Automorphic.fixedVectors ρ K := by
  ext v
  constructor
  · intro hv h hh
    simpa using hv ⟨h, hh⟩
  · intro hv h
    simpa using hv h h.2

theorem isAdmissible_iff : ∀ {G V : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V), GlobalTheory.PRep.IsAdmissible ρ ↔ GroundTheory.Automorphic.IsAdmissible ρ := by
  intro G V _ _ _ _ _ ρ
  have hs : GlobalTheory.PRep.IsSmooth ρ ↔ GroundTheory.Automorphic.IsSmooth ρ := Iff.rfl
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨hs.1 h1, fun K hc ho => ?_⟩
    have := h2 K ho hc
    rwa [fixed_eq_fixedVectors] at this
  · rintro ⟨h1, h2⟩
    refine ⟨hs.2 h1, fun K ho hc => ?_⟩
    rw [fixed_eq_fixedVectors]
    exact h2 K hc ho

end GlobalTheory.CompanionTheory.AdmDict
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacquetMultiplicitySubquotientLeStatement
section
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.Seg
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.jacquet_multiplicity_subquotient_le : ∀ {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {h N : ℕ} (y : Fin h → IrrGL (k := k)) (hy : ∑ a, (y a).1 = N) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ (GL (Fin N) k) V) (P : Representation ℂ (GL (Fin N) k) W) (hP : IsSmooth P) (h : IsSubquotient π P), jm y hy π ≤ jm y hy P := by
  first | exact @GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | exact GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient | (intros; apply GlobalTheory.CompanionTheory.JmMono.jm_le_of_isSubquotient <;> assumption)
end

