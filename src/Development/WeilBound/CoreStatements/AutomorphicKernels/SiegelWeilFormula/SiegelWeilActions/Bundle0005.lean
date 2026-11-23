module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0004
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Bundle0003
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnfoldingCompactness.MatrixOfUnipotentFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AdelicFormCongruences.ExistsGlCol

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.Imports
section

end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.LinearFormAdelic
section
set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Act.C5.Meas

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def linearFormAdelic (δ : E) : AE F E →ₗ[AF F] AF F :=
  (Algebra.TensorProduct.rid F (AF F) (AF F)).toLinearMap ∘ₗ
    LinearMap.baseChange (AF F) (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1)

theorem inclR_eq' (x : E) : inclR (F := F) (AF F) x = (1 : AF F) ⊗ₜ[F] x := rfl

theorem sigma_invol' {B : Base F E} (hB : B.IsGood σ) (x : E) : σ (σ x) = x := by
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  apply τ.injective
  rw [hB.cm.2.2.2 τ, hB.cm.2.2.2 τ, star_star]

theorem exists_ne_sigma {B : Base F E} (hB : B.IsGood σ) : ∃ x : E, σ x ≠ x := by
  by_contra hne
  push Not at hne
  obtain ⟨τ⟩ := (inferInstance : Nonempty (E →+* ℂ))
  have hc : (NumberField.InfinitePlace.mk τ).IsComplex := hB.cm.2.1.isComplex _
  rw [NumberField.InfinitePlace.isComplex_mk_iff] at hc
  apply hc
  show NumberField.ComplexEmbedding.conjugate τ = τ
  ext x
  rw [NumberField.ComplexEmbedding.conjugate_coe_eq]
  show star (τ x) = τ x
  rw [← hB.cm.2.2.2 τ x, hne x]

theorem fixed_mem {B : Base F E} (hB : B.IsGood σ) {q : E} (hq : σ q = q) : ∃ f : F, algebraMap F E f = q := by
  by_contra hne
  push Not at hne
  have hli : LinearIndependent F ![(1 : E), q] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      refine ⟨?_, rfl⟩
      simpa using hst
    · exfalso
      apply hne (-(s / t))
      have h1 : t • q = -(s • (1 : E)) := eq_neg_of_add_eq_zero_right hst
      have h2 : q = t⁻¹ • -(s • (1 : E)) := by rw [← h1, smul_smul, inv_mul_cancel₀ ht, one_smul]
      rw [h2, Algebra.algebraMap_eq_smul_one, smul_neg, smul_smul, neg_smul, div_eq_inv_mul]
  have hcard : Fintype.card (Fin 2) = Module.finrank F E := by rw [hB.cm.2.2.1]; rfl
  have hspan := hli.span_eq_top_of_card_eq_finrank hcard
  have hσid : σ.toLinearMap = LinearMap.id := by
    refine LinearMap.ext_on_range hspan fun i => ?_
    fin_cases i
    · simp
    · simpa using hq
  obtain ⟨x, hx⟩ := exists_ne_sigma hB
  exact hx (by simpa using LinearMap.congr_fun hσid x)

theorem eig_line {B : Base F E} (hB : B.IsGood σ) {k : ℤ} (hk : k * k = 1) {δ y : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = (k : E) * δ) (hy : σ y = (k : E) * y) : ∃ f : F, y = f • δ := by
  have hk0 : (k : E) ≠ 0 := by
    intro h
    have h1 : ((k * k : ℤ) : E) = 1 := by rw [hk]; simp
    rw [Int.cast_mul, h, zero_mul] at h1
    exact zero_ne_one h1
  have hfix : σ (y / δ) = y / δ := by
    rw [map_div₀, hy, hδ, mul_div_mul_left _ _ hk0]
  obtain ⟨f, hf⟩ := fixed_mem hB hfix
  refine ⟨f, ?_⟩
  rw [Algebra.smul_def, hf, div_mul_cancel₀ _ hδ0]

theorem ell_spec {δ : E} (hδ0 : δ ≠ 0) : (Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) δ = 1 := by
  have hex : ∃ ℓ : E →ₗ[F] F, δ ≠ 0 → ℓ δ = 1 := by
    have : ¬ ∀ φ : Module.Dual F E, φ δ = 0 := fun h => hδ0 ((Module.forall_dual_apply_eq_zero_iff F δ).1 h)
    push Not at this
    obtain ⟨φ, hφ⟩ := this
    exact ⟨(φ δ)⁻¹ • φ, fun _ => by simp [hφ]⟩
  exact Classical.epsilon_spec hex hδ0

theorem ellA_smul_inclR {δ : E} (hδ0 : δ ≠ 0) (a : AF F) : linearFormAdelic (F := F) δ (a • inclR (F := F) (AF F) δ) = a := by
  rw [inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
  simp [linearFormAdelic, LinearMap.baseChange_tmul, ell_spec hδ0]

theorem ellA_inclR (δ : E) (e : E) : ∃ f : F, linearFormAdelic (F := F) δ (inclR (F := F) (AF F) e) = algebraMap F (AF F) f := by
  refine ⟨(Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1) e, ?_⟩
  rw [inclR_eq']
  simp [linearFormAdelic, LinearMap.baseChange_tmul, Algebra.algebraMap_eq_smul_one]

theorem eig_AE {B : Base F E} (hB : B.IsGood σ) {k : ℤ} (hk : k * k = 1) {δ : E} (hδ0 : δ ≠ 0)
    (hδ : σ δ = (k : E) * δ) {z : AE F E} (hz : cA σ z = (k : AE F E) * z) :
    z = linearFormAdelic (F := F) δ z • inclR (F := F) (AF F) δ := by
  have hinv := sigma_invol' hB
  set ℓ : E →ₗ[F] F := Classical.epsilon fun ℓ : E →ₗ[F] F => δ ≠ 0 → ℓ δ = 1 with hℓdef
  have hℓ : ℓ δ = 1 := ell_spec hδ0
  have hsm : ∀ x : E, (k : F) • x = (k : E) * x := fun x => by rw [Algebra.smul_def, map_intCast]
  have hkk : (k : F) * k = 1 := by exact_mod_cast hk
  let g : E →ₗ[F] E := ℓ.smulRight δ
  let p : E →ₗ[F] E := LinearMap.id + (k : F) • σ.toLinearMap
  have hzero : (LinearMap.id - g) ∘ₗ p = 0 := by
    ext e
    have hw : σ (e + (k : F) • σ e) = (k : E) * (e + (k : F) • σ e) := by
      rw [hsm (σ e), map_add (f := _), map_mul, map_intCast, hinv, mul_add, ← mul_assoc, ← Int.cast_mul, hk, Int.cast_one, one_mul,
        add_comm]
    obtain ⟨f, hf⟩ := eig_line hB hk hδ0 hδ hw
    show (e + (k : F) • σ e) - ℓ (e + (k : F) • σ e) • δ = 0
    rw [hf, map_smul, hℓ, smul_eq_mul, mul_one, sub_self]
  have hbc : ∀ w : AE F E, (LinearMap.id - g).baseChange (AF F) w = w - linearFormAdelic (F := F) δ w • inclR (F := F) (AF F) δ := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      rw [LinearMap.baseChange_tmul, inclR_eq', TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      simp [linearFormAdelic, g, LinearMap.baseChange_tmul, TensorProduct.tmul_sub, TensorProduct.smul_tmul]
      rfl
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, map_add (f := _), add_smul]
      abel
  have hpc : ∀ w : AE F E, p.baseChange (AF F) w = w + (k : F) • cA σ w := by
    intro w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul a e =>
      simp [p, cA, LinearMap.baseChange_tmul]
    | add x y hx hy =>
      rw [map_add (f := _), hx, hy, map_add (f := _), smul_add]
      abel
  have hkz : (k : F) • cA σ z = z := by
    rw [hz, show ((k : ℤ) : AE F E) = algebraMap F (AE F E) (k : F) by rw [map_intCast], ← Algebra.smul_def, smul_smul, hkk,
      one_smul]
  have h2 : p.baseChange (AF F) z = (2 : F) • z := by
    rw [hpc, hkz, two_smul]
  have h0 : (LinearMap.id - g).baseChange (AF F) (p.baseChange (AF F) z) = 0 := by
    rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp, hzero, LinearMap.baseChange_zero, LinearMap.zero_apply]
  rw [h2, LinearMap.map_smul_of_tower, hbc] at h0
  exact (sub_eq_zero.1 ((smul_eq_zero.1 h0).resolve_left two_ne_zero))

theorem continuous_ellA (δ : E) : Continuous (linearFormAdelic (F := F) (E := E) δ) :=
  IsModuleTopology.continuous_of_linearMap (R := AF F) (linearFormAdelic (F := F) (E := E) δ)

end PositivityTheory.SiegelWeilFormula.Act.C5.Meas

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelWeilActions.SplitPrimeIdeals
section
noncomputable section

open scoped TensorProduct NNReal Matrix Classical ComplexOrder
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)

set_option linter.unusedSectionVars false

namespace PositivityTheory.SiegelWeilFormula.Act.C4

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

variable {d : SD σ} (L : LD d)

def emS : Fin L.n ⊕ Fin L.n → Fin d.n ⊕ Fin d.n := Sum.map L.em L.em

def padM (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) :
    Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) :=
  fun r c => if h : (∃ a, emS L a = r) ∧ ∃ a, emS L a = c then M h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) r c

theorem emS_inj : Function.Injective (emS L) := Sum.map_injective.2 ⟨L.inj, L.inj⟩

theorem padM_emS (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (a a' : Fin L.n ⊕ Fin L.n) :
    padM L M (emS L a) (emS L a') = M a a' := by
  have h : (∃ x, emS L x = emS L a) ∧ ∃ x, emS L x = emS L a' := ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩
  simp only [padM]
  rw [dite_eq_left h, emS_inj L h.1.choose_spec, emS_inj L h.2.choose_spec]

theorem padM_out_row (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) {r : Fin d.n ⊕ Fin d.n}
    (hr : ¬ ∃ a, emS L a = r) (c : Fin d.n ⊕ Fin d.n) : padM L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [padM]
  rw [dite_eq_right (fun h => hr h.1)]

theorem padM_out_col (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (r : Fin d.n ⊕ Fin d.n)
    {c : Fin d.n ⊕ Fin d.n} (hc : ¬ ∃ a, emS L a = c) : padM L M r c = (1 : Matrix _ _ (AE F E)) r c := by
  simp only [padM]
  rw [dite_eq_right (fun h => hc h.2)]

theorem mem_out {r : Fin d.n ⊕ Fin d.n} (h : ¬ ∃ a, emS L a = r) :
    r ∈ ({Sum.inl L.i₀, Sum.inr L.i₀} : Set (Fin d.n ⊕ Fin d.n)) := by
  rcases r with i | i
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inl a, by simp [emS, ha]⟩).elim
  · by_cases hi : i = L.i₀
    · simp [hi]
    · obtain ⟨a, ha⟩ := (L.rng i).1 hi
      exact (h ⟨Sum.inr a, by simp [emS, ha]⟩).elim

theorem em_ne (a : Fin L.n) : L.em a ≠ L.i₀ := (L.rng (L.em a)).2 ⟨a, rfl⟩

theorem not_inl (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, emS L a = Sum.inl i := by
  rintro ⟨a | a, ha⟩
  · simp only [emS, Sum.map_inl, Sum.inl.injEq] at ha
    exact em_ne L a (ha.trans hi)
  · simp [emS] at ha

theorem not_inr (i : Fin d.n) (hi : i = L.i₀) : ¬ ∃ a, emS L a = Sum.inr i := by
  rintro ⟨a | a, ha⟩
  · simp [emS] at ha
  · simp only [emS, Sum.map_inr, Sum.inr.injEq] at ha
    exact em_ne L a (ha.trans hi)

theorem inFrame_j (g : G2 σ L.Y) : inFrame d.b (L.j g) = padM L (inFrame L.b g) := by
  ext r c
  by_cases h : (∃ a, emS L a = r) ∧ ∃ a, emS L a = c
  · obtain ⟨⟨a, rfl⟩, ⟨a', rfl⟩⟩ := h
    rw [padM_emS]
    have := congrFun (congrFun (L.j_in g) a) a'
    simpa [Matrix.submatrix_apply, emS] using this
  · rcases not_and_or.1 h with h1 | h1
    · rw [padM_out_row L _ h1]
      exact (L.j_out g r (mem_out L h1) c).1
    · rw [padM_out_col L _ r h1]
      exact (L.j_out g c (mem_out L h1) r).2

theorem sub_mem_nA (β : nA σ d.Y d.b) : β.1.submatrix L.em L.em ∈ nA σ L.Y L.b := by
  obtain ⟨⟨ε, hε⟩, -⟩ := d.ok.frame
  obtain ⟨⟨ε', hε'⟩, -⟩ := L.ok.frame
  have hee : ε = ε' := Afc.eps_eq L hε hε'
  subst hee
  rw [kunf.mem_nA_iff hε']
  have h1 : β.1 ∈ kfour.nCond σ d.n ε := (kunf.mem_nA_iff hε β.1).1 β.2
  exact Afc.sub_nCond (σ := σ) L.em β.1 h1

def prj : nA σ d.Y d.b →+ nA σ L.Y L.b where
  toFun β := ⟨β.1.submatrix L.em L.em, sub_mem_nA L β⟩
  map_zero' := by
    apply Subtype.ext
    rfl
  map_add' β β' := by
    apply Subtype.ext
    rfl

theorem prj_val (β : nA σ d.Y d.b) : (prj L β).1 = β.1.submatrix L.em L.em := rfl

theorem continuous_prj : Continuous (prj L) := by
  refine Continuous.subtype_mk ?_ _
  exact continuous_subtype_val.matrix_submatrix L.em L.em

theorem pad_matrix_lower_block (M : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) (AE F E)) (hM : M.toBlocks₂₁ = 0) :
    (padM L M).toBlocks₂₁ = 0 := by
  ext i k
  simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply]
  by_cases hi : i = L.i₀
  · rw [padM_out_row L M (not_inr L i hi)]
    simp [Matrix.one_apply]
  · by_cases hk : k = L.i₀
    · rw [padM_out_col L M _ (not_inl L k hk)]
      simp [Matrix.one_apply]
    · obtain ⟨a, rfl⟩ := (L.rng i).1 hi
      obtain ⟨a', rfl⟩ := (L.rng k).1 hk
      have h1 := padM_emS L M (Sum.inr a) (Sum.inl a')
      simp only [emS, Sum.map_inr, Sum.map_inl] at h1
      rw [h1]
      have h2 := congrFun (congrFun hM a) a'
      simpa [Matrix.toBlocks₂₁] using h2

theorem upper_block_mul_of_lower_zero {k : ℕ} {P Q : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (AE F E)} (hQ : Q.toBlocks₂₁ = 0)
    (h : P * Q = 1) : P.toBlocks₁₁ * Q.toBlocks₁₁ = 1 := by
  have h1 := congrArg Matrix.toBlocks₁₁ h
  rw [← Matrix.fromBlocks_toBlocks P, ← Matrix.fromBlocks_toBlocks Q, Matrix.fromBlocks_multiply, hQ] at h1
  have h2 : (1 : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) (AE F E)).toBlocks₁₁ = 1 := by
    ext i j; simp [Matrix.toBlocks₁₁, Matrix.one_apply]
  simpa [h2] using h1

theorem lower_block_embedded_parabolic {x : G2 σ L.Y} (hx : ∃ t, IsPar x t) : (inFrame d.b (L.j x)).toBlocks₂₁ = 0 := by
  obtain ⟨t, ht⟩ := hx
  obtain ⟨-, t₀, ht₀⟩ := L.ok.frame
  rw [inFrame_j]
  exact pad_matrix_lower_block L _ ((kunf.isPar_frame ht₀ x t).1 ht).1

theorem j_par {g : G2 σ L.Y} (h : g ∈ par2 σ L.Y) : L.j g ∈ par2 σ d.Y := by
  obtain ⟨t, ht⟩ := mem_parabolic_GL2_iff.1 h
  obtain ⟨-, t₁, ht₁⟩ := d.ok.frame
  set P := inFrame d.b (L.j g)
  set Q := inFrame d.b (L.j g⁻¹)
  have hP : P.toBlocks₂₁ = 0 := lower_block_embedded_parabolic L ⟨t, ht⟩
  have hQ : Q.toBlocks₂₁ = 0 := lower_block_embedded_parabolic L ⟨t⁻¹, ht.inv⟩
  have hPQ : P * Q = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, mul_inv_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have hQP : Q * P = 1 := by
    rw [← GlobalTheory.EisBL.DoubledParabolic.inFrame_mul, ← map_mul, inv_mul_cancel, map_one, GlobalTheory.EisBL.DoubledParabolic.inFrame_one]
  have e1 := upper_block_mul_of_lower_zero hQ hPQ
  have e2 := upper_block_mul_of_lower_zero hP hQP
  set T0 := incM F t₁.1
  set Ti := incM F (t₁⁻¹).1
  have hT : T0 * Ti = 1 := by
    show incM F t₁.1 * incM F (t₁⁻¹).1 = 1
    rw [← kunf.incM_mul', Units.mul_inv]; ext i j; simp [incM, Matrix.one_apply]
  have hT' : Ti * T0 = 1 := by
    show incM F (t₁⁻¹).1 * incM F t₁.1 = 1
    rw [← kunf.incM_mul', Units.inv_mul]; ext i j; simp [incM, Matrix.one_apply]
  let t' : GL (Fin d.n) (AE F E) := ⟨T0 * P.toBlocks₁₁ * Ti, T0 * Q.toBlocks₁₁ * Ti, by
      calc T0 * P.toBlocks₁₁ * Ti * (T0 * Q.toBlocks₁₁ * Ti) = T0 * (P.toBlocks₁₁ * (Ti * T0) * Q.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e1, Matrix.mul_one, hT], by
      calc T0 * Q.toBlocks₁₁ * Ti * (T0 * P.toBlocks₁₁ * Ti) = T0 * (Q.toBlocks₁₁ * (Ti * T0) * P.toBlocks₁₁) * Ti := by
            simp only [Matrix.mul_assoc]
        _ = 1 := by rw [hT', Matrix.mul_one, e2, Matrix.mul_one, hT]⟩
  exact mem_parabolic_GL2_iff.2 ⟨t', (kunf.isPar_frame ht₁ (L.j g) t').2 ⟨hP, rfl⟩⟩

def padE (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E :=
  fun r c => if h : (∃ a, emS L a = r) ∧ ∃ a, emS L a = c then N h.1.choose h.2.choose
    else (1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) E) r c

theorem padM_incM (N : Matrix (Fin L.n ⊕ Fin L.n) (Fin L.n ⊕ Fin L.n) E) : padM L (incM F N) = incM F (padE L N) := by
  ext r c
  simp only [padM, padE, incM, Matrix.map_apply]
  split_ifs with h
  · rfl
  · rw [Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp

theorem j_rat {g : G2 σ L.Y} (h : g ∈ rat2 σ L.Y) : L.j g ∈ rat2 σ d.Y := by
  obtain ⟨γ, hγ⟩ := Subgroup.mem_subgroupOf.1 h
  have hm : mat2 g = incM F γ.1 := by
    show g.1.1 = _
    rw [← hγ]
    rfl
  have hf : inFrame L.b g = incM F ((L.b⁻¹).1 * γ.1 * L.b.1) := by
    rw [kunf.incM_mul', kunf.incM_mul', ← hm]
    rfl
  refine kunf.rat_of_inFrame (b := d.b) (M := padE L ((L.b⁻¹).1 * γ.1 * L.b.1)) ?_
  rw [inFrame_j, hf, padM_incM]

end PositivityTheory.SiegelWeilFormula.Act.C4

end
end

