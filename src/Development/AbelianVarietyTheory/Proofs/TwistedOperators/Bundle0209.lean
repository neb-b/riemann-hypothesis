module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0190
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0192
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0195
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0185
public import Formalism.PeriodIntegrals.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittSmallGroupEmbeddingMemPointwiseStabilizerIso
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsMulRightInvariantOfFundamentalDomain
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0202
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedNFlag
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteLevelDatumClasses
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LiftLevel

def vmvBil (E : Type) [Field E] [NumberField E] (n r : ℕ) :
    (Fin n → E) →ₗ[𝓞 E] (Fin r → E) →ₗ[𝓞 E] Matrix (Fin n) (Fin r) E :=
  LinearMap.mk₂ (𝓞 E) (fun v u => vecMulVec v u)
    (fun v v' u => by ext i j; simp [vecMulVec, add_mul])
    (fun a v u => by ext i j; simp [vecMulVec, smul_mul_assoc])
    (fun v u u' => by ext i j; simp [vecMulVec, mul_add])
    (fun a v u => by ext i j; simp [vecMulVec, mul_smul_comm])

theorem tens_quot_finite {E : Type} [Field E] [NumberField E] {n r : ℕ} (Λ : Lt E n) (L : Lt E r)
    (hΛ : Λ.FG) (hL : L.FG) (𝔞 𝔪 : Ideal (𝓞 E)) (hm : 𝔪 ≠ ⊥) :
    Finite (tens Λ (𝔞 • L) ⧸ (tens Λ ((𝔞 * 𝔪) • L)).addSubgroupOf (tens Λ (𝔞 • L))) := by
  set A := tens Λ (𝔞 • L) with hA
  set B := tens Λ ((𝔞 * 𝔪) • L) with hB
  have hM : (Submodule.map₂ (vmvBil E n r) Λ L).FG := hΛ.map₂ _ hL
  have hMZ : ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).FG := hM.restrictScalars
  have hle : A.toIntSubmodule ≤ (Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ := by
    intro x hx
    have hsub : A ≤ ((Submodule.map₂ (vmvBil E n r) Λ L).restrictScalars ℤ).toAddSubgroup := by
      rw [hA, tens, AddSubgroup.closure_le]
      rintro y ⟨v, hv, u, hu, rfl⟩
      exact Submodule.apply_mem_map₂ (vmvBil E n r) hv (Submodule.smul_le_right hu)
    exact hsub hx
  have hAfg : A.toIntSubmodule.FG :=
    (isNoetherian_submodule.mp (isNoetherian_of_fg_of_noetherian _ hMZ)) _ hle
  haveI : AddGroup.FG A := by
    have : Module.Finite ℤ A.toIntSubmodule := Module.Finite.iff_fg.mpr hAfg
    exact (Module.Finite.iff_addGroup_fg).mp this
  set N := Ideal.absNorm 𝔪 with hN
  have hNpos : 0 < N := Nat.pos_of_ne_zero (fun h => hm (Ideal.absNorm_eq_zero_iff.mp h))
  have hNA : ∀ x ∈ A, N • x ∈ B := by
    intro x hx
    induction hx using AddSubgroup.closure_induction with
    | mem y hy =>
      obtain ⟨v, hv, u, hu, rfl⟩ := hy
      apply AddSubgroup.subset_closure
      refine ⟨v, hv, N • u, ?_, ?_⟩
      · have h1 : ((N : 𝓞 E)) • u ∈ 𝔪 • (𝔞 • L) := Submodule.smul_mem_smul (Ideal.absNorm_mem 𝔪) hu
        rw [← Submodule.mul_smul, mul_comm] at h1
        rwa [← Nat.cast_smul_eq_nsmul (𝓞 E)]
      · ext i j; simp [vecMulVec]; ring
    | zero => simp
    | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
    | neg x _ hx => rw [smul_neg]; exact neg_mem hx
  haveI : AddGroup.FG (A ⧸ B.addSubgroupOf A) := AddGroup.fg_of_surjective (QuotientAddGroup.mk'_surjective _)
  apply AddCommGroup.finite_of_fg_torsion
  intro q
  induction q using QuotientAddGroup.induction_on with
  | H x =>
    refine isOfFinAddOrder_iff_nsmul_eq_zero.mpr ⟨N, hNpos, ?_⟩
    rw [← QuotientAddGroup.mk_nsmul, QuotientAddGroup.eq_zero_iff, AddSubgroup.mem_addSubgroupOf]
    simpa using hNA x x.2

theorem lvCls_finite : ∀ (D : D7) (S T : HSp D) (C : Ctx S T) (Lv : GlobalTheory.SW.Level C.X), Finite (GlobalTheory.LiftLevel.LvCls C Lv) := by
  intro D S T C Lv
  exact tens_quot_finite _ _ (Submodule.fg_span (Set.finite_range _)) C.X.Λ_fg _ _ Lv.ne_bot

end GlobalTheory.LiftLevel

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTorusWeightsFiniteDimensionalSubspace
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.TorusWtFin

open Complex

noncomputable abbrev dg {n : ℕ} (θ : Fin n → ℝ) : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))

lemma diag_mem (n : ℕ) (ε : Fin n → Bool) (θ : Fin n → ℝ) : dg θ ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    rw [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal,
      ← Matrix.diagonal_one]
    congr 1
    funext i
    simp only [Pi.star_apply, Complex.star_def, ← Complex.exp_conj, ← Complex.exp_add]
    simp [Complex.conj_ofReal]
  · unfold Formalism.REAL.Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

lemma sum_single {n : ℕ} (μ : Fin n → ℝ) (a : Fin n) (c : ℝ) :
    (∑ b, μ b * (Pi.single a c : Fin n → ℝ) b) = μ a * c := by
  simp [Pi.single_apply]

lemma wt_int {n : ℕ} (ε : Fin n → Bool) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) {μ : Fin n → ℝ} {v : H} (hv : v ≠ 0)
    (hw : Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v) (a : Fin n) : ∃ k : ℤ, μ a = k := by
  have h1 := hw (Pi.single a (2 * Real.pi)) (diag_mem n ε _)
  have h0 := hw 0 (diag_mem n ε _)
  change ρ (dg _) v = _ at h1 h0
  have hD : dg (Pi.single a (2 * Real.pi) : Fin n → ℝ) = dg (0 : Fin n → ℝ) := by
    unfold dg
    congr 1
    funext b
    by_cases hb : b = a
    · subst hb
      simp only [Pi.single_eq_same, Pi.zero_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero]
      push_cast
      exact Complex.exp_two_pi_mul_I
    · simp [Pi.single_apply, hb]
  rw [sum_single] at h1
  rw [hD, h0] at h1
  simp only [Pi.zero_apply, mul_zero, Finset.sum_const_zero, Complex.ofReal_zero, zero_mul,
    Complex.exp_zero, one_smul] at h1
  have h2 : (Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) - 1) • v = 0 := by
    rw [sub_smul, one_smul, ← h1, sub_self]
  have h3 : Complex.exp (((μ a * (2 * Real.pi) : ℝ) : ℂ) * Complex.I) = 1 := by
    rcases smul_eq_zero.1 h2 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv
  obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.1 h3
  refine ⟨k, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h4 : ((μ a : ℝ) : ℂ) = (k : ℂ) := by
    have := hk
    push_cast at this
    have hI : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by simp [hpi, Complex.I_ne_zero]
    apply mul_right_cancel₀ hI
    linear_combination this
  exact_mod_cast h4

lemma exp_injOn : Set.InjOn (fun x : ℝ => Complex.exp ((x : ℂ) * Complex.I)) {x | ∃ k : ℤ, x = k} := by
  rintro x ⟨k, rfl⟩ y ⟨k', rfl⟩ h
  simp only at h
  have h1 : Complex.exp ((((k - k' : ℤ) : ℝ) : ℂ) * Complex.I) = 1 := by
    have h' : Complex.exp ((k : ℂ) * Complex.I) = Complex.exp ((k' : ℂ) * Complex.I) := by
      exact_mod_cast h
    push_cast
    rw [sub_mul, Complex.exp_sub, h', div_self (Complex.exp_ne_zero _)]
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 h1
  have hm' : (((k - k' : ℤ) : ℝ) : ℂ) = ((2 * m * Real.pi : ℝ) : ℂ) := by
    push_cast
    apply mul_right_cancel₀ Complex.I_ne_zero
    push_cast at hm
    linear_combination hm
  have hm'' : ((k - k' : ℤ) : ℝ) = ((2 * m : ℤ) : ℝ) * Real.pi := by
    have := Complex.ofReal_injective hm'
    push_cast at this ⊢
    linarith
  by_cases h0 : (2 * m : ℤ) = 0
  · rw [h0] at hm''
    simp only [Int.cast_zero, zero_mul] at hm''
    have : (k - k' : ℤ) = 0 := by exact_mod_cast hm''
    have : k = k' := by omega
    rw [this]
  · exact absurd hm''.symm ((irrational_pi.intCast_mul h0).ne_int _)

theorem finite_weights : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S : Submodule ℂ H), FiniteDimensional ℂ S → ∃ F : Finset (Fin n → ℝ), ∀ (μ : Fin n → ℝ) (v : H), v ∈ S → v ≠ 0 → Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v → μ ∈ F := by
  intro n ε H _ _ ρ S hS
  let W : Set (Fin n → ℝ) := {μ | ∃ v ∈ S, v ≠ 0 ∧ Formalism.MainNotions.S.IsWtOn (Formalism.REAL.Kset ε) ρ μ v}
  suffices hW : W.Finite by
    exact ⟨hW.toFinset, fun μ v hv h0 hw => hW.mem_toFinset.2 ⟨v, hv, h0, hw⟩⟩

  let T : Fin n → Module.End ℂ H := fun a => (ρ (dg (Pi.single a (1 : ℝ)))).toLinearMap
  let C : Fin n → Set ℂ := fun a => {c | ∃ v ∈ S, v ≠ 0 ∧ T a v = c • v}
  have hC : ∀ a, (C a).Finite := by
    intro a
    have hx : ∀ c : C a, ∃ v : S, (v : H) ≠ 0 ∧ T a v = (c : ℂ) • (v : H) := fun c => by
      obtain ⟨v, hvS, hv0, hv⟩ := c.2
      exact ⟨⟨v, hvS⟩, hv0, hv⟩
    choose xs hxs using hx
    have hli : LinearIndependent ℂ (fun c : C a => ((xs c : S) : H)) :=
      (T a).eigenvectors_linearIndependent (C a) (fun c => (xs c : H))
        (fun c => ⟨Module.End.mem_eigenspace_iff.2 (hxs c).2, (hxs c).1⟩)
    have hli' : LinearIndependent ℂ xs := LinearIndependent.of_comp S.subtype hli
    have := hli'.finite
    exact Set.finite_coe_iff.1 this
  let Z : Fin n → Set ℝ := fun a => {x | (∃ k : ℤ, x = k) ∧ Complex.exp ((x : ℂ) * Complex.I) ∈ C a}
  have hZ : ∀ a, (Z a).Finite := by
    intro a
    refine Set.Finite.of_finite_image ((hC a).subset ?_) (exp_injOn.mono fun x hx => hx.1)
    rintro _ ⟨x, hx, rfl⟩
    exact hx.2
  refine (Set.Finite.pi hZ).subset ?_
  rintro μ ⟨v, hvS, hv0, hw⟩ a _
  refine ⟨wt_int ε ρ hv0 hw a, v, hvS, hv0, ?_⟩
  have h := hw (Pi.single a (1 : ℝ)) (diag_mem n ε _)
  rw [sum_single, mul_one] at h
  exact h

end GlobalTheory.TorusWtFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVacuaSmoothFamilyComplexGaussians
section
open MeasureTheory

namespace GlobalTheory.FockFamily

theorem fock_vacua_family : ∀ {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] (β : V →ₗ[ℝ] V →ₗ[ℝ] ℝ), (∀ q, (∀ x, β x q = 0) → q = 0) →
    ∀ J : ℝ → (V × V) →ₗ[ℝ] (V × V), (∀ w, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => J t w) → (∀ t w, J t (J t w) = -w) →
    (∀ t, ∃ g : SchwartzMap V ℂ, g ≠ 0 ∧ ∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
    ∃ M : ℝ → V →ₗ[ℝ] V →ₗ[ℝ] ℂ, (∀ x y, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) fun t => M t x y) ∧
      ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p : ℝ × V => M p.1 p.2 p.2) ∧
      (∀ t₀ : ℝ, ∃ ε > 0, ∀ᶠ t in nhds t₀, ∀ x, (M t x x).re ≤ -(ε * ‖x‖ ^ 2)) ∧
      (∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x = Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) →
        ∀ x, g x = g 0 * Complex.exp (M t x x)) ∧
      ∃ (n : ℕ) (qs qs' : Fin n → V) (cs : Fin n → ℂ), ∀ x,
        HasDerivAt (fun t => M t x x) (∑ i, cs i * (β x (qs i) : ℂ) * (β x (qs' i) : ℂ)) 0 := by
  intro V _ _ _ β hβ J hJ _ hex
  choose g0 hg0ne hg0 using hex
  have hunit : ∀ t, IsUnit (GlobalTheory.FockFamily.blockB (J t)) := fun t =>
    GlobalTheory.T.isUnit_upperRightBlock_of_heisenbergDerivative_solution β hβ (J t) (g0 t) (g0 t).continuous (fun h => hg0ne t (SchwartzMap.ext (fun x => congrFun h x))) (hg0 t)
  obtain ⟨hB, hD⟩ := GlobalTheory.T.contDiff_prodLinearMap_upperRight_lowerRight_blocks J hJ
  obtain ⟨hsm, hjoint⟩ := _root_.GlobalTheory.FockFamily.fockForm_family_contDiff β J hB hD hunit
  have hray : ∀ t (g : SchwartzMap V ℂ), (∀ w x, GlobalTheory.GaussLine.dHeis β (J t w) ⇑g x =
      Complex.I * GlobalTheory.GaussLine.dHeis β w ⇑g x) → ∀ x, g x = g 0 * Complex.exp (GlobalTheory.FockFamily.fockForm β (J t) x x) :=
    fun t g hg => GlobalTheory.T.eq_exp_fockGaussianForm_of_heisenbergDerivative_eq β (J t) (hunit t) g g.differentiable hg
  refine ⟨fun t => GlobalTheory.FockFamily.fockForm β (J t), hsm, hjoint, ?_, hray, ?_⟩
  · exact _root_.GlobalTheory.quadForm_unif_target (fun t => GlobalTheory.FockFamily.fockForm β (J t)) hjoint.continuous
      (fun t v hv => GlobalTheory.T.gaussian_form_re_neg_of_ne_zero _ (g0 t) (hg0ne t) (hray t (g0 t) (hg0 t)) v hv)
  · exact GlobalTheory.T.exists_hasDerivAt_diag_eq_sum_mul_pairings β hβ _ (fun x y => ((hsm x y).differentiable (by simp)).differentiableAt)

end GlobalTheory.FockFamily
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GelfandTraceConjInvertibleScalarMatrix
section
open scoped InnerProductSpace

namespace GlobalTheory

theorem recursive_matrixPower_eq_matrix_pow {A : Type} [Ring A] {n : ℕ} (E : Fin n → Fin n → A) (k : ℕ) :
    Matrix.of (Formalism.REAL.epow E k) = (Matrix.of E) ^ k := by
  induction k with
  | zero =>
    ext a b
    simp [Formalism.REAL.epow, Matrix.one_apply]
  | succ k ih =>
    ext a b
    rw [pow_succ, ← ih]
    simp [Formalism.REAL.epow, Matrix.mul_apply]

theorem scalarMatrix_mul_algebraMatrix_mul_apply {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) A) (P Q : Matrix (Fin n) (Fin n) ℂ) (a b : Fin n) :
    ((algebraMap ℂ A).mapMatrix P.transpose * M * (algebraMap ℂ A).mapMatrix Q.transpose) a b
      = ∑ c, ∑ d, (P c a * Q b d) • M c d := by
  rw [Finset.sum_comm]
  simp only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply,
    Finset.sum_mul]
  refine Finset.sum_congr rfl fun d _ => Finset.sum_congr rfl fun c _ => ?_
  rw [← Algebra.commutes, ← Algebra.smul_def, ← Algebra.smul_def, smul_smul, mul_comm]

theorem etr_conj_scalar_matrix {A : Type} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A)
    (P : Matrix (Fin n) (Fin n) ℂ) (hP : IsUnit P) (k : ℕ) :
    Formalism.REAL.etr (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k = Formalism.REAL.etr E k := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  set L : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix P.transpose with hL
  set R : Matrix (Fin n) (Fin n) A := (algebraMap ℂ A).mapMatrix (P⁻¹).transpose with hR
  have hLR : L * R = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h2, Matrix.transpose_one, map_one]
  have hRL : R * L = 1 := by
    rw [hL, hR, ← map_mul, ← Matrix.transpose_mul, h1, Matrix.transpose_one, map_one]
  have hE : Matrix.of (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) = L * Matrix.of E * R := by
    ext a b
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply]
    rfl
  have hpow : ∀ m : ℕ, (L * Matrix.of E * R) ^ m = L * (Matrix.of E) ^ m * R := by
    intro m
    induction m with
    | zero => simp [hLR]
    | succ m ih =>
      rw [pow_succ, ih, pow_succ]
      calc L * Matrix.of E ^ m * R * (L * Matrix.of E * R)
          = L * Matrix.of E ^ m * (R * L) * Matrix.of E * R := by simp only [mul_assoc]
        _ = L * (Matrix.of E ^ m * Matrix.of E) * R := by rw [hRL]; simp only [mul_assoc, one_mul]
  have hk := recursive_matrixPower_eq_matrix_pow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k
  rw [hE, hpow, ← recursive_matrixPower_eq_matrix_pow] at hk
  have hent : ∀ a, Formalism.REAL.epow (fun a b => ∑ c, ∑ d, (P c a * P⁻¹ b d) • E c d) k a a
      = ∑ c, ∑ d, (P c a * P⁻¹ a d) • Formalism.REAL.epow E k c d := by
    intro a
    have := congrFun (congrFun hk a) a
    rw [hL, hR, scalarMatrix_mul_algebraMatrix_mul_apply] at this
    exact this
  unfold Formalism.REAL.etr
  simp only [hent]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [Finset.sum_comm]
  simp only [← Finset.sum_smul, ← Matrix.mul_apply, h1, Matrix.one_apply, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq, Finset.mem_univ, if_true]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.HaarCoords
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix GlobalTheory.MixModel GlobalTheory.MixPer
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.HaarCoords

theorem haar_coords : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), ∃ (μ : Measure (UX D ρ)) (lB : Measure (Mx D ρ S₀.rank)) (lC : Measure (skewA D ρ)), μ.IsHaarMeasure ∧ lB.IsAddHaarMeasure ∧ lC.IsAddHaarMeasure ∧ SFinite μ ∧ SFinite lB ∧ SFinite lC ∧ Measurable (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) ∧ ∃ ν₀ : Measure (flagN d), ν₀.IsHaarMeasure ∧ ν₀.map Subtype.val = (μ.prod (lB.prod lC)).map (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) := by
  intro D S S₀ ρ d
  obtain ⟨iU1, iU2, iU3⟩ := GlobalTheory.UnitU.topology D ρ
  obtain ⟨-, familyMassSecondLine, iM3, iM4, -⟩ := lattice_Mx D ρ S₀.rank
  obtain ⟨-, indexCSecond, iC3, iC4, -⟩ := lattice_Mx D ρ ρ
  obtain ⟨iN1, iN2, iN3, -⟩ := GlobalTheory.Mem.TrueRecord.top_NFlag S (isIsoSub_e d)
  haveI : BorelSpace (UX D ρ) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ S₀.rank) := ⟨rfl⟩
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  have hcl : IsClosed ((skewA D ρ : Set (Mx D ρ ρ))) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (skewA D ρ) := hcl.isClosedEmbedding_subtypeVal.isEmbedding.secondCountableTopology
  haveI : T2Space (skewA D ρ) := inferInstance
  let μ : Measure (UX D ρ) := Measure.haar
  let lB : Measure (Mx D ρ S₀.rank) := Measure.addHaar
  let lC : Measure (skewA D ρ) := Measure.addHaar
  obtain ⟨e, he⟩ := GlobalTheory.MixPer.flagCoord_homeo D S S₀ ρ d
  have hΦ : (fun p : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) => d.levi p.1.1 * (d.nB p.2.1 * d.nC p.2.2)) =
      Subtype.val ∘ e := funext fun p => (he p).symm
  have hem : Measurable e := e.continuous.measurable
  refine ⟨μ, lB, lC, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
  · rw [hΦ]; exact (continuous_subtype_val.comp e.continuous).measurable
  refine ⟨(μ.prod (lB.prod lC)).map e, ?_, ?_⟩
  · haveI := Measure.IsFiniteMeasureOnCompacts.map (μ.prod (lB.prod lC)) e
    haveI : ((μ.prod (lB.prod lC)).map e).IsOpenPosMeasure := e.continuous.isOpenPosMeasure_map e.surjective
    suffices h : ((μ.prod (lB.prod lC)).map e).IsMulLeftInvariant from ⟨⟩
    refine ⟨fun g => ?_⟩
    obtain ⟨p₀, hp₀⟩ := e.surjective g
    have hg : (g : GA D S) = d.levi p₀.1.1 * (d.nB p₀.2.1 * d.nC p₀.2.2) := by rw [← hp₀, he]
    obtain ⟨⟨u', hu'⟩, b', c'⟩ := p₀
    obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.HaarCoords.transl_nB_preserves D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance b'
    obtain ⟨Tc, hTc, hTc'⟩ := GlobalTheory.HaarCoords.transl_nC D S S₀ ρ d μ lB lC inferInstance inferInstance inferInstance inferInstance
      inferInstance inferInstance c'
    let Ta : UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) → UX D ρ × (Mx D ρ S₀.rank × skewA D ρ) :=
      Prod.map (fun u => ⟨u', hu'⟩ * u) id
    have hTa : MeasurePreserving Ta (μ.prod (lB.prod lC)) (μ.prod (lB.prod lC)) :=
      (measurePreserving_mul_left μ _).prod (MeasurePreserving.id _)
    have hT := hTa.comp (hTb.comp hTc)
    have key : (fun x => g * x) ∘ e = e ∘ (Ta ∘ Tb ∘ Tc) := by
      funext p
      apply Subtype.ext
      have h3 : ∀ q, d.levi (Ta q).1.1 * (d.nB (Ta q).2.1 * d.nC (Ta q).2.2) =
          d.levi u' * (d.levi q.1.1 * (d.nB q.2.1 * d.nC q.2.2)) := fun q => by
        simp only [Ta, Prod.map_fst, Prod.map_snd, id, Subgroup.coe_mul, map_mul, mul_assoc]
      simp only [Function.comp_apply, Subgroup.coe_mul, he]
      rw [h3, hTb', hTc', hg]
      simp only [mul_assoc]
    rw [Measure.map_map (measurable_const_mul g) hem, key, ← Measure.map_map hem hT.measurable, hT.map_eq]
  · rw [Measure.map_map continuous_subtype_val.measurable hem, hΦ]

end GlobalTheory.HaarCoords

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdeleFrameAdjointMatrixHalfIdempotentSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

noncomputable section
namespace GlobalTheory.AdjScalar
variable {D : D7}

theorem cA_cA (z : AE D) : cA D (cA D z) = z := by
  induction z using TensorProduct.induction_on with
  | zero => rw [RingHom.map_zero, RingHom.map_zero]
  | add x y hx hy => rw [RingHom.map_add (f := _), RingHom.map_add (f := _), hx, hy]
  | tmul a x =>
    change a ⊗ₜ[D.host.F] star (star x) = _
    rw [star_star]

theorem map_adj_smul {R K : Type} [CommRing R] [CommRing K] (f : R →+* K) (σ : R →+* R) {m n : ℕ}
    (G1 : Matrix (Fin m) (Fin m) R) (G2 : Matrix (Fin n) (Fin n) R) (P : Matrix (Fin m) (Fin m) K)
    (Q : Matrix (Fin n) (Fin n) K) (X : Matrix (Fin n) (Fin m) R) (a : R) :
    P * ((G1 * ((a • X).map σ)ᵀ * G2).map f) * Q = f (σ a) • (P * ((G1 * (X.map σ)ᵀ * G2).map f) * Q) := by
  have h1 : (a • X).map σ = σ a • X.map σ := by
    ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  have h2 : ∀ (M : Matrix (Fin m) (Fin n) R) (b : R), (b • M).map f = f b • M.map f := by
    intro M b; ext i j; simp [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul]
  rw [h1, Matrix.transpose_smul, Matrix.mul_smul, Matrix.smul_mul, h2, Matrix.mul_smul, Matrix.smul_mul]

theorem frMapAdj_smul (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D))
    (a : AE D) (x : WO S T) :
    frMapAdj S T βS βT (a • x) = toEAf D (cA D a) • frMapAdj S T βS βT x :=
  map_adj_smul (toEAf D) (cA D) _ _ _ _ x a

theorem cA_incA' (c : D.host.E) : cA D (incA D c) = incA D (star c) := rfl

theorem smul_absorb {K : Type} [CommRing K] {m n : ℕ} (B : Matrix (Fin m) (Fin m) K) (F : Matrix (Fin m) (Fin n) K)
    (u v : K) (hF : u • F = F) : (u * v) • (B * F) = (1 : K) • (B * (v • F)) := by
  rw [one_smul, Matrix.mul_smul, mul_comm, mul_smul, ← Matrix.mul_smul B u F, hF]

theorem adjA_half_smul (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Lev.EAf D)) (βT : GL (Fin T.rank) (Lev.EAf D))
    (e : AE D) (c : D.host.E) (x : WO S T) (h : IsHalf (cA D e) x) :
    adjA S T βS βT (e * incA D (star c)) x = adjA S T βS βT 1 (incA D c • x) := by
  have hx : cA D e • x = x := by
    ext i j; exact h i j
  have hF : toEAf D e • frMapAdj S T βS βT x = frMapAdj S T βS βT x := by
    conv_rhs => rw [← hx]
    rw [frMapAdj_smul, cA_cA]
  unfold adjA
  rw [frMapAdj_smul, cA_incA', map_one, map_mul]
  exact smul_absorb _ _ _ _ hF

end GlobalTheory.AdjScalar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedModelFormValueTorusGeneratorFirstGroupStatement
section
open Matrix Formalism.UG GlobalTheory.Hk3 GlobalTheory.FinWeil GlobalTheory.SphTheta ValuativeRel Classical
open GlobalTheory.LFun (HasSatU IsSatVecU heckeVec)
open GlobalTheory.LGrp (bcParam extProd)
open GlobalTheory.WeilM (UG IsQuad Darboux symp sbClass SB IsWeilB IsWeilPair TestClass schr dbl diagCols)
open GlobalTheory.IndefiniteRowSideFullHecke.SphericalThetaInertPlace (str chi IsUnramAdd)
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixedModelForm_value_torusGenerator_firstGroup : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (ψ : AddChar L ℂ) (n n' : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : GU σ n × GU σ n' →* Module.End ℂ M) (s : M), IsStd ϖ σ q δ ψ ρ ω s → CayleyRule q n' ρ (ω.comp (MonoidHom.inl _ _)) s → ∀ ℓ : M →ₗ[ℂ] ℂ, ℓ s = 1 → (∀ a ∈ mixLat L n' n, ∀ v, ℓ (ρ a v) = ℓ v) → (∀ x, (¬ ∃ a ∈ mixLat L n' n, x - a ∈ intMat L (Fin n') (Fin n)) → ℓ (ρ x s) = 0) → ∀ (k : Fin (n / 2)) (t : GU σ n), t.1.1 = tMat ϖ n (n / 2) (Pi.single k 1) → ℓ (ω (t, 1) s) = (-1) ^ n' * (q : ℂ) ^ (2 * ((n' / 2 : ℕ) : ℤ) - n') := by
  first | exact @GlobalTheory.SphTheta.TorusFirst.value_torus_first | exact GlobalTheory.SphTheta.TorusFirst.value_torus_first | (intros; apply GlobalTheory.SphTheta.TorusFirst.value_torus_first <;> assumption)
end

