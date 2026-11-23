module

public import Mathlib
public import Formalism.LocalRingCardinality.DataTheta
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.OscActMonomialOfUnique
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0166
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0155
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0011
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GlESymmApply
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0170

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerGaussianVectorsFockSpace
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.Mem.Osc Matrix
open scoped ComplexOrder

namespace GlobalTheory.GaussInner

theorem pairing_mul_eq_exp {σ : Type} [Fintype σ] [DecidableEq σ] (S T : Matrix σ σ ℂ) (x y : σ → ℂ)
    (E E' : MvPowerSeries σ ℂ) (hS : Sᵀ = S) (hT : Tᵀ = T)
    (hE : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E‖ ^ 2))
    (hE' : Summable (fun α : σ →₀ ℕ => (GlobalTheory.FockSeq.mfact α : ℝ) * ‖MvPowerSeries.coeff α E'‖ ^ 2))
    (h0 : MvPowerSeries.coeff 0 E = 1) (h0' : MvPowerSeries.coeff 0 E' = 1)
    (hd : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E =
      MvPowerSeries.coeff α (x l • E + ∑ k, S l k • (MvPowerSeries.X k * E)))
    (hd' : ∀ l α, ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) E' =
      MvPowerSeries.coeff α (y l • E' + ∑ k, T l k • (MvPowerSeries.X k * E')))
    (D : ℝ → ℂ) (hD0 : D 0 = 1)
    (hD : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (T * S)).det ∧
      HasDerivAt D (-((t : ℂ) * (T * S * (1 - ((t : ℂ) ^ 2) • (T * S))⁻¹).trace) * D t) t) :
    (∑' α : σ →₀ ℕ, (GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') * D 1 =
      Complex.exp (1 / 2 * (x ⬝ᵥ (1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x) +
        y ⬝ᵥ (x + S *ᵥ ((1 - T * S)⁻¹ *ᵥ (y + T *ᵥ x))))) := by
  obtain ⟨hc, hm⟩ := moments σ S T x y E E' hE hE' hd hd'
  set f : ℝ → ℂ := fun s => ∑' α : σ →₀ ℕ, (s : ℂ) ^ α.degree *
    ((GlobalTheory.FockSeq.mfact α : ℂ) * MvPowerSeries.coeff α E * MvPowerSeries.coeff α E') with hf
  set w : ℝ → σ → ℂ := fun s => (1 - ((s : ℂ) ^ 2) • (T * S))⁻¹ *ᵥ (y + (s : ℂ) • T *ᵥ x) with hw
  set u : ℝ → σ → ℂ := fun s => x + (s : ℂ) • S *ᵥ w s with hu
  set Φ : ℝ → ℂ := fun s => (s : ℂ) / 2 * (x ⬝ᵥ w s + y ⬝ᵥ u s) with hΦ
  have hΦ' : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt Φ (u t ⬝ᵥ w t) t := fun t ht =>
    GlobalTheory.Mem.GaussPhase.hasDerivAt_phase σ S T x y t hS hT (hD t ht).1
  have hg : ∀ t ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt (fun s => f s * D s * Complex.exp (-Φ s)) 0 t := by
    intro t ht
    have ht' := Set.Ioo_subset_Icc_self ht
    obtain ⟨p, q, m, n, h1, h2, h3, h4, h5⟩ := hm t ht
    have h6 := GlobalTheory.gaussian_pairing_moment_algebra σ S T x y t (f t) p q m n hS hT (hD t ht').1 h1 h2 h3 h4
    change _ = f t * (u t ⬝ᵥ w t + _) at h6
    rw [h6] at h5
    refine ((h5.fun_mul (hD t ht').2).fun_mul (hΦ' t ht').fun_neg.cexp).congr_deriv ?_
    ring
  have hgc : ContinuousOn (fun s => f s * D s * Complex.exp (-Φ s)) (Set.Icc 0 1) :=
    (hc.mul fun t ht => (hD t ht).2.continuousAt.continuousWithinAt).mul
      fun t ht => (hΦ' t ht).fun_neg.cexp.continuousAt.continuousWithinAt
  have key := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le zero_le_one hgc hg
    intervalIntegrable_const
  have f0 : f 0 = 1 := by
    simp only [hf]
    rw [tsum_eq_single 0]
    · simp [h0, h0', GlobalTheory.FockSeq.mfact]
    · intro α hα
      have : α.degree ≠ 0 := fun h => hα ((Finsupp.degree_eq_zero_iff α).1 h)
      simp [this]
  have Φ0 : Φ 0 = 0 := by simp [hΦ]
  rw [f0, hD0, Φ0, intervalIntegral.integral_zero, Complex.exp_neg] at key
  have e : f 1 * D 1 = Complex.exp (Φ 1) := by
    have := Complex.exp_ne_zero (Φ 1)
    simp only [neg_zero, Complex.exp_zero, mul_one] at key
    field_simp at key
    linear_combination -key
  simpa [hf, hΦ, hu, hw] using e

theorem deriv_gauss {P Q : ℕ} (A : Matrix (Fin P) (Fin Q) ℂ) (x : Ix P Q → ℂ) (l : Ix P Q) (α : Ix P Q →₀ ℕ) :
    ((α l : ℂ) + 1) * MvPowerSeries.coeff (α + Finsupp.single l 1) (expPS (gaussPoly A x)) =
      MvPowerSeries.coeff α (x l • expPS (gaussPoly A x) +
        ∑ k, fromBlocks 0 A Aᵀ 0 l k • (MvPowerSeries.X k * expPS (gaussPoly A x))) := by
  rw [GlobalTheory.OscExpDeriv.coeff_deriv_expPS _ _ (coeff_zero_gaussPoly A x)]
  congr 1
  rcases l with i | j
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [GlobalTheory.OscGauss.pderiv_inl_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add (f := _), map_sum]
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [GlobalTheory.OscGauss.pderiv_inr_gaussPoly, ← MvPolynomial.coeToMvPowerSeries.ringHom_apply, map_add (f := _), map_sum]
      simp [MvPolynomial.coeToMvPowerSeries.ringHom_apply, Fintype.sum_sum_type, add_mul, Finset.sum_mul, MvPowerSeries.smul_eq_C_mul, mul_assoc]

theorem posDef_smul {P Q : ℕ} {B : Matrix (Fin P) (Fin Q) ℂ} (hB : (1 - Bᴴ * B).PosDef) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) 1) : (1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B)).PosDef := by
  have h4 : (0 : ℂ) ≤ ((1 - t ^ 4 : ℝ) : ℂ) :=
    Complex.zero_le_real.2 (sub_nonneg.2 (pow_le_one₀ ht.1 ht.2))
  have e : 1 - (((t : ℂ) ^ 2) • B)ᴴ * (((t : ℂ) ^ 2) • B) = (1 - Bᴴ * B) + ((1 - t ^ 4 : ℝ) : ℂ) • (Bᴴ * B) := by
    rw [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have : star ((t : ℂ) ^ 2) * (t : ℂ) ^ 2 = (t : ℂ) ^ 4 := by simp; ring
    rw [this]; push_cast; module
  rw [e]
  exact hB.add_posSemidef ((posSemidef_conjTranspose_mul_self B).smul h4)

theorem inner_gauss_gauss : ∀ (P Q : ℕ) (F : Fock (Ix P Q)) (A B : Matrix (Fin P) (Fin Q) ℂ) (x y : Ix P Q → ℂ), (1 - Aᴴ * A).PosDef → (1 - Bᴴ * B).PosDef → ∀ v w : F.H, HasCoeff F v (expPS (gaussPoly A x)) → HasCoeff F w (expPS (gaussPoly B y)) → let a : Fin P → ℂ := fun i => star (x (Sum.inl i)); let b : Fin Q → ℂ := fun j => star (x (Sum.inr j)); let c : Fin P → ℂ := fun i => y (Sum.inl i); let d : Fin Q → ℂ := fun j => y (Sum.inr j); let M := (1 - B * Aᴴ)⁻¹; let N := (1 - Aᴴ * B)⁻¹; inner ℂ v w = ((1 - Aᴴ * B).det)⁻¹ * Complex.exp (a ⬝ᵥ M *ᵥ c + d ⬝ᵥ N *ᵥ b + a ⬝ᵥ (M * B) *ᵥ b + d ⬝ᵥ (N * Aᴴ) *ᵥ c) := by
  intro P Q F A B x y hA hB v w hv hw a b c d M N
  obtain ⟨s1, hin⟩ := GlobalTheory.FockParseval.parseval _ F v w _ _ hv hw
  obtain ⟨s2, -⟩ := GlobalTheory.FockParseval.parseval _ F w w _ _ hw hw
  have hU : ∀ t ∈ Set.Icc (0 : ℝ) 1, IsUnit (1 - ((t : ℂ) ^ 2) • (Aᴴ * B)).det := fun t ht => by
    simpa only [Matrix.mul_smul] using
      GlobalTheory.isUnit_det_one_sub_conjTranspose_mul_of_contractions P Q A _ hA (posDef_smul hB ht)
  have hU1 : IsUnit (1 - Aᴴ * B).det := by simpa using hU 1 ⟨zero_le_one, le_rfl⟩
  have hy : y = Sum.elim c d := by ext (i | j) <;> rfl
  have key := pairing_mul_eq_exp (fromBlocks 0 Aᴴᵀ Aᴴ 0) (fromBlocks 0 B Bᵀ 0) (Sum.elim a b) y
    (MvPowerSeries.map (starRingEnd ℂ) (expPS (gaussPoly A x))) (expPS (gaussPoly B y))
    (by simp [fromBlocks_transpose]) (by simp [fromBlocks_transpose]) (by simpa using s1) s2
    (by rw [MvPowerSeries.coeff_map]; simp [expPS, MvPowerSeries.coeff_apply]) (by simp [expPS, MvPowerSeries.coeff_apply])
    (fun l α => by
      have := congrArg (starRingEnd ℂ) (deriv_gauss A x l α)
      rw [← MvPowerSeries.coeff_map (f := starRingEnd ℂ) (n := α)] at this
      rcases l with i | j <;>
        simpa [MvPowerSeries.smul_eq_C_mul, Fintype.sum_sum_type, a, b] using this)
    (deriv_gauss B y) (fun s : ℝ => (1 - ((s : ℂ) ^ 2) • (Aᴴ * B)).det) (by simp)
    (fun t ht => GlobalTheory.FockDetDer.hasDerivAt_det_one_sub_sq P Q A B t (hU t ht))
  have hb := GlobalTheory.gaussian_phase_critical_value_blocks P Q A B a c b d hU1
  simp only [← hy] at hb
  rw [hb] at key
  simp only [MvPowerSeries.coeff_map, Complex.ofReal_one, one_pow, one_smul] at key
  rw [hin, ← key, mul_comm, mul_assoc, mul_inv_cancel₀ hU1.ne_zero, mul_one]

end GlobalTheory.GaussInner
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsHCTypeUConj
section
noncomputable section

open Matrix Formalism.MainNotions.S

namespace GlobalTheory.CoefSpace.Conj

variable {k : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  {π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)}

theorem ujset_eq (k : ℕ) : UJset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  GlobalTheory.RealPar.ujset_const true

theorem kset_eq (k : ℕ) : Formalism.REAL.Kset (allPos k) = (Matrix.unitaryGroup (Fin k) ℂ : Set _) :=
  (GlobalTheory.DefiniteCheck.kset_const k true).trans (ujset_eq k)

theorem conj_mem {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ Matrix.unitaryGroup (Fin k) ℂ) :
    g.map star ∈ Matrix.unitaryGroup (Fin k) ℂ :=
  Matrix.transpose_mem_unitaryGroup_iff.2 (Unitary.star_mem hg)

def tor (θ : Fin k → ℝ) : Matrix (Fin k) (Fin k) ℂ := Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)

theorem tor_conj (θ : Fin k → ℝ) : (tor θ).map star = tor (-θ) := by
  rw [tor, Matrix.diagonal_map (star_zero ℂ)]
  congr 1
  funext a
  simp [← Complex.exp_conj]

theorem tor_mem (θ : Fin k → ℝ) : tor θ ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, tor, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp [← Complex.exp_conj, ← Complex.exp_add]

theorem wt_iff (μ : Fin k → ℝ) (v : H) : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v ↔
    ∀ θ, π (tor θ) v = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • v :=
  ⟨fun h θ => h θ (by rw [kset_eq]; exact tor_mem θ), fun h θ _ => h θ⟩

theorem wt_conj {μ : Fin k → ℝ} {v : H} :
    IsWtOn (Formalism.REAL.Kset (allPos k)) (fun g => π (g.map star)) μ v ↔ IsWtOn (Formalism.REAL.Kset (allPos k)) π (-μ) v := by
  simp only [wt_iff, tor_conj]
  refine ⟨fun h θ => ?_, fun h θ => ?_⟩
  · simpa using h (-θ)
  · simpa using h (-θ)

def revM (k : ℕ) : Matrix (Fin k) (Fin k) ℂ := (1 : Matrix (Fin k) (Fin k) ℂ).submatrix Fin.revPerm id

theorem revM_mem : revM k ∈ Matrix.unitaryGroup (Fin k) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, revM, Matrix.conjTranspose_submatrix,
    Matrix.conjTranspose_one, Matrix.submatrix_mul_equiv, Matrix.mul_one, Matrix.submatrix_id_id]

theorem tor_revM (θ : Fin k → ℝ) : tor θ * revM k = revM k * tor fun a => θ (Fin.rev a) := by
  ext a b
  simp only [tor, revM, Matrix.diagonal_mul, Matrix.mul_diagonal, Matrix.submatrix_apply, Fin.revPerm_apply, id,
    Matrix.one_apply]
  split_ifs with h
  · subst h
    simp
  · simp

theorem wt_rev (hπ : IsURepOn (UJset (allPos k)) π) {μ : Fin k → ℝ} {v : H} (hv0 : v ≠ 0)
    (hv : IsWtOn (Formalism.REAL.Kset (allPos k)) π μ v) :
    π (revM k) v ≠ 0 ∧ IsWtOn (Formalism.REAL.Kset (allPos k)) π (fun a => μ (Fin.rev a)) (π (revM k) v) := by
  rw [ujset_eq] at hπ
  refine ⟨fun h => hv0 ?_, (wt_iff _ _).2 fun θ => ?_⟩
  · rw [← norm_eq_zero, ← hπ.2.1 _ revM_mem v, h, norm_zero]
  · have e : ∑ a, μ a * θ (Fin.rev a) = ∑ a, μ (Fin.rev a) * θ a := by
      rw [← Equiv.sum_comp Fin.revPerm]
      simp
    rw [← ContinuousLinearMap.comp_apply, ← hπ.1.2 _ (tor_mem θ) _ revM_mem, tor_revM,
      hπ.1.2 _ revM_mem _ (tor_mem _), ContinuousLinearMap.comp_apply, (wt_iff _ _).1 hv, map_smul, e]

theorem cdom_neg_rev {μ Λ : Fin k → ℝ} (h : CDom (allPos k) μ Λ) :
    CDom (allPos k) (fun a => -μ (Fin.rev a)) fun a => -Λ (Fin.rev a) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun a b => c (Fin.rev b) (Fin.rev a), fun a b h => ⟨Fin.rev_lt_rev.1 (hc _ _ h).1, rfl⟩, ?_⟩
  funext x
  have h1 := congrFun e (Fin.rev x)
  rw [← Equiv.sum_comp Fin.revPerm] at h1
  simp only [← Equiv.sum_comp Fin.revPerm (fun b => (c _ b : ℝ) • Formalism.REAL.root _ b)] at h1
  rw [Finset.sum_comm] at h1
  simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, Formalism.REAL.root, Pi.single_apply, Fin.revPerm_apply,
    Fin.rev_inj, smul_eq_mul] at h1 ⊢
  rw [show -Λ x.rev - -μ x.rev = -(Λ x.rev - μ x.rev) by ring, h1, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun b _ => by ring

theorem isHCTypeU_conj {u : Fin k → ℝ} (h : IsHCTypeU k u π) :
    IsHCTypeU k (fun i => -u (Fin.rev i)) (fun g => π (g.map star)) := by
  obtain ⟨h1, h2, h3, h4, -, h5, ⟨v, -, hv0, hv⟩, h6⟩ := h
  have hl : Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) =
      fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
    funext a
    unfold allPos
    rw [GlobalTheory.DefiniteCheck.lowK_const, GlobalTheory.DefiniteCheck.lowK_const, Fin.val_rev, Nat.cast_sub a.2]
    push_cast
    ring
  have h3' := h3
  rw [ujset_eq] at h3'
  refine ⟨h1, h2, ?_, h4, fun _ _ _ _ => trivial, fun S hS hst => h5 S hS fun g hg x hx => ?_,
    ⟨_, trivial, (wt_rev h3 hv0 hv).1, ?_⟩, fun μ x _ hx0 hx => ?_⟩
  · rw [ujset_eq]
    refine ⟨⟨?_, fun a ha b hb => ?_⟩, fun g hg => h3'.2.1 _ (conj_mem hg), fun x => ?_⟩
    · beta_reduce
      rw [Matrix.map_one _ (star_zero ℂ) (star_one ℂ)]
      exact h3'.1.1
    · have : (a * b).map star = a.map star * b.map star := Matrix.map_mul (f := starRingEnd ℂ)
      beta_reduce
      rw [this]
      exact h3'.1.2 _ (conj_mem ha) _ (conj_mem hb)
    · exact (h3'.2.2 x).comp (continuous_id.matrix_map continuous_star).continuousOn fun g hg => conj_mem hg
  · rw [kset_eq] at hg
    have := hst (g.map star) (by rw [kset_eq]; exact conj_mem hg) x hx
    have e : (g.map star).map star = g := by
      ext a b
      simp
    simpa only [e] using this
  · rw [hl, wt_conj]
    convert (wt_rev h3 hv0 hv).2 using 1
    funext a
    simp
  · obtain ⟨a1, a2⟩ := wt_rev h3 hx0 (wt_conj.1 hx)
    rw [hl]
    convert cdom_neg_rev (h6 _ _ trivial a1 a2) using 1
    funext a
    simp

end GlobalTheory.CoefSpace.Conj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
section
noncomputable section

open NumberField IsDedekindDomain Topology Matrix Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host

namespace GlobalTheory.CuspRep.CsdUnitary

open Central

section

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}


omit [_root_.NumberField.IsTotallyComplex E] in
theorem norm_of_pow (χ : HChar E) (z : Ideles E) {n : ℕ} (hn : 0 < n) (h : ‖((χ.1 (z ^ n) : ℂˣ) : ℂ)‖ = 1) :
    ‖((χ.1 z : ℂˣ) : ℂ)‖ = 1 := by
  rw [map_pow, Units.val_pow_eq_pow_val, norm_pow] at h
  exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hn.ne').1 h

theorem norm_int (χ : HChar E) (k : GL (Fin 1) (Af E))
    (hk : k ∈ GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)) :
    ‖((χ.1 (finId E (GeneralLinearGroup.det k)) : ℂˣ) : ℂ)‖ = 1 := by
  let U : Subgroup (GL (Fin 1) (Af E)) := (χ.1.comp (finId E)).ker.comap GeneralLinearGroup.det
  have hU : IsOpen (U : Set (GL (Fin 1) (Af E))) :=
    (isOpen_ker_finIdele E (χ.1.comp (finId E)) (χ.2.1.comp (continuous_finId E))).preimage
      GeneralLinearGroup.continuous_det
  have : T2Space (Af E) :=
    inferInstanceAs (T2Space (RestrictedProduct (fun v : HeightOneSpectrum (𝓞 E) => v.adicCompletion E)
      (fun v => (v.adicCompletionIntegers E : Set (v.adicCompletion E))) Filter.cofinite))
  set K : Subgroup (GL (Fin 1) (Af E)) := GlobalTheory.GLIntegral.glSub (GlobalTheory.GLIntegral.intSubring E)
  have : CompactSpace K := isCompact_iff_compactSpace.1
    (GlobalTheory.GLIntegral.isCompact_glSub _ (GlobalTheory.AdeleCocompact.isCompact_integral E))
  have : Finite (K ⧸ U.subgroupOf K) := Subgroup.quotient_finite_of_isOpen _ (hU.preimage continuous_subtype_val)
  have hi := (Subgroup.finiteIndex_of_finite_quotient (H := U.subgroupOf K)).index_ne_zero
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero hi ⟨k, hk⟩
  refine norm_of_pow χ _ hn ?_
  have h2 : χ.1 (finId E (GeneralLinearGroup.det (k ^ n))) = 1 := h1
  rw [← map_pow, ← map_pow, h2, Units.val_one, norm_one]

theorem isUnitary_of_inf (χ : HChar E) (h : ∀ y, ‖((chiInf χ y : ℂˣ) : ℂ)‖ = 1) : χ.IsUnitary := by
  intro z
  change ‖((χ.1 z : ℂˣ) : ℂ)‖ = 1
  obtain ⟨n, hn, -, h1⟩ := Subgroup.exists_pow_mem_of_index_ne_zero
    (GlobalTheory.Mem.UnitIndex.finiteIndex_unitIdl_sup E).index_ne_zero z
  refine norm_of_pow χ z hn ?_
  obtain ⟨u, hu, _, ⟨γ, rfl⟩, e⟩ := Subgroup.mem_sup.1 h1
  have key : ∀ u ∈ GlobalTheory.Mem.Chr.unitIdl E, ∀ i j, (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)).val i j ∈
      GlobalTheory.GLIntegral.intSubring E := fun u hu i j v => by
    rw [RankOne.obo_apply]
    exact (hu v).le
  have h2 := norm_int χ (RankOne.obo _ (Units.map (pFin E).toMonoidHom u))
    ⟨key u hu, by rw [← map_inv, ← map_inv]; exact key _ (inv_mem hu)⟩
  rw [show GeneralLinearGroup.det (RankOne.obo _ (Units.map (pFin E).toMonoidHom u)) = _ from CG.det_oneByOne _] at h2
  have h3 : ‖((χ.1 (infId E (Units.map (pInf E).toMonoidHom u)) : ℂˣ) : ℂ)‖ = 1 := h _
  have h4 : χ.1 (diagUnits E γ) = 1 := χ.2.2 γ
  rw [← e, map_mul, h4, mul_one, ← infId_mul_finId u, map_mul, Units.val_mul, norm_mul, h2, h3, one_mul]

theorem norm_chiInf (χ : HChar E) (h : ∀ z, star z = z → dchi χ z = 0) (y : (Cinf E)ˣ) :
    ‖((chiInf χ y : ℂˣ) : ℂ)‖ = 1 := by
  classical
  have h1 : ∀ w : InfinitePlace E, dchi χ (Pi.single w 1) = 0 := fun w => h _ (by
    funext v
    by_cases e : v = w
    · subst e; simp
    · simp [e])
  have h2 : ∀ w : InfinitePlace E, (dchi χ (Pi.single w Complex.I)).re = 0 := fun w => by
    have e : expU ((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)) = 1 := Units.ext (funext fun v => by
      change Complex.exp (((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)) v) = 1
      by_cases e : v = w
      · subst e; simp
      · simp [e])
    have h3 := congrArg norm (chiInf_expU χ ((2 * Real.pi : ℝ) • (Pi.single w Complex.I : Cinf E)))
    rw [e, map_one, Units.val_one, norm_one, Complex.norm_exp, map_smul, eq_comm, Real.exp_eq_one_iff,
      Complex.smul_re, smul_eq_mul] at h3
    exact (mul_eq_zero.1 h3).resolve_left (by positivity)
  have h3 : ∀ z : Cinf E, (dchi χ z).re = 0 := fun z => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.univ_sum_single z, map_sum, Complex.re_sum]
    refine Finset.sum_eq_zero fun w _ => ?_
    have e : (Pi.single w (z w) : Cinf E) =
        (z w).re • (Pi.single w 1 : Cinf E) + (z w).im • (Pi.single w Complex.I : Cinf E) := by
      rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
      simp
    rw [e, map_add (f := _), map_smul, map_smul, h1, smul_zero, zero_add, Complex.smul_re, h2, smul_zero]
  rw [← expU_log y, chiInf_expU, Complex.norm_exp, h3, Real.exp_zero]

theorem lie_scL {π : CuspSub E a} {ω : HChar E} (h : π.HasCentral ω) (z : Cinf E) {ψ : Sm E a} (hψ : ψ ∈ π.V) :
    lie E a (scL a z) ψ = dchi ω z • ψ := by
  refine Subtype.ext <| funext fun g => ?_
  have h1 := hasDerivAt_scalar z ψ g
  have e : (fun t : ℝ => ψ.1 (g * GeneralLinearGroup.scalar (Fin a) (infId E (expU (t • z))))) =
      fun t : ℝ => Complex.exp (t * dchi ω z) * ψ.1 g := by
    funext t
    rw [← scalar_comm, h.apply hψ]
    congr 1
    refine (chiInf_expU ω _).trans ?_
    rw [map_smul, Complex.real_smul]
  rw [e] at h1
  refine h1.unique ?_
  change HasDerivAt _ (dchi ω z * ψ.1 g) 0
  simpa using (((Complex.ofRealCLM.hasDerivAt (x := 0)).mul_const (dchi ω z)).cexp).mul_const (ψ.1 g)

end

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {a : ℕ}

theorem thetaOp_scL (z : Cinf L) : thetaOp (.lie (scL a z)) = (.lie (scL a (-star z)) : Op L a) := by
  refine congrArg (fun X => Op.lie (toL X)) ?_
  change -(GlobalTheory.Tw.Phi a (Cinf L) * (Matrix.diagonal fun _ => z)ᴴ * (GlobalTheory.Tw.Phi a (Cinf L))ᵀ) = _
  have e : (Matrix.diagonal fun _ : Fin a => z)ᴴ = star z • (1 : Matrix (Fin a) (Fin a) (Cinf L)) := by
    rw [Matrix.diagonal_conjTranspose, Matrix.smul_one_eq_diagonal]; rfl
  rw [e, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul, Phi_mul_transpose, ← neg_smul,
    Matrix.smul_one_eq_diagonal]

theorem dchi_theta {π : CuspSub L a} {ω : HChar L} (h : π.HasCentral ω) (hπ : π.IsCsd) (z : Cinf L) :
    dchi ω (-star z) = dchi ω z := by
  obtain ⟨T, hT⟩ := hπ
  have := Submodule.nontrivial_iff_ne_bot.2 π.ne_bot
  obtain ⟨φ, hφ⟩ := exists_ne (0 : π.V)
  have e : ∀ (x : Cinf L) (ψ : π.V), π.op (.lie (scL a x)) ψ = dchi ω x • ψ := fun x ψ =>
    Subtype.ext (lie_scL h x ψ.2)
  have h1 := hT (.lie (scL a z)) φ
  rw [thetaOp_scL, e, e, map_smul] at h1
  exact smul_left_injective ℂ ((map_ne_zero_iff T T.injective).2 hφ) h1

theorem isUnitary_of_isCsd : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (a : ℕ) (π : GlobalTheory.CuspRep.CG L a),
    π.IsCsd → π.IsUnitary := by
  intro L _ _ _ a π hπ
  induction π using Quotient.inductionOn with
  | _ π =>
    obtain ⟨ω, h⟩ := exists_hasCentral L a π
    refine (CG.isUnitary_mk π).2 ⟨ω, isUnitary_of_inf ω (norm_chiInf ω fun z hz => ?_), h⟩
    have h1 := dchi_theta h hπ z
    rw [hz, map_neg] at h1
    linear_combination -h1 / 2

end GlobalTheory.CuspRep.CsdUnitary
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpwardLevelMoveIncidenceOfPairs
section
open Formalism.BasicNotions Formalism.L2.Forms Formalism.UG Formalism.L2.GlobalTheoryTheory.LocalLatticeBases NumberField IsDedekindDomain Matrix GlobalTheory.LevelHecke
open scoped TensorProduct

namespace GlobalTheory.LevelHecke

section
variable {R V k W W' : Type} [CommRing R] [AddCommGroup V] [Module R V] [Field k]
  [AddCommGroup W] [Module k W] [AddCommGroup W'] [Module k W']

theorem mem_loc_map_equiv (res : R →+* k) (g : V ≃ₗ[R] V) (M : Submodule R V) (y : V) :
    y ∈ loc res (M.map (g : V →ₗ[R] V)) ↔ g.symm y ∈ loc res M := by
  rw [mem_loc, mem_loc]
  refine exists_congr fun s => and_congr_right fun _ => ?_
  rw [Submodule.mem_map_equiv, map_smul]

theorem act_pairOf_value (res : R →+* k) (g : V ≃ₗ[R] V) (M M' : Submodule R V) (pr : M →+ W) (pr' : M' →+ W')
    (φ : Module.Dual k W) (φ' : Module.Dual k W')
    (hs : ∀ (a : R) z, pr (a • z) = res a • pr z) (hs' : ∀ (a : R) z, pr' (a • z) = res a • pr' z)
    (t : R) (z : M) (e : V) (he : t • e = z.1) (h1 : φ (pr z) = 1)
    (hm : e ∈ loc res (M'.map (g : V →ₗ[R] V)))
    (h : ∀ (x : M') (hx : t • g x.1 ∈ M), φ' (pr' x) = φ (pr ⟨_, hx⟩)) :
    ((pairOf res M' pr' φ').act g).f e = 1 := by
  rw [mem_loc_map_equiv] at hm
  obtain ⟨s, hs0, hx⟩ := (mem_loc _ _ _).1 hm
  have e1 : t • g (s • g.symm e) = (s • z : M).1 := by
    rw [map_smul, g.apply_symm_apply, smul_comm, he]; rfl
  have hx2 : t • g (s • g.symm e) ∈ M := by rw [e1]; exact (s • z).2
  have h2 := h ⟨_, hx⟩ hx2
  have e2 : (⟨_, hx2⟩ : M) = s • z := Subtype.ext e1
  rw [locExt_spec res M' pr' hs' _ hm s hx, map_smul, e2, hs, map_smul, h1] at h2
  show φ' (locExt res M' pr' (g.symm e)) = 1
  exact smul_right_injective k hs0 h2

end

set_option maxHeartbeats 1000000 in
theorem up_move_incidence : ∀ (D : D7) (u : D.what₂.Word) (A : AtTTied u) (i : ℕ) (hi : i ≤ D.R.m) (P : LvTied u A i hi) (K : ClsTied u i hi) (v : (D.mem u).A.vT) (c c' : (D.mem u).C.cls i) (z : ↥(Ld D u i hi c)) (γ : GL (Fin (D.R.N i)) D.host.E), (D.fm u).fv i v c (P.pr v c z) = 1 → loc (A.res v) (mulLat γ.1 (clsCrd D u i hi c')) = loc (A.res v) (Ld D u i hi c) → loc (A.res v) (mulLat γ.1 (Ld D u i hi c')) = loc (A.res v) (Ld D u i hi c ⊔ Submodule.span (𝓞 D.host.E) {(((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1}) → (∀ (x : ↥(Ld D u i hi c')) (hx : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • (γ.1 *ᵥ x.1) ∈ Ld D u i hi c), (D.fm u).fv i v c' (P.pr v c' x) = (D.fm u).fv i v c (P.pr v c ⟨_, hx⟩)) → ((pc P v c').act (glE γ)).IsKer (pc P v c).L ∧ ∃ e, ((pc P v c').act (glE γ)).f e = 1 ∧ locExt (A.res v) (Ld D u i hi c) (P.pr v c) ((((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • e) = P.pr v c z := by
  intro D u A i hi P K v c c' z γ h1 h2 h3 h4
  have hT : (((D.mem u).A.T : ℕ) : D.host.E) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.mem u).A.T_prime.ne_zero
  have he : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) • ((((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1) = z.1 := by
    rw [Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul D.host.E, smul_smul, mul_inv_cancel₀ hT, one_smul]
  refine ⟨fun y => ?_, (((D.mem u).A.T : ℕ) : D.host.E)⁻¹ • z.1, ?_, ?_⟩
  · rw [Pr.mem_act]
    have h5 := pc_isKer P K v c' ((glE γ).symm y)
    rw [_root_.GlobalTheory.LevelHecke.loc_lk_eq_loc_cls D u A i hi K v c', ← mem_loc_map_equiv, map_glE, h2] at h5
    exact h5
  · refine act_pairOf_value (A.res v) (glE γ) _ _ (P.pr v c) (P.pr v c') _ _ (P.pr_smul v c) (P.pr_smul v c')
      _ z _ he h1 ?_ h4
    rw [map_glE, h3]
    exact le_loc _ _ (Submodule.mem_sup_right (Submodule.subset_span rfl))
  · rw [he]; exact locExt_coe _ _ _ (P.pr_smul v c) z

end GlobalTheory.LevelHecke
end

