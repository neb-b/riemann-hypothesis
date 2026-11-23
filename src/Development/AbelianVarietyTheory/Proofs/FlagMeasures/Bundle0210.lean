module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0162
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0148
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0168
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompact
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PsiComplexifiedKEquivariance
section
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Count GlobalTheory.Dec
open scoped InnerProductSpace ComplexOrder

noncomputable section
namespace GlobalTheory.Dec.Equivar
variable {n : ℕ}

lemma diag_KC (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ a, d a ≠ 0) : Matrix.diagonal d ∈ KC ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_diagonal]
    exact IsUnit.mk0 _ (Finset.prod_ne_zero_iff.2 fun a _ => hd a)
  · unfold Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1; funext a; ring

lemma KC_mul {ε : Fin n → Bool} {a b : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) (hb : b ∈ KC ε) :
    a * b ∈ KC ε := by
  refine ⟨ha.1.mul hb.1, ?_⟩
  rw [Matrix.mul_assoc, hb.2, ← Matrix.mul_assoc, ha.2, Matrix.mul_assoc]

lemma KC_inv {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : a⁻¹ ∈ KC ε := by
  have hd := (Matrix.isUnit_iff_isUnit_det a).1 ha.1
  refine ⟨Matrix.isUnit_nonsing_inv_iff.2 ha.1, ?_⟩
  calc a⁻¹ * Jm ε = a⁻¹ * (Jm ε * a) * a⁻¹ := by
        rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_right _ _ hd]
    _ = Jm ε * a⁻¹ := by rw [← ha.2, Matrix.nonsing_inv_mul_cancel_left _ _ hd]

lemma KC_conjT {ε : Fin n → Bool} {a : Matrix (Fin n) (Fin n) ℂ} (ha : a ∈ KC ε) : aᴴ ∈ KC ε := by
  refine ⟨by simpa [Matrix.star_eq_conjTranspose] using ha.1.star, ?_⟩
  have h := congrArg Matrix.conjTranspose ha.2
  simp only [Matrix.conjTranspose_mul, Jm_conjTranspose] at h
  exact h.symm

variable {ε : Fin n → Bool} {abelian₂ : Fin n → ℝ} {W : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
  {τ : Matrix (Fin n) (Fin n) ℂ → (W →L[ℂ] W)} {w : W}

lemma tau_diag (hτ : IsTau ε abelian₂ τ w) (r : Fin n → ℝ) :
    τ (Matrix.diagonal fun a => Complex.exp (r a)) w = Complex.exp (-((∑ a, abelian₂ a * r a : ℝ) : ℂ)) • w := by
  refine ext_inner_left ℂ fun u => ?_
  set c : ℂ := -((∑ a, abelian₂ a * r a : ℝ) : ℂ) with hc
  let f : ℂ → ℂ := fun s => ⟪u, τ (Matrix.diagonal fun a => Complex.exp (r a * s)) w⟫_ℂ
  let g : ℂ → ℂ := fun s => Complex.exp (c * s) * ⟪u, w⟫_ℂ
  have hf : Differentiable ℂ f := by
    have h1 : Differentiable ℂ (fun s : ℂ => fun i j : Fin n =>
        (Matrix.diagonal fun a => Complex.exp (r a * s)) i j) := by
      refine differentiable_pi.2 fun i => differentiable_pi.2 fun j => ?_
      by_cases h : i = j
      · subst h; simp only [Matrix.diagonal_apply_eq]; fun_prop
      · simp only [Matrix.diagonal_apply_ne _ h]; fun_prop
    have := (hτ.2.2.1 u w).comp (s := Set.univ) h1.differentiableOn
      (fun s _ => diag_KC ε fun a => Complex.exp_ne_zero _)
    exact differentiableOn_univ.1 this
  have hg : Differentiable ℂ g := by fun_prop
  have hfg : ∀ t : ℝ, f (t * Complex.I) = g (t * Complex.I) := by
    intro t
    have hmem : Matrix.diagonal (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) ∈ Kset ε := by
      refine ⟨?_, (diag_KC ε fun a => Complex.exp_ne_zero _).2⟩
      rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
        Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
      congr 1
      funext a
      rw [Pi.star_apply, Complex.star_def, Complex.mul_conj', Complex.norm_exp_ofReal_mul_I]
      simp
    have h := hτ.2.2.2.2.2.2.1 (fun a => r a * t) hmem
    simp only [f, g]
    have e : (fun a => Complex.exp (r a * (t * Complex.I))) =
        (fun a => Complex.exp (((r a * t : ℝ) : ℂ) * Complex.I)) := by
      funext a; push_cast; rw [mul_assoc]
    rw [e, h, inner_smul_right, hc]
    congr 2
    simp only [Pi.neg_apply, ← mul_assoc, ← Finset.sum_mul, neg_mul, Finset.sum_neg_distrib]
    push_cast; ring
  have hfreq : ∃ᶠ z in nhdsWithin (0 : ℂ) {0}ᶜ, f z = g z := by
    have ht : Filter.Tendsto (fun t : ℝ => (t : ℂ) * Complex.I) (nhdsWithin 0 {0}ᶜ) (nhdsWithin 0 {0}ᶜ) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have : Continuous fun t : ℝ => (t : ℂ) * Complex.I := by fun_prop
        simpa using (this.tendsto 0).mono_left nhdsWithin_le_nhds
      · filter_upwards [self_mem_nhdsWithin] with t ht
        simpa using ht
    exact ht.frequently (Filter.Frequently.of_forall hfg)
  have := AnalyticOnNhd.eq_of_frequently_eq (hf.differentiableOn.analyticOnNhd isOpen_univ)
    (hg.differentiableOn.analyticOnNhd isOpen_univ) hfreq
  have := congrFun this 1
  simpa [f, g, inner_smul_right] using this

lemma tau_lo (hτ : IsTau ε abelian₂ τ w) {b : Matrix (Fin n) (Fin n) ℂ} (hb : b ∈ KC ε) (hlo : IsLo b)
    (hpos : ∀ l, 0 < b l l) : τ b w = ((∏ l, ‖b l l‖ ^ (-(abelian₂ l)) : ℝ) : ℂ) • w := by
  have hne : ∀ l, b l l ≠ 0 := fun l => (hpos l).ne'
  have hn : ∀ l, 0 < ‖b l l‖ := fun l => norm_pos_iff.2 (hne l)
  have hexp : ∀ l, Complex.exp (Real.log ‖b l l‖ : ℝ) = b l l := fun l => by
    rw [← Complex.ofReal_exp, Real.exp_log (hn l)]
    exact Complex.norm_of_nonneg' (hpos l).le
  have hu : Matrix.diagonal (fun a => (b a a)⁻¹) * b ∈ KC ε :=
    KC_mul (diag_KC ε fun a => inv_ne_zero (hne a)) hb
  have hu1 : IsLoUni (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    intro i j
    refine ⟨fun h => by simp [Matrix.diagonal_mul, hlo i j h], fun h => ?_⟩
    subst h
    simp [Matrix.diagonal_mul, hne]
  have e : b = (Matrix.diagonal fun a => Complex.exp (Real.log ‖b a a‖ : ℝ)) *
      (Matrix.diagonal (fun a => (b a a)⁻¹) * b) := by
    simp only [hexp]
    ext i j
    simp [Matrix.diagonal_mul, hne]
  have h1 := hτ.2.1.2 _ (diag_KC ε (d := fun a => Complex.exp (Real.log ‖b a a‖ : ℝ))
    fun a => Complex.exp_ne_zero _) _ hu
  rw [← e] at h1
  rw [h1, ContinuousLinearMap.comp_apply, hτ.2.2.2.2.2.2.2 _ hu hu1, tau_diag hτ]
  congr 1
  rw [← Complex.ofReal_neg, ← Complex.ofReal_exp, ← Finset.sum_neg_distrib, Real.exp_sum]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  rw [Real.rpow_def_of_pos (hn l)]
  congr 1; ring

lemma tau_cont (hτ : IsTau ε abelian₂ τ w) (v : W) : ContinuousOn (fun k => τ k v) (Kset ε) := by
  have := hτ.1
  have e : (fun k => τ k v) = fun k => ∑ i, ⟪stdOrthonormalBasis ℂ W i, τ k v⟫_ℂ • stdOrthonormalBasis ℂ W i := by
    funext k
    rw [(stdOrthonormalBasis ℂ W).sum_repr']
  rw [e]
  refine continuousOn_finsetSum _ fun i _ => ContinuousOn.smul ?_ continuousOn_const
  exact (hτ.2.2.1 _ v).continuousOn.mono fun k hk => FormF.K_KC hk

lemma muInt_cast {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) (l : Fin n) :
    (muInt lam l : ℝ) = lowK ε lam l + 2 * rhoC ε l := by
  obtain ⟨m, hm⟩ := hlam.2 l
  have h1 := half_sum_roots_standard n ε l
  have h2 : lam l + Formalism.QuantumDeterminants.rhoStd n l = ((m + n - 1 - (l : ℕ) : ℤ) : ℝ) := by
    simp only [Formalism.QuantumDeterminants.rhoStd]; push_cast; linarith
  have h3 : (muInt lam l : ℝ) = lam l + Formalism.QuantumDeterminants.rhoStd n l := by
    rw [muInt, h2, Int.floor_intCast]
  rw [h3]
  simp only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply]
  linarith

lemma scalar_eq {lam : Fin n → ℝ} (hlam : IsHCParam lam) (ε : Fin n → Bool) {d : Fin n → ℂ} (hd : ∀ l, d l ≠ 0) :
    (∏ l, (d l * star (d l)) ^ (-(muInt lam l))) * ((∏ l, ‖d l‖ ^ (4 * rhoC ε l) : ℝ) : ℂ) =
      ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) * ((∏ l, ‖d l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) := by
  simp only [Complex.star_def, Complex.mul_conj', ← Complex.ofReal_pow, ← Complex.ofReal_zpow,
    ← Complex.ofReal_prod, ← Complex.ofReal_mul, ← Finset.prod_mul_distrib]
  congr 1
  refine Finset.prod_congr rfl fun l _ => ?_
  have hn : 0 < ‖d l‖ := norm_pos_iff.2 (hd l)
  rw [← Real.rpow_intCast, ← Real.rpow_natCast, ← Real.rpow_mul hn.le, ← Real.rpow_add hn, ← Real.rpow_add hn]
  congr 1
  push_cast
  rw [muInt_cast hlam ε]
  ring

theorem psEquiv_of (hT : PhiTri) (hP : PhiPos) (hI : IwasawaKC) (hH : IwasawaInt) : PsEquiv := by
  intro n ε lam W _ _ τ w hlam hτ x y hx hy
  have hyd := (Matrix.isUnit_iff_isUnit_det y).1 hy.1
  have hx' : (y * x * yᴴ).PosDef := hx.mul_mul_conjTranspose_same (Matrix.vecMul_injective_of_isUnit hy.1)
  obtain ⟨κ, β, hκ, -⟩ := hI n ε
  have hmem : ∀ k : KG ε, y⁻¹ * toMK k ∈ KC ε := fun k => KC_mul (KC_inv hy) (FormF.K_KC k.2)
  ext u
  refine ext_inner_left ℂ fun v => ?_
  have hadj : ∀ a : W, ⟪v, τ y a⟫_ℂ = ⟪τ yᴴ v, a⟫_ℂ := fun a => by
    rw [hτ.2.2.2.1 _ (KC_conjT hy), Matrix.conjTranspose_conjTranspose]
  rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, hadj,
    FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx', FormF.psEntry hP n ε lam W τ w hτ.1 (tau_cont hτ) _ hx]
  congr 1
  have hF : ContinuousOn (fun k : Matrix (Fin n) (Fin n) ℂ =>
      Phi lam (k⁻¹ * x * k) * (⟪τ yᴴ v, τ k w⟫_ℂ * ⟪τ k w, τ yᴴ u⟫_ℂ)) (Kset ε) := by
    refine ContinuousOn.mul ?_ ((ContinuousOn.inner (𝕜 := ℂ) continuousOn_const (tau_cont hτ w)).mul
      (ContinuousOn.inner (𝕜 := ℂ) (tau_cont hτ w) continuousOn_const))
    refine ContinuousOn.congr (f := fun k => Phi lam (kᴴ * x * k)) ?_ fun k hk => by simp only [FormF.K_inv hk]
    unfold Phi
    refine continuousOn_finsetProd _ fun i _ => ContinuousOn.zpow₀ ?_ _ fun k hk => Or.inl ?_
    · unfold leadMinor
      exact (((continuous_id.matrix_conjTranspose.matrix_mul continuous_const).matrix_mul
        continuous_id).matrix_submatrix _ _).matrix_det.continuousOn
    · exact (hP n lam _ (hx.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1 i
  rw [← hH n ε y⁻¹ (fun k => κ (y⁻¹ * toMK k)) (fun k => β (y⁻¹ * toMK k)) (KC_inv hy)
    (fun k => hκ _ (hmem k)) _ hF]
  congr 1
  funext k
  obtain ⟨h1, h2, h3, h4, h5⟩ := hκ _ (hmem k)
  have hk : toMK k ∈ Kset ε := k.2
  generalize κ (y⁻¹ * toMK k) = c at *
  generalize β (y⁻¹ * toMK k) = b at *
  generalize toMK k = g at *
  have hg : g = y * (c * b) := by rw [← h5, Matrix.mul_nonsing_inv_cancel_left _ _ hyd]
  have hgg : gᴴ * g = 1 := Unitary.star_mul_self_of_mem hk.1
  have hc : cᴴ = b * gᴴ * y := by
    rw [← FormF.K_inv h1]
    apply Matrix.inv_eq_left_inv
    have : gᴴ * y * c * b = 1 := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc, ← hg, hgg]
    have := mul_eq_one_comm.1 this
    simpa only [Matrix.mul_assoc] using this
  have hz : c⁻¹ * x * c = b * (g⁻¹ * (y * x * yᴴ) * g) * bᴴ := by
    have : c = yᴴ * g * bᴴ := by
      rw [← Matrix.conjTranspose_conjTranspose c, hc]
      simp [Matrix.mul_assoc]
    rw [FormF.K_inv h1, FormF.K_inv hk, hc]
    conv_lhs => rw [this]
    simp only [Matrix.mul_assoc]
  have hne : ∀ l, b l l ≠ 0 := fun l => (h4 l).ne'
  have hΩ : g⁻¹ * (y * x * yᴴ) * g ∈ Omega n := by
    rw [FormF.K_inv hk]
    exact (hP n lam _ (hx'.conjTranspose_mul_mul_same
        (Matrix.mulVec_injective_of_isUnit (FormF.K_KC hk).1))).1
  have hΦ := (hT n lam b _ bᴴ h3 (fun i j h => by simp [h3 j i h]) (fun l => ⟨hne l, by simp [hne l]⟩) hΩ).2
  have hw : τ g w = ((∏ l, ‖b l l‖ ^ (-(lowK ε lam l)) : ℝ) : ℂ) • τ y (τ c w) := by
    conv_lhs => rw [hg]
    rw [hτ.2.1.2 _ hy _ (KC_mul (FormF.K_KC h1) h2), hτ.2.1.2 _ (FormF.K_KC h1) _ h2]
    simp only [ContinuousLinearMap.comp_apply]
    rw [tau_lo hτ h2 h3 h4, map_smul, map_smul]
  have hs := scalar_eq hlam ε (d := fun l => b l l) hne
  rw [hz, hΦ, hw, inner_smul_right, inner_smul_left, Complex.conj_ofReal, hadj, hτ.2.2.2.1 _ hy]
  simp only [Matrix.conjTranspose_apply]
  linear_combination (-(Phi lam (g⁻¹ * (y * x * yᴴ) * g) * (⟪τ yᴴ v, τ c w⟫_ℂ * ⟪τ c w, τ yᴴ u⟫_ℂ))) * hs

theorem psEquiv : PsEquiv := psEquiv_of GlobalTheory.PhiTriangular.phiTri GlobalTheory.Dec.phiPos GlobalTheory.Dec.iwasawaKC GlobalTheory.IwaInt.iwasawaInt

end GlobalTheory.Dec.Equivar
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalBlockFrameLocalSplit
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.LocSplit

theorem biorth_decomp {K : Type} [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    (h : Biorth r m T T') (y : Fin n → K) :
    y = ∑ b ∈ Finset.range m, T b *ᵥ (T' b *ᵥ y) := by
  have := congrArg (fun M : Matrix (Fin n) (Fin n) K => M *ᵥ y) h.2.2
  simp only [Matrix.one_mulVec, Matrix.sum_mulVec] at this
  simp only [Matrix.mulVec_mulVec]
  exact this.symm

theorem biorth_map {E K : Type} [CommRing E] [CommRing K] {n m : ℕ} {r : ℕ → ℕ}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    (h : Biorth r m T T') (φ : E →+* K) {P : Matrix (Fin n) (Fin n) K} (hP : IsUnit P) :
    Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have key : ∀ b b', (T' b).map φ * P * (P⁻¹ * (T b').map φ) = (T' b * T b').map φ := by
    intro b b'
    rw [Matrix.mul_assoc, ← Matrix.mul_assoc P, h1, Matrix.one_mul, Matrix.map_mul]
  refine ⟨fun b => ?_, fun b b' hb => ?_, ?_⟩
  · rw [key, h.1 b, Matrix.map_one _ (map_zero φ) (map_one φ)]
  · rw [key, h.2.1 b b' hb, Matrix.map_zero _ (map_zero φ)]
  · have e : ∀ b, P⁻¹ * (T b).map φ * ((T' b).map φ * P)
        = P⁻¹ * φ.mapMatrix (T b * T' b) * P := by
      intro b
      rw [RingHom.mapMatrix_apply, Matrix.map_mul]
      simp only [Matrix.mul_assoc]
    simp only [e]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum, h.2.2, map_one, mul_one, h2]

theorem map_mulVec_comp {E K : Type} [CommRing E] [CommRing K] {n p : ℕ} (φ : E →+* K)
    (A : Matrix (Fin n) (Fin p) E) (y : Fin p → E) :
    A.map φ *ᵥ (fun l => φ (y l)) = fun l => φ ((A *ᵥ y) l) := by
  ext i
  exact (RingHom.map_mulVec φ A y i).symm

theorem block_mem {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    {b k : ℕ} (hb : b < k) {v : Fin (r b) → K} (hv : v ∈ Λ b) : T b *ᵥ v ∈ F k := by
  rw [hF]
  intro b'
  rw [Matrix.mulVec_mulVec]
  by_cases e : b' = b
  · subst e
    rw [h.1, Matrix.one_mulVec]
    exact ⟨hv, fun hk => absurd hk (by omega)⟩
  · rw [h.2.1 _ _ e, Matrix.zero_mulVec]
    exact ⟨zero_mem _, fun _ => rfl⟩

theorem mem_locFlag_iff {E : Type} [Field E] [NumberField E] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule (𝓞 E) (Fin n → E)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) E} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) E}
    {Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)} (h : Biorth r m T T')
    (hΛ : ∀ b, Submodule.IsFullLattice E (Λ b))
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0))
    (φ : E →+* ℂ) {P : Matrix (Fin n) (Fin n) ℂ} (hP : IsUnit P) (k : ℕ) (y : Fin n → ℂ) :
    y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0 := by
  have hd : IsUnit P.det := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  constructor
  · intro hy b hb
    unfold locFlag at hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨z, hz, rfl⟩ := hx
      have h0 := ((hF k z).1 hz b).2 hb
      rw [Matrix.mulVec_mulVec, Matrix.mul_assoc, h1, Matrix.mul_one, map_mulVec_comp, h0]
      ext l
      simp
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.mulVec_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.mulVec_smul, hx, smul_zero]
  · intro hy
    rw [biorth_decomp (biorth_map h φ hP) y]
    refine Submodule.sum_mem _ fun b _ => ?_
    by_cases hb : k ≤ b
    · simp only [hy b hb, Matrix.mulVec_zero]
      exact zero_mem _
    have A : ∀ v : Fin (r b) → E,
        (P⁻¹ * (T b).map φ) *ᵥ (fun l => φ (v l)) ∈ locFlag φ P F k := by
      intro v
      have hv : v ∈ Submodule.span E (Λ b : Set (Fin (r b) → E)) := by
        letI := hΛ b
        rw [Submodule.IsFullLattice.span_eq_top]; trivial
      induction hv using Submodule.span_induction with
      | mem x hx =>
        rw [← Matrix.mulVec_mulVec, map_mulVec_comp]
        exact Submodule.subset_span ⟨_, block_mem h hF (by omega) hx, rfl⟩
      | zero =>
        have : (fun l => φ ((0 : Fin (r b) → E) l)) = 0 := by ext l; simp
        rw [this, Matrix.mulVec_zero]
        exact zero_mem _
      | add x y _ _ hx hy =>
        have : (fun l => φ ((x + y) l)) = (fun l => φ (x l)) + fun l => φ (y l) := by ext l; simp
        rw [this, Matrix.mulVec_add]
        exact add_mem hx hy
      | smul c x _ hx =>
        have : (fun l => φ ((c • x) l)) = φ c • fun l => φ (x l) := by ext l; simp
        rw [this, Matrix.mulVec_smul]
        exact Submodule.smul_mem _ _ hx
    have B : ∀ u : Fin (r b) → ℂ, (P⁻¹ * (T b).map φ) *ᵥ u ∈ locFlag φ P F k := by
      intro u
      have e : u = ∑ j, u j • fun l => φ ((Pi.single j (1 : E) : Fin (r b) → E) l) := by
        ext l
        simp [Finset.sum_apply, Pi.single_apply, apply_ite φ]
      rw [e, Matrix.mulVec_sum]
      refine Submodule.sum_mem _ fun j _ => ?_
      rw [Matrix.mulVec_smul]
      exact Submodule.smul_mem _ _ (A _)
    exact B _

theorem exists_lowers_blocks {R K : Type} [CommRing R] [CommRing K] [Algebra R K] {n m : ℕ} {r : ℕ → ℕ}
    {F : ℕ → Submodule R (Fin n → K)}
    {T : ∀ b, Matrix (Fin n) (Fin (r b)) K} {T' : ∀ b, Matrix (Fin (r b)) (Fin n) K}
    {Λ : ∀ b, Submodule R (Fin (r b) → K)} (h : Biorth r m T T')
    (hF : ∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) (c : ℕ)
    (Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) K)
    (hZ : ∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) :
    ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  refine ⟨∑ b : Fin m, T b * Z b * T' (b + c + 1), fun a y hy => ?_, fun a => ?_⟩
  · rw [Matrix.sum_mulVec]
    refine Submodule.sum_mem _ fun b _ => ?_
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    have h1 := (hF _ y).1 hy (b + c + 1)
    by_cases hb : (b : ℕ) < a
    · exact block_mem h hF hb (hZ b _ h1.1)
    · rw [h1.2 (by omega), Matrix.mulVec_zero, Matrix.mulVec_zero]
      exact zero_mem _
  · rw [Matrix.mul_sum, Matrix.sum_mul, Finset.sum_eq_single a]
    · rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.1, Matrix.one_mul, Matrix.mul_assoc, h.1,
        Matrix.mul_one]
    · intro b _ hb
      rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h.2.1 _ _ (fun e => hb (Fin.ext e.symm)),
        Matrix.zero_mul, Matrix.zero_mul, Matrix.zero_mul]
    · intro ha
      exact absurd (Finset.mem_univ a) ha

theorem locSplit : ∀ (E : Type) [Field E] [NumberField E] (n m : ℕ) (F : ℕ → Submodule (𝓞 E) (Fin n → E)) (r : ℕ → ℕ) (T : ∀ b, Matrix (Fin n) (Fin (r b)) E) (T' : ∀ b, Matrix (Fin (r b)) (Fin n) E) (Λ : ∀ b, Submodule (𝓞 E) (Fin (r b) → E)), Biorth r m T T' → (∀ b, Submodule.IsFullLattice E (Λ b)) → (∀ k y, y ∈ F k ↔ ∀ b, T' b *ᵥ y ∈ Λ b ∧ (k ≤ b → T' b *ᵥ y = 0)) → (∀ (φ : E →+* ℂ) (P : Matrix (Fin n) (Fin n) ℂ), IsUnit P → Biorth r m (fun b => P⁻¹ * (T b).map φ) (fun b => (T' b).map φ * P) ∧ ∀ k y, y ∈ locFlag φ P F k ↔ ∀ b, k ≤ b → ((T' b).map φ * P) *ᵥ y = 0) ∧ ∀ c, (∀ Y ∈ lowers F c, ∀ b, ∀ y ∈ Λ (b + c + 1), (T' b * Y * T (b + c + 1)) *ᵥ y ∈ Λ b) ∧ ∀ Z : ∀ b : Fin m, Matrix (Fin (r b)) (Fin (r (b + c + 1))) E, (∀ b : Fin m, ∀ y ∈ Λ (b + c + 1), Z b *ᵥ y ∈ Λ b) → ∃ Y ∈ lowers F c, ∀ b : Fin m, T' b * Y * T (b + c + 1) = Z b := by
  intro E _ _ n m F r T T' Λ h hΛ hF
  refine ⟨fun φ P hP => ⟨biorth_map h φ hP, mem_locFlag_iff h hΛ hF φ hP⟩, fun c => ⟨?_, ?_⟩⟩
  · intro Y hY b y hy
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    exact ((hF (b + 1) _).1 (hY (b + 1) _ (block_mem h hF (by omega) hy)) b).1
  · exact exists_lowers_blocks h hF c

end GlobalTheory.RadCov.LocSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealComplexSpanOrthonormalSkewFamily
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.SkewSpan

theorem skew_conj {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) : Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε = -B := by
  have h' : Bᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * B) := eq_neg_of_add_eq_zero_left h
  rw [Matrix.mul_assoc, h', Matrix.mul_neg, ← Matrix.mul_assoc, Formalism.REAL.Jm_mul_self,
    Matrix.one_mul]

theorem trace_twisted {n : ℕ} (ε : Fin n → Bool) {B : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.inG ε B) (X : Matrix (Fin n) (Fin n) ℂ) :
    (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace = - starRingEnd ℂ (X * Bᴴ).trace := by
  have h1 : (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * Bᴴ).trace
      = (Xᴴ * (Formalism.REAL.Jm ε * Bᴴ * Formalism.REAL.Jm ε)).trace := by
    rw [Matrix.mul_assoc, Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp only [Matrix.mul_assoc]
  have h2 : starRingEnd ℂ (X * Bᴴ).trace = (Xᴴ * B).trace := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose, Matrix.trace_mul_comm]
  rw [h1, h2, skew_conj ε h, Matrix.mul_neg, Matrix.trace_neg]

theorem real_span (n d : ℕ) (ε : Fin n → Bool) (B : Fin d → Matrix (Fin n) (Fin n) ℂ)
    (s : Set (Fin d)) (hB : ∀ i k, (B i * (B k)ᴴ).trace = if i = k then 1 else 0)
    (hG : ∀ i, Formalism.REAL.inG ε (B i)) :
    (∀ X, (X ∈ Submodule.span ℂ (B '' s) ∧ Formalism.REAL.inG ε X) ↔ X ∈ Submodule.span ℝ (B '' s)) ∧
    (∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0) ∧
    ∀ X i, (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε * (B i)ᴴ).trace
      = - starRingEnd ℂ (X * (B i)ᴴ).trace := by
  have h2 : ∀ X ∈ Submodule.span ℂ (B '' s), ∀ i, i ∉ s → (X * (B i)ᴴ).trace = 0 := by
    intro X hX i hi
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      rw [hB, if_neg]
      rintro rfl
      exact hi hk
    | zero => simp
    | add x y _ _ hx hy => rw [Matrix.add_mul, Matrix.trace_add, hx, hy, add_zero]
    | smul c x _ hx => rw [Matrix.smul_mul, Matrix.trace_smul, hx, smul_zero]
  have hexp : ∀ X ∈ Submodule.span ℂ (B '' s), X = ∑ i, (X * (B i)ᴴ).trace • B i := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      simp [hB]
    | zero => simp
    | add x y _ _ hx hy =>
      simp only [Matrix.add_mul, Matrix.trace_add, add_smul, Finset.sum_add_distrib]
      rw [← hx, ← hy]
    | smul c x _ hx =>
      simp only [Matrix.smul_mul, Matrix.trace_smul, smul_assoc, ← Finset.smul_sum]
      rw [← hx]
  refine ⟨fun X => ⟨?_, ?_⟩, h2, fun X i => trace_twisted ε (hG i) X⟩
  · rintro ⟨hX, hXG⟩
    rw [hexp X hX]
    refine Submodule.sum_mem _ fun i _ => ?_
    by_cases hi : i ∈ s
    · have h3 := trace_twisted ε (hG i) X
      rw [skew_conj ε hXG, Matrix.neg_mul, Matrix.trace_neg, neg_inj] at h3
      have h4 : (X * (B i)ᴴ).trace = (((X * (B i)ᴴ).trace.re : ℝ) : ℂ) :=
        (Complex.conj_eq_iff_re.mp h3.symm).symm
      rw [h4, Complex.coe_smul]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)
    · rw [h2 X hX i hi, zero_smul]
      exact Submodule.zero_mem _
  · intro hX
    refine ⟨Submodule.span_le_restrictScalars ℝ ℂ _ hX, ?_⟩
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨k, hk, rfl⟩ := hx
      exact hG k
    | zero => simp [Formalism.REAL.inG]
    | add x y _ _ hx hy =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_add, Matrix.add_mul, Matrix.mul_add, add_add_add_comm, hx, hy,
        add_zero]
    | smul c x _ hx =>
      unfold Formalism.REAL.inG at *
      rw [Matrix.conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add,
        hx, smul_zero]

end GlobalTheory.SkewSpan
end

