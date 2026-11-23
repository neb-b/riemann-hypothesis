module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0017
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.InfiniteAdeleHaarMapEqScaledVolume
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SelfDualMeasureRealDiagonal
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0191
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.T2SpaceNumberFieldInfiniteAdeles
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.CompletionIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueSelfDualMeasuresFinitePlace

@[expose] public section

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualMeasurePi
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.SdPi

section Abstract

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  {P : Type} [Fintype P]

theorem exists_form (e : A ≃+* (P → ℝ)) (he' : Continuous e.symm)
    (χ : A → ℂ) (hχc : Continuous χ) (hχ1 : ∀ x, ‖χ x‖ = 1) (hχa : ∀ x y, χ (x + y) = χ x * χ y)
    (hnd : ∀ x, (∀ y, χ (x * y) = 1) → x = 0) :
    ∃ a : P → ℝ, (∀ w, a w ≠ 0) ∧
      ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * e x w : ℝ) : ℂ)) := by
  classical
  obtain ⟨L, hLc, hLa, hL⟩ := GlobalTheory.GaugeEx.SdInf.exists_log_char (fun u => χ (e.symm u))
    (hχc.comp he') (fun u => hχ1 _) (fun u v => by rw [map_add (f := _), hχa])
  let Lh : (P → ℝ) →+ ℝ := AddMonoidHom.mk' L hLa
  let Ll : (P → ℝ) →ₗ[ℝ] ℝ :=
    { toFun := L, map_add' := hLa, map_smul' := fun c u => map_real_smul Lh hLc c u }
  let a : P → ℝ := fun w => L (fun j => if w = j then 1 else 0)
  have hform : ∀ u, L u = ∑ w, a w * u w := fun u => by
    have h := Ll.pi_apply_eq_sum_univ u
    change L u = ∑ i, u i • L (fun j => if i = j then 1 else 0) at h
    rw [h]
    exact Finset.sum_congr rfl fun w _ => by simp [a, mul_comm]
  have hchi : ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * e x w : ℝ) : ℂ)) :=
    fun x => by
      have := hL (e x)
      simp only [RingEquiv.symm_apply_apply] at this
      rw [this, hform]
  refine ⟨a, fun w hw => ?_, hchi⟩
  have h0 : e.symm (fun j => if w = j then 1 else 0) = 0 := hnd _ fun y => by
    have : ∑ j, a j * e (e.symm (fun j => if w = j then (1 : ℝ) else 0) * y) j = 0 :=
      Finset.sum_eq_zero fun j _ => by
        by_cases h : w = j
        · subst h; simp [hw]
        · simp [map_mul, h]
    rw [hchi, this]
    simp
  have h1 := congrFun (congrArg e h0) w
  simp at h1

def eqv (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) : A ≃ₜ+ (P → ℝ) :=
  { e.toAddEquiv with
    continuous_toFun := he
    continuous_invFun := he' }

theorem eqv_apply (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) (x : A) :
    eqv e he he' x = e x := rfl

def eqvPi (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) (ι : Type) :
    (ι → A) ≃ₜ+ (ι × P → ℝ) :=
  { toFun := fun x q => e (x q.1) q.2
    invFun := fun u i => e.symm fun w => u (i, w)
    left_inv := fun x => by funext i; simp
    right_inv := fun u => by funext q; simp
    map_add' := fun x y => by funext q; simp
    continuous_toFun := continuous_pi fun q =>
      (continuous_apply q.2).comp (he.comp (continuous_apply q.1))
    continuous_invFun := continuous_pi fun i =>
      he'.comp (continuous_pi fun w => continuous_apply (i, w)) }

theorem eqvPi_apply (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm) (ι : Type)
    (x : ι → A) (q : ι × P) : eqvPi e he he' ι x q = e (x q.1) q.2 := rfl

end Abstract

section Meas

variable {A : Type} [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
  [SecondCountableTopology A] [MeasurableSpace A] [BorelSpace A] {P : Type} [Fintype P]

theorem map_pi_eq (e : A ≃+* (P → ℝ)) (he : Continuous e) (he' : Continuous e.symm)
    (k : Measure A) [SigmaFinite k] (c₀ : ℝ≥0∞) (h0 : c₀ ≠ 0) (ht : c₀ ≠ ⊤)
    (hm : k.map (eqv e he he') = c₀ • (volume : Measure (P → ℝ))) (ι : Type) [Fintype ι] :
    (Measure.pi fun _ : ι => k).map (eqvPi e he he' ι) =
      (∏ _i : ι, c₀) • (volume : Measure (ι × P → ℝ)) := by
  set c : ℝ≥0∞ := ∏ _i : ι, c₀ with hcdef
  have hc0 : c ≠ 0 := Finset.prod_ne_zero_iff.2 fun _ _ => h0
  have hct : c ≠ ⊤ := ENNReal.prod_ne_top fun _ _ => ht
  have hEm : Measurable (eqvPi e he he' ι) := (eqvPi e he he' ι).continuous.measurable
  have hem : Measurable (eqv e he he') := (eqv e he he').continuous.measurable
  have hrect : ∀ s : ι × P → Set ℝ, (∀ q, MeasurableSet (s q)) →
      ((Measure.pi fun _ : ι => k).map (eqvPi e he he' ι)) (Set.pi Set.univ s) =
        c * ∏ q, volume (s q) := by
    intro s hs
    rw [Measure.map_apply hEm (MeasurableSet.univ_pi hs)]
    have hpre : eqvPi e he he' ι ⁻¹' Set.pi Set.univ s =
        Set.pi Set.univ fun i => eqv e he he' ⁻¹' Set.pi Set.univ fun w => s (i, w) := by
      ext x
      simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left, eqvPi_apply,
        eqv_apply, Prod.forall]
    rw [hpre, Measure.pi_pi]
    have hi : ∀ i, k (eqv e he he' ⁻¹' Set.pi Set.univ fun w => s (i, w)) =
        c₀ * ∏ w, volume (s (i, w)) := fun i => by
      rw [← Measure.map_apply hem (MeasurableSet.univ_pi fun w => hs _), hm, Measure.smul_apply,
        smul_eq_mul, volume_pi_pi]
    simp only [hi]
    rw [Finset.prod_mul_distrib, Fintype.prod_prod_type]
  have hv : (volume : Measure (ι × P → ℝ)) =
      c⁻¹ • (Measure.pi fun _ : ι => k).map (eqvPi e he he' ι) := by
    rw [volume_pi]
    refine Measure.pi_eq fun s hs => ?_
    rw [Measure.smul_apply, smul_eq_mul, hrect s hs, ← mul_assoc, ENNReal.inv_mul_cancel hc0 hct,
      one_mul]
  rw [hv, smul_smul, ENNReal.mul_inv_cancel hc0 hct, one_smul]

theorem selfDual_pi_of_form [LocallyCompactSpace A] (e : A ≃+* (P → ℝ)) (he : Continuous e)
    (he' : Continuous e.symm) (a : P → ℝ) (ha : ∀ w, a w ≠ 0) (χ : A → ℂ)
    (hχ : ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * e x w : ℝ) : ℂ)))
    (k : Measure A) (hk : SelfDual k fun s t => χ (s * t)) (ι : Type) [Fintype ι] :
    SelfDual (Measure.pi fun _ : ι => k) (fun x y => χ (x ⬝ᵥ y)) := by
  haveI := hk.1
  have h1 : SelfDual (k.map (eqv e he he')) (fun u v : P → ℝ =>
      Complex.exp (2 * Real.pi * Complex.I * ((∑ w, a w * (u w * v w) : ℝ) : ℂ))) := by
    refine (selfDual_transport A (P → ℝ) (eqv e he he') k _).1 ?_
    have hf : (fun x y : A => Complex.exp (2 * Real.pi * Complex.I *
        ((∑ w, a w * (eqv e he he' x w * eqv e he he' y w) : ℝ) : ℂ))) =
        fun s t => χ (s * t) := by
      funext s t
      simp only [hχ, map_mul, Pi.mul_apply, eqv_apply]
    rw [hf]
    exact hk
  have h2 := GlobalTheory.SelfDualDiagReal.eq_of_selfDual_diag P a ha (k.map (eqv e he he')) h1
  have hc0 : 0 < ∏ w, √|a w| := Finset.prod_pos fun w _ => Real.sqrt_pos.2 (abs_pos.2 (ha w))
  have h3 := map_pi_eq e he he' k _ (by simpa using hc0) ENNReal.ofReal_ne_top h2 ι
  have hcc : ∏ _i : ι, ENNReal.ofReal (∏ w, √|a w|) =
      ENNReal.ofReal (∏ q : ι × P, √|a q.2|) := by
    rw [← ENNReal.ofReal_prod_of_nonneg (fun _ _ => hc0.le), Fintype.prod_prod_type]
  have h4 := GlobalTheory.SelfDualDiagReal.selfDual_diag (ι × P) (fun q => a q.2) (fun q => ha q.2)
  rw [← hcc, ← h3] at h4
  have h5 := (selfDual_transport (ι → A) (ι × P → ℝ) (eqvPi e he he' ι)
    (Measure.pi fun _ => k) _).2 h4
  have hf : (fun x y : ι → A => Complex.exp (2 * Real.pi * Complex.I *
      ((∑ q : ι × P, a q.2 * (eqvPi e he he' ι x q * eqvPi e he he' ι y q) : ℝ) : ℂ))) =
      fun x y => χ (x ⬝ᵥ y) := by
    funext x y
    have hdot : ∀ w, e (x ⬝ᵥ y) w = ∑ i, e (x i) w * e (y i) w := fun w => by
      set_option synthInstance.maxHeartbeats 100000 in
        simp [dotProduct, map_sum, Finset.sum_apply]
    have hs : ∑ q : ι × P, a q.2 * (eqvPi e he he' ι x q * eqvPi e he he' ι y q) =
        ∑ w, a w * e (x ⬝ᵥ y) w := by
      simp only [eqvPi_apply, hdot, Finset.mul_sum]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [hχ, hs]
  rw [hf] at h5
  exact h5

end Meas

end GlobalTheory.CompanionTheory.SW.SdPi


open GlobalTheory.CompanionTheory.SW.SdPi GlobalTheory.CompanionTheory.SW.RealCoord in
theorem GlobalTheory.CompanionTheory.SW.selfDual_pi_inf : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ k : Measure (Ainf F), SelfDual k (fun s t => psiInf F ψ (s * t)) → ∀ (ι : Type) [Fintype ι], SelfDual (Measure.pi fun _ : ι => k) (fun x y => psiInf F ψ (x ⬝ᵥ y)) := by
  intro F _ _ hF ψ hψ k hk ι _
  haveI := hF
  obtain ⟨h1, h2, h3, h4, -⟩ := isLocR_Ainf F hF
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have he : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) :=
    (GlobalTheory.CompanionTheory.SW.RealCoord.isHomeomorph_coord F).continuous
  have he' : Continuous (GlobalTheory.CompanionTheory.SW.RealCoord.coord F).symm :=
    (GlobalTheory.CompanionTheory.SW.RealCoord.coordHomeo F).symm.continuous
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  obtain ⟨a, ha, hχ⟩ := GlobalTheory.CompanionTheory.SW.SdPi.exists_form
    (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) he'
    (psiInf F ψ) hpc (fun _ => hψ.2.1 _)
    (fun u v => by
      simp only [psiInf, map_add (f := _), ← AddChar.map_add_eq_mul]
      congr 1
      exact Prod.ext rfl (add_zero _).symm)
    (_root_.GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).2.2
  exact GlobalTheory.CompanionTheory.SW.SdPi.selfDual_pi_of_form
    (GlobalTheory.CompanionTheory.SW.RealCoord.coord F) he he' a ha _ hχ k hk ι
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArchimedeanSelfdualSymmetricFormUnique
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW

theorem selfDual_matrix_unique_of_equiv {R P ι : Type} [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [SecondCountableTopology R] [MeasurableSpace R] [BorelSpace R]
    [Fintype P] [Fintype ι] [DecidableEq ι] (a : R ≃+ (P → ℝ)) (ha : Continuous a)
    (ha' : Continuous a.symm) (χ : R → ℂ) (hc : Continuous χ) (h1 : ∀ x, ‖χ x‖ = 1)
    (hadd : ∀ x y, χ (x + y) = χ x * χ y) (hnd : ∀ x, (∀ y, χ (x * y) = 1) → x = 0)
    (AR : Matrix ι ι R) (hAR : ARᵀ = AR) (hu : IsUnit AR.det) {μ ν : Measure (ι → R)}
    (hμ : SelfDual μ (fun x y => χ (x ⬝ᵥ (AR *ᵥ y))))
    (hν : SelfDual ν (fun x y => χ (x ⬝ᵥ (AR *ᵥ y)))) : μ = ν := by
  obtain ⟨L₀, hL₀c, hL₀a, hL₀⟩ := GlobalTheory.GaugeEx.SdInf.exists_log_char
    (fun u => χ (a.symm u)) (hc.comp ha') (fun u => h1 _) (fun u v => by
      rw [map_add (f := _), hadd])
  let L : R → ℝ := fun x => L₀ (a x)
  have hLc : Continuous L := hL₀c.comp ha
  have hLa : ∀ x y, L (x + y) = L x + L y := fun x y => by simp only [L, map_add (f := _), hL₀a]
  have hL : ∀ x, χ x = Complex.exp (2 * Real.pi * Complex.I * ((L x : ℝ) : ℂ)) :=
    fun x => by simpa using hL₀ (a x)
  let e : (ι → R) ≃+ (ι → P → ℝ) := AddEquiv.piCongrRight fun _ => a
  have hec : Continuous e := by
    show Continuous fun (x : ι → R) i => a (x i)
    fun_prop
  have hec' : Continuous e.symm := by
    show Continuous fun (x : ι → P → ℝ) i => a.symm (x i)
    fun_prop
  have key := GlobalTheory.GaugeEx.SdInf.existsUnique_of_equiv e hec hec'
    (fun x y => L (x ⬝ᵥ (AR *ᵥ y)))
    (fun x x' y => by rw [add_dotProduct, hLa])
    (fun x y => by
      have : x ⬝ᵥ (AR *ᵥ y) = y ⬝ᵥ (AR *ᵥ x) := by
        rw [Matrix.dotProduct_mulVec, dotProduct_comm, ← Matrix.mulVec_transpose, hAR]
      rw [this])
    (fun y => hLc.comp (by
      have : Continuous fun x : ι → R => ∑ i, x i * (AR *ᵥ y) i :=
        continuous_finsetSum _ fun i _ => (continuous_apply i).mul continuous_const
      exact this))
    (fun x h => by
      funext i
      refine hnd _ fun t => ?_
      have h0 := h (AR⁻¹ *ᵥ Pi.single i t)
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hu, Matrix.one_mulVec,
        dotProduct_single] at h0
      rw [hL, h0]
      simp)
  have hfun : (fun x y : ι → R => χ (x ⬝ᵥ (AR *ᵥ y))) =
      fun x y => Complex.exp (2 * Real.pi * Complex.I * ((L (x ⬝ᵥ (AR *ᵥ y)) : ℝ) : ℂ)) := by
    funext x y
    exact hL _
  rw [hfun] at hμ hν
  exact key.unique hμ hν

theorem selfDual_rationalForm_Ainf_unique : ∀ (F : Type) [Field F] [NumberField F], IsTotallyReal F → ∀ (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ k : Measure (Ainf F), SelfDual k (fun s t => psiInf F ψ (s * t)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 → ∀ μ ν : Measure (ι → Ainf F), SelfDual μ (fun x y => psiInf F ψ (x ⬝ᵥ (A.map (algebraMap F (Ainf F)) *ᵥ y))) → SelfDual ν (fun x y => psiInf F ψ (x ⬝ᵥ (A.map (algebraMap F (Ainf F)) *ᵥ y))) → μ = ν := by
  intro F _ _ hF ψ hψ _ _ ι _ _ A hA hdet μ ν hμ hν
  haveI : IsTotallyReal F := hF
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hF
  haveI := h1
  haveI := h3
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  have hnd : ∀ x : Ainf F, (∀ y, psiInf F ψ (x * y) = 1) → x = 0 := (_root_.GlobalTheory.GaugeEx.CharLoc.char_local F ψ hψ).2.2
  obtain ⟨a, ha, ha'⟩ := GlobalTheory.GaugeEx.SdInf.exists_equiv_Ainf F
  have hpc : Continuous (psiInf F ψ) := hψ.1.comp (continuous_id.prodMk continuous_const)
  have hadd : ∀ x y, psiInf F ψ (x + y) = psiInf F ψ x * psiInf F ψ y := fun x y => by
    simp only [psiInf, map_add (f := _), ← AddChar.map_add_eq_mul]
    congr 1
    exact Prod.ext rfl (add_zero _).symm
  have hAR : (A.map (algebraMap F (Ainf F)))ᵀ = A.map (algebraMap F (Ainf F)) := by
    rw [← Matrix.transpose_map, hA.eq]
  have hu : IsUnit (A.map (algebraMap F (Ainf F))).det := by
    have : (A.map (algebraMap F (Ainf F))).det = algebraMap F (Ainf F) A.det :=
      ((algebraMap F (Ainf F)).map_det A).symm
    rw [this]
    exact (Ne.isUnit hdet).map _
  exact selfDual_matrix_unique_of_equiv a ha ha' (psiInf F ψ) hpc (fun u => hψ.2.1 _) hadd hnd
    _ hAR hu hμ hν

end GlobalTheory.CompanionTheory.SW
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.NonarchimedeanSelfdualSymmetricFormUnique
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdUniq

theorem not_selfDual_one (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [T2Space V] [LocallyCompactSpace V] [MeasurableSpace V] [BorelSpace V] [Nontrivial V]
    (k : Measure V) : ¬ SelfDual k (fun _ _ => (1 : ℂ)) := by
  intro hk
  haveI := hk.1
  obtain ⟨h, hh⟩ := exists_ne (0 : V)
  obtain ⟨g, hg1, hg0, hgc, -⟩ := exists_continuous_one_zero_of_isCompact (X := V)
    (s := {0}) (t := {-h}) isCompact_singleton isClosed_singleton
    (by simpa [eq_comm] using hh)
  let g' : V → ℂ := fun x => ((g x : ℝ) : ℂ)
  have hc' : Continuous g' := Complex.continuous_ofReal.comp g.continuous
  have hs' : HasCompactSupport g' := hgc.comp_left (g := Complex.ofReal) (by simp)
  let Φ : V → ℂ := fun x => g' x - g' (x - h)
  have hc2 : Continuous fun x => g' (x - h) := hc'.comp (by fun_prop)
  have hs2 : HasCompactSupport fun x => g' (x - h) :=
    hs'.comp_homeomorph (Homeomorph.subRight h)
  have hΦc : Continuous Φ := hc'.sub hc2
  have hΦs : HasCompactSupport Φ := hs'.sub hs2
  have e : ∫ x, Φ x * (1 : ℂ) ∂k = 0 := by
    simp only [mul_one, Φ]
    rw [integral_sub (hc'.integrable_of_hasCompactSupport hs')
      (hc2.integrable_of_hasCompactSupport hs2), integral_sub_right_eq_self g' h, sub_self]
  have hI : Integrable (fun _ : V => ∫ x, Φ x * (1 : ℂ) ∂k) k := by
    rw [e]
    exact integrable_zero V ℂ k
  have key : ∫ _ : V, (∫ x, Φ x * (1 : ℂ) ∂k) * (1 : ℂ) ∂k = Φ (-0) := hk.2 Φ hΦc hΦs hI 0
  rw [e, zero_mul, integral_zero, neg_zero] at key
  have h1 : g 0 = 1 := hg1 rfl
  have h2 : g (-h) = 0 := hg0 rfl
  have h3 : Φ 0 = 1 := by simp [Φ, g', h1, h2]
  rw [h3] at key
  exact zero_ne_one key

variable (F : Type) [Field F] [NumberField F]

noncomputable def chiV (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) : AddChar (Fv F v) ℂ :=
  ψ.compAddMonoidHom ((AddMonoidHom.inr (Ainf F) (Af F)).comp (GlobalTheory.AdelicU.singleFin v).toAddMonoidHom)

theorem chiV_apply (ψ : AddChar (AF F) ℂ) (v : HeightOneSpectrum (𝓞 F)) (t : Fv F v) :
    chiV F ψ v t = psiV F ψ v t := rfl

theorem selfDual_unique_coord : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsCharAF F ψ → ∀ (v : HeightOneSpectrum (𝓞 F)) (k : Measure (Fv F v)), SelfDual k (fun s t => psiV F ψ v (s * t)) → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (A : Matrix ι ι F), A.IsSymm → A.det ≠ 0 → ∀ μ ν : Measure (ι → Fv F v), SelfDual μ (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → SelfDual ν (fun x y => psiV F ψ v (x ⬝ᵥ (A.map (algebraMap F (Fv F v)) *ᵥ y))) → μ = ν := by
  intro F _ _ ψ hψ v k hk ι _ _ A hA hdet μ ν hμ hν
  obtain ⟨h1, h2, h3, h4, -⟩ := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  have hc : Continuous (chiV F ψ v) :=
    hψ.1.comp (Continuous.prodMk continuous_const (GlobalTheory.AdelicU.continuous_singleFin v))
  have hu : ∀ t, ‖chiV F ψ v t‖ = 1 := fun t => hψ.2.1 _
  have hne : ∃ t, chiV F ψ v t ≠ 1 := by
    by_contra hcon
    push Not at hcon
    refine not_selfDual_one (Fv F v) k ?_
    have e : (fun s t : Fv F v => psiV F ψ v (s * t)) = fun _ _ => (1 : ℂ) := by
      funext s t
      exact hcon _
    rwa [e] at hk
  set M : Matrix ι ι (Fv F v) := A.map (algebraMap F (Fv F v)) with hM
  have hMs : Mᵀ = M := by
    rw [hM, ← Matrix.transpose_map, hA.eq]
  have hMd : M.det ≠ 0 := by
    have : M.det = algebraMap F (Fv F v) A.det := by
      rw [hM]; exact (RingHom.map_det (algebraMap F (Fv F v)) A).symm
    rw [this]
    exact (map_ne_zero _).2 hdet
  have hs : ∀ x y, Matrix.toBilin' M x y = Matrix.toBilin' M y x := by
    intro x y
    rw [Matrix.toBilin'_apply', Matrix.toBilin'_apply', Matrix.dotProduct_mulVec, dotProduct_comm,
      ← Matrix.mulVec_transpose, hMs]
  have hn : ∀ x, (∀ y, Matrix.toBilin' M x y = 0) → x = 0 := by
    intro x hx
    refine Matrix.eq_zero_of_vecMul_eq_zero hMd ?_
    refine dotProduct_eq_zero _ fun w => ?_
    rw [← Matrix.dotProduct_mulVec, ← Matrix.toBilin'_apply']
    exact hx w
  have huniq := GlobalTheory.SelfDualFinite.existsUnique_of_bilin v (chiV F ψ v) hc hu hne (ι → Fv F v)
    (Matrix.toBilin' M) hs hn
  have e : (fun x y : ι → Fv F v => chiV F ψ v (Matrix.toBilin' M x y)) =
      fun x y => psiV F ψ v (x ⬝ᵥ (M *ᵥ y)) := by
    funext x y
    rw [Matrix.toBilin'_apply', chiV_apply]
  rw [e] at huniq
  exact huniq.unique ⟨hμ.1, hμ.2⟩ ⟨hν.1, hν.2⟩

end GlobalTheory.CompanionTheory.SW.SdUniq
end

