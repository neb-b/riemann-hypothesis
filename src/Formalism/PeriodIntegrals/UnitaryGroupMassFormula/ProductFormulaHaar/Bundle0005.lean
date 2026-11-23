module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0001
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0004
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ModFIotaFinitePlace
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0003
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.Bundle0002
public import Formalism.PeriodIntegrals.Bundle0014

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.HaarMain
section
noncomputable section

open MeasureTheory Measure ValuativeRel Topology Module
open scoped NNReal ENNReal Pointwise

namespace PI.ProdFormulaE.HaarBox

variable {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

theorem modF_nonneg' (a : K) : 0 ≤ modF K a := by
  rcases eq_or_ne a 0 with h | h
  · rw [h, modF_zero]
  · exact (modF_pos h).le

variable {E : Type} [AddCommGroup E] [Module K E] [TopologicalSpace E] [IsModuleTopology K E]
variable {ι : Type} [Fintype ι] [DecidableEq ι]

def equivOfDet (b : Basis ι K E) (A : Matrix ι ι K) (hA : A.det ≠ 0) : E ≃ₗ[K] E :=
  LinearEquiv.ofIsUnitDet (f := Matrix.toLin b b A) (v := b) (v' := b)
    (by rw [LinearMap.toMatrix_toLin]; exact hA.isUnit)

theorem coe_equivOfDet (b : Basis ι K E) (A : Matrix ι ι K) (hA : A.det ≠ 0) :
    ⇑(equivOfDet b A hA) = Matrix.toLin b b A := rfl

variable [MeasurableSpace E] [BorelSpace E]

def ScaleBox (b : Basis ι K E) (μ : Measure E) : Prop :=
  ∀ (i : ι) (a : K) (ha : a ≠ 0),
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' box b 1) =
      (distribHaarChar K (Units.mk0 a ha) : ℝ≥0∞) * μ (box b 1)

def TransvBox (b : Basis ι K E) : Prop :=
  ∀ t : Matrix.TransvectionStruct ι K, ∃ γ : ι → ValueGroupWithZero K, (∀ i, γ i ≠ 0) ∧
    Matrix.toLin b b t.toMatrix '' box b γ = box b γ

private theorem measure_toLin_mul_image_of_forall (b : Basis ι K E) (μ : Measure E) (A B : Matrix ι ι K)
    (hA : ∀ S : Set E, μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S)
    (hB : ∀ S : Set E, μ (Matrix.toLin b b B '' S) = ENNReal.ofReal (modF K B.det) * μ S)
    (S : Set E) :
    μ (Matrix.toLin b b (A * B) '' S) = ENNReal.ofReal (modF K (A * B).det) * μ S := by
  rw [Matrix.toLin_mul b b b, LinearMap.coe_comp, Set.image_comp, hA, hB, Matrix.det_mul, modF_mul,
    ENNReal.ofReal_mul (modF_nonneg' _), mul_assoc]

private theorem measure_toLin_transvection_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (htrans : TransvBox b) (t : Matrix.TransvectionStruct ι K) (S : Set E) :
    μ (Matrix.toLin b b t.toMatrix '' S) = ENNReal.ofReal (modF K t.toMatrix.det) * μ S := by
  obtain ⟨γ, hγ, himg⟩ := htrans t
  have hdet : t.toMatrix.det ≠ 0 := by rw [Matrix.TransvectionStruct.det]; exact one_ne_zero
  rw [Matrix.TransvectionStruct.det, modF_one, ENNReal.ofReal_one, one_mul]
  have h := image_eq_of_box b μ (equivOfDet b t.toMatrix hdet) γ hγ 1
    (by rw [coe_equivOfDet, himg, one_mul]) S
  rwa [coe_equivOfDet, one_mul] at h

private theorem measure_toLin_diagonal_update_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (i : ι) (a : K) (ha : a ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal (Function.update 1 i a)) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal (Function.update (1 : ι → K) i a)).det) * μ S := by
  have hdetv : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det = a := by
    rw [Matrix.det_diagonal, Finset.prod_update_of_mem (Finset.mem_univ i)]
    simp
  have hdet : (Matrix.diagonal (Function.update (1 : ι → K) i a)).det ≠ 0 := by
    rw [hdetv]
    exact ha
  rw [hdetv, modF_of_ne ha, ENNReal.ofReal_coe_nnreal]
  have h := image_eq_of_box b μ (equivOfDet b _ hdet) 1 (fun _ => by simp) _
    (by rw [coe_equivOfDet]; exact hscale i a ha) S
  rwa [coe_equivOfDet] at h

private theorem measure_toLin_diagonal_image (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (D : ι → K) (hD : ∀ i, D i ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
      ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S := by
  classical
  suffices h : ∀ s : Finset ι, ∀ D : ι → K, (∀ i, D i ≠ 0) → (∀ i ∉ s, D i = 1) → ∀ S : Set E,
      μ (Matrix.toLin b b (Matrix.diagonal D) '' S) =
        ENNReal.ofReal (modF K (Matrix.diagonal D).det) * μ S from
    h Finset.univ D hD (fun i hi => absurd (Finset.mem_univ i) hi) S
  intro s
  induction s using Finset.induction_on with
  | empty =>
    intro D _ h1 S
    have hD1 : D = 1 := funext fun i => h1 i (by simp)
    subst hD1
    have h1' : Matrix.diagonal (1 : ι → K) = 1 := Matrix.diagonal_one
    rw [h1', Matrix.toLin_one, LinearMap.id_coe, Set.image_id, Matrix.det_one, modF_one,
      ENNReal.ofReal_one, one_mul]
  | insert j s hj ih =>
    intro D h0 h1 S
    have hsplit : Matrix.diagonal D = Matrix.diagonal (Function.update D j 1) *
        Matrix.diagonal (Function.update 1 j (D j)) := by
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h]
    rw [hsplit]
    refine measure_toLin_mul_image_of_forall b μ _ _ (ih _ ?_ ?_) (measure_toLin_diagonal_update_image b μ hscale j (D j) (h0 j)) S
    · intro i
      by_cases h : i = j
      · subst h; simp
      · simp [Function.update_of_ne h, h0 i]
    · intro i hi
      by_cases h : i = j
      · subst h; simp
      · rw [Function.update_of_ne h]
        exact h1 i (by simp [h, hi])

theorem image_toLin (b : Basis ι K E) (μ : Measure E) [μ.IsAddHaarMeasure]
    (hscale : ScaleBox b μ) (htrans : TransvBox b)
    (A : Matrix ι ι K) (hA : A.det ≠ 0) (S : Set E) :
    μ (Matrix.toLin b b A '' S) = ENNReal.ofReal (modF K A.det) * μ S := by
  classical
  revert S
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (fun M => ∀ S : Set E, μ (Matrix.toLin b b M '' S) = ENNReal.ofReal (modF K M.det) * μ S)
    A hA ?_ ?_ ?_
  · intro D hD S
    refine measure_toLin_diagonal_image b μ hscale D (fun i => ?_) S
    rw [Matrix.det_diagonal] at hD
    exact Finset.prod_ne_zero_iff.1 hD i (Finset.mem_univ i)
  · intro t S
    exact measure_toLin_transvection_image b μ htrans t S
  · intro A B _ _ hA hB S
    exact measure_toLin_mul_image_of_forall b μ A B hA hB S

end PI.ProdFormulaE.HaarBox

namespace PI.ProdFormulaE.HaarAlgP

open HaarBox

theorem haarAlg_of
    (hscale : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] [MeasurableSpace E] [BorelSpace E] (n : ℕ) (b : Basis (Fin n) K E)
      (μ : Measure E) [μ.IsAddHaarMeasure], ScaleBox b μ)
    (htrans : ∀ (K : Type) [Field K] [ValuativeRel K] [TopologicalSpace K]
      [IsNonarchimedeanLocalField K] (E : Type) [AddCommGroup E] [Module K E] [TopologicalSpace E]
      [IsModuleTopology K E] (n : ℕ) (b : Basis (Fin n) K E), TransvBox b) :
    St.HaarAlg := by
  intro K _ _ _ _ A _ _ _ _ _ _ _ _ μ _ y hy S
  classical
  let b := Module.finBasis K A
  set M := LinearMap.toMatrix b b (LinearMap.mulLeft K y) with hM
  have hdet : M.det = Algebra.norm K y := by
    rw [hM, LinearMap.det_toMatrix, Algebra.norm_apply]
    rfl
  have hdet0 : M.det ≠ 0 := by
    rw [hdet]
    exact (hy.map (Algebra.norm K)).ne_zero
  have h := image_toLin b μ (hscale K A _ b μ) (htrans K A _ b) M hdet0 S
  rw [hdet, hM, Matrix.toLin_toMatrix] at h
  exact h

end PI.ProdFormulaE.HaarAlgP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormSt
section
open IsDedekindDomain NumberField

namespace PI.ProdFormulaE

theorem normLoc_of (hI : IndexFormula) (hC : CardStep) : St.NormLoc :=
  fun _F _ _ p _K _ _ _ _ ι hd hv z => modF_iota_finitePlace p ι hI hC hd hv z

theorem normLoc_of_card (hC : CardStep) : St.NormLoc := normLoc_of modulus_mul_card_quotient hC

theorem modulus_eq_finitePlace : St.NormLoc := normLoc_of_card card_quotient_eq_absNorm

theorem modF_localization_eq_adicAbv {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] {sig : E →ₐ[F] E} {p : HeightOneSpectrum (𝓞 F)}
    (L : Formalism.MainNotions.S.Loc.LocAt F E sig p) [IsNonarchimedeanLocalField L.Fp] (z : F) :
    modF L.Fp (L.ιF z) = NumberField.HeightOneSpectrum.adicAbv F p z :=
  modF_locAt modulus_mul_card_quotient card_quotient_eq_absNorm L z

end PI.ProdFormulaE
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.NormTraceLeOne
section
noncomputable section

namespace PI.ProdFormulaE.TrIntP

theorem norm_le_one_of_isIntegral {ℓ : ℕ} [Fact ℓ.Prime] {t : ℚ_[ℓ]} (ht : IsIntegral ℤ t) :
    ‖t‖ ≤ 1 := by
  have ht' : IsIntegral ℤ_[ℓ] t := ht.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 ht'
  rw [← hy]
  exact y.norm_le_one

theorem norm_trace_le_one : St.TrInt := by
  intro ℓ _ K _ _ _ w hw
  exact norm_le_one_of_isIntegral (Algebra.isIntegral_trace hw)

end PI.ProdFormulaE.TrIntP
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ProdFormulaEOf
section
noncomputable section

open IsDedekindDomain NumberField MeasureTheory ValuativeRel Formalism.MainNotions.S.Loc

namespace PI.ProdFormulaE.Top

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {sig : E →ₐ[F] E}

theorem modF_nonneg {K : Type} [Field K] [TopologicalSpace K] [IsTopologicalRing K]
    [LocallyCompactSpace K] (a : K) : 0 ≤ modF K a := by
  by_cases h : a = 0
  · rw [h, modF_zero]
  · exact (modF_pos h).le

theorem modK_eq (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    {p : HeightOneSpectrum (𝓞 F)} (L : LocAt F E sig p) (M : Model L.Fp L.Ep) (hM : M.OK)
    {x : E} (hx : x ≠ 0) :
    M.modK (L.ιE x) = FinitePlace.mk p (Algebra.norm F x) := by
  haveI := L.lf
  haveI := hM.borel
  haveI := hM.haar.haar
  haveI := L.free
  haveI := Base.finite L
  haveI := L.top
  unfold Model.modK
  rw [hH L.Fp L.Ep M.mu (L.ιE x) (Base.isUnit_ιE L hx) _, hM.haar.volR, mul_one,
    ENNReal.toReal_ofReal (modF_nonneg _), Base.norm_ιE L h2, hN F p L.Fp L.ιF L.dense L.val]

theorem clause1 (hH : St.HaarAlg) (hN : St.NormLoc) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)
    (M : ∀ p, Model (L p).Fp (L p).Ep) (hM : ∀ p, (M p).OK) (x : E) (hx : x ≠ 0) :
    (Function.mulSupport fun p => (M p).modK ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (M p).modK ((L p).ιE x) = |((Algebra.norm ℚ x : ℚ) : ℝ)|⁻¹ := by
  have hz : Algebra.norm F x ≠ 0 := Algebra.norm_ne_zero_iff.2 hx
  have he : (fun p => (M p).modK ((L p).ιE x)) =
      (fun w : FinitePlace F => w (Algebra.norm F x)) ∘ FinitePlace.equivHeightOneSpectrum.symm := by
    funext p
    rw [modK_eq hH hN h2 (L p) (M p) (hM p) hx]
    rfl
  rw [he]
  refine ⟨?_, ?_⟩
  · rw [Function.mulSupport_comp_eq_preimage]
    exact (FinitePlace.hasFiniteMulSupport hz).preimage
      (FinitePlace.equivHeightOneSpectrum.symm.injective.injOn)
  · rw [Function.comp_def, finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm
      (f := fun w : FinitePlace F => w (Algebra.norm F x)),
      FinitePlace.prod_eq_inv_abs_norm hz, Algebra.norm_norm, Rat.cast_inv, Rat.cast_abs]

theorem fibFin (hR : St.ResCharIff) {q : ℕ} (hq : q.Prime) :
    {p : HeightOneSpectrum (𝓞 F) | resChar p = q}.Finite := by
  have hne : Ideal.span {(q : 𝓞 F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hq.ne_zero
  refine (Ideal.finite_factors hne).subset fun p hp => ?_
  simp only [Set.mem_ofPred_eq] at hp ⊢
  rw [Ideal.dvd_span_singleton]
  exact (hR F p q hq).1 hp

theorem transport {K : Type} [Field K] [TopologicalSpace K] {m : ℕ} (ℓ : ℕ) (h : m = ℓ)
    [Fact m.Prime] [Fact ℓ.Prime] [Algebra ℚ_[m] K] (hc : Continuous (algebraMap ℚ_[m] K))
    (hf : FiniteDimensional ℚ_[m] K) :
    ∃ A : Algebra ℚ_[ℓ] K, Continuous (@algebraMap ℚ_[ℓ] K _ _ A) ∧
      @FiniteDimensional ℚ_[ℓ] K _ _ A.toModule ∧
      ∀ (w : K) (a : ℚ), ‖@Algebra.trace ℚ_[ℓ] K _ _ A w - (a : ℚ_[ℓ])‖ =
        ‖Algebra.trace ℚ_[m] K w - (a : ℚ_[m])‖ := by
  subst h
  exact ⟨inferInstance, hc, hf, fun _ _ => rfl⟩

theorem transport_at (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (q : ℕ) [Fact q.Prime]
    (i : {p : HeightOneSpectrum (𝓞 F) // resChar p = q}) :
    ∃ A : Algebra ℚ_[q] (L i.1).Fp, Continuous (@algebraMap ℚ_[q] (L i.1).Fp _ _ A) ∧
      @FiniteDimensional ℚ_[q] (L i.1).Fp _ _ A.toModule ∧
      ∀ (w : (L i.1).Fp) (a : ℚ), ‖@Algebra.trace ℚ_[q] (L i.1).Fp _ _ A w - (a : ℚ_[q])‖ =
        (haveI := (L i.1).ellPrime
         ‖Algebra.trace ℚ_[resChar i.1] (L i.1).Fp w - (a : ℚ_[resChar i.1])‖) :=
  haveI := (L i.1).ellPrime
  transport q i.2 (L i.1).qlCont (L i.1).qlFin

def fam (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (q : ℕ) [Fact q.Prime] :
    Tr.LocFam F q {p : HeightOneSpectrum (𝓞 F) // resChar p = q} where
  P i := i.1
  K i := (L i.1).Fp
  fld _ := inferInstance
  vr _ := inferInstance
  top _ := inferInstance
  lf i := (L i.1).lf
  cz i := (L i.1).char0
  alg i := (transport_at L q i).choose
  cont i := (transport_at L q i).choose_spec.1
  fin i := (transport_at L q i).choose_spec.2.1
  ιF i := (L i.1).ιF
  dense i := (L i.1).dense
  val i := (L i.1).val

theorem fam_over (hR : St.ResCharIff) (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p)
    (q : ℕ) [hq : Fact q.Prime] : (fam L q).Over := by
  refine ⟨Subtype.val_injective, fun p => ⟨?_, fun h => ⟨⟨p, (hR F p q hq.out).2 h⟩, rfl⟩⟩⟩
  rintro ⟨i, rfl⟩
  exact (hR F i.1 q hq.out).1 i.2

theorem clause2 (hT : Tr.TrSum) (hI : St.TrInt) (hR : St.ResCharIff) (h2 : Module.finrank F E = 2)
    (L : ∀ p : HeightOneSpectrum (𝓞 F), LocAt F E sig p) (x : E) :
    (Function.mulSupport fun p => (L p).psiE ((L p).ιE x)).Finite ∧
      ∏ᶠ p, (L p).psiE ((L p).ιE x) =
        Complex.exp (2 * Real.pi * Complex.I * (((Algebra.trace ℚ E x : ℚ) : ℂ))) := by
  classical
  set z := Algebra.trace F E x with hzdef
  have hex (p : HeightOneSpectrum (𝓞 F)) :
      ∃ a : ℚ, (∃ n : ℕ, a.den = (resChar p) ^ n) ∧
        (haveI := (L p).ellPrime
         ‖Algebra.trace ℚ_[resChar p] (L p).Fp ((L p).ιF z) - (a : ℚ_[resChar p])‖ ≤ 1) ∧
        (L p).psiE ((L p).ιE x) = Complex.exp (2 * Real.pi * Complex.I * (a : ℂ)) := by
    obtain ⟨a, ha, hn, he⟩ := (L p).psiE_def ((L p).ιE x)
    exact ⟨a, ha, by rwa [Base.trace_ιE_ql (L p) h2] at hn, he⟩
  choose a ha hn he using hex
  have hfun : (fun p => (L p).psiE ((L p).ιE x)) =
      fun p => Complex.exp (2 * Real.pi * Complex.I * ((a p : ℚ) : ℂ)) := funext he
  rw [hfun]
  have hprime : ∀ p : HeightOneSpectrum (𝓞 F), (resChar p).Prime := fun p => (L p).ellPrime.out
  let fib : ℕ → Finset (HeightOneSpectrum (𝓞 F)) := fun q =>
    if hq : q.Prime then (fibFin hR hq).toFinset else ∅
  have hfib : ∀ p q, p ∈ fib q ↔ resChar p = q := by
    intro p q
    by_cases hq : q.Prime
    · simp only [fib, dif_pos hq, Set.Finite.mem_toFinset, Set.mem_ofPred_eq]
    · simp only [fib, dif_neg hq, Finset.notMem_empty, false_iff]
      rintro rfl
      exact hq (hprime p)

  have hfin : {p | (a p).den ≠ 1}.Finite := by
    obtain ⟨d, hd0, hdint⟩ :=
      (IsFractionRing.isAlgebraic_iff ℤ ℚ F |>.mpr (.of_finite ℚ z)).exists_integral_multiple
    have hne : Ideal.span {((d : ℤ) : 𝓞 F)} ≠ 0 := by
      rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
      exact_mod_cast hd0
    refine (Ideal.finite_factors hne).subset fun p hp => ?_
    simp only [Set.mem_ofPred_eq] at hp ⊢
    rw [Ideal.dvd_span_singleton]
    by_contra hdp
    apply hp
    haveI := (L p).ellPrime
    have hres : ((resChar p : ℕ) : 𝓞 F) ∈ p.asIdeal := (hR F p (resChar p) (hprime p)).1 rfl
    have hnd : ¬ ((resChar p : ℕ) : ℤ) ∣ d := by
      rintro ⟨k, hk⟩
      apply hdp
      rw [hk, Int.cast_mul]
      exact p.asIdeal.mul_mem_right _ (by exact_mod_cast hres)
    have hd1 : ‖(d : ℚ_[resChar p])‖ = 1 :=
      le_antisymm (Padic.norm_int_le_one d)
        (not_lt.1 fun h => hnd (Padic.norm_intCast_lt_one_iff.1 h))
    have hint : IsIntegral ℤ ((L p).ιF (d • z)) := hdint.map (L p).ιF.toIntAlgHom
    haveI := (L p).qlFin
    have hT1 := hI (resChar p) (L p).Fp ((L p).ιF (d • z)) hint
    have hsm : (L p).ιF (d • z) = algebraMap ℚ_[resChar p] (L p).Fp (d : ℚ_[resChar p]) *
        (L p).ιF z := by
      rw [zsmul_eq_mul, map_mul, map_intCast, map_intCast]
    rw [hsm, ← Algebra.smul_def, map_smul, smul_eq_mul, norm_mul, hd1,
      one_mul] at hT1
    obtain ⟨n, hn'⟩ := ha p
    exact Frac.den_eq_one_of_norm_le_one hn' hT1 (hn p)
  refine Frac.finprod_exp resChar hprime a ha fib hfib hfin _ fun q hq => ?_

  have hfs : Set.Finite {p : HeightOneSpectrum (𝓞 F) | resChar p = q} := fibFin hR hq.out
  haveI : Fintype {p : HeightOneSpectrum (𝓞 F) // resChar p = q} := hfs.fintype
  have hsum := hT F q _ (fam L q) (fam_over hR L q) z
  have htr : Algebra.trace ℚ F z = Algebra.trace ℚ E x := Algebra.trace_trace x
  rw [htr] at hsum
  have hsub : ∑ i ∈ fib q, (a i : ℚ_[q]) =
      ∑ i : {p : HeightOneSpectrum (𝓞 F) // resChar p = q}, (a i.1 : ℚ_[q]) :=
    Finset.sum_subtype _ (fun p => hfib p q) _
  rw [hsub, ← eq_ratCast (algebraMap ℚ ℚ_[q]), ← hsum]
  refine Frac.norm_sum_sub_sum_le_one _ _ _ fun i _ => ?_
  have h1 := (transport_at L q i).choose_spec.2.2 ((L i.1).ιF z) (a i.1)
  exact h1.trans_le (hn i.1)

theorem prodFormulaE_of (hH : St.HaarAlg) (hN : St.NormLoc) (hT : Tr.TrSum) (hI : St.TrInt)
    (hR : St.ResCharIff) : PI.ProdFormulaE.ProdFormulaE := by
  intro F E _ _ _ _ _ sig h2 L
  exact ⟨fun M hM x hx => clause1 hH hN h2 L M hM x hx, fun x => clause2 hT hI hR h2 L x⟩

end PI.ProdFormulaE.Top

end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ProductFormulaHaar.ResChar
section
noncomputable section

open IsDedekindDomain NumberField

namespace PI.ProdFormulaE.ResCharP

theorem eq_iff_mem_asIdeal : St.ResCharIff := by
  intro F _ _ p ℓ hℓ
  show ringChar (𝓞 F ⧸ p.asIdeal) = ℓ ↔ _
  haveI : p.asIdeal.IsPrime := p.isPrime
  have hz : ((ℓ : 𝓞 F ⧸ p.asIdeal) = 0) ↔ (ℓ : 𝓞 F) ∈ p.asIdeal := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
  rw [← hz]
  constructor
  · intro h
    rw [← h]
    exact ringChar.Nat.cast_ringChar
  · intro h
    rcases hℓ.eq_one_or_self_of_dvd _ (ringChar.dvd h) with h1 | h1
    · exfalso
      have hc := ringChar.Nat.cast_ringChar (R := 𝓞 F ⧸ p.asIdeal)
      rw [h1, Nat.cast_one] at hc
      exact one_ne_zero hc
    · exact h1

end PI.ProdFormulaE.ResCharP
end
end

