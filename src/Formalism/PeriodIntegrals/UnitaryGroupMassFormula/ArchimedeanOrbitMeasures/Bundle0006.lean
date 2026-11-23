module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.ExpCut

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PsiSmoothHolds
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge

attribute [local instance] Matrix.linftyOpNormedAddCommGroup Matrix.linftyOpNormedSpace Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

def unrLin (n : ℕ) : EuclideanSpace ℝ (Fin n × Fin n × Bool) →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ where
  toFun := unrealify
  map_add' x y := by funext i j; apply Complex.ext <;> simp [unrealify]
  map_smul' c x := by funext i j; apply Complex.ext <;> simp [unrealify]

def reLin (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] EuclideanSpace ℝ (Fin n × Fin n × Bool) where
  toFun X := (WithLp.equiv 2 _).symm (realifyFun X)
  map_add' X Y := by
    ext q; rcases q with ⟨i, j, b⟩; cases b <;> simp [realifyFun]
  map_smul' c X := by
    ext q; rcases q with ⟨i, j, b⟩; cases b <;> simp [realifyFun]

theorem re_unr (n : ℕ) (v : EuclideanSpace ℝ (Fin n × Fin n × Bool)) : reLin n (unrLin n v) = v := by
  ext q
  rcases q with ⟨i, j, b⟩
  cases b <;> simp [reLin, unrLin, realifyFun, unrealify, LinearMap.coe_mk, AddHom.coe_mk] <;> rfl

def unit2 (n : ℕ) : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := 1 + 1
  inv := (1 / 2 : ℂ) • 1
  val_inv := by rw [Matrix.mul_smul, mul_one, smul_add, ← add_smul]; norm_num
  inv_val := by rw [Matrix.smul_mul, one_mul, smul_add, ← add_smul]; norm_num

theorem psiSmooth_holds : PsiSmoothU := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁
  set P := EuclideanSpace ℝ ι
  set Q := EuclideanSpace ℝ η
  set_option synthInstance.maxHeartbeats 200000 in
    letI : ContinuousSMul ℝ (P × Q) := inferInstance
  set A : P × Q →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (unrLin n).toContinuousLinearMap ∘L m.subtypeL ∘L (L₀.toContinuousLinearEquiv : P →L[ℝ] m) ∘L
      ContinuousLinearMap.fst ℝ P Q with hA
  set Bm : P × Q →L[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    (unrLin n).toContinuousLinearMap ∘L h.subtypeL ∘L (L₁.toContinuousLinearEquiv : Q →L[ℝ] h) ∘L
      ContinuousLinearMap.snd ℝ P Q with hBm
  set Gm : Matrix (Fin n) (Fin n) ℂ →L[ℝ] P × Q :=
    ((L₀.symm.toContinuousLinearEquiv : m →L[ℝ] P) ∘L m.orthogonalProjectionOnto ∘L (reLin n).toContinuousLinearMap).prod
      ((L₁.symm.toContinuousLinearEquiv : h →L[ℝ] Q) ∘L h.orthogonalProjectionOnto ∘L (reLin n).toContinuousLinearMap)
    with hGm
  set Mf : P × Q → Matrix (Fin n) (Fin n) ℂ := fun p => NormedSpace.exp (A p) * NormedSpace.exp (Bm p) with hMf
  set Ff : Matrix (Fin n) (Fin n) ℂ → Matrix (Fin n) (Fin n) ℂ :=
    fun M => (2 : ℂ) • ((M - 1) * Ring.inverse (M + 1)) with hFf
  have hpsi : psiE ε m h L₀ L₁ = fun p => Gm (Ff (Mf p)) := by
    funext p
    simp only [psiE, hGm, hFf, hMf, hA, hBm, Matrix.nonsing_inv_eq_ringInverse]
    rfl
  have hM0 : Mf 0 = 1 := by simp [hMf]

  have hexpA : HasFDerivAt (fun p => NormedSpace.exp (A p)) A 0 := by
    have h0 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _)
        (A 0) := by rw [map_zero]; exact hasFDerivAt_exp_zero
    have h1 := h0.comp (0 : P × Q) A.hasFDerivAt
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  have hexpB : HasFDerivAt (fun p => NormedSpace.exp (Bm p)) Bm 0 := by
    have h0 : HasFDerivAt (NormedSpace.exp : Matrix (Fin n) (Fin n) ℂ → _) (1 : Matrix (Fin n) (Fin n) ℂ →L[ℝ] _)
        (Bm 0) := by rw [map_zero]; exact hasFDerivAt_exp_zero
    have h1 := h0.comp (0 : P × Q) Bm.hasFDerivAt
    exact h1.congr_fderiv (ContinuousLinearMap.ext fun v => rfl)
  have hMd : HasFDerivAt Mf (A + Bm) 0 := by
    have h1 := hexpA.mul' hexpB
    have e1 : NormedSpace.exp (A 0) = 1 := by rw [map_zero, NormedSpace.exp_zero]
    have e2 : NormedSpace.exp (Bm 0) = 1 := by rw [map_zero, NormedSpace.exp_zero]
    refine h1.congr_fderiv (ContinuousLinearMap.ext fun v => ?_)
    change NormedSpace.exp (A 0) * Bm v + A v * NormedSpace.exp (Bm 0) = A v + Bm v
    rw [e1, e2, one_mul, mul_one, add_comm]
  have hFd : HasFDerivAt Ff (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) 1 := by
    have hs : HasFDerivAt (fun M : Matrix (Fin n) (Fin n) ℂ => M - 1) (ContinuousLinearMap.id ℝ _) 1 :=
      (hasFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).sub_const 1
    have hi :=
      (hasFDerivAt_ringInverse (𝕜 := ℝ) (unit2 n)).comp (1 : Matrix (Fin n) (Fin n) ℂ)
        ((hasFDerivAt_id (1 : Matrix (Fin n) (Fin n) ℂ)).add_const 1)
    have hp := (hs.mul' hi).const_smul (2 : ℂ)
    refine hp.congr_fderiv ?_
    have hinv : Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℂ) + 1) = (1 / 2 : ℂ) • 1 := by
      rw [show (1 : Matrix (Fin n) (Fin n) ℂ) + 1 = ((unit2 n : (Matrix (Fin n) (Fin n) ℂ)ˣ) : Matrix _ _ ℂ) from rfl,
        Ring.inverse_unit]
      rfl
    refine ContinuousLinearMap.ext fun X => ?_
    change (2 : ℂ) • (((1 : Matrix (Fin n) (Fin n) ℂ) - 1) * _ + X * Ring.inverse ((1 : Matrix (Fin n) (Fin n) ℂ) + 1)) = X
    rw [sub_self, zero_mul, zero_add, hinv, Matrix.mul_smul, mul_one, smul_smul]
    norm_num
  have hall : HasFDerivAt (psiE ε m h L₀ L₁) (Gm ∘L (ContinuousLinearMap.id ℝ _) ∘L (A + Bm)) 0 := by
    rw [hpsi]
    have hF' : HasFDerivAt Ff (ContinuousLinearMap.id ℝ (Matrix (Fin n) (Fin n) ℂ)) (Mf 0) := by rw [hM0]; exact hFd
    exact Gm.hasFDerivAt.comp (0 : P × Q) (hF'.comp (0 : P × Q) hMd)
  have hid : Gm ∘L (ContinuousLinearMap.id ℝ _) ∘L (A + Bm) = ContinuousLinearMap.id ℝ (P × Q) := by
    refine ContinuousLinearMap.ext fun q => ?_
    obtain ⟨x, y⟩ := q
    have hre : reLin n (A (x, y) + Bm (x, y)) = (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _) := by
      show reLin n (unrLin n (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
        unrLin n (L₁ y : EuclideanSpace ℝ (Fin n × Fin n × Bool))) = _
      rw [map_add (f := _), re_unr, re_unr]
    have h1 : (L₁ y : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ mᗮ := by
      rw [Submodule.mem_orthogonal]; intro u hu; exact horth u hu _ (L₁ y).2
    have h2 : (L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ hᗮ := by
      rw [Submodule.mem_orthogonal]; intro u hu; rw [real_inner_comm]; exact horth _ (L₀ x).2 u hu
    simp only [hGm, ContinuousLinearMap.comp_apply, ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.add_apply, LinearMap.coe_toContinuousLinearMap']
    rw [hre]
    refine Prod.ext ?_ ?_
    · show L₀.symm (m.orthogonalProjectionOnto ((L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _))) = x
      rw [map_add (f := _), Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h1, add_zero, LinearIsometryEquiv.symm_apply_apply]
    · show L₁.symm (h.orthogonalProjectionOnto ((L₀ x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) + (L₁ y : _))) = y
      rw [map_add (f := _), Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
        Submodule.orthogonalProjectionOnto_apply_of_mem_orthogonal h2, zero_add, LinearIsometryEquiv.symm_apply_apply]
  refine ⟨?_, by rw [hall.fderiv, hid]⟩

  rw [hpsi]
  have hMc : ContDiffAt ℝ 1 Mf 0 := by
    have ha : ContDiffAt ℝ 1 (fun p => NormedSpace.exp (A p)) 0 :=
      ((NormedSpace.exp_analytic (𝕂 := ℝ) (A 0)).contDiffAt).comp (0 : P × Q) A.contDiff.contDiffAt
    have hb : ContDiffAt ℝ 1 (fun p => NormedSpace.exp (Bm p)) 0 :=
      ((NormedSpace.exp_analytic (𝕂 := ℝ) (Bm 0)).contDiffAt).comp (0 : P × Q) Bm.contDiff.contDiffAt
    exact ha.mul hb
  have hFc : ContDiffAt ℝ 1 Ff (Mf 0) := by
    rw [hM0]
    have hi : ContDiffAt ℝ 1 (fun M : Matrix (Fin n) (Fin n) ℂ => Ring.inverse (M + 1)) 1 :=
      (contDiffAt_ringInverse ℝ (unit2 n)).comp (1 : Matrix (Fin n) (Fin n) ℂ)
        (contDiffAt_id.add contDiffAt_const)
    exact ((contDiffAt_id.sub contDiffAt_const).mul hi).const_smul (2 : ℂ)
  exact Gm.contDiff.contDiffAt.comp (0 : P × Q) (hFc.comp (0 : P × Q) hMc)

theorem expProdU_of_two (hC : CayProdU) (hM : PsiMeasU) (hI : PsiInvU) : ExpProdU :=
  expProdU_of_parts hC psiSmooth_holds hM hI

end PI.AprimeInfW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.SumLPresHolds
section
noncomputable section

namespace PI.AprimeInfW

open MeasureTheory Topology Metric Formalism.MainNotions.S Formalism.MainNotions.S.Gauge

def CayDensG : Prop := ∀ (n : ℕ) (ε : Fin n → Bool), GaugeDens ε →
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ f₀ : gLie ε → ℝ, Measurable f₀ ∧ ContinuousAt f₀ 0 ∧ f₀ 0 = gaugeU ε ∧
      ∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x)

def sumL {n : ℕ} (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool))) (hmh : m ⊔ h = gLie ε)
    {ι η : Type} [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h) :
    EuclideanSpace ℝ ι × EuclideanSpace ℝ η →ₗ[ℝ] gLie ε where
  toFun p := ⟨(L₀ p.1 : EuclideanSpace ℝ _) + (L₁ p.2 : EuclideanSpace ℝ _), by
    rw [← hmh]; exact Submodule.add_mem_sup (L₀ p.1).2 (L₁ p.2).2⟩
  map_add' p q := by ext1; simp only [Prod.fst_add, Prod.snd_add, map_add (f := _), Submodule.coe_add]; abel
  map_smul' c p := by ext1; simp [smul_add]

def SumLPres : Prop := ∀ (n : ℕ) (ε : Fin n → Bool) (m h : Submodule ℝ (EuclideanSpace ℝ (Fin n × Fin n × Bool)))
    (hmh : m ⊔ h = gLie ε), (∀ x ∈ m, ∀ y ∈ h, inner ℝ x y = 0) →
    ∀ (ι η : Type) [Fintype ι] [Fintype η] (L₀ : EuclideanSpace ℝ ι ≃ₗᵢ[ℝ] m) (L₁ : EuclideanSpace ℝ η ≃ₗᵢ[ℝ] h),
    Function.Injective (sumL ε m h hmh L₀ L₁) ∧
    ∀ S : Set (EuclideanSpace ℝ ι × EuclideanSpace ℝ η), MeasurableSet S →
      MeasurableSet (sumL ε m h hmh L₀ L₁ '' S) ∧ ∀ g : gLie ε → ENNReal, Measurable g →
        ∫⁻ x in sumL ε m h hmh L₀ L₁ '' S, g x = ∫⁻ p in S, g (sumL ε m h hmh L₀ L₁ p)

theorem cayProdU_of (hC : CayDensG) (hP : SumLPres) : CayProdU := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁ hG
  obtain ⟨r₀, hr₀, f₀, hm, hc, h0, hS⟩ := hC n ε hG
  obtain ⟨_, hPS⟩ := hP n ε m h hmh horth ι η L₀ L₁
  set F := sumL ε m h hmh L₀ L₁ with hF
  set_option synthInstance.maxHeartbeats 200000 in
    have hFc : Continuous F := LinearMap.continuous_of_finiteDimensional F
  refine ⟨r₀ / 2, by positivity, fun p => f₀ (F p), hc.comp_of_eq hFc.continuousAt (map_zero F), ?_,
    hm.comp hFc.measurable, ?_⟩
  · show f₀ (F 0) = gaugeU ε
    rw [map_zero]
    exact h0
  · intro S hSb hSm
    obtain ⟨hFSm, hint⟩ := hPS S hSm
    have hsub : F '' S ⊆ ball (0 : gLie ε) r₀ := by
      rintro _ ⟨p, hp, rfl⟩
      have hp' := hSb hp
      rw [mem_ball_zero_iff] at hp' ⊢
      have h1 : ‖p.1‖ < r₀ / 2 := lt_of_le_of_lt (norm_fst_le p) hp'
      have h2 : ‖p.2‖ < r₀ / 2 := lt_of_le_of_lt (norm_snd_le p) hp'
      have e : ‖F p‖ = ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ := rfl
      rw [e]
      calc _ ≤ ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ +
            ‖(L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ := norm_add_le _ _
        _ = ‖p.1‖ + ‖p.2‖ := by
          rw [show ‖(L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.1‖ from L₀.norm_map p.1,
            show ‖(L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖p.2‖ from L₁.norm_map p.2]
        _ < r₀ := by linarith
    have himg : (fun p : EuclideanSpace ℝ ι × EuclideanSpace ℝ η =>
        cayR ε ((L₀ p.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ p.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)))) '' S =
        (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' (F '' S) :=
      (Set.image_image (fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) F S).symm
    rw [himg, hS _ hsub hFSm,
      hint (fun x => ENNReal.ofReal (f₀ x)) (ENNReal.measurable_ofReal.comp hm)]

theorem sumLPres_holds : SumLPres := by
  intro n ε m h hmh horth ι η _ _ L₀ L₁

  have mkE : ∀ (κ : Type) [Fintype κ], ∃ e : EuclideanSpace ℝ κ ≃ᵐ (κ → ℝ),
      MeasurePreserving e ∧ ∀ x, e x = WithLp.ofLp x := by
    intro κ _
    refine ⟨{ toEquiv := WithLp.equiv 2 (κ → ℝ)
              measurable_toFun := (PiLp.volume_preserving_ofLp κ).measurable
              measurable_invFun := ?_ }, ?_, fun x => rfl⟩
    · first
      | exact (PiLp.volume_preserving_toLp κ).measurable
      | exact WithLp.measurable_toLp 2 _
      | fun_prop
      | measurability
    · exact PiLp.volume_preserving_ofLp κ
  obtain ⟨eι, heι, heιa⟩ := mkE ι
  obtain ⟨eη, heη, heηa⟩ := mkE η
  obtain ⟨eS, heS, heSa⟩ := mkE (ι ⊕ η)
  have heSs : ∀ f, (eS.symm f).ofLp = f := fun f => by rw [← heSa, eS.apply_symm_apply]
  let φ : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ EuclideanSpace ℝ (ι ⊕ η) :=
    (eι.prodCongr eη).trans ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm.trans eS.symm)
  have hsum : MeasurePreserving (MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)) := by
    first
    | exact MeasureTheory.measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ η => (volume : Measure ℝ))
    | exact MeasureTheory.volume_measurePreserving_sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)
    | exact MeasureTheory.Measure.volume_preserving_sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)
    | exact MeasureTheory.measurePreserving_sumPiEquivProdPi_of_measurePreserving
  have hφ : MeasurePreserving φ :=
    ((MeasurePreserving.symm _ heS).comp (MeasurePreserving.symm _ hsum)).comp (heι.prod heη)
  have hφl : ∀ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ∀ i, (φ q).ofLp (Sum.inl i) = q.1.ofLp i := by
    intro q i
    show (eS.symm ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm (eι q.1, eη q.2))).ofLp
      (Sum.inl i) = _
    rw [heSs, heιa]
    first
    | rfl
    | simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have hφr : ∀ q : EuclideanSpace ℝ ι × EuclideanSpace ℝ η, ∀ j, (φ q).ofLp (Sum.inr j) = q.2.ofLp j := by
    intro q j
    show (eS.symm ((MeasurableEquiv.sumPiEquivProdPi (fun _ : ι ⊕ η => ℝ)).symm (eι q.1, eη q.2))).ofLp
      (Sum.inr j) = _
    rw [heSs, heηa]
    first
    | rfl
    | simp [MeasurableEquiv.sumPiEquivProdPi, Equiv.sumPiEquivProdPi]
  have hφl' : ∀ u : EuclideanSpace ℝ (ι ⊕ η), ∀ i, (φ.symm u).1.ofLp i = u.ofLp (Sum.inl i) := by
    intro u i
    rw [← hφl, φ.apply_symm_apply]
  have hφr' : ∀ u : EuclideanSpace ℝ (ι ⊕ η), ∀ j, (φ.symm u).2.ofLp j = u.ofLp (Sum.inr j) := by
    intro u j
    rw [← hφr, φ.apply_symm_apply]

  have key : ∀ q, ‖(sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖φ q‖ := by
    intro q
    have e0 : (sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool)) =
        (L₀ q.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
          (L₁ q.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool)) := rfl
    have horth' := horth _ (L₀ q.1).2 _ (L₁ q.2).2
    have e1 := norm_add_sq_eq_norm_sq_add_norm_sq_real horth'
    have n0 : ‖(L₀ q.1 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖q.1‖ := L₀.norm_map q.1
    have n1 : ‖(L₁ q.2 : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖q.2‖ := L₁.norm_map q.2
    have e2 : ‖φ q‖ ^ 2 = ‖q.1‖ ^ 2 + ‖q.2‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
        Fintype.sum_sum_type]
      simp only [hφl, hφr]
    have e3 : ‖(sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ ^ 2 =
        ‖φ q‖ ^ 2 := by
      rw [e2, e0, sq, e1, n0, n1]
      ring
    rw [← Real.sqrt_sq (norm_nonneg (sumL ε m h hmh L₀ L₁ q : EuclideanSpace ℝ (Fin n × Fin n × Bool))),
      ← Real.sqrt_sq (norm_nonneg (φ q)), e3]

  let sp : EuclideanSpace ℝ (ι ⊕ η) →ₗ[ℝ] EuclideanSpace ℝ ι × EuclideanSpace ℝ η :=
    { toFun := φ.symm
      map_add' := fun u w => by
        ext k
        · simp [hφl']
        · simp [hφr']
      map_smul' := fun c u => by
        ext k
        · simp [hφl']
        · simp [hφr'] }
  let ψi : EuclideanSpace ℝ (ι ⊕ η) →ₗᵢ[ℝ] gLie ε :=
    { (sumL ε m h hmh L₀ L₁).comp sp with
      norm_map' := fun v => by
        show ‖(sumL ε m h hmh L₀ L₁ (φ.symm v) : EuclideanSpace ℝ (Fin n × Fin n × Bool))‖ = ‖v‖
        rw [key, φ.apply_symm_apply] }
  have hsurj : Function.Surjective ψi := by
    intro x
    have hx : (x : EuclideanSpace ℝ (Fin n × Fin n × Bool)) ∈ m ⊔ h := by
      rw [hmh]
      exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hx
    refine ⟨φ (L₀.symm ⟨a, ha⟩, L₁.symm ⟨b, hb⟩), ?_⟩
    show sumL ε m h hmh L₀ L₁ (φ.symm (φ (L₀.symm ⟨a, ha⟩, L₁.symm ⟨b, hb⟩))) = x
    rw [φ.symm_apply_apply]
    apply Subtype.ext
    show (L₀ (L₀.symm ⟨a, ha⟩) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) +
      (L₁ (L₁.symm ⟨b, hb⟩) : EuclideanSpace ℝ (Fin n × Fin n × Bool)) = x
    rw [L₀.apply_symm_apply, L₁.apply_symm_apply]
    exact hab
  let ψ : EuclideanSpace ℝ (ι ⊕ η) ≃ₗᵢ[ℝ] gLie ε := LinearIsometryEquiv.ofSurjective ψi hsurj
  have hψ : MeasurePreserving ψ := ψ.measurePreserving
  let T : (EuclideanSpace ℝ ι × EuclideanSpace ℝ η) ≃ᵐ gLie ε :=
    φ.trans ψ.toHomeomorph.toMeasurableEquiv
  have hT : MeasurePreserving T := hψ.comp hφ
  have hFT : ∀ q, sumL ε m h hmh L₀ L₁ q = T q := by
    intro q
    show sumL ε m h hmh L₀ L₁ q = sumL ε m h hmh L₀ L₁ (φ.symm (φ q))
    rw [φ.symm_apply_apply]
  have hFT' : ⇑(sumL ε m h hmh L₀ L₁) = ⇑T := funext hFT
  refine ⟨?_, fun S hS => ⟨?_, fun g _ => ?_⟩⟩
  · rw [hFT']
    exact T.injective
  · rw [hFT']
    exact T.measurableSet_image.mpr hS
  · rw [hFT']
    exact (hT.setLIntegral_comp_emb T.measurableEmbedding g S).symm

theorem cayProdU_of_G (hC : CayDensG) : CayProdU := cayProdU_of hC sumLPres_holds

def CayDensEx : Prop := ∀ (n : ℕ) (ε : Fin n → Bool),
    ∃ r₀ : ℝ, 0 < r₀ ∧ ∃ f₀ : gLie ε → ℝ, Measurable f₀ ∧ ContinuousAt f₀ 0 ∧
      ∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x)

def CayValId : Prop := ∀ (n : ℕ) (ε : Fin n → Bool), GaugeDens ε → ∀ r₀ : ℝ, 0 < r₀ → ∀ f₀ : gLie ε → ℝ,
    Measurable f₀ → ContinuousAt f₀ 0 →
    (∀ S ⊆ ball (0 : gLie ε) r₀, MeasurableSet S →
        Formalism.REAL.muG ε ((fun x : gLie ε => cayR ε (x : EuclideanSpace ℝ (Fin n × Fin n × Bool))) '' S) =
          ∫⁻ x in S, ENNReal.ofReal (f₀ x)) → f₀ 0 = gaugeU ε

theorem cayDensG_of (h1 : CayDensEx) (h2 : CayValId) : CayDensG := by
  intro n ε hG
  obtain ⟨r₀, hr₀, f₀, hm, hc, hS⟩ := h1 n ε
  exact ⟨r₀, hr₀, f₀, hm, hc, h2 n ε hG r₀ hr₀ f₀ hm hc hS, hS⟩

end PI.AprimeInfW
end
end

