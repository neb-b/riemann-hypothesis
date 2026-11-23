module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.ParabolicThetaScalar
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0046
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.IsParOfFrame
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0041
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockSpaces.ProdGenMem
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0042

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaB
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
theorem par_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ (n0 m0 : d.G) (A D : GL (Fin d.n) (AE F E)),
      inFrame d.b n0 = Matrix.fromBlocks 1 ((inFrame d.b p).toBlocks₁₂ * (inFrame d.b p).toBlocks₂₂⁻¹) 0 1 ∧
      inFrame d.b m0 = Matrix.fromBlocks A.1 0 0 D.1 ∧ A.1 = (inFrame d.b p).toBlocks₁₁ ∧
      D.1 = (inFrame d.b p).toBlocks₂₂ ∧ p = n0 * m0 := by
  set g := inFrame d.b p with hg
  set A := g.toBlocks₁₁
  set B := g.toBlocks₁₂
  set D := g.toBlocks₂₂
  have hgb : g = Matrix.fromBlocks A B 0 D := by rw [← h21, Matrix.fromBlocks_toBlocks]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit g := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hdet : IsUnit (A.det * D.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ A B D, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det g).1 hug
  have hA : IsUnit A.det := isUnit_of_mul_isUnit_left hdet
  have hD : IsUnit D.det := isUnit_of_mul_isUnit_right hdet
  set Md : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E) := Matrix.fromBlocks A 0 0 D with hMd_def
  have hMd : IsUnit Md := (Matrix.isUnit_iff_isUnit_det _).2 (by rw [hMd_def, Matrix.det_fromBlocks_zero₂₁]; exact hA.mul hD)
  obtain ⟨C', hC'⟩ := _root_.PositivityTheory.SiegelWeilFormula.KWhit.frame_form_k d
  have hP : (mat2 p)ᵀ * dbl (incM F d.Y.J) * (mat2 p).map (cA σ).toRingHom = dbl (incM F d.Y.J) := p.2
  have hgf := KWhit.form_conj_in (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hP
  have hC'' : (incM F d.b.1)ᵀ * dbl (incM F d.Y.J) * (incM F d.b.1).map (cA σ).toRingHom =
      Matrix.fromBlocks 0 1 C' 0 := hC'
  rw [hC''] at hgf
  have hgf' : gᵀ * Matrix.fromBlocks 0 1 C' 0 * g.map (cA σ).toRingHom = Matrix.fromBlocks 0 1 C' 0 := hgf
  rw [hgb] at hgf'
  have hMdf := KWhit.block_diag_form (cA σ).toRingHom A B D C' hgf'
  rw [← hC''] at hMdf
  have hM0mem := KWhit.form_conj_out (cA σ).toRingHom (_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d) hMdf
  have hM0u : IsUnit (incM F d.b.1 * Md * incM F (d.b⁻¹).1) := (hBm.mul hMd).mul hBi
  let u : GL (Fin d.n ⊕ Fin d.n) (AE F E) := hM0u.unit
  have hu : (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) =
      incM F d.b.1 * Md * incM F (d.b⁻¹).1 := IsUnit.unit_spec hM0u
  have hmem : u ∈ UG (cA σ) (dbl (incM F d.Y.J)) := by
    show (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))ᵀ * dbl (incM F d.Y.J) *
      (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)).map (cA σ) = dbl (incM F d.Y.J)
    rw [hu]
    exact hM0mem
  let m0 : d.G := ⟨u, hmem⟩
  have hm0 : inFrame d.b m0 = Md := by
    show incM F (d.b⁻¹).1 * (u : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E)) * incM F d.b.1 = Md
    rw [hu]
    simp only [← Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.one_mul]
    rw [Matrix.mul_assoc, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]
  have hAu := (Matrix.isUnit_iff_isUnit_det A).2 hA
  have hDu := (Matrix.isUnit_iff_isUnit_det D).2 hD
  refine ⟨p * m0⁻¹, m0, hAu.unit, hDu.unit, ?_, ?_, IsUnit.unit_spec hAu, IsUnit.unit_spec hDu,
    (inv_mul_cancel_right p m0).symm⟩
  · have e := _root_.PositivityTheory.SiegelWeilFormula.KWhit.inFrame_mul_k d (p * m0⁻¹) m0
    rw [inv_mul_cancel_right, hm0] at e
    apply (hMd.mul_left_inj).1
    rw [← e, ← hg, hgb, hMd_def, Matrix.fromBlocks_multiply]
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hD]
  · rw [hm0, IsUnit.unit_spec, IsUnit.unit_spec]
theorem q_T'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (i₀ : Fin d.n) {q : d.G} {lam : (AE F E)ˣ} (hq : IsQ F E i₀ (inFrame d.b q) lam) :
    ∃ c : ℂ, ∀ Φ ∈ d.sch, ∀ X : Mx F E d.m d.n, (∀ a, X a i₀ = 0) → d.T (d.om q Φ) X = c * d.T Φ X := by
  set M := inFrame d.b q with hM
  obtain ⟨n0, m0, A, D, hn, hm, hA, hD, hp⟩ := _root_.PositivityTheory.SiegelWeilFormula.Avac.par_frame_k d q (isQ_21 hq)
  refine ⟨(d.χ (Matrix.GeneralLinearGroup.det A) : ℂ) *
    (((absE F E (Matrix.GeneralLinearGroup.det A) : ℝ) ^ ((d.m : ℝ) / 2) : ℝ) : ℂ), fun Φ hΦ X hX => ?_⟩
  have hD1 : ∀ j k, k ≠ i₀ → D.1 j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k := by
    rw [hD]; exact isQ_22 hq
  have hDu : IsUnit M.toBlocks₂₂.det := by
    rw [← hD]; exact (Matrix.isUnit_iff_isUnit_det _).1 D.isUnit
  have hDi : ∀ j k, k ≠ i₀ → M.toBlocks₂₂⁻¹ j k = (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) j k :=
    inv_col (isQ_22 hq) (Matrix.nonsing_inv_mul _ hDu)
  have hβ : ∀ i j, i ≠ i₀ → j ≠ i₀ → (M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) i j = 0 := by
    intro i j hi hj
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : k = i₀
    · subst hk; rw [hDi _ _ hj, Matrix.one_apply_ne (Ne.symm hj), mul_zero]
    · rw [isQ_12 hq i k hi hk, zero_mul]
  have hG : ∀ i j, (i = i₀ ∨ j = i₀) → d.gram X X i j = 0 := by
    intro i j hij
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply]
    refine Finset.sum_eq_zero fun b _ => ?_
    rcases hij with rfl | rfl
    · rw [Finset.sum_mul]
      refine Finset.sum_eq_zero fun a _ => ?_
      rw [hX a, zero_mul, zero_mul]
    · rw [hX b, map_zero, mul_zero]
  have htt : d.tt ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
    have : Matrix.trace ((M.toBlocks₁₂ * M.toBlocks₂₂⁻¹) * d.gram X X) = 0 := by
      simp only [Matrix.trace, Matrix.diag]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [Matrix.mul_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases h : i = i₀ ∨ j = i₀
      · rw [hG j i (h.symm), mul_zero]
      · push_neg at h
        rw [hβ i j h.1 h.2, zero_mul]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.tt, this, map_zero]
  have hXD : X * (D⁻¹).1ᵀ = X := by
    have h1 : X * D.1ᵀ = X := by
      ext a j
      rw [Matrix.mul_apply]
      rw [Finset.sum_eq_single j]
      · rw [Matrix.transpose_apply]
        by_cases hj : j = i₀
        · subst hj; rw [hX a, zero_mul]
        · rw [hD1 j j hj, Matrix.one_apply_eq, mul_one]
      · intro k _ hk
        rw [Matrix.transpose_apply]
        by_cases hk0 : k = i₀
        · subst hk0; rw [hX a, zero_mul]
        · rw [hD1 j k hk0, Matrix.one_apply_ne (Ne.symm hk), mul_zero]
      · simp
    calc X * (D⁻¹).1ᵀ = X * D.1ᵀ * (D⁻¹).1ᵀ := by rw [h1]
      _ = X * ((D⁻¹).1 * D.1)ᵀ := by rw [Matrix.transpose_mul, Matrix.mul_assoc]
      _ = X := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.transpose_one, Matrix.mul_one]
  have hm0s : d.om m0 Φ ∈ d.sch := _root_.PositivityTheory.SiegelWeilFormula.KWhit.om_mem_sch_k d m0 hΦ
  rw [hp, map_mul, Module.End.mul_apply, (hT.2.1 F E σ d _ hm0s).1 n0 _ hn X, htt, mul_zero, neg_zero,
    AddChar.map_zero_eq_one, one_mul, (hT.2.1 F E σ d Φ hΦ).2.1 m0 A D hm X, hXD]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacIwaC
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open GlobalTheory.Doubling (absE)
theorem isPar_of_frame_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (p : d.G) (h21 : (inFrame d.b p).toBlocks₂₁ = 0) :
    ∃ t : GL (Fin d.n) (AE F E), IsPar p t ∧ (Matrix.GeneralLinearGroup.det t : AE F E) = (inFrame d.b p).toBlocks₁₁.det := by
  obtain ⟨-, tb, htb⟩ := d.ok.frame
  set M := inFrame d.b p with hM
  let E1 : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := Matrix.fromRows 1 0
  let DC : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) (AE F E) := diagCols (Fin d.n)
  have htb' : d.b.1.toCols₁ = (diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1 := htb
  have hcol : ∀ N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E), N * E1 = N.toCols₁ := by
    intro N
    ext i j
    simp [E1, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, Matrix.toCols₁]
  have h1 : incM F d.b.1 * E1 = incM F (d.b.1.toCols₁) := by
    rw [hcol]
    ext i j
    rfl
  have h2 : incM F ((diagCols (Fin d.n) : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n) E) * tb.1) = DC * incM F tb.1 := by
    rw [incM_mul'']
    congr 1
    ext i j
    cases i <;> simp [DC, diagCols, incM, Matrix.one_apply, apply_ite] <;> split_ifs <;> simp_all
  have hb : incM F d.b.1 * E1 = DC * incM F tb.1 := h1.trans ((congrArg (incM F) htb').trans h2)
  have hTb : incM F tb.1 * incM F (tb⁻¹).1 = 1 := by
    rw [← incM_mul'', Units.mul_inv]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hTb' : incM F (tb⁻¹).1 * incM F tb.1 = 1 := by
    rw [← incM_mul'', Units.inv_mul]
    exact Matrix.map_one _ (map_zero _) (map_one _)
  have hdc : DC = incM F d.b.1 * E1 * incM F (tb⁻¹).1 := by
    rw [hb, Matrix.mul_assoc, hTb, Matrix.mul_one]
  have hME : M * E1 = E1 * M.toBlocks₁₁ := by
    rw [hcol]
    ext i j
    cases i with
    | inl i => simp [E1, Matrix.toCols₁, Matrix.toBlocks₁₁, Matrix.mul_apply, Matrix.one_apply]
    | inr i =>
      have := congrFun (congrFun h21 i) j
      simp only [Matrix.toBlocks₂₁, Matrix.of_apply, Matrix.zero_apply] at this
      simp [E1, Matrix.toCols₁, this, Matrix.mul_apply]
  have hBm : IsUnit (incM F d.b.1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_mul_inv_k d, Matrix.det_one]⟩)
  have hBi : IsUnit (incM F (d.b⁻¹).1) := (Matrix.isUnit_iff_isUnit_det _).2
    (isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, _root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.det_one]⟩)
  have hug : IsUnit M := (hBi.mul (Units.isUnit p.1)).mul hBm
  have hgb : M = Matrix.fromBlocks M.toBlocks₁₁ M.toBlocks₁₂ 0 M.toBlocks₂₂ := by
    rw [← h21, Matrix.fromBlocks_toBlocks]
  have hdet : IsUnit (M.toBlocks₁₁.det * M.toBlocks₂₂.det) := by
    rw [← Matrix.det_fromBlocks_zero₂₁ M.toBlocks₁₁ M.toBlocks₁₂ M.toBlocks₂₂, ← hgb]
    exact (Matrix.isUnit_iff_isUnit_det M).1 hug
  have hA : IsUnit M.toBlocks₁₁.det := isUnit_of_mul_isUnit_left hdet
  have hTbu : IsUnit (incM F tb.1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb, Matrix.det_one]⟩
  have hTbiu : IsUnit (incM F (tb⁻¹).1).det :=
    isUnit_iff_exists_inv.2 ⟨_, by rw [← Matrix.det_mul, hTb', Matrix.det_one]⟩
  have hu : IsUnit (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_mul, Matrix.det_mul]
    exact (hTbu.mul hA).mul hTbiu
  refine ⟨hu.unit, ?_, ?_⟩
  · show mat2 p * DC = DC * (hu.unit : Matrix (Fin d.n) (Fin d.n) (AE F E))
    rw [IsUnit.unit_spec, _root_.PositivityTheory.SiegelWeilFormula.KWhit.matrixRep_eq_frameConj_inFrame d p]
    change incM F d.b.1 * M * incM F (d.b⁻¹).1 * DC = DC * (incM F tb.1 * M.toBlocks₁₁ * incM F (tb⁻¹).1)
    rw [hdc]
    calc incM F d.b.1 * M * incM F (d.b⁻¹).1 * (incM F d.b.1 * E1 * incM F (tb⁻¹).1)
        = incM F d.b.1 * M * (incM F (d.b⁻¹).1 * incM F d.b.1) * E1 * incM F (tb⁻¹).1 := by
          simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * (M * E1) * incM F (tb⁻¹).1 := by
          rw [_root_.PositivityTheory.SiegelWeilFormula.KWhit.incM_inv_mul_k d, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = incM F d.b.1 * E1 * (incM F (tb⁻¹).1 * incM F tb.1) * M.toBlocks₁₁ * incM F (tb⁻¹).1 := by
          rw [hME, hTb', Matrix.mul_one]; simp only [Matrix.mul_assoc]
      _ = _ := by simp only [Matrix.mul_assoc]
  · rw [Matrix.GeneralLinearGroup.val_det_apply, IsUnit.unit_spec, Matrix.det_mul, Matrix.det_mul, mul_comm _ M.toBlocks₁₁.det,
      mul_assoc, ← Matrix.det_mul, hTb, Matrix.det_one, mul_one]
theorem a_mul_par_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {q : d.G} {t : GL (Fin d.n) (AE F E)} (hq : IsPar q t) (y : d.G) :
    d.a (q * y) = (absE F E (Matrix.GeneralLinearGroup.det t) : ℝ) * d.a y := by
  obtain ⟨p, t', hp, k, hk, rfl⟩ := d.ok.hgt.iwa y
  rw [← mul_assoc, d.ok.hgt.val _ _ (KSplitP.isPar_mul hq hp) k hk, d.ok.hgt.val p t' hp k hk, map_mul, map_mul,
    NNReal.coe_mul]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacKA
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
open PositivityTheory.SiegelWeilFormula.KSing.UnitaryGroupBasics (mkGR inFrame_mul inFrame_one cw_mul cw_one form_w)
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ}
theorem crd_add_k (X Z : Mx F E d.m d.n) (k : Fin d.m × Fin d.n × Fin 2) : d.crd (X + Z) k = d.crd X k + d.crd Z k := by
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.add_apply, map_add (f := _), Finsupp.coe_add, Pi.add_apply]
theorem crd_fin_k {Z : Mx F E d.m d.n} (hZ : finOne F • Z = 0) (k : Fin d.m × Fin d.n × Fin 2) : (d.crd Z k).2 = 0 := by
  have h := congrArg (fun M => d.crd M k) hZ
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, Matrix.smul_apply, map_smul, Finsupp.smul_apply, Matrix.zero_apply, map_zero, Finsupp.coe_zero,
    Pi.zero_apply, smul_eq_mul] at h
  have h2 := congrArg Prod.snd h
  have e : ∀ c : AF F, (finOne F * c).2 = c.2 := fun c => by
    show (1 : Af F) * c.2 = c.2
    exact one_mul _
  simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd]
  rw [← e]
  exact h2
theorem loc_add_of_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) {Z : Mx F E d.m d.n} (hZ : d.cw w Z = 0) (X : Mx F E d.m d.n) :
    R.loc w (X + Z) = R.loc w X := by
  have : d.cw w (X + Z) = d.cw w X := by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw] at hZ ⊢
    rw [Matrix.map_add _ (map_add _), hZ, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.RD_k.loc
  rw [this]
def psiW_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X)) * g fun k => (d.crd X k).2
theorem vg_tens_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g = R.tens w (fP 1) (_root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w) := by
  funext X
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k]
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ w)]
  ring
theorem psiW_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (w : InfinitePlace F) :
    ∀ X Z, (∀ w', w' ≠ w → d.cw w' Z = 0) → finOne F • Z = 0 → _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w (X + Z) = _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k R g w X := by
  intro X Z h1 h2
  have e1 : (∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' (X + Z))) = ∏ w' ∈ Finset.univ.erase w, fP 1 (R.loc w' X) :=
    Finset.prod_congr rfl fun w' hw' => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w' (h1 w' (Finset.ne_of_mem_erase hw'))]
  have e2 : (fun k => (d.crd (X + Z) k).2) = fun k => (d.crd X k).2 := by
    funext k
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_add_k]
    show (d.crd X k).2 + (d.crd Z k).2 = (d.crd X k).2
    rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.crd_fin_k h2, add_zero]
  unfold _root_.PositivityTheory.SiegelWeilFormula.Avac.psiW_k
  rw [e1, e2]
theorem gauss_indep_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) :
    ∀ X Z, (∀ w, d.cw w Z = 0) → (∏ w, fP 1 (R.loc w (X + Z))) = ∏ w, fP 1 (R.loc w X) := by
  intro X Z h
  exact Finset.prod_congr rfl fun w _ => by rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.loc_add_of_k R w (h w)]
theorem fP_smul_one_k (c : ℂ) (u : Fin d.m → Fin d.n → ℂ) : fP (c • (1 : PX d.m d.n)) u = c * fP 1 u := by
  simp only [fP, evX, MvPolynomial.smul_eq_C_mul, mul_one, MvPolynomial.eval_C, map_one, one_mul]
theorem isSchwartz_fourierProjection_one : IsSw (fP (1 : PX d.m d.n)) := by
  obtain ⟨φ, hφ⟩ := KMain.schwartz_polyGauss (m := d.m) (n := d.n) (2 * Real.pi) (by positivity) 1
  exact ⟨φ, hφ⟩
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacRes
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d)
def ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : Fin d.m × Fin d.n × Fin 2 → Af F :=
  fun k => if h : ∃ j, L.em j = k.2.1 then z (k.1, h.choose, k.2.2) else 0
def ext_k (X' : Mx F E d.m L.n) : Mx F E d.m d.n := fun a i => if h : ∃ j, L.em j = i then X' a h.choose else 0
theorem choose_em_k (j : Fin L.n) (h : ∃ j', L.em j' = L.em j) : h.choose = j := L.inj h.choose_spec
theorem ext_sub_k (X : Mx F E d.m d.n) (hX : ∀ a, X a L.i₀ = 0) : _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em) = X := by
  funext a i
  by_cases h : ∃ j, L.em j = i
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_pos h, Matrix.submatrix_apply, id, h.choose_spec]
  · have : i = L.i₀ := by
      by_contra hi
      exact h ((L.rng i).1 hi)
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, dif_neg h]
    rw [this, hX]
theorem crd_ext_k (X' : Mx F E d.m L.n) (k : Fin d.m × Fin d.n × Fin 2) :
    (d.crd (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') k).2 = _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (fun k' => (L.sd.crd X' k').2) k := by
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.crd, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h, map_zero, Finsupp.coe_zero, Pi.zero_apply]
    rfl
theorem continuous_ins_k : Continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L (F := F)) := by
  refine continuous_pi fun k => ?_
  by_cases h : ∃ j, L.em j = k.2.1
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h]; exact continuous_apply _
  · simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_neg h]; exact continuous_const
def prj_k (z : Fin d.m × Fin d.n × Fin 2 → Af F) : Fin d.m × Fin L.n × Fin 2 → Af F := fun k => z (k.1, L.em k.2.1, k.2.2)
theorem prj_ins_k (z : Fin d.m × Fin L.n × Fin 2 → Af F) : _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z) = z := by
  funext k
  have h : ∃ j, L.em j = L.em k.2.1 := ⟨_, rfl⟩
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L k.2.1 h]
theorem SB_ins_k {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) ∈ SB (Fin d.m × Fin L.n × Fin 2 → Af F) := by
  refine ⟨hg.1.comp_continuous (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L), ?_⟩
  have hc : IsCompact (_root_.PositivityTheory.SiegelWeilFormula.Avac.prj_k L '' tsupport g) := hg.2.isCompact.image (continuous_pi fun k => continuous_apply _)
  refine hc.of_isClosed_subset (isClosed_tsupport _) ?_
  refine (tsupport_comp_subset_preimage g (_root_.PositivityTheory.SiegelWeilFormula.Avac.continuous_ins_k L)).trans fun z hz => ⟨_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z, hz, _root_.PositivityTheory.SiegelWeilFormula.Avac.prj_ins_k L z⟩
theorem sum_loc_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (X : Mx F E d.m d.n) :
    ∑ a, ∑ i, ‖R.loc w X a i‖ ^ 2 = ∑ i, ∑ a, ‖(((R.fr w)⁻¹).1 *ᵥ fun b => d.cw w X b i) a‖ ^ 2 := by
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  simp only [_root_.PositivityTheory.SiegelWeilFormula.RD_k.loc, Matrix.map_apply, norm_star]
  rfl
theorem hζ'_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.ζ = 1 ∨ R.ζ = Complex.I := by
  rcases R.hζ with h | h
  · exact Or.inl h.2
  · exact Or.inr h.2
theorem gauss_ext_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (w : InfinitePlace F) (X' : Mx F E d.m L.n) :
    fP 1 (R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = fP 1 (R'.loc w X') := by
  suffices key : ∑ a, ∑ i, ‖R'.loc w X' a i‖ ^ 2 = ∑ a, ∑ i, ‖R.loc w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') a i‖ ^ 2 by
    simp only [fP, gs, key, evX, map_one]
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k, _root_.PositivityTheory.SiegelWeilFormula.Avac.sum_loc_k]
  refine Fintype.sum_of_injective L.em L.inj _ _ (fun i hi => ?_) (fun j => ?_)
  · have h : ¬ ∃ j, L.em j = i := fun ⟨j, hj⟩ => hi ⟨j, hj⟩
    have : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b i) = 0 := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_neg h, map_zero, Pi.zero_apply]
    simp [this]
  · have h : ∃ j', L.em j' = L.em j := ⟨_, rfl⟩
    have e : (fun b => d.cw w (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X') b (L.em j)) = fun b => L.sd.cw w X' b j := by
      funext b
      simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.cw, _root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k, Matrix.map_apply, dif_pos h, _root_.PositivityTheory.SiegelWeilFormula.Avac.choose_em_k L j h]
    rw [e]
    exact norm_frame_eq d.ok.hm (d.A.J.map (d.B.emb w).1) (R'.fr w) (R.fr w) R'.ζ R.ζ (R'.sg w) (R.sg w) (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R')
      (_root_.PositivityTheory.SiegelWeilFormula.Avac.hζ'_k R) (R'.hfr w) (R.hfr w) _
theorem res_vg_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) :
    (fun X' => _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L X')) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := by
  funext X'
  simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k]
  congr 1
  · exact Finset.prod_congr rfl fun w _ => _root_.PositivityTheory.SiegelWeilFormula.Avac.gauss_ext_k L R R' w X'
  · congr 1
    funext k
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.crd_ext_k L X' k
def resL_k : (Mx F E d.m d.n → ℂ) →ₗ[ℂ] (Mx F E d.m L.n → ℂ) := LinearMap.funLeft ℂ ℂ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L)
theorem res_vac_k (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) {f : Mx F E d.m d.n → ℂ} (hf : f ∈ R.vac) : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L f ∈ R'.vac := by
  have : R.vac ≤ R'.vac.comap (_root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, hg, rfl⟩
    show _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) ∈ R'.vac
    have e : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (_root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g) = _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R' (fun z => g (_root_.PositivityTheory.SiegelWeilFormula.Avac.ins_k L z)) := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vg_k L R R' g
    rw [e]
    exact _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_mem_k R' (_root_.PositivityTheory.SiegelWeilFormula.Avac.SB_ins_k L hg)
  exact this hf
theorem vac_res'_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hF : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (R' : _root_.PositivityTheory.SiegelWeilFormula.RD_k L.sd) :
    ∀ Φ ∈ d.sch, d.T Φ ∈ R.vac → ∃ Φ', L.IsRes Φ Φ' ∧ L.sd.T Φ' ∈ R'.vac := by
  intro Φ hΦ hv
  have h1 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ R'.vac := _root_.PositivityTheory.SiegelWeilFormula.Avac.res_vac_k L R R' hv
  have h2 : _root_.PositivityTheory.SiegelWeilFormula.Avac.resL_k L (d.T Φ) ∈ L.sd.schM := (hF F E σ L.sd R').1 (_root_.PositivityTheory.SiegelWeilFormula.Avac.vac_le_fock_k R' h1)
  obtain ⟨Φ', hΦ', e⟩ := (hT.1 F E σ L.sd).2.1 _ h2
  refine ⟨Φ', ⟨hΦ', fun X hX => ?_⟩, e ▸ h1⟩
  rw [e]
  show d.T Φ (_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_k L (X.submatrix id L.em)) = d.T Φ X
  rw [_root_.PositivityTheory.SiegelWeilFormula.Avac.ext_sub_k L X hX]
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfockMem
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KFock
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem prodGen_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (S : InfinitePlace F → 𝓢(Fin d.m → Fin d.n → ℂ, ℂ))
    (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (hg : g ∈ SB (Fin d.m × Fin d.n × Fin 2 → Af F)) :
    (fun X => (∏ w, S w (R.loc w X)) * g fun k => (d.crd X k).2) ∈ d.schM := by
  obtain ⟨T, hT⟩ := piProdSch (InfinitePlace F) (Fin d.m → Fin d.n → ℂ) S
  obtain ⟨L, hL⟩ := _root_.PositivityTheory.SiegelWeilFormula.KFock.archEquiv_k d R
  rw [_root_.PositivityTheory.SiegelWeilFormula.SD_k.schM, Submodule.mem_comap]
  refine Submodule.subset_span ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L T, g, hg, ?_⟩
  funext c
  simp only [LinearMap.funLeft_apply, pureA, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp, hT, hL,
    _root_.PositivityTheory.SiegelWeilFormula.KFock.crd_cmb_k]
theorem fock_le_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.fock ≤ d.schM := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨P, g, hg, rfl⟩
  have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (fun w => (isSw_fP (P w)).choose) g hg
  have e : (fun X => (∏ w, fP (P w) (R.loc w X)) * g fun k => (d.crd X k).2) =
      fun X => (∏ w, (isSw_fP (P w)).choose (R.loc w X)) * g fun k => (d.crd X k).2 := by
    funext X
    congr 1
    exact Finset.prod_congr rfl fun w _ => by rw [(isSw_fP (P w)).choose_spec]
  change _ ∈ d.schM
  rw [e]
  exact h
theorem tens_mem_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (w : InfinitePlace F) (f : (Fin d.m → Fin d.n → ℂ) → ℂ) (hf : IsSw f)
    (Ψ : Mx F E d.m d.n → ℂ) (hΨ : Ψ ∈ R.away w) : R.tens w f Ψ ∈ d.schM := by
  obtain ⟨φ, hφ⟩ := hf
  have h : R.away w ≤ d.schM.comap (_root_.PositivityTheory.SiegelWeilFormula.KFock.tensL_k R w f) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨P, g, hg, rfl⟩
    have h := _root_.PositivityTheory.SiegelWeilFormula.KFock.prodGen_mem_k d R (Function.update (fun w' => (isSw_fP (P w')).choose) w φ) g hg
    show R.tens w f _ ∈ d.schM
    convert h using 1
    funext X
    show f (R.loc w X) * ((∏ w' ∈ Finset.univ.erase w, fP (P w') (R.loc w' X)) * g fun k => (d.crd X k).2) =
      (∏ w', (Function.update (fun w' => (isSw_fP (P w')).choose) w φ w') (R.loc w' X)) * g fun k => (d.crd X k).2
    rw [← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ w), Function.update_self, hφ, mul_assoc]
    congr 2
    refine Finset.prod_congr rfl fun w' hw' => ?_
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hw'), (isSw_fP (P w')).choose_spec]
  exact h hΨ
end PositivityTheory.SiegelWeilFormula.KFock
end
end
end

