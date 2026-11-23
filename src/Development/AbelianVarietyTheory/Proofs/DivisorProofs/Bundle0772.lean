module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Formalism.QuotientMetricDivisors.Statement
public import Formalism.MeanHeightDescent.DivisionInequalityWithCovolume
public import Development.AbelianVarietyTheory.Counterexamples.RotationExamples.MeasureFailsForLargeConstant
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsAddHaarMeasureVolumeLie
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0740
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0767
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0760
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0759
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0713
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.ExistsNormRconvLeSiegel
public import GroundTheory.AutomorphicForms.ReductionSiegel
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0764
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0761
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0762
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0676
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0668
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumePerRankLeNegSlopeScaled
section
open NumberField

noncomputable section

namespace GlobalTheory.CovolCore

section Transport

variable {R V W E F : Type} [Ring R] [AddCommGroup V] [Module R V] [AddCommGroup W] [Module R W]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem rk_deg_transport (ρ : V →+ E) (σ : W →+ F) (T : V →+ W) {A : Submodule R V} {B : Submodule R W}
    (hA : Formalism.HN.IsLat ρ A) (hB : Formalism.HN.IsLat σ B)
    (hAB : ∀ y, y ∈ B ↔ ∃ x ∈ A, T x = y) (hn : ∀ x ∈ A, ‖σ (T x)‖ = ‖ρ x‖) :
    Formalism.HN.rk σ B = Formalism.HN.rk ρ A ∧ Formalism.HN.deg σ B = Formalism.HN.deg ρ A := by
  let f : A.toAddSubgroup →+ E := ρ.comp A.toAddSubgroup.subtype
  let g : A.toAddSubgroup →+ F := (σ.comp T).comp A.toAddSubgroup.subtype
  have h1 : ∀ y, y ∈ Formalism.HN.zl ρ A ↔ ∃ m, f m = y :=
    fun y => ⟨fun ⟨m, hm, e⟩ => ⟨⟨m, hm⟩, e⟩, fun ⟨m, e⟩ => ⟨m.1, m.2, e⟩⟩
  have h2 : ∀ y, y ∈ Formalism.HN.zl σ B ↔ ∃ m, g m = y := fun y =>
    ⟨fun ⟨m, hm, e⟩ => by
      obtain ⟨x, hx, rfl⟩ := (hAB m).1 hm
      exact ⟨⟨x, hx⟩, e⟩, fun ⟨m, e⟩ => ⟨T m.1, (hAB _).2 ⟨m.1, m.2, rfl⟩, e⟩⟩
  have hn' : ∀ m, ‖f m‖ = ‖g m‖ := fun m => (hn m.1 m.2).symm
  haveI := hA.2
  haveI := hB.2
  refine ⟨?_, ?_⟩
  · have hf : Function.Injective f := fun x y h => Subtype.ext (hA.1 x.2 y.2 h)
    have hg : Function.Injective g := fun x y h =>
      hf (Formalism.HN.QuotientRealization.eq_of_norm_eq g f (fun m => (hn' m).symm) h)
    have e1 : Formalism.HN.zl ρ A = LinearMap.range f.toIntLinearMap := Submodule.ext h1
    have e2 : Formalism.HN.zl σ B = LinearMap.range g.toIntLinearMap := Submodule.ext h2
    unfold Formalism.HN.rk Formalism.F.rk
    rw [e1, e2, ← (LinearEquiv.ofInjective f.toIntLinearMap hf).finrank_eq,
      ← (LinearEquiv.ofInjective g.toIntLinearMap hg).finrank_eq]
  · unfold Formalism.HN.deg Formalism.F.deg
    rw [Formalism.HN.QuotientRealization.covol_eq_of_norm_eq f g _ _ h1 h2 hn']

end Transport

theorem cnorm_smul {ι : Type} [Fintype ι] (s : ℝ) (hs : 0 ≤ s) (u : ι → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm ((s : ℂ) • u) = s * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs, mul_pow,
    ← Finset.mul_sum]
  rw [Real.sqrt_mul (sq_nonneg s), Real.sqrt_sq hs]

end GlobalTheory.CovolCore

namespace GlobalTheory.CovolCore

theorem lcv_div_le_neg_slope_sq : ∀ (K V : Type) [Field K] [NumberField K] [IsTotallyComplex K] [StarRing K]
    [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (N : (K →+* ℂ) → V → ℝ), GlobalTheory.AllWt.HasGram N →
    ∀ (L : Submodule (𝓞 K) V) (d : ℕ), 0 < d → ∀ (b : Fin d → V), LinearIndependent K b →
    (∀ x ∈ L, x ∈ Submodule.span K (Set.range b)) →
    ∀ (X : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ) (s : ℝ), 0 < s → s ≤ 1 → (∀ v, IsUnit (X v).det) →
    (∀ v (c : Fin d → K), Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X v c = s * N v.embedding (∑ k, c k • b k)) →
    Submodule.IsFullLattice K (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) →
    Formalism.DivisionValues.lcv X (L.comap ((Fintype.linearCombination K b).restrictScalars (𝓞 K))) / (d : ℝ) ≤
      -GlobalTheory.AllWt.slope_sq N L := by
  intro K V _ _ _ _ _ _ _ _ N hN L d hd b hb hLb X s hs0 hs1 hX hnorm hM
  set φ := Fintype.linearCombination K b with hφ
  set M := L.comap (φ.restrictScalars (𝓞 K)) with hMdef
  have hφa : ∀ c : Fin d → K, φ c = ∑ k, c k • b k := fun c => Fintype.linearCombination_apply K b c
  let X' : InfinitePlace K → Matrix (Fin d) (Fin d) ℂ := fun v => (s : ℂ) • X v
  have hs' : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hX' : ∀ v, IsUnit (X' v).det := fun v => by
    show IsUnit ((s : ℂ) • X v).det
    rw [Matrix.det_smul]
    exact ((Ne.isUnit hs').pow _).mul (hX v)
  have hfc : ∀ v c, Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X v c =
      (s : ℂ) • Formalism.HermitianLatticesTheory.fcoord (Pi.basisFun K (Fin d)) X' v c := by
    intro v c
    have e : X' v = (Units.mk0 (s : ℂ) hs') • X v := rfl
    simp only [Formalism.HermitianLatticesTheory.fcoord]
    rw [e, Matrix.inv_smul' (X v) (Units.mk0 (s : ℂ) hs') (hX v), Units.smul_def, Matrix.smul_mulVec, smul_smul,
      Units.val_inv_eq_inv_val, Units.val_mk0, mul_inv_cancel₀ hs', one_smul]
  have hOC : GlobalTheory.MeasureLeaf.OneConstant X X' (fun _ => s ^ 2) := fun v =>
    ⟨by positivity, fun x y => by
      simp only [Formalism.HermitianLatticesTheory.majAt, hfc, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [star_mul', Complex.star_def, Complex.conj_ofReal]
      push_cast
      ring⟩
  have hn' : ∀ v c, Formalism.HermitianLatticesTheory.normAt (Pi.basisFun K (Fin d)) X' v c = N v.embedding (φ c) := by
    intro v c
    have h := hnorm v c
    simp only [Formalism.HermitianLatticesTheory.normAt, hfc, cnorm_smul s hs0.le] at h
    rw [hφa]
    exact mul_left_cancel₀ hs0.ne' h
  have h1 := GlobalTheory.MeasureLeaf.lcv_of_oneConstant hd X X' hX hX' (fun _ => s ^ 2) hOC M hM
  have h2 := Formalism.ExtensionFiltration.lcvMu K d hd X' hX' M hM
  have hlog : 2 / (Module.finrank ℚ K : ℝ) * ∑ v : InfinitePlace K, Real.log (s ^ 2) ≤ 0 := by
    refine mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos fun v _ => ?_)
    exact Real.log_nonpos (sq_nonneg _) (by nlinarith)
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hMfg : M.FG := hM.toIsLattice.fg
  have hML : ∀ y, y ∈ L ↔ ∃ x ∈ M, φ x = y := fun y =>
    ⟨fun hy => by
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun K).1 (hLb y hy)
      refine ⟨c, ?_, by rw [hφa, hc]⟩
      show φ c ∈ L
      rw [hφa, hc]; exact hy,
     fun ⟨x, hx, e⟩ => e ▸ hx⟩
  have hLM : L = M.map (φ.restrictScalars (𝓞 K)) := by
    ext y
    rw [hML y, Submodule.mem_map]
    rfl
  have hLfg : L.FG := by rw [hLM]; exact hMfg.map _
  obtain ⟨⟨n, ⟨b0, X0⟩, hG⟩⟩ := id hN
  change GlobalTheory.AllWt.IsGram b0 X0 N at hG
  rw [GlobalTheory.AllWt.slope_sq_eq hG hLfg]
  have hlatM := (Formalism.HN.plLat K (Fin d → K) (Fin d) (Pi.basisFun K (Fin d)) X' hX' M hMfg).1
  have hlatL := (Formalism.HN.plLat K V (Fin n) b0 X0 (fun v => (hG v).1) L hLfg).1
  have hnr : ∀ x ∈ M, ‖Formalism.HermitianLatticesTheory.realize b0 X0 (φ.toAddMonoidHom x)‖ =
      ‖Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X' x‖ := fun x _ => by
    rw [← sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _), GlobalTheory.AllWt.norm_realize_sq, GlobalTheory.AllWt.norm_realize_sq]
    exact Finset.sum_congr rfl fun v _ => by rw [(hG v).2, hn' v x]; rfl
  obtain ⟨e1, e2⟩ := rk_deg_transport (Formalism.HermitianLatticesTheory.realize (Pi.basisFun K (Fin d)) X')
    (Formalism.HermitianLatticesTheory.realize b0 X0) φ.toAddMonoidHom hlatM hlatL hML hnr
  have key : Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M = Formalism.HN.muDef b0 X0 L := by
    unfold Formalism.HN.rk at e1
    unfold Formalism.HN.deg at e2
    unfold Formalism.HN.muDef Formalism.HN.slope Formalism.F.slope
    rw [e1, e2]
  have h3 : Formalism.DivisionValues.lcv X' M / (d : ℝ) = -Formalism.HN.muDef (Pi.basisFun K (Fin d)) X' M := by
    rw [h2]; field_simp
  rw [h1, h3, key]
  linarith

end GlobalTheory.CovolCore
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EsymmMulSchurPolynomialJacobiTrudi
section
open scoped Classical

open MvPolynomial in
theorem GlobalTheory.JSW.PieriDeterminant.vdm_ne (n : ℕ) : Matrix.det (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) ≠ 0 := by
  have h : (Matrix.of fun i j : Fin n => (X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) =
      (Matrix.vandermonde (fun i => (X i : MvPolynomial (Fin n) ℤ))).submatrix id Fin.revPerm := by
    ext i j
    simp only [Matrix.of_apply, Matrix.submatrix_apply, Matrix.vandermonde_apply, id, Fin.revPerm_apply, Fin.val_rev]
    rw [show n - 1 - (j : ℕ) = n - ((j : ℕ) + 1) by omega]
  rw [h, Matrix.det_permute']
  refine mul_ne_zero (by simp [Units.ne_zero]) ?_
  rw [Matrix.det_vandermonde_ne_zero_iff]
  exact MvPolynomial.X_injective

namespace GlobalTheory.JSW.PieriDeterminant

theorem adj {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n)) :
    ∀ d : ℕ, ∀ a b : Fin n, (b : ℕ) = a + d + 1 → l a = l b → a ∉ J → b ∈ J →
      ∃ a' b' : Fin n, (b' : ℕ) = a' + 1 ∧ l a' = l b' ∧ a' ∉ J ∧ b' ∈ J := by
  intro d
  induction d with
  | zero => intro a b h1 h2 h3 h4; exact ⟨a, b, by omega, h2, h3, h4⟩
  | succ d ih =>
    intro a b h1 h2 h3 h4
    have hc : (a : ℕ) + 1 < n := by have := b.isLt; omega
    let c : Fin n := ⟨a + 1, hc⟩
    have hac : a ≤ c := by show (a : ℕ) ≤ a + 1; omega
    have hcb : c ≤ b := by show (a : ℕ) + 1 ≤ b; omega
    have hlc : l c = l a := le_antisymm (hl hac) (h2 ▸ hl hcb)
    by_cases hcJ : c ∈ J
    · exact ⟨a, c, rfl, hlc.symm, h3, hcJ⟩
    · exact ih c b (by show (b : ℕ) = a + 1 + d + 1; omega) (hlc.trans h2) hcJ h4

theorem det_zero {n : ℕ} (l : Fin n → ℕ) (hl : Antitone l) (J : Finset (Fin n))
    (hJ : ¬ Antitone (l + (fun i => if i ∈ J then 1 else 0))) :
    Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
      ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) = 0 := by
  obtain ⟨a, b, hab, hlt⟩ : ∃ a b : Fin n, a ≤ b ∧ ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) a <
      ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) b := by
    simp only [Antitone, not_forall, not_le] at hJ
    obtain ⟨a, b, h1, h2⟩ := hJ; exact ⟨a, b, h1, h2⟩
  simp only [Pi.add_apply] at hlt
  have hla := hl hab
  have hA : a ∉ J := by intro h; simp only [h, if_true] at hlt; split_ifs at hlt <;> omega
  have hB : b ∈ J := by by_contra h; simp only [h, if_false] at hlt; split_ifs at hlt <;> omega
  have hE : l a = l b := by simp only [hA, hB, if_true, if_false] at hlt; omega
  have hne : a ≠ b := by rintro rfl; exact hA hB
  obtain ⟨a', b', h1, h2, h3, h4⟩ :=
    adj l hl J ((b : ℕ) - a - 1) a b (by have : (a : ℕ) < b := lt_of_le_of_ne hab (fun h => hne (Fin.ext h)); omega) hE hA hB
  refine Matrix.det_zero_of_column_eq (i := a') (j := b') (fun h => by rw [h] at h1; omega) (fun i => ?_)
  simp only [Matrix.of_apply, h3, h4, if_true, if_false]
  congr 1
  have := b'.isLt
  omega

end GlobalTheory.JSW.PieriDeterminant

open MvPolynomial in
theorem GlobalTheory.JSW.esymm_mul_schur : ∀ (n : ℕ) (l : Fin n → ℕ), Antitone l → ∀ j ≤ n, MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j ∧ Antitone (l + (fun i => if i ∈ J then 1 else 0))), GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) := by
  intro n l hl j _
  apply mul_right_cancel₀ (GlobalTheory.JSW.PieriDeterminant.vdm_ne n)
  have h1 := _root_.GlobalTheory.JSW.esymm_mul_alternant n (fun k => l k + n - 1 - k) j
  beta_reduce at h1
  calc MvPolynomial.esymm (Fin n) ℤ j * GlobalTheory.JSW.schur n l * _
      = ∑ J ∈ (Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        rw [mul_assoc, GlobalTheory.T.schur_mul_vandermonde_det_eq_det n l hl, h1]
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          Matrix.det (Matrix.of fun i k : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^
            ((l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0)) := by
        refine (Finset.sum_filter_of_ne fun J _ hJ => ?_).symm
        by_contra h
        exact hJ (GlobalTheory.JSW.PieriDeterminant.det_zero l hl J h)
    _ = ∑ J ∈ ((Finset.univ : Finset (Finset (Fin n))).filter (fun J => J.card = j)).filter
          (fun J => Antitone (l + (fun i => if i ∈ J then 1 else 0))),
          GlobalTheory.JSW.schur n (l + (fun i => if i ∈ J then 1 else 0)) *
            Matrix.det (Matrix.of fun i j : Fin n => (MvPolynomial.X i : MvPolynomial (Fin n) ℤ) ^ (n - 1 - (j : ℕ))) := by
        refine Finset.sum_congr rfl fun J hJ => ?_
        rw [GlobalTheory.T.schur_mul_vandermonde_det_eq_det n _ (Finset.mem_filter.1 hJ).2]
        have e : ∀ k : Fin n, ((l + (fun i => if i ∈ J then 1 else 0) : Fin n → ℕ)) k + n - 1 - (k : ℕ) =
            (l k + n - 1 - (k : ℕ)) + if k ∈ J then 1 else 0 := by
          intro k; have := k.isLt; simp only [Pi.add_apply]; split_ifs <;> omega
        simp only [e]
    _ = _ := by rw [Finset.filter_filter, Finset.sum_mul]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyFieldEqGaloisCohomologyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomology_field_eq_galoisCohomology : GlobalTheory.EtC.B7 := by
  first | (exact @GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (exact GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois) | (intros; apply GlobalTheory.EtC.FieldTw.field_tw_coh_eq_galois  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAffineSpaceMorphismOfCoordinatesStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_affineSpace_morphism_of_coordinates : ∀ (Rg : Type) [CommRing Rg] (T : Scheme.{0}) (n : ℕ) (t : T ⟶ Sp Rg) (x : Fin n → Γ(T, ⊤)), ∃ g : T ⟶ Sp (MvPolynomial (Fin n) Rg), g ≫ affπ Rg n = t ∧ ∀ i, coord g i = x i := by
  first | (exact @GlobalTheory.HomFixPoint.exists_affine_hom) | (exact GlobalTheory.HomFixPoint.exists_affine_hom) | (intros; apply GlobalTheory.HomFixPoint.exists_affine_hom  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjFiniteUnipotentMemOpenSubgroupStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_conj_finiteUnipotent_mem_openSubgroup : ∀ (E : Type) [Field E] [NumberField E] (a r : ℕ) (L : Subgroup (GL (Fin a) (Af E))),
    IsOpen (L : Set (GL (Fin a) (Af E))) → ∀ ω : Set (GA E a), IsCompact ω →
    ∃ M : ℕ, 0 < M ∧ ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i), ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
      ∀ z : BlockIx a r → Ad E, (∀ p, (z p).1 = 0) →
      (∀ p, ∃ c ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E, (z p).2 = (M : Af E) * c) →
      ∃ l ∈ L, (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k)⁻¹ * unip z *
        (b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k) = finGL E a l := by
  first | exact @GlobalTheory.FinConj.exists_conj_unip_mem | exact GlobalTheory.FinConj.exists_conj_unip_mem | (intros; apply GlobalTheory.FinConj.exists_conj_unip_mem <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqSqSubMulSq
section
open scoped TensorProduct
open IsLocalRing IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace GlobalTheory.OddLocalNormEtale

theorem exists_eq_sq_sub_mul_sq : ∀ (L : Type) [CommRing L] [IsReduced L] [Algebra ℚ L] [FiniteDimensional ℚ L] (v : IsDedekindDomain.HeightOneSpectrum ℤ), v.asIdeal ≠ Ideal.span {2} →
    ∀ m m' d d' : v.adicCompletion ℚ ⊗[ℚ] L, m * m' = 1 → d * d' = 1 →
    (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval m' f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d f = 0) → (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧ (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval d' f = 0) →
    ∃ a b : v.adicCompletion ℚ ⊗[ℚ] L, m = a * a - d * (b * b) := by
  intro L _ _ _ _ v hv m m' d d' hm hd im im' id id'
  obtain ⟨hH, hF⟩ := GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField v
  letI : Algebra (v.adicCompletionIntegers ℚ) (v.adicCompletion ℚ ⊗[ℚ] L) :=
    ((algebraMap (v.adicCompletion ℚ) (v.adicCompletion ℚ ⊗[ℚ] L)).comp
      (v.adicCompletionIntegers ℚ).subtype).toAlgebra
  have key : ∀ x : v.adicCompletion ℚ ⊗[ℚ] L,
      (∃ f : Polynomial (v.adicCompletion ℚ), f.Monic ∧
        (∀ i, f.coeff i ∈ v.adicCompletionIntegers ℚ) ∧ Polynomial.aeval x f = 0) →
      IsIntegral (v.adicCompletionIntegers ℚ) x := by
    rintro x ⟨f, hf, hc, hx⟩
    obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic
      (f := (v.adicCompletionIntegers ℚ).subtype)
      ((Polynomial.lifts_iff_coeff_lifts f).2 fun n => ⟨⟨_, hc n⟩, rfl⟩) hf
    refine ⟨g, hgm, ?_⟩
    rw [← hg, Polynomial.aeval_def, Polynomial.eval₂_map] at hx
    exact hx
  have h2 : (2 : ℤ) ∉ v.asIdeal := fun h =>
    hv ((PrincipalIdealRing.isMaximal_of_irreducible Int.prime_two.irreducible).eq_of_le
      v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2u : IsUnit (2 : v.adicCompletionIntegers ℚ) := by
    rw [adicCompletionIntegers.isUnit_iff_valued_eq_one]
    have h := valuedAdicCompletion_eq_valuation' v (2 : ℚ)
    have h' : v.valuation ℚ (2 : ℚ) = 1 := by
      have := (valuation_eq_one_iff_notMem v (K := ℚ) (r := (2 : ℤ))).2 h2
      simpa using this
    rw [h'] at h
    rw [← h]
    congr 1
    exact (map_ofNat (algebraMap ℚ (v.adicCompletion ℚ)) 2).symm
  exact GlobalTheory.OddLocalNorm.exists_eq_of_isIntegral (v.adicCompletionIntegers ℚ) h2u hm hd
    (key _ im) (key _ im') (key _ id) (key _ id')

end GlobalTheory.OddLocalNormEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEtaleNbhdKillingCurveCohomologyClassStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_etaleNbhd_killing_curveCohomologyClass : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (n i : ℤ), 0 < n → ∀ x : Ht q (sp B) n i, ∃ (A' : Type) (_ : CommRing A') (_ : Algebra B A'), IsExcisionNbhd B A' f ∧ pull _ (spMap (algebraMap B A')) _ _ x = 0 := by
  first | (exact @GlobalTheory.EtC.CurveNbhdExcision.main) | (exact GlobalTheory.EtC.CurveNbhdExcision.main) | (intros; apply GlobalTheory.EtC.CurveNbhdExcision.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsImmersedClosedOpenIntersectionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat GlobalTheory.HomFixUniv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_immersed_closed_open_intersection : ∀ (Y : Scheme.{0}) [IsNoetherian Y] (Z₁ Z₂ : Scheme.{0}) (ι₁ : Z₁ ⟶ Y) (ι₂ : Z₂ ⟶ Y) (U : Y.Opens), IsClosedImmersion ι₁ → IsClosedImmersion ι₂ → ∃ (W : Scheme.{0}) (j : W ⟶ Y), IsImmersion j ∧ QuasiCompact j ∧ IsLocallyNoetherian W ∧ ∀ (T : Scheme.{0}) (g : T ⟶ Y), ((∃ w : T ⟶ Z₁, w ≫ ι₁ = g) ∧ (∃ w : T ⟶ Z₂, w ≫ ι₂ = g) ∧ ∀ τ, g τ ∈ U) ↔ ∃ w : T ⟶ W, w ≫ j = g := by
  first | (exact @GlobalTheory.HomFixMat.exists_immersed_locus) | (exact GlobalTheory.HomFixMat.exists_immersed_locus) | (intros; apply GlobalTheory.HomFixMat.exists_immersed_locus  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsCompactDetBandSiegelSetStatement
section
open NumberField MeasureTheory GlobalTheory.CuspRep GlobalTheory.HCF Topology
open scoped NumberField.AdeleRing
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_isCompact_detBand_siegelSet : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ω : Set (GA E a)), IsCompact ω →
    ∀ t R : ℝ, 0 < t → ∃ C : Set (GA E a), IsCompact C ∧ C ⊆ band E a ∧
      ∀ b ∈ ω, ∀ (ρ : Fin a → ℝ) (hρ : ∀ i, 0 < ρ i),
        (∀ i j : Fin a, (j : ℕ) = i + 1 → t * ρ j ≤ ρ i) → (∀ i j : Fin a, (j : ℕ) = i + 1 → ρ i ≤ R * ρ j) →
        ∀ k ∈ (GroundTheory.Automorphic.Reduction.maxCompact (K := E) (n := a)),
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ band E a →
          b * GroundTheory.Automorphic.Reduction.diagUnits a (fun i => GroundTheory.Automorphic.Reduction.posIdele (K := E) (ρ i) (hρ i)) * k ∈ C := by
  first | exact @GlobalTheory.SiegelBand.exists_isCompact_band_siegel | exact GlobalTheory.SiegelBand.exists_isCompact_band_siegel | (intros; apply GlobalTheory.SiegelBand.exists_isCompact_band_siegel <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKummerClassAgreeingNearZerosStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_kummerClass_agreeing_near_zeros : ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → ∀ f : B, f ≠ 0 → ∀ (A' : Type) [CommRing A'] [Algebra B A'], IsExcisionNbhd B A' f → ∀ w : Ht q (sp (Localization.Away (algebraMap B A' f))) 1 1, ∃ g : B, IsCoprime f g ∧ ∃ (A₂ C : Type) (_ : CommRing A₂) (_ : CommRing C) (_ : Algebra B A₂) (_ : Algebra A' A₂) (_ : IsScalarTower B A' A₂) (_ : Algebra B C), IsExcisionNbhd B A₂ f ∧ IsUnit (algebraMap B A₂ g) ∧ IsExcisionNbhd B C g ∧ ∃ a : Ht q (sp (Localization.Away (f * g))) 1 1, pull _ (spMap (Localization.awayMap (algebraMap B C) (f * g))) _ _ a = 0 ∧ ∀ (φ : Localization.Away (algebraMap B A' f) →+* Localization.Away (algebraMap B A₂ f)) (ψ : Localization.Away (f * g) →+* Localization.Away (algebraMap B A₂ f)), φ.comp (algebraMap A' _) = (algebraMap A₂ _).comp (algebraMap A' A₂) → ψ.comp (algebraMap B _) = (algebraMap A₂ _).comp (algebraMap B A₂) → pull _ (spMap φ) _ _ w = pull _ (spMap ψ) _ _ a := by
  first | (exact @GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros) | (exact GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros) | (intros; apply GlobalTheory.EtC.KummerStep.exists_class_agreeing_near_zeros <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteField
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.ParamLabel

variable {p : ℕ} [Fact p.Prime]

theorem exists_labelsChar_of_pos (L : GlobalTheory.GLq.LabelDatum p) {d : ℕ} (hd : 0 < d) (θ : Tor p d →* ℂˣ) :
    ∃ x : Fbar p, LabelsChar L θ x := by
  have hp : 0 < p ^ d - 1 := Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' (Fact.out : p.Prime).one_lt)
  haveI : NeZero (p ^ d - 1) := ⟨hp.ne'⟩
  have hprim : IsPrimitiveRoot (L.gen d) (p ^ d - 1) := L.gen_order d hd ▸ IsPrimitiveRoot.orderOf _
  have h0 : L.gen d ≠ 0 := hprim.ne_zero hp.ne'
  have hprimC : IsPrimitiveRoot (L.teich (L.gen d)) (p ^ d - 1) := by
    refine ⟨by rw [← map_pow, hprim.pow_eq_one, map_one], fun l hl => hprim.dvd_of_pow_eq_one l ?_⟩
    exact L.teich_inj _ _ (pow_ne_zero _ h0) one_ne_zero (by rw [map_pow, hl, map_one])
  let γ : Tor p d := ⟨Units.mk0 _ h0, by
    rw [mem_rootsOfUnity]
    exact Units.ext (by simpa using hprim.pow_eq_one)⟩
  have hγ : γ ^ (p ^ d - 1) = 1 := Subtype.ext ((mem_rootsOfUnity _ _).1 γ.2)
  obtain ⟨k, -, hk⟩ := hprimC.eq_pow_of_pow_eq_one (ξ := ((θ γ : ℂˣ) : ℂ))
    (by rw [← Units.val_pow_eq_pow_val, ← map_pow, hγ, map_one, Units.val_one])
  refine ⟨L.gen d ^ k, by rw [← pow_mul, mul_comm, pow_mul, hprim.pow_eq_one, one_pow], fun u => ?_⟩
  have hu : ((u : (Fbar p)ˣ) : Fbar p) ^ (p ^ d - 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, (mem_rootsOfUnity _ _).1 u.2, Units.val_one]
  obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hu
  have hex : ∃ n : ℕ, ((u : (Fbar p)ˣ) : Fbar p) = L.gen d ^ n := ⟨n, hn.symm⟩
  unfold GlobalTheory.GLq.thetaOf
  rw [dite_eq_left hex]
  have e : u = γ ^ hex.choose := Subtype.ext (Units.ext (by simpa [γ] using hex.choose_spec))
  rw [map_pow, hk, ← Units.val_pow_eq_pow_val, ← map_pow, ← e]

theorem prod_frobenius_orbit_mem_lifts {d : ℕ} {x : Fbar p} (hx : x ^ (p ^ d - 1) = 1) :
    (∏ i : Fin d, (X - C (x ^ p ^ (i : ℕ)))) ∈ Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
  have hxd : x ^ p ^ d = x := by
    have h1 : p ^ d = (p ^ d - 1) + 1 := (Nat.sub_add_cancel (Nat.one_le_pow _ _ (Fact.out : p.Prime).pos)).symm
    rw [h1, pow_succ, hx, one_mul]
  rw [Fin.prod_univ_eq_prod_range (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d]
  have hfix : (∏ i ∈ Finset.range d, (X - C (x ^ p ^ i) : (Fbar p)[X])).map (frobenius (Fbar p) p) =
      ∏ i ∈ Finset.range d, (X - C (x ^ p ^ i)) := by
    have h1 := Finset.prod_range_succ (fun i => (X - C (x ^ p ^ i) : (Fbar p)[X])) d
    rw [Finset.prod_range_succ', hxd, pow_zero, pow_one] at h1
    rw [Polynomial.map_prod, ← mul_right_cancel₀ (X_sub_C_ne_zero x) h1]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Polynomial.map_sub, map_X, map_C, frobenius_def, pow_succ, pow_mul]
  rw [Polynomial.lifts_iff_coeff_lifts]
  intro n
  have h2 := congrArg (fun q => q.coeff n) hfix
  simp only [coeff_map, frobenius_def] at h2
  obtain ⟨m, hm⟩ := (mem_bot_iff_intCast p (Fbar p)).1 ((Subfield.mem_bot_iff_pow_eq_self (Fbar p) p).2 h2)
  exact ⟨(m : ZMod p), by rw [map_intCast, hm]⟩

theorem exists_labels (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r) :
    ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  choose x hx using fun c : Cyc s.1 => exists_labelsChar_of_pos L (cycLen_pos s.1 c) (s.2 c)
  have hl : (∏ y : Σ c : Cyc s.1, Fin (cycLen s.1 c), (X - C (rootElt x y))) ∈
      Polynomial.lifts (algebraMap (ZMod p) (Fbar p)) := by
    rw [Fintype.prod_sigma]
    refine Subsemiring.prod_mem _ fun c _ => ?_
    simp only [rootElt]
    exact prod_frobenius_orbit_mem_lifts (d := cycLen s.1 c) (x := x c) (hx c).1
  obtain ⟨f, hf, -, hm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl
    (monic_prod_of_monic _ _ fun y _ => monic_X_sub_C _)
  refine ⟨x, f, hx, fun c => (hx c).1, hm, ?_⟩
  unfold Formalism.CyclotomicNorms.rootsBar
  rw [hf, ← Polynomial.roots_multiset_prod_X_sub_C (Finset.univ.val.map (rootElt x)), Multiset.map_map]
  rfl

end GlobalTheory.ParamLabel
end

