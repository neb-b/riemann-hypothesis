module

public import Mathlib
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.NDDefs
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.GelfandKazhdanDuality.IsCuspFormDualMap
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHasCentChar
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1206
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DiscreteSpectrumGLTwoOfCuspidalSpectrum
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0382
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0360
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajan
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Unfold2
public import Formalism.RealPlaceAnalysis.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SubsingletonRankZero
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspDiscreteDecompositionGL
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinGLMemOfPow
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0114
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0002
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.ClozelPurity.EopV

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousOnRingInverseOfIsOpenEmbeddingUnits
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.GLOpen

theorem continuousOn_ringInverse_of_isOpenEmbedding_units
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) :
    ContinuousOn (Ring.inverse : A → A) {x | IsUnit x} := by
  rintro _ ⟨u, rfl⟩
  refine ContinuousAt.continuousWithinAt ?_
  rw [← hA.continuousAt_iff]
  have h : (Ring.inverse ∘ Units.val : Aˣ → A) = fun v => ((v⁻¹ : Aˣ) : A) := by
    funext v
    exact Ring.inverse_unit v
  rw [h]
  exact Units.continuous_coe_inv.continuousAt

theorem isOpenEmbedding_val_GL
    (A : Type) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]
    (hA : IsOpenEmbedding (Units.val : Aˣ → A)) (n : ℕ) :
    IsOpenEmbedding (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) := by
  have hdet : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.det) :=
    continuous_id.matrix_det
  have hunit : ∀ M : Matrix (Fin n) (Fin n) A, IsUnit M ↔ IsUnit M.det :=
    fun M => Matrix.isUnit_iff_isUnit_det M
  have hadj : Continuous (fun M : Matrix (Fin n) (Fin n) A => M.adjugate) :=
    continuous_id.matrix_adjugate
  have hopen : IsOpen {x : A | IsUnit x} := hA.isOpen_range
  refine ⟨Units.isEmbedding_val_mk' (f := fun M : Matrix (Fin n) (Fin n) A => M⁻¹) ?_
    fun u => (Matrix.coe_units_inv u).symm, ?_⟩
  · have hinv : ContinuousOn
        (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det • M.adjugate) {M | IsUnit M} := by
      have hri : ContinuousOn (fun M : Matrix (Fin n) (Fin n) A => Ring.inverse M.det)
          {M | IsUnit M} :=
        (GlobalTheory.CompanionTheory.SW.GLOpen.continuousOn_ringInverse_of_isOpenEmbedding_units A hA).comp hdet.continuousOn
          fun M hM => (hunit M).mp hM
      exact hri.smul hadj.continuousOn
    exact hinv.congr fun M _ => Matrix.inv_def M
  · have h : Set.range (Units.val : GL (Fin n) A → Matrix (Fin n) (Fin n) A) =
        (fun M : Matrix (Fin n) (Fin n) A => M.det) ⁻¹' {x | IsUnit x} := by
      ext M
      exact hunit M
    rw [h]
    exact hopen.preimage hdet

end GlobalTheory.CompanionTheory.SW.GLOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CuspidalEqTwistNormalised
section
noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.L2.Host GlobalTheory.CuspRep GlobalTheory.ContraPair GlobalTheory.DiscSpec GlobalTheory.UnitaryBC PositivityTheory.PRW.GKD

namespace GlobalTheory.CompanionTheory.TwistNorm

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

theorem val_expId (ω : HChar E) (t : ℝ) :
    ((ω.1 (GlobalTheory.DiscChar.expId E t) : ℂˣ) : ℂ) = Complex.exp (t * dchi ω 1) := by
  refine (chiInf_expU ω _).trans (congrArg _ ?_)
  rw [show (fun _ : InfinitePlace E => (t : ℂ)) = t • (1 : Cinf E) from funext fun _ => by simp, map_smul]
  simp

theorem isNormalised_rank_zero (π : CuspSub E 0) : IsNormalised π := fun φ _ t g => by
  rw [Subsingleton.elim (splitCentre E 0 t * g) g]

theorem isNormalised_twist {π : CuspSub E a} {ω ν : HChar E} (hω : π.HasCentral ω)
    (hν : ∀ t : ℝ, ((chiDet a ν (splitCentre E a t) : ℂˣ) : ℂ) = Complex.exp (-(t * dchi ω 1))) :
    IsNormalised (π.twist ν) := by
  rintro _ ⟨ψ, hψ, rfl⟩ t g
  change ψ.1 (splitCentre E a t * g) * (chiDet a ν (splitCentre E a t * g) : ℂˣ) = ψ.1 g * (chiDet a ν g : ℂˣ)
  have h1 : ψ.1 (splitCentre E a t * g) = Complex.exp (t * dchi ω 1) * ψ.1 g := by
    rw [GlobalTheory.CuspRep.CuspidalL2GL.splitCentre_eq_scalar, hω.apply hψ]
    exact congrArg (· * ψ.1 g) (val_expId ω t)
  rw [h1, map_mul, Units.val_mul, hν, mul_mul_mul_comm, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]

theorem exists_twist_normalised : ∀ {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}, ∀ (π : CuspSub E a),
    ∃ (π₀ : CuspSub E a) (χ : HChar E), IsNormalised π₀ ∧ π = π₀.twist χ := by
  intro E _ _ _ a π
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact ⟨π, 1, isNormalised_rank_zero π, π.twist_one.symm⟩
  · obtain ⟨ω, hω⟩ := Central.exists_hasCentral E a π
    obtain ⟨ν, hν⟩ := GlobalTheory.SplitCentreChar.exists_hChar_splitCentre E a ha (dchi ω 1)
    refine ⟨π.twist ν, ν⁻¹, isNormalised_twist hω hν, ?_⟩
    rw [← CuspSub.twist_mul, mul_inv_cancel, CuspSub.twist_one]

end GlobalTheory.CompanionTheory.TwistNorm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DiracKHolds
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.InjHw

namespace GlobalTheory.CompanionTheory.RealMult.DiracProof

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {Kf : Fin n → Fin n → Module.End ℂ V}

theorem expU_add' (X : Matrix (Fin n) (Fin n) ℂ) (hX : Xᴴ = -X) (s t : ℝ) :
    expU X hX (s + t) = expU X hX s * expU X hX t := by
  apply Subtype.ext
  show NormedSpace.exp (((s + t : ℝ) : ℂ) • X) = NormedSpace.exp ((s : ℂ) • X) * NormedSpace.exp ((t : ℂ) • X)
  rw [Complex.ofReal_add, add_smul, Matrix.exp_add_of_commute]
  exact ((Commute.refl X).smul_left _).smul_right _

theorem expU_two_pi (a : Fin n) (hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I)) :
    expU (Matrix.single a a Complex.I) hX (2 * Real.pi) = 1 := by
  apply Subtype.ext
  show NormedSpace.exp (((2 * Real.pi : ℝ) : ℂ) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ)) = 1
  have e : (((2 * Real.pi : ℝ) : ℂ)) • (Matrix.single a a Complex.I : Matrix (Fin n) (Fin n) ℂ) =
      diagonal (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) := by
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hc : i = a
      · subst hc
        simp
      · simp [Matrix.single_apply, hc, Ne.symm hc]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.smul_apply, Matrix.single_apply,
        if_neg (fun hh => hij (hh.1.symm.trans hh.2)), smul_zero]
  rw [e, Matrix.exp_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext c
  have hh : NormedSpace.exp (fun c => if c = a then ((2 * Real.pi : ℝ) : ℂ) * Complex.I else 0) c =
      if c = a then Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) else 1 := by
    split_ifs with hc <;> simp [hc, Complex.exp_eq_exp_ℂ]
  rw [hh]
  have h2 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * Complex.I) = 1 := by
    push_cast
    exact Complex.exp_two_pi_mul_I
  rw [h2]
  simp

theorem weight_int (h : IsDerivK σ Kf) (a : Fin n) (r : ℝ) {v : V} (hv : v ≠ 0)
    (hr : Kf a a v = (r : ℂ) • v) : ∃ m : ℤ, r = m := by
  have hX : (Matrix.single a a Complex.I)ᴴ = -(Matrix.single a a Complex.I) := by
    rw [single_conjT, Complex.star_def, Complex.conj_I, single_negI]
  set X : Matrix (Fin n) (Fin n) ℂ := Matrix.single a a Complex.I with hXdef
  set φ : ℝ → V := fun s => σ (expU X hX s) v with hφ
  have hd0 : HasDerivAt φ ((Complex.I * r) • v) 0 := by
    have := deriv_expU (Kf := Kf) h X hX v
    have e := sum_single (Kf := Kf) v a a Complex.I
    rw [← hXdef] at e
    rw [e, hr, smul_smul] at this
    exact this
  have hstep : ∀ s, HasDerivAt φ ((Complex.I * r) • φ s) s := by
    intro s
    let L : V →L[ℝ] V :=
      ((LinearMap.isometryOfInner (σ (expU X hX s)) (h.1 _)).toContinuousLinearMap).restrictScalars ℝ
    have hL : ∀ y, L y = σ (expU X hX s) y := fun _ => rfl
    have h1 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) 0 :=
      L.hasFDerivAt.comp_hasDerivAt 0 hd0
    have h2 : HasDerivAt (fun t => L (φ t)) (L ((Complex.I * r) • v)) (s - s) := by
      rwa [sub_self]
    have h3 := h2.comp_sub_const s s
    have e : (fun t => L (φ (t - s))) = φ := by
      funext t
      have : expU X hX t = expU X hX s * expU X hX (t - s) := by
        rw [← expU_add']
        congr 1
        ring
      simp only [hL, hφ, this, map_mul, Module.End.mul_apply]
    rw [e] at h3
    have e2 : L ((Complex.I * r) • v) = (Complex.I * r) • φ s := by
      rw [hL, map_smul]
    rwa [e2] at h3
  set ψ : ℝ → V := fun s => Complex.exp ((s : ℂ) * (-(Complex.I * r))) • φ s with hψ
  have hψd : ∀ s, HasDerivAt ψ 0 s := by
    intro s
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ) * (-(Complex.I * r))) (-(Complex.I * r)) s := by
      simpa using (Complex.ofRealCLM.hasDerivAt (x := s)).mul_const (-(Complex.I * (r : ℂ)))
    have h2 := h1.cexp
    have h3 := h2.smul (hstep s)
    have : Complex.exp ((s : ℂ) * (-(Complex.I * r))) • (Complex.I * r) • φ s +
        (Complex.exp ((s : ℂ) * (-(Complex.I * r))) * -(Complex.I * r)) • φ s = 0 := by
      rw [smul_smul, ← add_smul]
      simp
    rw [this] at h3
    exact h3
  have hconst : ψ (2 * Real.pi) = ψ 0 :=
    is_const_of_deriv_eq_zero (fun s => (hψd s).differentiableAt) (fun s => (hψd s).deriv) _ _
  have h0 : φ 0 = v := by
    have : expU X hX 0 = 1 := by
      apply Subtype.ext
      show NormedSpace.exp (((0 : ℝ) : ℂ) • X) = 1
      simp
    simp [hφ, this]
  have h2π : φ (2 * Real.pi) = v := by
    show σ (expU X hX (2 * Real.pi)) v = v
    rw [show expU X hX (2 * Real.pi) = 1 from expU_two_pi a hX, map_one, Module.End.one_apply]
  have hE : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v = v := by
    have b : ψ 0 = v := by simp [hψ, h0]
    have a' : ψ (2 * Real.pi) = Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • v := by
      show Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) • φ (2 * Real.pi) = _
      rw [h2π]
    rw [← a', hconst, b]
  have hE1 : Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) = 1 := by
    have : (Complex.exp (((2 * Real.pi : ℝ) : ℂ) * (-(Complex.I * r))) - 1) • v = 0 := by
      rw [sub_smul, hE, one_smul, sub_self]
    rcases smul_eq_zero.1 this with h' | h'
    · exact sub_eq_zero.1 h'
    · exact absurd h' hv
  obtain ⟨m, hm⟩ := Complex.exp_eq_one_iff.1 hE1
  refine ⟨-m, ?_⟩
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h5 : (r : ℂ) = ((-m : ℤ) : ℂ) := by
    push_cast at hm ⊢
    have h6 : (2 * (Real.pi : ℂ) * Complex.I) * ((r : ℂ) + m) = 0 := by
      linear_combination -hm
    have h7 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [hpi, Complex.I_ne_zero]
    have := (mul_eq_zero.1 h6).resolve_left h7
    linear_combination this
  exact_mod_cast h5

theorem kF_gl {E1 E2 : Fin n → Fin n → Module.End ℂ V} (h : IsPair E1 E2) : Formalism.REAL.GlRel (kF E1 E2) := by
  intro a b c d
  have h1 := h.gl1 a b c d
  have h2 := h.gl2 a b c d
  have e : kF E1 E2 a b * kF E1 E2 c d - kF E1 E2 c d * kF E1 E2 a b =
      (E1 a b * E1 c d - E1 c d * E1 a b) + (E2 a b * E2 c d - E2 c d * E2 a b) := by
    simp only [kF, add_mul, mul_add]
    rw [h.comm a b c d, h.comm c d a b]
    abel
  rw [e, h1, h2]
  split_ifs <;> simp [kF] <;> abel

end GlobalTheory.CompanionTheory.RealMult.DiracProof

namespace GlobalTheory.CompanionTheory.RealMult

end GlobalTheory.CompanionTheory.RealMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinCellsDecomposition
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.EisCellsAsm

section Compl

variable {K : Type} [Field K]

theorem exists_isCompl {n r : ℕ} (c : Matrix (Fin r) (Fin n) K) (hc : LinearIndependent K c) :
    ∃ a : Matrix (Fin n) (Fin n) K, IsCompl c a := by
  classical
  set W := Submodule.span K (Set.range c) with hW
  obtain ⟨W', hWW'⟩ := Submodule.exists_isCompl W
  have hrW : Module.finrank K W = r := by
    rw [hW, finrank_span_eq_card hc, Fintype.card_fin]
  have hsum := Submodule.finrank_add_eq_of_isCompl hWW'
  rw [hrW, Module.finrank_fin_fun] at hsum
  set m := Module.finrank K W' with hm
  have hn : n = r + m := hsum.symm
  let bW : Module.Basis (Fin m) K W' := Module.finBasisOfFinrankEq K W' hm.symm
  let d : Fin m → (Fin n → K) := fun j => (bW j : Fin n → K)
  have hd : LinearIndependent K d :=
    bW.linearIndependent.map' W'.subtype (Submodule.ker_subtype W')
  have hdisj : Disjoint (Submodule.span K (Set.range c)) (Submodule.span K (Set.range d)) := by
    refine hWW'.disjoint.mono_right ?_
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (bW j).2
  have hv : LinearIndependent K (Sum.elim c d) := hc.sum_type hd hdisj
  let e : Fin n ≃ Fin r ⊕ Fin m := (finCongr hn).trans finSumFinEquiv.symm
  refine ⟨fun i => Sum.elim c d (e i), ?_, ?_⟩
  · have hli : LinearIndependent K (fun i => Sum.elim c d (e i)) := hv.comp e e.injective
    exact (Matrix.isUnit_iff_isUnit_det _).mp (Matrix.linearIndependent_rows_iff_isUnit.mp hli)
  · intro i hi
    have he : e i = Sum.inl ⟨i, hi⟩ := by
      have : finCongr hn i = Fin.castAdd m ⟨i, hi⟩ := Fin.ext rfl
      simp only [e, Equiv.trans_apply, this, finSumFinEquiv_symm_apply_castAdd]
    change Sum.elim c d (e i) = c ⟨i, hi⟩
    rw [he]
    rfl

end Compl

variable {D : D7} {n : ℕ}

abbrev sg (D : D7) : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)

theorem sg_sg (D : D7) (x : D.host.E) : sg D (sg D x) = x := by
  show star (star x) = x
  exact star_star x

theorem mat_mul' (x y : G D n) : mat (x * y) = mat x * mat y := by
  simp only [mat, map_mul, Units.val_mul]

theorem mat_inv_of (x : G D n) {g : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E} (hg : IsUnit g.det)
    (h : mat x = g.map (incA D)) : mat x⁻¹ = g⁻¹.map (incA D) := by
  have h1 : mat x⁻¹ = (mat x)⁻¹ := by
    simp only [mat, map_inv, Matrix.coe_units_inv]
  rw [h1, h]
  refine Matrix.inv_eq_left_inv ?_
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul g hg, Matrix.map_one _ (map_zero _) (map_one _)]

theorem mk_eq_iff_siegel (hR : RatPts) (x y : GF D n) {gx gy : Matrix (Fin (n + n)) (Fin (n + n)) D.host.E}
    (hx : IsUnit gx.det) (mx : mat x.1 = gx.map (incA D)) (my : mat y.1 = gy.map (incA D)) :
    mk ((P D n).subgroupOf (GF D n)) x = mk ((P D n).subgroupOf (GF D n)) y ↔ IsSiegelP (gy * gx⁻¹) := by
  have hmem : y.1 * x.1⁻¹ ∈ GF D n := mul_mem y.2 (inv_mem x.2)
  have hmat : mat (y.1 * x.1⁻¹) = (gy * gx⁻¹).map (incA D) := by
    rw [mat_mul', mat_inv_of x.1 hx mx, my, Matrix.map_mul]
  rw [← (hR D n).2.2 _ hmem _ hmat]
  show Quotient.mk _ x = Quotient.mk _ y ↔ _
  rw [Quotient.eq, QuotientGroup.rightRel_apply, Subgroup.mem_subgroupOf]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem isSiegelParabolic_one (K : Type) [Field K] (n : ℕ) : IsSiegelP (1 : Matrix (Fin (n + n)) (Fin (n + n)) K) := by
  unfold IsSiegelP
  intro i j
  exact Matrix.one_apply_ne (finSumFinEquiv.injective.ne Sum.inr_ne_inl)

theorem eisCells_of : Bruhat → RatPts → PInv → Term2 → EisCells := by
  intro hBr hRat hPInv hT2 D n V ψ χ θ μ ω hS Φ hconv μr hμr c hc
  classical
  have ha : ∀ U : Submodule D.host.E (Fin n → D.host.E), ∃ a, IsCompl (c U) a :=
    fun U => exists_isCompl (c U) (hc U).1
  choose a haU using ha
  obtain ⟨hU, huniq⟩ := hBr D.host.E (sg D) (sg_sg D) two_ne_zero n c hc a haU
  have hq : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      ∃ γ ∈ GF D n, mat γ = (repMat (sg D) q.2.1 (a q.1)).map (incA D) :=
    fun q => (hRat D n).2.1 _ (hU q.1 q.2.1 q.2.2).1 (hU q.1 q.2.1 q.2.2).2
  choose γ hγGF hγmat using hq
  have hdet : ∀ q : (U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U),
      IsUnit (repMat (sg D) q.2.1 (a q.1)).det := fun q => (hU q.1 q.2.1 q.2.2).1
  let f : ((U : Submodule D.host.E (Fin n → D.host.E)) × HermE D (Module.finrank D.host.E U)) →
      GlobalTheory.Eis.Cosets (P D n) (GF D n) :=
    fun q => mk ((P D n).subgroupOf (GF D n)) ⟨γ q, hγGF q⟩
  have hinj : Function.Injective f := by
    intro q q' hqq
    have h1 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q.2.1 (a q.1))⁻¹) :=
      (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ ⟨γ q', hγGF q'⟩ (hdet q) (hγmat q) (hγmat q')).mp hqq
    have h2 : IsSiegelP (repMat (sg D) q'.2.1 (a q'.1) * (repMat (sg D) q'.2.1 (a q'.1))⁻¹) := by
      rw [Matrix.mul_nonsing_inv _ (hdet q')]
      exact isSiegelParabolic_one _ n
    exact (huniq _ (hdet q') (hU q'.1 q'.2.1 q'.2.2).2).unique h1 h2
  have hsurj : Function.Surjective f := by
    intro z
    obtain ⟨g, hg, hgu, hgm⟩ := (hRat D n).1 _ (Quotient.out z).2
    obtain ⟨q, hqs, -⟩ := huniq g hg hgu
    refine ⟨q, ?_⟩
    rw [← Quotient.out_eq z]
    exact (mk_eq_iff_siegel hRat ⟨γ q, hγGF q⟩ (Quotient.out z) (hdet q) (hγmat q) hgm).mpr hqs
  let e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  have hrle : ∀ U : Submodule D.host.E (Fin n → D.host.E), Module.finrank D.host.E U ≤ n := fun U =>
    (Submodule.finrank_le U).trans_eq (Module.finrank_fin_fun _)
  have hsum : Summable (GlobalTheory.Eis.term (P D n) (GF D n) (fun γ => ((ω γ) Φ).1 0) 1) := Summable.of_norm hconv
  have h3 := (e.hasSum_iff).mpr hsum.hasSum
  unfold GlobalTheory.Eis.cosetSum
  convert h3 using 1
  funext q
  have hrel : (⟨γ q, hγGF q⟩ : GF D n) * (Quotient.out (e q))⁻¹ ∈ (P D n).subgroupOf (GF D n) := by
    have h0 : Quotient.mk _ (Quotient.out (e q)) = Quotient.mk _ (⟨γ q, hγGF q⟩ : GF D n) :=
      Quotient.out_eq (f q)
    exact QuotientGroup.rightRel_apply.mp (Quotient.exact h0)
  rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at hrel
  have hp : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ ∈ (P D n ⊓ GF D n : Subgroup (G D n)) := by
    refine Subgroup.mem_inf.mpr ⟨?_, (GF D n).mul_mem (Quotient.out (e q)).2 ((GF D n).inv_mem (hγGF q))⟩
    have h2 : ((Quotient.out (e q) : GF D n) : G D n) * (γ q)⁻¹ =
        (γ q * ((Quotient.out (e q) : GF D n) : G D n)⁻¹)⁻¹ := by
      rw [mul_inv_rev, inv_inv]
    rw [h2]
    exact (P D n).inv_mem hrel
  have hw' := hPInv D n V ψ χ θ μ ω hS Φ _ hp (γ q)
  simp only [inv_mul_cancel_right] at hw'
  simp only [Function.comp_apply, GlobalTheory.Eis.term, mul_one]
  rw [hw']
  exact (hT2 D n V ψ χ θ μ ω hS Φ _ (hrle q.1) (μr _) (hμr _) (c q.1) (a q.1) (haU q.1) q.2
    (γ q) (hγGF q) (hγmat q)).symm

end GlobalTheory.CompanionTheory.EisCellsAsm

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EisensteinSecondTermFromParts
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisCells

theorem term_of_covariance : PositivityTheory.GramSchwartzFunctions.EC.HeisSch → PositivityTheory.GramSchwartzFunctions.EC.Covar → PositivityTheory.GramSchwartzFunctions.EC.Zero →
    PositivityTheory.GramSchwartzFunctions.EC.Unfold2 → PositivityTheory.GramSchwartzFunctions.EC.ThetaInv → PositivityTheory.GramSchwartzFunctions.EC.Term2 := by
  intro hHeis hCovar hZero hUnf hTheta D n V ψ χ θ μ ω hS Φ r hr μr hμr c a hc b γ hγ hmat
  obtain ⟨-, -, hψ, -, -, hθ, ⟨𝓕, hcov⟩, -⟩ := id hS
  have hinv : mat γ * mat γ⁻¹ = 1 := by
    simp only [mat]
    rw [map_inv]
    simp
  rw [hZero D ψ hψ θ hθ V n μ 𝓕 hcov (ω γ Φ).1 (ω γ Φ).2,
    ← hUnf D ψ hψ θ hθ V n r hr μ 𝓕 hcov μr hμr c a hc b Φ.1 Φ.2]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  simp only [← hmat]
  have hΨ := hHeis D ψ hψ θ hθ V n (HMul.hMul (zy y) (mat γ)) Φ.1 Φ.2
  have h1 := hCovar D n V ψ χ θ μ ω hS γ hγ (HMul.hMul (zy y) (mat γ)) Φ
    ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ rfl
  have h2 := hTheta D n V ψ χ θ μ ω hS ⟨Heisenberg₂ ψ V (HMul.hMul (zy y) (mat γ)) Φ.1, hΨ⟩ γ hγ
  have hv : HMul.hMul (HMul.hMul (zy y) (mat γ)) (mat γ⁻¹) = zy y := by
    rw [Matrix.mul_assoc, hinv, Matrix.mul_one]
  rw [hv] at h1
  rw [h1] at h2
  exact h2

end GlobalTheory.CompanionTheory.EisCells
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRightHaarMeasure
section
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL MeasureTheory PositivityTheory.S2.Clozel

noncomputable section

namespace GlobalTheory.CompanionTheory.AdelicHaar

theorem exists_haar_rightInvariant : ∀ (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ), ∃ μ : Measure (GA E a), μ.IsHaarMeasure ∧ μ.IsMulRightInvariant :=
  fun E _ _ _ a => ⟨Measure.haar, inferInstance, GlobalTheory.CovolGL.isMulRightInvariant E a Measure.haar⟩

end GlobalTheory.CompanionTheory.AdelicHaar
end
end

