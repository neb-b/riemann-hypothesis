module

public import Mathlib
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0001
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0002
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0008
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0004
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.BlockTheory.HeightDefect.Bundle0005
public import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
public import Formalism.LocalRingCardinality.DataDIV
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets
public import Development.AbelianVarietyTheory.Definitions.HeightFunctions.FiniteDimensionalOfSz
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.WeierstrassPTorsionIntegralAndDistinctMod

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.IsKStableOnOfLieStableFiniteDim
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar

theorem flow_mem_map {V H : Type*} [AddCommGroup V] [Module ℂ V] [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (ι : V →ₗ[ℂ] H) (a : V →ₗ[ℂ] V) (W : Submodule ℂ V) [FiniteDimensional ℂ W] (hW : ∀ w ∈ W, a w ∈ W)
    (U : ℝ → H →L[ℂ] H) (h0 : U 0 = 1) (hadd : ∀ s t, U (s + t) = U s * U t)
    (hder : ∀ v, HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) 0) (t : ℝ) :
    ∀ x ∈ W.map ι, U t x ∈ W.map ι := by
  classical
  have hd : ∀ v s, HasDerivAt (fun t : ℝ => U t (ι v)) (U s (ι (a v))) s := by
    intro v s
    have h1 : HasDerivAt (fun t : ℝ => U (t - s) (ι v)) (ι (a v)) s := by
      have := (show HasDerivAt (fun t : ℝ => U t (ι v)) (ι (a v)) (s - s) by
        rw [sub_self]; exact hder v)
      exact this.comp_sub_const s s
    have h2 := ((U s).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s h1
    have h3 : (fun t : ℝ => U t (ι v)) = ((U s).restrictScalars ℝ) ∘ fun t : ℝ => U (t - s) (ι v) := by
      ext r
      have := hadd s (r - s)
      rw [add_sub_cancel] at this
      simp [this]
    rw [h3]
    exact h2
  rintro _ ⟨w, hw, rfl⟩
  rw [← (W.map ι).orthogonal_orthogonal, Submodule.mem_orthogonal]
  intro y hy
  let b := Module.finBasis ℂ W
  let f : ℝ → Fin (Module.finrank ℂ W) → ℂ := fun s i => inner ℂ y (U s (ι (b i)))
  have hf : ∀ s (u : W), inner ℂ y (U s (ι u)) = ∑ j, b.repr u j * f s j := by
    intro s u
    have h3 : (u : V) = ∑ j, b.repr u j • (b j : V) := by
      have := congrArg W.subtype (b.sum_repr u)
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum] at this
      exact this.symm
    rw [h3]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [f, map_sum, map_smul, inner_sum, inner_smul_right]
  let M : Matrix (Fin (Module.finrank ℂ W)) (Fin (Module.finrank ℂ W)) ℂ :=
    fun i j => b.repr ⟨a (b i), hW _ (b i).2⟩ j
  let L := LinearMap.toContinuousLinearMap (Matrix.toLin' M)
  have hfd : ∀ s, HasDerivAt f (L (f s)) s := by
    intro s
    rw [hasDerivAt_pi]
    intro i
    have h2 := ((innerSL ℂ y).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt s (hd (b i) s)
    have := hf s ⟨a (b i), hW _ (b i).2⟩
    have h4 : L (f s) i = ∑ j, b.repr ⟨a (b i), hW _ (b i).2⟩ j * f s j := by
      simp only [L, LinearMap.coe_toContinuousLinearMap', Matrix.toLin'_apply]
      rfl
    rw [h4, ← this]
    exact h2
  have hf0 : f 0 = 0 := by
    ext i
    simp only [f, h0]
    exact Submodule.inner_left_of_mem_orthogonal (K := W.map ι) ⟨b i, (b i).2, rfl⟩ hy
  have hz : f = fun _ => 0 := by
    refine ODE_solution_unique_univ (v := fun _ x => L x) (s := fun _ => Set.univ) (K := ‖L‖₊) (t₀ := 0)
      (fun _ => L.lipschitz.lipschitzOnWith) (fun s => ⟨hfd s, trivial⟩) (fun s => ⟨?_, trivial⟩) hf0
    simpa using hasDerivAt_const s (0 : Fin (Module.finrank ℂ W) → ℂ)
  rw [hf t ⟨w, hw⟩, hz]
  simp

theorem isKStableOn_of_kStable : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ W : Submodule ℂ R.HK.V, FiniteDimensional ℂ W → KStable R.HK.act W → IsKStableOn ε σ (W.map R.ι) := by
  intro p q n e ε T R σ hb hF W hfin hK k hk
  obtain ⟨Y, hY, hexp, -⟩ := Formalism.REAL.compact_exists_log_bounded ε k hk
  obtain ⟨X, rfl⟩ := (Matrix.reindex e e).surjective Y
  have hX : X ∈ upq p q := by
    have h1 := hY.1
    unfold Formalism.REAL.inG at h1
    rw [← hb.reindex_Jm, Matrix.conjTranspose_reindex] at h1
    apply (Matrix.reindex e e).injective
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv] at h1
    simp only [Matrix.reindex_apply]
    rw [Matrix.submatrix_add]
    exact h1
  have hKC : IsKC X := by
    intro a b hab
    rw [hb.sameBlock_iff] at hab
    have h2 := congrFun (congrFun hY.2 (e a)) (e b)
    simp only [Formalism.REAL.Jm, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply] at h2
    cases h3 : ε (e a) <;> cases h4 : ε (e b) <;> rw [h3, h4] at hab h2
    · exact (hab rfl).elim
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (1/2 : ℂ) * h2
    · simp only [if_true, Bool.false_eq_true, if_false] at h2
      linear_combination (-1/2 : ℂ) * h2
    · exact (hab rfl).elim
  have hk' : σ k = R.U.π (T.expt ((1 : ℝ) • X)) := by
    rw [hF, one_smul, T.expt_cov X hX, ← hexp]
    congr 1
    open scoped Matrix.Norms.Operator in
    exact (NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (by
      exact LinearMap.continuous_of_finiteDimensional (Matrix.reindexAlgEquiv ℂ ℂ e).toLinearMap) X).symm
  rw [hk']
  exact flow_mem_map R.ι (R.HK.act X) W (hK X hKC) (fun t => R.U.π (T.expt (t • X)))
    (by simp [T.expt_zero]) (fun s t => by simp only [T.expt_add X hX, map_mul]) (R.der X hX) 1

end GlobalTheory.RealPar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MemHermitianStandardLatticeIffPairingIntegral
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta IsDedekindDomain NumberField
open scoped TensorProduct nonZeroDivisors

namespace GlobalTheory.WeilUnramifiedCompare

section Lattice

variable {E : Type} [Field E] [NumberField E] [StarRing E]

theorem hT_coord (V : HSpace E) (x y : Fin V.rank → E) :
    V.hT (∑ i, x i • V.frame i) (∑ k, y k • V.frame k) = ∑ i, ∑ k, star (x i) * V.gram i k * y k := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum V.hT, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, map_sum, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [map_smul, smul_eq_mul, HSpace.gram, starRingEnd_apply]
  ring

theorem mem_hermitianStandardLattice_iff_pairing_integral (V : HSpace E) (x : V.V) : x ∈ V.L0 ↔ ∀ y ∈ V.L0, ∃ o : 𝓞 E, (o : E) = V.hT y x := by
  have h : Formalism.E.hdual V.hT V.L0 = V.L0 := V.baseLattice_isUnimodular
  conv_lhs => rw [← h]
  simp only [Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap, Submodule.mem_one, LinearMap.restrictScalars_apply]

end Lattice

open GlobalTheory.IndefiniteRowSideFullHecke.ShiftMapsUpDown (offS homInt homLat latFin latFinAA mapUp mapDown locPart gramFin AEf vacSign vacSignOf theta0
  HyperspecialFixesVacuum HomLatSelfDual mapUp_add mapUp_neg mapUp_zero)

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

section Adeles

variable (F : Type) [Field F] [NumberField F] (S : Finset (HeightOneSpectrum (𝓞 F)))



variable {F} in
theorem intAf_mul {a b : Af F} (ha : a ∈ intAf F) (hb : b ∈ intAf F) : a * b ∈ intAf F := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)


end Adeles

variable {X : ThetaX D} {T : ThetaTied D X}

end GlobalTheory.WeilUnramifiedCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.MyTiedNotMeasTupleTied
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta IsDedekindDomain NumberField Formalism.UG.P

namespace GlobalTheory.MeasTupleEq

theorem map_residue_surjective (O : Type) [CommRing O] [IsLocalRing O] (n : ℕ) :
    Function.Surjective (Matrix.GeneralLinearGroup.map (n := Fin n) (IsLocalRing.residue O)) := by
  intro g
  classical
  let M : Matrix (Fin n) (Fin n) O := fun a b =>
    Function.surjInv (IsLocalRing.residue_surjective (R := O)) ((g : Matrix (Fin n) (Fin n) _) a b)
  have hM : M.map (IsLocalRing.residue O) = (g : Matrix (Fin n) (Fin n) _) := by
    ext a b
    simp only [M]
    exact Function.surjInv_eq _ _
  have hdet : IsUnit M.det := by
    have h1 : IsUnit (IsLocalRing.residue O M.det) := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply, hM]
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using (Matrix.GeneralLinearGroup.det g).isUnit
    exact (isUnit_map_iff (IsLocalRing.residue O) _).1 h1
  refine ⟨Matrix.GeneralLinearGroup.mk'' M hdet, Units.ext ?_⟩
  exact hM

variable {D : D7} {X : ThetaX D}

end GlobalTheory.MeasTupleEq

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorsionIntegralDistinctOfPos
section
open NumberField IsDedekindDomain Polynomial GlobalTheory.FieldSize
open scoped IntermediateField

namespace GlobalTheory.TorsionIntegralPos
open GlobalTheory.TorsionIntegral


open IsLocalRing in
theorem torsion_integral_distinct_of_pos : ∀ (L : PeriodPair) (W : ValuationSubring ℂ) (m : ℕ),
    (2 : ℂ)⁻¹ ∈ W → (3 : ℂ)⁻¹ ∈ W → L.g₂ ∈ W → L.g₃ ∈ W → (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)⁻¹ ∈ W →
    0 < m → (m : ℂ)⁻¹ ∈ W →
    (∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W) ∧
    ∀ t t', (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → (m : ℂ) * t' ∈ L.lattice →
      t' ∉ L.lattice → L.weierstrassP t - L.weierstrassP t' ∈ W.nonunits →
      t - t' ∈ L.lattice ∨ t + t' ∈ L.lattice := by
  intro L W m h2 _ hg2 hg3 hΔ hpos hm
  have hI : ∀ t, (m : ℂ) * t ∈ L.lattice → t ∉ L.lattice → L.weierstrassP t ∈ W :=
    fun t a b => integral L W m h2 hg2 hg3 hpos.ne' hm a b
  refine ⟨hI, fun t t' a b a' b' hn => ?_⟩
  by_contra hc
  have hne : L.weierstrassP t ≠ L.weierstrassP t' := mt (GlobalTheory.weierstrassP_eq_iff L b b').1 hc
  rw [not_or] at hc
  obtain ⟨hs, hp⟩ := sum_prod L b b' hne
  let x1 : W := ⟨_, hI t a b⟩
  let x2 : W := ⟨_, hI t' a' b'⟩
  let x3 : W := ⟨_, hI (t + t') (by rw [mul_add]; exact add_mem a a') hc.2⟩
  let x4 : W := ⟨_, hI (t - t') (by rw [mul_sub]; exact sub_mem a a') hc.1⟩
  let g2 : W := ⟨L.g₂, hg2⟩
  let g3 : W := ⟨L.g₃, hg3⟩
  let h : W := ⟨2⁻¹, h2⟩
  let e : W := ⟨_, hΔ⟩
  have c2 : ((2 : W) : ℂ) = 2 := rfl
  have c27 : ((27 : W) : ℂ) = 27 := rfl
  have e1 : (x3 + x4) * (x1 - x2) ^ 2 = 2 * x1 * x2 * (x1 + x2) - g2 * h * (x1 + x2) - g3 := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h, c2]
    linear_combination hs
  have e2 : x3 * x4 * (x1 - x2) ^ 2 = (x1 * x2 + g2 * h ^ 2) ^ 2 + g3 * (x1 + x2) := by
    apply Subtype.ext
    simp [x1, x2, x3, x4, g2, g3, h]
    linear_combination hp
  have e3 : 2 * h = 1 := by
    apply Subtype.ext
    simp [h, c2]
  have e4 : (g2 ^ 3 - 27 * g3 ^ 2) * e = 1 := by
    apply Subtype.ext
    simp [g2, g3, e, c27, disc L]
  have e5 : residue W (x1 - x2) = 0 :=
    (residue_eq_zero_iff _).2 (ValuationSubring.coe_mem_nonunits_iff.1 hn)
  have f1 := congrArg (residue W) e1
  have f2 := congrArg (residue W) e2
  have f3 := congrArg (residue W) e3
  have f4 := congrArg (residue W) e4
  simp only [map_mul, map_add (f := _), map_sub, map_pow, map_ofNat, map_one] at f1 f2 f3 f4 e5
  rw [sub_eq_zero] at e5
  rw [← e5] at f1 f2
  generalize residue W x1 = x at *
  generalize residue W g2 = A at *
  generalize residue W g3 = B at *
  generalize residue W h = u at *
  have k1 : 4 * x ^ 3 - A * x - B = 0 := by linear_combination (A * x) * f3 - f1
  have k2 : (4 * x ^ 2 + A) ^ 2 + 32 * B * x = 0 := by
    have hA : 4 * (x * x + A * u ^ 2) = 4 * x ^ 2 + A := by
      linear_combination A * (2 * u + 1) * f3
    rw [← hA]; linear_combination -16 * f2
  have k3 : A ^ 3 - 27 * B ^ 2 = 0 := by
    linear_combination (A - 3 * x ^ 2) * k2 + (12 * x ^ 3 + 5 * A * x + 27 * B) * k1
  rw [k3, zero_mul] at f4
  exact zero_ne_one f4

end GlobalTheory.TorsionIntegralPos
end

-- bundled from Development.AbelianVarietyTheory.Proofs.HeightProofs.TorusWeightVectorIffCartanWeightVector
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.RealPar Matrix MeasureTheory
open scoped TensorProduct

namespace GlobalTheory.RealPar.TorusWt

variable {p q n : ℕ}

def torX (θ : Ix p q → ℝ) : Mat p q := Matrix.diagonal fun a => (θ a : ℂ) * Complex.I

theorem torX_mem (θ : Ix p q → ℝ) : torX θ ∈ upq p q := by
  change _ = _
  ext a b
  have hJ : TH.Jm p q = Matrix.diagonal (Sum.elim (fun _ => 1) (fun _ => -1)) := by
    ext a b
    rcases a with a | a <;> rcases b with b | b <;>
      simp [TH.Jm, Formalism.UG.Jpq, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp
  rw [hJ, torX, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_add]
  by_cases h : a = b
  · subst h; simp; ring
  · simp [h]

theorem smul_torX (t : ℝ) (θ : Ix p q → ℝ) : t • torX θ = torX fun a => t * θ a := by
  ext a b
  by_cases h : a = b
  · subst h; simp [torX, mul_assoc]
  · simp [torX, h]

theorem torX_eq_sum (θ : Ix p q → ℝ) : torX θ = ∑ a, ((θ a : ℂ) * Complex.I) • Eab a a := by
  ext a b
  simp only [torX, Eab, Matrix.sum_apply, Matrix.smul_apply, Matrix.single_apply, Matrix.diagonal_apply]
  rw [Finset.sum_eq_single a]
  · simp
  · intro c _ hc; simp [hc]
  · simp

theorem reindex_cov_expt (T : GrpData p q) (e : Ix p q ≃ Fin n) (θ : Fin n → ℝ) :
    Matrix.reindex e e ((T.cov (T.expt (torX fun a => θ (e a))) : GL (Ix p q) ℂ) : Mat p q) =
      Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I) := by
  rw [T.expt_cov _ (torX_mem _), torX, Matrix.exp_diagonal]
  ext i j
  obtain ⟨a, rfl⟩ := e.surjective i
  obtain ⟨b, rfl⟩ := e.surjective j
  simp [Matrix.diagonal_apply, Pi.coe_exp, Complex.exp_eq_exp_ℂ]

theorem diag_mem_Kset (ε : Fin n → Bool) (θ : Fin n → ℝ) :
    (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Formalism.REAL.Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp [← Complex.exp_conj, ← Complex.exp_add]
  · rw [Formalism.REAL.Jm, Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    ring

theorem flow_eq {T : GrpData p q} (R : DSRep T) {X : Mat p q} (hX : X ∈ upq p q) {v : R.HK.V} {c : ℂ}
    (hv : R.HK.act X v = c • v) : R.U.π (T.expt X) (R.ι v) = Complex.exp c • R.ι v := by
  set f : ℝ → R.U.H := fun t => R.U.π (T.expt (t • X)) (R.ι v) with hf
  have hd : ∀ t, HasDerivAt f (c • f t) t := by
    intro t
    have h0 := R.der X hX v
    rw [hv, map_smul] at h0
    have h1 : HasDerivAt (fun s : ℝ => f (s - t)) (c • R.ι v) t := by
      have := HasDerivAt.comp_sub_const t t (f := f) (f' := c • R.ι v) (by rw [sub_self]; exact h0)
      exact this
    have h2 := ((R.U.π (T.expt (t • X))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
    convert (preTransparency := .reducible) h2 using 1
    · funext s
      simp only [hf, Function.comp, ContinuousLinearMap.coe_restrictScalars']
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, ← T.expt_add X hX, add_sub_cancel]
    · simp [hf]
  have hg : ∀ t : ℝ, HasDerivAt (fun t : ℝ => Complex.exp (-(c * t)) • f t) 0 t := by
    intro t
    have h1 : HasDerivAt (fun t : ℝ => Complex.exp (-(c * t))) (Complex.exp (-(c * t)) * (-c)) t := by
      have : HasDerivAt (fun t : ℝ => -(c * (t : ℂ))) (-c) t := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := t)).const_mul c).fun_neg
      exact this.cexp
    convert h1.fun_smul (hd t) using 1
    rw [smul_smul, ← add_smul]; simp
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [hf, one_smul, zero_smul, T.expt_zero, map_one, Complex.ofReal_one, mul_one, Complex.ofReal_zero, mul_zero,
    neg_zero, Complex.exp_zero, ContinuousLinearMap.one_apply] at hc
  conv_rhs => rw [← hc, smul_smul, ← Complex.exp_add]
  simp

theorem isWtOn_iff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (μ : Fin n → ℝ) (v : R.HK.V), IsWtOn (Formalism.REAL.Kset ε) σ μ (R.ι v) ↔ ∀ a, R.HK.act (Eab a a) v = ((μ (e a) : ℝ) : ℂ) • v := by
  intro p q n e ε T R σ _ hF μ v
  have key : ∀ θ : Fin n → ℝ, R.U.π (T.expt (torX fun a => θ (e a))) =
      σ (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)) := fun θ => by
    rw [hF, reindex_cov_expt]
  constructor
  · intro h a
    set θ : Fin n → ℝ := Pi.single (e a) 1 with hθ
    have h0 := R.der _ (torX_mem fun b => θ (e b)) v
    have h1 : (fun t : ℝ => R.U.π (T.expt (t • torX fun b => θ (e b))) (R.ι v)) =
        fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v := by
      funext t
      rw [smul_torX, key fun b => t * θ b, h _ (diag_mem_Kset ε _)]
      congr 2
      rw [Finset.sum_eq_single (e a)]
      · simp [hθ]; ring
      · intro c _ hc; simp [hθ, hc]
      · simp
    have h2 : HasDerivAt (fun t : ℝ => Complex.exp ((μ (e a) * Complex.I) * t) • R.ι v)
        ((μ (e a) * Complex.I) • R.ι v) 0 := by
      have : HasDerivAt (fun t : ℝ => ((μ (e a) * Complex.I) * (t : ℂ))) (μ (e a) * Complex.I) 0 := by
        simpa using ((Complex.ofRealCLM.hasDerivAt (x := 0)).const_mul (μ (e a) * Complex.I))
      simpa using this.cexp.smul_const (R.ι v)
    rw [h1] at h0
    have h3 := h0.unique h2
    rw [← map_smul] at h3
    have h4 := R.ι_inj h3
    have h5 : (torX fun b => θ (e b)) = Complex.I • Eab a a := by
      rw [torX_eq_sum, Finset.sum_eq_single a]
      · simp [hθ]
      · intro c _ hc; simp [hθ, hc]
      · simp
    rw [h5, map_smul, LinearMap.smul_apply, mul_comm, mul_smul] at h4
    exact smul_right_injective _ Complex.I_ne_zero h4
  · intro h θ _
    rw [← key]
    apply flow_eq R (torX_mem _)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [torX_eq_sum, map_sum, LinearMap.sum_apply]
    simp only [map_smul, LinearMap.smul_apply, h, smul_smul, ← Finset.sum_smul]
    congr 1
    rw [← e.sum_comp]
    push_cast
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun a _ => by ring

end GlobalTheory.RealPar.TorusWt

end
end

