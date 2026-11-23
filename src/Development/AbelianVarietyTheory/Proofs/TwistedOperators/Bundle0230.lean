module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0205
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SatakeParameterOfSpherical
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0303
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsDualFamilyOfIsLattice
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0214
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PowDvdOfHermMatEq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0152
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0204
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0132
public import Development.AutomorphicArithmetic.CyclotomicBounds.RamifiedDiscriminants.CondSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0136
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0134
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeanXMulStarRat
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory NumberField Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.IsoMean

def cplx {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (z : Mx D 1 k) :
    WO V W :=
  ∑ i, z 0 i • (B i).map (incA D)

section

variable {D : D7} (V W : HSp D) {k : ℕ} (B : Fin k → Matrix (Fin W.rank) (Fin V.rank) D.host.E)

theorem cplx_add (z z' : Mx D 1 k) : cplx V W B (z + z') = cplx V W B z + cplx V W B z' := by
  simp only [cplx, Matrix.add_apply, add_smul, Finset.sum_add_distrib]

theorem cplx_zero : cplx V W B 0 = 0 := by
  simp [cplx]

theorem continuous_cplx : Continuous (cplx V W B) := by
  unfold cplx
  refine continuous_finsetSum _ fun i _ => ?_
  exact (continuous_id.matrix_elem 0 i).smul continuous_const

theorem cplx_rat (c : Matrix (Fin 1) (Fin k) D.host.E) :
    cplx V W B (c.map (incA D)) = (∑ i, c 0 i • B i).map (incA D) := by
  ext p q
  set_option synthInstance.maxHeartbeats 100000 in
    simp [cplx, Matrix.sum_apply, map_sum, smul_eq_mul]

end

theorem symplO_eq_add {D : D7} (S T : HSp D) (x y : WO S T) : symplO S T x y = symplOH S T x y + symplOH S T x y := by
  have h2 : algebraMap D.host.F (AF D.host.F) (1 / 2) * 2 = 1 := by
    rw [← map_ofNat (algebraMap D.host.F (AF D.host.F)) 2, ← map_mul]
    norm_num
  unfold symplOH
  linear_combination (-symplO S T x y) * h2

theorem meanX_heisO_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (F : WO V W → ℂ) (hF : IsThetaFunO ψ V W F) (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) (hx : ∀ y, symplO V W x (emb V W P Q y) = 0) :
    meanX V W P Q μ 𝓨 (heisO ψ V W w F) x = ψ (symplO V W x w) * meanX V W P Q μ 𝓨 F x := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  have skew : ∀ x y, symplOH V W y x = -symplOH V W x y := fun x y => by
    have e := l3 (x + y)
    rw [l1, l2, l2, l3 x, l3 y] at e
    linear_combination e
  obtain ⟨γ, rfl⟩ := hw
  unfold meanX
  rw [← integral_const_mul]
  congr 1
  funext y
  have hq := hF.quasi γ (emb V W P Q y + x)
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  simp only [heisO]
  rw [er] at hwX ⊢
  rw [show emb V W P Q y + x + ratW W V γ = ratW W V γ + (emb V W P Q y + x) by abel, hq, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  rw [l1, l2, skew (ratW W V γ) (emb V W P Q y), hH0 _ _ (hwX y), skew (ratW W V γ) x, symplO_eq_add, skew (ratW W V γ) x]
  ring

theorem meanX_mul_star_rat {D : D7} (V W : HSp D) {a b : ℕ} (P : Matrix (Fin W.rank) (Fin a) D.host.E)
    (Q : Matrix (Fin b) (Fin V.rank) D.host.E) (μ : Measure (Mx D a b)) (𝓨 : Set (Mx D a b))
    (ψ : AddChar (AF D.host.F) ℂ) (hψ : IsStdChar D ψ (-1)) (F F' : WO V W → ℂ) (hF : IsThetaFunO ψ V W F)
    (hF' : IsThetaFunO ψ V W F') (w : WO V W) (hw : w ∈ ratL W V)
    (hwX : ∀ y, symplO V W w (emb V W P Q y) = 0) (x : WO V W) :
    meanX V W P Q μ 𝓨 F (w + x) * star (meanX V W P Q μ 𝓨 F' (w + x)) =
      meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x) := by
  obtain ⟨l1, l2, l3, -, -⟩ := GlobalTheory.OrientedFormLaws.symplOH_laws D V W
  have hH0 : ∀ x y, symplO V W x y = 0 → symplOH V W x y = 0 := fun x y e => by
    unfold symplOH; rw [e, mul_zero]
  obtain ⟨γ, rfl⟩ := hw
  have er : (((incA D).toAddMonoidHom.mapMatrix (m := Fin W.rank) (n := Fin V.rank)) γ) = ratW W V γ := rfl
  rw [er] at hwX ⊢
  have key : ∀ G : WO V W → ℂ, IsThetaFunO ψ V W G →
      meanX V W P Q μ 𝓨 G (ratW W V γ + x) = ψ (-(symplOH V W (ratW W V γ) x)) * meanX V W P Q μ 𝓨 G x := by
    intro G hG
    unfold meanX
    rw [← integral_const_mul]
    congr 1
    funext y
    rw [show emb V W P Q y + (ratW W V γ + x) = ratW W V γ + (emb V W P Q y + x) by abel, hG.quasi, l2,
      hH0 _ _ (hwX y), zero_add]
  rw [key F hF, key F' hF', star_mul]
  have hn : ψ (-(symplOH V W (ratW W V γ) x)) * star (ψ (-(symplOH V W (ratW W V γ) x))) = 1 := by
    have h1 := hψ.1.2.1 (-(symplOH V W (ratW W V γ) x))
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, h1]
    norm_num
  linear_combination (meanX V W P Q μ 𝓨 F x * star (meanX V W P Q μ 𝓨 F' x)) * hn

end GlobalTheory.IsoMean

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSmoothVectorsDiscreteSeriesModelIff
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SmVecModel

section Conj

variable {n : ℕ} {J P G : Matrix (Fin n) (Fin n) ℂ}

theorem conj_cancel (hP : IsUnit P) (g : Matrix (Fin n) (Fin n) ℂ) : P * (P⁻¹ * g * P) * P⁻¹ = g := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc P * (P⁻¹ * g * P) * P⁻¹ = (P * P⁻¹) * g * (P * P⁻¹) := by simp only [Matrix.mul_assoc]
    _ = g := by rw [h1]; simp

theorem lie_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * G + G * X = 0) :
    (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P * X * P⁻¹)ᴴ * J + J * (P * X * P⁻¹)
      = (P * X * P⁻¹)ᴴ * J * (P * P⁻¹) + (P * P⁻¹)ᴴ * J * (P * X * P⁻¹) := by rw [h1]; simp
    _ = (P⁻¹)ᴴ * (Xᴴ * G + G * X) * P⁻¹ := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [hX]; simp

theorem lie_conj_inv (hP : IsUnit P) (hG : Pᴴ * J * P = G) {X : Matrix (Fin n) (Fin n) ℂ} (hX : Xᴴ * J + J * X = 0) :
    (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P) = 0 := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  calc (P⁻¹ * X * P)ᴴ * G + G * (P⁻¹ * X * P)
      = Pᴴ * (Xᴴ * ((P * P⁻¹)ᴴ * J) + J * (P * P⁻¹) * X) * P := by
        rw [← hG]; simp only [conjTranspose_mul, Matrix.mul_assoc, Matrix.mul_add, Matrix.add_mul]
    _ = 0 := by rw [h1, conjTranspose_one, Matrix.one_mul, Matrix.mul_one, hX]; simp

theorem exp_smul_conj (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P * X * P⁻¹)) = P * NormedSpace.exp (t • X) * P⁻¹ := by
  rw [← Matrix.exp_conj _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem exp_smul_conj_inv (hP : IsUnit P) (X : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) :
    NormedSpace.exp (t • (P⁻¹ * X * P)) = P⁻¹ * NormedSpace.exp (t • X) * P := by
  rw [← Matrix.exp_conj' _ _ hP, Matrix.mul_smul, Matrix.smul_mul]

theorem prod_conj_inv (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P⁻¹ * g * P).prod = P⁻¹ * l.prod * P := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h2]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P⁻¹ * a * P * (P⁻¹ * l.prod * P) = P⁻¹ * a * (P * P⁻¹) * l.prod * P := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]

theorem prod_conj (hP : IsUnit P) (l : List (Matrix (Fin n) (Fin n) ℂ)) :
    (l.map fun g => P * g * P⁻¹).prod = P * l.prod * P⁻¹ := by
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)
  induction l with
  | nil => simp [h1]
  | cons a l ih =>
    rw [List.map_cons, List.prod_cons, List.prod_cons, ih]
    calc P * a * P⁻¹ * (P * l.prod * P⁻¹) = P * a * (P⁻¹ * P) * l.prod * P⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by
        rw [Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 hP)]
        simp only [Matrix.mul_assoc, Matrix.one_mul]

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}

theorem smoothVec_of_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w) :
    SmoothVec {X | Xᴴ * J + J * X = 0} σ w := by
  intro k Xs hXs
  have h := hw k (fun i => P⁻¹ * Xs i * P) fun i => lie_conj_inv hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, P * (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))).prod * P⁻¹ =
      (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P⁻¹ * Xs i * P))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P⁻¹ * g * P := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj_inv hP _ _
    rw [this, prod_conj_inv hP, conj_cancel hP]
  simpa only [e] using h

theorem smoothVec_to_conj (hP : IsUnit P) (hG : Pᴴ * J * P = G) {w : H}
    (hw : SmoothVec {X | Xᴴ * J + J * X = 0} σ w) :
    SmoothVec {X | Xᴴ * G + G * X = 0} (fun g => σ (P * g * P⁻¹)) w := by
  intro k Xs hXs
  have h := hw k (fun i => P * Xs i * P⁻¹) fun i => lie_conj hP hG (hXs i)
  have e : ∀ t : Fin k → ℝ, (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))).prod =
      P * (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).prod * P⁻¹ := by
    intro t
    have : (List.ofFn fun i => NormedSpace.exp (t i • (P * Xs i * P⁻¹))) =
        (List.ofFn fun i => NormedSpace.exp (t i • Xs i)).map fun g => P * g * P⁻¹ := by
      rw [List.map_ofFn]
      congr 1
      funext i
      exact exp_smul_conj hP _ _
    rw [this, prod_conj hP]
  simpa only [e] using h

end Conj

theorem mem_sm_iff : ∀ {D : D7} {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) (τ : D.what₂.Tau) (w : M.H τ),
    w ∈ M.sm τ ↔ SmoothVec (GlobalTheory.SmoothGlob.lieSet (M.ε τ)) (M.σ τ) w := by
  intro D V S M τ w
  rw [GlobalTheory.SmVec.sm_eq M τ, GlobalTheory.SmVec.mem_smSub]
  constructor
  · intro h
    exact smoothVec_of_conj (M.fr_unit τ) (M.fr_gram τ) h
  · intro h
    exact smoothVec_to_conj (M.fr_unit τ) (M.fr_gram τ) h

end GlobalTheory.SmVecModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.NoExcludedParameterOfLiftParameters
section
open MeasureTheory NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR.Links
open GlobalTheory.IndefiniteRowSideFullHecke.IteratedLiftChains GlobalTheory.PRep GlobalTheory.LFun
open Formalism.UG (IsCommensurated Hecke)
open Formalism.MainNotions.SchurIrreducible (IsSplit)

noncomputable section

namespace GlobalTheory.NoExcl

open Formalism.MainNotions.StandardLattice Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.IndefR.Lift GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem isHermND_gram (V : HSp D) : IsHermND D.sp.cm.sig V.gram :=
  (GlobalTheory.Mem.Vol.cmData_isCMExt_and_gram_isHermND _ _ D.sp.cm).2 V

theorem chart (V : HSp D) {v : HeightOneSpectrum (𝓞 D.host.F)} {w : HeightOneSpectrum (𝓞 D.host.E)}
    (h : w.under (𝓞 D.host.F) = v) (hv : IsSplit (E := D.host.E) v) :
    (∃ e, IsSplitChart D.sp.cm.sig V.gram (frameLat V) h e) ∧ Ideal.absNorm w.asIdeal = Formalism.UG.qV D.host.F v := by
  have hspan : Submodule.span D.host.E (frameLat V : Set (Fin V.rank → D.host.E)) = ⊤ := by
    have hfull : Submodule.span D.host.E (V.L0 : Set V.V) = ⊤ := by
      let W := Submodule.span D.host.E (V.L0 : Set V.V)
      change W = ⊤
      by_contra h
      let e : V.V ≃ₗ⋆[D.host.E] V.V :=
        (V.frame.equivFun.trans (starLinearEquiv D.host.E)).trans V.frame.equivFun.symm
      let g : V.V →ₗ[D.host.E] Module.Dual D.host.E W :=
        (LinearMap.domRestrict' W).comp (V.hT.comp e.toLinearMap)
      have hdim : Module.finrank D.host.E (Module.Dual D.host.E W) < Module.finrank D.host.E V.V := by
        rw [Subspace.dual_finrank_eq]
        exact Submodule.finrank_lt h
      obtain ⟨x, hx, hx₀⟩ :=
        Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
      have hsmul (a : D.host.E) : a • e x ∈ V.L0 := by
        rw [← V.baseLattice_isUnimodular]
        rw [Formalism.HermitianLatticesTheory.dualBasic_mem_dual]
        intro y hy
        have hxy : V.hT (e x) y = 0 :=
          congrArg (fun f : Module.Dual D.host.E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
        have hyx : V.hT y (e x) = 0 := by
          rw [(V.herm.eq (e x) y).symm, hxy, map_zero]
        simp [hyx]
      let i : D.host.E →ₗ[𝓞 D.host.E] V.L0 :=
        ((LinearMap.toSpanSingleton D.host.E _ (e x)).restrictScalars (𝓞 D.host.E)).codRestrict V.L0 hsmul
      let : Module.Finite (𝓞 D.host.E) V.L0 := Module.Finite.iff_fg.mpr V.standardTuple_isLattice.fg
      let : Module.Finite (𝓞 D.host.E) D.host.E := Module.Finite.of_injective i fun a b hab =>
        smul_left_injective D.host.E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
      exact RingOfIntegers.not_isField D.host.E
        (isField_of_isIntegral_of_isField (R := 𝓞 D.host.E) (S := D.host.E)
          (FaithfulSMul.algebraMap_injective _ _) (Field.toIsField _))
    have heq : (frameLat V : Set (Fin V.rank → D.host.E)) =
        V.frame.equivFun.toLinearMap '' (V.L0 : Set V.V) :=
      (V.frame.equivFun.toEquiv.image_eq_preimage_symm _).symm
    rw [heq, ← Submodule.map_span, hfull, Submodule.map_top, LinearEquiv.range]
  obtain ⟨⟨e, he, -⟩, w', -, -, h1, -⟩ := SplitChart.split_chart_and_places (isCMExt_host D) (isHermND_gram V)
    (frameLat_fg V) hspan h hv (SelfDual.isSelfDualAt_frameLat D V v)
  exact ⟨⟨e, he⟩, h1⟩

section Param

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant] {W : Submodule ℂ (DividedPowerChartLift V ν)}

end Param

section Chars

open Formalism.L2.Host

variable {T : Type} {L : LevCh D T} {t₀ : T}

end Chars

section Zero

variable {V : HSp D} {ν : Measure (GA D V)} [ν.IsHaarMeasure] [ν.IsMulRightInvariant]
  {σ π : Submodule ℂ (DividedPowerChartLift V ν)}

end Zero

end GlobalTheory.NoExcl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.RationalFrameStabiliserNormalisesUnipotentRadica
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.AdjointIsotropicDecomposition
open scoped ENNReal
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.FrameStab

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem incA_injective (D : D7) : Function.Injective (incA D) :=
  Algebra.TensorProduct.includeRight_injective (NumberField.AdeleRing.algebraMap_injective (𝓞 D.host.F) D.host.F)

theorem mt_mul (W : HSp D) (g h : GA D W) : Formalism.L2.Theta.mt W (g * h) = Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W h := by
  simp [Formalism.L2.Theta.mt]

theorem mt_inv_mul (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g⁻¹ * Formalism.L2.Theta.mt W g = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_inv (W : HSp D) (g : GA D W) : Formalism.L2.Theta.mt W g * Formalism.L2.Theta.mt W g⁻¹ = 1 := by
  rw [← mt_mul]; simp [Formalism.L2.Theta.mt]

theorem mt_mul_frame (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (n : GA D W) (hn : n ∈ NI W L) :
    Formalism.L2.Theta.mt W n * L.map (incA D) = L.map (incA D) := by
  induction hn using Subgroup.closure_induction with
  | mem g hg =>
    have h1 : (Formalism.L2.Theta.mt W g - 1) * L.map (incA D) = 0 := hg.1
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h1
    exact h1
  | one => simp [Formalism.L2.Theta.mt]
  | mul x y _ _ hx hy => rw [mt_mul, Matrix.mul_assoc, hy, hx]
  | inv x _ hx =>
    calc Formalism.L2.Theta.mt W x⁻¹ * L.map (incA D)
        = Formalism.L2.Theta.mt W x⁻¹ * (Formalism.L2.Theta.mt W x * L.map (incA D)) := by rw [hx]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]

theorem mt_conj_sub_one (W : HSp D) (γ m : GA D W) : Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1 =
    Formalism.L2.Theta.mt W γ * (Formalism.L2.Theta.mt W m - 1) * Formalism.L2.Theta.mt W γ⁻¹ := by
  rw [mt_mul, mt_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, mt_mul_inv]

theorem conj_sub_one_kills_frame_of_fixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (γ m : GA D W)
    (hΓiL : Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D) = L.map (incA D))
    (h1 : (Formalism.L2.Theta.mt W m - 1) * L.map (incA D) = 0) :
    (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) * L.map (incA D) = 0 := by
  rw [mt_conj_sub_one, Matrix.mul_assoc, hΓiL, Matrix.mul_assoc, h1, Matrix.mul_zero]

theorem rowFrame_mul_conj_sub_one_eq_zero_of_fixed (W : HSp D) {s : ℕ} (P : Matrix (Fin s) (Fin W.rank) D.host.E) (γ m : GA D W)
    (hPΓ : P.map (incA D) * Formalism.L2.Theta.mt W γ = P.map (incA D))
    (h2 : P.map (incA D) * (Formalism.L2.Theta.mt W m - 1) = 0) :
    P.map (incA D) * (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) = 0 := by
  rw [mt_conj_sub_one, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hPΓ, h2, Matrix.zero_mul]

theorem conj_unipotentRadical_kernelCondition_of_rationalFixed (W : HSp D) {s : ℕ} (L : Matrix (Fin W.rank) (Fin s) D.host.E) (P : Matrix (Fin s) (Fin W.rank) D.host.E)
    (γ m : GA D W) (γ₀ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hγ₀ : Formalism.L2.Theta.mt W γ = γ₀.map (incA D)) (hγγi : γ₀ * γi = 1) (hPγi : P * γi = P)
    (hΓL : Formalism.L2.Theta.mt W γ * L.map (incA D) = L.map (incA D))
    (h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a)
    (x : Fin W.rank → D.host.E) (hx : P *ᵥ x = 0) : ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W (γ * m * γ⁻¹) - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
  have hy : P *ᵥ (γi *ᵥ x) = 0 := by
    rw [Matrix.mulVec_mulVec, hPγi]; exact hx
  obtain ⟨a, ha⟩ := h3 _ hy
  refine ⟨a, ?_⟩
  have hyb : (fun i => incA D ((γi *ᵥ x) i)) = γi.map (incA D) *ᵥ (fun i => incA D (x i)) := by
    funext i; exact RingHom.map_mulVec (incA D) γi x i
  have hxb : Formalism.L2.Theta.mt W γ *ᵥ (fun i => incA D ((γi *ᵥ x) i)) = fun i => incA D (x i) := by
    rw [hyb, Matrix.mulVec_mulVec, hγ₀, ← Matrix.map_mul, hγγi, Matrix.map_one _ (map_zero _) (map_one _),
      Matrix.one_mulVec]
  have hxi : Formalism.L2.Theta.mt W γ⁻¹ *ᵥ (fun i => incA D (x i)) = fun i => incA D ((γi *ᵥ x) i) := by
    rw [← hxb, Matrix.mulVec_mulVec, mt_inv_mul, Matrix.one_mulVec]
  rw [mt_conj_sub_one, ← Matrix.mulVec_mulVec, hxi, ← Matrix.mulVec_mulVec, ha, Matrix.mulVec_mulVec, hΓL]

theorem stab : ∀ (D : D7) (W : HSp D) (s : ℕ) (L : Matrix (Fin W.rank) (Fin s) D.host.E), IsIsoFrame W L →
    (∀ γ ∈ GQ W, ∀ γ₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W γ = γ₀.map (incA D) →
      γ₀ * L = L → ∀ n ∈ NI W L, γ * n * γ⁻¹ ∈ NI W L) ∧
    (∀ n ∈ NI W L, ∀ n₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E, Formalism.L2.Theta.mt W n = n₀.map (incA D) →
      n₀ * L = L) := by
  intro D W s L _
  refine ⟨?_, fun n hn n₀ hn₀ => ?_⟩
  swap
  · apply Matrix.map_injective (incA_injective D)
    show (n₀ * L).map (incA D) = L.map (incA D)
    rw [Matrix.map_mul, ← hn₀]
    exact mt_mul_frame W L n hn
  intro γ hγ γ₀ hγ₀ hL
  obtain ⟨g, hg, e⟩ := hγ
  have hg0 : (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E) = γ₀ := by
    apply Matrix.map_injective (incA_injective D)
    show (g : Matrix (Fin W.rank) (Fin W.rank) D.host.E).map (incA D) = γ₀.map (incA D)
    rw [← hγ₀]
    exact congrArg Units.val e

  obtain ⟨σ, hσ⟩ : ∃ σ : D.host.E →+* D.host.E, σ = (D.sp.cm.sig : D.host.E →+* D.host.E) := ⟨_, rfl⟩
  obtain ⟨G, hG⟩ : ∃ G, G = W.gram := ⟨_, rfl⟩
  obtain ⟨P, hP⟩ : ∃ P : Matrix (Fin s) (Fin W.rank) D.host.E, P = Formalism.UG.cT σ L * G := ⟨_, rfl⟩
  obtain ⟨γi, hγi⟩ : ∃ γi : Matrix (Fin W.rank) (Fin W.rank) D.host.E, γi = (g⁻¹ : GL (Fin W.rank) D.host.E).1 :=
    ⟨_, rfl⟩
  have hγγi : γ₀ * γi = 1 := by rw [← hg0, hγi]; exact Units.mul_inv g
  have hU : Formalism.UG.cT σ γ₀ * G * γ₀ = G := by rw [← hg0, hσ, hG]; exact hg
  have hPγ : P * γ₀ = P := by
    calc P * γ₀ = Formalism.UG.cT σ (γ₀ * L) * G * γ₀ := by rw [hL, hP]
      _ = Formalism.UG.cT σ L * (Formalism.UG.cT σ γ₀ * G * γ₀) := by
        rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
      _ = P := by rw [hU, hP]
  have hPγi : P * γi = P := by
    calc P * γi = P * γ₀ * γi := by rw [hPγ]
      _ = P := by rw [Matrix.mul_assoc, hγγi, Matrix.mul_one]

  have hΓL : Formalism.L2.Theta.mt W γ * L.map (incA D) = L.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hL]
  have hΓiL : Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D) = L.map (incA D) := by
    calc Formalism.L2.Theta.mt W γ⁻¹ * L.map (incA D)
        = Formalism.L2.Theta.mt W γ⁻¹ * (Formalism.L2.Theta.mt W γ * L.map (incA D)) := by rw [hΓL]
      _ = L.map (incA D) := by rw [← Matrix.mul_assoc, mt_inv_mul, Matrix.one_mul]
  have hPΓ : P.map (incA D) * Formalism.L2.Theta.mt W γ = P.map (incA D) := by
    rw [hγ₀, ← Matrix.map_mul, hPγ]
  have hPΓi : P.map (incA D) * Formalism.L2.Theta.mt W γ⁻¹ = P.map (incA D) := by
    calc P.map (incA D) * Formalism.L2.Theta.mt W γ⁻¹
        = P.map (incA D) * Formalism.L2.Theta.mt W γ * Formalism.L2.Theta.mt W γ⁻¹ := by rw [hPΓ]
      _ = P.map (incA D) := by rw [Matrix.mul_assoc, mt_mul_inv, Matrix.mul_one]

  have key : NI W L ≤ (NI W L).comap (MulAut.conj γ).toMonoidHom := by
    refine (Subgroup.closure_le _).2 fun m hm => ?_
    have h1 : (Formalism.L2.Theta.mt W m - 1) * L.map (incA D) = 0 := hm.1
    have h2 : P.map (incA D) * (Formalism.L2.Theta.mt W m - 1) = 0 := by
      have := hm.2.1
      rw [hP, hσ, hG]; exact this
    have h3 : ∀ x : Fin W.rank → D.host.E, P *ᵥ x = 0 → ∃ a : Fin s → AE D,
        (Formalism.L2.Theta.mt W m - 1) *ᵥ (fun i => incA D (x i)) = L.map (incA D) *ᵥ a := by
      rw [hP, hσ, hG]; exact hm.2.2
    rw [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨conj_sub_one_kills_frame_of_fixed W L γ m hΓiL h1, ?_, ?_⟩
    · have := rowFrame_mul_conj_sub_one_eq_zero_of_fixed W P γ m hPΓ h2
      rw [hP, hσ, hG] at this; exact this
    · intro x hx
      rw [← hG, ← hσ, ← hP] at hx
      exact conj_unipotentRadical_kernelCondition_of_rationalFixed W L P γ m γ₀ γi hγ₀ hγγi hPγi hΓL h3 x hx
  intro n hn
  exact key hn

end GlobalTheory.FrameStab
end
end

