module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LogPeriodLimit
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0079
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0004
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0067
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0083
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0073
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagModelBaseProjectionPoints
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0081
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0039

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIntPreimageOfOrthogonalKernel
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.IntegralKernel

theorem exists_clear_denominators {g : ℕ} (w : Fin g → ℚ) :
    ∃ (D : ℤ) (v : Fin g → ℤ), D ≠ 0 ∧ ∀ i, (v i : ℚ) = (D : ℚ) * w i := by
  classical
  have hdvd : ∀ i, ∃ k : ℤ, (∏ j, ((w j).den : ℤ)) = ((w i).den : ℤ) * k := fun i =>
    Finset.dvd_prod_of_mem (fun j => ((w j).den : ℤ)) (Finset.mem_univ i)
  choose k hk using hdvd
  refine ⟨∏ j, ((w j).den : ℤ), fun i => (w i).num * k i, ?_, ?_⟩
  · exact Finset.prod_ne_zero_iff.mpr fun j _ => by exact_mod_cast (w j).den_nz
  · intro i
    rw [hk i]
    push_cast
    have h := Rat.mul_den_eq_num (w i)
    rw [← h]
    ring

theorem cast_mulVec {g : ℕ} (S : Matrix (Fin g) (Fin g) ℤ) (v : Fin g → ℤ) (i : Fin g) :
    (((S *ᵥ v) i : ℤ) : ℚ) = ((S.map (Int.cast : ℤ → ℚ)) *ᵥ (fun j => (v j : ℚ))) i := by
  simp [Matrix.mulVec, dotProduct]

theorem exists_smul_eq_mulVec (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) (hS : Sᵀ = S)
    (u : Fin g → ℤ) (hu : ∀ v : Fin g → ℤ, S *ᵥ v = 0 → u ⬝ᵥ v = 0) :
    ∃ (N : ℤ) (c : Fin g → ℤ), N ≠ 0 ∧ N • u = S *ᵥ c := by
  classical
  let Sq : Matrix (Fin g) (Fin g) ℚ := S.map (Int.cast : ℤ → ℚ)
  let uq : Fin g → ℚ := fun i => (u i : ℚ)
  have hSq : Sqᵀ = Sq := by
    ext i j
    have := congrFun (congrFun hS i) j
    simp only [Matrix.transpose_apply] at this
    simp [Sq, this]

  have hker : ∀ w : Fin g → ℚ, Sq *ᵥ w = 0 → uq ⬝ᵥ w = 0 := by
    intro w hw
    obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators w
    have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • w := by
      funext j; simp [hv j]
    have hSv : S *ᵥ v = 0 := by
      funext i
      have h1 := cast_mulVec S v i
      rw [hvq, Matrix.mulVec_smul] at h1
      have h2 : (((S *ᵥ v) i : ℤ) : ℚ) = 0 := by
        rw [h1]
        change ((D : ℚ) • (Sq *ᵥ w)) i = 0
        rw [hw]; simp
      exact_mod_cast h2
    have h0 := hu v hSv
    have h1 : ((u ⬝ᵥ v : ℤ) : ℚ) = (D : ℚ) * (uq ⬝ᵥ w) := by
      simp only [dotProduct, Int.cast_sum, Int.cast_mul, Finset.mul_sum, hv, uq]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h0] at h1
    have hDq : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    simpa [hDq] using h1.symm
  let f : (Fin g → ℚ) →ₗ[ℚ] (Fin g → ℚ) := Sq.mulVecLin
  let φ : Module.Dual ℚ (Fin g → ℚ) :=
    { toFun := fun w => uq ⬝ᵥ w
      map_add' := fun a b => dotProduct_add uq a b
      map_smul' := fun r a => by simp [dotProduct_smul] }
  have hφ : φ ∈ LinearMap.range f.dualMap := by
    rw [LinearMap.range_dualMap_eq_dualAnnihilator_ker]
    rw [Submodule.mem_dualAnnihilator]
    intro w hw
    exact hker w (by simpa [f] using hw)
  obtain ⟨ψ, hψ⟩ := hφ
  let c : Fin g → ℚ := fun i => ψ (Pi.single i 1)
  have hψc : ∀ w, ψ w = c ⬝ᵥ w := by
    intro w
    conv_lhs => rw [pi_eq_sum_univ' w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [map_sum, c, dotProduct, mul_comm]
  have hu_eq : uq = Sq *ᵥ c := by
    funext i
    have h1 : φ (Pi.single i 1) = uq i := by
      change uq ⬝ᵥ Pi.single i 1 = uq i
      simp
    have h2 : φ (Pi.single i 1) = ψ (Sq *ᵥ Pi.single i 1) := by
      rw [← hψ]; rfl
    rw [← h1, h2, hψc, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hSq]
    simp
  obtain ⟨D, v, hD, hv⟩ := exists_clear_denominators c
  refine ⟨D, v, hD, ?_⟩
  funext i
  have h1 := cast_mulVec S v i
  have hvq : (fun j => (v j : ℚ)) = (D : ℚ) • c := by
    funext j; simp [hv j]
  rw [hvq, Matrix.mulVec_smul] at h1
  have h2 : (((D • u) i : ℤ) : ℚ) = (((S *ᵥ v) i : ℤ) : ℚ) := by
    rw [h1]
    change _ = ((D : ℚ) • (Sq *ᵥ c)) i
    rw [← hu_eq]
    simp [uq]
  exact_mod_cast h2

end GlobalTheory.CompanionTheory.Ar.IntegralKernel
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsIsKerProj
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular
open GlobalTheory.CompanionTheory.Ar.RiemannLimit GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

namespace GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit

theorem exists_isKerProj (g : ℕ) (S : Matrix (Fin g) (Fin g) ℤ) :
    ∃ Pr : Matrix (Fin g) (Fin g) ℝ, IsKerProj S Pr := by
  classical
  set M : Matrix (Fin g) (Fin g) ℝ := S.map (fun x : ℤ => (x : ℝ)) with hM
  let K : Submodule ℝ (EuclideanSpace ℝ (Fin g)) := LinearMap.ker (Matrix.toEuclideanLin M)
  let P : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g) :=
    (K.starProjection : EuclideanSpace ℝ (Fin g) →ₗ[ℝ] EuclideanSpace ℝ (Fin g))
  let Pr : Matrix (Fin g) (Fin g) ℝ := Matrix.toEuclideanLin.symm P
  have hPr : Matrix.toEuclideanLin Pr = P := LinearEquiv.apply_symm_apply _ _
  have hmv : ∀ v : Fin g → ℝ, Pr *ᵥ v = WithLp.ofLp (P (WithLp.toLp 2 v)) := by
    intro v
    rw [← hPr, Matrix.toLpLin_apply]
  have hidem : ∀ x, P (P x) = P x := by
    intro x
    have hx : K.starProjection x ∈ K := Submodule.starProjection_apply_mem K x
    exact (Submodule.starProjection_eq_self_iff).2 hx
  refine ⟨Pr, ?_, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    refine LinearMap.ext fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hmv, hmv,
      WithLp.toLp_ofLp, hidem]
  · have hs : Pr.IsHermitian := by
      apply Matrix.isSymmetric_toEuclideanLin_iff.mp
      rw [hPr]
      exact Submodule.starProjection_isSymmetric K
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial] using hs.eq
  · intro v
    rw [hmv]
    constructor
    · intro h
      have hk : WithLp.toLp 2 v ∈ K := by
        have h' : M *ᵥ v = 0 := h
        rw [LinearMap.mem_ker, Matrix.toLpLin_apply]
        simp [h']
      have : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := (Submodule.starProjection_eq_self_iff).2 hk
      rw [this]
    · intro h
      have h1 : P (WithLp.toLp 2 v) = WithLp.toLp 2 v := by
        rw [← WithLp.toLp_ofLp (p := 2) (P (WithLp.toLp 2 v)), h]
      have hk : WithLp.toLp 2 v ∈ K := (Submodule.starProjection_eq_self_iff).1 h1
      rw [LinearMap.mem_ker, Matrix.toLpLin_apply] at hk
      have h' : M *ᵥ v = 0 := by simpa using hk
      exact h'

end GlobalTheory.CompanionTheory.Ar.Cusp.BoundaryLimit
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtBasePoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.CovGraph

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.CovGraph

theorem regAt_valAt_sum {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]
    {x : (Σ k, ι k) → Ω} {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts (mCoordIdeal x)) {α : Type} (s : Finset α)
    (f : α → Ω) (hf : ∀ a ∈ s, RegAt x (mCoordIdeal z) (f a)) :
    RegAt x (mCoordIdeal z) (∑ a ∈ s, f a) ∧ valAt x (∑ a ∈ s, f a) z = ∑ a ∈ s, valAt x (f a) z := by
  obtain ⟨h0, -, v0, -, hst⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring K ι Ω x z hz
  induction s using Finset.induction_on with
  | empty => simpa using ⟨h0, v0⟩
  | insert a s ha ih =>
    obtain ⟨ih1, ih2⟩ := ih fun b hb => hf b (Finset.mem_insert_of_mem hb)
    have hfa := hf a (Finset.mem_insert_self a s)
    obtain ⟨-, r, -, v⟩ := hst _ _ hfa ih1
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨r, v.trans (by rw [ih2])⟩

theorem coE_regAt_valAt : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (zb : (Σ k, baseIdx ι' M'.blk k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), zb ∈ mcPts (mCoordIdeal M'.x) → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal zb) → M.GoodAt F (mCoordIdeal (zb ∘ Cv.v)) → ∀ (p : Ψ × Fin N) (q : Σ k, ι k) (r : Σ k, ι' k), RegAt M'.x (mCoordIdeal zb) (coE Cv F' F p q r) ∧ valAt M'.x (coE Cv F' F p q r) zb = ∑ I, ∑ I' ∈ Finset.univ.filter (IsStepRows N j p.2), valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv zb F' F hz hF' hF hG' hG p q r
  obtain ⟨-, -, -, -, hst⟩ := GlobalTheory.CompanionTheory.Ar.PB.ValRing.regAt_valAt_ring _ _ _ M'.x zb hz
  have hT : ∀ a b, RegAt M'.x (mCoordIdeal zb) (trMat Cv F' F p.1 a b) := fun a b =>
    (Cv.agree zb hz F' F hF' hF hG' hG p.1 a b).1
  have hmin := CovMap.LocImg.reg_minor hz hT
  have hxv : M'.x ∘ Cv.v = Cv.φ ∘ M.x := funext Cv.x_eq
  have hzv := RegPhi.comp_mem_mcPts Cv.block Cv.φ hxv hz
  have hu (I : Finset (Fin N)) :
      RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I)) ∧
        valAt M'.x (Cv.φ (F.u q I)) zb = valAt M.x (F.u q I) (zb ∘ Cv.v) := by
    obtain ⟨d, g, h, hg, hh, hn, he⟩ := (hG.2.1 q I).1
    have hg' := RegPhi.isMultiHomog_rename_block Cv.block hg
    have hh' := RegPhi.isMultiHomog_rename_block Cv.block hh
    have hn' := RegPhi.rename_notMem Cv.block hn
    have hae (f : MRing (baseIdx ι M.blk)) :
        aeval M'.x (rename Cv.v f) = Cv.φ (aeval M.x f) := by
      rw [aeval_rename, hxv, RegPhi.aeval_comp_ringHom]
    have he' : aeval M'.x (rename Cv.v g) = Cv.φ (F.u q I) * aeval M'.x (rename Cv.v h) := by
      rw [hae, hae, he, map_mul]
    refine ⟨⟨_, _, _, hg', hh', hn', he'⟩, ?_⟩
    let value := eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) g) /
      eval (zb ∘ Cv.v) (map (Int.castRingHom ℂ) h)
    have hv : IsValueAt M.x (F.u q I) (zb ∘ Cv.v) value :=
      ⟨d, g, h, hg, hh, ValRing.aeval_ne_zero_of_notMem hzv hh hn, he,
        ValRing.eval_ne_zero_of_notMem hh hn, rfl⟩
    have hv' : IsValueAt M'.x (Cv.φ (F.u q I)) zb value := by
      refine ⟨_, _, _, hg', hh', ValRing.aeval_ne_zero_of_notMem hz hh' hn', he',
        ValRing.eval_ne_zero_of_notMem hh' hn', ?_⟩
      rw [RegPhi.eval_rename_block, RegPhi.eval_rename_block]
    exact (valAt_eq hz hv').trans (valAt_eq hzv hv).symm
  have hu' := fun I' => (hG'.2.1 r I').2
  have hterm : ∀ I I', RegAt M'.x (mCoordIdeal zb) (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) ∧
      valAt M'.x (Cv.φ (F.u q I) * minorIJ (trMat Cv F' F p.1) I I' * F'.u' I' r) zb =
        valAt M.x (F.u q I) (zb ∘ Cv.v) * minorIJ (Cv.trans F' F zb p.1) I I' * valAt M'.x (F'.u' I' r) zb := by
    intro I I'
    obtain ⟨r1, -, v1, -⟩ := hst _ _ (hu I).1 (hmin I I').1
    obtain ⟨r2, -, v2, -⟩ := hst _ _ r1 (hu' I')
    refine ⟨r2, v2.trans ?_⟩
    rw [v1, (hu I).2, (hmin I I').2]
    rfl
  have hin := fun I => regAt_valAt_sum hz (Finset.univ.filter (IsStepRows N j p.2)) _
    fun I' _ => (hterm I I').1
  have hout := regAt_valAt_sum hz Finset.univ _ fun I _ => (hin I).1
  refine ⟨hout.1, ?_⟩
  refine hout.2.trans (Finset.sum_congr rfl fun I _ => ?_)
  rw [(hin I).2]
  exact Finset.sum_congr rfl fun I' _ => (hterm I I').2

end GlobalTheory.CompanionTheory.Ar.PB.CovGraph
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverFramesAtPoint
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

noncomputable section
namespace GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An

section Loc

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}

def LocAn (S : Set E) (z : E) (φ : E → ℂ) : Prop :=
  ∃ f : E → ℂ, AnalyticAt ℂ f z ∧ ∀ᶠ w in 𝓝[S] z, φ w = f w

theorem LocAn.of_analyticAt {φ : E → ℂ} (h : AnalyticAt ℂ φ z) : LocAn S z φ :=
  ⟨φ, h, Eventually.of_forall fun _ => rfl⟩

theorem LocAn.const (c : ℂ) : LocAn S z fun _ => c := .of_analyticAt analyticAt_const

theorem LocAn.add {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w + ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w + g w, hf.add hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.mul {φ ψ : E → ℂ} (h : LocAn S z φ) (h' : LocAn S z ψ) : LocAn S z fun w => φ w * ψ w := by
  obtain ⟨f, hf, e⟩ := h
  obtain ⟨g, hg, e'⟩ := h'
  refine ⟨fun w => f w * g w, hf.mul hg, ?_⟩
  filter_upwards [e, e'] with w a b
  rw [a, b]

theorem LocAn.sum {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∑ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 0
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.prod {σ : Type} (s : Finset σ) {φ : σ → E → ℂ} (h : ∀ i ∈ s, LocAn S z (φ i)) :
    LocAn S z fun w => ∏ i ∈ s, φ i w := by
  induction s using Finset.induction_on with
  | empty => simpa using LocAn.const (S := S) (z := z) 1
  | insert a s ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem LocAn.det {n : ℕ} {A : E → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b) :
    LocAn S z fun w => (A w).det := by
  simp only [Matrix.det_apply']
  exact LocAn.sum _ fun σ _ => (LocAn.const _).mul (LocAn.prod _ fun i _ => h _ _)

theorem LocAn.minor {N : ℕ} {A : E → Matrix (Fin N) (Fin N) ℂ} (h : ∀ a b, LocAn S z fun w => A w a b)
    (I J : Finset (Fin N)) : LocAn S z fun w => minorIJ (A w) I J := by
  unfold minorIJ
  split_ifs with e
  · exact LocAn.det fun a b => h _ _
  · exact LocAn.const 0

end Loc

section Val

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {S : Set E} {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

theorem eval_eq_zero_of_mem {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : f ∈ mCoordIdeal b) :
    eval b (map (Int.castRingHom ℂ) f) = 0 := by
  have h0 : mConeMap b f = 0 := hf
  have e : ∀ f : MRing ι, eval (fun _ => (1 : ℂ)) (mConeMap b f) = eval b (map (Int.castRingHom ℂ) f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [mConeMap]
    | add p q hp hq => simp [map_add (f := _), hp, hq]
    | mul_X p q hp =>
      have e1 : eval (fun _ => (1 : ℂ)) (mConeMap b (X q)) = b q := by simp [mConeMap]
      rw [map_mul, map_mul, hp, e1, map_mul, map_mul, map_X, eval_X]
  rw [← e, h0, map_zero]

theorem notMem_of_eval_ne_zero {b : (Σ k, ι k) → ℂ} {f : MRing ι} (hf : eval b (map (Int.castRingHom ℂ) f) ≠ 0) :
    f ∉ mCoordIdeal b := fun h => hf (eval_eq_zero_of_mem h)

theorem coord_ne_zero_of_notMem {b : (Σ k, ι k) → ℂ} {q : Σ k, ι k} (h : (X q : MRing ι) ∉ mCoordIdeal b) :
    b q ≠ 0 := fun e => h (by
  show mConeMap b (X q) = 0
  rw [mConeMap, aeval_X, e, map_zero, zero_mul])

theorem analyticAt_eval {σ : Type} {b : E → σ → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (p : MvPolynomial σ ℤ) : AnalyticAt ℂ (fun w => eval (b w) (map (Int.castRingHom ℂ) p)) z := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using analyticAt_const
  | add p q hp hq =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p + q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) + eval (b w) (map (Int.castRingHom ℂ) q) := by
      funext w; rw [map_add (f := _), map_add (f := _)]
    rw [e]; exact hp.add hq
  | mul_X p q hp =>
    have e : (fun w => eval (b w) (map (Int.castRingHom ℂ) (p * X q))) = fun w =>
        eval (b w) (map (Int.castRingHom ℂ) p) * b w q := by
      funext w; rw [map_mul, map_mul, map_X, eval_X]
    rw [e]; exact hp.mul (hb q)

theorem regAt_eventually {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) : ∀ᶠ w in 𝓝 z, RegAt x (mCoordIdeal (b w)) s := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  filter_upwards [(analyticAt_eval hb h).continuousAt.eventually_ne (ValRing.eval_ne_zero_of_notMem hh hn)] with w hw
  exact ⟨d, g, h, hg, hh, notMem_of_eval_ne_zero hw, heq⟩

theorem locAn_valAt {x : (Σ k, ι k) → Ω} {b : E → (Σ k, ι k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hpt : ∀ w ∈ S, b w ∈ mcPts (mCoordIdeal x)) (hz : z ∈ S) {s : Ω} (hs : RegAt x (mCoordIdeal (b z)) s) :
    LocAn S z fun w => valAt x s (b w) := by
  obtain ⟨d, g, h, hg, hh, hn, heq⟩ := hs
  have h0 := ValRing.eval_ne_zero_of_notMem hh hn
  have hx := ValRing.aeval_ne_zero_of_notMem (hpt z hz) hh hn
  refine ⟨fun w => eval (b w) (map (Int.castRingHom ℂ) g) / eval (b w) (map (Int.castRingHom ℂ) h),
    (analyticAt_eval hb g).div (analyticAt_eval hb h) h0, ?_⟩
  filter_upwards [nhdsWithin_le_nhds ((analyticAt_eval hb h).continuousAt.eventually_ne h0), self_mem_nhdsWithin]
    with w hw hwS
  exact valAt_eq (hpt w hwS) ⟨d, g, h, hg, hh, hx, heq, hw, rfl⟩

end Val

section Good

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {z : E}
  {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Finite Ψ] {N j : ℕ}

theorem goodAt_eventually (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk)
    {b : E → (Σ k, baseIdx ι M.blk k) → ℂ} (hb : ∀ q, AnalyticAt ℂ (fun w => b w q) z)
    (hg : M.GoodAt F (mCoordIdeal (b z))) : ∀ᶠ w in 𝓝 z, M.GoodAt F (mCoordIdeal (b w)) := by
  obtain ⟨h1, h2, h3⟩ := hg
  have A : ∀ᶠ w in 𝓝 z, ∀ k, (X ⟨k, F.c k⟩ : MRing (baseIdx ι M.blk)) ∉ mCoordIdeal (b w) := by
    refine eventually_all.2 fun k => ?_
    filter_upwards [(hb ⟨k, F.c k⟩).continuousAt.eventually_ne (coord_ne_zero_of_notMem (h1 k))] with w hw
    refine notMem_of_eval_ne_zero ?_
    simpa using hw
  have B : ∀ᶠ w in 𝓝 z, ∀ q I, RegAt M.x (mCoordIdeal (b w)) (F.u q I) ∧ RegAt M.x (mCoordIdeal (b w)) (F.u' I q) :=
    eventually_all.2 fun q => eventually_all.2 fun I =>
      (regAt_eventually hb (h2 q I).1).and (regAt_eventually hb (h2 q I).2)
  have C : ∀ᶠ w in 𝓝 z, ∀ p, M.blk p = none → F.υ p ≠ 0 ∧ RegAt M.x (mCoordIdeal (b w)) (F.υ p) ∧
      RegAt M.x (mCoordIdeal (b w)) (F.υ p)⁻¹ := by
    refine eventually_all.2 fun p => ?_
    by_cases hp : M.blk p = none
    · filter_upwards [regAt_eventually hb (h3 p hp).2.1, regAt_eventually hb (h3 p hp).2.2] with w a c
      exact fun _ => ⟨(h3 p hp).1, a, c⟩
    · exact Eventually.of_forall fun _ h => absurd h hp
  filter_upwards [A, B, C] with w a c d
  exact ⟨a, c, d⟩

end Good

section Img

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ} {K' : Type} [Fintype K'] {ι' : K' → Type} [∀ k, Fintype (ι' k)] {Φ' : Type} [Field Φ']
  {y' : (Σ k, ι' k) → Φ'}

theorem analyticAt_coord (z : (Σ k, ι' k) → ℂ) (q : Σ k, ι' k) :
    AnalyticAt ℂ (fun w : (Σ k, ι' k) → ℂ => w q) z :=
  (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ k, ι' k) => ℂ) q).analyticAt z

theorem locAn_img {M : FlagModel y Ψ N j} {M' : FlagModel y' Ψ N j} (Cv : FlagCover M' M)
    {z : (Σ k, ι' k) → ℂ} {F' : FrameData ι' Ψ N M'.Ω M'.blk} {F : FrameData ι Ψ N M.Ω M.blk}
    (hz : z ∈ mcPts (mCoordIdeal y'))
    (hp1 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∈ mcPts (mCoordIdeal M'.x))
    (hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x))
    (hF' : M'.IsFrame F') (hF : M.IsFrame F)
    (hg' : M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)))
    (hg : M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v))) (q : Σ k, ι k) :
    LocAn (mcPts (mCoordIdeal y')) z fun w => img Cv F' F w q := by
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  obtain ⟨k, m⟩ := q
  by_cases hk : ∀ p, M.blk p ≠ some k
  · refine .of_analyticAt ?_
    have e : (fun w => img Cv F' F w ⟨k, m⟩) = fun w => basePart M'.blk w (Cv.v ⟨⟨k, hk⟩, m⟩) := by
      funext w
      exact congrFun (img_base Cv F' F w) ⟨⟨k, hk⟩, m⟩
    rw [e]
    exact hb _
  · obtain ⟨p, hp⟩ : ∃ p, M.blk p = some k := by simpa using hk
    obtain ⟨k', hp'⟩ := exists_blk_cover M' hp
    simp only [img_step Cv F' F _ hp hp' m]
    unfold stepCoord
    refine LocAn.sum _ fun I _ => (locAn_valAt hbv hp2 hz (hg.2.1 _ I).1).mul (LocAn.sum _ fun I' _ => ?_)
    by_cases hI : IsStepRows N j p.2 I'
    · simp only [if_pos hI]
      refine (LocAn.minor (fun a c => ?_) I I').mul
        (LocAn.sum _ fun m' _ => (locAn_valAt hb hp1 hz (hg'.2.1 _ I').2).mul (.of_analyticAt (analyticAt_coord z _)))
      exact locAn_valAt hb hp1 hz (Cv.agree _ (hp1 z hz) F' F hF' hF hg' hg p.1 a c).1
    · simp only [if_neg hI]
      exact LocAn.const 0

end Img

theorem main : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (K' : Type) [Fintype K'] (ι' : K' → Type) [∀ k, Fintype (ι' k)] (Φ' : Type) [Field Φ'] (y' : (Σ k, ι' k) → Φ') (M' : FlagModel y' Ψ N j) (Cv : FlagCover M' M) (z : (Σ k, ι' k) → ℂ) (F' : FrameData ι' Ψ N M'.Ω M'.blk) (F : FrameData ι Ψ N M.Ω M.blk), z ∈ mcPts (mCoordIdeal y') → M'.IsFrame F' → M.IsFrame F → M'.GoodAt F' (mCoordIdeal (basePart M'.blk z)) → M.GoodAt F (mCoordIdeal (basePart M'.blk z ∘ Cv.v)) → ∃ (V : Set ((Σ k, ι' k) → ℂ)) (f : ((Σ k, ι' k) → ℂ) → (Σ k, ι k) → ℂ), IsOpen V ∧ z ∈ V ∧ AnalyticOnNhd ℂ f V ∧ ∀ z' ∈ V ∩ mcPts (mCoordIdeal y'), M'.GoodAt F' (mCoordIdeal (basePart M'.blk z')) ∧ M.GoodAt F (mCoordIdeal (basePart M'.blk z' ∘ Cv.v)) ∧ f z' = CovMap.LocImg.img Cv F' F z' := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M K' _ ι' _ Φ' _ y' M' Cv z F' F hz hF' hF hg' hg
  have hp1 := (_root_.GlobalTheory.CompanionTheory.Ar.PB.CPts.main K' ι' Φ' y' Ψ N j M').1
  have hp2 : ∀ w ∈ mcPts (mCoordIdeal y'), basePart M'.blk w ∘ Cv.v ∈ mcPts (mCoordIdeal M.x) := fun w hw =>
    (_root_.GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.Pt.main K ι Φ y Ψ N j M K' ι' Φ' y' M' Cv _ (hp1 w hw)).1
  have hb : ∀ q, AnalyticAt ℂ (fun w => basePart M'.blk w q) z := fun q => analyticAt_coord z _
  have hbv : ∀ q, AnalyticAt ℂ (fun w => (basePart M'.blk w ∘ Cv.v) q) z := fun q => hb _
  choose f hf hev using locAn_img Cv hz hp1 hp2 hF' hF hg' hg
  have e1 : ∀ᶠ w in 𝓝 z, AnalyticAt ℂ (fun w q => f q w) w :=
    (analyticAt_pi_iff.2 hf).eventually_analyticAt
  have e2 : ∀ᶠ w in 𝓝 z, w ∈ mcPts (mCoordIdeal y') → ∀ q, img Cv F' F w q = f q w :=
    eventually_nhdsWithin_iff.1 (eventually_all.2 hev)
  obtain ⟨V, hV, hVo, hzV⟩ := eventually_nhds_iff.1
    (e1.and (e2.and ((goodAt_eventually M' F' hb hg').and (goodAt_eventually M F hbv hg))))
  refine ⟨V, fun w q => f q w, hVo, hzV, fun w hw => (hV w hw).1, fun w hw => ?_⟩
  obtain ⟨-, a, c, d⟩ := hV w hw.1
  exact ⟨c, d, funext fun q => (a hw.2 q).symm⟩

end GlobalTheory.CompanionTheory.Ar.PB.CovMap.LocImg.An
end
end

