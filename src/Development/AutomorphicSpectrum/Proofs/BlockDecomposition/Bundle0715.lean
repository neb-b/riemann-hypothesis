module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsRadNMulLevM
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0710
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0549
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0711
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0687
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0048
public import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0001
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0707
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0696
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0692
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0691
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0699
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0695
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0693
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0694
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RankOneThetaIntegralRayLimit
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0697

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HaarSkewMatricesConjScaling
section
noncomputable section
open scoped Matrix NNReal ENNReal TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.CompanionTheory.QKAvg
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SkewMod

open GlobalTheory.CompanionTheory.IwaAd GlobalTheory.CompanionTheory.CgMod

variable {D : D7} {n : ℕ}

def skewPart (D : D7) (n : ℕ) (x : Mx D n n) : Mx D n n := half D • (x - adj x)

theorem skewPart_add (x y : Mx D n n) : skewPart D n (x + y) = skewPart D n x + skewPart D n y := by
  simp only [skewPart, adj_add]
  rw [← smul_add]
  congr 1
  abel

def skewPartHom (D : D7) (n : ℕ) : Mx D n n →+ Mx D n n := AddMonoidHom.mk' (skewPart D n) skewPart_add

theorem skewPart_mem (x : Mx D n n) : skewPart D n x ∈ skewA D n := by
  rw [mem_skewA, skewPart, adj_smul, cA_half, adj_sub, adj_adj, ← smul_neg, neg_sub]

theorem skewPart_of_mem {s : Mx D n n} (hs : s ∈ skewA D n) : skewPart D n s = s := by
  rw [skewPart, mem_skewA.1 hs, sub_neg_eq_add, smul_add]
  exact half_smul_add s

theorem skewPart_anti {c : AE D} (hc : cA D c = -c) {s : Mx D n n} (hs : s ∈ skewA D n) :
    skewPart D n (c • s) = 0 := by
  rw [skewPart, adj_smul, mem_skewA.1 hs, hc, neg_smul, smul_neg, neg_neg, sub_self, smul_zero]

theorem skewPart_split {d e : AE D} (he : cA D e = -e) (hde : d * e = 1) (x : Mx D n n) :
    skewPart D n x + d • skewPart D n (e • x) = x := by
  have h : d * half D * e = half D := by rw [mul_comm d, mul_assoc, hde, mul_one]
  rw [skewPart, skewPart, adj_smul, he, neg_smul, sub_neg_eq_add, ← smul_add, smul_smul, smul_smul, h, smul_add,
    smul_sub]
  have := half_smul_add x
  rw [sub_add_add_cancel]
  exact this

set_option synthInstance.maxHeartbeats 400000 in
theorem continuous_skewPart : Continuous (skewPartHom D n) := by
  haveI : IsTopologicalAddGroup (Mx D n n) := (lattice_Mx D n n).1
  have h : Continuous fun x : Mx D n n => x - adj x := continuous_id.sub (continuous_adj (D := D) (m := n) (n := n))
  change Continuous fun x : Mx D n n => half D • (x - adj x)
  exact h.const_smul (half D)

theorem lr_skew (a : GL (Fin n) (AE D)) : ∀ s ∈ skewA D n, GlobalTheory.ModuLR.lrCE a (ad a)⁻¹ s ∈ skewA D n :=
  fun s hs => (skewConj a.1 ⟨s, hs⟩).2

theorem lr_skew_symm (a : GL (Fin n) (AE D)) :
    ∀ s ∈ skewA D n, (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹).symm s ∈ skewA D n :=
  fun s hs => (skewConj (a⁻¹).1 ⟨s, hs⟩).2


set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1000000 in
theorem map_skewConj : ∀ (D : D7) (r : ℕ) (κ : Measure (skewA D r)), κ.IsAddHaarMeasure → ∀ a : GL (Fin r) (AE D), κ.map (skewConj a.1) = ((absA D (Matrix.GeneralLinearGroup.det a) ^ r)⁻¹ : ℝ≥0) • κ := by
  intro D n κ hκ a
  obtain ⟨i1, i2, i3, i4, -, -⟩ := lattice_Mx D n n
  haveI : IsTopologicalAddGroup (Mx D n n) := i1
  haveI : LocallyCompactSpace (Mx D n n) := i2
  haveI : SecondCountableTopology (Mx D n n) := i3
  haveI : T2Space (Mx D n n) := i4
  haveI : BorelSpace (Mx D n n) := ⟨rfl⟩
  haveI : BorelSpace (skewA D n) := Subtype.borelSpace _
  haveI : SecondCountableTopology (skewA D n) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI : T2Space (skewA D n) := Topology.IsEmbedding.subtypeVal.t2Space
  have hcl : IsClosed (skewA D n : Set (Mx D n n)) := isClosed_eq continuous_adj continuous_neg
  haveI : LocallyCompactSpace (skewA D n) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  obtain ⟨d, e, hde, hd, he⟩ := exists_anti_units D
  have hsq := char_sq (skewA D n) (skewPartHom D n) continuous_skewPart skewPart_mem
    (fun s hs => skewPart_of_mem hs) (mulCE d e hde)
    (fun s hs => skewPart_anti hd hs) (fun s hs => skewPart_anti he hs)
    (fun x => skewPart_split he hde x) (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹)
    (lr_smul a d e hde) (lr_skew a) (lr_skew_symm a)
  have hlr : addEquivAddHaarChar (GlobalTheory.ModuLR.lrCE a (ad a)⁻¹) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE _ _ D.sp.cm.sig (isCMExt_host D) n n a (ad a)⁻¹
    rw [h]
    exact congrArg (fun t => absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n * t ^ n) (absA_det_ad_inv a)
  have hT : addEquivAddHaarChar (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) =
      absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n :=
    (pow_left_inj₀ zero_le zero_le two_ne_zero).1 ((hsq.trans hlr).trans (sq _).symm)
  have h := addEquivAddHaarChar_smul_map κ (restr (skewA D n) _ (lr_skew a) (lr_skew_symm a))
  have e1 : (⇑(restr (skewA D n) _ (lr_skew a) (lr_skew_symm a)) : skewA D n → skewA D n) = skewConj a.1 := rfl
  rw [hT, e1] at h
  have hne : absA D (Matrix.GeneralLinearGroup.det a : (AE D)ˣ) ^ n ≠ 0 := pow_ne_zero _ (absA_pos _).ne'
  conv_rhs => rw [← h]
  rw [smul_smul, inv_mul_cancel₀ hne, one_smul]

end GlobalTheory.CompanionTheory.SkewMod
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableThetaKernelProduct
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS
open IsDedekindDomain NumberField
open GlobalTheory.RegSch (ikS projS Lvl)
open PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L
open GlobalTheory.CompanionTheory.ColumnSplitting
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.ColumnSplitting

namespace Integ

variable {D : D7} {n t : ℕ} {B W : HSp D}

theorem det_bl {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) :
    Matrix.det (bl hn 1 y 0 1 : Mx D n n) = 1 := by
  unfold bl
  rw [Matrix.det_submatrix_equiv_self, Matrix.det_fromBlocks_zero₂₁]
  simp

def blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) : GL (Fin n) (AE D) :=
  ⟨bl hn 1 y 0 1, bl hn 1 (-y) 0 1, GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ rfl,
    GlobalTheory.CompanionTheory.JacobiMaps.sh_mul hn _ _ (neg_neg y).symm⟩

theorem det_blU {r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (a : GL (Fin n) (AE D)) (ha : a.1 = bl hn 1 y 0 1) :
    Matrix.GeneralLinearGroup.det a = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, Units.val_one, ha]
  exact det_bl hn y

theorem lintegral_comp_char_one {A : Type} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [LocallyCompactSpace A] [SecondCountableTopology A] [T2Space A] [MeasurableSpace A] [BorelSpace A]
    (μ : Measure A) [μ.IsAddHaarMeasure] (φ : A ≃ₜ+ A) (hc : addEquivAddHaarChar φ = 1) (g : A → ℝ≥0∞) :
    ∫⁻ y, g (φ y) ∂μ = ∫⁻ y, g y ∂μ := by
  have key := addEquivAddHaarChar_smul_map μ φ
  rw [hc, one_smul] at key
  have hp : MeasurePreserving φ μ μ := ⟨φ.continuous.measurable, key⟩
  exact hp.lintegral_comp_emb φ.toHomeomorph.measurableEmbedding g

theorem lintegral_bl {a r t n : ℕ} (hn : r + t = n) (y : Mx D r t) (ν : Measure (Mx D a n))
    (hν : ν.IsAddHaarMeasure) (g : Mx D a n → ℝ≥0∞) :
    ∫⁻ U, g (mm U (bl hn 1 y 0 1)) ∂ν = ∫⁻ U, g U ∂ν := by
  obtain ⟨i1, i2, i3, i4, i5⟩ := top_mx (D := D) a n
  haveI := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  let φ := GlobalTheory.ModuLR.lrCE (1 : GL (Fin a) (AE D)) (blU hn y)
  have hc : addEquivAddHaarChar φ = 1 := by
    have h := GlobalTheory.ResidueEisenstein.ModMat.addEquivAddHaarChar_lrCE D.host.F D.host.E D.sp.cm.sig (isCMExt_host D) a n
      (1 : GL (Fin a) (AE D)) (blU hn y)
    rw [det_blU hn y (blU hn y) rfl] at h
    simpa only [map_one, one_pow, mul_one] using h
  have e : ∀ U : Mx D a n, mm U (bl hn 1 y 0 1) = φ U := fun U => by
    simp only [φ]
    rw [GlobalTheory.ModuLR.lrCE_apply, Units.val_one, Matrix.one_mul]
    rfl
  simp only [e]
  exact lintegral_comp_char_one ν φ hc g

theorem jn_first {a r t n : ℕ} (hn : r + t = n) (w : Mx D a r) (v : Mx D a t) :
    (jn hn w v).submatrix id (fun j => finCongr hn (Fin.castAdd t j)) = w := by
  ext i j
  simp [jn, Matrix.submatrix_apply, Matrix.fromCols]

theorem xu_bl (d : HypDec B W t) (hn : W.rank + t = n) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (h : GA D W) (U : Mx D t n) (y : Mx D W.rank t) :
    mm (XU d hn x₀ h U) (bl hn 1 y 0 1) =
      mm d.jX (mm U (bl hn 1 y 0 1)) + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1)) := by
  unfold XU
  simp only [mm]
  rw [Matrix.add_mul, Matrix.mul_assoc, Matrix.mul_assoc]

theorem inner_eq (hIkL : IkLint) (hJn : JnBl) {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n) {θ : InfFam D}
    (hθ : IsInfFam θ) {M : Mx D B.rank n → ℂ} (hM : M ∈ schwartzA θ B.rank n)
    (hM0 : ∀ x, 0 ≤ (M x).re ∧ (M x).im = 0) (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) (h : GA D W)
    (y : Mx D W.rank t) :
    ∫⁻ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK ∂I.μ₁ =
      ‖ikp I M (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))‖ₑ := by
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have hb : mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1) = jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0) :=
    hJn D n t _ _ hn _ _ y
  rw [← hb, ← hIkL D n t B W d I θ hθ M hM hM0]
  simp only [xu_bl]
  exact lintegral_bl hn y I.μ₁ hf.1
    (fun U => ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm d.jX U + mm d.j0 (mm (jn hn (ww W x₀ h) 0) (bl hn 1 y 0 1))))‖ₑ ∂I.νK)

theorem continuous_jn {a r t n : ℕ} (hn : r + t = n) :
    Continuous fun u : Mx D a r × Mx D a t => jn hn u.1 u.2 := by
  refine continuous_matrix fun i j => ?_
  change Continuous fun u : Mx D a r × Mx D a t =>
    Matrix.fromCols u.1 u.2 i ((finSumFinEquiv.trans (finCongr hn)).symm j)
  generalize (finSumFinEquiv.trans (finCongr hn)).symm j = s
  cases s with
  | inl k => exact continuous_fst.matrix_elem i k
  | inr k => exact continuous_snd.matrix_elem i k

theorem continuous_bl {r t n : ℕ} (hn : r + t = n) : Continuous fun y : Mx D r t => (bl hn 1 y 0 1 : Mx D n n) :=
  (continuous_const.matrix_fromBlocks continuous_id continuous_const continuous_const).matrix_submatrix _ _

theorem continuous_pt {d : HypDec B W t} (hn : W.rank + t = n) (I : IkD d n)
    (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E) :
    Continuous fun p : I.l.K × Par D n t W =>
      mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)) := by
  have := isTopologicalRing_tens (F := D.host.F) (E := D.host.E) (R := AF D.host.F)
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  obtain ⟨-, g2, -, -, g5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  have hT := (top_mx (D := D) B.rank n).1
  have hU : Continuous fun p : I.l.K × Par D n t W => p.2.2.1 := continuous_fst.comp (continuous_snd.comp continuous_snd)
  have hh : Continuous fun p : I.l.K × Par D n t W => p.2.1 := continuous_fst.comp continuous_snd
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hX : Continuous fun p : I.l.K × Par D n t W => XU d hn x₀ p.2.1 p.2.2.1 :=
    (continuous_const.matrix_mul hU).add (continuous_const.matrix_mul
      ((continuous_jn hn).comp (((continuous_ww x₀).comp hh).prodMk continuous_const)))
  exact ((continuous_mt B).comp (continuous_subtype_val.comp continuous_fst).inv).matrix_mul
    (hX.matrix_mul ((continuous_bl hn).comp hy))

end Integ


open Integ in
theorem integrable_core : IkSch → Dom → OrbFin → Shift → IkLint → Fub4 → JnBl → ∀ (D : D7) (n t : ℕ) (B W : HSp D) (d : HypDec B W t) (hn : W.rank + t = n) (I : IkD d n) θ, IsInfFam θ → ∀ (μ : Measure (Mx D W.rank t)), μ.IsAddHaarMeasure → ∀ (x₀ : Matrix (Fin W.rank) (Fin W.rank) D.host.E), x₀.det ≠ 0 → ∀ Φ ∈ schwartzA θ B.rank n, ∀ η ∈ schwartzA θ W.rank t, Integrable (core hn I x₀ Φ η) (I.νK.prod (Q0 I μ)) := by
  intro hIk hDom hOrb _ hIkL hFub hJn D n t B W d hn I θ hθ μ hμ x₀ hx₀ Φ hΦ η hη
  obtain ⟨M, hM, hM0, hMd⟩ := hDom D θ hθ B.rank n n id Function.injective_id Φ hΦ
  have hΨ : ikp I M ∈ schwartzA θ W.rank n := (hIk D n t B W d I θ hθ M hM).2
  obtain ⟨N, hN, -, hNd⟩ := hDom D θ hθ W.rank n W.rank (fun j => finCongr hn (Fin.castAdd t j))
    (fun a b h => by simpa using h) (ikp I M) hΨ

  obtain ⟨h1, h2⟩ := top_par (D := D) n t W
  obtain ⟨-, i2, i3, i4, i5⟩ := top_mx (D := D) t n
  obtain ⟨-, j2, j3, j4, j5⟩ := top_mx (D := D) W.rank t
  obtain ⟨-, g2, g3, -, -, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D W
  obtain ⟨-, k2, -, -, k5, -⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D B
  have hBG : BorelSpace (GA D W) := ⟨rfl⟩
  have hB : BorelSpace (GA D B) := ⟨rfl⟩
  have hK : BorelSpace I.l.K := Subtype.borelSpace _
  have o0 : OpensMeasurableSpace (Par D n t W) := h1.opensMeasurable
  have oK : OpensMeasurableSpace I.l.K := hK.opensMeasurable
  have e1 : SecondCountableTopologyEither I.l.K (Par D n t W) := ⟨Or.inr h2⟩
  have o1 : OpensMeasurableSpace (I.l.K × Par D n t W) := Prod.opensMeasurableSpace
  obtain ⟨𝓕, hf⟩ := I.cov₁
  have := hf.1
  have := I.haar
  have := I.probK
  have hcM : Continuous M := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ M hM).1
  have hcΦ : Continuous Φ := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ Φ hΦ).1
  have hcη : Continuous η := (GlobalTheory.CompanionTheory.WeilTheta.schwartzA_continuous_and_dominated D θ hθ _ _ η hη).1
  have hpt := continuous_pt (d := d) hn I x₀
  have hy : Continuous fun p : I.l.K × Par D n t W => p.2.2.2 := continuous_snd.comp (continuous_snd.comp continuous_snd)
  have hcore : Continuous (core hn I x₀ Φ η) :=
    (hcΦ.comp hpt).mul (Complex.continuous_conj.comp (hcη.comp hy))
  refine ⟨hcore.measurable.aestronglyMeasurable, ?_⟩

  set F : I.l.K × GA D W × Mx D t n × Mx D W.rank t → ℝ≥0∞ := fun p =>
    ‖M (mm (mt B ((p.1 : GA D B)⁻¹)) (mm (XU d hn x₀ p.2.1 p.2.2.1) (bl hn 1 p.2.2.2 0 1)))‖ₑ * ‖η p.2.2.2‖ₑ with hF
  have hFm : Measurable F :=
    (hcM.comp hpt).measurable.enorm.mul (hcη.comp hy).measurable.enorm
  have hle : ∀ p, ‖core hn I x₀ Φ η p‖ₑ ≤ F p := fun p => by
    simp only [core, hF, enorm_mul, RCLike.enorm_conj]
    gcongr
    rw [enorm_le_iff_norm_le]
    refine (hMd _).trans ?_
    simpa using Complex.re_le_norm _
  have hη' : ∫⁻ y, ‖η y‖ₑ ∂μ < ⊤ :=
    hasFiniteIntegral_iff_enorm.1 (GlobalTheory.CompanionTheory.WSum.integrable_schwartzA_haar D θ hθ W.rank t μ η hη).2
  have hN' : ∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m < ⊤ := hOrb D θ hθ W I.m I.haar x₀ hx₀ N hN
  have hin : ∀ y h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ≤ ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ := fun y h => by
    simp only [hF]
    have e : ∀ U, ∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ * ‖η y‖ₑ ∂I.νK =
        (∫⁻ k : I.l.K, ‖M (mm (mt B ((k : GA D B)⁻¹)) (mm (XU d hn x₀ h U) (bl hn 1 y 0 1)))‖ₑ ∂I.νK) * ‖η y‖ₑ := fun U =>
      lintegral_mul_const' _ _ enorm_ne_top
    simp only [e]
    rw [lintegral_mul_const' _ _ enorm_ne_top, inner_eq hIkL hJn hn I hθ hM hM0 x₀ h y]
    gcongr
    rw [enorm_le_iff_norm_le]
    have h3 := hNd (jn hn (ww W x₀ h) (mm (ww W x₀ h) y + 0))
    rw [jn_first] at h3
    exact h3.trans (Complex.re_le_norm _)
  rw [hasFiniteIntegral_iff_enorm]
  calc ∫⁻ p, ‖core hn I x₀ Φ η p‖ₑ ∂(I.νK.prod (Q0 I μ))
      ≤ ∫⁻ p, F p ∂(I.νK.prod (Q0 I μ)) := lintegral_mono hle
    _ = ∫⁻ y, ∫⁻ h, ∫⁻ U, ∫⁻ k : I.l.K, F (k, h, U, y) ∂I.νK ∂I.μ₁ ∂I.m ∂μ :=
        (hFub I.l.K (GA D W) (Mx D t n) (Mx D W.rank t) I.νK I.m I.μ₁ μ).2 F hFm
    _ ≤ ∫⁻ y, ∫⁻ h, ‖N (ww W x₀ h)‖ₑ * ‖η y‖ₑ ∂I.m ∂μ :=
        lintegral_mono fun y => lintegral_mono fun h => hin y h
    _ = (∫⁻ h, ‖N (ww W x₀ h)‖ₑ ∂I.m) * ∫⁻ y, ‖η y‖ₑ ∂μ := by
        simp only [lintegral_mul_const' _ _ enorm_ne_top]
        rw [lintegral_const_mul' _ _ hN'.ne]
    _ < ⊤ := ENNReal.mul_lt_top hN' hη'

end GlobalTheory.CompanionTheory.ColumnSplitting

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LFunctionSideEquidistribution
section
noncomputable section

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology Filter PositivityTheory.Rg.Base1 GroundTheory.Global GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil
open scoped TensorProduct ENNReal NNReal Matrix Classical

namespace GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

theorem nm_mul {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    {x x' : (AF F ⊗[F] E)ˣ} {n n' : (AF F)ˣ} (h : IsNm σ x n) (h' : IsNm σ x' n') : IsNm σ (x * x') (n * n') := by
  unfold IsNm at *
  have e : ((n * n' : (AF F)ˣ) : AF F) ⊗ₜ[F] (1 : E) = ((n : AF F) ⊗ₜ[F] (1 : E)) * ((n' : AF F) ⊗ₜ[F] (1 : E)) := by
    simp
  rw [e, h, h']
  simp only [Units.val_mul, map_mul]
  ring

theorem nm_ofF {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
    (a : (AF F)ˣ) : IsNm σ (ofF a) (a * a) := by
  unfold IsNm
  have e : ((ofF a : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) = (a : AF F) ⊗ₜ[F] (1 : E) := rfl
  rw [e]
  simp [sigR]

theorem ray_sq {F : Type} [Field F] [NumberField F] {θ : ℝ →+* Ainf F} {r : ℝ → (AF F)ˣ} (hr : IsRay θ r) {ε : ℝ}
    (hε : 0 < ε) : r (ε ^ 2) = r ε * r ε := by
  apply Units.ext
  have h1 := hr ε hε
  have h2 := hr (ε ^ 2) (by positivity)
  refine Prod.ext ?_ ?_
  · change ((r (ε ^ 2) : AF F)).1 = (r ε : AF F).1 * (r ε : AF F).1
    rw [h1.1, h2.1, ← map_mul, sq]
  · change ((r (ε ^ 2) : AF F)).2 = (r ε : AF F).2 * (r ε : AF F).2
    rw [h1.2, h2.2, one_mul]

theorem md_mul {F : Type} [Field F] [NumberField F] (a b : (AF F)ˣ) : md (a * b) = md a * md b := by
  simp [md]

theorem md_pos {F : Type} [Field F] [NumberField F] (a : (AF F)ˣ) : 0 < md a := (IdeleGroup.ideleModule F a).2

theorem bound : PositivityTheory.Rg.Mass.Equi → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (J : Matrix (Fin 1) (Fin 1) E), IsHermND σ J → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (li : Measure (Ainf F)) (lam : ∀ v : HeightOneSpectrum (𝓞 F), Measure (Fv F v)), IsStdInf li → (∀ v, IsStdV v (lam v)) → ∀ θ : ℝ →+* Ainf F, Continuous θ → ∀ r, IsRay θ r → ∀ (S : Finset (HeightOneSpectrum (𝓞 F))) (φ : (Fin 1 → Fin 1 → Ainf F ⊗[F] E) → ℝ) (A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin 1 → Fin 1 → Fv F v ⊗[F] E)), IsTest σ J b S φ A →
    ∃ C : ℝ≥0, ∀ (y : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ), IsNm σ y n → ENNReal.ofReal (md n) * Th φ A y ≤ C := by
  intro hEq F E _ _ _ _ _ σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT
  obtain ⟨K, hK, hdec⟩ := GlobalTheory.T.idele_class_compact_ray_decomposition F E σ hcm θ hθ r hr
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish.th_eq_zero_of_large_module F E σ hcm J hJ d b S φ A hT
  obtain ⟨C, hC⟩ := _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.UnitBd.unit_bound hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT K hK (max 1 R)
  refine ⟨C, fun y n hn => ?_⟩
  obtain ⟨q, k, ε, hk, hε, rfl, hm⟩ := hdec y n hn
  rw [_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul]
  by_cases h : ε ≤ max 1 R
  · rw [hm]
    exact hC k hk ε hε h
  · have h1 : 1 < ε := lt_of_le_of_lt (le_max_left _ _) (not_le.1 h)
    have h2 : R < ε := lt_of_le_of_lt (le_max_right _ _) (not_le.1 h)
    have h3 : 2 * Module.finrank ℚ F ≠ 0 := by
      have := Module.finrank_pos (R := ℚ) (M := F)
      omega
    have h4 : ε ≤ ε ^ (2 * Module.finrank ℚ F) := le_self_pow₀ h1.le h3
    have h5 := hR _ n hn (by rw [hm]; linarith)
    rw [_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Th_ofE_mul] at h5
    rw [h5, mul_zero]
    exact bot_le

theorem lside : PositivityTheory.Rg.Mass.Equi → LSide := by
  intro hEq F E _ _ _ _ _ σ J d b li lam μ 𝓕 mi m hcm hJ hli hlam hμ h𝓕 hmi hm θ hθ r hr S φ A hT
  obtain ⟨⟨_, _, _⟩, -⟩ := _root_.GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, -, -, -, hB, -, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have hG := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hcm 1 J hJ (AF F)
  haveI : IsTopologicalGroup (HA (AF F) σ J) := hG.1
  haveI : LocallyCompactSpace (HA (AF F) σ J) := hG.2.1
  haveI : SecondCountableTopology (HA (AF F) σ J) := hG.2.2.1
  haveI : T2Space (HA (AF F) σ J) := hG.2.2.2.1
  haveI : BorelSpace (HA (AF F) σ J) := hG.2.2.2.2.1
  have hfin : μ 𝓕 < ⊤ := ((_root_.GlobalTheory.CompanionTheory.SW.finVol_unitaryGroup F E σ hcm 1 J hJ).2 μ hμ).2 𝓕 h𝓕
  have : μ.IsHaarMeasure := hμ
  let Γ : Subgroup (HA (AF F) σ J) := HFinIn (AF F) σ J
  have : Countable Γ := (_root_.GlobalTheory.CompanionTheory.SW.rational_countable_discrete F E σ hcm 1 J hJ).1
  have h𝓕' : IsFundamentalDomain Γ 𝓕 μ := h𝓕
  have h0 : μ 𝓕 ≠ 0 := (_root_.GlobalTheory.CompanionTheory.SW.LatticeUnimod.unimodular_of_isFundamentalDomain (HA (AF F) σ J) Γ μ 𝓕 h𝓕' hfin).1
  have hft : μ 𝓕 ≠ ⊤ := hfin.ne
  obtain ⟨C, hC⟩ := bound hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT
  obtain ⟨R, hR⟩ := _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.Vanish.th_eq_zero_of_large_module F E σ hcm J hJ d b S φ A hT
  have hM := fun x => _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.mean_eq_lint F E σ hcm J hJ μ 𝓕 hμ h𝓕 d b S φ A hT x
  have hnm : ∀ (x : (AF F ⊗[F] E)ˣ) (n : (AF F)ˣ) (h : HA (AF F) σ J), IsNm σ x n → IsNm σ (x * ue (AF F) σ J h⁻¹) n :=
    fun x n h hn => by simpa using nm_mul hn (_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.isNm_ue_one F E σ hcm J hJ h⁻¹)
  have hcan : (μ 𝓕)⁻¹ * μ 𝓕 = 1 := ENNReal.inv_mul_cancel h0 hft
  refine ⟨⟨C, fun x n hn => ?_⟩, ⟨R, fun x n hn hRn => ?_⟩, fun x n hn => ?_⟩
  · rw [(hM x).1, mul_left_comm, ← lintegral_const_mul _ (hM x).2]
    calc _ ≤ (μ 𝓕)⁻¹ * ∫⁻ _ in 𝓕, (C : ℝ≥0∞) ∂μ := by
            gcongr with h
            exact hC _ n (hnm x n h hn)
      _ = C := by
            rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (C : ℝ≥0∞), ← mul_assoc, hcan, one_mul]
  · rw [(hM x).1]
    have : ∀ h : HA (AF F) σ J, Th φ A (x * ue (AF F) σ J h⁻¹) = 0 := fun h => hR _ n (hnm x n h hn) hRn
    simp [this]
  · set m := 2 * Module.finrank ℚ F with hmdef
    have hmr := (_root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.MdRay.norm_md_ray F hcm.1 θ hθ r hr).2
    have hmd : ∀ ε : ℝ, 0 < ε → md (n * r (ε ^ 2)) = md n * ε ^ m := fun ε hε => by
      rw [md_mul, hmr _ (by positivity), hmdef, pow_mul]
    have hne : ∀ ε : ℝ, 0 < ε → IsNm σ (x * ofF (r ε)) (n * r (ε ^ 2)) := fun ε hε => by
      rw [ray_sq hr hε]
      exact nm_mul hn (nm_ofF _)
    set f : ℝ → HA (AF F) σ J → ℝ≥0∞ := fun ε h =>
      ENNReal.ofReal (md (n * r (ε ^ 2))) * Th φ A (x * ofF (r ε) * ue (AF F) σ J h⁻¹) with hf
    have hfm : ∀ ε, Measurable (f ε) := fun ε => (hM _).2.const_mul _
    have hbd : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ h, f ε h ≤ C := by
      filter_upwards [self_mem_nhdsWithin] with ε hε h
      exact hC _ _ (hnm _ _ h (hne ε hε))
    have hpt : ∀ h, Tendsto (fun ε => f ε h) (𝓝[>] 0) (𝓝 (vol b li lam S φ A)) := fun h => by
      have hy := hnm x n h hn
      have e0 : ∀ ε, x * ofF (r ε) * ue (AF F) σ J h⁻¹ = x * ue (AF F) σ J h⁻¹ * ofF (r ε) := fun ε => by
        rw [mul_assoc, mul_comm (ofF (r ε)), ← mul_assoc]
      have hT1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), Th φ A (x * ue (AF F) σ J h⁻¹ * ofF (r ε)) ≠ ⊤ := by
        filter_upwards [hbd, self_mem_nhdsWithin] with ε h1 h2 h3
        have h4 := h1 h
        simp only [hf, e0, h3] at h4
        rw [ENNReal.mul_top (by simpa using md_pos _)] at h4
        exact absurd h4 (not_le.2 ENNReal.coe_lt_top)
      have hL := _root_.GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil.FixedUnit.equi_unit hEq F E σ hcm J hJ d b li lam hli hlam θ hθ r hr S φ A hT _ n hy hT1
      have hmn : ENNReal.ofReal (md n) ≠ 0 := by simpa using md_pos n
      have h2 := ENNReal.Tendsto.const_mul hL (Or.inr (ENNReal.ofReal_ne_top (r := md n)))
      rw [← mul_assoc, ENNReal.mul_inv_cancel hmn ENNReal.ofReal_ne_top, one_mul] at h2
      refine h2.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with ε hε
      have hε' : (0 : ℝ) < ε := hε
      simp only [hf]
      rw [e0, hmd ε hε', ENNReal.ofReal_mul (md_pos n).le]
      exact (mul_assoc _ _ _).symm
    have hlim : Tendsto (fun ε => ∫⁻ h in 𝓕, f ε h ∂μ) (𝓝[>] 0) (𝓝 (∫⁻ _ in 𝓕, vol b li lam S φ A ∂μ)) := by
      refine tendsto_lintegral_filter_of_dominated_convergence (fun _ => (C : ℝ≥0∞))
        (Eventually.of_forall hfm) (hbd.mono fun ε h => ae_of_all _ h) ?_ (ae_of_all _ hpt)
      rw [lintegral_const, Measure.restrict_apply_univ]
      exact ENNReal.mul_ne_top ENNReal.coe_ne_top hft
    have h2 := ENNReal.Tendsto.const_mul hlim (Or.inr (ENNReal.inv_ne_top.2 h0)) (a := (μ 𝓕)⁻¹)
    rw [lintegral_const, Measure.restrict_apply_univ, mul_comm (vol b li lam S φ A), ← mul_assoc, hcan, one_mul] at h2
    refine h2.congr fun ε => ?_
    simp only [hf]
    rw [(hM _).1, lintegral_const_mul _ (hM _).2, mul_left_comm]
    rfl

end GlobalTheory.CompanionTheory.SW.RankOneSiegelWeil

end
end

