module

public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0228
public import Development.AbelianVarietyTheory.Definitions.Divisors.BasePlaceNotMemChiGridBadPlaces
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0315
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ValuationXiZeroEqOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0400
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelWeilUnitaryConvergent
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0471
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0140
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0194
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0477
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0557
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0301
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0439
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0432
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0015
public import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0352
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWeilRepresentationVacuumCosetVectorsGrid
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0771
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHasLocalSmall
public import Development.AbelianVarietyTheory.Definitions.Divisors.BplusOfEquivariant
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IdempotentMulEqZeroOfOrthogonal
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0558

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.DepthLatticeGridCoreIffFirstRowExtByZero
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin

noncomputable section

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem gen_negSp (S T : HSp D) (α : Af D.host.F) (a : D.host.E) (s : Fin S.rank → D.host.E) (t : Fin T.rank → D.host.E) :
    (Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * (negSp S).gram k j) : WO S T) =
      -(Matrix.of fun i j => pairA D.host.F 0 α ⊗ₜ[D.host.F] (a * t i * ∑ k, star (s k) * S.gram k j) : WO S T) := by
  ext i j; simp [negSp_gram, Finset.sum_neg_distrib, TensorProduct.tmul_neg]

theorem latO_negSp (S T : HSp D) (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    (P : HeightOneSpectrum (𝓞 D.host.F) → Prop) : latO (negSp S) T LS LT P = latO S T LS LT P := by
  apply le_antisymm
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    show _ ∈ latO S T LS LT P
    rw [gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)
  · refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩
    rw [← neg_neg (Matrix.of _), ← gen_negSp S T α a s t]
    exact neg_mem (AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩)

theorem latO_mul_left {S T T' : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    {LT' : Submodule (𝓞 D.host.E) (Fin T'.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (A : Matrix (Fin T'.rank) (Fin T.rank) D.host.E) (hA : ∀ t ∈ LT, A *ᵥ t ∈ LT') {u : WO S T}
    (hu : u ∈ latO S T LS (LT : Set _) P) : (rat A : Mx D T'.rank T.rank) * u ∈ latO S T' LS (LT' : Set _) P :=
  GlobalTheory.OverTgt.mul_mem_latO (rat A) (fun _ hy => GlobalTheory.SeeSaw.CoreGlue.rat_mulVec_mem A hA hy) hu

theorem latO_mul_right {S S' T : HSp D} {LS : Set (Fin S.rank → D.host.E)} {LS' : Set (Fin S'.rank → D.host.E)}
    {LT : Set (Fin T.rank → D.host.E)} {P : HeightOneSpectrum (𝓞 D.host.F) → Prop}
    (M : Matrix (Fin S.rank) (Fin S'.rank) D.host.E)
    (hM : ∀ s ∈ LS, ∃ s' ∈ LS', ∀ j, ∑ l, (∑ k, star (s k) * S.gram k l) * M l j = ∑ k, star (s' k) * S'.gram k j)
    {u : WO S T} (hu : u ∈ latO S T LS LT P) : u * (rat M : Mx D S.rank S'.rank) ∈ latO S' T LS' LT P := by
  induction hu using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨α, hαi, hα, a, ha, s, hs, t, ht, rfl⟩ := hw
    obtain ⟨s', hs', hss⟩ := hM s hs
    refine AddSubgroup.subset_closure ⟨α, hαi, hα, a, ha, s', hs', t, ht, ?_⟩
    ext i j
    rw [Matrix.mul_apply, Matrix.of_apply, ← hss j, Finset.mul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Matrix.of_apply]
    show _ * incA D (M l j) = _
    rw [GlobalTheory.RankZeroVac.incA_tmul', Algebra.TensorProduct.tmul_mul_tmul, mul_one, mul_assoc]
  | zero => rw [Matrix.zero_mul]; exact zero_mem _
  | add x y _ _ hx hy => rw [Matrix.add_mul]; exact add_mem hx hy
  | neg x _ hx => rw [Matrix.neg_mul]; exact neg_mem hx

theorem hatMx_mul_left {m m' n : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)} {Λ'' : Submodule (𝓞 D.host.E) (Fin m' → D.host.E)}
    (A : Matrix (Fin m') (Fin m) D.host.E) (hA : ∀ t ∈ Λ', A *ᵥ t ∈ Λ'') {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : (rat A : Mx D m' m) * x ∈ hatMx (I • homLat Λ Λ'') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I 1 A (fun y hy => by rwa [Matrix.one_mulVec]) hA x hx
  rwa [rat_one, Matrix.mul_one] at h

theorem hatMx_mul_right {m n n' : ℕ} (I : Ideal (𝓞 D.host.E)) {Λ : Submodule (𝓞 D.host.E) (Fin n → D.host.E)}
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin n' → D.host.E)} {Λ' : Submodule (𝓞 D.host.E) (Fin m → D.host.E)}
    (N : Matrix (Fin n) (Fin n') D.host.E) (hN : ∀ s ∈ Λ₁, N *ᵥ s ∈ Λ) {x : Mx D m n}
    (hx : x ∈ hatMx (I • homLat Λ Λ')) : x * (rat N : Mx D n n') ∈ hatMx (I • homLat Λ₁ Λ') := by
  have h := GlobalTheory.TwistHatMx.rat_conj_mem_hatMx I N 1 hN (fun y hy => by rwa [Matrix.one_mulVec]) x hx
  rwa [rat_one, Matrix.one_mul] at h

theorem wittEmbedding_preserves_hermitianForm {S S₀ : HSp D} {ρ : ℕ} (d : HypDec S S₀ ρ) (s : Fin S₀.rank → D.host.E) (j : Fin S₀.rank) :
    ∑ l, (∑ k, star ((d.i₀ *ᵥ s) k) * S.gram k l) * d.i₀ l j = ∑ k, star (s k) * S₀.gram k j := by
  have h : Matrix.vecMul (Matrix.vecMul (star (d.i₀ *ᵥ s)) S.gram) d.i₀ = Matrix.vecMul (star s) S₀.gram := by
    rw [Matrix.star_mulVec, Matrix.vecMul_vecMul, Matrix.vecMul_vecMul, ← Matrix.mul_assoc, d.iso]
  have hj := congrFun h j
  simpa only [Matrix.vecMul, dotProduct, Pi.star_apply] using hj

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem std_zA_lat {F : Frames G} (hF : Std F) : (∀ y ∈ G.Λ (.grid 0 0), F.oz.iA *ᵥ y ∈ G.Λ (.core 0)) ∧
    ∀ x ∈ G.Λ (.core 0), F.oz.qA *ᵥ x ∈ G.Λ (.grid 0 0) := by
  have hΛ : G.Λ (.core 0) = sumLat (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι) (L.ΛY 0) G.sp.dec0.a (fun _ => 1) :=
    G.sp.lat0
  have hqi : F.oz.qA * F.oz.iA = 1 := rat_injective (by rw [rat_mul, rat_one]; exact F.oz.pA_jA)
  have hperp := G.sp.dec0.perp
  have hqa : F.oz.qA * G.sp.dec0.a = 0 := by
    change (HSpace.gram (Yc D 0))⁻¹ * (F.oz.iAᴴ * HSpace.gram (G.V (.core 0))) * G.sp.dec0.a = 0
    rw [hF.zA, Matrix.mul_assoc, Matrix.mul_assoc]
    have hp : (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ * HSpace.gram (G.sp.P 0).sp * G.sp.dec0.a = 0 := hperp
    rw [← Matrix.mul_assoc (frameMat (G.sp.P 0).sp (Yc D 0) G.sp.dec0.ι)ᴴ, hp, Matrix.mul_zero]
  refine ⟨fun y hy => ?_, fun x hx => ?_⟩
  · rw [hΛ]
    refine ⟨y, hy, 0, fun _ => (FractionalIdeal.mem_one_iff _).2 ⟨0, map_zero _⟩, ?_⟩
    rw [Matrix.mulVec_zero, add_zero, hF.zA]
  · rw [hΛ] at hx
    obtain ⟨y, hy, u, -, rfl⟩ := hx
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← hF.zA, hqi, hqa, Matrix.one_mulVec,
      Matrix.zero_mulVec, add_zero]
    exact hy

theorem std_aJ_lat {F : Frames G} (hF : Std F) (h : 2 * 0 + 2 ≤ D.R.m) :
    (∀ y ∈ G.Λ (.core 1), (F.dJ 0 h).i₀ *ᵥ y ∈ G.Λ (.grid 1 0)) ∧
    (∀ x ∈ G.Λ (.grid 1 0), ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y) ∧
    ∀ x ∈ G.Λ (.grid 1 0), (F.dJ 0 h).q0 *ᵥ x ∈ G.Λ (.core 1) := by
  have h1 : 1 ≤ D.R.m := by omega
  have hΛ : G.Λ (.grid 1 0) = sumLat (frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι) (G.Λ (.core 1))
      (G.colDec 1 le_rfl h1).a (stairId (G.pl.stA sc) (G.pl.stAbar sc) (1 - 1)) := G.sp.colLat 1 le_rfl h1
  have hi : (F.dJ 0 h).i₀ = frameMat (G.V (.grid 1 0)) (G.V (.core 1)) (G.colDec 1 le_rfl h1).ι := hF.aJ 0 h
  have hqi : (F.dJ 0 h).q0 * (F.dJ 0 h).i₀ = 1 := rat_injective (by rw [rat_mul, rat_one]; exact (F.dJ 0 h).p0_j0)
  have mem : ∀ x, x ∈ G.Λ (.grid 1 0) ↔ ∃ y ∈ G.Λ (.core 1), x = (F.dJ 0 h).i₀ *ᵥ y := by
    intro x
    rw [hΛ, hi]
    constructor
    · rintro ⟨y, hy, u, -, rfl⟩
      refine ⟨y, hy, ?_⟩
      have : (G.colDec 1 le_rfl h1).a *ᵥ u = 0 := by
        funext i; simp [Matrix.mulVec, dotProduct]
      rw [this, add_zero]
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y, hy, 0, fun p => p.elim0, by rw [Matrix.mulVec_zero, add_zero]⟩
  refine ⟨fun y hy => (mem _).2 ⟨y, hy, rfl⟩, fun x hx => (mem x).1 hx, fun x hx => ?_⟩
  obtain ⟨y, hy, rfl⟩ := (mem x).1 hx
  rwa [Matrix.mulVec_mulVec, hqi, Matrix.one_mulVec]

end GlobalTheory.CoreRowLat

namespace GlobalTheory.CoreRowLat

variable {D : D7}

theorem depthLattice_generalPosition_iff_extByZero {P₁ P₀ Y Lz S : HSp D} (o : OrthDec P₀ Y Lz) (d : HypDec S P₁ 0)
    {Λ₁ : Submodule (𝓞 D.host.E) (Fin P₁.rank → D.host.E)} {Λ₀ : Submodule (𝓞 D.host.E) (Fin P₀.rank → D.host.E)}
    {ΛY : Submodule (𝓞 D.host.E) (Fin Y.rank → D.host.E)} {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)}
    (I : Ideal (𝓞 D.host.E)) (Q : AE D → Prop)
    (hiA : ∀ y ∈ ΛY, o.iA *ᵥ y ∈ Λ₀) (hqA : ∀ x ∈ Λ₀, o.qA *ᵥ x ∈ ΛY)
    (hi0 : ∀ y ∈ Λ₁, d.i₀ *ᵥ y ∈ ΛS) (hq0 : ∀ x ∈ ΛS, ∃ y ∈ Λ₁, x = d.i₀ *ᵥ y) (hq0' : ∀ x ∈ ΛS, d.q0 *ᵥ x ∈ Λ₁)
    (a : WO P₁ Y) :
    (o.jA * a ∈ latO (negSp P₁) P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀)) ↔
    (d.ext0 Y a ∈ latO (negSp S) Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) ∧
      ∀ e : AE D, Q e → e • d.ext0 Y a ∈ hatMx (I • homLat ΛS ΛY)) := by
  have hpj : d.p0 * (rat d.i₀ : Mx D _ _) = 1 := d.p0_j0
  have hpA : (rat o.qA : Mx D _ _) * o.jA = 1 := o.pA_jA
  have cB : ∀ x : WO P₁ Y, x * d.p0 * (rat d.i₀ : Mx D _ _) = x := fun x => by
    rw [Matrix.mul_assoc, hpj, Matrix.mul_one]
  have cA : ∀ x : WO P₁ Y, (rat o.qA : Mx D _ _) * (o.jA * x) = x := fun x => by
    rw [← Matrix.mul_assoc, hpA, Matrix.one_mul]
  have ext : d.ext0 Y a = a * d.p0 := rfl
  rw [ext, latO_negSp, latO_negSp]
  have hA1 : o.jA * a ∈ latO P₁ P₀ (Λ₁ : Set _) (Λ₀ : Set _) (fun _ => True) ↔
      a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      have := latO_mul_left o.qA hqA hu
      rwa [cA] at this
    · intro hu; exact latO_mul_left o.iA hiA hu
  have hB1 : a ∈ latO P₁ Y (Λ₁ : Set _) (ΛY : Set _) (fun _ => True) ↔
      a * d.p0 ∈ latO S Y (ΛS : Set _) (ΛY : Set _) (fun _ => True) := by
    constructor
    · intro hu
      exact latO_mul_right d.q0 (fun s hs => ⟨d.i₀ *ᵥ s, hi0 s hs, fun j => GlobalTheory.RankZeroVac.wittDecomposition_gram_projection_identity d s j⟩) hu
    · intro hu
      have := latO_mul_right d.i₀ (fun s hs => by
        obtain ⟨y, hy, rfl⟩ := hq0 s hs
        exact ⟨y, hy, fun j => wittEmbedding_preserves_hermitianForm d y j⟩) hu
      rwa [cB] at this
  have hA2 : ∀ e : AE D, e • (o.jA * a) ∈ hatMx (I • homLat Λ₁ Λ₀) ↔ e • a ∈ hatMx (I • homLat Λ₁ ΛY) := by
    intro e
    rw [← Matrix.mul_smul]
    constructor
    · intro hx
      have := hatMx_mul_left I o.qA hqA hx
      rwa [cA] at this
    · intro hx; exact hatMx_mul_left I o.iA hiA hx
  have hB2 : ∀ e : AE D, e • a ∈ hatMx (I • homLat Λ₁ ΛY) ↔ e • (a * d.p0) ∈ hatMx (I • homLat ΛS ΛY) := by
    intro e
    rw [← Matrix.smul_mul]
    constructor
    · intro hx; exact hatMx_mul_right I d.q0 hq0' hx
    · intro hx
      have := hatMx_mul_right I d.i₀ hi0 hx
      rwa [cB] at this
  exact and_congr (hA1.trans hB1) (forall_congr' fun e => imp_congr_right fun _ => (hA2 e).trans (hB2 e))

variable {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

theorem jA_mem_latCore_iff : OnStd fun {D} _ _ _ {G} _ F => ∀ (h : 2 * 0 + 2 ≤ D.R.m) (a : WO (G.V (.core 1)) (Yc D 0)),
    F.oz.jA * a ∈ latCore G 0 ↔ (F.dJ 0 h).ext0 (Yc D 0) a ∈ latRow G 0 := by
  intro D _ T L _ _ sc G W M _ F hF h a
  obtain ⟨hiA, hqA⟩ := std_zA_lat hF
  obtain ⟨hi0, hq0, hq0'⟩ := std_aJ_lat hF h
  exact depthLattice_generalPosition_iff_extByZero F.oz (F.dJ 0 h) G.modul (fun e => IsIdemSum e G.pl.W0) hiA hqA hi0 hq0 hq0' a

end GlobalTheory.CoreRowLat

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.EvenThetaChainUpwardLiftHeckeParamTransferred
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.EvenOnto
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.EvenOnto

theorem PiLocalization₂.val_autCusp {D : D7} (c : Com D) (s : PiLocalization₂ D) (u : s.CC c) (x : SmT s.M) :
    IsAutFunSm c.θ s.V (PiLocalization₂.val u x) ∧ IsCuspFun s.V (PiLocalization₂.val u x) := by
  have hT := (GlobalTheory.MultMem.mem_mult_iff D c.θ s.V _ s.M _ _ _).1 ((mem_multT _ _ _ _ _).1 u.2)
  have key : ∀ y : SmT s.M, PiLocalization₂.val u y =
      (PiTensorProduct.lift (PiTensorProduct.lift.symm (u : SmT s.M →ₗ[ℂ] (GA D s.V → ℂ)))) y := by
    intro y; rw [LinearEquiv.apply_symm_apply]
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
    rw [key, map_smul, PiTensorProduct.lift.tprod]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_smul r (hT.aut f), GlobalTheory.MultMem.isCuspFun_smul r (hT.cusp f)⟩
  | add x y hx hy =>
    have e : PiLocalization₂.val u (x + y) = PiLocalization₂.val u x + PiLocalization₂.val u y := map_add _ _ _
    rw [e]
    exact ⟨GlobalTheory.MultMem.isAutFunSm_add hx.1 hy.1,
      GlobalTheory.MultMem.isCuspFun_add hx.1.toIsAutFun hy.1.toIsAutFun hx.2 hy.2⟩

theorem upPar_of_transfer : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Hk3.HoweUnram → ∀ D : D7, UpPar D := by
  intro hRD hHowe D c hc k hk s s' hs hs' p hp u B φ hu v _ hne
  set y := PiLocalization₂.val u v with hy
  have hy0 : y ≠ 0 := by
    intro h; apply hne; funext x; simp [Step.up, h]
  have hyB : GlobalTheory.LFun.IsParamFunV s.V c.S (fun g => conj (y g)) B := hu.2 v hy0
  have hconj : (fun x => conj (p.up φ y x)) =
      fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν := by
    funext x; simp only [Step.up]; rw [← integral_conj]; congr 1; funext g; simp [map_mul]
  have hne' : (fun x => ∫ g in s.fd, thetaKO p.ω g x (p.pt φ) * conj (y g) ∂s.ν) ≠ 0 := by
    rw [← hconj]; intro h; apply hne; funext x; simpa using congrFun h x
  have hrank : s'.V.rank = s.V.rank + c.t := by rw [hs'.rank, hs.rank]; ring
  have hYA := PiLocalization₂.val_autCusp c s u v
  have hunr : ∀ w0 ∉ c.S, ∀ w' : HeightOneSpectrum (𝓞 D.host.E), w'.under (𝓞 D.host.F) = w0 →
      GlobalTheory.LFun.UnrAt (c.χ k) w' ∧ GlobalTheory.LFun.UnrAt (c.χ k) w' := by
    intro w0 hw0 w' hw'
    have h1 := hc.unr k hk w' (by simpa [GlobalTheory.LFun.above, hw'] using hw0)
    exact ⟨h1, h1⟩
  unfold ParFun
  rw [hconj]
  intro w0 hw0 w h
  have hw0' : w0 ∉ c.S := by simpa using hw0
  exact _root_.GlobalTheory.ChainOnto.thetaIntegral_param hRD D (_root_.GlobalTheory.ChainOnto.transferOn_all hHowe D) c.ψ c.θ s.V s'.V _ _ p.ω hc.inf hp.pre.weil c.t hrank s.ν s.fd
    hs.haar hs.fund w0 (hunr w0 hw0') w h (p.pt φ)
    ((_root_.GlobalTheory.EvenOnto.fock_sph_vac D c hc k hk s s' hs hs' p hp φ).2.2.2 w0 hw0') y (B w) hYA.1 hYA.2 (hyB w0 hw0 w h) hne'

end GlobalTheory.EvenOnto

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsLocalOperatorThetaQuotientFinitePlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct ComplexConjugate

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_localOperator_thetaQuotient_finitePlace : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (a a' : ℕ)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V Γ.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ Γ.V' Γ.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs Γ Xc om om' R Rf →
    ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F)), ∀ hv ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ Γ.W (GlobalTheory.AdelicU.evFin F v),
    ∃ T : Module.End ℂ (Rf.Pi v),
      (∀ φ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om (1, hv)) φ φ₁ → Rf.p v φ₁ = T (Rf.p v φ)) ∧
      ∀ φ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v), ∀ φ₁ ∈ GlobalTheory.WeilM.SB (Fin a' × Fin (a + a') → Fv F v),
        GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Acts (GlobalTheory.AdelicU.evFin F v) (om' (1, hv)) φ φ₁ → Rf.p' v φ₁ = T (Rf.p' v φ) := by
  first | exact @GlobalTheory.LocalDescent.exists_localOp | exact GlobalTheory.LocalDescent.exists_localOp | (intros; apply GlobalTheory.LocalDescent.exists_localOp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstRowCosetVectorsIsLocalThetaVector
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.FlipRun
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.RowLocVec

variable {D : D7}


open GlobalTheory.HalfProd GlobalTheory.ExportSeries.RestrictHalfModel in
theorem prodHalf_halfInd {m n : ℕ} {a b : AE D} (ha : a * a = a) (hb : b * b = b) {Λ : AddSubgroup (Mx D m n)}
    (hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ) :
    prodHalf a b (halfInd b Λ) (halfInd a Λ) = halfInd (a + b) Λ := by
  classical
  funext x
  rw [prodHalf_apply]
  by_cases hx : IsHalf (a + b) x
  · have hx' : a • x + b • x = x := by rw [← add_smul]; exact (isHalf_iff' _ _).1 hx
    rw [if_pos hx, mul_one]
    unfold halfInd
    by_cases hxΛ : x ∈ Λ
    · rw [if_pos ⟨hΛ a ha x hxΛ, isHalf_smul ha x⟩, if_pos ⟨hΛ b hb x hxΛ, isHalf_smul hb x⟩, if_pos ⟨hxΛ, hx⟩, one_mul]
    · rw [if_neg (show ¬ (x ∈ Λ ∧ IsHalf (a + b) x) from fun h => hxΛ h.1)]
      by_cases h1 : a • x ∈ Λ
      · rw [if_neg (show ¬ (b • x ∈ Λ ∧ IsHalf b (b • x)) from fun h => hxΛ (hx' ▸ add_mem h1 h.1)), mul_zero]
      · rw [if_neg (show ¬ (a • x ∈ Λ ∧ IsHalf a (a • x)) from fun h => h1 h.1), zero_mul]
  · rw [if_neg hx, mul_zero]
    unfold halfInd
    rw [if_neg (show ¬ (x ∈ Λ ∧ IsHalf (a + b) x) from fun h => hx h.2)]

theorem exists_compl_idem {e e₀ : AE D} {P P₀ : Finset (Pl D.host.E)} (hsub : P₀ ⊆ P) (he : IsIdemSum e P)
    (he₀ : IsIdemSum e₀ P₀) : ∃ b, e = e₀ + b ∧ b * b = b ∧ e₀ * b = 0 := by
  classical
  obtain ⟨⟨es, h1, rfl⟩, -⟩ := he
  obtain ⟨⟨es₀, h1₀, rfl⟩, -⟩ := he₀
  have heq : ∑ Q ∈ P₀, es₀ Q = ∑ Q ∈ P₀, es Q := Finset.sum_congr rfl fun Q hQ =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ Q Q (h1₀ Q hQ) (h1 Q (hsub hQ))).1 rfl
  have horth : ∀ Q ∈ P, ∀ Q' ∈ P, Q ≠ Q' → es Q * es Q' = 0 := fun Q hQ Q' hQ' h =>
    (GlobalTheory.PlaceIdemUniq.idemAt_unique_orth D _ _ Q Q' (h1 Q hQ) (h1 Q' hQ')).2 h
  refine ⟨∑ Q ∈ P \ P₀, es Q, ?_, ?_, ?_⟩
  · rw [heq, ← Finset.sum_sdiff hsub, add_comm]
  · exact (⟨_, P \ P₀, es, fun Q hQ => (h1 Q (Finset.sdiff_subset hQ)).1,
      fun Q hQ Q' hQ' hne => horth Q (Finset.sdiff_subset hQ) Q' (Finset.sdiff_subset hQ') (Ne.symm hne), rfl⟩ :
        GlobalTheory.PlaceModelSum.IsOrthSum _) |> GlobalTheory.PlaceModelSum.IsOrthSum.idem
  · rw [heq, Finset.sum_mul_sum]
    exact Finset.sum_eq_zero fun Q hQ => Finset.sum_eq_zero fun Q' hQ' =>
      horth Q (hsub hQ) Q' (Finset.sdiff_subset hQ') fun h => (Finset.mem_sdiff.1 hQ').2 (h ▸ hQ)


open GlobalTheory.HalfProd in
theorem isThetaAt_extend {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} (hψ : IsStdChar D ψ (-1))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT) {a b : AE D} {P : Finset (Pl D.host.E)} (hP : IsIdemSum (a + b) P)
    (ha : a * a = a) (hb : b * b = b) (hab : a * b = 0) {f₀ Φ f : WO S T → ℂ}
    (hvac : IsLatVac (heisO ψ S T) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) f₀)
    (hΦ : IsSBHalf a (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) Φ)
    (hf : IsThetaAt ψ (symplO S T) (heisO ψ S T) a
      (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀ Φ f) :
    IsSBHalf (a + b) (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)
        (prodHalf a b (halfInd b (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) Φ) ∧
      IsThetaAt ψ (symplO S T) (heisO ψ S T) (a + b)
        (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True) 1 f₀
        (prodHalf a b (halfInd b (latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True)) Φ) f := by
  set Λ := latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True with hΛdef
  have hΛ : ∀ e : AE D, e * e = e → ∀ u ∈ Λ, e • u ∈ Λ := fun e he u hu => GlobalTheory.PlaceModelSum.idem_smul_latO he hu
  have hΨ := GlobalTheory.isSBHalf_halfInd b Λ
  refine ⟨isSBHalf_prodHalf ha hb hΛ hΨ hΦ, (GlobalTheory.PlaceModelSum.isOrthSum_of_isIdemSum hP).exists_model hψ hS hT hP.2 hvac,
    fun T₀ hT₀ => ?_⟩
  have hm := isPlaceModel_prodHalf ha hb hab hΛ hΨ hT₀
  have key : T₀ (prodHalf a b (halfInd b Λ) (halfInd a Λ)) = f₀ := by
    rw [prodHalf_halfInd ha hb hΛ]
    have := hT₀.vac
    rwa [one_smul] at this
  rw [key] at hm
  exact hf.2 _ hm

end GlobalTheory.RowLocVec

namespace GlobalTheory.RowLocVec

theorem cosVec_isLocVec : GlobalTheory.RowClaim.Big fun {D} _ _ _ _ {T} _ _ _ _ _ {_} ch => ∀ (t : T) (i : Fin D.R.m) (κ : ch.G.CosAt i), ∃ e, IsIdemSum e (locPl ch.G t) ∧ ∃ φ, IsLocVec ch.W (.chi (i : ℕ) 0) e (ch.W.vac i) φ (ch.W.cosVec i κ) := by
  refine ⟨0, fun ε CF _ => ⟨0, fun D large₂ _ _ Γ _ _ Pl0 T A Ks _ _ _ R F s ch _ _ t i κ => ?_⟩⟩
  classical
  have hL := s.core.lev
  obtain ⟨e₀, he₀, hcos⟩ := ch.W.cosVec_is
  obtain ⟨e, he⟩ := GlobalTheory.FunObj.LocTensor.exists_idemSum_locPl hL ch.G t
  obtain ⟨b, rfl, hb, hab⟩ := exists_compl_idem (by unfold locPl; exact Finset.subset_union_left) he he₀
  have hS : IsSelfDualC (ch.G.pS (.chi (i : ℕ) 0)) (ch.G.latS (.chi (i : ℕ) 0)) :=
    isSelfDualC_neg (node_isV ch.G hL (X := .grid ((i : ℕ) + 1) 0) ⟨i.2, Nat.zero_le _⟩).sd
  have hT : IsSelfDualC (ch.G.pT (.chi (i : ℕ) 0)) (ch.G.latT (.chi (i : ℕ) 0)) :=
    (node_isV ch.G hL (X := .grid (i : ℕ) 0) ⟨i.2.le, Nat.zero_le _⟩).sd
  have ha := GlobalTheory.PlaceDatum.idemSum_mul_self he₀
  exact ⟨e₀ + b, he, _, isThetaAt_extend ch.W.ψ_std hS hT he ha hb hab (ch.W.vac_is i i.2).2.lat
    (GlobalTheory.GridWeil.isSBHalf_cosInd hS hT (ch.G.pl.modul_ne_bot ch.sc) ha (GlobalTheory.PlaceDatum.infPart_idemSum he₀) κ)
    (hcos i i.2 κ)⟩

end GlobalTheory.RowLocVec
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlacePointConditionTorusInverseDiagIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlace_pointCondition_torus_inverseDiag_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∃ u : UX D ρ, ∃ a ∈ p.A₁, GlobalTheory.AscFin.MxOff (· = v) (mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ u.1.1) - xZero dW - a)) → ∀ i, (t⁻¹).1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.FinPl.PtInv.inv_int_of_pt | exact GlobalTheory.FinPl.PtInv.inv_int_of_pt | (intros; apply GlobalTheory.FinPl.PtInv.inv_int_of_pt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodPlaceShiftConditionTorusDiagIntegralStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.SepRows GlobalTheory.Asc
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.FinPl (Lat idAt idOff intAt grpAt grpOff MxAt latV latA InK MonoAt OrthAt PrimAt ColsAt)
open scoped nonZeroDivisors ContDiff
open GlobalTheory.AscFin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.goodPlace_shiftCondition_torus_diag_integral : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ (V V₀ W W₀ : HSp D) (ρ : ℕ) (dV : HypDec V V₀ ρ) (dW : HypDec W W₀ ρ) (p : Pieces V₀ W W₀ ρ ρ) (LV : Lat V) (LV₀ : Lat V₀) (LW : Lat W) (LW₀ : Lat W₀) (v : GlobalTheory.FinPl.Pl D), GoodAt dV dW (xZero dW) ψ LV LV₀ LW LW₀ v → StdAt dV dW p LV LW v → ∀ t : GL (Fin ρ) (AE D), (∀ i j, i ≠ j → t.1 i j = 0) → dW.levi t ∈ grpAt W (· = v) → (∀ N : Mx D ρ ρ, MxAt (· = v) N → (∀ i j, j ≤ i → N i j = 0) → mt W (dW.levi t)⁻¹ ⬝ (xZero dW ⬝ N) ∈ p.A₁ → psiE ψ (upSum N) = 1) → ∀ i j : Fin ρ, j.1 = i.1 + 1 → t.1 i i - 1 ∈ intAt D (· = v) := by
  first | exact @GlobalTheory.AscFin.ShiftInt.shift_int | exact GlobalTheory.AscFin.ShiftInt.shift_int | (intros; apply GlobalTheory.AscFin.ShiftInt.shift_int <;> assumption)
end

