module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0046
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0010
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroSupport
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0620
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0628
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0637
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0645
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0253
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0020
public import Formalism.LocalToGlobal.GroupLattices.ComparisonMaps.ComparisonZeroEmbedding
public import Formalism.SharpRestriction.GrowthBounds.ChartedClasses.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.TwistedLevelAgreement.StepInTwK
public import Formalism.SharpRestriction.GrowthBounds.BaseLevels.LevelsGEmpty
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelsTwG
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0297
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplittingFstMemIntegers
public import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
public import Formalism.LocalRingCardinality.DataLevel
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0596
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0599
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthCommonDenominatorRankLe
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformStrictnessAndFaceCutBounds
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0625
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0641
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0646
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0651

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjParahoricBlockLift
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.TypeRec.factG
open Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev

noncomputable section

namespace GlobalTheory.ParahLift

section Core

variable {K : Type} [CommRing K]

theorem pl_blkDiag_mem {m r : ℕ} {x : GL (Fin r) K} {M : GL (Fin m) K} (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  intro i j hij
  have hj : j.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hi : ¬ i.val < r := by
    unfold Formalism.L2.DIV.blk2 at hij; split_ifs at hij with h1 h2 <;> omega
  have hne : i ≠ j := fun h => hi (h ▸ hj)
  show M.val i j = 0
  rw [hM i j, dite_eq_right (fun h => hi h.1), if_neg hne]

theorem pl_blkOf_eq {m r t : ℕ} (hm : m = r + t) (a : Fin m) :
    Formalism.L2.DIV.blkOf r t a = Formalism.L2.DIV.blk2 r a := by
  have ha := a.2
  unfold Formalism.L2.DIV.blkOf Formalism.L2.DIV.blk2
  split_ifs with h
  · rfl
  · have : (a.val - r) / t = 0 := Nat.div_eq_of_lt (by omega)
    omega

theorem pl_blockTri_eq {m r t : ℕ} (hm : m = r + t) :
    Formalism.L2.DIV.blockTri (κ := K) (n := m) (Formalism.L2.DIV.blkOf r t) = Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r) := by
  have : (Formalism.L2.DIV.blkOf r t : Fin m → ℕ) = Formalism.L2.DIV.blk2 r := funext (pl_blkOf_eq hm)
  rw [this]

theorem pl_core {m r t : ℕ} (hm : m = r + t) (hr : r ≤ m) {b M : GL (Fin m) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M) :
    b * M * b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr (b * M * b⁻¹) = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 (b * M * b⁻¹) = 1 := by
  have hM2 := pl_blkDiag_mem hM
  have hbinv := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).inv_mem hb
  have hbM := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hb hM2
  have hall := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blk2 r)).mul_mem hbM hbinv
  have hE := pl_blockTri_eq (K := K) hm
  refine ⟨hE ▸ hall, ?_, ?_⟩
  · have hMr : Formalism.L2.DIV.upperLeftBlock hr M = x := by
      apply Units.ext
      ext i j
      rw [Formalism.L2.DIV.upper_block_val_submatrix hr hM2, Matrix.submatrix_apply, hM, dite_eq_left ⟨i.2, j.2⟩]
      rfl
    unfold Formalism.L2.DIV.upperLeftBlock at hMr ⊢
    rw [Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hbM hbinv, Formalism.L2.DIV.extendMatrixByIdentityAlongIndices_mul _ hb hM2, Formalism.L2.DIV.extendOne_inv _ hb, hMr]
  · have hb' : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hb
    have hM' : M ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hM2
    have hbinv' : b⁻¹ ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) := hE ▸ hbinv
    have hbM' := (Formalism.L2.DIV.blockTri (κ := K) (Formalism.L2.DIV.blkOf r t)).mul_mem hb' hM'
    have hdM : Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 M = 1 := by
      apply Units.ext
      rw [Formalism.L2.DIV.diag_block_det_val 1 hM', Units.val_one]
      have hsub : (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)) = 1 := by
        ext a c
        have ha : ¬ a.1.val < r := fun h => by
          have h2 := a.2
          simp [Formalism.L2.DIV.blkOf, h] at h2
        rw [Matrix.submatrix_apply, hM, dite_eq_right (fun h => ha h.1), Matrix.one_apply]
        by_cases hac : a = c
        · subst hac; simp
        · rw [if_neg hac, if_neg (fun h => hac (Subtype.ext h))]
      show (M.val.submatrix (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m) (Subtype.val : {a : Fin m // Formalism.L2.DIV.blkOf r t a = 1} → Fin m)).det = 1
      rw [hsub, Matrix.det_one]
    rw [Formalism.L2.DIV.diag_block_det_mul hbM' hbinv', Formalism.L2.DIV.diag_block_det_mul hb' hM', hdM, mul_one]
    unfold Formalism.L2.DIV.dBlk
    rw [Formalism.L2.DIV.extendOne_inv _ hb', mul_inv_cancel]

theorem pl_core_cast {n m r t : ℕ} (hn : n = m) (hm : m = r + t) (hr : r ≤ m) (hr' : r ≤ n) {b M : GL (Fin m) K}
    {X : GL (Fin n) K} {x : GL (Fin r) K}
    (hb : b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 r)) (hM : GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity x M)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c) :
    X ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf r t) ∧
    Formalism.L2.DIV.upperLeftBlock hr' X = Formalism.L2.DIV.upperLeftBlock hr b * x * (Formalism.L2.DIV.upperLeftBlock hr b)⁻¹ ∧
    Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf r t) 1 X = 1 := by
  subst hn
  have hXe : X = b * M * b⁻¹ := Units.ext (Matrix.ext fun a c => hX a c)
  subst hXe
  exact pl_core hm hr hb hM

theorem pl_one_cast {n m : ℕ} (hn : n = m) {b Y : GL (Fin m) K} {X : GL (Fin n) K} (hY : Y = 1)
    (hX : ∀ a c : Fin m, X.val (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * Y * b⁻¹).val a c) : X = 1 := by
  subst hn; subst hY
  apply Units.ext
  ext a c
  have h := hX a c
  rw [mul_one, mul_inv_cancel] at h
  exact h

end Core

end GlobalTheory.ParahLift

namespace GlobalTheory.ParahLift

section LevFn

open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {n : ℕ}
  {LL : Type} [CommRing LL]

theorem pl_levFn_eq_one (β : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (Ld : Formalism.L2.DIV.LevDat E LL n)
    (x : GL (Fin n) (E ⊗[F] Formalism.L2.Herm.Af F)) (hP : Ld.P.chi = 1)
    (hg : ∀ PP ∈ Ld.Pg, ∀ c ∈ Finset.range Ld.s,
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf Ld.r Ld.t) (c + 1) (Formalism.L2.DIV.redFn β PP x) = 1)
    (hq : ∀ PP ∈ Ld.Q, Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blk2 Ld.r) 1 (Formalism.L2.DIV.redFn β PP x) = 1) :
    Formalism.L2.DIV.levFn β Ld x = 1 := by
  unfold Formalism.L2.DIV.levFn
  rw [Finset.prod_eq_one (fun PP hPP => Finset.prod_eq_one (fun c hc => by rw [hg PP hPP c hc, map_one])),
    Finset.prod_eq_one (fun PP hPP => by rw [hq PP hPP, map_one])]
  have h1 : Formalism.L2.DIV.ext1 Ld.P.H Ld.P.chi (Formalism.L2.DIV.rTup β Ld x) = 1 := by
    unfold Formalism.L2.DIV.ext1
    split_ifs
    · rw [hP]; rfl
    · rfl
  rw [h1, mul_one, mul_one]

end LevFn

theorem exists_conj_parahoric_lift : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type}
  [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (cG : Formalism.L2.DIV.G0 R.Pg D.R.r ≃* G0g D.nd) (k : Fin D.R.m) (s : T)
  (P : Formalism.IndefR.principalLevelFrame.RowPsi (Formalism.IndefR.Links.Vc D k) D.R.nV) (L : G0g D.nd → Formalism.AUTREP.GAf D.host.E D.R.nV),
  (∀ g, L g ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV) →
  (∀ κ ∈ ReciprocityTheory.Aut.Umax D.host.E D.R.nV, Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ κ) ∈ Formalism.L2.DIV.St (R.βV k)) →
  (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q s → ∃ (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w)
      (b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP s'.w)), s'.w = PP ∧ GlobalTheory.CenFrame.IsResidue s' φ ∧
        GlobalTheory.CenFrame.FrameRed (GlobalTheory.FrameBlockDiagonal.rankV D k) P (R.βV k) s' φ b ∧ (PP ∈ R.Pg → b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r))) →
  (∀ g (s' : ReciprocityTheory.Aut.SplitPlace D.host.E) (φ : GlobalTheory.CenFrame.Os s' →+* Formalism.L2.DIV.kP s'.w), GlobalTheory.CenFrame.IsResidue s' φ →
      (s'.w ∈ R.Q s → ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧ Matrix.GeneralLinearGroup.map φ y = 1) ∧
      ∀ hP : s'.w ∈ R.Pg, ∃ y, GlobalTheory.CenFrame.IsCompOf s' (L g) y ∧
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm g) ⟨s'.w, hP⟩) (Matrix.GeneralLinearGroup.map φ y)) →
  ∃ c : G, ∀ g : G,
    Formalism.IndefR.Lev.IsLevelLift (Formalism.IndefR.Links.Vc D k) (R.βV k) (R.datVt k s) (R.eG g) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) ∧
    Formalism.IndefR.Lev.levChi (Formalism.IndefR.Links.Vc D k) (R.βV k) (Formalism.IndefR.Lev.flagL (R.datVt k s)) (P.ψ (L ((R.eG.trans cG) (c * g * c⁻¹)))) = 1 := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R cG k s P L H1 H2 H3 H4
  have hn : (Formalism.IndefR.Links.Vc D k).rank = D.R.nV := GlobalTheory.FrameBlockDiagonal.rankV D k
  have hm : D.R.nV = D.R.r + D.R.t := rfl
  have hr : D.R.r ≤ D.R.nV := Nat.le_add_right _ _
  have hr' : D.R.r ≤ (Formalism.IndefR.Links.Vc D k).rank := hn ▸ hr
  have hA : ∀ PP : ↥R.Pg, ∃ b : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1), b ∈ Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blk2 D.R.r) ∧
      ∀ h : G0g D.nd, ∃ M : GL (Fin D.R.nV) (Formalism.L2.DIV.kP PP.1),
        GlobalTheory.FrameBlockDiagonal.IsBlockDiagonalWithIdentity (R.eG ((R.eG.trans cG).symm h) PP) M ∧
        ∀ a c, (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))).val
          (Fin.cast hn.symm a) (Fin.cast hn.symm c) = (b * M * b⁻¹).val a c := by
    rintro ⟨PP, hPP⟩
    obtain ⟨s', φ, b, hw, hres, hfr, hb⟩ := H3 PP (Or.inl hPP)
    subst hw
    refine ⟨b, hb hPP, fun h => ?_⟩
    obtain ⟨y, hy, hbd⟩ := (H4 h s' φ hres).2 hPP
    exact ⟨_, hbd, hfr (L h) (H1 h) y hy⟩
  have hB : ∀ PP ∈ R.Q s, ∀ h : G0g D.nd,
      Formalism.L2.DIV.redFn (R.βV k) PP (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) = 1 := by
    intro PP hPP h
    obtain ⟨s', φ, b, hw, hres, hfr, -⟩ := H3 PP (Or.inr hPP)
    subst hw
    obtain ⟨y, hy, h1⟩ := (H4 h s' φ hres).1 hPP
    exact pl_one_cast hn h1 (hfr (L h) (H1 h) y hy)
  choose bf hbf Mf hMd hMe using hA
  refine ⟨R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹), fun g => ?_⟩
  set c := R.eG.symm (fun PP => (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹) with hc
  set h := (R.eG.trans cG) (c * g * c⁻¹) with hh
  have hsymm : (R.eG.trans cG).symm h = c * g * c⁻¹ := MulEquiv.symm_apply_apply _ _
  have hx : ∀ PP : ↥R.Pg, R.eG ((R.eG.trans cG).symm h) PP =
      (Formalism.L2.DIV.upperLeftBlock hr (bf PP))⁻¹ * R.eG g PP * Formalism.L2.DIV.upperLeftBlock hr (bf PP) := by
    intro PP
    rw [hsymm, map_mul, map_mul, map_inv, hc, MulEquiv.apply_symm_apply]
    simp only [Pi.mul_apply, Pi.inv_apply, inv_inv]
  have hcore : ∀ PP : ↥R.Pg,
      Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h))) ∈
        Formalism.L2.DIV.blockTri (Formalism.L2.DIV.blkOf D.R.r D.R.t) ∧
      Formalism.L2.DIV.upperLeftBlock hr' (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) =
        R.eG g PP ∧
      Formalism.L2.DIV.dBlk (Formalism.L2.DIV.blkOf D.R.r D.R.t) 1
        (Formalism.L2.DIV.redFn (R.βV k) PP.1 (Formalism.IndefR.Lev.finE (Formalism.IndefR.Links.Vc D k) (P.ψ (L h)))) = 1 := by
    intro PP
    obtain ⟨h1, h2, h3⟩ := pl_core_cast hn hm hr hr' (hbf PP) (hMd PP h) (hMe PP h)
    refine ⟨h1, ?_, h3⟩
    rw [h2, hx PP]
    group
  have hSt := H2 (L h) (H1 h)
  refine ⟨⟨P.into _, Formalism.L2.DIV.mem_parLev.2 ⟨GlobalTheory.LevFinCong.finE_mem_UA _ _, hSt, fun PP hPP => (hcore ⟨PP, hPP⟩).1,
    fun PP hPP => ?_⟩, ?_⟩, ?_⟩
  · rw [hB PP hPP h]; exact Subgroup.one_mem _
  · funext PP
    exact (hcore PP).2.1
  · unfold Formalism.IndefR.Lev.levChi
    rw [pl_levFn_eq_one _ _ _ rfl, Units.val_one]
    · intro PP hPP c' hc'
      have hc0 : c' = 0 := by
        have : c' < 1 := Finset.mem_range.1 hc'
        omega
      subst hc0
      exact (hcore ⟨PP, hPP⟩).2.2
    · intro PP hPP
      rw [hB PP hPP h]
      exact Formalism.L2.DIV.blockDiagonalExtendByOnePrimeField_one _ _

end GlobalTheory.ParahLift
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsOrthonormalStepBasisBaseLatticeCharts
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.G Formalism.L2.G Formalism.MainNotions.G.CmpJ Formalism.L2.Forms Formalism.UG
open scoped TensorProduct

namespace GlobalTheory.Mem.Top.KerTwLv


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem stepBasis_std : ∀ {K : Ctx} {B : Base} {f : Fr B.toPre} {T : TwDat B} (w : ColW B f T), K.Over B.toPre → Forced K B T → Pinned K B f T w →
    ∀ (Z : w.Lt) (t : ColumnDataSplitPrimes K w Z) (Wt : Set B.places.Pl) (nch : NChoice (w.D Z)) (n : NchT w Z Wt nch) (Y : DivX (w.D Z)),
    V4.MuIsW (w.st Z) f T Wt w.I.xi → TC.QpIs w.I Y.Qp →
    ∀ (O : ∀ u a, GL3Theta.LiftObj (w.D Z) ((w.D Z).chTw u a)), TC.StdO w.I w.l Z Y.Qp O →
    (∀ u a i, i < B.R.m → Formalism.L2.Ker.UnfIsAll (O u a) i) → ∀ (E : KerEnt (w.D Z) Y (w.tw Z)), TC.EntOk E O →
    ∀ (Fl : ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
        G.Fills ((w.D Z).gat u v hg)),
      ∀ (hfl : ∀ u v hg, (Fl u v hg).t = (w.D Z).R.t ∧ (Fl u v hg).mm = (w.D Z).R.m),
      (∀ u v hg (x : Fin ((w.D Z).gat u v hg).P.nV) (s : Fin (((w.D Z).gat u v hg).P.n' x)), ∀ j ∈ SizeData₂.lifts (w.D Z),
        ((Fl u v hg).w x j s : ℝ) = wj (w.D Z) j (t.Gt.gat_pos u v hg ⟨x, s⟩) - G.kaJ (w.D Z) j) →
    ∀ u (v : (w.D Z).what₂.places.Pl) (hg : GIdx (w.D Z).host ((w.D Z).mem u).A.T ((w.D Z).what₂.places.resChar v)),
      haveI : Fact ((w.D Z).what₂.places.resChar v).Prime := ⟨(w.D Z).what₂.places.resChar_prime v⟩
      ∀ (hμ : (w.D Z).what₂.muAt v ≠ (w.D Z).what₂.mu0),
      ∀ (tt : Formalism.L2.Forms.SymmetricTwistedColumnsAtPrimes n.tp t.C (w.tw Z)), TC.StdTw w.I w.l Z w.l0 tt →
      ∀ j (hj : j + 1 ≤ (w.D Z).R.m), ∃ B : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E,
        cT (sigD (w.D Z) : (w.D Z).host.E →+* (w.D Z).host.E)
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 * gramN (w.D Z) (j + 1) hj *
          (reGL (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E B).1 = 1 ∧
        ∀ (β : tt.ch.Ch u ((w.D Z).what₂.muAt v) (j + 1)) w' h (x : Fin ((w.D Z).sp.X (j + 1)).rank → w'.adicCompletion (w.D Z).host.F),
          (∃ y ∈ Formalism.L2.Herm.locL w' (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb,
            ∀ a, ((t.g.herm.g u v hg).spl w' h (y a)).1 = x a) ↔
          ∀ a, (((GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg B w' h)⁻¹ :
            GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)) :
              Matrix (Fin ((w.D Z).sp.X (j + 1)).rank) (Fin ((w.D Z).sp.X (j + 1)).rank) (w'.adicCompletion (w.D Z).host.F)).mulVec x a ∈
            w'.adicCompletionIntegers (w.D Z).host.F := by
  intro K B f T w hK hF hP Z t Wt nch n Y hmu hQp O hstdO hunf E hent Fl hfl hwt u v hg hμ tt hstd j hj
  have hsc := (GlobalTheory.Mem.Col2.TC.spaces_in_coordinates w.I w.ok w.pins w.l Z).2.2.2 (j+1) hj
  obtain ⟨k, hk⟩ := hstd.1.reads u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  have hcar := tt.forms.car u ((w.D Z).what₂.muAt v) hμ (j+1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj
  refine ⟨1, ?_, ?_⟩
  · rw [hsc.1]
    simp [cT, Matrix.map_one]
  · intro β w' h x
    have hfr : GlobalTheory.Mem.Top.KerTwLv.frOf t.g.herm u v hg (1 : GL (Fin ((w.D Z).sp.X (j + 1)).rank) (w.D Z).host.E) w' h = 1 :=
      map_one _
    rw [hfr, inv_one]
    simp only [Units.val_one, Matrix.one_mulVec]
    have hT : ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) ∉ w'.asIdeal := by
      intro hT
      have hcop : Nat.Coprime ((w.D Z).what₂.places.resChar v) ((w.D Z).mem u).A.T :=
        (Nat.Prime.coprime_iff_not_dvd hg.1).2 hg.2.2.2.2.2
      obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 hcop
      apply w'.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : ((1 : ℤ) : 𝓞 (w.D Z).host.F) = (a : 𝓞 (w.D Z).host.F) * (((w.D Z).what₂.places.resChar v : ℕ) : 𝓞 (w.D Z).host.F)
          + (b : 𝓞 (w.D Z).host.F) * ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.F) := by
        rw [← hab]; push_cast; ring
      rw [Int.cast_one] at e
      rw [e]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ h) (Ideal.mul_mem_left _ _ hT)
    have hLb : ∀ y, y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
        ∀ a, ∃ r : 𝓞 (w.D Z).host.E, y a = r ∧ (a.1 + 1 = ((w.D Z).sp.X (j + 1)).rank → (w.px.piT u : 𝓞 (w.D Z).host.E) ∣ r) := by
      intro y
      have e1 := (hcar β).Lb_eq
      have e2 := hk.lb β
      have hr := rankN (w.D Z) (j + 1) hj
      have hmap : y ∈ (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb ↔
          reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E y ∈
            reL (rankN (w.D Z) (j + 1) hj) (tt.ch.lev u ((w.D Z).what₂.muAt v) (j + 1) (Formalism.MainNotions.G.CmpJ.AgreeLv.one_le j) hj β).Lb := by
        constructor
        · intro hy
          exact ⟨y, hy, rfl⟩
        · rintro ⟨z, hz, hzy⟩
          have : z = y := (reV (rankN (w.D Z) (j + 1) hj) (w.D Z).host.E).injective hzy
          exact this ▸ hz
      rw [hmap, ← e1]
      refine (e2 _).trans ?_
      simp only [TC.baseL, Set.mem_setOf_eq, reV, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
      constructor
      · intro H a
        obtain ⟨r, hr1, hr2⟩ := H (finCongr hr a)
        refine ⟨r, ?_, fun ha => hr2 ?_⟩
        · rw [LinearMap.funLeft_apply, Equiv.symm_apply_apply] at hr1
          exact hr1
        · have e : ((finCongr hr a : Fin _) : ℕ) = a := rfl
          rw [e]
          exact ha.trans hr
      · intro H b
        obtain ⟨r, hr1, hr2⟩ := H ((finCongr hr).symm b)
        refine ⟨r, hr1, fun hb => hr2 ?_⟩
        have e : (((finCongr hr).symm b : Fin _) : ℕ) = b := rfl
        rw [e]
        exact hb.trans hr.symm
    have hπ : (w.px.piT u : 𝓞 (w.D Z).host.E) * (B.fields.conjO (w.px.piT u) : 𝓞 (w.D Z).host.E) =
        ((((w.D Z).mem u).A.T : ℕ) : 𝓞 (w.D Z).host.E) :=
      B.primes_piT_norm w.px u
    have L := @GlobalTheory.T.mem_locL_iff_forall_mem_intV_of_not_mem (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ _ w' _ _ _ _ _ _ hT hπ hLb
    have PI := @_root_.GlobalTheory.splitting_fst_mem_integers (w.D Z).host.F (w.D Z).host.E _ _ _ _ _ w' _ ((t.g.herm.g u v hg).spl_alg w' h)
    constructor
    · rintro ⟨y, hy, hyx⟩ a
      rw [← hyx a]
      exact PI _ ((L y).1 hy a)
    · intro hx
      refine ⟨fun a => (1 : (w.D Z).host.E) ⊗ₜ[(w.D Z).host.F] x a, (L _).2
        (fun a => Subring.subset_closure (Or.inr ⟨⟨x a, hx a⟩, rfl⟩)), fun a => ?_⟩
      rw [(t.g.herm.g u v hg).spl_alg]

end GlobalTheory.Mem.Top.KerTwLv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionFunctionIntegralStrictlyCon
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

namespace GlobalTheory.PolFan.StarKey

theorem exists_starFun_strict : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (ψ w : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q ψ → IsCentreSet H.bar q ψ w → ∃ K D : ℕ, 0 < K ∧ 0 < D ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → ∃ n : ℤ, (starFun H.bar ψ w K D).evalZ β = n) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → (∀ β ∈ balForms H.bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) → IsStrict H.bar (starFun H.bar ψ w K D) γ) ∧ (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Module.finrank (𝓞 E) X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell H.bar ψ γ → ∀ β₀ ∈ balForms H.bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ → ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ → IsStrict H.bar (starFun H.bar ψ w K D) (Fin.cons β₀ fun j => γ (s j))) := by
  intro E _ _ _ H q ψ w hdom hψ hcs
  obtain ⟨D₀, hD₀, hint⟩ := _root_.GlobalTheory.PolFan.StarDen.starDepth_den E H q ψ w hψ hcs
  obtain ⟨N₀, C₀, hdata⟩ := _root_.GlobalTheory.PolFan.StrictData.exists_strict_data E H q ψ hdom hψ
  obtain ⟨b, hgens⟩ := _root_.GlobalTheory.PolFan.StarGens.exists_bounded_gens E H q ψ w hψ hcs
  have hD₀r : (0 : ℝ) < D₀ := by exact_mod_cast hD₀
  refine ⟨N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1, D₀, by omega, hD₀, ?_, ?_, ?_⟩
  · intro X _ _ _ _ hX β hβ hp
    obtain ⟨n₁, hn₁⟩ := (hψ X hX).integral β hβ hp
    obtain ⟨n₂, hn₂⟩ := hint X hX β hβ hp
    refine ⟨D₀ * (N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1) * n₁ + n₂, ?_⟩
    rw [starFun_evalZ, hn₁]
    push_cast
    linear_combination hn₂
  · intro X _ _ _ _ hX m γ hγ hnoc
    obtain ⟨N, ℓ, hN, hNN, hsw, -⟩ := hdata X hX m γ hγ
    have hgap := _root_.GlobalTheory.PolFan.StarGap.starDepth_le_gap E H q ψ w hψ hcs X hX m γ N ℓ hγ hnoc hN hsw
    have hnn : ∀ β : LinearMap.BilinForm ℤ X, 0 ≤ (starDepth H.bar ψ w).evalZ β := fun β =>
      starDepth_eval_nonneg (fun a b => (β a b : ℝ))
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKN : (N : ℝ) + 1 ≤ K := by
      have : N + 1 ≤ K := by rw [hKdef]; omega
      exact_mod_cast this
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    refine ⟨N, ((D₀ * K : ℕ) : ℤ) • ℓ, hN, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · have h0 := hsw.1 i
      have hps : (starDepth H.bar ψ w).evalZ (γ i) = 0 :=
        le_antisymm (by have := hgap (γ i) (hγ.mem i) (hγ.nonneg i); linarith) (hnn _)
      rw [starFun_evalZ, hps]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      rw [h0]; ring
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, smul_eq_mul]
      push_cast
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have k1 : (N : ℝ) * P ≤ K * (L - N * Ψ) := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      nlinarith [mul_le_mul_of_nonneg_left k1 hD₀r.le]
    · have hg := hgap β hβ hp
      have hf := hsw.2.1 β hβ hp
      have hps := hnn β
      rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, smul_eq_mul] at he
      push_cast at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      set L : ℝ := (ℓ β : ℝ)
      have e1 : (N : ℝ) * P = K * (L - N * Ψ) := by
        have := mul_left_cancel₀ hD₀r.ne' (show (D₀ : ℝ) * (N * P) = D₀ * (K * (L - N * Ψ)) by linear_combination he)
        exact this
      have e2 : L - N * Ψ = 0 := by nlinarith [mul_le_mul_of_nonneg_left hg hN0]
      exact hsw.2.2 β hβ hp (by linarith)
  · intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h hcut hpos
    obtain ⟨N, ℓ, hN, hNN, hsw, hcuts⟩ := hdata X hX m γ hγ
    obtain ⟨h', hcut', hpos', hdom'⟩ := hcuts m' s h hcut
    have hp' : 0 < h' β₀ := hpos' β₀ hin₀ hpos
    obtain ⟨hin, hone, hzero, heq⟩ :=
      _root_.GlobalTheory.PolFan.starDepth_on_cell E H q ψ w hψ hcs X hX m γ hγ β₀ hβ₀ hp₀ hw₀ hin₀ m' s h' hcut' hp'
    set K := N₀ + N₀ * C₀ + N₀ ^ 2 * C₀ * b + 1 with hKdef
    have hKb : N + N * C₀ + N ^ 2 * C₀ * b + 1 ≤ K := by
      rw [hKdef]
      have h1 : N * C₀ ≤ N₀ * C₀ := Nat.mul_le_mul_right _ hNN
      have h2 : N ^ 2 * C₀ * b ≤ N₀ ^ 2 * C₀ * b :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left hNN 2))
      omega
    have hoff := _root_.GlobalTheory.PolFan.StarKey.OffCell.off_cell E H q ψ w b hψ hcs X hX (hgens X hX) m γ N ℓ hγ hN hsw β₀ hβ₀ hp₀ hw₀ hin₀ m' s h'
      hcut' hp' C₀ hdom' K hKb
    have hlinγ : ∀ β, InRCone γ β → (ℓ β : ℝ) = N * ψ.evalZ β := fun β hβ => StarKey.ell_eq_of_inRCone hγ.linear hsw hβ
    have hcast : (((h' β₀).toNat : ℕ) : ℝ) = (h' β₀ : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hp'.le]
    have hH0 : (0 : ℝ) < h' β₀ := by exact_mod_cast hp'
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    refine ⟨N * (h' β₀).toNat, (D₀ : ℤ) • (((K : ℤ) * h' β₀) • ℓ + (N : ℤ) • h'), by
      have : 0 < (h' β₀).toNat := by omega
      positivity, fun i => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        rw [starFun_evalZ, hone]
        have hl := hlinγ β₀ hin₀
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
        push_cast
        rw [hcast, hl]; ring
      · simp only [Fin.cons_succ]
        have hh : h' (γ (s j)) = 0 := (hcut'.2 (s j)).2 ⟨j, rfl⟩
        rw [starFun_evalZ, hzero j]
        simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul, hh]
        push_cast
        rw [hcast, hsw.1 (s j)]; ring
    · rw [starFun_evalZ]
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul]
      push_cast
      rw [hcast]
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        have hi := hin β hβ hp hc
        rw [hl]
        nlinarith [mul_le_mul_of_nonneg_left hi (mul_nonneg hD₀r.le hN0.le)]
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]
    · rw [starFun_evalZ] at he
      simp only [LinearMap.smul_apply, LinearMap.add_apply, smul_eq_mul] at he
      push_cast at he
      rw [hcast] at he
      set P := (starDepth H.bar ψ w).evalZ β
      set Ψ := ψ.evalZ β
      by_cases hc : InRCone γ β
      · have hl := hlinγ β hc
        rw [hl] at he
        refine heq β hβ hp hc ?_
        have : ((D₀ : ℝ) * N) * ((h' β₀ : ℝ) * P) = ((D₀ : ℝ) * N) * (h' β : ℝ) := by linear_combination he
        exact mul_left_cancel₀ (mul_pos hD₀r hN0).ne' this
      · have ho := hoff β hβ hp hc
        nlinarith [mul_lt_mul_of_pos_left ho hD₀r]

end GlobalTheory.PolFan.StarKey
end

