module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1733
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2799
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MixedLagrangianOppositeLagrangianChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1740
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1424
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2786
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2806
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProjOverWeierstrass
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2803
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1836
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2784
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1579
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1561
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0682
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2809
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1656
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0027
public import Formalism.LocalToGlobal.IndefiniteReal.FWExist
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0054

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStandingTripleThetaFirst
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000

namespace GlobalTheory.TopFlip.ChartB

theorem reindex_blocks {K C : Type} [Field K] {n p q d : ℕ} (e : Fin p ⊕ Fin q ≃ Fin d) (ρ : Fin p ⊕ Fin q ≃ C)
    (x : Matrix (Fin n) (Fin n) K) (Z : Matrix (Fin n) (Fin d) K) (P R : Matrix (Fin p) (Fin p) K)
    (Q S : Matrix (Fin q) (Fin q) K) (r : Fin n) (c : C) :
    (x * (Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S)) r ((finSumFinEquiv.symm.trans ρ).symm c) =
    (x * Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))) r ((e.symm.trans ρ).symm c) := by
  have h : Z.submatrix id (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv P Q *
      GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
      (Z * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix id (e.symm.trans finSumFinEquiv).symm := by
    have h1 : GlobalTheory.Doubling.blkMat finSumFinEquiv P Q * GlobalTheory.Doubling.blkMat finSumFinEquiv R (-S) =
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (P * R) (-(Q * S))).submatrix (e.symm.trans finSumFinEquiv).symm
          (e.symm.trans finSumFinEquiv).symm := by
      unfold GlobalTheory.Doubling.blkMat GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk
      rw [submatrix_mul_equiv, fromBlocks_multiply]
      ext a b
      simp
    rw [Matrix.mul_assoc, h1, submatrix_mul_equiv]
  rw [Matrix.mul_assoc, h, Matrix.mul_assoc]
  simp [Matrix.mul_apply]

variable {D : D7}

theorem adj_coord (S X : HSp D) (y : Matrix (Fin S.rank) (Fin X.rank) (AE D)) :
    (S.gram⁻¹).map (incA D) * ((HMul.hMul yᵀ (incM S.gram) : Matrix (Fin X.rank) (Fin S.rank) (AE D)).map (cA D))ᵀ =
      y.map (cA D) := by
  have e0 : ((incM S.gram).map (cA D))ᵀ = S.gram.map (incA D) := by
    ext a b
    exact congrArg (incA D) (show star (S.gram b a) = S.gram a b from S.herm.eq (S.frame b) (S.frame a))
  rw [Matrix.map_mul, Matrix.transpose_mul, e0, ← Matrix.mul_assoc, GlobalTheory.RouteCoords.inv_mul_gram, Matrix.one_mul]
  rfl

theorem linB_ptB {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} (B : Frames G) (t : T)
    {i j : Fin D.R.m} (e : Num G i j) (w : Pl D.host.E)
    (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) :
    linB B t i j w (ptB e u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)) * (loc w (B.β (i + 1) j)).val))) := by
  have h1 := adj_coord (spW₁ G i j) (spX G i j) (u.submatrix id (e.symm.trans finSumFinEquiv).symm)
  have h2 : (((spX G i j).gram.map (incA D)).map (toEAf D)).map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w))) := by
    rw [GlobalTheory.Doubling.gram_hsum]
    refine Matrix.ext fun a b => ?_
    refine (GlobalTheory.FunObj.Good.cpt_incA w _).trans ?_
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h3 : (frX B i j).val.map (cpt w) = GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val
      (-(loc w (B.β (i + 1) j)).val) := by
    refine Matrix.ext fun a b => ?_
    change cpt w (GlobalTheory.Doubling.blkMat finSumFinEquiv (B.β i (j + 1)).val (-(B.β (i + 1) j).val) a b) = _
    obtain ⟨a | a, rfl⟩ := finSumFinEquiv.surjective a <;> obtain ⟨b | b, rfl⟩ := finSumFinEquiv.surjective b <;>
      simp [GlobalTheory.Doubling.blkMat, -finSumFinEquiv_apply_left, -finSumFinEquiv_apply_right]
  have h4 : (frMapAdj (spW₁ G i j) (spX G i j) (B.β i j) (frX B i j) (ptB e u)).map (cpt w) =
      ((loc w (B.β i j))⁻¹).val * ((u.map (fun a => cpt w (toEAf D (cA D a)))).submatrix id
        (e.symm.trans finSumFinEquiv).symm * GlobalTheory.Doubling.blkMat finSumFinEquiv
      ((spV G i j).gram.map (algebraMap D.host.E (Kw w))) ((spV₁ G i j).gram.map (algebraMap D.host.E (Kw w)))) *
      GlobalTheory.Doubling.blkMat finSumFinEquiv (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [← h2, ← h3]
    unfold frMapAdj
    erw [h1]
    rw [Matrix.map_mul, Matrix.map_mul, Matrix.map_mul, Matrix.map_mul]
    rfl
  refine Matrix.ext fun r c => ?_
  unfold linB
  rw [h4]
  exact reindex_blocks e _ _ _ _ _ _ _ _ c


open GlobalTheory.FlipMatch.ChartOpp hiding isHalf_of_mulG in
theorem exists_mixChart_linB : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : GlobalTheory.ChiGrid.Consts} {G : GridData L sc} {μ₀ : T}, L.Is μ₀ → ∀ (W : G.Weil) (B : Frames G) (t : T) (i j : Fin D.R.m) (M : Vol G), SquareStanding G t →
    ∀ (e : Num G i j) (Bs : Base D.host.F D.host.E) (Γ : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.Geo G i j) (X : Chars D.host.F D.host.E)
      (om : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V Γ.W) (om' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep D.sp.cm.sig Γ.V' Γ.W), IsTripleOf W M t i j e Bs Γ X →
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple Bs Γ X om om' → IsDoublyCompatible t i j e Bs Γ X →
    ∀ (v : Bs.P) (w : Pl D.host.E), splitPrime (Bs.τ v) = w → ∀ jj : Fv D.host.F v ≃+* Kw w, IsPlaceIso (Bs.τ v) w jj → IsLocIso jj →
    ∀ cc : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w), (Γ.W.bas v).val.map jj * cc.val = basCols B e w →
    ∃ g : GL (Fin (spW₁ G i j).rank) (Kw w),
      IsMixChart v.1 (mixHalfS e (atPl w 1)) (mixHalfS e (cA D (atPl w 1))) (mixCoS B t e w)
        (fun u => chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (fun u => (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
          (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u))
        (Assignment.one.block _ _) ∧
      ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
          (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) = linB B t i j w (ptB e u) := by
  intro D T L sc G μ₀ _ W B t i j M _ e Bs Γ X _ _ h _ _ v w hw jj hjj _ cc hcc
  classical

  have hε : atPl w 1 = GlobalTheory.EmbChart.idem (Bs.τ v) :=
    (GlobalTheory.IdemAtPl.eq_atPl_of_isIdemAt (hw ▸ GlobalTheory.EmbChart.isIdemAt_idem (Bs.τ v))).symm
  have hsum : GlobalTheory.EmbChart.idem (Bs.τ v) + cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) := by
    rw [GlobalTheory.EmbChart.cA_idem, GlobalTheory.EmbChart.idem, ← LinearMap.map_add (f := _), add_sub_cancel]; rfl
  have hii := GlobalTheory.SrcHalfOne.idem_mul_self (Bs.τ v)
  have hic : GlobalTheory.EmbChart.idem (Bs.τ v) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) = 0 :=
    (GlobalTheory.EmbChart.isSplitIdem_idem (Bs.τ v)).2.1
  have hcc' : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by rw [← map_mul, hii]
  have hb₁ : GlobalTheory.EmbChart.idem (Bs.τ v) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      GlobalTheory.EmbChart.idem (Bs.τ v) := by rw [← hsum, mul_add, hii, hic, add_zero]
  have hb₂ : cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) =
      cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) := by
    rw [← hsum, mul_add, mul_comm (cA D _) (GlobalTheory.EmbChart.idem _), hic, zero_add, hcc']
  rw [hε]

  have hzero : cpt w (toEAf D (cA D (GlobalTheory.EmbChart.idem (Bs.τ v)))) = 0 := by
    rw [← hjj]
    exact (congrArg jj (GlobalTheory.SrcHalfOne.piW_cA_idem (Bs.τ v))).trans (map_zero jj)
  have hE : ∀ x : D.host.E, jj (Bs.τ v x) = algebraMap D.host.E (Kw w) x := fun x => by
    rw [← GlobalTheory.FunObj.Good.cpt_incA w x, ← hjj]
    exact congrArg jj (GlobalTheory.LocFrame.piW_incA (Bs.τ v) x).symm
  have hcA : ∀ a, jj (piW ((Bs.τ v).comp D.sp.cm.sig) a) = cpt w (toEAf D (cA D a)) := fun a => by
    rw [← hjj]
    exact congrArg jj (GlobalTheory.SrcHalfOne.piW_cA (Bs.τ v) a).symm

  obtain ⟨κ, hκ⟩ : ∃ κ : D.host.E →+* Kw w, κ = algebraMap D.host.E (Kw w) := ⟨_, rfl⟩
  obtain ⟨Bp, hBp⟩ : ∃ Bp : GL (Fin (spW₁ G i j).rank) (Kw w),
    Bp = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.V'.bas v) := ⟨_, rfl⟩
  obtain ⟨C, hC⟩ : ∃ C : GL (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (Kw w),
    C = Matrix.GeneralLinearGroup.map (jj : Fv D.host.F v.1 →+* Kw w) (Γ.W.bas v) := ⟨_, rfl⟩
  have hG₁ : ((spW₁ G i j).gram.map κ).det ≠ 0 := by
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero κ).2 (GlobalTheory.RouteCoords.gram_det_ne _)
  have hξ : xiAt w ≠ 0 := (map_ne_zero _).2 GlobalTheory.ChiGrid.cmHost_imaginaryGenerator_ne_zero
  have hCc : C.val * cc.val = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (loc w (B.β i (j + 1))).val (-(loc w (B.β (i + 1) j)).val) := by
    rw [hC]; exact hcc
  obtain ⟨g, hg⟩ := chart_algebra e Bp C cc _ hG₁ (loc w (B.β i j)) (loc w (B.β i (j + 1))) (loc w (B.β (i + 1) j))
    ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) (xiAt w) hξ hCc
  refine ⟨g, ?_⟩

  have hκm : ∀ {a b : Type} (Z : Matrix a b D.host.E), (Z.map (Bs.τ v)).map jj = Z.map κ := fun Z =>
    Matrix.ext fun _ _ => by rw [hκ]; exact hE _
  have hX : ∀ u, (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      (Bp⁻¹).val * u.map (fun a => cpt w (toEAf D a)) * ((C⁻¹).val)ᵀ := fun u => by
    unfold coX
    rw [map_mul_equiv, map_mul_equiv, Matrix.transpose_map, Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW (Bs.τ v))) = u.map (fun a => cpt w (toEAf D a)) := Matrix.ext fun _ _ => hjj _
    rw [this, hBp, hC]
    rfl
  have hJ1 : (Γ.V'.J.map (Bs.τ v)).map jj = -((spW₁ G i j).gram.map κ) := by
    rw [hκm, h.JW₁]
    ext a b
    simp
  have hJ2 : ((Γ.W.J.map (Bs.τ v))ᵀ).map jj = xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ) := by
    rw [Matrix.transpose_map, hκm, h.JWW, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.skewGram]
    ext a b
    simp only [Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, map_mul, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk,
      Matrix.reindex_apply, Matrix.submatrix_apply]
    rcases e.symm a with a | a <;> rcases e.symm b with b | b <;> simp [xiAt, hκ]
  have hY : ∀ u, (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u).map jj =
      -(Bp.valᵀ * (-((spW₁ G i j).gram.map κ)) * u.map (fun a => cpt w (toEAf D (cA D a))) *
        (xiAt w • GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ) ((spV₁ G i j).gram.map κ)) * C.val) := fun u => by
    unfold coY
    rw [Matrix.map_neg _ (map_neg jj), map_mul_equiv, map_mul_equiv, map_mul_equiv, map_mul_equiv, hJ1, hJ2,
      Matrix.map_map]
    have : u.map (⇑jj ∘ ⇑(piW ((Bs.τ v).comp D.sp.cm.sig))) = u.map (fun a => cpt w (toEAf D (cA D a))) :=
      Matrix.ext fun _ _ => hcA _
    rw [this, Matrix.transpose_map, hBp, hC]
    rfl

  have htr : ∀ u, chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) g cc
      (coY D.sp.cm.sig Γ.V' Γ.W (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) (((loc w (B.β i j))⁻¹).val *
        u.map (fun a => cpt w (toEAf D (cA D a))) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e ((spV G i j).gram.map κ * (loc w (B.β i (j + 1))).val)
          (-((spV₁ G i j).gram.map κ * (loc w (B.β (i + 1) j)).val))) := fun u => by
    unfold chart
    rw [hY, (hg 0 _).1]
  have hmu : ∀ u, (xiAt w)⁻¹ • chart jj (finCongr (rankW₁ G t i j w)) (colsEq t e w) (invT g) (invT cc)
      (coX (Bs.τ v) (Γ.V'.bas v) (Γ.W.bas v) u) =
      reindex (finCongr (rankW₁ G t i j w)) (colsEq t e w) ((loc w (B.β i j)).valᵀ * ((spW₁ G i j).gram.map κ)ᵀ *
        u.map (fun a => cpt w (toEAf D a)) *
        GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.blk e (((loc w (B.β i (j + 1)))⁻¹).val)ᵀ (-(((loc w (B.β (i + 1) j))⁻¹).val)ᵀ)) := fun u => by
    unfold chart
    rw [hX, ← (hg (u.map fun a => cpt w (toEAf D a)) 0).2]
    rfl
  have hinc : ∀ x : D.host.E, cpt w (toEAf D (inclR (AF D.host.F) x)) = κ x := fun x => by
    rw [hκ]; exact GlobalTheory.FunObj.Good.cpt_incA w x
  have hPl : ∀ k, colsEq t e w (e (.inl k)) ∈ Assignment.one.block _ _ := fun k => by
    rw [colsEq_inl]; exact Finset.mem_filter.2 ⟨Finset.mem_univ _, rfl⟩
  have hPr : ∀ k, colsEq t e w (e (.inr k)) ∉ Assignment.one.block _ _ := fun k hk => by
    rw [colsEq_inr] at hk; exact Bool.false_ne_true (Finset.mem_filter.1 hk).2

  have z₁ : ∀ z : AE D, GlobalTheory.EmbChart.idem (Bs.τ v) * z = z → cpt w (toEAf D (cA D z)) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have z₂ : ∀ z : AE D, cA D (GlobalTheory.EmbChart.idem (Bs.τ v)) * z = z → cpt w (toEAf D z) = 0 := fun z hz => by
    rw [← hz, RingHom.map_mul, RingHom.map_mul, hzero, zero_mul]
  have hat : ∀ (u : Matrix (Fin (spW₁ G i j).rank) (Fin ((spW G i j).rank + (spW₁ G i j).rank)) (AE D)) (b b' : AE D),
      b * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b →
      b' * algebraMap (AF D.host.F) (AE D) (GlobalTheory.LatVac.liftV v.1 1) = b' →
      IsHalf b (u.submatrix id fun k => e (.inl k)) → IsHalf b' (u.submatrix id fun k => e (.inr k)) →
      At (evFin D.host.F v.1) u := fun u b b' hb hb' h1 h2 c hc => by
    have k1 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb h1 c hc
    have k2 := GlobalTheory.BigDat.smul_eq_zero_of_isHalf v.1 hb' h2 c hc
    refine Matrix.ext fun a s => ?_
    obtain ⟨z, rfl⟩ := e.surjective s
    rcases z with k | k
    · exact congrFun₂ k1 a k
    · exact congrFun₂ k2 a k
  refine ⟨?_, fun u => by rw [htr, linB_ptB, hκ]⟩
  unfold IsMixChart
  simp only [htr, hmu]
  refine ⟨fun u hu => ?_, fun u hu => ?_⟩
  · have h1 : IsHalf (GlobalTheory.EmbChart.idem (Bs.τ v)) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h1 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h2 a k)
    exact ⟨hat u _ _ hb₁ hb₂ h1 h2, zero_inl e _ _ _ hPr _ _ _ _ hZ, zero_inr e _ _ _ hPl _ _ _ _ hU,
      eq_add_of_blocks e _ _ _ _ _ _ _ _ _ _ _ hZ hU (mixCoS_inl t e w B κ hinc u) (mixCoS_inr t e w B κ hinc u)⟩
  · have h1 : IsHalf (cA D (GlobalTheory.EmbChart.idem (Bs.τ v))) (u.submatrix id fun k => e (.inl k)) := fun a c =>
      GlobalTheory.FlipMatch.ChartOpp.isHalf_of_mulG _ hu.1 c a
    have h2 := isHalf_cA_of_adjV₁ e hu.2
    rw [Formalism.L2.Theta.cA_cA] at h2
    have hZ : ((u.map fun a => cpt w (toEAf D (cA D a))).submatrix id fun k => e (.inr k)) = 0 :=
      Matrix.ext fun a k => z₁ _ (h2 a k)
    have hU : ((u.map fun a => cpt w (toEAf D a)).submatrix id fun k => e (.inl k)) = 0 :=
      Matrix.ext fun a k => z₂ _ (h1 a k)
    exact ⟨hat u _ _ hb₂ hb₁ h1 h2, zero_inr e _ _ _ hPl _ _ _ _ hZ, zero_inl e _ _ _ hPr _ _ _ _ hU⟩

end GlobalTheory.TopFlip.ChartB
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardPairMemSchwartzBruhatOfConductorExponent
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta Formalism.L2.DIV IsDedekindDomain NumberField MeasureTheory Matrix
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest GlobalTheory.SqTop GlobalTheory.SqTower GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames GlobalTheory.ChainFr GlobalTheory.SquareDict GlobalTheory.SquareComm GlobalTheory.BigNZ GlobalTheory.FlipMatch GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ Num IsTripleOf IsDatumA IsDatumB incM)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chars Rep Acts SInf At piW psiLoc chrW)
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.TopFlip

namespace GlobalTheory.StdPairSBDepth

open GlobalTheory.StdPairSB GlobalTheory.StdPairCone ValuativeRel

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem gfun_eq_mul (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c : ℕ) {m r : ℕ} (A : Matrix (Fin m) (Fin m) k)
    (B : Matrix (Fin m) (Fin r) k) :
    gfun ν ϖ c A B = gfun ν ϖ n A (0 : Matrix (Fin m) (Fin r) k) * gfun 1 ϖ c A B := by
  have h0 : ∀ (i : Fin m) (j : Fin r),
      (0 : Matrix (Fin m) (Fin r) k) i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ n) := by
    intro i j
    simp [GlobalTheory.SplitWeil.cball]
  unfold gfun
  by_cases h : A.det ≠ 0 ∧ IsGLO A ∧ ∀ i j, B i j ∈ GlobalTheory.SplitWeil.cball (ϖ ^ c)
  · rw [dite_eq_left h, dite_eq_left h, dite_eq_left ⟨h.1, h.2.1, h0⟩]
    simp
  · rw [dite_eq_right h, dite_eq_right h, mul_zero]

theorem isLocallyConstant_gfun' {ν : kˣ →* ℂˣ} {ϖ : kˣ} {n : ℕ} (c : ℕ) (hϖ : GlobalTheory.SplitFlip.IsUnif ϖ)
    (hν : GlobalTheory.SplitFlip.CondLE ϖ n ν) (m r : ℕ) :
    IsLocallyConstant
      (fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k => gfun ν ϖ c q.1 q.2) := by
  have h1 := (isLocallyConstant_gfun hϖ hν m r).comp_continuous
    (f := fun q : Matrix (Fin m) (Fin m) k × Matrix (Fin m) (Fin r) k =>
      (q.1, (0 : Matrix (Fin m) (Fin r) k))) (continuous_fst.prodMk continuous_const)
  have h2 := isLocallyConstant_gfun (ν := (1 : kˣ →* ℂˣ)) (c := c) hϖ (fun _ _ => rfl) m r
  have h3 := h1.mul h2
  convert h3 using 1
  funext q
  exact gfun_eq_mul ν ϖ n c q.1 q.2

end GlobalTheory.StdPairSBDepth


open GlobalTheory.StdPairCone ValuativeRel in
theorem GlobalTheory.StdPairSBDepth.stdPair_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (ν : kˣ →* ℂˣ) (ϖ : kˣ) (n c a a' : ℕ), IsUnif ϖ → CondLE ϖ n ν →
      GlobalTheory.StdPairCone.stdA ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a) (Fin (a + a')) k) ∧
        GlobalTheory.StdPairCone.stdB ν ϖ c a a' ∈ GlobalTheory.WeilM.SB (Matrix (Fin a') (Fin (a + a')) k) := by
  intro k _ _ _ _ ν ϖ n c a a' hϖ hν
  haveI := GlobalTheory.SplitWeil.t2Space k
  have hc1 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₁ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.castAdd a' j)
  have hc2 : ∀ m : ℕ, Continuous fun X : Matrix (Fin m) (Fin (a + a')) k => blk₂ X := by
    intro m; exact continuous_pi fun i => continuous_pi fun j => continuous_id.matrix_elem i (Fin.natAdd a j)
  have hK : ∀ m : ℕ, IsCompact (Set.univ.pi fun _ : Fin m => Set.univ.pi fun _ : Fin (a + a') => (𝒪[k] : Set k) :
      Set (Matrix (Fin m) (Fin (a + a')) k)) :=
    fun m => isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => GlobalTheory.SplitWeil.isCompact_int k
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · have : stdA ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun X => (blk₁ X, blk₂ X) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSBDepth.isLocallyConstant_gfun' c hϖ hν a a').comp_continuous ((hc1 a).prodMk (hc2 a))
  · refine HasCompactSupport.intro (hK a) fun X hX => ?_
    by_contra hne
    obtain ⟨h1, h2⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₁ X) (B := blk₂ X) hϖ hne
    exact hX fun i _ j _ => Fin.addCases (motive := fun j => X i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
  · have : stdB ν ϖ c a a' = (fun q => GlobalTheory.StdPairSB.gfun ν ϖ c q.1 q.2) ∘ fun Y => (blk₂ Y, blk₁ Y) := rfl
    rw [this]
    exact (GlobalTheory.StdPairSBDepth.isLocallyConstant_gfun' c hϖ hν a' a).comp_continuous ((hc2 a').prodMk (hc1 a'))
  · refine HasCompactSupport.intro (hK a') fun Y hY => ?_
    by_contra hne
    obtain ⟨h2, h1⟩ := GlobalTheory.StdPairSB.integral_of_ne (A := blk₂ Y) (B := blk₁ Y) hϖ hne
    exact hY fun i _ j _ => Fin.addCases (motive := fun j => Y i j ∈ 𝒪[k]) (fun j => h1 i j) (fun j => h2 i j) j
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TateModuleFreeFinrankTwoMulDim
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AV.AbVar

theorem tl_free_finrank : ∀ (K : Type) [Field K] (l : ℕ) [Fact l.Prime], (l : K) ≠ 0 → ∀ (A : AbVar K), Module.Free ℤ_[l] (Tl l A) ∧ Module.Finite ℤ_[l] (Tl l A) ∧ Module.finrank ℤ_[l] (Tl l A) = 2 * A.dim ∧ Module.Finite ℚ_[l] (Vl l A) ∧ Module.finrank ℚ_[l] (Vl l A) = 2 * A.dim := by
  intro K _ l _ hl A
  have hc : ∀ n : ℕ, Nat.card {x : A.Pt // x ^ (l ^ n) = 1} = l ^ (2 * A.dim * n) := by
    intro n
    have h := GlobalTheory.T.card_torsion_geometricPoints_eq_pow_two_dim K A (l ^ n) (by push_cast; exact pow_ne_zero _ hl)
    rw [h, ← pow_mul, mul_comm n]
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.TateFree.free_finite_finrank A.Pt l (2 * A.dim) hc
  refine ⟨h1, h2, h3, inferInstance, ?_⟩
  rw [Module.finrank_baseChange, h3]

end GlobalTheory.AV.AbVar
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorDegDataUnitaryTypeStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensorDegData_unitary_type : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) , ∀ (D D' : DegData R (maximalIdeal R)) {r : ℕ} (W : Matrix (Fin r) (Fin r) ℤ), ((W + W.transpose).map (Int.cast : ℤ → ℝ)).PosDef → IsUnit (W + W.transpose).det → ∀ T : Tens D.toPre D'.toPre W, ∀ (ρ : 𝓞 E →+* Matrix (Fin r) (Fin r) ℤ), (∀ a, (ρ a).transpose * (W + W.transpose) = (W + W.transpose) * ρ (H.bar a)) → W = (W + W.transpose) * ρ H.w0 → Nontrivial D.toPre.X → 1 ≤ r → ∀ [Module (𝓞 E) D'.toPre.X] (o : letI := H.starRing; D'.toPre.OAct (𝓞 E)), (letI := H.starRing; T.IsAct o ρ) → (letI := H.starRing; TraceFormTwistIso D'.toPre o H.w0) → ∃ Dm : Datum H, PelOK Dm D'.toPre o := by
  first | exact @GlobalTheory.Mum.tens_pelOK | exact GlobalTheory.Mum.tens_pelOK | (intros; apply GlobalTheory.Mum.tens_pelOK <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSeesawTripleMovedToSelfDualIsValid
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.DivisionValues (vw)
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.CMVal (IsHeckeL)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.SqTop
open GlobalTheory.ConstRatio (NegIdx Factor)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.BotMove
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle GlobalTheory.Grid Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Mult MeasureTheory

noncomputable section

namespace GlobalTheory.BotMove

theorem rig_move {D : D7} {V : HSp D} (rr : Rig V) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (g : GA D V)
    (hr : rr.Is) (hΛ : IsSelfDualC V Λ) (hm : GlobalTheory.FinPl.Moves V g rr.Λ Λ (fun _ => True)) :
    Rig.Is (⟨Λ, Lev.finE V g * rr.β, rr.s, rr.B⟩ : Rig V) :=
  ⟨hΛ, GlobalTheory.Core.Mi.FrameMove.isFrame_of_moves D V g rr.Λ Λ rr.β hm hr.2.1, hr.2.2⟩

theorem moveTri_is : ∀ {D : D7} {T : Type} {A A' WW : HSp D} (Y : Tri T A A' WW) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (α β : T → ((AE D)ˣ →* Circle)) (νH : T → HChar D.host.E) (S : T → Finset (Formalism.L2.DIV.Pl D.host.E)),
    Y.Is ψ θ α β νH S →
    ∀ (ΛA : Submodule (𝓞 D.host.E) (Fin A.rank → D.host.E)) (ΛA' : Submodule (𝓞 D.host.E) (Fin A'.rank → D.host.E))
      (ΛW : Submodule (𝓞 D.host.E) (Fin WW.rank → D.host.E)),
    IsSelfDualC A ΛA → IsSelfDualC A' ΛA' → IsSelfDualC WW ΛW →
    ∀ g ∈ GfC A, ∀ g' ∈ GfC A', ∀ h ∈ GfC WW,
    GlobalTheory.FinPl.Moves A g Y.rA.Λ ΛA (fun _ => True) → GlobalTheory.FinPl.Moves A' g' Y.rA'.Λ ΛA' (fun _ => True) →
    GlobalTheory.FinPl.Moves WW h Y.rW.Λ ΛW (fun _ => True) →
    ∀ (t₀ : T) (r r' : T → ℂ), (∀ t, r t ≠ 0 ∧ r' t ≠ 0) →
    (∀ t, Y.ω t (g, h) Y.vac = r t • Y.ω t₀ (g, h) Y.vac) → (∀ t, Y.ω' t (g', h) Y.vac' = r' t • Y.ω' t₀ (g', h) Y.vac') →
    (moveTri Y ΛA ΛA' ΛW g g' h t₀ r r').Is ψ θ α β νH S := by
  intro D T A A' WW Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv'
  exact ⟨hY.rank, rig_move _ _ _ hY.rigA hA mA, rig_move _ _ _ hY.rigA' hA' mA', rig_move _ _ _ hY.rigW hW mW, hY.weil,
    hY.weil', GlobalTheory.T.movedVacuum_negHom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', GlobalTheory.T.movedVacuum_hom_eq_vacuum_movedLattices Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', hY.idem, hY.expo, GlobalTheory.T.movedFiniteDatum_negHom_eq_standardPair_first Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv',
    _root_.GlobalTheory.BotMoveSnd.snd_moved Y ψ θ α β νH S hY ΛA ΛA' ΛW hA hA' hW g hg g' hg' h hh mA mA' mW t₀ r r' hr hv hv', _root_.GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain _ _ g hY.meas.1 hY.meas.2, _root_.GlobalTheory.RightTranslateFundDomain.haar_and_fundDomain _ _ g' hY.meas'.1 hY.meas'.2⟩

end GlobalTheory.BotMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalChartsOfSiegelOfForFan
section
namespace GlobalTheory.Published

theorem toroidalCharts_of_siegel_of_forFan (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hF : GlobalTheory.Published.ToroidalChartsForFan) :
    GlobalTheory.Published.ToroidalCharts := by
  refine hF.toroidalCharts fun E _ _ _ H q => ?_
  obtain ⟨φs, hφ, -⟩ := hS (Module.finrank ℚ E * q + 1) (Nat.le_add_left _ _)
  obtain ⟨φ, h₁, h₂, -⟩ := GlobalTheory.PolFan.exists_fine_invariant_fan H hφ (Nat.le_succ _) ∅ (by simp)
  exact ⟨φ, h₁, h₂⟩

end GlobalTheory.Published
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceLatticeLeSpanThetaSeriesAwayFromOwnPrimeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT Formalism.IndefR.Datum Formalism.IndefR.Lev
open GlobalTheory.FormTies GlobalTheory.OnTies GlobalTheory.TraceClassRank
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.OnCmp GlobalTheory.BigOn GlobalTheory.RealIndexBound
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.traceLattice_le_span_thetaSeries_awayFromOwnPrime : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : Full D) [Algebra T.J.Q.c.F D.what₂.LL] (R : RealDat D A T.J.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec) (fw : FWTie T.J R κ v₀) (O : ∀ i, OMDat T.J.toCore R i Unit (fun _ => A.μ0)) (hT : LawsFull T), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m), OMPins T.J R κ v₀ O i → R.βV i = 1 → R.LUnif → IoExt R → OneMapRow0 T.J R κ v₀ O i → PhaseTie T.J R κ v₀ O (fun _ => 1) i → GlobalTheory.OneMapAll.ClassSumsSpan (O i) (κ i) → ∀ (v : HeightOneSpectrum (𝓞 D.what₂.LL)), v ∈ R.twPl → R.tup_mu_on → QGuard R → GlobalTheory.FinalJoin2.FieldOK0 D (ownAt D v) → Formalism.L2.Host.ValLL0 D R.C → (∀ x, (((R.C.delAt (Formalism.EigenvalueLevelCeiling.plc v)).1 x : ℂˣ) : ℂ) ∈ D.what₂.embLL.range) → T.J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal → RunPin (T := T) R i (κ i).n v (ownAt D v) → ∀ (ℓ : G → (LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l ≃ₗ[𝓞 D.host.E] LaMod (T.Q.Dw ((i : ℕ) + 1)) T.Q.l)), LevelPin (T := T) R i ℓ → ActionPin (T := T) (R := R) hT.p fw i ℓ → ∀ (U : Subgroup G), (∀ u : U, ∀ PP : R.Pg, ((R.eG (u : G) PP : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) (kP PP.1)).det = 1) → ∀ (ψ : U →* D.what₂.LLˣ), CompareOffOwn hT.p fw i ℓ U ψ 1 v (ownAt D v) := by
  first | exact @GlobalTheory.CompareOff.compareOffOwn_run | exact GlobalTheory.CompareOff.compareOffOwn_run | (intros; apply GlobalTheory.CompareOff.compareOffOwn_run <;> assumption)
end

