module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GlobSet
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0014
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NinfGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.BaseOfCore
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0075
public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.EmbeddingIntegerAlgebraMap
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.LocFacts
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0364
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SaturatedPf
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0129
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0370

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.GramDetJoinedFamilyEqPmNormDifference
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory.GramDet

theorem det_sub_single {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (Y : Matrix n n E) (l : n) (d : E) :
    (Y - Matrix.single l l d).det = Y.det - d * Y.adjugate l l := by
  have h : Y - Matrix.single l l d = Y.updateRow l (Y l + (-d) • (Pi.single l 1 : n → E)) := by
    ext i j
    by_cases hi : i = l
    · subst hi
      by_cases hj : j = i
      · subst hj; simp [sub_eq_add_neg]
      · simp [hj, Ne.symm hj]
    · simp [Matrix.updateRow_ne hi, Ne.symm hi]
  rw [h, Matrix.det_updateRow_add, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self,
    Matrix.adjugate_apply]
  ring

theorem det_blocks_single {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (Z Y : Matrix n n E) (l : n) (c c' : E) (hZ : IsUnit Z.det) :
    (Matrix.fromBlocks Z (Matrix.single l l c) (Matrix.single l l c') Y).det
      = Z.det * Y.det - c * c' * (Z.adjugate l l * Y.adjugate l l) := by
  letI := Matrix.invertibleOfIsUnitDet Z hZ
  rw [Matrix.det_fromBlocks₁₁, Matrix.single_mul_mul_single, det_sub_single]
  have h : Z.det * (⅟Z) l l = Z.adjugate l l := by
    rw [Matrix.invOf_eq_nonsing_inv, Matrix.inv_def, Matrix.smul_apply, smul_eq_mul, ← mul_assoc,
      Ring.mul_inverse_cancel _ hZ, one_mul]
  rw [← h]; ring

theorem det_blocks_swap {E : Type} [CommRing E] {n : Type} [Fintype n] [DecidableEq n]
    (A B C D : Matrix n n E) :
    (Matrix.fromBlocks A B C D).det = (Matrix.fromBlocks B A D C).det ∨
    (Matrix.fromBlocks A B C D).det = -(Matrix.fromBlocks B A D C).det := by
  have h := Matrix.det_permute' (Equiv.sumComm n n) (Matrix.fromBlocks B A D C)
  have h2 : (Matrix.fromBlocks B A D C).submatrix id (Equiv.sumComm n n)
      = Matrix.fromBlocks A B C D := by
    ext (i | i) (j | j) <;> rfl
  rw [h2] at h
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumComm n n)) with h1 | h1
  · left; rw [h, h1]; simp
  · right; rw [h, h1]; simp

theorem adjugate_last {E : Type} [CommRing E] {r : ℕ} (Z : Matrix (Fin (r + 1)) (Fin (r + 1)) E) :
    Z.adjugate (Fin.last r) (Fin.last r) = (Z.submatrix Fin.castSucc Fin.castSucc).det := by
  rw [Matrix.adjugate_fin_succ_eq_det_submatrix, Fin.succAbove_last, ← two_mul, pow_mul]
  simp

theorem det_gram_sum_elim {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {r : ℕ} (f f' : Fin (r + 1) → V) (T T' : F) (hf : ∀ a b, H.h (f a) (f b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T) else 0) (hf' : ∀ a b, H.h (f' a) (f' b) = if a = Fin.last r ∧ b = Fin.last r then -(algebraMap F E T') else 0) (hD : IsUnit (H.Dl f f' (r + 1))) : (H.gram (Sum.elim f f')).det = H.Gdet f f' T T' ∨ (H.gram (Sum.elim f f')).det = -H.Gdet f f' T T' := by
  set Z := H.Zhat f f' with hZ
  have hD1 : H.Dl f f' (r + 1) = Z.det := by
    simp [HermSp.Dl, hZ]
  have hD0 : H.Dl f f' r = Z.adjugate (Fin.last r) (Fin.last r) := by
    rw [adjugate_last]
    simp only [HermSp.Dl, Nat.le_succ, dif_pos]
    rfl
  set c : E →+* E := (M.L.cj : E →+* E) with hc
  have hg : H.gram (Sum.elim f f') = Matrix.fromBlocks
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T))) Z (c.mapMatrix Z).transpose
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T'))) := by
    ext (i | i) (j | j)
    · simp [HermSp.gram, hf, Matrix.single_apply, and_comm, eq_comm]
    · rfl
    · exact H.h_herm _ _
    · simp [HermSp.gram, hf', Matrix.single_apply, and_comm, eq_comm]
  have hG : H.Gdet f f' T T' = (Matrix.fromBlocks Z
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T)))
      (Matrix.single (Fin.last r) (Fin.last r) (-(algebraMap F E T')))
      (c.mapMatrix Z).transpose).det := by
    rw [det_blocks_single _ _ _ _ _ (hD1 ▸ hD), Matrix.det_transpose, ← RingHom.map_det,
      ← Matrix.adjugate_transpose, ← RingHom.map_adjugate, HermSp.Gdet, hD1, hD0]
    simp [HermSp.normE, hc]
  rw [hg, hG]
  exact det_blocks_swap _ _ _ _

end GlobalTheory.GramDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarMeasureBesselUnitaryEqPullbackProduct
section
open scoped Classical ENNReal
open MeasureTheory Matrix NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.Full Formalism.L2.SG.LocWSOf GlobalTheory.TypeAsm
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.PullHaarW

open Formalism.L2.SG.RealObj

section Gen

variable {k r n : ℕ} {ε : Fin n → Bool} {Q : Matrix (Fin n) (Fin (2 * r + k + 1)) ℂ}
  {Qi : Matrix (Fin (2 * r + k + 1)) (Fin n) ℂ}

theorem trG_memUH (h2 : Q * Qi = 1) (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) (γ : Formalism.REAL.UJ ε) :
    trG Q Qi γ ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r) := by
  have hγ : (Formalism.MainNotions.S.uMat γ)ᴴ * Formalism.REAL.Jm ε * Formalism.MainNotions.S.uMat γ = Formalism.REAL.Jm ε := γ.2
  have hQi := Formalism.L2.SG.Pf.Choice.qiHqi ε h2 hg
  show (Qi * Formalism.MainNotions.S.uMat γ * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qi * Formalism.MainNotions.S.uMat γ * Q) = Formalism.QuantumDeterminants.Hpk k r
  calc (Qi * Formalism.MainNotions.S.uMat γ * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qi * Formalism.MainNotions.S.uMat γ * Q)
      = Qᴴ * ((Formalism.MainNotions.S.uMat γ)ᴴ * (Qiᴴ * Formalism.QuantumDeterminants.Hpk k r * Qi) * Formalism.MainNotions.S.uMat γ) * Q := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = Formalism.QuantumDeterminants.Hpk k r := by rw [hQi, hγ, hg]

theorem trG_surj (hn : n = 2 * r + k + 1) (h1 : Qi * Q = 1) (h2 : Q * Qi = 1)
    (hg : Qᴴ * Formalism.REAL.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r) {x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ}
    (hx : x ∈ Formalism.QuantumDeterminants.UH (Formalism.QuantumDeterminants.Hpk k r)) : ∃ γ : Formalism.REAL.UJ ε, trG Q Qi γ = x := by
  subst hn
  have hx' : xᴴ * Formalism.QuantumDeterminants.Hpk k r * x = Formalism.QuantumDeterminants.Hpk k r := hx
  have hQiH := Formalism.L2.SG.Pf.Choice.qiHqi ε h2 hg
  have hγ : (Q * x * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * x * Qi) = Formalism.REAL.Jm ε := by
    calc (Q * x * Qi)ᴴ * Formalism.REAL.Jm ε * (Q * x * Qi)
        = Qiᴴ * (xᴴ * (Qᴴ * Formalism.REAL.Jm ε * Q) * x) * Qi := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Formalism.REAL.Jm ε := by rw [hg, hx', hQiH]
  refine ⟨Formalism.L2.SG.Pf.WFL.toUJ (Q * x * Qi) hγ, ?_⟩
  show Qi * (Q * x * Qi) * Q = x
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, h1, Matrix.one_mul, Matrix.mul_assoc, h1, Matrix.mul_one]

theorem trG_fix (h2 : Q * Qi = 1) (γ : Formalism.REAL.UJ ε) (w : Fin n → ℂ) :
    trG Q Qi γ *ᵥ (Qi *ᵥ w) = Qi *ᵥ w ↔ Formalism.MainNotions.S.uMat γ *ᵥ w = w := by
  have key : trG Q Qi γ *ᵥ (Qi *ᵥ w) = Qi *ᵥ (Formalism.MainNotions.S.uMat γ *ᵥ w) := by
    simp only [trG, Matrix.mulVec_mulVec, Matrix.mul_assoc, h2, Matrix.mul_one]
  rw [key]
  constructor
  · intro h
    have e : ∀ y, Q *ᵥ (Qi *ᵥ y) = y := fun y => by rw [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
    have h' : Q *ᵥ (Qi *ᵥ (Formalism.MainNotions.S.uMat γ *ᵥ w)) = Q *ᵥ (Qi *ᵥ w) := congrArg _ h
    rwa [e, e] at h'
  · intro h
    rw [h]

theorem trG_fix_single (h1 : Qi * Q = 1) (h2 : Q * Qi = 1) (γ : Formalism.REAL.UJ ε) (i : Fin (2 * r + k + 1)) (c : ℂ)
    (w : Fin n → ℂ) (hQ : Q *ᵥ Pi.single i 1 = c • w) :
    trG Q Qi γ *ᵥ Pi.single i 1 = Pi.single i 1 ↔ Formalism.MainNotions.S.uMat γ *ᵥ w = w := by
  have hb : (Pi.single i 1 : Fin (2 * r + k + 1) → ℂ) = Qi *ᵥ (c • w) := by
    rw [← hQ, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have hc : c ≠ 0 := by
    rintro rfl
    have h0 : (Pi.single i 1 : Fin (2 * r + k + 1) → ℂ) = 0 := by rw [hb, zero_smul, Matrix.mulVec_zero]
    have h := congrFun h0 i
    simp at h
  rw [hb, trG_fix h2, Matrix.mulVec_smul]
  constructor
  · intro h
    exact smul_right_injective _ hc h
  · intro h
    rw [h]

end Gen

section Set

variable {D : D7} {X : HidaSetting D}

theorem trG_mem_UW_iff (C : Choice X 1) (u : D.what₂.Word) (τ : D.what₂.Tau) (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) :
    trG (C.Q τ) (C.Qi τ) γ ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) ↔
      (∀ a, Formalism.MainNotions.S.uMat γ *ᵥ rv X.B.I (vOf X τ) (X.eR a) = rv X.B.I (vOf X τ) (X.eR a)) ∧
      (∀ a, Formalism.MainNotions.S.uMat γ *ᵥ rv X.B.I (vOf X τ) (X.fR a) = rv X.B.I (vOf X τ) (X.fR a)) ∧
      Formalism.MainNotions.S.uMat γ *ᵥ rv X.B.I (vOf X τ) (X.zR u) = rv X.B.I (vOf X τ) (X.zR u) := by
  obtain ⟨h1, h2, hg, hef⟩ := C.isT τ
  simp only [Formalism.QuantumDeterminants.UWset, Set.mem_setOf_eq, zB, Formalism.QuantumDeterminants.bvec]
  rw [trG_fix h2]
  constructor
  · rintro ⟨-, ha, hz⟩
    exact ⟨fun a => (trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).1).1 (ha a).1,
      fun a => (trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).2).1 (ha a).2, hz⟩
  · rintro ⟨he, hf, hz⟩
    exact ⟨trG_memUH h2 hg γ, fun a => ⟨(trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).1).2 (he a),
      (trG_fix_single h1 h2 γ _ _ _ (hef a a rfl).2).2 (hf a)⟩, hz⟩

theorem mem_Hset_iff (C : Choice X 1) (u : D.what₂.Word) (x : X.B.I.Ginf) :
    x ∈ Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) ↔
      ∀ τ, Matrix.of (trI C x τ) ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ) := by
  simp only [trI, Equiv.apply_symm_apply]
  simp_rw [trG_mem_UW_iff C u]
  constructor
  · intro hx τ
    exact ⟨fun a => hx _ _ (Or.inl (Or.inl ⟨a, rfl⟩)), fun a => hx _ _ (Or.inl (Or.inr ⟨a, rfl⟩)),
      hx _ _ (Or.inr rfl)⟩
  · intro h v y hy
    obtain ⟨τ, rfl⟩ : ∃ τ, v = vOf X τ := ⟨X.pl v, (X.pl.symm_apply_apply v).symm⟩
    obtain ⟨he, hf, hz⟩ := h τ
    rcases hy with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hy
    · exact he a
    · exact hf a
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact hz

end Set

open Formalism.L2.SG.RealObj.InfCut.ProductExactness

section Meas

variable {D : D7} {X : HidaSetting D}

theorem n_eq' : X.B.I.n = 2 * D.R.rS + D.R.k + 1 := by
  rw [X.n_eq, dimS_eq]

theorem trI_eq (C : Choice X 1) : trI C = Pi.map (fun τ (γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ))) =>
    (Matrix.of.symm (trG (C.Q τ) (C.Qi τ) γ) : Formalism.QuantumDeterminants.Mt D.R.k D.R.rS)) ∘
    (Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm).symm := by
  funext x τ
  simp [trI, Pi.map]
  rfl

theorem trI_closedEmb (C : Choice X 1) : Topology.IsClosedEmbedding (trI C) := by
  rw [trI_eq]
  exact (Topology.IsClosedEmbedding.piMap fun τ => Formalism.L2.SG.Pf.BaseOf.trG_closedEmb n_eq'
    (X.B.I.ε (vOf X τ)) (C.isT τ).2.1).comp (Homeomorph.piCongrLeft _).symm.isClosedEmbedding

theorem UW_sub_range (C : Choice X 1) (u : D.what₂.Word) :
    {y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS | ∀ τ, Matrix.of (y τ) ∈
      Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)} ⊆ Set.range (trI C) := by
  intro y hy
  have h : ∀ τ, ∃ γ : Formalism.REAL.UJ (X.B.I.ε (vOf X τ)), trG (C.Q τ) (C.Qi τ) γ = Matrix.of (y τ) := fun τ =>
    trG_surj n_eq' (C.isT τ).1 (C.isT τ).2.1 (C.isT τ).2.2.1 (hy τ).1
  choose γ hγ using h
  refine ⟨Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm γ, ?_⟩
  funext τ
  have key : (Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm γ) (vOf X τ) = γ τ :=
    congrFun (Homeomorph.symm_apply_apply
      (Homeomorph.piCongrLeft (Y := fun v => Formalism.REAL.UJ (X.B.I.ε v)) X.pl.symm) γ) τ
  simp only [trI]
  rw [key, hγ τ]
  rfl

end Meas

theorem pullH : ∀ (D : D7) (X : HidaSetting D) (C : Choice X 1) (hB : WuBessel C), GoodLoc C hB →
    ∀ u : D.what₂.Word, ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ X.muH u Set.univ = c ∧
      ∀ A : Set X.B.I.Ginf, MeasurableSet A → X.muH u A = c * Measure.pi (C.muW u) (trI C '' A) := by
  intro D X C _ _ u
  have he : MeasurableEmbedding (trI C) := (trI_closedEmb C).measurableEmbedding
  haveI : ∀ τ, SigmaFinite (C.muW u τ) := fun τ => (C.muW_haar u τ).1
  set μ := Measure.pi (C.muW u) with hμ
  set P : Set (D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) := Set.univ.pi (fun τ =>
    {m | Matrix.of m ∈ Formalism.QuantumDeterminants.UWset D.R.k D.R.rS (zB X (C.Qi τ) u τ)}) with hP
  have hPc : μ Pᶜ = 0 := PiM.pi_conc _ _ fun τ => (C.muW_haar u τ).2.2.1
  have hPr : P ⊆ Set.range (trI C) := fun y hy => UW_sub_range C u (fun τ => hy τ (Set.mem_univ τ))
  have hrc : μ (Set.range (trI C))ᶜ = 0 := measure_mono_null (Set.compl_subset_compl.2 hPr) hPc
  set ρ := μ.comap (trI C) with hρ
  have hρA : ∀ A, ρ A = μ (trI C '' A) := fun A => he.comap_apply μ A
  have hμ1 : μ Set.univ = 1 := by
    rw [hμ, Measure.pi_univ]
    simp [C.muW_one]
  have hρ1 : ρ Set.univ = 1 := by
    rw [hρA, Set.image_univ, ← hμ1]
    refine le_antisymm (measure_mono (Set.subset_univ _)) ?_
    calc μ Set.univ ≤ μ (Set.range (trI C)) + μ (Set.range (trI C))ᶜ := measure_univ_le_add_compl _
      _ = μ (Set.range (trI C)) := by rw [hrc, add_zero]
  haveI : IsFiniteMeasure ρ := ⟨by rw [hρ1]; exact ENNReal.one_lt_top⟩
  have hρ0 : ρ ≠ 0 := fun h => by
    have h1 := hρ1
    rw [h] at h1
    simp at h1
  let H : Subgroup X.B.I.Ginf := Formalism.L2.SG.PoincareInHH.HinfS X.B.I
    (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)})
  have hH : (H : Set X.B.I.Ginf) = Hset X.B.I (Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.eX a)) ∪
      Set.range (fun a => crdOf X.B.I X.ιE X.bas (X.fY a)) ∪ {crdOf X.B.I X.ιE X.bas (X.zu u)}) := rfl
  have hHclosed : IsClosed (H : Set X.B.I.Ginf) := by
    show IsClosed {s : X.B.I.Ginf | ∀ v, ∀ x ∈ _, Formalism.MainNotions.S.uMat (s v) *ᵥ rv X.B.I v x = rv X.B.I v x}
    simp only [Set.setOf_forall]
    refine isClosed_iInter fun v => isClosed_iInter fun x => isClosed_iInter fun _ => isClosed_eq ?_ continuous_const
    exact Continuous.matrix_mulVec ((Units.continuous_val.comp continuous_subtype_val).comp (continuous_apply v)) continuous_const
  have hHc : ρ (H : Set X.B.I.Ginf)ᶜ = 0 := by
    rw [hH, hρA]
    refine measure_mono_null ?_ hPc
    rintro _ ⟨x, hx, rfl⟩ hy
    exact hx ((mem_Hset_iff C u x).2 fun τ => hy τ (Set.mem_univ τ))
  have hmapρ : ρ.map (trI C) = μ := by
    rw [hρ, he.map_comap, Measure.restrict_eq_self_of_ae_mem (by rw [ae_iff]; exact hrc)]
  have hinv : ∀ s ∈ H, ρ.map (fun x => s * x) = ρ := by
    intro s hs
    have hs' := (mem_Hset_iff C u s).1 (by rw [← hH]; exact hs)
    have hcomm : trI C ∘ (fun x => s * x) =
        (fun y τ => Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)) (y τ)) ∘ trI C := by
      funext x τ
      show C.Qi τ * (Formalism.MainNotions.S.uMat (s (vOf X τ)) * Formalism.MainNotions.S.uMat (x (vOf X τ))) * C.Q τ =
        C.Qi τ * Formalism.MainNotions.S.uMat (s (vOf X τ)) * C.Q τ * (C.Qi τ * Formalism.MainNotions.S.uMat (x (vOf X τ)) * C.Q τ)
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc (C.Q τ) (C.Qi τ), (C.isT τ).2.1, Matrix.one_mul]
    have hLm : Measurable (fun (y : D.what₂.Tau → Formalism.QuantumDeterminants.Mt D.R.k D.R.rS) τ =>
        Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)) (y τ)) :=
      Measurable.of_eval fun τ => (Formalism.L2.SG.Pf.WFL.measurable_lmulM _).comp (measurable_pi_apply τ)
    have hμL : μ.map (fun y τ => Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)) (y τ)) = μ := by
      haveI : ∀ τ, SigmaFinite ((C.muW u τ).map (Formalism.QuantumDeterminants.lmulM (Matrix.of (trI C s τ)))) := fun τ => by
        rw [(C.muW_haar u τ).2.2.2 _ (hs' τ)]
        infer_instance
      rw [hμ, Measure.pi_map_pi (fun τ => (Formalism.L2.SG.Pf.WFL.measurable_lmulM _).aemeasurable)]
      congr 1
      funext τ
      exact (C.muW_haar u τ).2.2.2 _ (hs' τ)
    rw [← he.comap_map (ρ.map (fun x => s * x)), Measure.map_map he.measurable (measurable_const_mul s), hcomm,
      ← Measure.map_map hLm he.measurable, hmapρ, hμL]
  obtain ⟨hσ, h0, hc, hi⟩ := X.muH_haar u
  haveI := hσ
  rw [← hH] at hc hi
  obtain ⟨κ, hκ0, hκT, hκ⟩ := PiM.uniq_on_closed (H) hHclosed (X.muH u) ρ hc hHc hi hinv h0 hρ0
  refine ⟨κ, hκ0, hκT, ?_, fun A _ => ?_⟩
  · rw [hκ, Measure.smul_apply, hρ1, smul_eq_mul, mul_one]
  · rw [hκ, Measure.smul_apply, hρA, smul_eq_mul]

end GlobalTheory.PullHaarW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegersDenseLocalIntegersModG
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.IotaDense

theorem iota_dense : ∀ (D : D7) (p : PlF D), ∀ c ∈ (D.s.atP p).O, ∃ a : 𝓞 D.host.E, ∃ o ∈ (D.s.atP p).O,
    c = (D.s.atP p).ιE (a : D.host.E) + (D.s.atP p).ιE ((gS D : ℕ) : D.host.E) * o := by
  intro D p c hc
  obtain ⟨hR, -, -, -, hO, -, -, -, hunit, hcl⟩ := GlobalTheory.LocAtTopology.locAt_topology D.sp.cm D.conjF
    (fun x => by rw [D.conjF_eq, Formalism.BasicNotions.Examples₂.star_eq_conj]) p (D.s.atP p)
  have hg : ((gS D : ℕ) : D.host.E) ≠ 0 := by
    have : gS D ≠ 0 := by
      unfold gS
      exact mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero
    exact_mod_cast this
  obtain ⟨w, hw⟩ := hunit _ hg
  set S : Set (D.s.atP p).Ep := (fun z => ((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - z)) ⁻¹' ((D.s.atP p).O : Set _)
    with hSdef
  have hSo : IsOpen S := hO.preimage (continuous_const.mul (continuous_const.sub continuous_id))
  have hcS : c ∈ S := by
    show _ * (c - c) ∈ (D.s.atP p).O
    rw [sub_self, mul_zero]; exact zero_mem _
  have hcc : c ∈ closure (Set.range fun x : 𝓞 D.host.E => (D.s.atP p).ιE (x : D.host.E)) := by
    rw [hcl]; exact hc
  obtain ⟨z, hzS, a, rfl⟩ := mem_closure_iff.1 hcc S hSo hcS
  refine ⟨a, _, hzS, ?_⟩
  show c = _ + _ * (((w⁻¹ : (D.s.atP p).Epˣ) : (D.s.atP p).Ep) * (c - _))
  rw [← hw, ← mul_assoc, Units.mul_inv, one_mul]
  ring

end GlobalTheory.IotaDense
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicPartEqSpanScaledFrameUnitriangular
section
noncomputable section

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full
  Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RowLatXS

theorem xlam_eq_span_scaled : ∀ (D : D7) (T : D.host.E) (G : LFlag (D.sp.Y 0) D.R.rS T) (Z : LocDat D) (A : ∀ p : PlF D, LocNG.FrameD (locH Z p) D.R.rS), (∀ p, (A p).f = fun a => frFac Z.δ p a • baseChange₂ D p (frame G a)) → ∀ Λ : LV D, Submodule.IsLattice D.host.E Λ → (∀ p, ∃ n ∈ (A p).N, ∃ L, (A p).IsInner L ∧ lattice₂ D Z.M p Λ = LocNG.img n ((A p).LamStd L)) → ∃ e' : Fin D.R.rS → (VS D).V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ XLam Λ G = Submodule.span (𝓞 D.host.E) {y | ∃ (a : Fin D.R.rS) (x : D.host.E), x ∈ (ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) ∧ y = x • e' a} := by
  intro D T G Z A hA Λ hΛ hloc
  have hdd : ddS D ≠ 0 := by
    unfold ddS
    rw [Ne, FractionalIdeal.coeIdeal_eq_zero, Ideal.map_eq_bot_iff_of_injective]
    · exact differentIdeal_ne_bot
    · exact FaithfulSMul.algebraMap_injective _ _
  have hJ : ∀ a : Fin D.R.rS, GlobalTheory.RowLatXS.Ia Λ G.fl a =
      ((ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ))) : FractionalIdeal (nonZeroDivisors (𝓞 D.host.E)) D.host.E) :
        Submodule (𝓞 D.host.E) D.host.E) := by
    intro a
    refine _root_.GlobalTheory.Sloc.fg_eq_of_completions D Z _ _ (GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).1
      (FractionalIdeal.fg_of_isNoetherianRing le_rfl _) (fun p => ?_)
    rw [_root_.GlobalTheory.RowLatXS.span_coefIdeal_eq_span_frFac D T G Z A hA Λ hΛ hloc p a]
    have h := Formalism.L2.SG.Pf.locDiffC_holds D Z p a.castSucc
    simp only [Fin.coe_castSucc] at h
    exact h.symm
  obtain ⟨e', he, hX⟩ := _root_.GlobalTheory.RowLatAssembly.xLam_eq_span (VS D) D.R.rS T G Λ
    (fun a => ddS D ^ (-((D.R.rS : ℤ) - (a : ℕ)))) (fun a => zpow_ne_zero _ hdd)
    (fun a x hx hxa => by
      have h1 : G.fl.coefX x a ∈ GlobalTheory.RowLatXS.Ia Λ G.fl a :=
        ((GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).2 _).2 ⟨x, hx, hxa, rfl⟩
      rw [hJ a] at h1
      exact h1)
    (fun a t ht => by
      have h1 : t ∈ GlobalTheory.RowLatXS.Ia Λ G.fl a := by rw [hJ a]; exact ht
      exact ((GlobalTheory.T.flagCoeffIdealOfLattice_fg_and_mem_iff _ _ _ G.fl Λ a hΛ.fg).2 t).1 h1)
  exact ⟨e', he, hX⟩

end GlobalTheory.RowLatXS
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SaturatedSpanOfGramDetIsUnitIntegralLattice
section
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.Unfold GlobalTheory.LocOver GlobalTheory.GenMass
open scoped Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

namespace GlobalTheory

theorem satur_of_gram_det_unit : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) {ι : Type} [Fintype ι] [DecidableEq ι] (Λ : Submodule M.L.O V) (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.h x y ∈ M.L.O) (m : ι → V) (hm : ∀ i, m i ∈ Λ) (hdet : IsUnitO M (H.gram m).det), ∀ v ∈ Λ, v ∈ Submodule.span E (Set.range m) → v ∈ Submodule.span M.L.O (Set.range m) := by
  intro F _ _ _ E _ _ _ _ M V _ _ H ι _ _ Λ hΛ m hm hdet v hv hvE
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hvE

  have hG : ∀ a b, H.gram m a b ∈ M.L.O := fun a b => hΛ _ (hm b) _ (hm a)
  let G' : Matrix ι ι M.L.O := Matrix.of fun a b => ⟨H.gram m a b, hG a b⟩
  have hmap : M.L.O.subtype.mapMatrix G' = H.gram m := by
    ext a b
    rfl
  have hadj : ∀ a b, (H.gram m).adjugate a b ∈ M.L.O := by
    intro a b
    rw [← hmap, ← RingHom.map_adjugate]
    exact (G'.adjugate a b).2

  have hpair : ∀ a, (Matrix.mulVec (H.gram m) c) a ∈ M.L.O := by
    intro a
    have hsum : H.h (∑ i, c i • m i) (m a) = (Matrix.mulVec (H.gram m) c) a := by
      let φ : V →+ E := AddMonoidHom.mk' (fun x => H.h x (m a)) (fun x x' => H.h_add_left x x' (m a))
      have hφ : H.h (∑ i, c i • m i) (m a) = φ (∑ i, c i • m i) := rfl
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hφ, map_sum]
      simp only [Matrix.mulVec, dotProduct, HermSp.gram, Matrix.of_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      show H.h (c i • m i) (m a) = _
      rw [H.h_smul_left, mul_comm]
    rw [← hsum]
    exact hΛ _ hv _ (hm a)

  have hdc : ∀ i, (H.gram m).det * c i ∈ M.L.O := by
    intro i
    have key : Matrix.mulVec (H.gram m).adjugate (Matrix.mulVec (H.gram m) c) = (H.gram m).det • c := by
      rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec]
    have hi := congrFun key i
    rw [Pi.smul_apply, smul_eq_mul] at hi
    have hmem : ∀ w : ι → E, (∀ j, w j ∈ M.L.O) → (Matrix.mulVec (H.gram m).adjugate w) i ∈ M.L.O := by
      intro w hw
      simp only [Matrix.mulVec, dotProduct]
      exact Subring.sum_mem _ fun j _ => Subring.mul_mem _ (hadj i j) (hw j)
    rw [← hi]
    exact hmem _ hpair

  obtain ⟨_, y, hy, hdy⟩ := hdet
  have hc : ∀ i, c i ∈ M.L.O := by
    intro i
    have hci : c i = y * ((H.gram m).det * c i) := by
      rw [← mul_assoc, mul_comm y, hdy, one_mul]
    rw [hci]
    exact Subring.mul_mem _ hy (hdc i)
  refine Submodule.sum_mem _ fun i _ => ?_
  have hsm : c i • m i = (⟨c i, hc i⟩ : M.L.O) • m i := rfl
  rw [hsm]
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

end GlobalTheory
end

