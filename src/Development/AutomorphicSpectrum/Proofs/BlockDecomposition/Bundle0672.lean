module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.HermitianCellMeasures.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0206
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
public import Formalism.LocalToGlobal.BesselHermitianTheta.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1567
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0657
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHolds
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0632
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0424
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0644
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0528
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0669
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0498
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0656
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0597
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0665
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0660
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0664
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0658
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0661
public import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.CoefDataExists
public import Development.WeilBound.CoreStatements.PublishedTheorems.SiegelWeilSchrodinger.SiegelWeilUnitarySchrodingerLit
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0261
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0262
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0018
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0496
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0482
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianMeasureEulerProduct

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.BlockMatrixApplyInrInr
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EmbK

open GlobalTheory.CompanionTheory.JacobiMaps

section Entries

variable {R : Type} [CommRing R] {n r t : ℕ}

theorem block_matrix_apply_inl_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inl j)) = a i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]

theorem block_matrix_apply_inl_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inl i)) (finSumFinEquiv (Sum.inr j)) = b i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]

theorem block_matrix_apply_inr_inl (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inl j)) = c i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]

theorem block_matrix_apply_inr_inr (a b c d : Matrix (Fin n) (Fin n) R) (i j : Fin n) :
    blk4 a b c d (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j)) = d i j := by
  simp only [blk4, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

theorem entry (hn : r + t = n) (a b c d : Matrix (Fin t) (Fin t) R) (i j : Fin (n + n)) :
    blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j ∨
    ∃ i' j', blk4 (bl hn 1 0 0 a) (bl hn 0 0 0 b) (bl hn 0 0 0 c) (bl hn 1 0 0 d) i j = blk4 a b c d i' j' ∧
      (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) i' j' = (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) i j := by
  have h1 : (1 : Matrix (Fin (n + n)) (Fin (n + n)) R) =
      blk4 (bl hn 1 0 0 1) (bl hn 0 0 0 0) (bl hn 0 0 0 0) (bl hn 1 0 0 1) := by
    have z : bl hn (0 : Matrix (Fin r) (Fin r) R) 0 0 (0 : Matrix (Fin t) (Fin t) R) = 0 := blockMatrix_zero hn
    rw [blockRowSubstitution_one, z, GlobalTheory.StdUnn.Model.block_matrix_one]
  have h2 : (1 : Matrix (Fin (t + t)) (Fin (t + t)) R) = blk4 1 0 0 1 := GlobalTheory.StdUnn.Model.block_matrix_one.symm
  rw [h1, h2]
  have bll : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = a i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]
  have blr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = b i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₂]
  have brl : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j)) = c i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₁]
  have brr : ∀ (a : Matrix (Fin r) (Fin r) R) b c (d : Matrix (Fin t) (Fin t) R) i j,
      bl hn a b c d ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr i)) ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j)) = d i j := by
    intro a b c d i j; simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]
  obtain ⟨i, rfl⟩ := finSumFinEquiv.surjective i
  obtain ⟨j, rfl⟩ := finSumFinEquiv.surjective j
  rcases i with i | i <;> rcases j with j | j <;>
    obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i <;>
    obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j <;>
    rcases i with i | i <;> rcases j with j | j <;>
    simp only [block_matrix_apply_inl_inl, block_matrix_apply_inl_inr, block_matrix_apply_inr_inl, block_matrix_apply_inr_inr, bll, blr, brl, brr, true_or] <;>
    first
    | exact Or.inl rfl
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inl a b c d i j).symm, block_matrix_apply_inl_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inl_inr a b c d i j).symm, block_matrix_apply_inl_inr _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inl a b c d i j).symm, block_matrix_apply_inr_inl _ _ _ _ i j⟩
    | exact Or.inr ⟨_, _, (block_matrix_apply_inr_inr a b c d i j).symm, block_matrix_apply_inr_inr _ _ _ _ i j⟩

theorem map_one_apply {T : Type} [CommRing T] {N : ℕ} (f : R →+* T) (i j : Fin N) :
    f ((1 : Matrix (Fin N) (Fin N) R) i j) = (1 : Matrix (Fin N) (Fin N) T) i j := by
  by_cases h : i = j
  · subst h; simp
  · simp [Matrix.one_apply_ne h]

end Entries

variable {D : D7} {n r t : ℕ} {hn : r + t = n}

theorem emb_entries_one (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) T) i j) (i j : Fin (n + n)) :
    f (mat (M.emb u) i j) = (1 : Matrix (Fin (n + n)) (Fin (n + n)) T) i j := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, h'⟩
  · rw [h, map_one_apply]
  · rw [h, block_matrix_of_blocks, hu i' j', ← map_one_apply f i' j', h', map_one_apply]

theorem emb_entries_mem (M : Maps D hn) {T : Type} [CommRing T] (f : AE D →+* T) (P : Subring T) {u : G D t}
    (hu : ∀ i j, f (mat u i j) ∈ P) (i j : Fin (n + n)) : f (mat (M.emb u) i j) ∈ P := by
  rw [M.emb_mat u _ _ _ _ (block_matrix_of_blocks (mat u)).symm]
  rcases entry hn (b11 (mat u)) (b12 (mat u)) (b21 (mat u)) (b22 (mat u)) i j with h | ⟨i', j', h, -⟩
  · rw [h, map_one_apply]
    by_cases e : i = j
    · subst e; simpa using P.one_mem
    · simpa [Matrix.one_apply_ne e] using P.zero_mem
  · rw [h, block_matrix_of_blocks]
    exact hu i' j'

theorem stab_entries {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    {v : HeightOneSpectrum (𝓞 F)} {m : GL (Fin N) (Fv F v ⊗[F] E)}
    (h : m ∈ Formalism.UG.stabGL (latLoc F (stdLattice E N) v)) (i j : Fin N) :
    m.1 i j ∈ intLoc F E v ∧ (m⁻¹).1 i j ∈ intLoc F E v := by
  have hs : (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v := by
    refine mem_latLoc_stdLattice.2 fun k => ?_
    by_cases e : k = j
    · subst e; simpa using (intLoc F E v).one_mem
    · simpa [Pi.single_eq_of_ne e] using (intLoc F E v).zero_mem
  constructor
  · have h1 := mem_latLoc_stdLattice.1 ((h _).1 hs) i
    simpa using h1
  · have e : m.1 *ᵥ ((m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E)) = Pi.single j 1 := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have h2 : (m⁻¹).1 *ᵥ (Pi.single j 1 : Fin N → Fv F v ⊗[F] E) ∈ latLoc F (stdLattice E N) v :=
      (h _).2 (by rw [e]; exact hs)
    have h1 := mem_latLoc_stdLattice.1 h2 i
    simpa using h1

theorem emb_mem_KOff : ∀ {D : D7} {n r t : ℕ} {hn : r + t = n} (M : Maps D hn) (S : Finset (Pl D)) (u : G D t),
    u ∈ KOff D t S → M.emb u ∈ KOff D n S := by
  intro D n r t hn M S u hu
  obtain ⟨hf, h1, h2⟩ := mem_levelOff.1 hu
  refine mem_levelOff.2 ⟨mem_finPts_iff_forall.2 fun w => ?_, fun v hv => ?_, fun v hv => ?_⟩
  · have hw := mem_finPts_iff_forall.1 hf w
    have ent : ∀ i j, compInf D.host.F D.host.E w (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) hw
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_projArch, map_one]
    exact emb_entries_one M _ ent i j
  · have ent : ∀ i j, cv D v (mat u i j) = (1 : Matrix (Fin (t + t)) (Fin (t + t)) _) i j := fun i j => by
      have e := congrArg (fun g => (matHom _ D.sp.cm.sig (Jst D t) g).1 i j) (h1 v hv)
      simp only [map_one, Units.val_one] at e
      exact e
    apply matHom_injective
    apply Units.ext
    ext i j
    rw [matHom_proj, map_one]
    exact emb_entries_one M _ ent i j
  · have key : ∀ x : G D t, proj D.sp.cm.sig (Jst D t) v x ∈ stabLoc D.sp.cm.sig (Jst D t) (stdLattice D.host.E (t + t)) v →
        ∀ i j, (matHom _ D.sp.cm.sig (Jst D n) (proj D.sp.cm.sig (Jst D n) v (M.emb x))).1 i j ∈ intLoc D.host.F D.host.E v := by
      intro x hx i j
      exact emb_entries_mem M (cv D v) _ (fun i j => (stab_entries hx i j).1) i j
    refine GlobalTheory.StdUnn.StabFin.mem_stab_std (key u (h2 v hv)) fun i j => ?_
    rw [← map_inv, ← map_inv, ← map_inv]
    exact key u⁻¹ (by rw [map_inv]; exact inv_mem (h2 v hv)) i j

end GlobalTheory.CompanionTheory.EmbK
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CentreCharacterCommutator
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJE

theorem adj_herm {D : D7} {ρ : ℕ} (b₀ : HermE D ρ) :
    adj (b₀.1.map (incA D) : Mx D ρ ρ) = b₀.1.map (incA D) := by
  have h := rat_conjTranspose b₀.1
  have e : b₀.1ᴴ = b₀.1 := b₀.2
  rw [e] at h
  exact h.symm

theorem chz_jc {D : D7} {ρ p : ℕ} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D ρ) (y x : Mx D ρ p) :
    chz ψ b₀ (GlobalTheory.CompanionTheory.FJE.jc y x) = GlobalTheory.CompanionTheory.FJE.chv ψ b₀ x y := by
  set B : Mx D ρ ρ := b₀.1.map (incA D) with hB
  have hadj : adj B = B := adj_herm b₀
  have e1 : Matrix.trace (B * (y * adj x)) = Matrix.trace (pr b₀ x y) := by
    show _ = Matrix.trace (adj x * (B * y))
    rw [← Matrix.mul_assoc, Matrix.trace_mul_comm]
  have e2 : Matrix.trace (B * (x * adj y)) = cA D (Matrix.trace (pr b₀ x y)) := by
    rw [← GlobalTheory.CompanionTheory.FourierN.trace_adj]
    have h : adj (pr b₀ x y) = HMul.hMul (HMul.hMul (adj y) B : Mx D p ρ) x := by
      show adj (HMul.hMul (adj x) (HMul.hMul B y : Mx D ρ p) : Mx D p p) = _
      rw [adj_mul, adj_mul, adj_adj, hadj]
    rw [h, Matrix.trace_mul_comm, Matrix.mul_assoc x, Matrix.trace_mul_comm]
  have e3 : Matrix.trace (HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 : Mx D ρ ρ) =
      Matrix.trace (pr b₀ x y) + cA D (Matrix.trace (pr b₀ x y)) := by
    show Matrix.trace (B * (y * adj x + x * adj y)) = _
    rw [Matrix.mul_add, Matrix.trace_add, e1, e2]
  rw [chz, show HMul.hMul (b₀.1.map (incA D)) (GlobalTheory.CompanionTheory.FJE.jc y x).1 = HMul.hMul B (GlobalTheory.CompanionTheory.FJE.jc y x).1 from rfl, e3,
    GlobalTheory.CompanionTheory.FourierN.halfTr_add_cA]
  rfl

end GlobalTheory.CompanionTheory.FJE
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ContinuousCutc
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw PositivityTheory.Rg.Rsw.L PositivityTheory.Rg.Rsw.Em

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace GlobalTheory.CompanionTheory.EisE

variable {D : D7} {n r t a b : ℕ}

theorem jn_smul (hn : r + t = n) (e : AE D) (x : Mx D a r) (v : Mx D a t) :
    e • jn hn x v = jn hn (e • x) (e • v) := by
  ext i j
  simp only [jn, Matrix.smul_apply, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j <;> rfl

theorem intOff_jn (hn : r + t = n) {S : Finset (Pl D)} (x : Mx D a r) (v : Mx D a t) :
    IntOff S (jn hn x v) ↔ IntOff S x ∧ IntOff S v := by
  constructor
  · intro h
    refine ⟨fun w hw i j => ?_, fun w hw i j => ?_⟩
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inl j))
      simpa [jn] using this
    · have := h w hw i ((finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))
      simpa [jn] using this
  · rintro ⟨h1, h2⟩ w hw i j
    simp only [jn, Matrix.submatrix_apply, id]
    rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
    · exact h1 w hw i j
    · exact h2 w hw i j

theorem continuous_jn (hn : r + t = n) : Continuous (fun z : Mx D a r × Mx D a t => jn hn z.1 z.2) := by
  refine continuous_matrix fun i j => ?_
  simp only [jn, Matrix.submatrix_apply, id]
  rcases (finSumFinEquiv.trans (finCongr hn)).symm j with j | j
  · exact continuous_fst.matrix_elem i j
  · exact continuous_snd.matrix_elem i j

def cutc (hn : r + t = n) (X : Mx D a n) : Mx D a r × Mx D a t :=
  (X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inl j),
    X.submatrix id fun j => (finSumFinEquiv.trans (finCongr hn)) (Sum.inr j))

theorem continuous_cutc (hn : r + t = n) : Continuous (cutc (D := D) (a := a) hn) := by
  refine Continuous.prodMk ?_ ?_ <;> exact continuous_matrix fun i j => continuous_id.matrix_elem _ _

theorem cutc_jn (hn : r + t = n) (x : Mx D a r) (v : Mx D a t) : cutc hn (jn hn x v) = (x, v) := by
  refine Prod.ext ?_ ?_ <;> ext i j <;> simp [cutc, jn]

theorem intOff_smul {S : Finset (Pl D)} {e : AE D} (hS : IsIdem S e) (x : Mx D a b) : IntOff S (e • x) := by
  intro v hv i j
  have h0 : cv D v e = 0 := by rw [hS.2 v, ite_eq_right hv]
  simp only [Matrix.smul_apply, smul_eq_mul, map_mul, h0, zero_mul]
  exact zero_mem _

theorem adj_smul {e : AE D} (hc : cA D e = e) (x : Mx D a b) : adj (e • x) = e • adj x := by
  ext i j
  simp [adj, hc]

theorem ip_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (x : Mx D V.rank a) (y : Mx D V.rank b) :
    ip V (e • x) (e • y) = e • ip V x y := by
  simp only [ip, mm, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem yv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : yv V b₀ (e • z.1, e • z.2) = e • yv V b₀ z := by
  simp only [yv, ip_smul he hc, mm, Matrix.mul_smul]

theorem pr_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (b₀ : HermE D r) (x y : Mx D r t) :
    pr b₀ (e • x) (e • y) = e • pr b₀ x y := by
  simp only [pr, adj_smul hc, Matrix.smul_mul, Matrix.mul_smul, smul_smul, he]

theorem qv_smul {e : AE D} (he : e * e = e) (hc : cA D e = e) (V : HSp D) (b₀ : HermE D r)
    (z : Mx D V.rank r × Mx D V.rank t) : qv V b₀ (e • z.1, e • z.2) = e • qv V b₀ z := by
  simp only [qv, ip_smul he hc, yv_smul he hc, pr_smul he hc, smul_sub]

theorem pch_smul {ψ : AddChar (AF D.host.F) ℂ} {e : AE D} {x : Mx D t t} (hx : e • x = x) (T : Mx D t t) :
    pch ψ x (e • T) = pch ψ x T := by
  have : mm x (e • T) = mm x T := by
    conv_rhs => rw [← hx]
    simp only [mm, Matrix.smul_mul, Matrix.mul_smul]
  simp only [pch, this]

theorem isOrb_smul {V : HSp D} {b₀ : HermE D r} {e : AE D} {ν : Measure (Mx D V.rank r × Mx D V.rank t)}
    (h : IsOrb V b₀ e ν) (c : ℝ≥0) : IsOrb V b₀ e (c • ν) := by
  have := h.fin
  have : SecondCountableTopologyEither (Mx D V.rank r) (Mx D V.rank t) :=
    ⟨Or.inl (lattice_Mx D V.rank r).2.2.1⟩
  have : BorelSpace (Mx D V.rank r) := ⟨rfl⟩
  have : BorelSpace (Mx D V.rank t) := ⟨rfl⟩
  have : BorelSpace (Mx D V.rank r × Mx D V.rank t) := Prod.borelSpace
  have : OpensMeasurableSpace (Mx D V.rank r × Mx D V.rank t) := BorelSpace.opensMeasurable
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · rw [smul_apply, h.supp, smul_zero]
  · intro g hg
    rw [Measure.map_smul, h.invU g hg]
    apply Continuous.aemeasurable
    exact (continuous_const.matrix_mul continuous_fst).prodMk
      (continuous_const.matrix_mul continuous_snd)
  · intro y hy
    rw [Measure.map_smul, h.invS y hy]
    apply Continuous.aemeasurable
    exact continuous_fst.prodMk (continuous_snd.add (continuous_fst.matrix_mul continuous_const))
  · intro g hg
    rw [Measure.map_smul, h.cov g hg, smul_comm]
    apply Continuous.aemeasurable
    exact continuous_fst.prodMk (continuous_snd.matrix_mul continuous_const)

theorem isOrb_zero {V : HSp D} {b₀ : HermE D r} {e : AE D} : IsOrb (t := t) V b₀ e 0 := by
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩ <;> simp

end GlobalTheory.CompanionTheory.EisE

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FibreMeasureExtensionSymmetricStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ GlobalTheory.CompanionTheory.SW.StageF GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WeilSiegel.Free NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fibre_measure_extension_symmetric : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F) (n : ℕ) (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R] (d : ℕ) (b : Module.Basis (Fin d) F E) (lam : Measure R) (m₁ : HermR R σ 1 → Measure (Fin 1 → Fin (M + 1) → R ⊗[F] E)) (m' : HermR R σ n → Measure (Fin n → Fin M → R ⊗[F] E)) (s : (Fin 1 → Fin (M + 1) → R ⊗[F] E) → HA R σ (blockOne (algebraMap F E t) J)) (B₀ : Set R) (a : R → Rˣ) (κ₁ cm : Rˣ → ℝ≥0), HermitianMeasureData σ J t n b lam m₁ m' s B₀ a κ₁ cm → ∀ φ : (Fin (n + 1) → Fin (M + 1) → R ⊗[F] E) → ℝ≥0∞, Measurable φ → Measurable (fun z : R × (Fin n → R ⊗[F] E) × HermR R σ n => Pint σ J t m₁ m' s φ z.1 z.2.1 z.2.2) := by
  first | exact @GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | exact GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF | (intros; apply GlobalTheory.CompanionTheory.SW.StageF.measurable_PintF <;> assumption)
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierZeroHoldsStatement
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fourier_zero_holds : PositivityTheory.PfSWUS.FourierZero := by
  first | exact @GlobalTheory.CompanionTheory.FourierN.fourierZero | exact GlobalTheory.CompanionTheory.FourierN.fourierZero | (intros; apply GlobalTheory.CompanionTheory.FourierN.fourierZero <;> assumption)
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HermitianEulerProductStandard
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.SiegelND
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.CompanionTheory.WeilSiegel.Frame GlobalTheory.CompanionTheory.WhitFree
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg

theorem isHermND_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsHermND σ (1 : Matrix (Fin M) (Fin M) E) := by
  refine ⟨fun i j => ?_, by simp⟩
  by_cases h : i = j
  · subst h
    simp
  · simp [Matrix.one_apply, h, Ne.symm h]

theorem exists_test_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ n : ℕ, 0 < n → ∀ ψ : AddChar (AF F) ℂ, IsCharAF F ψ → ∀ db : Measure (HermR (AF F) σ n), SdHerm F E σ (AF F) ψ n db → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (laminf : Measure (Ainf F)) (lam : ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Measure (Fv F v)), GlobalTheory.CompanionTheory.SW.IsStdInf laminf → (∀ v, GlobalTheory.CompanionTheory.SW.IsStdV v (lam v)) → ∃ S₁ : Finset (IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F)), ∀ S, S₁ ⊆ S → ∃ (ρ : ℕ → HermR (Ainf F) σ n → ℝ) (U : ℕ → ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers F), Set (HermR (Fv F v) σ n)), (∀ k, Continuous (ρ k) ∧ HasCompactSupport (ρ k) ∧ (∀ y, 0 ≤ ρ k y) ∧ 0 < ∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n)) ∧ Filter.Tendsto (fun k => tsupport (ρ k)) Filter.atTop (nhds (0 : HermR (Ainf F) σ n)).smallSets ∧ (∀ k v, IsCompact (U k v) ∧ IsOpen (U k v) ∧ (0 : HermR (Fv F v) σ n) ∈ U k v) ∧ (∀ v, Filter.Tendsto (fun k => U k v) Filter.atTop (nhds (0 : HermR (Fv F v) σ n)).smallSets) ∧ (∀ k v, 0 < (GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal) ∧ (∀ k, Integrable (GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k))) db ∧ ∀ z, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y * ψ (pairHerm (AF F) σ n y z) ∂db = GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) (-z)) ∧ (∀ k, ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db = ((∫ y, ρ k y ∂(GlobalTheory.CompanionTheory.SW.coordHerm (Ainf F) σ b laminf n) : ℝ) : ℂ) * ∏ v ∈ S, ((GlobalTheory.CompanionTheory.SW.coordHerm (Fv F v) σ b (lam v) n (U k v)).toReal : ℂ)) ∧ (∀ k y, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y‖ ≤ ‖∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db‖) ∧ ∀ y, Filter.Tendsto (fun k => GlobalTheory.CompanionTheory.SiegelND.Coef.fouH σ ψ db (GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k)) y / ∫ y, GlobalTheory.CompanionTheory.SiegelND.Coef.testH σ b (ρ k) S (U k) y ∂db) Filter.atTop (nhds ((GlobalTheory.CompanionTheory.SiegelND.Coef.intH σ b n S).indicator (fun _ => (1 : ℂ)) (GlobalTheory.CompanionTheory.SiegelND.Coef.hermFin σ y))) := by
  intro F E _ _ _ _ _ σ hCM n hn ψ hψ db hdb d b laminf lam hinf hlam
  obtain ⟨S₁, h⟩ := GlobalTheory.CompanionTheory.SiegelND.Coef.TestN.exists_testH_approx F E σ hCM (2 * n + 1) 1 (isHermND_one σ _) n
    (by omega) ψ hψ db hdb d b laminf lam hinf hlam
  refine ⟨S₁, fun S hS => ?_⟩
  obtain ⟨ρ, U, a1, a2, a3, a4, a5, a6, a7, a8⟩ := h S hS
  exact ⟨ρ, U, a1, a2, fun k v => ⟨(a3 k v).1, (a3 k v).2.1, (a3 k v).2.2.1⟩, a4, fun k v => (a3 k v).2.2.2, a5, a6, a7, a8⟩

end GlobalTheory.CompanionTheory.SiegelND.Coef.TestDeg
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegrableOfSummableFundamentalDomain
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.HermFD

theorem integrable_of_cover {A : Type*} [AddGroup A] [TopologicalSpace A] [MeasurableSpace A] [BorelSpace A]
    [SecondCountableTopology A] [MeasurableAdd A] [ContinuousAdd A] (L : AddSubgroup A) [Countable L]
    (μ : Measure A) [μ.IsAddLeftInvariant] (𝓖 : Set A) (hFD : IsAddFundamentalDomain L 𝓖 μ) (h1 : μ 𝓖 = 1)
    (f : A → ℝ) (hf : Continuous f) (hf0 : ∀ z, 0 ≤ f z) (hS : Summable (fun ζ : L => f ζ.1))
    (K : Set A) (hK : ∀ x, ∃ γ ∈ L, γ + x ∈ K) (κ : ℝ) (hκ : 0 ≤ κ)
    (hb : ∀ ζ ∈ L, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) : Integrable f μ := by
  have hpt : ∀ z : A, ∑' ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    intro z
    obtain ⟨γ, hγ, hz⟩ := hK z
    have h2 : ∀ ζ : L, ENNReal.ofReal (f (ζ.1 + z)) ≤
        ENNReal.ofReal (κ * f ((Equiv.subRight (⟨γ, hγ⟩ : L) ζ).1)) := by
      intro ζ
      apply ENNReal.ofReal_le_ofReal
      have e : ζ.1 + z = (ζ.1 - γ) + (γ + z) := by simp [sub_eq_add_neg, add_assoc]
      rw [e]
      exact hb _ (L.sub_mem ζ.2 hγ) _ hz
    refine (ENNReal.tsum_le_tsum h2).trans ?_
    rw [(Equiv.subRight (⟨γ, hγ⟩ : L)).tsum_eq (fun ζ : L => ENNReal.ofReal (κ * f ζ.1)),
      ← tsum_mul_left, ENNReal.ofReal_tsum_of_nonneg (fun ζ => mul_nonneg hκ (hf0 _)) (hS.mul_left κ)]
  have hm : ∀ g : L, AEMeasurable (fun x : A => ENNReal.ofReal (f (g +ᵥ x))) (μ.restrict 𝓖) := fun g =>
    (ENNReal.measurable_ofReal.comp (hf.comp (continuous_const.add continuous_id)).measurable).aemeasurable
  have hI : ∫⁻ x, ENNReal.ofReal (f x) ∂μ ≤ ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) := by
    rw [hFD.lintegral_eq_tsum'', ← lintegral_tsum hm]
    calc _ ≤ ∫⁻ _ in 𝓖, ENNReal.ofReal (κ * ∑' ζ : L, f ζ.1) ∂μ :=
          lintegral_mono fun x => hpt x
      _ = _ := by simp [h1]
  exact ⟨hf.aestronglyMeasurable, (hasFiniteIntegral_iff_ofReal (.of_forall hf0)).2 (hI.trans_lt ENNReal.ofReal_lt_top)⟩


set_option synthInstance.maxHeartbeats 400000 in
theorem integrable_of_periodisation_bound : ∀ (D : D7) (ρ : ℕ) (lz : Measure (hermA D ρ)) (𝓖 : Set (hermA D ρ)), IsCovolOneH lz 𝓖 →
  ∀ f : hermA D ρ → ℝ, Continuous f → (∀ z, 0 ≤ f z) → Summable (fun ζ : ratHerm D ρ => f ζ.1) →
  ∀ K : Set (hermA D ρ), (∀ x, ∃ γ ∈ ratHerm D ρ, γ + x ∈ K) → ∀ κ : ℝ, 0 ≤ κ →
    (∀ ζ ∈ ratHerm D ρ, ∀ z ∈ K, f (ζ + z) ≤ κ * f ζ) → Integrable f lz := by
  intro D ρ lz 𝓖 hC f hf hf0 hS K hK κ hκ hb
  obtain ⟨hlam, hFD, h1⟩ := hC
  obtain ⟨i1, i2, i3, i4, -, -⟩ := GlobalTheory.TowerResNonzero.lattice_ratMx D ρ ρ
  haveI : BorelSpace (Mx D ρ ρ) := ⟨rfl⟩
  haveI : BorelSpace (hermA D ρ) := Subtype.borelSpace _
  haveI : SecondCountableTopology (hermA D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
  haveI : ContinuousAdd (hermA D ρ) := ⟨Continuous.subtype_mk ((continuous_subtype_val.comp continuous_fst).add
    (continuous_subtype_val.comp continuous_snd)) _⟩
  haveI : MeasurableAdd (hermA D ρ) := ContinuousAdd.measurableAdd
  haveI : DiscreteTopology (ratHerm D ρ) := GlobalTheory.CompanionTheory.FourierN.discrete_ratHerm
  haveI : Countable (ratHerm D ρ) := by
    haveI : SecondCountableTopology (ratHerm D ρ) := TopologicalSpace.Subtype.secondCountableTopology _
    exact (TopologicalSpace.separableSpace_iff_countable).1 inferInstance
  exact integrable_of_cover (ratHerm D ρ) lz 𝓖 hFD h1 f hf hf0 hS K hK κ hκ hb

end GlobalTheory.CompanionTheory.HermFD
end
end

