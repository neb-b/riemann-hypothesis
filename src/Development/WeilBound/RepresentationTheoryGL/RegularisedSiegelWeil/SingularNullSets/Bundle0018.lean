module

public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.WeakApproximationFinitePlace
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JacobiMapsExist
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0268
public import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.SiegelEisenstein.GramMatrixAdjoint
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.Bundle0016

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MatGExt
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

open GlobalTheory.CompanionTheory.JacobiMaps GlobalTheory.StdUnn.Model

namespace PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

variable {D : D7} {n : ℕ}

theorem matG_mul (g h : G D n) : mat (g * h) = mat g * mat h := rfl

theorem matG_ext {g h : G D n} (e : mat g = mat h) : g = h := by
  apply Subtype.ext; apply Units.ext; exact e

theorem matG_inv {g : G D n} {M : Mx D (n + n) (n + n)} (h : mat g * M = 1) : mat g⁻¹ = M := by
  have e : mat g⁻¹ * mat g = 1 := by
    rw [← matG_mul, inv_mul_cancel]; rfl
  calc mat g⁻¹ = mat g⁻¹ * (mat g * M) := by rw [h, Matrix.mul_one]
    _ = M := by rw [← Matrix.mul_assoc, e, Matrix.one_mul]

theorem adjM_mul {a b c : ℕ} (x : Mx D a b) (y : Mx D b c) : adj (x * y) = adj y * adj x := by
  simp only [adj, Matrix.map_mul, Matrix.transpose_mul]

theorem adjM_one {a : ℕ} : adj (1 : Mx D a a) = 1 := by
  simp only [adj, Matrix.map_one _ (map_zero _) (map_one _), Matrix.transpose_one]

end PositivityTheory.Rg.Rsw.L.UnitaryGroupMatrix

namespace PositivityTheory.Rg.Rsw.L


open UnitaryGroupMatrix in
theorem geng : GenG := by
  intro D n A _ h1 hA
  let S : Subgroup (G D n) :=
    { carrier := {g | (∀ x ∈ A, g * x ∈ A) ∧ ∀ x ∈ A, g⁻¹ * x ∈ A}
      mul_mem' := fun {g h} hg hh =>
        ⟨fun x hx => by rw [mul_assoc]; exact hg.1 _ (hh.1 x hx),
         fun x hx => by rw [mul_inv_rev, mul_assoc]; exact hh.2 _ (hg.2 x hx)⟩
      one_mem' := ⟨fun x hx => by rwa [one_mul], fun x hx => by rwa [inv_one, one_mul]⟩
      inv_mem' := fun {g} hg => ⟨hg.2, fun x hx => by rw [inv_inv]; exact hg.1 x hx⟩ }
  have hS : S = ⊤ := by
    refine _root_.GlobalTheory.StdUnn.eq_top_of_levi_unip_weyl D n S ?_ ?_ ?_
    · intro g a hg
      refine ⟨hA g (Or.inr (Or.inl ⟨a, hg⟩)), hA g⁻¹ (Or.inr (Or.inl ⟨a⁻¹, ?_⟩))⟩
      rw [inv_inv]
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp only [mul_zero, zero_mul, add_zero, zero_add]
      rw [← adjM_mul, a.mul_inv, adjM_one, block_matrix_one]
    · intro g b hg
      refine ⟨hA g (Or.inl ⟨b, hg⟩), hA g⁻¹ (Or.inl ⟨-b, ?_⟩)⟩
      apply matG_inv
      rw [hg, submatrix_fromBlocks_mul]
      simp [block_matrix_one]
    · intro g hg
      have e : g⁻¹ = g * (g * g) := by
        apply matG_ext
        rw [matG_inv (M := blk4 0 (-1) 1 0), matG_mul, matG_mul, hg, submatrix_fromBlocks_mul, submatrix_fromBlocks_mul]
        · simp
        · rw [hg, submatrix_fromBlocks_mul]; simp [block_matrix_one]
      have hw := hA g (Or.inr (Or.inr hg))
      refine ⟨hw, fun x hx => ?_⟩
      rw [e, mul_assoc, mul_assoc]
      exact hw _ (hw _ (hw x hx))
  ext g
  simp only [Set.mem_univ, iff_true]
  have hg : g ∈ S := hS ▸ Subgroup.mem_top g
  simpa using hg.1 1 h1

end PositivityTheory.Rg.Rsw.L

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.SingularNullSets.MemOfCoord
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open IsDedekindDomain NumberField

namespace PositivityTheory.Rg.Rsw.L.LApproxId

open GlobalTheory.CompanionTheory.SiegelND.Coef.TestN

theorem memHA (D : D7) (t : ℕ) (X : Mx D t t) : X ∈ hermA D t ↔ X ∈ HermR (AF D.host.F) D.sp.cm.sig t := by
  constructor
  · intro h a c
    have h' : GlobalTheory.MixModel.adj X = X := h
    have := congrFun (congrFun h' a) c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using this
  · intro h
    change GlobalTheory.MixModel.adj X = X
    ext a c
    simpa [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply] using h a c

theorem smul_memA (D : D7) (t : ℕ) (e : AE D) (he : cA D e = e) (X : Mx D t t) (h : X ∈ hermA D t) :
    e • X ∈ hermA D t := by
  have h' : GlobalTheory.MixModel.adj X = X := h
  change GlobalTheory.MixModel.adj (e • X) = e • X
  ext a c
  have := congrFun (congrFun h' a) c
  simp only [GlobalTheory.MixModel.adj, Matrix.transpose_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul,
    map_mul, he] at this ⊢
  rw [this]

theorem pch_eq (D : D7) (t : ℕ) (ψ : AddChar (AF D.host.F) ℂ) (X T : Mx D t t) (hX : X ∈ hermA D t)
    (hT : T ∈ hermA D t) :
    pch ψ X T = ψ (pairHerm (AF D.host.F) D.sp.cm.sig t ⟨X, (memHA D t X).1 hX⟩ ⟨T, (memHA D t T).1 hT⟩) := by
  simp only [pch, halfTr, trA, pairHerm, Matrix.trace, Matrix.diag_apply, Matrix.mul_apply]

theorem coord_fix (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (X : HermR (AF D.host.F) D.sp.cm.sig t) (hX : e • X.1 = X.1) (i : Idx t d) :
    ε * hCo (AF D.host.F) D.sp.cm.sig b X i = hCo (AF D.host.F) D.sp.cm.sig b X i :=
  (hCo_smul _ b ε X X (by rw [← heS, hX]) i).symm

theorem mem_of_coord (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) (y : HermR (AF D.host.F) D.sp.cm.sig t)
    (hw : ∀ i, ε * eA y i = eA y i) : e • y.1 = y.1 := by
  have hyA : y.1 ∈ hermA D t := (memHA D t y.1).2 y.2
  have hY := (memHA D t _).1 (smul_memA D t e hcA y.1 hyA)
  have h1 : eA ⟨e • y.1, hY⟩ = eA y := by
    funext i
    rw [heA, hCo_smul _ b ε y ⟨e • y.1, hY⟩ (by rw [← heS]) i, ← heA, hw]
  exact congrArg Subtype.val (eA.injective h1)


set_option synthInstance.maxHeartbeats 200000 in
theorem exTheta' (D : D7) (t : ℕ) (e : AE D) (ε : AF D.host.F) (heS : e = algebraMap (AF D.host.F) (AE D) ε)
    (hcA : cA D e = e) {d : ℕ} (b : Module.Basis (Fin d) D.host.F D.host.E)
    (eA : HermR (AF D.host.F) D.sp.cm.sig t ≃ₜ+ (Idx t d → AF D.host.F))
    (heA : ∀ X, eA X = hCo (AF D.host.F) D.sp.cm.sig b X) :
    ∃ Θ : hermS D t e ≃ₜ+ (Idx t d → fixE ε),
      ∀ x i, ((Θ x i) : AF D.host.F) = eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := by
  have hfix : ∀ (x : hermS D t e) i, ε * eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i =
      eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i := fun x i => by
    rw [heA]; exact coord_fix D t e ε heS b ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ x.2 i
  have hinv : ∀ v : Idx t d → fixE ε, e • (eA.symm (fun i => (v i).1)).1 = (eA.symm (fun i => (v i).1)).1 :=
    fun v => mem_of_coord D t e ε heS hcA b eA heA _ (fun i => by rw [eA.apply_symm_apply]; exact (v i).2)
  refine ⟨{ toFun := fun x i => ⟨eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ i, hfix x i⟩
            invFun := fun v => ⟨⟨(eA.symm (fun i => (v i).1)).1, (memHA D t _).2 (eA.symm _).2⟩, hinv v⟩
            left_inv := fun x => by
              apply Subtype.ext; apply Subtype.ext
              simp
            right_inv := fun v => by
              funext i
              apply Subtype.ext
              simp
            map_add' := fun x y => by
              funext i
              apply Subtype.ext
              change eA _ i = eA _ i + eA _ i
              exact congrFun (map_add eA ⟨x.1.1, (memHA D t x.1.1).1 x.1.2⟩ ⟨y.1.1, (memHA D t y.1.1).1 y.1.2⟩) i
            continuous_toFun := continuous_pi fun i => Continuous.subtype_mk ((continuous_apply i).comp
              (eA.continuous.comp ((continuous_subtype_val.comp continuous_subtype_val).subtype_mk _))) _
            continuous_invFun := ((continuous_subtype_val.comp (eA.symm.continuous.comp
              (continuous_pi fun i => continuous_subtype_val.comp (continuous_apply i)))).subtype_mk _).subtype_mk _ },
    fun x i => rfl⟩

theorem e_eq (D : D7) (S : Finset (Pl D)) (e : AE D) (he : IsIdem S e) :
    e = algebraMap (AF D.host.F) (AE D) ((1, LIdemEx.indS S) : AF D.host.F) := by
  have h : e = LIdemEx.eS S := LIdemEx.ae_ext _ _ (fun w => by rw [he.1 w, (LIdemEx.isIdem_eS S).1 w])
    (fun v => by rw [he.2 v, (LIdemEx.isIdem_eS S).2 v])
  exact h.trans rfl

end PositivityTheory.Rg.Rsw.L.LApproxId

end
end

