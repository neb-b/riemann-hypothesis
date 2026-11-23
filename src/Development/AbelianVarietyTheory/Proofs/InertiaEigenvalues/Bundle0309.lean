module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0012
public import Formalism.LocalToGlobal.GaloisLevelStructure.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0286
public import GroundTheory.LocalFields.Bundle0003
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowMulMemLatIff
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0255
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIntegersTensorEqLetterwiseProductAinf
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExistsOfLayers
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0222
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0060

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OrthKerEqRangeAdjoint
section
open Formalism.BasicNotions Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef NumberField IsDedekindDomain GlobalTheory.EtaJoin

noncomputable section

namespace GlobalTheory.EtaJoin.TypeSum

theorem orth_ker_eq_range_adjoint {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    [FiniteDimensional ℂ V] [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
    (A : V →ₗ[ℂ] W) : (LinearMap.ker A)ᗮ = LinearMap.range (LinearMap.adjoint A) := by
  have h : (LinearMap.range (LinearMap.adjoint A))ᗮ = LinearMap.ker A := by
    ext x
    simp only [Submodule.mem_orthogonal, LinearMap.mem_range, LinearMap.mem_ker, forall_exists_index,
      forall_apply_eq_imp_iff, LinearMap.adjoint_inner_left]
    constructor
    · intro hx
      exact ext_inner_left ℂ (fun y => by rw [hx y, inner_zero_right])
    · intro hx y
      rw [hx, inner_zero_right]
  rw [← h, Submodule.orthogonal_orthogonal]

variable {D : D7}

def eqvMt {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    D.what₂.Mt μ' j' ≃ₗ[ℂ] D.what₂.Mt μ j := by
  subst hμ; subst hj; exact LinearEquiv.refl ℂ _

theorem map_eqvMt_self {μ : D.what₂.Tup} {j : ℕ} (hμ : μ = μ) (hj : j = j) (V : Submodule ℂ (D.what₂.Mt μ j)) :
    V.map (eqvMt hμ hj).toLinearMap = V :=
  Submodule.map_id V

theorem map_eqvMt_thetaT_isot {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) (σ : D.what₂.FT) :
    ((D.what₂.isot j' σ).map (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      (D.what₂.isot j σ).map (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem map_eqvMt_range_thetaT {μ μ' : D.what₂.Tup} {j j' : ℕ} (hμ : μ' = μ) (hj : j' = j) :
    (LinearMap.range (D.what₂.thetaT μ' j')).map (eqvMt hμ hj).toLinearMap =
      LinearMap.range (D.what₂.thetaT μ j) := by
  subst hμ; subst hj; exact map_eqvMt_self _ _ _

theorem isoTyp_eq_of_isoRep {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} {W : Type}
    [AddCommGroup W] [Module ℂ W] (ρ : Representation ℂ (GQ L n) W) {S S' : Submodule ℂ (GAf L n → W)}
    (hS : ∀ h, ∀ f ∈ S, NG.rt L n h f ∈ S) (h : NG.IsoRep S S') : NG.isoTyp ρ S = NG.isoTyp ρ S' := by
  unfold NG.isoTyp
  congr 1
  ext T
  exact ⟨fun ⟨h1, h2⟩ => ⟨h1, (h.symm hS).trans h2⟩, fun ⟨h1, h2⟩ => ⟨h1, h.trans h2⟩⟩

variable {M : MtFam D}

theorem typeV_of_transport (A : AVTied D M) (i : D.nd.Loc) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (S' : Submodule ℂ (GAf D.host.E D.R.nV → (M μ' j' h1 h2).wt.W))
    (hirr : NG.IsIrrRep (M μ' j' h1 h2).wt.ρ S')
    (hne : (NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real ≠ ⊥) :
    ∃ P, ((NG.isoTyp (M μ' j' h1 h2).wt.ρ S').comap (M μ' j' h1 h2).real).map (eqvMt hμ hj).toLinearMap =
      D.naut.typeV i P := by
  subst hμ; subst hj
  obtain ⟨P, hP⟩ := A.surj i S' hirr hne
  refine ⟨P, ?_⟩
  have e := isoTyp_eq_of_isoRep (M.loc i).wt.ρ (A.irr i P).1.stable hP
  rw [map_eqvMt_self, A.typeV i P, e]
  rfl

theorem eig_of_transport (A : AVTied D M) (i : D.nd.Loc) (P : D.naut.AV i) (x : D.nd.X i)
    (hx : D.naut.ptV i P = some x) {μ' : D.what₂.Tup} {j' : ℕ}
    (hμ : μ' = D.nd.mu i) (hj : j' = D.nd.j i) (h1 : 1 ≤ j') (h2 : j' ≤ D.R.m)
    (V : Submodule ℂ (D.what₂.Mt μ' j')) (hV : V.map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P)
    (w : PlE D.host) (k : ℕ) (s : SplitPlace D.host.E) (ϖ : s.v.adicCompletion (maximalRealSubfield D.host.E))
    (hw : SplitOut D.nd i w) (hc : IsConjPl D.host w s.w) (hu : IsUnif D.host.E s.v ϖ) (k1 : 1 ≤ k)
    (k2 : k ≤ D.R.nV) (c : ℂ)
    (hV' : ∀ y ∈ V, NG.tN (M μ' j' h1 h2).J s ϖ k ((M μ' j' h1 h2).real y) = c • (M μ' j' h1 h2).real y) :
    c = iotaOC D i ((D.nd.hT i w k : D.nd.X i → D.nd.O i) x) := by
  subst hμ; subst hj
  rw [map_eqvMt_self] at hV
  subst hV
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (D.naut.typeV_ne i P)
  have e1 := A.eigen i P x hx w k s ϖ hw hc hu k1 k2 y hy
  have e2 := hV' y hy
  have hr : (M.loc i).real y ≠ 0 := fun h => hy0 ((M.loc i).real_inj (h.trans (map_zero _).symm))
  exact smul_left_injective ℂ hr (e2.symm.trans e1)

end GlobalTheory.EtaJoin.TypeSum

namespace GlobalTheory.EtaJoin.TypeSum

theorem main : ∀ (D : D7) (M : MtFam D) (i : D.nd.Loc), HeckeTied D M → AVTied D M → SplitUnif D → TypeOrth D i →
    ThetaCut D (D.nd.mu i) (D.nd.j i) → Rows.IsotInternal D.what₂ → Formalism.MainNotions.SumRepresentations.ConclusionZ D →
    (∀ σ, D.what₂.isot (D.nd.j i) σ ≠ ⊥ → D.nd.goodRow σ ∧ ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i),
      Formalism.MainNotions.N.HG D.nd D.naut i' ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' σ) → ZSpec D i := by
  intro D M i HT A SU TO TC II PZ EX
  have hZ0 : Idx.Z0 D (D.nd.mu i) (D.nd.j i) = LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    unfold Idx.Z0
    rw [orth_ker_eq_range_adjoint]
    exact inf_eq_left.2 TC
  have hmu : ∀ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), D.nd.mu i' = D.nd.mu i := fun i' hi' => by
    rw [D.nd.mu_w, D.nd.mu_w, ((D.nd.locs_mem _ _ i').1 hi').2]
  let G : Set (D.naut.AV i) := {P | ∃ i' ∈ D.nd.locs (D.nd.j i) (D.nd.w i), ∃ x' ∈ Formalism.MainNotions.N.ZgoodN D.nd D.naut i',
    ∃ P' : D.naut.AV i', D.naut.ptV i' P' = some x' ∧ ∃ (hμ : D.nd.mu i' = D.nd.mu i) (hj : D.nd.j i' = D.nd.j i),
      (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P}

  have hin : ∀ P ∈ G, D.naut.typeV i P ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) := by
    rintro P ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    have hZ := (PZ i' ⟨x', hx'⟩).2.1
    have h1 : D.naut.typeV i' P' ≤ LinearMap.range (D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) := by
      refine le_trans ?_ (LinearMap.map_le_range (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i'))
        (p := Formalism.MainNotions.N.goodPartM D.nd D.naut i'))
      rw [hZ]
      refine le_trans ?_ (le_biSup (fun x => Formalism.MainNotions.N.eigC D.nd D.naut i' x) hx')
      unfold Formalism.MainNotions.N.eigC
      exact le_biSup (fun Q => D.naut.typeV i' Q) (show P' ∈ {Q | D.naut.ptV i' Q = some x'} from hP')
    rw [← he, ← map_eqvMt_range_thetaT hμ hj]
    exact Submodule.map_mono h1

  have hsub : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) ≤ ⨆ P ∈ G, D.naut.typeV i P := by
    rw [LinearMap.range_eq_map, ← ((II (D.nd.j i) (D.nd.j_range i).1 (D.nd.j_range i).2).submodule_iSup_eq_top),
      Submodule.map_iSup]
    refine iSup_le fun σ => ?_
    by_cases h0 : D.what₂.isot (D.nd.j i) σ = ⊥
    · rw [h0, Submodule.map_bot]; exact bot_le
    obtain ⟨hg, i', hi', hHG, hAt⟩ := EX σ h0
    have hj : D.nd.j i' = D.nd.j i := ((D.nd.locs_mem _ _ i').1 hi').1
    have hμ := hmu i' hi'
    have h1 : D.what₂.isot (D.nd.j i') σ ≤ Formalism.MainNotions.N.goodPartM D.nd D.naut i' :=
      le_biSup (fun τ => D.what₂.isot (D.nd.j i') τ) (show σ ∈ {τ | D.nd.goodRow τ ∧ Formalism.MainNotions.N.AtM D.nd D.naut i' τ} from ⟨hg, hAt⟩)
    have h2 := Submodule.map_mono (f := D.what₂.thetaT (D.nd.mu i') (D.nd.j i')) h1
    rw [(PZ i' hHG).2.1] at h2
    rw [← map_eqvMt_thetaT_isot hμ hj]
    refine le_trans (Submodule.map_mono h2) ?_
    rw [Submodule.map_le_iff_le_comap]
    refine iSup₂_le fun x' hx' => ?_
    unfold Formalism.MainNotions.N.eigC
    refine iSup₂_le fun P' hP' => ?_
    rw [← Submodule.map_le_iff_le_comap]
    have hne : (NG.isoTyp (M.loc i').wt.ρ (A.S i' P')).comap (M.loc i').real ≠ ⊥ := by
      rw [← A.typeV i' P']; exact D.naut.typeV_ne i' P'
    obtain ⟨P, hP⟩ := typeV_of_transport A i hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (A.S i' P') (A.irr i' P') hne
    have hT : (D.naut.typeV i' P').map (eqvMt hμ hj).toLinearMap = D.naut.typeV i P := by
      rw [A.typeV i' P']; exact hP
    rw [hT]
    exact le_biSup (fun Q => D.naut.typeV i Q) (show P ∈ G from ⟨i', hi', x', hx', P', hP', hμ, hj, hT⟩)
  have hZG : LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)) = ⨆ P ∈ G, D.naut.typeV i P :=
    le_antisymm hsub (iSup₂_le hin)
  have hout : ∀ P, P ∉ G → D.naut.typeV i P ≤ (LinearMap.range (D.what₂.thetaT (D.nd.mu i) (D.nd.j i)))ᗮ := by
    intro P hP
    rw [← Submodule.isOrtho_iff_le]
    apply Submodule.IsOrtho.symm
    rw [Submodule.isOrtho_iff_le, hZG]
    refine iSup₂_le fun Q hQ => ?_
    rw [← Submodule.isOrtho_iff_le]
    exact TO Q P (fun h => hP (h ▸ hQ))
  unfold ZSpec
  rw [hZ0]
  intro P
  refine ⟨(em (P ∈ G)).elim (fun h => Or.inl (hin P h)) (fun h => Or.inr (hout P h)), fun x hx => ⟨fun hg => ?_, fun hb => hout P ?_⟩⟩
  · exact hin P ⟨i, (D.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩, x, (D.Zgood_tie i x).1 hg, P, hx, rfl, rfl, map_eqvMt_self _ _ _⟩
  · rintro ⟨i', hi', x', hx', P', hP', hμ, hj, he⟩
    obtain ⟨hj', hw'⟩ := (D.nd.locs_mem _ _ i').1 hi'
    by_cases hii : i' = i
    · subst hii
      rw [map_eqvMt_self] at he
      have hPP : P' = P := by
        by_contra hne
        have hd : Disjoint (D.naut.typeV i' P') (D.naut.typeV i' P) := (D.naut.typeV_indep i').pairwiseDisjoint hne
        rw [he] at hd
        exact D.naut.typeV_ne i' P (disjoint_self.1 hd)
      subst hPP
      rw [hx] at hP'
      cases hP'
      exact hb ((D.Zgood_tie _ _).2 hx')
    · obtain ⟨φ, hφ⟩ := HT.sameO i i' hj'.symm hw'.symm
      obtain ⟨v, k, hv, hv', k1, k2, hunit⟩ := HT.sep i i' φ hφ hj'.symm hw'.symm (Ne.symm hii) x x'
      obtain ⟨s, ϖ, hc, hu⟩ := SU v hv.1
      have e := eig_of_transport A i P x hx hμ hj (D.nd.j_range i').1 (D.nd.j_range i').2 (D.naut.typeV i' P') he
        v k s ϖ hv hc hu k1 k2 _ (fun y hy => A.eigen i' P' x' hP' v k s ϖ hv' hc hu k1 k2 y hy)
      rw [hφ] at e
      have hinj : Function.Injective (iotaOC D i') := by
        intro a b h
        simp only [iotaOC, RingHom.coe_comp, Function.comp_apply] at h
        exact IsFractionRing.injective (D.nd.O i') (FractionRing (D.nd.O i'))
          ((D.naut.iotaQ i').injective ((D.naut.iotaQC i').injective h))
      rw [hinj e, sub_self] at hunit
      exact not_isUnit_zero hunit

end GlobalTheory.EtaJoin.TypeSum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PeriodMatrixRestrictionScalarsBlockDiagonal
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.PMon

theorem unramifiedToBst_algebraMap_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) (q : ℚ_[l]) :
    ks P (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l) q) = algebraMap ℚ_[l] (Bst P) q := by
  simp only [ks, RingHom.comp_apply]
  rw [← IsScalarTower.algebraMap_apply, Polynomial.algebraMap_apply]

theorem frobeniusSemistablePow_unramifiedToBst {l : ℕ} [Fact l.Prime] (P : LocPrime l) (m : ℕ) (c : ↥(MaximalUnramifiedExtension l)) :
    (phiSt P ^ m) (ks P c) = ks P (fr l m c) := by
  induction m with
  | zero => rfl
  | succ m ih =>
    rw [pow_succ', AlgHom.mul_apply, ih, add_comm, fr_add, fr_one]
    have := phiSt_algebraMap P (fr l m c)
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply] at this
    exact this

theorem frobeniusSemistablePow_galoisAction_comm {l : ℕ} [Fact l.Prime] (P : LocPrime l) (g : GQ l) (m : ℕ) (b : Bst P) :
    (phiSt P ^ m) (actSt P g b) = actSt P g ((phiSt P ^ m) b) := by
  induction m generalizing b with
  | zero => rfl
  | succ m ih => rw [pow_succ', AlgHom.mul_apply, ih, phiSt_actSt, AlgHom.mul_apply]

end GlobalTheory.PMon

namespace GlobalTheory.PMon

theorem inv_entries_mem_finiteExtension_unramified {l : ℕ} [Fact l.Prime] {N : Type} [Fintype N] [DecidableEq N] (K : FinExt l)
    (p : GL N ↥(MaximalUnramifiedExtension l)) (h : ∀ i j, (((p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) (i j : N) :
    ((((p⁻¹ : GL N ↥(MaximalUnramifiedExtension l)) : Matrix N N ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1 := by
  let S : Subfield ↥(MaximalUnramifiedExtension l) := K.1.toSubfield.comap (algebraMap ↥(MaximalUnramifiedExtension l) (Om l))
  let A : Matrix N N S := Matrix.of fun i j => ⟨(p : Matrix N N ↥(MaximalUnramifiedExtension l)) i j, h i j⟩
  have hA : (S.subtype).mapMatrix A = (p : Matrix N N ↥(MaximalUnramifiedExtension l)) := by refine Matrix.ext fun i j => ?_; rfl
  have hmem : ((p : Matrix N N ↥(MaximalUnramifiedExtension l))⁻¹ i j) ∈ S := by
    rw [Matrix.inv_def, ← hA, ← RingHom.map_adjugate, ← RingHom.map_det]
    simp only [Matrix.smul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, smul_eq_mul, Ring.inverse_eq_inv']
    exact S.mul_mem (S.inv_mem (A.det).2) (A.adjugate i j).2
  rw [Matrix.coe_units_inv]
  exact hmem

theorem period_resScalars : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (r : ℕ)
    (σ : ↥(GK K) →* GL n ↥(MaximalUnramifiedExtension l)) (Q : GL n (Bst P)) (ρ₀ : ↥(GK K) →* GL (n × Fin r) ℚ_[l])
    (p : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)),
    (∀ g : ↥(GK K), (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P) * (Q : Matrix n n (Bst P)).map (actSt P (g : GQ l)) = Q) →
    (∀ i j, (((p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) i j : ↥(MaximalUnramifiedExtension l)) : Om l) ∈ K.1) →
    (∀ g, (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) *
          (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) =
        Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) *
          (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l))) →
    ∃ Q₀ : GL (n × Fin r) (Bst P), ∀ g : ↥(GK K),
      (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] (Bst P)) *
        (Q₀ : Matrix (n × Fin r) (n × Fin r) (Bst P)).map (actSt P (g : GQ l)) = Q₀ := by
  intro l _ P n _ _ K r σ Q ρ₀ p h1 h2 h3
  classical
  let φm : Fin r → Bst P →+* Bst P := fun m => ((phiSt P ^ (m : ℕ) : Bst P →ₐ[ℚ_[l]] Bst P) : Bst P →+* Bst P)
  let Pu : GL (n × Fin r) (Bst P) := Units.map (RingHom.mapMatrix (m := n × Fin r) (ks P)).toMonoidHom p⁻¹
  let Du : GL (n × Fin r) (Bst P) := Units.map (Matrix.blockDiagonalRingHom n (Fin r) (Bst P)).toMonoidHom
    (MulEquiv.piUnits.symm fun m => Units.map (RingHom.mapMatrix (m := n) (φm m)).toMonoidHom Q)
  refine ⟨Pu * Du, fun g => ?_⟩
  set pv : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l) := ((p⁻¹ : GL (n × Fin r) ↥(MaximalUnramifiedExtension l)) : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) with hpv
  have hPu : (Pu : Matrix (n × Fin r) (n × Fin r) (Bst P)) = pv.map (ks P) := rfl
  have hDu : (Du : Matrix (n × Fin r) (n × Fin r) (Bst P)) =
      Matrix.blockDiagonal fun m => (Q : Matrix n n (Bst P)).map (φm m) := rfl
  set act := actSt P (g : GQ l)

  have hPfix : (pv.map (ks P)).map act = pv.map (ks P) := by
    refine Matrix.ext fun i j => ?_
    simp only [Matrix.map_apply]
    exact act_ks P g (inv_entries_mem_finiteExtension_unramified K p h2 i j)

  have hrel : (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) * pv =
      pv * Matrix.blockDiagonal (fun m : Fin r => (σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)) := by
    have hp : pv * (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) = 1 := by
      rw [hpv, ← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hp' : (p : Matrix (n × Fin r) (n × Fin r) ↥(MaximalUnramifiedExtension l)) * pv = 1 := by
      rw [hpv, ← Units.val_mul, mul_inv_cancel, Units.val_one]
    calc _ = pv * ((p : Matrix _ _ ↥(MaximalUnramifiedExtension l)) * (ρ₀ g : Matrix (n × Fin r) (n × Fin r) ℚ_[l]).map
            (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l))) * pv := by rw [← Matrix.mul_assoc, hp, Matrix.one_mul]
      _ = _ := by rw [h3, Matrix.mul_assoc, Matrix.mul_assoc, hp', Matrix.mul_one]
  have hrelB := congrArg (fun M => M.map (ks P)) hrel
  simp only [Matrix.map_mul, Matrix.map_map] at hrelB
  have hks : (ks P) ∘ (algebraMap ℚ_[l] ↥(MaximalUnramifiedExtension l)) = algebraMap ℚ_[l] (Bst P) := funext (unramifiedToBst_algebraMap_padic P)
  rw [hks, Matrix.blockDiagonal_map _ _ (map_zero _)] at hrelB

  have hblock : ∀ m : Fin r, ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) *
      ((Q : Matrix n n (Bst P)).map (φm m)).map act = (Q : Matrix n n (Bst P)).map (φm m) := by
    intro m
    have e1 : ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (fr l m)).map (ks P) =
        ((σ g : Matrix n n ↥(MaximalUnramifiedExtension l)).map (ks P)).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom]; exact (frobeniusSemistablePow_unramifiedToBst P m _).symm
    have e2 : ((Q : Matrix n n (Bst P)).map (φm m)).map act =
        ((Q : Matrix n n (Bst P)).map act).map (φm m) := by
      refine Matrix.ext fun i j => ?_; simp only [Matrix.map_apply, φm, AlgHom.coe_toRingHom, act]; exact (frobeniusSemistablePow_galoisAction_comm P _ m _).symm
    rw [e1, e2, ← Matrix.map_mul, h1 g]
  rw [Units.val_mul, hPu, hDu, Matrix.map_mul, hPfix, Matrix.blockDiagonal_map _ _ (map_zero _),
    ← Matrix.mul_assoc, hrelB, Matrix.mul_assoc, ← Matrix.blockDiagonal_mul]
  congr 2
  funext m
  exact hblock m

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PowPrimeMemUnitFiltrationUnitsMin
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem exists_one_add_pow_eq {R : Type*} [CommRing R] (y : R) (k : ℕ) :
    ∃ w : R, (1 + y) ^ k = 1 + (k : R) * y + y ^ 2 * w := by
  induction k with
  | zero => exact ⟨0, by simp⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨(1 + y) * w + k, ?_⟩
    rw [pow_succ, hw]; push_cast; ring

theorem one_add_pow_sub_one_mem {R : Type*} [CommRing R] (I : Ideal R) {n e k : ℕ} {y : R}
    (hy : y ∈ I ^ n) (hk : (k : R) ∈ I ^ e) :
    (1 + y) ^ k - 1 ∈ I ^ min (2 * n) (n + e) := by
  obtain ⟨w, hw⟩ := exists_one_add_pow_eq y k
  have h : (1 + y) ^ k - 1 = (k : R) * y + y ^ 2 * w := by rw [hw]; ring
  rw [h]
  refine Ideal.add_mem _ ?_ ?_
  · refine Ideal.pow_le_pow_right (min_le_right _ _) ?_
    rw [add_comm n e, pow_add]
    exact Ideal.mul_mem_mul hk hy
  · refine Ideal.pow_le_pow_right (min_le_left _ _) ?_
    refine Ideal.mul_mem_right _ _ ?_
    rw [two_mul, pow_add, pow_two]
    exact Ideal.mul_mem_mul hy hy

theorem natCast_mem_maximalIdeal_pow_of_ordIs {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {p e : ℕ} (h : OrdIs F p e) : (p : 𝒪[F]) ∈ 𝓂[F] ^ e := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton,
    ← IsDiscreteValuationRing.addVal_le_iff_dvd, IsDiscreteValuationRing.addVal_pow,
    IsDiscreteValuationRing.addVal_uniformizer hϖ]
  rw [OrdIs] at h
  rw [h]
  simp

theorem pow_mem_unitFiltrationUnits (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (p e n : ℕ) (hp : OrdIs F p e) :
    ∀ x ∈ unitFiltrationUnits F n, x ^ p ∈ unitFiltrationUnits F (min (2 * n) (n + e)) := by
  rintro _ ⟨u, hu, rfl⟩
  refine ⟨u ^ p, ?_, by simp⟩
  rw [SetLike.mem_coe, mem_unitFiltration] at hu ⊢
  have := one_add_pow_sub_one_mem (𝓂[F]) hu (natCast_mem_maximalIdeal_pow_of_ordIs hp)
  simpa using this

end GlobalTheory.PMon.Ram

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProductMapTensorAinfToBcrisWachInclusionConstant
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.HWL

namespace GlobalTheory.EvalIdem

theorem ringHom_eq_of_unique {O A S : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing S]
    (Q : A → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : A →ₐ[O] S), (∀ a, Q a → f a = f' a) → f = f')
    (F F' : A →+* S) (h0 : ∀ o, F (algebraMap O A o) = F' (algebraMap O A o))
    (h1 : ∀ a, Q a → F a = F' a) (a : A) : F a = F' a := by
  let _ : Algebra O S := (F.comp (algebraMap O A)).toAlgebra
  have := h S ⟨F, fun _ => rfl⟩ ⟨F', fun o => (h0 o).symm⟩ h1
  exact DFunLike.congr_fun this a

theorem io_const {O T : Type} [CommRing O] [CommRing T] [Algebra O T] {n : ℕ} (f : LetA O n →ₐ[O] T) (x : O) :
    f (fun j => PowerSeries.C (algebraMap O (ZMod n → O) x j)) = algebraMap O T x := f.commutes x

theorem const_eq {O T S : Type} [CommRing O] [CommRing T] [Algebra O T] [CommRing S] {n : ℕ}
    (Q : (ZMod n → O) → Prop)
    (h : ∀ (S : Type) [CommRing S] [Algebra O S] (f f' : (ZMod n → O) →ₐ[O] S),
      (∀ a, Q a → f a = f' a) → f = f')
    (f : LetA O n →ₐ[O] T) (G : T →+* S) (e : O →+* S) (i : ZMod n)
    (h0 : ∀ x, G (algebraMap O T x) = e x)
    (h1 : ∀ a, Q a → G (f (fun j => PowerSeries.C (a j))) = e (a i)) (a : ZMod n → O) :
    G (f (fun j => PowerSeries.C (a j))) = e (a i) :=
  ringHom_eq_of_unique Q h
    (G.comp (f.toRingHom.comp (RingHom.pi fun j =>
      (PowerSeries.C : O →+* PowerSeries O).comp (Pi.evalRingHom _ j))))
    (e.comp (Pi.evalRingHom _ i)) (fun x => (congrArg G (io_const f x)).trans (h0 x)) h1 a

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P} {LL : FinExt l}

theorem component_tmul {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) (w : Ainf l) :
    Algebra.TensorProduct.productMap ι P.ιB (β (x ⊗ₜ[ℤ_[l]] w)) = ι (x : ↥LL.1) * P.ιB (AI.ιA w) := by
  rw [hβ, Algebra.TensorProduct.productMap_apply_tmul]

theorem component_algebraMap {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) (x : ↥(OL LL)) :
    Algebra.TensorProduct.productMap ι P.ιB (β (algebraMap ↥(OL LL) (RA LL) x)) = ι (x : ↥LL.1) := by
  have h1 : algebraMap ↥(OL LL) (RA LL) x = x ⊗ₜ[ℤ_[l]] (1 : Ainf l) := rfl
  rw [h1, component_tmul hβ, map_one, map_one, mul_one]

theorem component_teich {β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B} (hβ : IsBeta AI β)
    (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR) {K : FinExt l} (c : ↥(K0 K)) (m : ℕ) (hm : 0 < m) (hl : ¬ l ∣ m)
    (hc : (c : Om l) ^ m = 1) (xb : OCb l) (hxb : IsTiltOf (c : Om l) m xb) :
    Algebra.TensorProduct.productMap ι P.ιB
      (β ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] WittVector.teichmuller l xb)) = algebraMap ↥(K0 K) P.R.BdR c := by
  rw [component_tmul hβ, AI.ιA_teich ⟨c, c.2.2⟩ m hm hl hc xb hxb, GlobalTheory.LocIota.ιB_algebraMap_Kur,
    OneMemClass.coe_one, map_one, one_mul]
  rfl


set_option maxHeartbeats 800000 in
theorem component_const : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K : FinExt l) (s : ℕ) (LL : FinExt l), Good K s LL → ∀ (Γ : GamS P K s LL) (R : WSer Γ) (I : IoS AI R), IoW I → ∀ β : RA LL →+* ↥LL.1 ⊗[ℚ_[l]] P.R.B, IsBeta AI β → ∀ (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ι : ↥LL.1 →ₐ[ℚ_[l]] P.R.BdR), (∀ c : ↥(K0 K), ι (Γ.emb i c) = algebraMap ↥(K0 K) P.R.BdR c) → ∀ o : ZMod (Module.finrank ℚ_[l] ↥(K0 K)) → ↥(OL LL), Algebra.TensorProduct.productMap ι P.ιB (β (I.io (fun j => PowerSeries.C (o j)))) = ι (o i : ↥LL.1) := by
  intro l _ P AI T K s LL hG Γ R I hI β hβ i ι hι o
  obtain ⟨-, -, hu⟩ := _root_.GlobalTheory.UnramIdem.exists_prod_hom l P K s LL hG Γ.emb Γ.emb_bij
  refine const_eq
    (fun a => ∃ (c : ↥(K0 K)) (m : ℕ), 0 < m ∧ ¬ l ∣ m ∧ (c : Om l) ^ m = 1 ∧
      ∀ j, ((a j : ↥(OL LL)) : ↥LL.1) = Γ.emb j c)
    (fun S _ _ f f' h => hu S f f' fun c m hm hl hc a ha => h a ⟨c, m, hm, hl, hc, ha⟩) I.io
    ((Algebra.TensorProduct.productMap ι P.ιB).toRingHom.comp β)
    (ι.toRingHom.comp (algebraMap ↥(OL LL) ↥LL.1)) i (component_algebraMap hβ ι) ?_ o
  rintro a ⟨c, m, hm, hl, hc, ha⟩
  obtain ⟨xb, hxb⟩ := GlobalTheory.MemLoc.exists_isTiltOf (c : Om l) m hm hl hc
  have h1 := component_teich hβ ι c m hm hl hc xb hxb
  rw [← hI c m hm hl hc xb hxb a ha, ← hι, ← ha] at h1
  exact h1

end GlobalTheory.EvalIdem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationJumpSumComapInjective
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ValuativeRel GroundTheory.LocalField GlobalTheory.PMon.Ram

namespace GlobalTheory.PMon.Ram

theorem jumpSum_comap_injective :
    ∀ (G G' : Type) [Group G] [Group G'] (j : G' →* G) (R : ℕ → Subgroup G) (B : Subgroup G), Function.Injective j →
      jumpSum (fun t => (R t).comap j) ⊤ (B.comap j) = jumpSum R j.range B := by
  intro G G' _ _ j R B hj
  unfold jumpSum
  apply finsum_congr
  intro t
  have h1 : (⊤ ⊓ (R t).comap j ≤ B.comap j) ↔ (j.range ⊓ R t ≤ B) := by
    rw [top_inf_eq]
    constructor
    · rintro h x ⟨⟨y, rfl⟩, hy⟩
      exact h (show y ∈ (R t).comap j from hy)
    · intro h y hy
      exact h ⟨⟨y, rfl⟩, hy⟩
  have h2 : Nat.card ↥(⊤ ⊓ (R t).comap j) = Nat.card ↥(j.range ⊓ R t) := by
    rw [top_inf_eq, ← Subgroup.map_comap_eq, Subgroup.card_map_of_injective hj]
  rw [h2]
  by_cases h : j.range ⊓ R t ≤ B
  · rw [if_pos (h1.mpr h), if_pos h]
  · rw [if_neg (fun h' => h (h1.mp h')), if_neg h]

end GlobalTheory.PMon.Ram
end

