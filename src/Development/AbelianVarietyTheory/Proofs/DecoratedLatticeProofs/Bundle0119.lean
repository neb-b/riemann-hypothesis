module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmEulerProductDiscrUnramified
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0108
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0087
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlace

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HermitianAdjointSymplecticActionThetaHeisenberg
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

open scoped ContDiff

namespace GlobalTheory.AdjointPair

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger

variable {D : D7}

theorem dagger_add (S T : HSp D) (x y : WO S T) : dagger S T (x + y) = dagger S T x + dagger S T y := by
  simp only [dagger, adj_add, Matrix.mul_add, Matrix.add_mul]

def daggerHom (S T : HSp D) : WO S T →+ WO T S where
  toFun := dagger S T
  map_zero' := by simp only [dagger, adj_zero, Matrix.zero_mul, Matrix.mul_zero]
  map_add' := dagger_add S T

theorem continuous_dagger (S T : HSp D) : Continuous (dagger S T) :=
  continuous_const.matrix_mul (continuous_adj.matrix_mul continuous_const)

theorem dagger_rat (S T : HSp D) (γ : Matrix (Fin T.rank) (Fin S.rank) D.host.E) :
    dagger S T (rat γ) = rat (S.gram⁻¹ * (γᴴ * T.gram)) := by
  rw [rat_mul, rat_mul, rat_conjTranspose]; rfl

theorem infPart_cA (z : AE D) : infPart D (cA D z) = sigR (Ainf D.host.F) D.sp.cm.sig (infPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem finPart_cA (z : AE D) : finPart D (cA D z) = sigR (Af D.host.F) D.sp.cm.sig (finPart D z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [RingHom.map_zero]
  | add x y hx hy => simp only [RingHom.map_add (f := _), hx, hy]
  | tmul a x => rfl

theorem map_dagger_zero {B : Type} [CommRing B] (p : AE D →+* B) (hp : ∀ z, p z = 0 → p (cA D z) = 0)
    (S T : HSp D) {x : WO S T} (hx : x.map p = 0) : (dagger S T x).map p = 0 := by
  have h1 : (adj x).map p = 0 := by
    funext i j
    have := congrFun (congrFun hx j) i
    simp only [adj, Matrix.map_apply, Matrix.transpose_apply, Matrix.zero_apply] at this ⊢
    exact hp _ this
  rw [dagger, Matrix.map_mul, Matrix.map_mul, h1, Matrix.zero_mul, Matrix.mul_zero]

theorem infPart_zero (z : AE D) (h : infPart D z = 0) : infPart D (cA D z) = 0 := by
  rw [infPart_cA, h, RingHom.map_zero]

theorem finPart_zero (z : AE D) (h : finPart D z = 0) : finPart D (cA D z) = 0 := by
  rw [finPart_cA, h, RingHom.map_zero]

theorem hO_dagger (S T : HSp D) (x y : WO S T) : hO T S (dagger S T x) (dagger S T y) = hO S T y x := by
  rw [hO_eq_trace, hO_eq_trace]
  simp only [dagger, adj_mul, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc, gA_giA_cancel, giA_gA_cancel]
  rw [Matrix.trace_mul_comm]
  simp only [Matrix.mul_assoc]

theorem symplO_dagger (S T : HSp D) (x y : WO S T) :
    symplO T S (dagger S T x) (dagger S T y) = -symplO S T x y := by
  have h := GlobalTheory.OrientedHeis.symplO_skew x y
  unfold symplO at h ⊢
  rw [hO_dagger]
  exact h

theorem symplOH_dagger (S T : HSp D) (x y : WO S T) :
    symplOH T S (dagger S T x) (dagger S T y) = -symplOH S T x y := by
  unfold symplOH
  rw [symplO_dagger, mul_neg]

theorem act_dagger (S T : HSp D) (g : GA D S) (h : GA D T) (x : WO S T) :
    dagger S T (actO S T g h x) = actO T S h g (dagger S T x) := by
  simp only [dagger, actO_eq, adj_mul, mt_inv S g, mt_inv T h, adj_adj, adj_gA, adj_giA, Matrix.mul_assoc,
    giA_gA_cancel, gA_giA_cancel]

theorem conj_psi {ψ : AddChar (AF D.host.F) ℂ} (hn : ∀ a, ‖ψ a‖ = 1) (a : AF D.host.F) :
    starRingEnd ℂ (ψ a) = ψ (-a) := by
  rw [AddChar.map_neg_eq_inv]
  exact (Complex.inv_eq_conj (hn a)).symm

theorem heis_dagger (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (w : WO S T)
    (f : WO S T → ℂ) : heisO ψ T S (dagger S T w) (cj (dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) (heisO ψ S T w f) := by
  funext y
  have hs : symplOH T S y (dagger S T w) = -symplOH S T (dagger T S y) w := by
    have := symplOH_dagger S T (dagger T S y) w
    rwa [dagger_dagger] at this
  simp only [heisO, GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, map_mul]
  rw [dagger_add, dagger_dagger, hs, conj_psi hn]

theorem theta_fwd (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) {f : WO S T → ℂ}
    (hf : IsThetaFunO ψ S T f) : IsThetaFunO ψ T S (cj (dagger T S) f) := {
  quasi γ w := by
    have hr : dagger T S (ratW S T γ) = ratW T S (T.gram⁻¹ * (γᴴ * S.gram)) := by
      rw [ratW_eq, ratW_eq]; exact dagger_rat T S γ
    have hq := hf.quasi (T.gram⁻¹ * (γᴴ * S.gram)) (dagger T S w)
    rw [← hr, symplOH_dagger, neg_neg] at hq
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj]
    rw [dagger_add, hq, map_mul, conj_psi hn]
  level := by
    obtain ⟨U, hU, hfix⟩ := hf.level
    refine ⟨U.comap (daggerHom T S), hU.preimage (continuous_dagger T S), fun u hu hinf => ?_⟩
    have h1 := heis_dagger ψ hn S T (dagger T S u) f
    rw [dagger_dagger, hfix (dagger T S u) hu (map_dagger_zero (infPart D) infPart_zero T S hinf)] at h1
    exact h1
  cont := Complex.continuous_conj.comp (hf.cont.comp (continuous_dagger T S))
  smooth k L hL hfin w := by
    have h := hf.smooth k ((daggerHom T S).comp L) ((continuous_dagger T S).comp hL)
      (fun t => map_dagger_zero (finPart D) finPart_zero T S (hfin t)) (dagger T S w)
    have e : (fun t => GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (dagger T S) f (w + L t)) =
        fun t => Complex.conjCLE (f (dagger T S w + (daggerHom T S).comp L t)) := by
      funext t
      simp only [GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj, AddMonoidHom.comp_apply, Complex.conjCLE_apply]
      rw [dagger_add]; rfl
    rw [e]
    exact Complex.conjCLE.contDiff.comp h }

theorem theta_iff (ψ : AddChar (AF D.host.F) ℂ) (hn : ∀ a, ‖ψ a‖ = 1) (S T : HSp D) (f : WO S T → ℂ) :
    IsThetaFunO ψ T S (cj (dagger T S) f) ↔ IsThetaFunO ψ S T f := by
  refine ⟨fun h => ?_, theta_fwd ψ hn S T⟩
  have := theta_fwd ψ hn T S h
  rwa [cj_cj (dagger T S) (dagger S T) (dagger_dagger S T)] at this

theorem adjoint_clauses : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) → ∀ S T : HSp D, (∀ x y : WO S T, symplO T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T y) = -symplO S T x y) ∧ (∀ g h (x : WO S T), GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T (actO S T g h x) = actO T S h g (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T x)) ∧ (∀ f : WO S T → ℂ, IsThetaFunO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) ↔ IsThetaFunO ψ S T f) ∧ ∀ (w : WO S T) (f : WO S T → ℂ), heisO ψ T S (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger S T w) (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) f) = GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.cj (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.dagger T S) (heisO ψ S T w f) := by
  intro D ψ hψ S T
  exact ⟨symplO_dagger S T, act_dagger S T, fun f => theta_iff ψ hψ.1.2.1 S T f, heis_dagger ψ hψ.1.2.1 S T⟩

end GlobalTheory.AdjointPair

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralCompAddEquivEqSmul
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.HalfTwist

theorem integral_comp_addEquiv_eq_smul {G : Type*} [AddGroup G] [TopologicalSpace G] [IsTopologicalAddGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    (ν : Measure G) [ν.IsAddHaarMeasure] (T : G ≃+ G) (hc : Continuous T) (hc' : Continuous T.symm) :
    ∃ r : ℝ, 0 < r ∧ ∀ φ : G → ℂ, ∫ x, φ (T x) ∂ν = r * ∫ x, φ x ∂ν := by
  haveI : (ν.map T).IsAddHaarMeasure := AddEquiv.isAddHaarMeasure_map ν T hc hc'
  let hT : G ≃ₜ G := { toEquiv := T.toEquiv, continuous_toFun := hc, continuous_invFun := hc' }
  have hemb : MeasurableEmbedding T := hT.measurableEmbedding
  refine ⟨((ν.map T).addHaarScalarFactor ν : ℝ), NNReal.coe_pos.2 (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _), ?_⟩
  intro φ
  have e := Measure.isAddLeftInvariant_eq_smul (ν.map T) ν
  rw [← hemb.integral_map φ]
  refine (congrArg (fun μ : Measure G => ∫ y, φ y ∂μ) e).trans ?_
  show ∫ y, φ y ∂(((ν.map T).addHaarScalarFactor ν) • ν) = _
  rw [integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

theorem isClosed_fix (D : D7) (m n : ℕ) (c : AE D) : IsClosed {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
  obtain ⟨i1, i2, -⟩ := Formalism.IndefR.Eqv.ae_facts D
  have : {x : Mx D m n | ∀ i j, c * x i j = x i j} = ⋂ i, ⋂ j, {x : Mx D m n | c * x i j = x i j} := by
    ext x; simp
  rw [this]
  refine isClosed_iInter fun i => isClosed_iInter fun j => isClosed_eq ?_ ?_
  · exact continuous_const.mul ((continuous_apply j).comp (continuous_apply i))
  · exact (continuous_apply j).comp (continuous_apply i)

theorem integral_twist_fix_eq_smul : ∀ (D : D7) (m n : ℕ) (c : AE D) (H : AddSubgroup (Mx D m n)), (∀ x, x ∈ H ↔ ∀ i j, c * x i j = x i j) → ∀ [MeasurableSpace H] [BorelSpace H] (ν : Measure H) [ν.IsAddHaarMeasure] (h : GL (Fin m) (AE D)) (a : GL (Fin n) (AE D)), ∃ r : ℝ, 0 < r ∧ ∀ φ : Mx D m n → ℂ, ∫ x : H, φ (h.1 ⬝ x.1 ⬝ a.1) ∂ν = r * ∫ x : H, φ x.1 ∂ν := by
  intro D m n c H hH _ _ ν _ h a
  obtain ⟨i1, i2, i3, i4, -⟩ := lattice_Mx D m n
  have key : ∀ y : Mx D m n, y ∈ H ↔ c • y = y := by
    intro y
    rw [hH]
    constructor
    · intro hy; ext i j; simpa using hy i j
    · intro hy i j; simpa using congrFun (congrFun hy i) j
  have mem : ∀ (g : GL (Fin m) (AE D)) (b : GL (Fin n) (AE D)) (y : Mx D m n), y ∈ H → g.1 ⬝ y ⬝ b.1 ∈ H := by
    intro g b y hy
    rw [key] at hy ⊢
    show c • (g.1 * y * b.1) = g.1 * y * b.1
    rw [← Matrix.smul_mul, ← Matrix.mul_smul, hy]
  have hcl : IsClosed (H : Set (Mx D m n)) := by
    have : (H : Set (Mx D m n)) = {x : Mx D m n | ∀ i j, c * x i j = x i j} := by
      ext x; exact hH x
    rw [this]; exact isClosed_fix D m n c
  haveI : LocallyCompactSpace H := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology H := Topology.IsInducing.subtypeVal.secondCountableTopology
  let T : H ≃+ H :=
    { toFun := fun x => ⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩
      invFun := fun x => ⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩
      left_inv := fun x => by
        apply Subtype.ext
        show (h⁻¹).1 * (h.1 * x.1 * a.1) * (a⁻¹).1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul, Matrix.mul_assoc, Units.mul_inv,
          Matrix.mul_one]
      right_inv := fun x => by
        apply Subtype.ext
        show h.1 * ((h⁻¹).1 * x.1 * (a⁻¹).1) * a.1 = x.1
        rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul, Matrix.mul_assoc, Units.inv_mul,
          Matrix.mul_one]
      map_add' := fun x y => by
        apply Subtype.ext
        show h.1 * (x.1 + y.1) * a.1 = h.1 * x.1 * a.1 + h.1 * y.1 * a.1
        rw [Matrix.mul_add, Matrix.add_mul] }
  have hc : Continuous T := by
    show Continuous fun x : H => (⟨h.1 ⬝ x.1 ⬝ a.1, mem h a x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  have hc' : Continuous T.symm := by
    show Continuous fun x : H => (⟨(h⁻¹).1 ⬝ x.1 ⬝ (a⁻¹).1, mem h⁻¹ a⁻¹ x.1 x.2⟩ : H)
    exact Continuous.subtype_mk ((continuous_const.matrix_mul continuous_subtype_val).matrix_mul continuous_const) _
  obtain ⟨r, hr, hφ⟩ := integral_comp_addEquiv_eq_smul ν T hc hc'
  exact ⟨r, hr, fun φ => hφ (fun x : H => φ x.1)⟩

end GlobalTheory.HalfTwist
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsSelfDualLatticeAtPlaceLatticeCompletion
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
open NumberField GlobalTheory.FinPl.FrameLat
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.IwaPlace.LocSD

variable {D : D7}

theorem exists_idem (v : Pl D) :
    ∃ ε : AE D, cA D ε = ε ∧ ε ∈ intAt D (· = v) ∧ ∀ a, a ∈ idAt D (· = v) → ε * a = a := by
  have hs := GlobalTheory.LatAlmostStd.intSupp_single_mul v (α := 1) (fun w => by rw [map_one]; exact one_mem _)
  rw [mul_one] at hs
  have hp : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨_, rfl, GlobalTheory.LatAlmostStd.evalV_single_same v 1, fun w hw => GlobalTheory.LatAlmostStd.evalV_single_ne v 1 hw⟩
  refine ⟨pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (1 : D.host.E), ?_,
    ⟨GlobalTheory.FinPl.LatMem.tmul_mem_idAt hs.2 _, AddSubgroup.subset_closure ⟨_, hs.1, 1, rfl⟩⟩,
    fun a ha => ((placeIdem_acts D v _ hp).1 a).1 ha⟩
  change pairA D.host.F 0 (singleV D.host.F v 1) ⊗ₜ[D.host.F] (D.sp.cm.sig (1 : D.host.E)) = _
  rw [map_one]

variable {S : HSp D}

theorem hermAt_mul_inc (y : Fin S.rank → AE D) (a : AE D) (s : Fin S.rank → D.host.E) :
    hermAt S y (fun i => a * incA D (s i)) = cA D a * pairing S s y := by
  unfold hermAt pairing FrameLat.row
  rw [Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [RingHom.map_mul, RingHom.map_mul, cA_incA, show gA S i j = incA D (S.gram i j) from rfl]
  ring

theorem hermAt_sum_right {m : ℕ} (y : Fin S.rank → AE D) (x : Fin m → Fin S.rank → AE D) :
    hermAt S y (fun i => ∑ l, x l i) = ∑ l, hermAt S y (x l) := by
  unfold hermAt
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Finset.sum_mul]
  rw [Finset.sum_comm (s := Finset.univ (α := Fin m))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]

theorem hermAt_mem_idAt {P : Pl D → Prop} {y : Fin S.rank → AE D} (hy : ∀ i, y i ∈ idAt D P)
    (x : Fin S.rank → AE D) : hermAt S y x ∈ idAt D P :=
  Ideal.sum_mem _ fun _ _ => Ideal.sum_mem _ fun j _ => Ideal.mul_mem_left _ _ (hy j)

variable {L : Lat S}

theorem exists_mul_mem (hL : IsSelfDualC S L) (v : Pl D) :
    ∃ m : ℕ, 0 < m ∧ ∀ y : Fin S.rank → AE D, (∀ i, y i ∈ intAt D (· = v)) → (m : AE D) • y ∈ latV S L (· = v) := by
  have hfull : Submodule.IsFullLattice D.host.E L := by
    haveI : Submodule.IsLattice D.host.E L := hL.1
    refine ⟨?_⟩
    obtain ⟨m, s, s', hs, _, hd⟩ := GlobalTheory.FinPl.LatMem.exists_dualBasis S hL
    apply eq_top_iff.mpr
    intro y _
    have hy : y = ∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) • s l := by
      funext a
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
      have heq : (∑ l, (∑ b, (∑ k, star (s' l k) * S.gram k b) * y b) * s l a) =
          ∑ b, ∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun l _ => Finset.sum_mul ..
      rw [heq]
      have hterm : ∀ b, (∑ l, (∑ k, star (s' l k) * S.gram k b) * y b * s l a) =
          (if a = b then 1 else 0) * y b := by
        intro b
        calc
          _ = ∑ l, (s l a * ∑ k, star (s' l k) * S.gram k b) * y b := by
            refine Finset.sum_congr rfl fun l _ => ?_
            ring
          _ = _ := by rw [← Finset.sum_mul, hd]
      simp_rw [hterm]
      simp
    rw [hy]
    exact Submodule.sum_mem _ fun l _ => Submodule.smul_mem _ _ (Submodule.subset_span (hs l))
  obtain ⟨N, hN, -, h⟩ := GlobalTheory.LatAlmostStd.exists_commensurable L hfull
  refine ⟨N.natAbs, Int.natAbs_pos.2 hN, fun y hy => ?_⟩
  have h1 : (N : AE D) • y ∈ latV S L (· = v) := by
    have e : (N : AE D) • y = ∑ i, fun k => y i * incA D ((Pi.single i (N • ((1 : 𝓞 D.host.E) : D.host.E)) :
        Fin S.rank → D.host.E) k) := by
      funext k
      rw [Finset.sum_apply, Finset.sum_eq_single k]
      · rw [Pi.single_eq_same, map_zsmul, show ((1 : 𝓞 D.host.E) : D.host.E) = 1 from rfl, RingHom.map_one,
          zsmul_one, Pi.smul_apply, smul_eq_mul, mul_comm]
      · intro i _ hi
        rw [Pi.single_eq_of_ne' hi, RingHom.map_zero, mul_zero]
      · intro hk; exact absurd (Finset.mem_univ k) hk
    rw [e]
    exact sum_mem fun i _ => int_mul_mem (hy i) (h i 1)
  rcases Int.natAbs_eq N with e | e
  · rw [← Int.cast_natCast, ← e]; exact h1
  · have e' : ((N.natAbs : ℕ) : ℤ) = -N := by omega
    rw [← Int.cast_natCast, e', Int.cast_neg, neg_smul]; exact neg_mem h1

theorem isSDAt_latV : ∀ (D : D7) (S : HSp D) (L : Lat S) (v : Pl D), IsSelfDualC S L → IsSDAt S v (latV S L (· = v)) := by
  intro D S L v hL
  refine ⟨fun y hy i => latV_supp hy i, exists_mul_mem hL v, fun y hy => ⟨fun hyL x hx => ?_, fun h => ?_⟩⟩
  · refine ⟨hermAt_mem_idAt hy x, ?_⟩
    obtain ⟨m, s, s', hs, hs', hd⟩ := exists_expansion hL
    have e : x = fun i => ∑ l, (fun l i => pairing S (s' l) x * incA D (s l i)) l i := funext fun i => hd x i
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, hermAt_sum_right, map_sum]
    refine sum_mem fun l _ => ?_
    rw [hermAt_mul_inc, RingHom.map_mul]
    exact mul_mem_intAE ((cA_int_iff _).2 (pairing_int hL (hs' l) hx)) (pairing_int hL (hs l) hyL)
  · obtain ⟨ε, hc, hε, hact⟩ := exists_idem v
    refine mem_of_pairing hL hy fun s hs => ?_
    have h1 := (h _ (int_mul_mem hε hs)).2
    rwa [hermAt_mul_inc, hc, hact (pairing S s y) (Ideal.sum_mem _ fun b _ => Ideal.mul_mem_left _ _ (hy b))] at h1

end GlobalTheory.IwaPlace.LocSD

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsTameFinitePlaceHermitianAll
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing
open NumberField IsDedekindDomain
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FinPl.TamePlaces

theorem extUnramAt (D : D7) (v : Pl D) : GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter.ExtUnramAt D v := by
  intro P hP _
  refine not_dvd_differentIdeal_iff.1 ?_
  rw [GlobalTheory.DensityEuler.differentIdeal_eq_top D.sp.cm]
  intro hd
  exact hP.ne_top (top_le_iff.1 (Ideal.dvd_iff_le.1 hd))

theorem split_over_two (D : D7) (v : Pl D) (h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal) :
    ∃ e ε, IsSplitIdem D e ∧ IsPlaceIdem D v ε ∧ e + cA D e = algebraMap (AF D.host.F) (AE D) ε := by
  obtain ⟨e, he, hc, hs, -⟩ := GlobalTheory.SplitIdem.exists_split_idempotent D v h2
  have hε : IsPlaceIdem D v (pairA D.host.F 0 (singleV D.host.F v 1)) :=
    ⟨singleV D.host.F v 1, rfl, GlobalTheory.SplitIdem.evalV_singleV_same D.host.F v 1,
      fun v' hv' => GlobalTheory.SplitIdem.evalV_singleV_ne D.host.F v 1 hv'⟩
  exact ⟨e, _, ⟨he, hc, v, _, hε, hs⟩, hε, hs⟩

theorem tame : ∀ (D : D7) (v : Pl D), Tame D v := by
  intro D v
  refine ⟨extUnramAt D v, ?_⟩
  by_cases h2 : (2 : 𝓞 D.host.F) ∈ v.asIdeal
  · exact Or.inr (split_over_two D v h2)
  · exact Or.inl h2

end GlobalTheory.FinPl.TamePlaces
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemLatticeCompletionAtPlacesOfFinPartMemHatLattiStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_latticeCompletionAtPlaces_of_finPart_mem_hatLattice : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → (fun i => Formalism.IndefR.Lev.swapAE D (finPart D (y i))) ∈ Formalism.L2.Herm.hatL (F := D.host.F) L → y ∈ latV S L P := by
  first | exact @GlobalTheory.HatLatV.mem_latV_of_hatL | exact GlobalTheory.HatLatV.mem_latV_of_hatL | (intros; apply GlobalTheory.HatLatV.mem_latV_of_hatL <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MixedModelCentralTermsGramIdentitiesStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mixed_model_central_terms_gram_identities : ∀ D : D7, (∀ (S S₀ T : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ), (∀ x : Mx D T.rank ρ, GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.starAdj S T (d.extX T x) ⬝ x = d.jY ⬝ (GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D)) ∧ ∀ (c : skewA D ρ) (x : Mx D T.rank ρ), d.qS T c x = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((GlobalTheory.IndefiniteRowSideFullHecke.SkewGramHalfModule.gramSkew T x).map (cA D) ⬝ c.1).trace)) ∧ ∀ (S T T₀ : HSp D) (ρ : ℕ) (d : HypDec T T₀ ρ) (c : skewA D ρ) (y : Mx D S.rank ρ), d.qT S c y = -(algebraMap D.host.F (AF D.host.F) (1 / 2) * Algebra.trace (AF D.host.F) (AE D) ((incA D D.host.xi0⁻¹ • (adj y ⬝ (gA S ⬝ y))) ⬝ c.1).trace) := by
  first | exact @GlobalTheory.CentralGram.central_gram | exact GlobalTheory.CentralGram.central_gram | (intros; apply GlobalTheory.CentralGram.central_gram <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RationalFramesSameGramOneUnitaryOrbitStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.rational_frames_same_gram_one_unitary_orbit : ∀ (D : D7) (W : HSp D) (ρ : ℕ) (x₀ : Matrix (Fin W.rank) (Fin ρ) D.host.E), LinearIndependent D.host.E x₀.transpose → (∀ x ∈ Orb W x₀, ∃ γ ∈ GQ W, mt W γ * (rat x₀ : Mx D W.rank ρ) = rat x) ∧ ∀ γ ∈ GQ W, ∀ x ∈ Orb W x₀, ∃ x' ∈ Orb W x₀, mt W γ * (rat x : Mx D W.rank ρ) = rat x' := by
  first | exact @GlobalTheory.WittOrbit.orb_eq_orbit | exact GlobalTheory.WittOrbit.orb_eq_orbit | (intros; apply GlobalTheory.WittOrbit.orb_eq_orbit <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeHyperbolicLineIdealsAtPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel GlobalTheory.IwaPlace Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.selfDualLattice_hyperbolic_line_ideals_at_place : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D) (ε : AE D) (hεε : ε * ε = ε) (hεc : cA D ε = ε) (hεI : ε ∈ intAt D (· = v)) (hε : ∀ a, a ∈ idAt D (· = v) ↔ ε * a = a), IsSDAt S v (latV S L (· = v)) → MonoAt d L L₀ v → ∃ α β : Fin ρ → AE D, (∀ i, α i ∈ idAt D (· = v)) ∧ (∀ i, β i ∈ idAt D (· = v)) ∧ (∀ i, α i * β i = ε) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jX i a ∈ latV S L (· = v) ↔ a * β i ∈ intAt D (· = v)) ∧ (∀ i, ∀ a ∈ idAt D (· = v), colMul d.jY i a ∈ latV S L (· = v) ↔ a * cA D (α i) ∈ intAt D (· = v)) := by
  first | exact @GlobalTheory.IwaIdeals.ideals_at_place | exact GlobalTheory.IwaIdeals.ideals_at_place | (intros; apply GlobalTheory.IwaIdeals.ideals_at_place <;> assumption)
end

