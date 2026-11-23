module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodProjectorSmallestSpaceForms
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0679
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0283
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0257
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0278
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0393
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RealMoveOfParts
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0491
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0475
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0482

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IotaProjectionAdjointBasisRowEigenvalue
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3

noncomputable section
namespace GlobalTheory.KapRec.Eigen

theorem exists_scaled_ext {K : Type} [Field K] (σ : K →+* ℂ) {n : ℕ} {W H : Type} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] (j : (Fin n → K) →ₛₗ[σ] W) (hli : LinearIndependent ℂ fun i => j (Pi.single i 1))
    (hsp : Submodule.span ℂ (Set.range fun i => j (Pi.single i 1)) = ⊤) (k : (Fin n → K) →ₛₗ[σ] H) {c : ℝ}
    (hc : ∀ x y, ⟪k x, k y⟫_ℂ = (c : ℂ) * ⟪j x, j y⟫_ℂ) :
    ∃ u : W →ₗ[ℂ] H, (∀ w, ‖u w‖ ^ 2 = c * ‖w‖ ^ 2) ∧ ∀ x, u (j x) = k x := by
  let b : Module.Basis (Fin n) ℂ W := Module.Basis.mk hli (le_of_eq hsp.symm)
  let u := b.constr ℂ (fun i => k (Pi.single i 1))
  have hb : ∀ i, b i = j (Pi.single i 1) := fun i => Module.Basis.mk_apply _ _ _
  have hu : ∀ i, u (b i) = k (Pi.single i 1) := fun i => Module.Basis.constr_basis _ _ _ _
  have hdec : ∀ x : Fin n → K, x = ∑ i, x i • Pi.single i 1 := fun x => by
    ext l
    simp [Finset.sum_apply, Pi.single_apply]
  have hj : ∀ x, j x = ∑ i, σ (x i) • b i := fun x => by
    conv_lhs => rw [hdec x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ, hb]
  have hk : ∀ x, k x = ∑ i, σ (x i) • k (Pi.single i 1) := fun x => by
    conv_lhs => rw [hdec x]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smulₛₗ]
  have hA : ∀ x, u (j x) = k x := fun x => by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hj, map_sum, hk]
    exact Finset.sum_congr rfl fun i _ => by rw [map_smul, hu]
  have hbas : ∀ i l, ⟪u (b i), u (b l)⟫_ℂ = (c : ℂ) * ⟪b i, b l⟫_ℂ := fun i l => by
    rw [hu, hu, hb, hb, hc]
  have key : ∀ z w, ⟪u z, u w⟫_ℂ = (c : ℂ) * ⟪z, w⟫_ℂ := fun z w => by
    rw [← b.sum_repr z, ← b.sum_repr w]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, sum_inner, inner_sum, inner_smul_left, inner_smul_right, hbas, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => by ring
  refine ⟨u, fun w => ?_, hA⟩
  have h := key w w
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  exact Complex.ofReal_injective (by push_cast; exact h)


set_option maxHeartbeats 2000000 in
theorem topMap_exists : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0), Pins R F cG → Holds R F → ∃ uA : D.what₂.Amb (Y.tup A3.A.μ0) →ₗ[ℂ] (R.HX A3.A.μ0).H, (∀ x, ‖uA x‖ ^ 2 = RealDat.nP F.lv2 true * ‖x‖ ^ 2) ∧ ∀ x, uA (Y.jA A3.A.μ0 x) = R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP hH
  have hFT := Y.formsA A3.A.μ0
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  let rf : (Fin (rDim D A3.A F.P1 F.ψ1 A3.A.μ0) → D.what₂.LL) →ₗ[D.what₂.LL] A3.A.fam.amb.FR A3.A.μ0 :=
    { toFun := rowForm A3.A F.P1 F.ψ1 A3.A.μ0
      map_add' := DatApi.rowForm_add A3.A F.P1 F.ψ1 A3.A.μ0
      map_smul' := DatApi.rowForm_smul A3.A F.P1 F.ψ1 A3.A.μ0 }
  refine exists_scaled_ext D.what₂.embLL (Y.jA A3.A.μ0) hFT.li hFT.span ((R.jX A3.A.μ0).comp rf) fun x y => ?_
  have h1 : (((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ = D.what₂.embLL (Formalism.DivisionValues.hform (rH D A3.A F.P1 F.ψ1 A3.A.μ0) x y) :=
    _root_.GlobalTheory.Mem.TopGram.topGram D G Pl0 T A3.A Ks R.toRealDat F.lv2 hP.char.base true A3.A.μ0 x y
  have alg : ∀ a : ℂ, a = ((RealDat.nP F.lv2 true : ℝ) : ℂ) * ((((RealDat.nP F.lv2 true)⁻¹ : ℝ) : ℂ) * a) := fun a => by
    rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ hpos.ne', Complex.ofReal_one, one_mul]
  rw [hFT.inner x y]
  refine Eq.trans ?_ (congrArg (fun z => ((RealDat.nP F.lv2 true : ℝ) : ℂ) * z) h1)
  exact alg ⟪R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 x), R.jX A3.A.μ0 (rowForm A3.A F.P1 F.ψ1 A3.A.μ0 y)⟫_ℂ

theorem iiStar_apply_eq {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) (μ : D.what₂.Tup) (y : EE) :
    (S.iotaQ μ ∘ₗ LinearMap.adjoint (S.iotaQ μ)) y = S.iota μ (S.eOp μ (LinearMap.adjoint (S.iota μ) y)) := by
  set w := LinearMap.adjoint (S.iotaQ μ) y with hw
  set z := LinearMap.adjoint (S.iota μ) y with hz
  have hQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), (w : S.Amb μ)⟫_ℂ = ⟪(q : S.Amb μ), z⟫_ℂ := by
    intro q
    rw [← Submodule.coe_inner, hw, hz, LinearMap.adjoint_inner_right, LinearMap.adjoint_inner_right]
    rfl
  have heV : ∀ x ∈ S.V0 μ, S.eOp μ x = x := by
    rintro _ ⟨a, rfl⟩
    exact congrArg (fun f : S.Amb μ →ₗ[ℂ] S.Amb μ => f a) (S.eOp_idem μ)
  set d := S.eOp μ z - (w : S.Amb μ) with hd
  have hdV : d ∈ S.V0 μ := sub_mem (LinearMap.mem_range_self _ _) w.2.1
  have hdQ : ∀ q : S.Qsp μ, ⟪(q : S.Amb μ), d⟫_ℂ = 0 := by
    intro q
    rw [hd, inner_sub_right, hQ, ← S.eOp_sa μ, heV _ q.2.1, sub_self]
  have hdU : d ∈ S.Usp μ := by
    set r := d - (S.Usp μ).starProjection d with hr0
    have hUV : S.Usp μ ≤ S.V0 μ := inf_le_left
    have hr : r ∈ S.Qsp μ :=
      ⟨sub_mem hdV (hUV (Submodule.starProjection_apply_mem _ _)), Submodule.sub_starProjection_mem_orthogonal d⟩
    have h1 : ⟪r, d⟫_ℂ = 0 := hdQ ⟨r, hr⟩
    have h2 : ⟪r, (S.Usp μ).starProjection d⟫_ℂ = 0 :=
      Submodule.inner_left_of_mem_orthogonal (Submodule.starProjection_apply_mem _ _) hr.2
    have h3 : ⟪r, r⟫_ℂ = 0 := by
      conv_lhs => rw [hr0]
      rw [inner_sub_right, ← hr0, h1, h2, sub_zero]
    have h4 : r = 0 := inner_self_eq_zero.1 h3
    rw [hr0, sub_eq_zero] at h4
    rw [h4]
    exact Submodule.starProjection_apply_mem _ _
  have hk : S.iota μ d = 0 := hdU.2
  rw [hd, map_sub, sub_eq_zero] at hk
  exact hk.symm

theorem transport_eig {D : D7} {EE : Type} [NormedAddCommGroup EE] [InnerProductSpace ℂ EE] [FiniteDimensional ℂ EE]
    (S : RowSide D EE) {E H : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (Θ : E →ₗ[ℂ] H) {μ μ' : D.what₂.Tup}
    (hμ : μ = μ') (uA : S.Amb μ →ₗ[ℂ] E) (uE : EE →ₗ[ℂ] H) {n : ℝ} (hn : 0 < n) (nA : ∀ x, ‖uA x‖ ^ 2 = n * ‖x‖ ^ 2)
    (nE : ∀ y, ‖uE y‖ ^ 2 = n * ‖y‖ ^ 2) (hι : ∀ x, uE (S.iota μ x) = Θ (uA x)) (y : EE)
    (hy : LinearMap.adjoint Θ (uE y) ∈ (S.V0 μ).map uA) {a : ℂ} (ha : Θ (LinearMap.adjoint Θ (uE y)) = a • uE y) :
    S.iota μ' (S.eOp μ' (LinearMap.adjoint (S.iota μ') y)) = a • y := by
  subst hμ
  rw [← iiStar_apply_eq]
  exact GlobalTheory.KappaLevels.iota_adjoint_transport Θ (S.iota μ) (S.V0 μ) uA uE hn nA nE (fun x _ => hι x) y hy ha


set_option maxHeartbeats 4000000 in
theorem eigen : (GlobalTheory.Published.DiscreteSeriesCover ∧ GlobalTheory.Published.HarishChandraModules ∧ GlobalTheory.Published.CasselmanWallach ∧ GlobalTheory.Published.HarishChandraFinite ∧ GlobalTheory.Published.CuspRapidDecay) → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → Lam3 Z → (∀ σ (i : Fin D.R.m), D.what₂.isot ((i : ℕ) + 1) (D.what₂.ft σ) ≠ ⊥) → ∀ σ, (RowSide.sharp D).iota D.what₂.mu0 ((RowSide.sharp D).eOp D.what₂.mu0 (LinearMap.adjoint ((RowSide.sharp D).iota D.what₂.mu0) (D.what₂.onb σ))) = ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • D.what₂.onb σ := by
  intro hCRD D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hL hI σ
  obtain ⟨uE, -, nE, hE⟩ := GlobalTheory.Adopt.levelRowsReading_embedding_goodRowsModel_with_norm D G Pl0 T A3.A Ks R.toRealDat F.lv2 Y.tupT Y.hm Y.hTop true D.what₂.EE
    (RowSide.sharp D) Y.Ish hP.char.base.models.HE Y.tied.sharp.ee
  obtain ⟨uA, nA, hA⟩ := topMap_exists D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH
  obtain ⟨p, hp, hl⟩ := GlobalTheory.T.basisRow_mem_definiteFamily_type_part hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hL hI uE hE σ
  have hup := GlobalTheory.T.adjoint_compositeLift_row_mem_span_goodRationalForms hCRD.2.2.2.2 D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH uE hE (D.what₂.onb σ)
  have hdt := (GlobalTheory.T.compositeIntertwiner_eq_thetaLift_goodProjector hCRD D G Pl0 I0 T A3 Ks R F cG X0 Y hP hH).1 A3.A.μ0
  have ha : R.Th A3.A.μ0 (LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ))) =
      ((R.kap * ∏ j ∈ Finset.Icc 1 D.R.m, D.what₂.lamP D.what₂.mu0 j (D.what₂.ft σ) : ℝ) : ℂ) • uE (D.what₂.onb σ) := by
    refine (hH.prim.thmB A3.A.μ0 p (uE (D.what₂.onb σ)) hp).trans ?_
    rw [hl]
  have hpos : (0 : ℝ) < RealDat.nP F.lv2 true := by
    unfold RealDat.nP
    exact_mod_cast Nat.card_pos
  have hFT := Y.formsA A3.A.μ0
  have hι : ∀ a, uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) a) = R.Th A3.A.μ0 (uA a) := by
    have key : uE ∘ₗ (RowSide.sharp D).iota (Y.tup A3.A.μ0) = R.Th A3.A.μ0 ∘ₗ uA := by
      refine LinearMap.ext_on_range hFT.span fun i => ?_
      show uE ((RowSide.sharp D).iota (Y.tup A3.A.μ0) (Y.jA A3.A.μ0 (Pi.single i 1))) =
        R.Th A3.A.μ0 (uA (Y.jA A3.A.μ0 (Pi.single i 1)))
      rw [← GlobalTheory.Mem.R3.DTheta.iota_sharp, hA]
      have h1 := hdt (Pi.single i 1)
      rw [hE] at h1
      exact hP.char.base.models.HE.1 (PiTensorProduct.lift.injective h1)
    exact fun a => LinearMap.congr_fun key a
  have hy : LinearMap.adjoint (R.Th A3.A.μ0) (uE (D.what₂.onb σ)) ∈
      ((RowSide.sharp D).V0 (Y.tup A3.A.μ0)).map uA := by
    refine (Submodule.span_le.2 ?_) hup
    rintro _ ⟨x, rfl⟩
    exact ⟨Y.jA A3.A.μ0 ((rE D A3.A F.P1 F.ψ1 A3.A.μ0).mulVec x), ⟨Y.jA A3.A.μ0 x, hFT.op_eq x⟩, hA _⟩
  exact transport_eig (RowSide.sharp D) (R.Th A3.A.μ0) Y.tup0 uA uE hpos nA nE hι (D.what₂.onb σ) hy ha

end GlobalTheory.KapRec.Eigen
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCoefficientFieldFiniteGroupEq
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.Ids

theorem coeffF_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {H H' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {l : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H} {l' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Level H'}
    {c : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l} {c' : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Coeff l'}
    (hH : H' = H) (hl : HEq l' l) (hc : HEq c' c) : c'.F = c.F := by
  subst hH
  obtain rfl := eq_of_heq hl
  obtain rfl := eq_of_heq hc
  rfl

theorem gc_equiv {B B' : Base} {px : PreX B.toPre} {px' : PreX B'.toPre} (h : Enl B B') (hp : HEq px' px) :
    ∃ γ : GlobalTheory.Mem.R3.Gc B px ≃* GlobalTheory.Mem.R3.Gc B' px', ∀ u, HEq (γ u) u := by
  obtain ⟨e, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e
  subst e
  cases hp
  exact ⟨MulEquiv.refl _, fun _ => HEq.rfl⟩

theorem dat_F_eq {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (h : Enl B B') (e : ExtN z z') : z'.core.Q.c.F = z.core.Q.c.F := by
  have hH := e.H
  have hl := e.l
  have hc := e.c
  clear e
  obtain ⟨e0, -⟩ := h
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at e0
  subst e0
  exact coeffF_eq (eq_of_heq hH) hl hc

theorem field_group_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∃ (eK : ↥(sideAt x g hg a).core.Q.c.F ≃+* ↥(sideAt x' g' hg' a').core.Q.c.F) (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ y, ((eK y : ↥(sideAt x' g' hg' a').core.Q.c.F) : ℂ) = (y : ℂ)) ∧ ∀ u, HEq (γ u) u := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a'
  have hc := l.extN.c
  have hH := l.extN.H
  have hl := l.extN.l
  show ∃ (eK : x.m.z.core.Q.c.F ≃+* x'.m.z.core.Q.c.F) (γ : GlobalTheory.Mem.R3.Gc B w.px ≃* GlobalTheory.Mem.R3.Gc B' w'.px), _
  obtain ⟨γ, hγ⟩ := gc_equiv l.enl l.px
  have hF : x'.m.z.core.Q.c.F = x.m.z.core.Q.c.F := dat_F_eq (z := datAt x g) (z' := datAt x' g') l.enl l.extN
  exact ⟨(IntermediateField.equivOfEq hF.symm).toRingEquiv, γ, fun y => rfl, hγ⟩

end GlobalTheory.HeightCounting.SerMove.Ids
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesCorrespondingFormsSameAdelicFunction
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Cx Formalism.IndefR.RecTie
open GlobalTheory.Mem.R3.Tr GlobalTheory.TwInputs.Move

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.ReadMove


set_option maxHeartbeats 4000000 in
theorem sameMap_of_heq {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt}
    (i : Fin (w.st Z).toD7.R.m) (i' : Fin (w'.st Z').toD7.R.m) (hi : (i : ℕ) = i')
    {S : (w.st Z).toD7.what₂.Tau → SPar} {S' : (w'.st Z').toD7.what₂.Tau → SPar}
    (M : Formalism.IndefR.Mult.DSModel (Wc (w.st Z).toD7 i) S) (M' : Formalism.IndefR.Mult.DSModel (Wc (w'.st Z').toD7 i') S')
    (a : HEq M'.H M.H) (b : HEq M'.nacg M.nacg) (c : HEq M'.ips M.ips) (d : HEq M'.σ M.σ) (l : HEq M'.lam M.lam) (e : HEq M'.ε M.ε)
    (g : HEq M'.fr M.fr) (X : HMod (Formalism.IndefR.Mult.MMap M)) (X' : HMod (Formalism.IndefR.Mult.MMap M')) (hX : HEq X' X)
    (u : X.H) (u' : X'.H) (hu : HEq u' u) : SameMap (X.e u) (X'.e u') := by
  obtain ⟨P', _⟩ := B'
  obtain ⟨P, _⟩ := B
  dsimp only at q
  subst q
  have e0 : i = i' := Fin.ext hi
  subst e0
  cases M
  cases M'
  dsimp only at a b c d l e g
  cases a; cases b; cases c; cases d; cases l; cases e; cases g
  have e' : X' = X := eq_of_heq hX
  subst e'
  have e'' : u' = u := eq_of_heq hu
  subst e''
  intro v v' hv y y' hy
  cases hy
  have : v' = v := funext fun τ => Subtype.ext (eq_of_heq (hv τ τ HEq.rfl)).symm
  subst this
  rfl


set_option maxHeartbeats 4000000 in
theorem read_same {B B' : Base} (q : B'.toPre = B.toPre) {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'}
    {w : ColW B f T} {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok}
    {Wt : Set B.places.Pl} {Wt' : Set B'.places.Pl} {z : Dat (w.st Z) w.I hX T Wt} {z' : Dat (w'.st Z') w'.I hX' T' Wt'}
    (hE : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (x : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (x' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hx : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → x' k' = φ (x k)) :
    ∀ (σ : (w.st Z).toD7.what₂.LL →+* ℂ) (σ' : (w'.st Z').toD7.what₂.LL →+* ℂ), σ = (w.st Z).toD7.what₂.embLL →
      σ' = (w'.st Z').toD7.what₂.embLL →
      SameMap ((z.R.HW j σ).e ((z.R.FW j).j σ x)) ((z'.R.HW j' σ').e ((z'.R.FW j').j σ' x')) := by
  rintro σ σ' rfl rfl
  obtain ⟨a, b, c, d, l, e, g, -, hW, -, -⟩ := hE.MW j j' hj
  exact sameMap_of_heq q j j' hj _ _ a b c d l e g _ _ hW _ _
    (GlobalTheory.Mem.R3.LiftRead.read_extN q hE j j' hj φ hφ x x' hx)

end GlobalTheory.HeightCounting.SerMove.ReadMove

namespace GlobalTheory.HeightCounting.SerMove


set_option maxHeartbeats 4000000 in
theorem reading_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → GlobalTheory.TwInputs.Move.SameMap (GlobalTheory.TwInputs.Move.evidence (sideAt x g hg a) j y) (GlobalTheory.TwInputs.Move.evidence (sideAt x' g' hg' a') j' y') := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj y y' hy
  exact ReadMove.read_same l.enl.1 l.extN j j' hj ι l.cp.embLL y y' hy _ _ (GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x g hg a))
    (GlobalTheory.TwInputs.Move.sign_at_base_place_eq_embedding (sideAt x' g' hg' a'))

end GlobalTheory.HeightCounting.SerMove

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesFiniteGroupsLevelsCorrespond
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

noncomputable section

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem eG_heq (B B' : Base) (h : B'.toPre = B.toPre) (px : PreX B.toPre) (px' : PreX B'.toPre) (hp : HEq px' px)
    (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E)) (hPg : HEq Pg' Pg)
    (eG : Gc B px ≃* Formalism.L2.DIV.G0 Pg B.R.r) (eG' : Gc B' px' ≃* Formalism.L2.DIV.G0 Pg' B'.R.r) (he : HEq eG' eG)
    (u : Gc B px) (u' : Gc B' px') (hu : HEq u' u) : HEq (eG u) (eG' u') := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h px px' hp Pg Pg' hPg eG eG' he u u' hu ⊢
  subst h
  cases hp
  cases hPg
  cases he
  cases hu
  rfl

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_heq (B B' : Base) (h : B'.toPre = B.toPre) (Pg : Finset (Formalism.L2.DIV.Pl B.host.E)) (Pg' : Finset (Formalism.L2.DIV.Pl B'.host.E))
    (hPg : HEq Pg' Pg) (Q Q' : Fin 2 → Type) (hQ : Q = Q') (pw : ∀ k, Q k → Formalism.L2.DIV.Pl B.host.E)
    (pw' : ∀ k, Q' k → Formalism.L2.DIV.Pl B'.host.E) (hpw : HEq pw pw')
    (c : Formalism.L2.DIV.G0 Pg B.R.r ≃* ∀ kv : (Σ k : Fin 2, Q k), GL (Fin B.R.r) (ZMod (B.host.g kv.1)))
    (c' : Formalism.L2.DIV.G0 Pg' B'.R.r ≃* ∀ kv : (Σ k : Fin 2, Q' k), GL (Fin B'.R.r) (ZMod (B'.host.g kv.1)))
    (hc : ∃ (plg : (Σ k : Fin 2, Q k) ≃ Pg) (iso : ∀ kv, ZMod (B.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg) : Formalism.L2.DIV.Pl B.host.E) = pw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c y kv))
    (hc' : ∃ (plg : (Σ k : Fin 2, Q' k) ≃ Pg') (iso : ∀ kv, ZMod (B'.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : Pg') : Formalism.L2.DIV.Pl B'.host.E) = pw' kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (B'.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (c' y kv)) :
    HEq c c' := by
  obtain ⟨P, r⟩ := B
  obtain ⟨P', r'⟩ := B'
  dsimp only at h Pg Pg' hPg pw pw' hpw c c' hc hc' ⊢
  subst h
  cases hPg
  subst hQ
  cases hpw
  apply heq_of_eq
  obtain ⟨p, i, h1, h2⟩ := hc
  obtain ⟨p', i', h1', h2'⟩ := hc'
  obtain rfl : p = p' := Equiv.ext fun kv => Subtype.ext ((h1 kv).trans (h1' kv).symm)
  refine MulEquiv.ext fun y => funext fun kv => ?_
  have h3 := (h2 y kv).symm.trans (h2' y kv)
  refine Units.ext (Matrix.ext fun a b => (i' kv).injective ?_)
  have h4 : (i kv) ((c y kv).1 a b) = (i' kv) ((c' y kv).1 a b) := congrArg (fun m : GL _ _ => m.1 a b) h3
  have h5 : (i kv) ((c y kv).1 a b) = (i' kv) ((c y kv).1 a b) :=
    RingHom.congr_fun (Subsingleton.elim (i kv).toRingHom (i' kv).toRingHom) _
  exact h5.symm.trans h4

end GlobalTheory.HeightCounting.SerMove.GrpsPf

namespace GlobalTheory.HeightCounting.SerMove.GrpsPf

theorem cG_read {X : Stages} {px : PreX X.B.toPre} {I : ColIn X.B px} {hX : X.B.fields.Ok} {T : TwDat X.B} {Wt : Set X.B.places.Pl}
    (z : Dat X I hX T Wt) :
    ∃ (plg : (Σ k : Fin 2, X.toD7.nd.PlG k) ≃ z.R.Pg) (iso : ∀ kv, ZMod (X.toD7.host.g kv.1) ≃+* Formalism.L2.DIV.kP (plg kv).1),
      (∀ kv, ((plg kv : z.R.Pg) : Formalism.L2.DIV.Pl X.toD7.host.E) = X.toD7.naut.plGw kv.1 kv.2) ∧
      ∀ y kv, y (plg kv) = Formalism.UG.bc (iso kv : ZMod (X.toD7.host.g kv.1) →+* Formalism.L2.DIV.kP (plg kv).1) (z.cG y kv) := by
  obtain ⟨plg, iso, h1, -, -, h4⟩ := z.pins.keep.grp
  refine ⟨plg, iso, h1, fun y kv => ?_⟩
  obtain ⟨u, rfl⟩ := z.R.eG.surjective y
  exact h4 u kv

theorem grps_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (γ : (sideAt x g hg a).Γ ≃* (sideAt x' g' hg' a').Γ), (∀ u, HEq (γ u) u) → Grps (sideAt x g hg a) (sideAt x' g' hg' a') ι γ := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' γ hγ
  refine ⟨fun u => ?_, ?_, fun u => ?_, fun u u' hu => ?_⟩
  · exact eG_heq B B' l.enl.1 w.px w'.px l.px x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg x.m.z.R.eG x'.m.z.R.eG l.extN.eG u (γ u) (hγ u)
  · exact cG_heq B B' l.enl.1 x.m.z.R.Pg x'.m.z.R.Pg l.extN.Pg (Dof x).nd.PlG (Dof x').nd.PlG (eq_of_heq l.gal.gal.PlG)
      (Dof x).naut.plGw (Dof x').naut.plGw l.gal.pl x.m.z.cG x'.m.z.cG (cG_read x.m.z) (cG_read x'.m.z)
  · exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u (γ u) (hγ u)).1.symm
  · have h : HEq (u' : (sideAt x' g' hg' a').Γ) (u : (sideAt x g hg a).Γ) := hu ▸ hγ u
    exact (GlobalTheory.Mem.R3.LevBC.lev_bc B B' l.enl.1 w.px w'.px l.px w.I w'.I w.ok w'.ok ι l.cp.embLL u.1 u'.1 h).2 u.2 u'.2

end GlobalTheory.HeightCounting.SerMove.GrpsPf

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinkedStatesSupLatticeMemIffCoordinateImage
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000
open GlobalTheory.HeightCounting.SerMove

namespace GlobalTheory.HeightCounting.SerMove.MKLink
open GlobalTheory.Mem.R3.MKExt Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor


set_option maxHeartbeats 4000000 in
theorem mk_iff_of_extN {B B' : Base} {f : Fr B.toPre} {f' : Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T}
    {w' : ColW B' f' T'} {Z : w.Lt} {Z' : w'.Lt} {hX : B.fields.Ok} {hX' : B'.fields.Ok} {Wt : Set B.places.Pl}
    {Wt' : Set B'.places.Pl} (z : Dat (w.st Z) w.I hX T Wt) (z' : Dat (w'.st Z') w'.I hX' T' Wt')
    (hB : B'.toPre = B.toPre) (hN : ExtN z z') (j : Fin (w.st Z).toD7.R.m) (j' : Fin (w'.st Z').toD7.R.m) (hj : (j : ℕ) = j')
    (φ : (w.st Z).toD7.what₂.LL →+* (w'.st Z').toD7.what₂.LL)
    (hφ : ∀ x, (w'.st Z').toD7.what₂.embLL (φ x) = (w.st Z).toD7.what₂.embLL x)
    (y : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) (y' : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL)
    (hyy : ∀ (k : Fin (z.R.nW j)) (k' : Fin (z'.R.nW j')), (k : ℕ) = k' → y' k' = φ (y k))
    (hy : y ∈ (z.R.FW j).WK) : y ∈ (z.R.FW j).MK ↔ y' ∈ (z'.R.FW j').MK := by
  cases B with | mk P => ?_
  cases B' with | mk P' => ?_
  dsimp only at hB
  subst hB
  have hH : z'.core.Q.H = z.core.Q.H := eq_of_heq hN.H
  have hκ := hN.κ j j' hj
  have ha : wtA (z'.geo.κ j') = wtA (z.geo.κ j) := by
    funext x
    unfold wtA
    refine Finset.sum_congr rfl fun t _ => ?_
    have e1 : ext0 ((z'.geo.κ j').aP t) = ext0 ((z.geo.κ j).aP t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).1) hj.symm hκ.1 t
    have e2 : ext0 ((z'.geo.κ j').aM t) = ext0 ((z.geo.κ j).aM t) :=
      extendByZero_eq_of_heq_families (fun i => ((w.st Z).toD7.R.sigW (i + 1)).2) hj.symm hκ.2.1 t
    rw [e1, e2]
    rfl
  have hj1 : (j' : ℕ) + 1 = (j : ℕ) + 1 := by rw [hj]
  have hn : z'.R.nW j' = z.R.nW j :=
    (congrFun (eq_of_heq hN.nW) j').trans (congrArg z.R.nW (Fin.ext hj.symm))
  have hinj : Function.Injective (w'.st Z').toD7.what₂.embLL := RingHom.injective _
  obtain ⟨g, he⟩ : ∃ g, z.geo.fw.e j g = ⟨y, hy⟩ := ⟨_, LinearEquiv.apply_symm_apply _ _⟩
  obtain ⟨g', hgg, hP⟩ := cusp_match' hH hN.Dw hN.l hN.Xo hN.c hN.U hj1 ha hκ.2.2 g
  have hx : ((z.geo.fw.e j g : (z.R.FW j).WK) : Fin (z.R.nW j) → (w.st Z).toD7.what₂.LL) = y :=
    congrArg Subtype.val he
  have hx' : y' = ((z'.geo.fw.e j' g' : (z'.R.FW j').WK) : Fin (z'.R.nW j') → (w'.st Z').toD7.what₂.LL) := by
    funext k'
    have hk : ((Fin.cast hn k' : Fin (z.R.nW j)) : ℕ) = k' := rfl
    have h3 := hN.forms j j' hj g g' hgg (Fin.cast hn k') k' hk
    have h4 := hyy (Fin.cast hn k') k' hk
    apply hinj
    rw [h4]
    exact (hφ _).trans ((congrArg (fun v => (w.st Z).toD7.what₂.embLL (v (Fin.cast hn k'))) hx).symm.trans h3.symm)
  subst hx'
  subst hx
  constructor
  · rintro ⟨_, h2⟩
    exact ⟨(z'.geo.fw.e j' g').2, (nrm_le_one_iff z'.geo.fw j' g').2 (hP.2 ((nrm_le_one_iff z.geo.fw j g).1 h2))⟩
  · rintro ⟨_, h2⟩
    exact ⟨(z.geo.fw.e j g).2, (nrm_le_one_iff z.geo.fw j g).2 (hP.1 ((nrm_le_one_iff z'.geo.fw j' g').1 h2))⟩

end GlobalTheory.HeightCounting.SerMove.MKLink

namespace GlobalTheory.HeightCounting.SerMove
open GlobalTheory.Mem.R3.Tr


set_option maxHeartbeats 4000000 in
theorem mk_iff_of_link : ∀ {K : Ctx} {B B' : Base} {f : Top.Fr B.toPre} {f' : Top.Fr B'.toPre} {T : TwDat B} {T' : TwDat B'} {w : ColW B f T} {w' : ColW B' f' T'} {P : Pre2 K w} {P' : Pre2 K w'} (x : St P) (x' : St P') (ι : (Dof x).what₂.LL →+* (Dof x').what₂.LL) (e : ↥(Dof x').LL0 ≃+* ↥(Dof x).LL0) (g : Geo x) (g' : Geo x'), Link x x' ι e g g' → ∀ (hg : GlobalTheory.RealGeo.InGeo g) (hg' : GlobalTheory.RealGeo.InGeo g') (a : BigHost (Dof x)) (a' : BigHost (Dof x')), ∀ (j : Fin (Dof x).R.m) (j' : Fin (Dof x').R.m), (j : ℕ) = j' → ∀ (y : Fin ((sideAt x g hg a).R.nW j) → (Dof x).what₂.LL) (y' : Fin ((sideAt x' g' hg' a').R.nW j') → (Dof x').what₂.LL), (∀ (k : Fin ((sideAt x g hg a).R.nW j)) (k' : Fin ((sideAt x' g' hg' a').R.nW j')), (k : ℕ) = k' → y' k' = ι (y k)) → y ∈ ((sideAt x g hg a).R.FW j).WK → (y ∈ ((sideAt x g hg a).R.FW j).MK ↔ y' ∈ ((sideAt x' g' hg' a').R.FW j').MK) := by
  intro K B B' f f' T T' w w' P P' x x' ι e g g' l hg hg' a a' j j' hj y y' hyy hy
  exact MKLink.mk_iff_of_extN (datAt x g) (datAt x' g') l.enl.1 l.extN j j' hj ι (fun t => l.cp.embLL t) y y' hyy hy

end GlobalTheory.HeightCounting.SerMove
end

