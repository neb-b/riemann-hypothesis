module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0540
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.WeilRepresentationUnitaryPair
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DsExistsOfDiscreteSeriesExists
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0530
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0555
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0096
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPelUnifPsiCoord
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0084
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0133
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingIntegralClosure
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LbIsoDetAffDetOm
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.LocM GlobalTheory.LieMet GlobalTheory.GrCl GlobalTheory.Reg
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.FlagMod
open GlobalTheory.Twist (resM resM_resM)

namespace GlobalTheory.HodgeCech

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}

section Dual

variable {X : Scheme.{0}} (t : SAB H X) {S : Type} [CommRing S] {g : ℕ}

theorem tanLin_bijective (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Function.Bijective (tanLin t h c.e) := by
  refine ⟨tanLin_injective t h c.e le_rfl h (c.isFrame.res le_rfl), fun a => ?_⟩
  obtain ⟨v, ⟨hv, e⟩, -⟩ := GlobalTheory.TanFibre.existsUnique_tanEv E H X t S x c.U h g c.e c.isFrame a
  exact ⟨tanOf hv, funext e⟩

def dualBasis (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) :
    Module.Basis (Fin g) S (TanM x t.G) :=
  Module.Basis.ofEquivFun (LinearEquiv.ofBijective _ (tanLin_bijective t c x h))

theorem dualBasis_repr (c : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (v : TanM x t.G)
    (i : Fin g) : (dualBasis t c x h).repr v i = tanLin t h c.e v i := rfl

theorem ev_detUnit (c c' : VB.Chart (LieVB.omega t.G) g) (x : Sp S ⟶ X) (h : ⊤ ≤ x ⁻¹ᵁ c.U) (h' : ⊤ ≤ x ⁻¹ᵁ c'.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (c.U ⊓ c'.U)) :
    ev x _ hh (c.isFrame.detUnit c'.isFrame inf_le_left inf_le_right).val =
      rdet ((dualBasis t c' x h').toMatrix (dualBasis t c x h)) := by
  show ev x _ hh ((c.isFrame.basis inf_le_left).det (c'.isFrame.basis inf_le_right)) = _
  rw [Module.Basis.det_apply, RingHom.map_det, rdet_self, ← Matrix.det_transpose]
  congr 1
  ext l i
  rw [Module.Basis.toMatrix_apply, dualBasis_repr, tanLin_apply, ← tanEv_resM t _ hh inf_le_right,
    sum_frMat c'.isFrame c.isFrame inf_le_right inf_le_left, tanEv_sum_smul]
  simp only [tanEv_resM t _ hh inf_le_left]
  have e : ∀ k, tanEv t (isTan_tv (dualBasis t c x h i)) h (c.e k) = if i = k then 1 else 0 := fun k => by
    rw [← tanLin_apply, ← dualBasis_repr, Module.Basis.repr_self, Finsupp.single_apply]
  simp only [e, mul_ite, _root_.mul_one, MulZeroClass.mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rfl

def detAff (t : SAB H X) (g : ℕ) : LB X :=
  ⟨{c : VB.Chart (LieVB.omega t.G) g // IsAffineOpen c.U}, fun c => c.1.U,
    fun c c' => c.1.isFrame.detUnit c'.1.isFrame inf_le_left inf_le_right⟩

theorem isLB_detAff (h : VB.IsVB (LieVB.omega t.G) g) : (detAff t g).IsLB := by
  refine ⟨top_le_iff.1 fun x _ => ?_, fun c => h.isLB_det.g_self c.1, fun c c' c'' => h.isLB_det.cocycle c.1 c'.1 c''.1⟩
  obtain ⟨U, e, hx, he⟩ := h x
  obtain ⟨V, hV, hxV, hVU⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := U) (x := x) hx
  exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨⟨V, _, he.res hVU⟩, hV⟩, hxV⟩

theorem lbIso_detAff (h : VB.IsVB (LieVB.omega t.G) g) : LBIso (detAff t g) (VB.det (LieVB.omega t.G) g) :=
  (VB.lbIso_det_of_frames (isLB_detAff t h) (fun c => c.1.e) (fun c => c.1.isFrame) fun _ _ => rfl).2

end Dual

variable {D : Datum H} {l : Level H} {Xo : Moduli D l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  (Y : Model Xo c β) {g : ℕ} {S : Type} [CommRing S]

theorem isAffineOpen_inf' {U V : Y.X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V) : IsAffineOpen (U ⊓ V) := by
  have := projProper _ _ _ Y.proj
  have : Y.X.IsSeparated := ⟨by
    rw [← terminal.comp_from Y.s]
    infer_instance⟩
  exact hU.inf hV

variable {Y}

def pairDet (M : MChart Y) (a : (detAff Y.t g).ι) : Γ(Y.X, M.U ⊓ a.1.U)ˣ :=
  (isUnit_rdet_toMatrix (dualBasis Y.t a.1 (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_right))
    (lieBasis M (tau (isAffineOpen_inf' Y M.hU a.2)) (tau_le _ inf_le_left))).unit

theorem ev_pairDet (M : MChart Y) (a : (detAff Y.t g).ι) (x : Sp S ⟶ Y.X) (h : ⊤ ≤ x ⁻¹ᵁ M.U) (h' : ⊤ ≤ x ⁻¹ᵁ a.1.U)
    (hh : ⊤ ≤ x ⁻¹ᵁ (M.U ⊓ a.1.U)) :
    ev x _ hh (pairDet M a).val = rdet ((dualBasis Y.t a.1 x h').toMatrix (lieBasis M x h)) := by
  have e : spMap (ev x _ hh) ≫ tau (isAffineOpen_inf' Y M.hU a.2) = x := spMap_ev x _ hh
  refine (map_rdet _ _).trans (congrArg rdet ?_)
  ext i j
  rw [Matrix.map_apply, Module.Basis.toMatrix_apply, Module.Basis.toMatrix_apply, dualBasis_repr, dualBasis_repr,
    ← tanPull_lieBasis M _ e (tau_le _ inf_le_left) h, tanLin_tanPull Y.t _ e (tau_le _ inf_le_right) h']
  rfl

variable (Y)

theorem lbIso_detAff_detOm : LBIso (detAff Y.t g) (detOm Y) := by
  refine ⟨⟨fun p => pairDet p.1 p.2⟩, fun p q => ?_⟩
  refine Eq.trans ?_ (mul_right_comm _ _ _)
  refine eq_mul_inv_of_mul_eq ?_
  refine Eq.trans ?_ (congrArg (· * _) (map_inv _ (detChg p.1 q.1)).symm)
  refine eq_inv_mul_of_mul_eq (Units.ext (ext_ev fun S _ z hz => ?_))
  have hp := le_preimage_mono inf_le_left hz
  have hq := le_preimage_mono inf_le_right hz
  have hp1 : ⊤ ≤ z ⁻¹ᵁ (p.1 : MChart Y).U := le_preimage_mono inf_le_left hp
  have hq1 : ⊤ ≤ z ⁻¹ᵁ (q.1 : MChart Y).U := le_preimage_mono inf_le_left hq
  have hp2 : ⊤ ≤ z ⁻¹ᵁ p.2.1.U := le_preimage_mono inf_le_right hp
  have hq2 : ⊤ ≤ z ⁻¹ᵁ q.2.1.U := le_preimage_mono inf_le_right hq
  refine (map_mul (ev z _ hz) _ _).trans ?_
  refine (congrArg₂ (· * ·) ((ev_res z _ hz (le_preimage_inf hp1 hq1) _).trans (ev_detChg _ _ z hp1 hq1 _))
    ((map_mul (ev z _ hz) _ _).trans (congrArg₂ (· * ·) ((ev_res z _ hz hp _).trans (ev_pairDet _ _ z hp1 hp2 hp))
      ((ev_res z _ hz (le_preimage_inf hp2 hq2) _).trans (ev_detUnit Y.t _ _ z hp2 hq2 _))))).trans
    (Eq.trans ?_ ((ev_res z _ hz hq _).trans (ev_pairDet _ _ z hq1 hq2 hq)).symm)
  rw [_root_.mul_comm, _root_.mul_comm (rdet _) (rdet _), rdet_toMatrix_mul, rdet_toMatrix_mul]

theorem lbIso_detOm_det (hO : (detOm Y).IsLB) (h : VB.IsVB (LieVB.omega Y.t.G) g) :
    LBIso (detOm Y) (VB.det (LieVB.omega Y.t.G) g) :=
  (lbIso_detAff_detOm Y).symm.trans hO (isLB_detAff Y.t h) h.isLB_det (lbIso_detAff Y.t h)

end GlobalTheory.HodgeCech
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftScalarEqLabelScalar
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open Formalism.IndefR.RecTie Formalism.IndefR.Lev Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3
open Classical
open GlobalTheory.Mem.R3.HasLabelling

namespace GlobalTheory.Mem.R3.LamLab

theorem adj_eig {X Y : Type} [NormedAddCommGroup X] [InnerProductSpace ℂ X] [FiniteDimensional ℂ X]
    [NormedAddCommGroup Y] [InnerProductSpace ℂ Y] [FiniteDimensional ℂ Y] (θ : X →ₗ[ℂ] Y) (c : ℝ) (x₀ : X)
    (h : ∀ x', ⟪θ x₀, θ x'⟫_ℂ = (c : ℂ) * ⟪x₀, x'⟫_ℂ) : θ (LinearMap.adjoint θ (θ x₀)) = (c : ℂ) • θ x₀ := by
  have ha : LinearMap.adjoint θ (θ x₀) = (c : ℂ) • x₀ := by
    refine ext_inner_right ℂ fun x' => ?_
    rw [LinearMap.adjoint_inner_left, h, inner_smul_left, Complex.conj_ofReal]
  rw [ha, map_smul]

theorem eigenvalue_eq_of_label : GlobalTheory.Published.WeilRepresentationUnitaryPair → GlobalTheory.Published.DiscreteSeriesExists → GlobalTheory.Published.HarishChandraFinite → GlobalTheory.Published.CuspRapidDecay → ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 T : Type) (A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) (X0 : BaseLevelRowSide D) (Y : Read (A3 := A3) R.toRealDat F.lv2 X0) (Z : ReadL R F X0 Y), Pins R F cG → Holds R F → HostHyp D → ∀ (σ : D.what₂.FT) (p : A3.fam3.base3.Ix) (i : Fin D.R.m) (t : T), HasLab Y σ p → (Y.tup t = D.what₂.mu0 ∨ ∃ w, Y.tup t = D.what₂.muAt w) → D.what₂.isot ((i : ℕ) + 1) σ ≠ ⊥ → D.what₂.lamP (Y.tup t) ((i : ℕ) + 1) σ = (s0Of R F).lam i t p A3.fam3.base3.v0 := by
  intro h1 h2 h3 h4 D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y Z hP hH hD σ p i t hL hU hne
  refine Y.tied.lift.lamP (Y.tup t) hU i σ _ hne fun y hy => ?_
  set θ := D.what₂.thetaP (Y.tup t) ((i : ℕ) + 1) with hθ
  obtain ⟨x, rfl⟩ := GlobalTheory.T.liftThetaMap_surjective_onto_cuspForms_usedTuple h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t hU y
  set K := (LinearMap.ker θ)ᗮ
  have hx0 : x - K.starProjection x ∈ LinearMap.ker θ := by
    have := K.sub_starProjection_mem_orthogonal x
    rwa [Submodule.orthogonal_orthogonal] at this
  have he : θ (K.starProjection x) = θ x := by
    rw [LinearMap.mem_ker, map_sub, sub_eq_zero] at hx0; exact hx0.symm
  have hW : Y.mj.eW i (θ (K.starProjection x)) ∈ R.Wp3 i p := by
    rw [he]; exact hL.1 i ⟨θ x, hy, rfl⟩
  have key := GlobalTheory.T.liftThetaMap_inner_eq_lambda_labelPart_baseLevel h1 h2 h3 h4 D G Pl0 I0 T A3 Ks R F cG X0 Y Z hP hH hD i t p hU (K.starProjection x)
    (K.starProjection_apply_mem x) hW
  have := adj_eig θ (R.lam3 i t p A3.A.v0) _ key
  rw [he] at this
  exact this

end GlobalTheory.Mem.R3.LamLab
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LineBundleIsoOfGenericIsoNormalLocalBase
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

theorem GlobalTheory.lbIso_of_generic_normal_local : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsNoetherianRing R → IsIntegrallyClosed R → ∀ (H : Scheme.{0}) (p : H ⟶ Sp R) (e : Sp R ⟶ H), Smooth p → QuasiCompact p → GeometricallyIntegral p → e ≫ p = 𝟙 _ → ∀ L M : LB H, L.IsLB → M.IsLB → LBIso (L.pull (pullback.fst p (jK R))) (M.pull (pullback.fst p (jK R))) → LBIso L M := by
  intro R _ _ _ hN hI H p e hs _ hg he L M hL hM h
  haveI : IsNoetherianRing R := hN
  haveI : IsIntegrallyClosed R := hI
  have hD := LB.isLB_div hM hL
  have h₁ : IsPreimmersion (jK R) := IsPreimmersion.of_isLocalization (nonZeroDivisors R)
  have h₂ : Flat (jK R) := by
    rw [HasRingHomProperty.Spec_iff (P := @Flat)]
    exact RingHom.flat_algebraMap_iff.2 (IsLocalization.flat _ (nonZeroDivisors R))
  obtain ⟨t, ht⟩ := GenericExtend.exists_isGen_of_densePart (Sp R) _ (jK R) (ZJ.isNormalScheme_sp R) h₁ h₂
    DVR.isDominant_jK inferInstance (Over.mk p) e (LB.div M L) he hs hg hD
    (DVR.exists_gen_of_isLB_local _ (LB.isLB_pull hD _)) ((IsoExtend.lbIso_pull_iff_gen L M _).1 h)
  exact ⟨t, ht⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearOnIsFineOfLinearOnPolarisationBaseFunction
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.LinOn

theorem finrank_int_eq' (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X] :
    Module.finrank ℤ X = Module.finrank ℚ E * Module.finrank (𝓞 E) X := by
  rw [← (TensorProduct.isBaseChange ℤ X ℚ).finrank_eq, ← (TensorProduct.isBaseChange (𝓞 E) X E).finrank_eq,
    Module.finrank_mul_finrank, (Algebra.IsPushout.cancelBaseChange ℤ ℚ (𝓞 E) E X).finrank_eq]

variable {X : Type} [AddCommGroup X] {m : ℕ}

section Pol

variable [Module.Finite ℤ X]

theorem sum_le_evalR {φ : InvFun ℤ} (h : IsPolFanOn (id : ℤ → ℤ) φ X) {γ : Fin m → LinearMap.BilinForm ℤ X}
    (h1 : ∀ i, γ i ∈ balForms (id : ℤ → ℤ) X) (h2 : ∀ i y, 0 ≤ γ i y y) {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * φ.evalZ (γ i) ≤ evalR φ (∑ i, c i • toReal (γ i)) := by
  classical
  have hmem : ∀ d : Fin m → ℝ, (∀ i, 0 ≤ d i) → ∑ i, d i • toReal (γ i) ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) :=
    fun d hd => GlobalTheory.PolFan.ConeSub.sum_smul_toReal_mem_psdCone ℤ id X m γ d h1 h2 hd
  have hsub : ∀ s : Finset (Fin m), ∑ i ∈ s, c i • toReal (γ i) ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) := fun s => by
    have := hmem (fun i => if i ∈ s then c i else 0) fun i => by
      split_ifs
      · exact hc i
      · exact le_rfl
    simpa [ite_smul, Finset.sum_ite_mem] using this
  have hone : ∀ a, toReal (γ a) ∈ psdCone (bar := (id : ℤ → ℤ)) (X := X) := fun a => by
    have := hmem (Pi.single a 1) fun i => by
      by_cases e : i = a
      · subst e; simp
      · simp [Pi.single_eq_of_ne e]
    simpa [Pi.single_apply, ite_smul] using this
  have key : ∀ s : Finset (Fin m), ∑ i ∈ s, c i * φ.evalZ (γ i) ≤ evalR φ (∑ i ∈ s, c i • toReal (γ i)) := fun s => by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      refine le_trans ?_ (h.superadd _ (smul_mem_psdCone (hone a) (hc a)) _ (hsub s))
      rw [h.homog _ (hone a) _ (hc a), evalR_toReal]
      linarith
  simpa using key Finset.univ

end Pol

section Mean

variable (M : ℕ) {k : ℕ} {s : (Fin k → ℤ) →ₗ[ℤ] X}

abbrev rd (s : (Fin k → ℤ) →ₗ[ℤ] X) (B : X → X → ℝ) : (Fin k → ℤ) → (Fin k → ℤ) → ℝ := fun a b => B (s a) (s b)

theorem fineMean_eval [Module.Finite ℤ X] (hs : Function.Surjective s) (B : X → X → ℝ) :
    (fineMean M).eval X B = (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s B) y - B 0 0 := by
  rw [InvFun.eval_eq _ hs]
  simp [fineMean]

theorem classMin_le {β : LinearMap.BilinForm ℤ X} (h : ∀ y, 0 ≤ β y y) (s : (Fin k → ℤ) →ₗ[ℤ] X) (a : Fin k → ℤ) :
    classMin M (rd s fun a b => (β a b : ℝ)) (redV M a) ≤ (β (s a) (s a) : ℝ) := by
  refine csInf_le ⟨0, ?_⟩ ⟨a, rfl, rfl⟩
  rintro x ⟨a, -, rfl⟩
  show (0 : ℝ) ≤ ((β (s a) (s a) : ℤ) : ℝ)
  exact_mod_cast h (s a)

theorem sum_classMin_le {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y) (s : (Fin k → ℤ) →ₗ[ℤ] X)
    {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) (y : Fin k → ZMod (M + 1)) :
    ∑ i, c i * classMin M (rd s fun a b => (γ i a b : ℝ)) y ≤
      classMin M (rd s fun a b => ∑ i, c i * (γ i a b : ℝ)) y := by
  obtain ⟨a₀, ha₀⟩ := redV_surjective M k y
  refine le_csInf ⟨_, a₀, ha₀, rfl⟩ ?_
  rintro x ⟨a, rfl, rfl⟩
  exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (classMin_le M (h i) s a) (hc i)

theorem sum_mul_mean {Y : Type} [Fintype Y] (K : ℝ) (c : Fin m → ℝ) (f : Fin m → Y → ℝ) :
    ∑ i, c i * (K * ∑ y, f i y) = K * ∑ y, ∑ i, c i * f i y := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun i _ => by ring

theorem mean_pos : (0 : ℝ) < (((M : ℝ) + 1) ^ k)⁻¹ := by positivity

theorem fineMean_evalZ [Module.Finite ℤ X] (hs : Function.Surjective s) (β : LinearMap.BilinForm ℤ X) :
    (fineMean M).evalZ β = (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s fun a b => (β a b : ℝ)) y := by
  rw [InvFun.evalZ, fineMean_eval M hs]
  simp

theorem fineMean_evalSum [Module.Finite ℤ X] (hs : Function.Surjective s) (γ : Fin m → LinearMap.BilinForm ℤ X)
    (c : Fin m → ℝ) :
    (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) =
      (((M : ℝ) + 1) ^ k)⁻¹ * ∑ y, classMin M (rd s fun a b => ∑ i, c i * (γ i a b : ℝ)) y := by
  rw [fineMean_eval M hs]
  simp

theorem sum_fineMean_le [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    {c : Fin m → ℝ} (hc : ∀ i, 0 ≤ c i) :
    ∑ i, c i * (fineMean M).evalZ (γ i) ≤ (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  rw [fineMean_evalSum M hs]
  simp only [fineMean_evalZ M hs]
  rw [sum_mul_mean]
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun y _ => sum_classMin_le M h s hc y) (mean_pos M).le

theorem classMin_sum_eq [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    (hs : Function.Surjective s)
    (he : (fineMean M).eval X (fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) = ∑ i, (1 : ℝ) * (fineMean M).evalZ (γ i))
    (y : Fin k → ZMod (M + 1)) :
    classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) y =
      ∑ i, (1 : ℝ) * classMin M (rd s fun a b => (γ i a b : ℝ)) y := by
  rw [fineMean_evalSum M hs] at he
  simp only [fineMean_evalZ M hs] at he
  rw [sum_mul_mean] at he
  have e3 := mul_left_cancel₀ (mean_pos (k := k) M).ne' he
  have := (Finset.sum_eq_sum_iff_of_le (s := Finset.univ)
    (f := fun y => ∑ i, (1 : ℝ) * classMin M (rd s fun a b => (γ i a b : ℝ)) y)
    (g := fun y => classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) y)
    fun y _ => sum_classMin_le M h s (fun _ => zero_le_one) y).1 e3.symm y (Finset.mem_univ y)
  exact this.symm

theorem exists_classMin_attained {β : LinearMap.BilinForm ℤ X} (h : ∀ y, 0 ≤ β y y) (s : (Fin k → ℤ) →ₗ[ℤ] X)
    (a₀ : Fin k → ℤ) :
    ∃ α, redV M α = redV M a₀ ∧ ∀ a, redV M a = redV M a₀ → β (s α) (s α) ≤ β (s a) (s a) := by
  obtain ⟨⟨α, hα⟩, -, h0⟩ := (measure fun a : {a : Fin k → ℤ // redV M a = redV M a₀} =>
    (β (s a.1) (s a.1)).toNat).wf.has_min Set.univ ⟨⟨a₀, rfl⟩, trivial⟩
  refine ⟨α, hα, fun a ha => ?_⟩
  have h1 : ¬ (β (s a) (s a)).toNat < (β (s α) (s α)).toNat := h0 ⟨a, ha⟩ trivial
  have := h (s a)
  have := h (s α)
  omega

theorem isFine_of_additive [Module.Finite ℤ X] {γ : Fin m → LinearMap.BilinForm ℤ X} (h : ∀ i y, 0 ≤ γ i y y)
    (he : (fineMean M).eval X (fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) = ∑ i, (1 : ℝ) * (fineMean M).evalZ (γ i)) :
    IsFine (M + 1) γ := by
  obtain ⟨k, s, hs⟩ := Module.Finite.exists_fin' ℤ X
  intro y
  obtain ⟨a₀, rfl⟩ := hs y
  let σ : LinearMap.BilinForm ℤ X := ∑ i, γ i
  have hσa : ∀ a b, σ a b = ∑ i, γ i a b := fun a b => by simp [σ, LinearMap.sum_apply]
  have hσ : ∀ y, 0 ≤ σ y y := fun y => by
    rw [hσa]; exact Finset.sum_nonneg fun i _ => h i y
  obtain ⟨α, hα, hmin⟩ := exists_classMin_attained M hσ s a₀
  obtain ⟨d, hd⟩ := exists_eq_add_of_redV_eq hα
  have hcm := classMin_sum_eq M h hs he (redV M a₀)

  have hval : classMin M (rd s fun a b => ∑ i, (1 : ℝ) * (γ i a b : ℝ)) (redV M a₀) = ((σ (s α) (s α) : ℤ) : ℝ) := by
    refine IsLeast.csInf_eq ⟨⟨α, hα, ?_⟩, ?_⟩
    · simp [rd, hσa]
    · rintro x ⟨a, ha, rfl⟩
      have := hmin a ha
      have h2 : ((σ (s α) (s α) : ℤ) : ℝ) ≤ ((σ (s a) (s a) : ℤ) : ℝ) := by exact_mod_cast this
      simpa [rd, hσa] using h2
  have hle : ∀ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) ≤ (γ i (s α) (s α) : ℝ) := fun i => by
    rw [← hα]; exact classMin_le M (h i) s α
  have hsum : ∑ i, classMin M (rd s fun a b => (γ i a b : ℝ)) (redV M a₀) = ∑ i, (γ i (s α) (s α) : ℝ) := by
    rw [hval] at hcm
    simp only [one_mul] at hcm
    rw [← hcm, hσa]
    push_cast
    rfl
  have heq := (Finset.sum_eq_sum_iff_of_le fun i _ => hle i).1 hsum
  refine ⟨s d, fun i μ => ?_⟩
  obtain ⟨e, rfl⟩ := hs μ
  have hn : ∀ x : X, (M + 1) • x = ((M : ℤ) + 1) • x := fun x => by
    rw [← natCast_zsmul]; push_cast; rfl
  have e1 : s a₀ + (M + 1) • s d = s α := by
    rw [hd, map_add (f := _), map_smul, hn]
  have e2 : s a₀ + (M + 1) • s e = s (a₀ + ((M : ℤ) + 1) • e) := by
    rw [map_add (f := _), map_smul, hn]
  rw [e1, e2]
  have h3 := classMin_le M (h i) s (a₀ + ((M : ℤ) + 1) • e)
  rw [redV_add_smul, heq i (Finset.mem_univ i)] at h3
  exact_mod_cast h3

end Mean

end GlobalTheory.PolFan.LinOn


open GlobalTheory.PolFan.LinOn in
theorem GlobalTheory.PolFan.linearOn_and_isFine_of_linearOn_baseFun (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E)
    (g q D : ℕ) (φs : InvFun ℤ) (𝓜 : Finset ℕ) (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X]
    [Module.Projective (𝓞 E) X] (hD : 0 < D) (hφ : IsPolFan (id : ℤ → ℤ) g φs) (hq : Module.finrank ℚ E * q ≤ g)
    (hX : Module.finrank (𝓞 E) X ≤ q) (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (hb : ∀ i, γ i ∈ balForms H.bar X)
    (hp : ∀ i y, 0 ≤ γ i y y) (hl : (baseFun (𝓞 E) D φs 𝓜).LinearOn γ) :
    (restr (𝓞 E) φs).LinearOn γ ∧ ∀ M ∈ 𝓜, IsFine (M + 1) γ := by
  haveI : Module.Finite ℤ X := Module.Finite.trans (𝓞 E) X
  haveI : Module.Projective ℤ X := by
    obtain ⟨n, r, hr⟩ := Module.Finite.exists_fin' (𝓞 E) X
    obtain ⟨h, hh⟩ := Module.projective_lifting_property r LinearMap.id hr
    exact Module.Projective.of_split (h.restrictScalars ℤ) (r.restrictScalars ℤ)
      (LinearMap.ext fun x => LinearMap.congr_fun hh x)
  have hrank : Module.finrank ℤ X ≤ g := by
    rw [finrank_int_eq' E X]
    exact (Nat.mul_le_mul_left _ hX).trans hq
  have hpol : IsPolFanOn (id : ℤ → ℤ) φs X := hφ X hrank
  have h1 : ∀ i, γ i ∈ balForms (id : ℤ → ℤ) X := fun i => mem_balForms_int.2 (hb i).1
  have hDr : (0 : ℝ) < D := by exact_mod_cast hD

  have hsplit : ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) →
      φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) ∧
      ∀ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * (fineMean M).evalZ (γ i) := by
    intro c hc
    have e0 : ∑ i, c i * φs.evalZ (γ i) ≤ φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by
      have := sum_le_evalR hpol h1 hp hc
      simpa [evalR, LinearMap.sum_apply] using this
    have eM : ∀ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤
        (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := fun M _ => sum_fineMean_le M hp hc
    have e3 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) +
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) =
        ∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) := by
      have e4 : ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) =
          D * (∑ i, c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i)) := by
        have e7 : ∀ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) =
            D * (c i * φs.evalZ (γ i) + ∑ M ∈ 𝓜, c i * (fineMean M).evalZ (γ i)) := fun i => by
          rw [← Finset.mul_sum]; ring
        simp only [e7]
        rw [← Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_comm (s := Finset.univ)]
      have h2 : (D : ℝ) * (φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) +
          ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ))) =
          ∑ i, c i * ((D : ℝ) * (φs.evalZ (γ i) + ∑ M ∈ 𝓜, (fineMean M).evalZ (γ i))) := by
        simpa only [InvFun.evalZ, eval_baseFun] using hl c hc
      rw [e4] at h2
      exact mul_left_cancel₀ hDr.ne' h2
    have hs2 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) ≤
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := Finset.sum_le_sum eM
    have e5 : φs.eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) = ∑ i, c i * φs.evalZ (γ i) := by linarith
    refine ⟨e5, ?_⟩
    have e6 : ∑ M ∈ 𝓜, ∑ i, c i * (fineMean M).evalZ (γ i) =
        ∑ M ∈ 𝓜, (fineMean M).eval X (fun a b => ∑ i, c i * (γ i a b : ℝ)) := by linarith
    exact fun M hM => ((Finset.sum_eq_sum_iff_of_le eM).1 e6 M hM).symm
  refine ⟨fun c hc => ?_, fun M hM => ?_⟩
  · simp only [InvFun.evalZ, eval_restr]
    exact (hsplit c hc).1
  · exact isFine_of_additive M hp ((hsplit (fun _ => 1) fun _ => zero_le_one).2 M hM)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.TraitChartForm

theorem jK_apply_eq_bot (R : Type) [CommRing R] [IsDomain R] (p : Sp (FractionRing R)) :
    (jK R) p = (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum R) := by
  apply PrimeSpectrum.ext
  change Ideal.comap (algebraMap R (FractionRing R)) p.asIdeal = ⊥
  rw [@Ideal.eq_bot_of_prime _ _ p.asIdeal p.isPrime]
  exact Ideal.comap_bot_of_injective _ (IsFractionRing.injective _ _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l}

end GlobalTheory.TraitChartForm

end
end

