module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0093
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0026
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0094
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsFlatAnIffIsConstMul
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.RulInst
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0063
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0019
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0096
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsTransition
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LeftEqIffLieVecSmul
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0068
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.IBIsKernel
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import Development.WeilBound.CoreStatements.TorusUniformisation.ChowMahlerFamilies.Bundle0025
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0067

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordsNeighbourhoodInOpen
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.RootHt.ArchB

namespace OpenNear

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R]
  {z : Sp R ⟶ X}

theorem val_int (hz : genPt ξ ⤳ centre z) (n : ℤ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨hz, (n : X.presheaf.stalk (centre z)), map_intCast _ n, map_intCast _ n⟩

theorem val_prod {T : Type} (s : Finset T) {a : T → Ω} {r : T → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i ∈ s, ValAt ξ z (a i) (r i)) : ValAt ξ z (∏ i ∈ s, a i) (∏ i ∈ s, r i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using val_one hz
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.prod_insert hi]
    exact val_mul (h i (Finset.mem_insert_self _ _)) (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

theorem val_aeval {κ : Type} {a : κ → Ω} {r : κ → R} (hz : genPt ξ ⤳ centre z)
    (h : ∀ i, ValAt ξ z (a i) (r i)) (P : MvPolynomial κ ℤ) :
    ValAt ξ z (MvPolynomial.aeval a P) (MvPolynomial.aeval r P) := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using val_int hz n
  | add p q hp hq => simpa only [map_add (f := _)] using val_add hp hq
  | mul_X p i hp => simpa only [map_mul, MvPolynomial.aeval_X] using val_mul hp (h i)

theorem genMap_germ {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) (p : Cpt ξ) (hp : p.1 ∈ W) :
    genMap ξ p (X.presheaf.germ W p.1 hp Q) =
      (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q) := by
  have h := TopCat.Presheaf.germ_stalkSpecializes X.presheaf hp p.2
  have h2 : (X.presheaf.stalkSpecializes p.2).hom (X.presheaf.germ W p.1 hp Q) =
      X.presheaf.germ W (genPt ξ) hW Q := by
    rw [← h]; rfl
  exact congrArg (Scheme.stalkClosedPointTo ξ).hom h2

theorem isUnit_germ_iff (hξ : IsCptGen ξ) {W : X.Opens} (hW : genPt ξ ∈ W) (Q : Γ(X, W)) {z : Sp ℂ ⟶ X}
    (hz : centre z ∈ W) {v : ℂ}
    (hv : ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hW Q)) v) :
    IsUnit (X.presheaf.germ W (centre z) hz Q) ↔ v ≠ 0 := by
  obtain ⟨h, s, hs, rfl⟩ := hv
  have hs' : s = X.presheaf.germ W (centre z) hz Q :=
    hξ.inj ⟨centre z, h⟩ (hs.trans (GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.OpenNear.genMap_germ hW Q ⟨centre z, h⟩ hz).symm)
  subst hs'
  have := Scheme.isLocalHom_stalkClosedPointTo' z
  constructor
  · exact fun hu => (hu.map (Scheme.stalkClosedPointTo z).hom).ne_zero
  · exact fun hv => (isUnit_map_iff (Scheme.stalkClosedPointTo z).hom _).1 (isUnit_iff_ne_zero.2 hv)

def segreRatio {K : Type} [Fintype K] {J : K → Type} (c : (k : K) → J k) (w : (Σ k, J k) → ℂ)
    (c' : (k : K) → J k) : ℂ := ∏ k, w ⟨k, c' k⟩ / w ⟨k, c k⟩

theorem val_segreRatio {K : Type} [Fintype K] {J : K → Type} {y : (Σ k, J k) → Ω} {z : Sp ℂ ⟶ X}
    {w : (Σ k, J k) → ℂ} {c : (k : K) → J k} (hz : genPt ξ ⤳ centre z) (hw : CoordsAt ξ y z w)
    (hc : ∀ k, w ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ValAt ξ z ((∏ k, y ⟨k, c' k⟩) / ∏ k, y ⟨k, c k⟩) (segreRatio c w c') := by
  rw [← Finset.prod_div_distrib]
  refine val_prod _ hz fun k _ => ?_
  obtain ⟨r, hr, hr'⟩ := (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).2 (c' k)
  rw [hr', mul_div_cancel_right₀ _ (hc k)]
  exact hr

theorem continuousAt_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (c' : (k : K) → J k) :
    ContinuousAt (fun w => segreRatio c w c') w₀ := by
  refine tendsto_finsetProd _ fun k _ => ?_
  exact ((continuous_apply _).continuousAt).div ((continuous_apply _).continuousAt) (hc k)

theorem continuousAt_aeval_segreRatio {K : Type} [Fintype K] {J : K → Type} {w₀ : (Σ k, J k) → ℂ}
    {c : (k : K) → J k} (hc : ∀ k, w₀ ⟨k, c k⟩ ≠ 0) (P : MvPolynomial ((k : K) → J k) ℤ) :
    ContinuousAt (fun w => MvPolynomial.aeval (segreRatio c w) P) w₀ := by
  induction P using MvPolynomial.induction_on with
  | C n => simpa using continuousAt_const
  | add p q hp hq =>
    simp only [map_add (f := _)]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, MvPolynomial.aeval_X]
    exact hp.mul (continuousAt_segreRatio hc i)

end OpenNear


open OpenNear in
theorem open_near : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω),
    (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) →
    ∀ (z₀ : Sp ℂ ⟶ X) (w₀ : (Σ k, J k) → ℂ) (U : X.Opens), CoordsAt ξ y z₀ w₀ → centre z₀ ∈ U →
      ∃ N ∈ 𝓝 w₀, ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), w ∈ N → CoordsAt ξ y z w → centre z ∈ U := by
  intro X Ω _ ξ K _ J _ y hgen ht z₀ w₀ U hw₀ hU
  choose c hc using hw₀.1
  have hc' : ∀ k, w₀ ⟨k, c k⟩ ≠ 0 := fun k => (hc k).ne_zero
  have hin₀ := in_chart (hgen (centre z₀)) hw₀ hc'
  obtain ⟨W, hWa, hW⟩ := ht.affine c hin₀.1
  have hz₀W : centre z₀ ∈ W := (hW _).2 ⟨hgen _, hin₀⟩
  obtain ⟨Q, hQU, hQ₀⟩ := hWa.exists_basicOpen_le (V := U) ⟨centre z₀, hU⟩ hz₀W
  have hgW : genPt ξ ∈ W := (hgen _).mem_open W.isOpen hz₀W
  have hreg : (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q) ∈
      Algebra.adjoin ℤ (Set.range fun j : (k : K) → J k => (∏ k, y ⟨k, j k⟩) / ∏ k, y ⟨k, c k⟩) := by
    rw [ht.ring c hin₀.1]
    intro p hp
    exact ⟨X.presheaf.germ W p.1 ((hW _).2 ⟨p.2, hp⟩) Q, GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.OpenNear.genMap_germ hgW Q p _⟩
  rw [Algebra.adjoin_range_eq_range_aeval] at hreg
  obtain ⟨P, hP⟩ := hreg
  have hval : ∀ (z : Sp ℂ ⟶ X) (w : (Σ k, J k) → ℂ), CoordsAt ξ y z w → (∀ k, w ⟨k, c k⟩ ≠ 0) →
      ValAt ξ z ((Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ W (genPt ξ) hgW Q))
        (MvPolynomial.aeval (segreRatio c w) P) := by
    intro z w hw hcw
    rw [← hP]
    exact val_aeval (hgen _) (val_segreRatio (hgen _) hw hcw) P
  have hne₀ : MvPolynomial.aeval (segreRatio c w₀) P ≠ 0 :=
    (isUnit_germ_iff ht.gen hgW Q hz₀W (hval z₀ w₀ hw₀ hc')).1
      ((Scheme.mem_basicOpen X Q _ hz₀W).1 hQ₀)
  refine ⟨{w | (∀ k, w ⟨k, c k⟩ ≠ 0) ∧ MvPolynomial.aeval (segreRatio c w) P ≠ 0}, ?_, ?_⟩
  · refine Filter.Eventually.and ?_ ((continuousAt_aeval_segreRatio hc' P).eventually_ne hne₀)
    exact Filter.eventually_all.2 fun k => ((continuous_apply _).continuousAt).eventually_ne (hc' k)
  · rintro z w ⟨hcw, hne⟩ hw
    have hzW : centre z ∈ W := (hW _).2 ⟨hgen _, in_chart (hgen _) hw hcw⟩
    exact hQU ((Scheme.mem_basicOpen X Q _ hzW).2
      ((isUnit_germ_iff ht.gen hgW Q hzW (hval z w hw hcw)).2 hne))

end GlobalTheory.CompanionTheory.Ar.RootHt.ArchB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenFramesInvertibleChange
section
open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Fl GlobalTheory.CompanionTheory.Ar.Flat GlobalTheory.CompanionTheory.Ar.LocFn

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange

theorem eigFrame_change : ∀ (S : Scheme.{0}) (R : Type) [CommRing R] [Nontrivial R] (G : Over S) [GrpObj G] [IsCommMonObj G] (x : Sp R ⟶ S) (O : Type) [CommRing O] (act : OAct O G) (σ : O →+* R) (n r : ℕ) (u : Fin n → (epsAt x ⟶ G)) (V : Fin r → (epsAt x ⟶ G)), IsEigFrame act x σ u → IsEigFrame act x σ V → r = n ∧ ∃ C : Matrix (Fin r) (Fin n) R, (∀ i, IsComb (C i) u (V i)) ∧ ∃ C' : Matrix (Fin n) (Fin r) R, C * C' = 1 ∧ C' * C = 1 := by
  intro S R _ _ G _ _ x O _ act σ n r u V hu hV
  obtain ⟨E, _, _, ⟨M⟩⟩ := lieModel_exists S G R x
  obtain ⟨ρ, hρ, -⟩ := lieModel_exists_unique_act S G R x E M O act.act act.hom act.one act.mul act.add
  obtain ⟨hc, hf⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fl.Bridge.comb_eig_frame S R G x E M
  have hfr := (hf O act ρ σ hρ).2
  choose u' hu' using fun i => M.onto (u i) (hu.1 i).1
  choose V' hV' using fun i => M.onto (V i) (hV.1 i).1
  obtain rfl : (fun k => M.pt (u' k)) = u := funext hu'
  obtain rfl : (fun k => M.pt (V' k)) = V := funext hV'
  obtain ⟨lu, su⟩ := (hfr n u').1 hu
  obtain ⟨lV, sV⟩ := (hfr r V').1 hV
  let bu : Module.Basis (Fin n) R (eigSp ρ σ) := (Module.Basis.span lu).map (LinearEquiv.ofEq _ _ su)
  let bV : Module.Basis (Fin r) R (eigSp ρ σ) := (Module.Basis.span lV).map (LinearEquiv.ofEq _ _ sV)
  have bu_eq : ∀ i, (bu i : E) = u' i := fun i => by
    simp [bu, Module.Basis.span_apply]
  have bV_eq : ∀ i, (bV i : E) = V' i := fun i => by
    simp [bV, Module.Basis.span_apply]
  have hrn : r = n := by simpa using Fintype.card_congr (bV.indexEquiv bu)
  refine ⟨hrn, (bu.toMatrix bV).transpose, fun i => ?_, (bV.toMatrix bu).transpose, ?_, ?_⟩
  · refine (hc n _ u' _).2 ?_
    have h : V' i = ∑ k, (bu.toMatrix bV).transpose i k • u' k := by
      have h := congrArg Subtype.val (bu.sum_repr (bV i))
      rw [bV_eq] at h
      rw [← h]
      clear h hc hf hfr hu hV hu' hV' hρ
      simp only [Submodule.coe_sum, Submodule.coe_smul, bu_eq, Matrix.transpose_apply, Module.Basis.toMatrix_apply]
    exact congrArg M.pt h
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, Module.Basis.toMatrix_mul_toMatrix_flip, Matrix.transpose_one]

end GlobalTheory.CompanionTheory.Ar.LocFn.FrameChange
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.EigenspaceBasisExists
section
open NumberField

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.HT.LatMult

open Module

variable {E : Type} [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module (𝓞 E) X]
  (k : Type) [Field k]

def pullAct : 𝓞 E →+* Module.End k (X →+ k) where
  toFun a :=
    { toFun := fun c => c.comp (DistribSMul.toAddMonoidHom X a)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  map_one' := by ext c x; simp
  map_mul' a b := by
    ext c x
    simp [mul_comm a b, mul_smul]
  map_zero' := by ext c x; simp
  map_add' a b := by
    ext c x
    simp [add_smul]

variable {X k}

theorem pullAct_apply (a : 𝓞 E) (c : X →+ k) (x : X) : pullAct X k a c x = c (a • x) := rfl

theorem trace_pullAct [Module.Free ℤ X] [Module.Finite ℤ X] [FiniteDimensional k (X →+ k)] (a : 𝓞 E) :
    ∃ n : ℤ, LinearMap.trace k (X →+ k) (pullAct X k a) = (n : k) := by
  classical
  let b := Module.Free.chooseBasis ℤ X
  let B := GlobalTheory.Diag.dualBasis k b
  refine ⟨∑ i, b.repr (a • b i) i, ?_⟩
  rw [LinearMap.trace_eq_matrix_trace k B, Matrix.trace]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.diag_apply, LinearMap.toMatrix_apply, GlobalTheory.Diag.dualBasis_repr, pullAct_apply,
    GlobalTheory.Diag.dualBasis_apply]

theorem eigenHom_eq_eigSp (τ : 𝓞 E →+* k) (σ : E →+* k) (h : σ.comp (algebraMap (𝓞 E) E) = τ) :
    GlobalTheory.Diag.eigenHom X τ = GlobalTheory.CompanionTheory.Ar.HT.eigSp (pullAct X k) σ := by
  ext c
  have hσ : ∀ a : 𝓞 E, σ (a : E) = τ a := fun a => by rw [← h]; rfl
  simp only [GlobalTheory.CompanionTheory.Ar.HT.eigSp, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    sub_eq_zero, Module.End.smul_def, Module.End.one_apply, hσ]
  constructor
  · intro hc a
    ext x
    simpa [pullAct_apply] using hc a x
  · intro hc a x
    simpa [pullAct_apply] using DFunLike.congr_fun (hc a) x

theorem nonempty_basis_eigenHom :
    ∀ (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X] [Module.Free ℤ X]
      [Module.Finite ℤ X] [Module (𝓞 E) X] (k : Type) [Field k] [IsAlgClosed k] [CharZero k]
      (τ : 𝓞 E →+* k),
      Nonempty (Module.Basis (Fin (Module.finrank ℤ X / Module.finrank ℚ E)) k
        (GlobalTheory.Diag.eigenHom X τ)) := by
  intro E _ _ X _ _ _ _ k _ _ _ τ
  classical
  have hinj : Function.Injective τ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [Ideal.under_def, RingHom.comap_ker, ← RingHom.injective_iff_ker_eq_bot]
    exact RingHom.injective_int _
  let σ : E →+* k := IsFractionRing.lift hinj
  have hσ : σ.comp (algebraMap (𝓞 E) E) = τ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hinj a
  let b := Module.Free.chooseBasis ℤ X
  let B := GlobalTheory.Diag.dualBasis k b
  haveI : FiniteDimensional k (X →+ k) := Module.Finite.of_basis B
  have hV : finrank k (X →+ k) = finrank ℤ X := by
    rw [finrank_eq_card_basis B, finrank_eq_card_basis b]
  have hmul := GlobalTheory.CompanionTheory.Ar.HT.EigDim.finrank_eigSp_mul k (X →+ k) E (pullAct X k)
    trace_pullAct σ
  rw [← eigenHom_eq_eigSp τ σ hσ, hV] at hmul
  have hd : 0 < finrank ℚ E := Module.finrank_pos
  have hdim : finrank k (GlobalTheory.Diag.eigenHom X τ) = finrank ℤ X / finrank ℚ E := by
    rw [← hmul, Nat.mul_div_cancel _ hd]
  haveI : FiniteDimensional k (GlobalTheory.Diag.eigenHom X τ) := inferInstance
  exact ⟨Module.finBasisOfFinrankEq _ _ hdim⟩

end GlobalTheory.CompanionTheory.Ar.HT.LatMult
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsAbPartBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Matrix
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC

open ReciprocityTheory.ChartRestriction.G.Out.GtBCPf

variable {L L' : Type} [Field L] [Field L']

def torusExtBC (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) :
    TorusExtension ((Over.pullback f).obj G) :=
  letI := T.grpB
  letI := T.addCommGroup
  haveI := T.q_hom
  haveI := T.i_hom
  { X := T.X
    addCommGroup := T.addCommGroup
    free := T.free
    finite := T.finite
    B := (Over.pullback f).obj T.B
    grpB := inferInstance
    isAbelian := GlobalTheory.isAbelianScheme_pullback_obj f T.B T.isAbelian
    q := (Over.pullback f).map T.q
    q_hom := inferInstance
    q_flat := qB_flat f T.q T.q_flat
    q_surjective := qB_surj f T.q T.q_surjective
    q_quasiCompact := MorphismProperty.of_isPullback (P := @QuasiCompact) (qB_sq f T.q) T.q_quasiCompact
    i := iB f T.X T.i
    i_hom := iB_hom f T.X T.i
    isKernel := iB_isKernel f T.X T.q T.i T.isKernel }

theorem torusRing_hom_ext {X : Type} [AddCommGroup X] {A : Type} [CommRing A]
    (g h : torusRing ZU X ⟶ CommRingCat.of A)
    (w : ∀ χ : X, g.hom (AddMonoidAlgebra.single χ 1) = h.hom (AddMonoidAlgebra.single χ 1)) : g = h := by
  apply CommRingCat.hom_ext
  refine AddMonoidAlgebra.ringHom_ext (fun b => ?_) w
  have hb : b = ((b.down : ℤ) : ULift ℤ) := by ext; simp
  have e : ∀ (n : ℤ) (r : torusRing ZU X ⟶ CommRingCat.of A),
      r.hom (AddMonoidAlgebra.single 0 ((n : ℤ) : ULift ℤ)) = (n : A) := fun n r => by
    have : (AddMonoidAlgebra.single (0 : X) ((n : ℤ) : ULift ℤ) : AddMonoidAlgebra (ULift ℤ) X) = (n : AddMonoidAlgebra (ULift ℤ) X) := by
      rw [AddMonoidAlgebra.intCast_def]
    exact (congrArg r.hom this).trans (map_intCast r.hom n)
  rw [hb, e, e]

def toZTorus (S : Scheme.{0}) (X : Type) [AddCommGroup X] : (splitTorus S X).left ⟶ Spec (torusRing ZU X) :=
  pullback.fst (splitTorusAff ZU X).hom (toZ S)

theorem hT_toZTorus {S S' : Scheme.{0}} (f : S' ⟶ S) (X : Type) [AddCommGroup X] :
    hT f X ≫ toZTorus S X = toZTorus S' X :=
  pullback.lift_fst _ _ _

theorem splitTorus_left_ext {S T : Scheme.{0}} {X : Type} [AddCommGroup X] {a b : T ⟶ (splitTorus S X).left}
    (h₁ : a ≫ toZTorus S X = b ≫ toZTorus S X) (h₂ : a ≫ (splitTorus S X).hom = b ≫ (splitTorus S X).hom) : a = b :=
  pullback.hom_ext h₁ h₂

theorem point_hT {X : Type} [AddCommGroup X] (e : L →+* L') {A : Type} [CommRing A] (a : Sp A ⟶ Sp L')
    (t' : Over.mk a ⟶ splitTorus (Sp L') X) (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X)
    (h : ∀ χ, charVal t χ = charVal t' χ) : t'.left ≫ hT (spMap e) X = t.left := by
  have key : (t'.left ≫ toZTorus (Sp L') X : Sp A ⟶ _) = (t.left ≫ toZTorus (Sp L) X : Sp A ⟶ _) := by
    have p : Spec.preimage (t'.left ≫ toZTorus (Sp L') X : Sp A ⟶ _) =
        Spec.preimage (t.left ≫ toZTorus (Sp L) X : Sp A ⟶ _) :=
      torusRing_hom_ext _ _ fun χ => (h χ).symm
    have := congrArg Spec.map p
    rwa [Spec.map_preimage, Spec.map_preimage] at this
  refine splitTorus_left_ext ?_ ?_
  · rw [Category.assoc, hT_toZTorus]; exact key
  · rw [Category.assoc, hT_snd, ← Category.assoc, Over.w t', Over.w t]; rfl

def eBC (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    (e : T.B ≅ B') : (torusExtBC f T).B ≅ (Over.pullback f).obj B' :=
  (Over.pullback f).mapIso e

theorem eBC_hom (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    [GrpObj B'] (e : T.B ≅ B') (h : letI := T.grpB; IsMonHom e.hom) :
    letI := (torusExtBC f T).grpB; IsMonHom (eBC f T e).hom := by
  letI := T.grpB
  haveI := h
  exact (inferInstance : IsMonHom ((Over.pullback f).map e.hom))

theorem map_left_fst {S S' : Scheme.{0}} (f : S' ⟶ S) {X Y : Over S} (a : X ⟶ Y) :
    ((Over.pullback f).map a).left ≫ pullback.fst Y.hom f = pullback.fst X.hom f ≫ a.left :=
  pullback.lift_fst _ _ _

theorem quot_bc (f : Sp L' ⟶ Sp L) {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) {B' : Over (Sp L)}
    (e : T.B ≅ B') : ((torusExtBC f T).q ≫ (eBC f T e).hom).left ≫ pullback.fst B'.hom f =
      pullback.fst G.hom f ≫ (T.q ≫ e.hom).left := by
  change ((Over.pullback f).map T.q ≫ (Over.pullback f).map e.hom).left ≫ _ = _
  rw [← Functor.map_comp]
  exact map_left_fst f _

theorem iB_point (e : L →+* L') {G : Over (Sp L)} [GrpObj G] {X : Type} [AddCommGroup X]
    (i : splitTorus (Sp L) X ⟶ G) {A : Type} [CommRing A] (a : Sp A ⟶ Sp L')
    (t' : Over.mk a ⟶ splitTorus (Sp L') X) (t : Over.mk (a ≫ spMap e) ⟶ splitTorus (Sp L) X)
    (h : ∀ χ, charVal t χ = charVal t' χ) :
    (t' ≫ iB (spMap e) X i).left ≫ pullback.fst G.hom (spMap e) = (t ≫ i).left := by
  rw [Over.comp_left, Over.comp_left, Category.assoc, iB_h, ← Category.assoc, point_hT e a t' t h]

theorem torusOver_torusExtBC (e : L →+* L') {G : Over (Sp L)} [GrpObj G] (T : TorusExtension G) :
    TorusOver e T (torusExtBC (spMap e) T) (pullback.fst G.hom (spMap e)) := by
  letI := T.addCommGroup
  exact ⟨AddEquiv.refl _, fun A _ a t' t h => iB_point e T.i a t' t h⟩

theorem lbIso_square {X X' Y Y' : Scheme.{0}} {φ : X' ⟶ X} {β : Y' ⟶ Y} {ψ : X ⟶ Y} {ψ' : X' ⟶ Y'}
    (hc : ψ' ≫ β = φ ≫ ψ) {A : LB X} {A' : LB X'} {B : LB Y} {B' : LB Y'} (hB : B.IsLB) (hA' : A'.IsLB)
    (hB' : B'.IsLB) (hA : A.IsLB) (a : LBIso A' (A.pull φ)) (b : LBIso B' (B.pull β)) (h : LBIso A (B.pull ψ)) :
    LBIso A' (B'.pull ψ') := by
  have a1 : LBIso (A.pull φ) ((B.pull β).pull ψ') :=
    LBIso.chartPull (chartPullPull A φ φ rfl)
      (chartPullLinComb B β (fun _ : PUnit => ψ') (fun _ => ψ) (fun _ => 1) φ (fun _ => hc)) h
  have a2 : LBIso (B'.pull ψ') ((B.pull β).pull ψ') :=
    LBIso.chartPull (chartPullPull _ ψ' ψ' rfl) (chartPullPull _ ψ' ψ' rfl) b
  have l1 := pull_isLB hA φ
  have l2 := pull_isLB (pull_isLB hB β) ψ'
  have l3 := pull_isLB hB' ψ'
  exact LBIso.trans hA' l1 l3 a (LBIso.trans l1 l2 l3 a1 a2.symm)

theorem exists_abPart_baseChange : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S : Scheme.{0}) (t : SAB H S) (L L' : Type) [Field L] [Field L'] (z : Sp L ⟶ S) (P : AbPart t z) (e : L →+* L'), ∃ (P' : AbPart t (spMap e ≫ z)) (mK : SABMap P'.tK P.tK (spMap e)) (mB : SABMap P'.tB P.tB (spMap e)), mK.φ ≫ P.m.φ = P'.m.φ ∧ mK.φ ≫ (P.τ.q ≫ P.e.hom).left = (P'.τ.q ≫ P'.e.hom).left ≫ mB.φ ∧ GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.TorusOver e P.τ P'.τ mK.φ := by
  intro E _ _ _ H S t L L' _ _ z P e
  obtain ⟨PK, cK, sK, aK, rK, mK, hK⟩ := sabPull Out.CubePf.cubePull (spMap e) P.tK
  obtain ⟨PB, cB, sB, aB, rB, mB, hB⟩ := sabPull Out.CubePf.cubePull (spMap e) P.tB
  obtain ⟨mZ, hZ⟩ := sabComp pullCubComp E H _ _ _ _ _ _ _ _ P.m mK
  let tK' : SAB H (Sp L') := ⟨(Over.pullback (spMap e)).obj P.tK.G, IsSemiAbelian.pullback (spMap e) P.tK.G P.tK.semi,
    OAct.pullback (spMap e) P.tK.G P.tK.act, PK, cK, sK, aK, rK⟩
  let tB' : SAB H (Sp L') := ⟨(Over.pullback (spMap e)).obj P.tB.G, IsSemiAbelian.pullback (spMap e) P.tB.G P.tB.semi,
    OAct.pullback (spMap e) P.tB.G P.tB.act, PB, cB, sB, aB, rB⟩
  let τ' : TorusExtension tK'.G := torusExtBC (spMap e) P.τ
  let e' : τ'.B ≅ tB'.G := eBC (spMap e) P.τ P.e
  have hψ : (τ'.q ≫ e'.hom).left ≫ mB.φ = mK.φ ≫ (P.τ.q ≫ P.e.hom).left := by
    rw [hK, hB]
    exact quot_bc (spMap e) P.τ P.e
  have act' : ∀ a, tK'.act.act a ≫ τ'.q ≫ e'.hom = τ'.q ≫ e'.hom ≫ tB'.act.act a := fun a => by
    change (Over.pullback (spMap e)).map (P.tK.act.act a) ≫ (Over.pullback (spMap e)).map P.τ.q ≫
      (Over.pullback (spMap e)).map P.e.hom = (Over.pullback (spMap e)).map P.τ.q ≫
      (Over.pullback (spMap e)).map P.e.hom ≫ (Over.pullback (spMap e)).map (P.tB.act.act a)
    simp only [← Functor.map_comp]
    rw [P.act a]
  have pp' : LBIso tK'.PP.L (tB'.PP.L.pull (τ'.q ≫ e'.hom).left) := by
    obtain ⟨wK, gK, -⟩ := mK.lin
    obtain ⟨wB, gB, -⟩ := mB.lin
    exact lbIso_square hψ P.tB.PP.isLB tK'.PP.isLB tB'.PP.isLB P.tK.PP.isLB ⟨wK, gK⟩ ⟨wB, gB⟩ P.pp
  have hT : TorusOver e P.τ τ' mK.φ := by
    rw [hK]
    exact torusOver_torusExtBC e P.τ
  exact ⟨⟨tK', mZ, τ', tB', e', eBC_hom (spMap e) P.τ P.e P.e_hom, act', pp'⟩, mK, mB, hZ.symm, hψ.symm, hT⟩

end GlobalTheory.CompanionTheory.Ar.Cusp.PtHt.Arch.AbPartBC
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.FiniteSurjectiveOpenImage
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.Strat

theorem preimage_le_of_finite_surjective : ∀ (Z Z' : Scheme.{0}) [IsIntegral Z] [IsIntegral Z'] (π : Z' ⟶ Z), IsFinite π → Surjective π → ∀ V : Z'.Opens, (V : Set Z').Nonempty → ∃ U : Z.Opens, (U : Set Z).Nonempty ∧ π ⁻¹ᵁ U ≤ V :=
  PositivityTheory.Xgn.finite_surjective_image_open

end GlobalTheory.CompanionTheory.Ar.Strat
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.HermitianSquareNormGram
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.TorusUnif
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.TorusUnif

theorem sqAt_sum_eq_gram : ∀ (L : Type) [Field L] [NumberField L] (B : GroundTheory.Heights₂.Heights.HermitianBundle.{0} L) (σ : L →+* ℂ) (n : ℕ)
    (ε : Fin n → B.carrier) (Γ : Matrix (Fin n) (Fin n) ℂ),
    (∀ a b, Γ a b = (B.metric.form σ).inner ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε a)
      ((1 : GroundTheory.Heights₂.Heights.ComplexAt σ) ⊗ₜ[𝓞 L] ε b)) → ∀ w : Fin n → ℂ,
    sqAt B σ (∑ a, GroundTheory.Heights₂.Heights.ComplexAt.ofComplex σ (w a) ⊗ₜ[𝓞 L] ε a) = (star w ⬝ᵥ (Γ *ᵥ w)).re :=
  @PositivityTheory.Xgn.hermitian_norm_square_formula

end GlobalTheory.CompanionTheory.Ar.TorusUnif
end

