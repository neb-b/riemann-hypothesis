module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2287
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2197
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2389
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2286
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2315
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2302
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2685
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2868
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2512
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2266
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2244
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2327
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2237
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2694
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2850
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0060
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2863
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2851
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2870
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtensionCompletedEtaleChart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2873
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsProperToroidalModelStructureMap
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2861

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieImageIffLieCorrespondenceDeRhamExtension
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

namespace GlobalTheory.PtExt


set_option maxHeartbeats 1000000 in
theorem isLieImage_iff_lieCorr : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (p : ℕ) [Fact p.Prime]  (R : Type) [CommRing R], IsNilpotent (p : R) → ∀ (A : Over (Sp R)) [GrpObj A] (g : ℕ), IsAbelianScheme A → SmoothOfRelativeDimension g A.hom → ∀ (G : PDivGroup p R) (t : G.TorsionTower A) (E : primDR A ≃ₗ[R] ((G.cocycles × G.omega) ⧸ _root_.LinearMap.range (G.cob.prod (_root_.LinearMap.codRestrict G.omegaSub ((_root_.LinearMap.piMap fun i => _root_.GlobalTheory.AugCot.d (_root_.Bialgebra.counitAlgHom _ (G.A i))).domRestrict G.funs) (fun b n => (_root_.GlobalTheory.PDiv.cotMap_d _ _).trans (_root_.congrArg _ (b.2 n))))))), (∀ c, IsCan t c (E c)) → ∀ (h : HdR A) (v : epsR R ⟶ A), IsLieImage h v ↔ t.LieCorr (G.lieUnivToLie (E.symm.dualMap h)) v := by
  intro hHdR p _ R _ hnil A _ g hA hsm G t E hE h v
  obtain ⟨N, hN⟩ := hnil
  haveI := isAdicComplete_span_natCast_of_isNilpotent p R ⟨N, hN⟩

  have key : ∀ (β : Form (A.hom ≫ 𝟙 _)) (hβ : Form.cl _ β ∈ primDR A) (w : G.omega),
      IsCan t ⟨_, hβ⟩ (G.rigOfOmega w) → G.lieUnivToLie (E.symm.dualMap h) w = h ⟨_, hβ⟩ := by
    intro β hβ w hw
    have e : E ⟨_, hβ⟩ = G.rigOfOmega w := isCan_unique R A p G t _ hA _ _ (hE _) hw
    change (E.symm.dualMap h) (G.rigOfOmega w) = _
    change h (E.symm (G.rigOfOmega w)) = _
    rw [← e, LinearEquiv.symm_apply_apply]
  constructor
  · rintro ⟨hv, hh⟩
    obtain ⟨x', hx', -⟩ := t.existsUnique_lieCorr hv
    obtain ⟨ψ, hψ⟩ := T.exists_hodgeFiltration_to_pDivOmega_linearMap p R N hN A hA G t
    haveI : Module.Finite R G.omega := .equiv (LinearEquiv.ofBijective _
      (PDivGroup.omegaLevel_bijective_of_pow_eq_zero p R N hN G N le_rfl)).symm
    have hs := surjective_of_range_sup_smul_top_eq_top R _ _ ψ
      (T.primitive_hodge_to_omega_span_mod_maximal hHdR p R N hN A g hA hsm G t ψ hψ)
    suffices e : x' = G.lieUnivToLie (E.symm.dualMap h) by rw [← e]; exact hx'
    refine LinearMap.ext fun w => ?_
    obtain ⟨c, rfl⟩ := hs w
    obtain ⟨c, hF⟩ := c
    have hF' := hF
    change c.1 ∈ F1 _ at hF'
    rw [hodgeFiltration_eq_range] at hF'
    obtain ⟨c, hc⟩ := c
    obtain ⟨β, rfl⟩ := hF'
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hc
    have hw : ψ ⟨_, hF⟩ = w :=
      PDivGroup.rigOfOmega_injective_of_pow p R N hN G (isCan_unique R A p G t _ hA _ _ (hψ _) hw2)
    rw [key β hc _ (hψ ⟨_, hF⟩), hw, lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 x' v hx', hh β hc]
  · intro hx
    refine ⟨hx.1, fun β hβ => ?_⟩
    obtain ⟨w, hw1, hw2⟩ := isCan_form R A p G t β hβ
    rw [← key β hβ w hw2]
    exact lie_cotVal_eq_tanVal R A p G t ⟨N, hN⟩ β w hw1 _ v hx

end GlobalTheory.PtExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftGeometricPointOverClosedFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.Mum.Emb.lift_closedPoint : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (M : Modif R) (G' : Over M.S) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ E : Emb M.π G', ∀ (P' : Scheme.{0}) (b : P' ⟶ PSpace R E.N) (X : E.H.toScheme.Opens) (a : X.toScheme ⟶ P'), LocallyQuasiFinite b → Surjective a → a ≫ b = X.ι ≫ E.f → (∀ z : E.H.toScheme, M.π (G'.hom (E.H.ι z)) = closedPoint R → z ∈ X) → ∀ x : P', IsClosed ({x} : Set P') → (b ≫ PSpace.str R E.N) x = closedPoint R → ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (ξ : Sp Ω ⟶ P') (s : Sp Ω ⟶ M.S), Set.range ξ = {x} → ξ ≫ b ≫ PSpace.str R E.N = s ≫ M.π → ∃ p : Sp Ω ⟶ X.toScheme, p ≫ a = ξ ∧ p ≫ X.ι ≫ E.H.ι ≫ G'.hom = s := by
  intro R _ _ _ hAdm M G' _ _ hG E P' b X a hb ha hab hX x hx hxc Ω _ _ ξ s hξ hs
  have hxr : ∀ w, ξ w = x := fun w => by
    have : ξ w ∈ Set.range ξ := ⟨w, rfl⟩
    rw [hξ] at this; exact this
  have hfo : ∀ h : E.H.toScheme, PSpace.str R E.N (E.f h) = M.π (G'.hom (E.H.ι h)) := fun h => by
    rw [← Scheme.Hom.comp_apply, E.f_over]; rfl
  have hcl : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → M.π (G'.hom (E.H.ι h)) = closedPoint R := by
    rintro h ⟨w, hw⟩
    rw [← hfo, ← hw, ← Scheme.Hom.comp_apply, Category.assoc, Scheme.Hom.comp_apply, hxr]
    exact hxc
  obtain ⟨z, hz⟩ := ha.surj x
  have hzx : E.f (X.ι z) = b x := by
    rw [← hz, ← Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hab]
  have hrng : E.f (X.ι z) ∈ Set.range (ξ ≫ b) := by
    let w : Sp Ω := Nonempty.some inferInstance
    exact ⟨w, by rw [Scheme.Hom.comp_apply, hxr, hzx]⟩
  have hg : ∃ g : E.H.toScheme, M.π (G'.hom (E.H.ι g)) = closedPoint R ∧ E.f g ∈ Set.range (ξ ≫ b) :=
    ⟨X.ι z, hcl _ hrng, hrng⟩
  have hs' : (ξ ≫ b) ≫ PSpace.str R E.N = s ≫ M.π := by rw [Category.assoc]; exact hs
  obtain ⟨Ω', _, io, q, hq1, hq2⟩ := GlobalTheory.T.exists_lift_after_field_extension R M.S M.π G' E Ω (ξ ≫ b) s hs' hg
  let φ : E.H.toScheme ⟶ pullback M.π (PSpace.str R E.N) :=
    pullback.lift (E.H.ι ≫ G'.hom) E.f (by rw [E.f_over, Category.assoc])
  haveI : Smooth G'.hom := hG.smooth
  have hφ : LocallyOfFiniteType φ := by
    have : LocallyOfFiniteType (φ ≫ pullback.fst _ _) := by
      rw [pullback.lift_fst]; infer_instance
    exact HasRingHomProperty.of_comp (fun _ _ => RingHom.FiniteType.of_comp_finiteType) this
  obtain ⟨p₀, hp₀⟩ := _root_.GlobalTheory.Mum.exists_pt_of_pt_ext _ _ φ hφ Ω (pullback.lift s (ξ ≫ b) hs'.symm) Ω' io q (by
    apply pullback.hom_ext
    · simp only [φ, Category.assoc, pullback.lift_fst]; exact hq2
    · simp only [φ, Category.assoc, pullback.lift_snd]; exact hq1)
  have hp1 : p₀ ≫ E.f = ξ ≫ b := by
    have := congrArg (· ≫ pullback.snd M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_snd, pullback.lift_snd] at this
  have hp2 : p₀ ≫ E.H.ι ≫ G'.hom = s := by
    have := congrArg (· ≫ pullback.fst M.π (PSpace.str R E.N)) hp₀
    simp only [φ, Category.assoc] at this
    rwa [pullback.lift_fst, pullback.lift_fst, ← Category.assoc] at this
  have hU : ∀ h : E.H.toScheme, E.f h ∈ Set.range (ξ ≫ b) → h ∈ X := fun h hh => hX h (hcl h hh)
  have hpX : Set.range p₀ ⊆ Set.range X.ι := by
    rintro _ ⟨w, rfl⟩
    rw [Scheme.Opens.range_ι]
    refine hU _ ⟨w, ?_⟩
    rw [← Scheme.Hom.comp_apply, hp1]
  let p : Sp Ω ⟶ X.toScheme := IsOpenImmersion.lift X.ι p₀ hpX
  have hpι : p ≫ X.ι = p₀ := IsOpenImmersion.lift_fac _ _ _
  haveI : IsNoetherianRing R := hAdm.1
  have c4 := _root_.GlobalTheory.Mum.FibConn.fib_conn R M.S M.π (by have := M.proper; infer_instance) G' hG.smooth E
    (_root_.GlobalTheory.Mum.connectedSpace_pullback_closedFibre_field R hAdm M) Ω (ξ ≫ b) hg
  have c3 := _root_.GlobalTheory.Mum.geomFibre_restrict_open_connected _ _ _ X E.f (ξ ≫ b) hU c4
  have c2 := GlobalTheory.T.connectedSpace_pullback_of_comp_of_surjective _ _ _ _ a b (X.ι ≫ E.f) (ξ ≫ b) hab ha c3
  refine ⟨p, _root_.GlobalTheory.Mum.eq_of_comp_eq_of_connectedSpace_pullback _ _ b hb Ω (ξ ≫ b) (p ≫ a) ξ ?_ rfl c2, ?_⟩
  · rw [Category.assoc, hab, ← Category.assoc, hpι, hp1]
  · rw [← Category.assoc, hpι, hp2]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleIsoEqUnitMulOneAddEpsPotential
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.RigChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.ConnUnit
open GlobalTheory.KS

theorem constFn_mul {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (O : X.Opens) (a b : R) :
    constFn q O (a * b) = constFn q O a * constFn q O b := by
  simp only [constFn, map_mul]

theorem constFn_eps_sq {k : Type} [Field k] {X : Scheme.{0}} (q : X ⟶ Sp (DualNumber k)) (O : X.Opens) :
    constFn q O DualNumber.eps * constFn q O DualNumber.eps = 0 := by
  rw [← constFn_mul, DualNumber.eps_mul_eps]; simp only [constFn, map_zero]

theorem rsT_resG {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (x : Γ(Y, U)) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT (resG Y h x) Q = rsT x Q := by
  rw [← rsT_of_le h, rsT_rsT h hQ]

theorem rsT_app {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (x : Γ(Y, U)) {Q : Z.Opens} (hQ : Q ≤ f ⁻¹ᵁ U) :
    rsT ((f.app U).hom x) Q = pbT f x Q := by
  rw [rsT_of_le hQ, pbT_of_le f hQ]
  rfl

theorem pbT_pbT {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) {O₀ : X.Opens} {O₁ : Y.Opens} {O₂ : Z.Opens}
    (h₁ : O₁ ≤ g ⁻¹ᵁ O₀) (h₂ : O₂ ≤ f ⁻¹ᵁ O₁) (s : Γ(X, O₀)) :
    pbT f (pbT g s O₁) O₂ = pbT (f ≫ g) s O₂ := by
  rw [pbT_of_le g h₁, pbT_of_le f h₂, pbT_of_le (f ≫ g) (h₂.trans (f.preimage_mono h₁))]
  exact congrArg (fun φ => φ.hom s) (Scheme.Hom.appLE_comp_appLE f g O₀ O₁ O₂ h₁ h₂)

theorem constFn_top_appTop {R : Type} [CommRing R] {X : Scheme.{0}} (q : X ⟶ Sp R) (x : Γ(Sp R, ⊤)) :
    constFn q ⊤ ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = q.appTop.hom x := by
  have e : (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom x) = x := by
    rw [← CommRingCat.comp_apply, Iso.hom_inv_id, CommRingCat.id_apply]
  unfold constFn
  rw [e]
  exact congrArg (fun φ => φ.hom x) (Scheme.Hom.appLE_eq_app (f := q) (U := ⊤))

theorem preimage_le_of_eps {k : Type} [Field k] {B X : Scheme.{0}} (q : B ⟶ Sp (DualNumber k)) (π₁ π₂ : B ⟶ X)
    (e : ∀ W : X.Opens, Γ(X, W) → Γ(B, π₂ ⁻¹ᵁ W))
    (hid : ∀ (W : X.Opens) (f : Γ(X, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) +
      constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W f) (W : X.Opens) : π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W := by
  by_contra h
  have h1 := hid W 1
  rw [pbT, dite_eq_right h, pbT_one π₂ le_rfl] at h1
  have hu : (1 + constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) *
      (1 - constFn q (π₂ ⁻¹ᵁ W) DualNumber.eps * e W 1) = 1 := by
    linear_combination (-(e W 1) ^ 2) * constFn_eps_sq q (π₂ ⁻¹ᵁ W)
  rw [← h1, zero_mul] at hu
  apply h
  intro y hy
  exfalso
  haveI : Nonempty (π₂ ⁻¹ᵁ W) := ⟨⟨y, hy⟩⟩
  exact zero_ne_one hu

theorem rsT_inv_mul {Y : Scheme.{0}} {U : Y.Opens} (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ U) :
    rsT (↑(u⁻¹) : Γ(Y, U)) Q * rsT (u : Γ(Y, U)) Q = 1 := by
  rw [← rsT_mul, Units.inv_mul, rsT_one hQ]

theorem rsT_res_val {Y : Scheme.{0}} {U V : Y.Opens} (h : V ≤ U) (u : Γ(Y, U)ˣ) {Q : Y.Opens} (hQ : Q ≤ V) :
    rsT ((res h u : Γ(Y, V)ˣ) : Γ(Y, V)) Q = rsT (u : Γ(Y, U)) Q :=
  rsT_resG h (u : Γ(Y, U)) hQ

theorem rsT_pullU_val {Y Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens) (u : Γ(Y, U)ˣ) {Q : Z.Opens}
    (hQ : Q ≤ f ⁻¹ᵁ U) : rsT ((pullU f U u : Γ(Z, f ⁻¹ᵁ U)ˣ) : Γ(Z, f ⁻¹ᵁ U)) Q = pbT f (u : Γ(Y, U)) Q :=
  rsT_app f U (u : Γ(Y, U)) hQ

theorem rsT_pull_g {Y Z : Scheme.{0}} (L : LB Y) (f : Z ⟶ Y) (a b : L.ι) (Q : Z.Opens)
    (hQ : Q ≤ f ⁻¹ᵁ (L.U a ⊓ L.U b)) (hQ' : Q ≤ (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b)) :
    rsT ((L.pull f).g (fun _ => a) (fun _ => b) : Γ(Z, (L.pull f).U (fun _ => a) ⊓ (L.pull f).U (fun _ => b))) Q =
      pbT f (L.g a b : Γ(Y, L.U a ⊓ L.U b)) Q := by
  simp only [LB.pull, LB.LinComb, Finset.univ_unique, Finset.prod_singleton, zpow_one]
  erw [rsT_res_val _ _ hQ', rsT_pullU_val _ _ _ hQ]

theorem isGen_rel {B X : Scheme.{0}} (L : LB X) (π₁ π₂ : B ⟶ X) (w : LB.Iso (L.pull π₁) (L.pull π₂))
    (hw : w.IsGen) (a b : L.ι) (Q : B.Opens) (hQ1 : Q ≤ π₁ ⁻¹ᵁ (L.U a ⊓ L.U b))
    (hQ2 : Q ≤ π₂ ⁻¹ᵁ (L.U a ⊓ L.U b)) :
    rsT (w.s (fun _ => a, fun _ => a)).val Q * pbT π₁ (L.g a b).val Q =
      pbT π₂ (L.g a b).val Q * rsT (w.s (fun _ => b, fun _ => b)).val Q := by
  have hQa : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => a, fun _ => a) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).1, Set.mem_iInter.2 fun _ => (hQ1 hy).1⟩
  have hQb : Q ≤ ((L.pull π₂).div (L.pull π₁)).U (fun _ => b, fun _ => b) :=
    fun y hy => ⟨Set.mem_iInter.2 fun _ => (hQ2 hy).2, Set.mem_iInter.2 fun _ => (hQ1 hy).2⟩
  have hQab := le_inf hQa hQb
  have h := congrArg (fun u => rsT (Units.val u) Q) (hw (fun _ => a, fun _ => a) (fun _ => b, fun _ => b))
  rw [rsT_res_val _ _ hQab, Units.val_mul, rsT_mul, rsT_res_val _ _ hQab] at h
  rw [h]
  simp only [LB.div]
  rw [Units.val_mul, rsT_mul]
  erw [rsT_res_val _ _ hQab]
  have hM := rsT_pull_g L π₂ a b Q hQ2 (le_inf (hQa.trans inf_le_left) (hQb.trans inf_le_left))
  have hN := rsT_pull_g L π₁ a b Q hQ1 (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [← map_inv]
  erw [rsT_res_val _ _ hQab]
  have hI := rsT_inv_mul ((L.pull π₁).g (fun _ => a) (fun _ => b))
    (le_inf (hQa.trans inf_le_right) (hQb.trans inf_le_right))
  rw [hN] at hI
  rw [hM]
  rw [show ∀ x y z t : Γ(B, Q), x * y * z * t = x * z * (y * t) from fun _ _ _ _ => by ring]
  erw [hI]
  exact _root_.mul_one _

theorem unit_mul_one_add_eps : ∀ (k : Type) [Field k] (R : Type) [CommRing R] (P : PolAV (Sp R)) (ρ : R →+* DualNumber k) (B' : Over (Sp (DualNumber k))) [GrpObj B'] (π₁ π₂ : B'.left ⟶ P.A.left), IsGrpPullback B' P.A (spMap ρ) π₁ → IsGrpPullback B' P.A (spMap (constHom ρ)) π₂ → (∀ (Z : Scheme.{0}) (x : Z ⟶ B'.left) (y : Z ⟶ Sp k), x ≫ B'.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ π₁ = x ≫ π₂) → ∀ (A₀ : Over (Sp k)) [GrpObj A₀] (m₀ : A₀.left ⟶ P.A.left), IsGrpPullback A₀ P.A (spMap ((TrivSqZeroExt.fstHom k k k).toRingHom.comp ρ)) m₀ → ∀ pr : B'.left ⟶ A₀.left, pr ≫ m₀ = π₂ → pr ≫ A₀.hom = B'.hom ≫ spMap (algebraMap k (DualNumber k)) → ∀ {J : Type} (V : J → P.A.left.Opens) (jj : J → P.L.ι) (ed : ∀ W : P.A.left.Opens, Γ(P.A.left, W) → Γ(A₀.left, m₀ ⁻¹ᵁ W)) (pb : ∀ i, Γ(A₀.left, m₀ ⁻¹ᵁ V i)), GlobalTheory.HeatConn.IsConnK P.A P.L A₀ m₀ (fun r => (ρ r).snd) V jj ed pb → (∀ (W : P.A.left.Opens) (f : Γ(P.A.left, W)), pbT π₁ f (π₂ ⁻¹ᵁ W) = pbT π₂ f (π₂ ⁻¹ᵁ W) + constFn B'.hom (π₂ ⁻¹ᵁ W) DualNumber.eps * pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) → ∀ w : LB.Iso (P.L.pull π₁) (P.L.pull π₂), w.IsGen → ∃ κ : (DualNumber k)ˣ, ∀ i, rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) = constFn B'.hom (π₂ ⁻¹ᵁ V i) κ.val * (1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i)) := by
  intro k _ R _ P ρ B' _ π₁ π₂ h₁ _ _ A₀ _ m₀ _ pr hpr _ J V jj ed pb hconn hid w hw
  obtain ⟨-, hcov, hVU, hcoc⟩ := hconn
  have hle : ∀ W, π₂ ⁻¹ᵁ W ≤ π₁ ⁻¹ᵁ W :=
    preimage_le_of_eps B'.hom π₁ π₂ (fun W f => pbT pr (ed W f) (π₂ ⁻¹ᵁ W)) hid
  have hpre : ∀ U, π₂ ⁻¹ᵁ U = pr ⁻¹ᵁ (m₀ ⁻¹ᵁ U) := fun U => by rw [← hpr]; rfl
  have hE2 : ∀ O : B'.left.Opens, constFn B'.hom O DualNumber.eps * constFn B'.hom O DualNumber.eps = 0 :=
    fun O => constFn_eps_sq B'.hom O
  have hchart : ∀ i, π₂ ⁻¹ᵁ V i ≤ ((P.L.pull π₂).div (P.L.pull π₁)).U (fun _ => jj i, fun _ => jj i) :=
    fun i y hy => ⟨Set.mem_iInter.2 fun _ => hVU i hy, Set.mem_iInter.2 fun _ => hVU i (hle _ hy)⟩
  have hcovB : (⊤ : B'.left.Opens) ≤ ⨆ i, π₂ ⁻¹ᵁ V i := by
    have := GlobalTheory.KS.le_iSup_inf_preimage π₂ V hcov ⊤
    simpa only [top_inf_eq] using this

  let u : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i)
  let E : ∀ O : B'.left.Opens, Γ(B'.left, O) := fun O => constFn B'.hom O DualNumber.eps
  let Pf : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => pbT pr (pb i) (π₂ ⁻¹ᵁ V i)
  let t : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i => u i * (1 - E _ * Pf i)
  let s : ∀ i, Γ(B'.left, π₂ ⁻¹ᵁ V i) := fun i =>
    rsT ((w.s (fun _ => jj i, fun _ => jj i))⁻¹).val (π₂ ⁻¹ᵁ V i) * (1 + E _ * Pf i)

  have hres : ∀ i i', rsT (u i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i)) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i) inf_le_left _, rsT_pbT pr (hpre (V i)).le inf_le_left _,
      rsT_constFn B'.hom inf_le_left _⟩
  have hres' : ∀ i i', rsT (u i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (Pf i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') ∧
      rsT (E (π₂ ⁻¹ᵁ V i')) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = E (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    refine ⟨rsT_rsT (hchart i') inf_le_right _, rsT_pbT pr (hpre (V i')).le inf_le_right _,
      rsT_constFn B'.hom inf_le_right _⟩

  have key : ∀ i i', rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') =
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))) := by
    intro i i'
    have hVV : V i ⊓ V i' ≤ P.L.U (jj i) ⊓ P.L.U (jj i') := inf_le_inf (hVU i) (hVU i')
    have hQ2 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₂ ⁻¹ᵁ (V i ⊓ V i') := le_rfl
    have hQ1 : π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' ≤ π₁ ⁻¹ᵁ (V i ⊓ V i') := hQ2.trans (hle _)
    have rel := isGen_rel P.L π₁ π₂ w hw (jj i) (jj i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')
      (hQ1.trans (π₁.preimage_mono hVV)) (hQ2.trans (π₂.preimage_mono hVV))
    have h := hid (V i ⊓ V i') (rsT (P.L.g (jj i) (jj i')).val (V i ⊓ V i'))
    rw [hcoc i i', pbT_mul, pbT_sub, pbT_pbT pr m₀ (m₀.preimage_mono hVV) (hpre _).le, hpr,
      pbT_rsT pr (m₀.preimage_mono inf_le_right) (hpre _).le, pbT_rsT pr (m₀.preimage_mono inf_le_left) (hpre _).le,
      pbT_rsT π₁ hVV (hle _), pbT_rsT π₂ hVV le_rfl] at h
    have hQeq : π₂ ⁻¹ᵁ (V i ⊓ V i') = π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i' := rfl
    rw [hQeq] at h
    have hG : pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        pbT π₂ (P.L.g (jj i) (jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = 1 := by
      rw [← pbT_mul, Units.inv_mul, pbT_one π₂ (hQ2.trans (π₂.preimage_mono hVV))]
    rw [h] at rel
    linear_combination (-(rsT (w.s (fun _ => jj i', fun _ => jj i')).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') -
      rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
        (1 + E _ * (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i'))))) * hG
      - pbT π₂ ((P.L.g (jj i) (jj i'))⁻¹).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * rel

  have ht : ∀ i i', rsT (t i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (t i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    obtain ⟨a1, a2, a3⟩ := hres i i'
    obtain ⟨b1, b2, b3⟩ := hres' i i'
    simp only [t, rsT_mul, rsT_sub, rsT_one inf_le_left, rsT_one inf_le_right, a1, a2, a3, b1, b2, b3, key i i']
    linear_combination (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') *
      (pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') - pbT pr (pb i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) *
      pbT pr (pb i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) * hE2 _
  have hts : ∀ i, t i * s i = 1 := by
    intro i
    have hinv := rsT_inv_mul (w.s (fun _ => jj i, fun _ => jj i)) (hchart i)
    simp only [t, s, u]
    linear_combination (1 - E _ * Pf i * (E _ * Pf i)) * hinv - (Pf i * Pf i) * hE2 _
  have hs : ∀ i i', rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') = rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') := by
    intro i i'
    have e1 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i)
    have e2 := congrArg (fun f => rsT f (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i')) (hts i')
    simp only [rsT_mul, rsT_one inf_le_left, rsT_one inf_le_right] at e1 e2
    rw [← ht i i'] at e2
    linear_combination rsT (s i') (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e1 - rsT (s i) (π₂ ⁻¹ᵁ V i ⊓ π₂ ⁻¹ᵁ V i') * e2
  obtain ⟨T, hT⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB t ht
  obtain ⟨S, hS⟩ := GlobalTheory.KS.exists_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB s hs
  have hTS : T * S = 1 := by
    refine GlobalTheory.KS.eq_of_rsT_eq (fun i => π₂ ⁻¹ᵁ V i) (fun _ => le_top) hcovB _ _ fun i => ?_
    rw [rsT_mul, hT, hS, hts, rsT_one le_top]

  have hab : IsAbelianScheme B' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback P.isAb h₁
  have hbij := GlobalTheory.allSixLaws.1.globalFns (Sp (DualNumber k)) B' hab
  obtain ⟨x, hx⟩ := hbij.2 T
  obtain ⟨y, hy⟩ := hbij.2 S
  have hxy : x * y = 1 := hbij.1 (by rw [map_mul, hx, hy, hTS, map_one])
  refine ⟨⟨(Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x,
    (Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom y,
    by rw [← map_mul, hxy, map_one], by rw [← map_mul, _root_.mul_comm, hxy, map_one]⟩, fun i => ?_⟩
  have hκ : constFn B'.hom ⊤ ((Scheme.ΓSpecIso (CommRingCat.of (DualNumber k))).hom.hom x) = T :=
    (constFn_top_appTop B'.hom x).trans hx
  have hc := hT i
  rw [← hκ, rsT_constFn B'.hom le_top] at hc
  simp only [t, u, Pf, E] at hc
  show u i = _
  simp only [u]
  linear_combination (-(1 + constFn B'.hom (π₂ ⁻¹ᵁ V i) DualNumber.eps * pbT pr (pb i) (π₂ ⁻¹ᵁ V i))) * hc +
    (rsT (w.s (fun _ => jj i, fun _ => jj i)).val (π₂ ⁻¹ᵁ V i) * pbT pr (pb i) (π₂ ⁻¹ᵁ V i) ^ 2) * hE2 _

end GlobalTheory.ConnUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDerivationExtendsCompletedToricChartRing
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartDer

theorem logDer_extend_chartRing : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)), ∀ (U : Y.X.affineOpens) (D : logDer Y.s (Scheme.IdealSheafData.vanishingIdeal (interior Y).compl) U) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (hx : ξ (closedPoint _) ∈ genι Y ⁻¹ᵁ U.1), IsEtaleCompletion (Scheme.stalkClosedPointTo ξ).hom → (ReciprocityTheory.AnForm.R.FinalTheorems.stalkId (genBdIdeal Y) (ξ (closedPoint _))).map (Scheme.stalkClosedPointTo ξ).hom = Ideal.span {∏ i, bdParam k m d i} → ∃ D' : Derivation ℤ (ChartRing k m d) (ChartRing k m d), (∀ r, D' (((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) r) = ((Scheme.stalkClosedPointTo ξ).hom.comp (((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) (ξ (closedPoint _)) hx).hom.comp ((genι Y).app U.1).hom)) (D.1 r)) ∧ ∀ i, D' (bdParam k m d i) ∈ Ideal.span {bdParam k m d i} := by
  intro E _ _ _ H Dw l Xo c Y U D k _ m d ξ hx hE hI
  have hiso : IsIso (genι Y) := isIso_fst Y
  set x := ξ (closedPoint _) with hxdef
  obtain ⟨δ, hδ⟩ := _root_.GlobalTheory.StalkDer.derivation_extend_stalk_of_iso _ _ (genι Y) U D.1 x hx
  set g := ((gen Y).presheaf.germ (genι Y ⁻¹ᵁ U.1) x hx).hom.comp ((genι Y).app U.1).hom with hg
  have hZ : ((genBd Y : TopologicalSpace.Closeds (gen Y)) : Set (gen Y)) = (genι Y) ⁻¹' ((interior Y).compl : Set Y.X) := by
    ext z
    simp only [TopologicalSpace.Opens.coe_compl, Set.mem_preimage, Set.mem_compl_iff, SetLike.mem_coe]
    rw [mem_genBd]
    unfold GlobalTheory.LogKS.interior Model.j
    have hc : ∀ w, (Y.jQ ≫ pullback.fst Y.s (spMap (RingHom.id c.F))) w = genι Y (Y.jQ w) := fun w => rfl
    simp only [Scheme.Hom.coe_opensRange, Set.mem_range, hc]
    constructor
    · rintro h ⟨w, hw⟩
      exact h ⟨w, (genι Y).isOpenEmbedding.injective hw⟩
    · rintro h ⟨w, hw⟩
      exact h ⟨w, by rw [← hw]; rfl⟩
  have hJ := _root_.GlobalTheory.StalkVan.stalkId_vanishingIdeal_preimage _ _ (genι Y) _ (genBd Y) hZ U x hx
  have hstab : ∀ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g,
      δ a ∈ ((Scheme.IdealSheafData.vanishingIdeal (interior Y).compl).ideal U).map g := by
    intro a ha
    induction ha using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨r, hr, rfl⟩ := hy
      have := hδ r
      simp only [hg, RingHom.comp_apply] at this ⊢
      rw [this]
      exact Ideal.mem_map_of_mem _ (D.2.2 r hr)
    | zero => simp
    | add y z _ _ hy hz => rw [map_add (f := _)]; exact Ideal.add_mem _ hy hz
    | smul c y hy' hy =>
      rw [smul_eq_mul, Derivation.leibniz, smul_eq_mul, smul_eq_mul]
      exact Ideal.add_mem _ (Ideal.mul_mem_left _ _ hy) (Ideal.mul_mem_right _ _ hy')
  have hC : CharZero (ChartRing k m d) :=
    (Spec.preimage (ξ ≫ genStr Y)).hom.charZero_iff (RingHom.injective _) |>.1 inferInstance
  have hk : CharZero k := (RingHom.charZero_iff (MvPowerSeries.C_injective (σ := Fin m ⊕ Fin d) (R := k))).2 hC
  obtain ⟨D', hD'⟩ := _root_.GlobalTheory.ChartDerivation.main _ k m d (Scheme.stalkClosedPointTo ξ).hom hE δ
  refine ⟨D', fun r => ?_, _root_.GlobalTheory.ChartDerBd.deriv_bdParam_mem_span _ k m d _ δ D' _ hstab hD' (by rw [← hJ]; exact hI)⟩
  simp only [RingHom.comp_apply]
  rw [hD']
  exact congrArg _ (hδ r)

end GlobalTheory.ChartDer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemAbelianLocusToricChartIffNotMemBoundary
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj Matrix TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.PullbackSections (TanM tv)
open GlobalTheory.KS (rsT pbT C1 IsCoc IsCob)
open GlobalTheory.LogKS (IsField)
open GlobalTheory.RayEv (Ray)
open GlobalTheory.Toroidal GlobalTheory.LogKS GlobalTheory.LogKSChart GlobalTheory.Heat
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChartAbLocus

theorem mem_abLocus_iff : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Geo.Tor.Level H) (Xo : Moduli Dw l) (c : Coeff l) (Y : Model Xo c (RingHom.id c.F)) (k : Type) [Field k] (m d : ℕ) (ξ : Sp (ChartRing k m d) ⟶ gen Y) (t : SAB H (Sp (ChartRing k m d))), SABMap t Y.t (ξ ≫ genι Y) → (∀ p : Sp (ChartRing k m d), ξ p ∈ genBd Y ↔ ∏ i, bdParam k m d i ∈ p.asIdeal) → ∀ p : Sp (ChartRing k m d), p ∈ abLocus t.G ↔ ∏ i, bdParam k m d i ∉ p.asIdeal := by
  intro E _ _ _ H Dw l Xo c Y k _ m d ξ t φ hbd p
  rw [← hbd, mem_genBd_iff, not_not, ← abLocus_pullback abLocusOne Y.t.semi φ.cart.1 p]
  rfl

end GlobalTheory.ChartAbLocus
end

