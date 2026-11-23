module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZeroOfIsAffineOpen
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdBox
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullUUnitsCompatGeneric
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.DvdOfAppEqZero
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.GermDiv

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ThickeningDetermines

theorem dvd_of_app_eq_zero {R : Type} [CommRing R] (r : R) {X : Scheme.{0}} (p : X ⟶ Sp R) [Flat p]
    {U : X.Opens} (hU : IsAffineOpen U) (f : Γ(X, U))
    (hf : ((pullback.fst p (spMap (Ideal.Quotient.mk (Ideal.span {r})))).app U).hom f = 0) :
    constFn p U r ∣ f := by
  have h := ProperFunctions.mem_map_ker_of_app_eq_zero
    (IsPullback.of_hasPullback p (spMap (Ideal.Quotient.mk (Ideal.span {r})))) hU f hf
  have hk : RingHom.ker (spMap (Ideal.Quotient.mk (Ideal.span {r}))).appTop.hom ≤
      Ideal.span {(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r} := by
    intro x hx
    obtain ⟨a, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).inv).2 x
    have e := congrArg (fun q => q.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (Ideal.span {r}))))
    have h0 : Ideal.Quotient.mk (Ideal.span {r}) a = 0 :=
      (ConcreteCategory.bijective_of_isIso
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ Ideal.span {r}))).inv).1
        ((e.trans hx).trans (map_zero _).symm)
    rw [Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton] at h0
    exact Ideal.mem_span_singleton.2 (map_dvd (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom h0)
  have h' := Ideal.map_mono hk h
  rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton] at h'
  exact h'

theorem cst_zero {R : Type} [CommRing R] {Z : Scheme.{0}} (q : Z ⟶ Sp R) (z : Z) : cst q z 0 = 0 := by
  rw [cst, gs_eq q z ⊤ trivial, map_zero, map_zero, map_zero]

theorem app_eq_zero_of_dvd {R : Type} [CommRing R] (r : R) {X Y Z : Scheme.{0}} (p : X ⟶ Sp R)
    (a : Y ⟶ X) (m : Z ⟶ Y) (t : Z ⟶ Sp (R ⧸ Ideal.span {r}))
    (ht : m ≫ a ≫ p = t ≫ spMap (Ideal.Quotient.mk (Ideal.span {r})))
    (U : X.Opens) (f : Γ(X, U)) (h : ∀ y : Y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) :
    ((m ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz => ?_
  have hz' : a (m z) ∈ U := hz
  have e1 : gs (𝟙 Z) z ((m ≫ a) ⁻¹ᵁ U) (((m ≫ a).app U).hom f) = gs (m ≫ a) z U f :=
    (gs_pull (𝟙 Z) (m ≫ a) z U hz f).trans (by rw [Category.id_comp])
  have e2 : gs (m ≫ a) z U f = (m.stalkMap z).hom (gs a (m z) U f) := by
    rw [← gs_pull m a z U hz', gs_stalkMap m z _ hz', gs_pull (𝟙 Y) a (m z) U hz', Category.id_comp]
  have e3 : (m.stalkMap z).hom (cst (a ≫ p) (m z) r) = 0 := by
    rw [H1.cst_stalkMap, ht, cst_comp,
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r), cst_zero]
  obtain ⟨c, hc⟩ := h _ hz'
  rw [e1, e2, hc, map_mul, e3, zero_mul, gs_eq (𝟙 Z) z _ hz, map_zero, map_zero]

theorem main : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R), I ≤ Ideal.jacobson ⊥ → ∀ (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom] [GeometricallyConnected H.hom] (N : LB H.left), N.IsLB → ∀ (s : LB.Sec N) (r : R), r ≠ 0 → (∀ (n : ℕ) (x : (thickObj R I n H).left) (j : N.ι), (fstG I n H).left x ∈ N.U j → Geo.Tor.cst ((fstG I n H).left ≫ H.hom) x r ∣ Geo.Tor.gs (fstG I n H).left x (N.U j) (s.f j)) → ∃ s' : LB.Sec N, SecIsMul H.hom r s s' := by
  intro R _ _ _ I hI H _ _ _ N hN s r hr h
  let q := Ideal.Quotient.mk (Ideal.span {r})
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback (spMap q)).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom (spMap q)
  let I₀ := I.map q
  have hI₀ : I₀ ≤ Ideal.jacobson ⊥ := by
    refine Ideal.map_le_iff_le_comap.2 (hI.trans ?_)
    rw [Ideal.comap_jacobson_of_surjective Ideal.Quotient.mk_surjective]
    exact Ideal.jacobson_mono bot_le
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom (spMap q)))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom (spMap q)))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have : IsClosedImmersion (spMap q) :=
    IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom (spMap q)))
  let κ := (secIdeal hN s).subschemeι
  have hiso := isIso_of_isClosedImmersion_of_thickenings _ I₀ hI₀ H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.fst π κ) fun n ↦ by
      have : IsClosedImmersion (thick _ I₀ n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG I₀ n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ I₀ n)))
      let m : (thickObj _ I₀ n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG I₀ n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ I₀ n) ≫ spMap (Ideal.quotientMap (I₀ ^ (n + 1)) q
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map)))
          (by
            have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
            have e2 : (fstG I₀ n H₀).left ≫ H₀.hom =
              pullback.snd H₀.hom (thick _ I₀ n) ≫ thick _ I₀ n := pullback.condition
            rw [Category.assoc, e1, ← Category.assoc, e2, Category.assoc, Category.assoc,
              ← Spec.map_comp, ← Spec.map_comp]
            rfl)
      have hm : m ≫ (fstG I n H).left = (fstG I₀ n H₀).left ≫ π := pullback.lift_fst _ _ _
      have h0 : ∀ j, (((fstG I₀ n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j => by
        rw [← hm]
        refine app_eq_zero_of_dvd r H.hom _ m ((fstG I₀ n H₀).left ≫ H₀.hom) ?_ _ _
          fun y hy => h n y j hy
        have e1 : π ≫ H.hom = H₀.hom ≫ spMap q := pullback.condition
        rw [← Category.assoc, hm, Category.assoc, Category.assoc, e1]
      have hle : κ.ker ≤ ((fstG I₀ n H₀).left ≫ π).ker := by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0
      exact ⟨pullback.lift (fstG I₀ n H₀).left (IsClosedImmersion.lift κ _ hle)
        (IsClosedImmersion.lift_fac _ _ _).symm, pullback.lift_fst _ _ _⟩
  have hker : secIdeal hN s ≤ π.ker := by
    have e : π = (inv (pullback.fst π κ) ≫ pullback.snd π κ) ≫ κ := by
      rw [Category.assoc, ← pullback.condition, IsIso.inv_hom_id_assoc]
    rw [e]
    exact (Scheme.IdealSheafData.ker_subschemeι (secIdeal hN s)).ge.trans
      (Scheme.Hom.le_ker_comp _ _)
  refine exists_div_sec H.hom hr s fun j x hx => ?_
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ :=
    H.left.isBasis_affineOpens.exists_subset_of_mem_open hx (N.U j).isOpen
  have hle : U ≤ N.U j := hUW
  have h1 := EffCartierData.ideal_locIdeal _ _ (exists_mem_chart hN)
    (associated_germ_sec s) ⟨U, hU⟩ j hle
  have h2 := Scheme.Hom.ideal_ker_le π ⟨U, hU⟩
    (hker ⟨U, hU⟩ (h1.ge (Ideal.mem_span_singleton_self _)))
  obtain ⟨g, hg⟩ := dvd_of_app_eq_zero r H.hom hU
    ((H.left.presheaf.map (homOfLE hle).op).hom (s.f j)) h2
  have hxU' : (𝟙 H.left : H.left ⟶ H.left) x ∈ U := hxU
  refine ⟨gs (𝟙 H.left) x U g, ?_⟩
  rw [← gs_res (𝟙 H.left) x hle hxU' (s.f j), hg, gs_mul _ x U hxU',
    gs_constFn H.hom U _ x hxU', Category.id_comp]

end GlobalTheory.GermDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPhiRelSmul
section
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.ProdTorsion


open Geo.Tor in
theorem val_scale {X Y Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {z : Z} {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) (c : Γ(Y, ⊤)ˣ) (t : LB.Gen (LB.LinComb L φ ε)) (r : Z ⟶ Y) :
    val (scaleGen c t) r z J = gm r z ⊤ c * val t r z J :=
  (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z le_top (hJ.mem φ r) c) rfl)


open Geo.Tor in
theorem exists_phiRel_smul (hG : GlobalFnsSt) {R : Type} [CommRing R] [IsDomain R] {D : DegPre R}
    {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ} (p : QkPt D F k)
    (w : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k))) (hw : w.IsGen)
    (ζ : F) (hζ : ζ ≠ 0) :
    ∃ w' : LB.Gen (LB.LinComb D.P.L (DegPre.lineφ D F p.g.b) (DegPre.lineε k)), w'.IsGen ∧
      ∀ s t : Fam D F k, PhiRel D F k p w s t → PhiRel D F k p w' s (ζ • t) := by
  let u : Γ((TF (R := R) F).left, ⊤)ˣ :=
    ((Ne.isUnit hζ).map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom).unit
  have hw' := scaleGen_isGen u w hw
  refine ⟨scaleGen u w, hw', fun s t h => (phiRel_iff hG p _ hw' s _).2 ?_⟩
  intro a' β hβ T ρ z' J hJ
  have h1 := (phiRel_iff hG p w hw s t).1 h a' β hβ T ρ z' J hJ
  have hu : gs (ρ.left ≫ (fst (TF (R := R) F) D.P.A).left) z' ⊤
      ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) =
      (gm (ρ ≫ fst (TF (R := R) F) D.P.A).left z' ⊤ u).val :=
    gs_unit _ z' ⊤ trivial u
  rw [sval_smul ζ t β ρ.left z' hJ, h1, val_mul hJ, val_mul hJ, val_scale hJ, hu]
  simp only [Units.val_mul]
  ring

theorem pow_eq_one_of_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j)
    {T : Over S} (x : T ⟶ G') (k : ℕ) (h : ∀ i, (x ≫ p.pr i) ^ k = 1) : x ^ k = 1 :=
  Fan.IsLimit.hom_ext p.lim _ _ fun i => by
    haveI := p.hom i
    show (x ^ k) ≫ p.pr i = 1 ≫ p.pr i
    rw [MonObj.pow_comp, MonObj.one_comp, h]

theorem equiv_comb {B M : Type} [CommRing B] [AddCommGroup M] [Module B M] (f : M ≃ₗ[B] M) {I : Type} [Fintype I]
    (a : I → B) (v : I → M) : f (∑ l, a l • v l) = ∑ l, a l • f (v l) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul]

theorem act_comb (hG : GlobalFnsSt) {S : Scheme.{0}} (P : PolAV S) (k : ℤ) (T : Over S) (θ : ThetaGrp P.A P.L k T)
    {I : Type} [Fintype I] (a : I → Γ(T.left, ⊤)) (c : Γ(T.left, ⊤)) (t u : I → LB.Sec (LPow P.A P.L k T))
    (t₀ t₁ : LB.Sec (LPow P.A P.L k T)) (h₀ : ∀ jj, t₀.f jj = ∑ l, liftFun P.A _ (a l) * (t l).f jj)
    (hu : ∀ l t', IsActOf P.A P.L k θ (t l) t' → ∀ jj, t'.f jj = liftFun P.A _ c * (u l).f jj)
    (ha : IsActOf P.A P.L k θ t₀ t₁) (jj) : t₁.f jj = ∑ l, liftFun P.A _ (a l * c) * (u l).f jj := by
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ P k T
  have h0 : SecM.ofSec P.A t₀ = ∑ l, a l • SecM.ofSec P.A (t l) :=
    Subtype.ext (funext fun jj => (h₀ jj).trans
      (BoxSpan.comb_apply P.A P.L k _ _ (fun l => SecM.ofSec P.A (t l)) jj).symm)
  have h1 := (equiv_comb (ρ θ) _ _).symm.trans ((congrArg (ρ θ) h0).symm.trans ((hρ _ _ _).1 ha))
  refine ((congrFun (congrArg Subtype.val h1) jj).symm.trans (BoxSpan.comb_apply P.A P.L k _ _ _ jj)).trans
    (Finset.sum_congr rfl fun l _ => ?_)
  have e := hu l (SecM.toSec P.A (ρ θ (SecM.ofSec P.A (t l)))) ((hρ _ _ _).2 rfl) jj
  refine (congrArg (liftFun P.A _ (a l) * ·) e).trans ((_root_.mul_assoc _ _ _).symm.trans
    (congrArg (· * (u l).f jj) ?_))
  exact (map_mul (liftHom P.A _) _ _).symm

theorem qkToAk_box : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U), Geo.Tor.ExpBijF U.toUnifPre → Geo.Tor.ExpBijF U'.toUnifPre → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ), 1 ≤ k → ∀ (p' : QkPt D'.toPre F k) (p : Fin j → QkPt D.toPre F k), IsBoxQk pD F k p' p → ∀ (x' : TFK (R := R) F ⟶ A'.A) (x : Fin j → (TFK (R := R) F ⟶ A.A)), (∀ i, x' ≫ pA.pr i = x i) → (∀ i, QkToAkU U.toUnifPre F k (p i) (x i)) → QkToAkU U'.toUnifPre F k p' x' := by
  intro hL R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P hB hB' F _ _ k hk p' p hp x' x hx h w' hw'
  have hG := hL.globalFns
  obtain ⟨w, hw⟩ := U.ext
  have hk1 : x' ^ k = 1 := pow_eq_one_of_pr pA.toIsPowGrp x' k fun i => by
    rw [hx i]; exact (h i w hw).1
  refine ⟨hk1, fun θ' hθ' => ?_⟩
  obtain ⟨θ, c, hc, hθ, hact⟩ := BoxTheta.box_theta_act hL R j A A' pA F k hk θ' (hθ' ▸ hk1)
  choose v hv hΦ using fun i => (h i w hw).2 (θ i) ((hθ i).trans (hθ' ▸ hx i))
  obtain ⟨V, hV, hVΦ⟩ := BoxPhi.phiRel_box hG R j D.toPre D'.toPre pD F k p' p hp v hv
  obtain ⟨Φ, hΦl⟩ := phiFun_of_globalFns hG R I D' F k hk p' V hV
  obtain ⟨V', hV', hV'Φ⟩ := exists_phiRel_smul hG p' V hV c hc
  obtain ⟨c₀, -, hexp⟩ := BoxExpansion.main hG R I j D D' A A' G G' pD pA pG U' U P w hw w' hw' F k
  obtain ⟨ρ, hρ, -⟩ := thetaGrp_acts_linearly hG _ A k (TFK (R := R) F)
  refine ⟨V', hV', fun t₀ t₁ s₀ s₁ e₀ e₁ ha => ?_⟩
  obtain ⟨n, a, t, t', hbox, hsum⟩ := boxProduct_span hL R j A A' pA F k hk t₀
  let u : Fin n → Fin j → LB.Sec (LPow A.A A.L (k : ℤ) (TFK (R := R) F)) :=
    fun l i => SecM.toSec A.A (ρ (θ i) (SecM.ofSec A.A (t l i)))
  have hu : ∀ l i, IsActOf A.A A.L (k : ℤ) (θ i) (t l i) (u l i) := fun l i => (hρ _ _ _).2 rfl
  choose u' hu' using fun l => exists_boxSec_pow_ext R j A A' pA F k (u l)
  choose s hs using fun l i => ((hB F k hk w hw).1 (t l i)).exists
  choose r hr using fun l i => ((hB F k hk w hw).1 (u l i)).exists
  choose S hS using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (s l)
  choose S₁ hS₁ using fun l => BoxFamily.exists_isBoxFam hG R j D.toPre D'.toPre pD F k (r l)
  have hSS : ∀ l, S₁ l = Φ (S l) := fun l => (hΦl _ _).1
    (hVΦ (s l) (r l) _ _ (fun i => hΦ i _ _ _ _ (hs l i) (hr l i) (hu l i)) (hS l) (hS₁ l))
  have E₀ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n a t' (fun l => c₀ • S l) t₀
    (fun l => hexp (t l) (s l) (t' l) (S l) (hs l) (hbox l) (hS l)) hsum
  have hsum₁ := act_comb hG A' k (TFK (R := R) F) θ' (fun l => (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom (a l))
    ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom c) t' u' t₀ t₁ hsum
    (fun l t'' h'' => hact (t l) (u l) (t' l) (u' l) t'' (hbox l) (hu' l) (hu l) h'') ha
  have E₁ := ExpansionLinear.expandsF_sum R I D' A' G' U'.toUnifPre F k w' hw' n (fun l => a l * c) u'
    (fun l => c₀ • S₁ l) t₁ (fun l => hexp (u l) (r l) (u' l) (S₁ l) (hr l) (hu' l) (hS₁ l))
    (fun jj => (hsum₁ jj).trans (Finset.sum_congr rfl fun l _ => by rw [map_mul]; rfl))
  have q₀ := ((hB' F k hk w' hw').1 t₀).unique e₀ E₀
  have q₁ := ((hB' F k hk w' hw').1 t₁).unique e₁ E₁
  have q : s₁ = c • Φ s₀ := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [q₁, q₀, map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hSS, map_smul, map_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    ring
  rw [q]
  exact hV'Φ _ _ ((hΦl _ _).2 rfl)

end GlobalTheory.ProdTorsion
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsPowOAct
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.TauBalBox

private theorem hom_ext_of_isPowGrp_pr {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) {T : Over S} {a b : T ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b := by
  apply p.lim.hom_ext
  rintro ⟨i⟩
  first
  | exact h i
  | simpa using h i

theorem exists_pow_oAct : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (O : Type) [CommRing O] [StarRing O] [Module O D.X] [Module O D'.X], (∀ (a : O) (x : D'.X), pD.xe (a • x) = a • pD.xe x) → ∀ oa : D.OAct O, ∃ oa' : D'.OAct O, ∀ a i, oa'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ oa.onB.act a := by
  intro hG R _ _ j D D' pD O _ _ _ _ hxe oa
  obtain ⟨⟨oB, hros⟩, hc, htau⟩ := oa
  letI := D.P.isAb.comm
  letI := D'.P.isAb.comm
  obtain ⟨r', hr'⟩ := (GlobalTheory.exists_powAct _ D'.P.A D.P.A j pD.pw).1 O oB
  have hros' : ∀ a : O, RosatiAdj D'.P.A D'.P.L (r'.act a) (r'.act (star a)) := fun a =>
    GlobalTheory.rosatiAdj_pow _ D'.P.A D.P.A j pD.pw D.P.L D'.P.L D.P.isLB D'.P.isLB ⟨pD.w, pD.w_gen⟩
      (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a)) (hr' a) (hr' (star a)) (hros a)
  have hc' : ∀ (a : O) (y : D'.X), D'.c (a • y) = D'.c y ≫ r'.act a := by
    intro a y
    apply hom_ext_of_isPowGrp_pr pD.pw
    intro i
    rw [pD.c_pr, Category.assoc, hr' a i, ← Category.assoc, pD.c_pr, hxe, Pi.smul_apply, hc]
  have htau' : ∀ a : O, D'.TauBal (r'.act a) (r'.act (star a)) (fun y => a • y) fun y => star a • y := by
    intro a
    haveI := oB.hom a
    haveI := oB.hom (star a)
    haveI := r'.hom a
    haveI := r'.hom (star a)
    exact tauBal_pow hG R j D D' pD (oB.act a) (oB.act (star a)) (r'.act a) (r'.act (star a))
      inferInstance inferInstance inferInstance inferInstance (hr' a) (hr' (star a)) (hros a)
      (fun y => a • y) (fun y => star a • y) (fun y => a • y) (fun y => star a • y)
      (fun x i => by simp only [hxe, Pi.smul_apply]) (fun x i => by simp only [hxe, Pi.smul_apply])
      (hc a) (hc (star a)) (htau a)
  exact ⟨⟨⟨r', hros'⟩, hc', htau'⟩, hr'⟩

end GlobalTheory.TauBalBox
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PowPullbackHomExt
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PowOLinear

theorem pow_hom_ext {S : Scheme.{0}} {G' G Z : Over S} [GrpObj G'] [GrpObj G] {j : ℕ}
    (p : IsPowGrp G' G j) {a b : Z ⟶ G'} (h : ∀ i, a ≫ p.pr i = b ≫ p.pr i) : a = b :=
  Fan.IsLimit.hom_ext p.lim a b h

theorem pow_pullback_hom_ext {S S' : Scheme.{0}} (f : S' ⟶ S) {G' G : Over S} [GrpObj G']
    [GrpObj G] {j : ℕ} (p : IsPowGrp G' G j) {Z : Over S'} {a b : Z ⟶ (Over.pullback f).obj G'}
    (h : ∀ i, a ≫ (Over.pullback f).map (p.pr i) = b ≫ (Over.pullback f).map (p.pr i)) : a = b :=
  (isLimitOfPreserves (Over.pullback f) p.lim).hom_ext fun i => h i.as

theorem res_pullU_val {S : Scheme.{0}} {X : Type} [AddCommGroup X] {Z : Over S}
    (g : Z ⟶ splitTorus S X) (χ : X) (h : ⊤ ≤ g.left ⁻¹ᵁ ⊤) :
    (res h (pullU g.left ⊤ (charUnit S X χ))).val = g.left.appTop.hom (charUnit S X χ).val := by
  have : (res h (pullU g.left ⊤ (charUnit S X χ))).val =
      (g.left.appLE ⊤ ⊤ h).hom (charUnit S X χ).val := rfl
  rw [this, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]; rfl

theorem charUnit_zero {S : Scheme.{0}} {X : Type} [AddCommGroup X] :
    (charUnit S X 0).val = 1 := by
  have h := SplitTorusHom.charUnit_add (S := S) (0 : X) 0
  rw [add_zero] at h
  exact ((charUnit S X 0).isUnit.mul_eq_left.mp h.symm)

theorem torusEndOf_pow {S : Scheme.{0}} {X X' : Type} [AddCommGroup X] [AddCommGroup X'] {j : ℕ}
    (xe : X' ≃+ (Fin j → X)) (pr : Fin j → (splitTorus S X' ⟶ splitTorus S X))
    (hpr : ∀ (i : Fin j) (χ : X),
      res (fun x _ => show (pr i).left.base x ∈ (⊤ : TopologicalSpace.Opens _) from trivial)
        (pullU (pr i).left ⊤ (charUnit S X χ)) = charUnit S X' (xe.symm (Pi.single i χ)))
    (h : X →+ X) (h' : X' →+ X') (hh : ∀ x i, xe (h' x) i = h (xe x i))
    (t : splitTorus S X ⟶ splitTorus S X) (ht : TorusEndOf X h t)
    (t' : splitTorus S X' ⟶ splitTorus S X') (htt : ∀ i, t' ≫ pr i = pr i ≫ t) :
    TorusEndOf X' h' t' := by
  have hpr' : ∀ i χ, (pr i).left.appTop.hom (charUnit S X χ).val =
      (charUnit S X' (xe.symm (Pi.single i χ))).val := fun i χ =>
    (res_pullU_val (pr i) χ _).symm.trans (congrArg Units.val (hpr i χ))
  have ht' : ∀ χ, t.left.appTop.hom (charUnit S X χ).val = (charUnit S X (h χ)).val := fun χ =>
    (res_pullU_val t χ _).symm.trans (congrArg Units.val (ht χ))
  have key : ∀ y : Fin j → X, t'.left.appTop.hom (charUnit S X' (xe.symm y)).val =
      (charUnit S X' (h' (xe.symm y))).val := by
    intro y
    induction y using Pi.single_induction with
    | zero => rw [map_zero, map_zero, charUnit_zero, map_one]
    | add u v hu hv =>
      rw [map_add (f := _), map_add (f := _), SplitTorusHom.charUnit_add, SplitTorusHom.charUnit_add, map_mul, hu, hv]
    | single i χ =>
      have e : h' (xe.symm (Pi.single i χ)) = xe.symm (Pi.single i (h χ)) := by
        apply xe.injective
        funext k
        rw [hh, xe.apply_symm_apply, xe.apply_symm_apply]
        by_cases hk : k = i
        · subst hk; simp
        · simp [Pi.single_eq_of_ne hk]
      rw [e, ← hpr', ← hpr', ← SplitTorusHom.appTop_comp, htt, SplitTorusHom.appTop_comp, ht']
  intro x
  apply Units.ext
  refine (res_pullU_val t' x _).trans ?_
  have := key (xe x)
  rwa [xe.symm_apply_apply] at this

end PowOLinear


open PowOLinear in
theorem oLinear_of_unifPow : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (j : ℕ) (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G G' : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GrpObj G'] [IsCommMonObj G'] (pD : IsPowDeg D'.toPre D.toPre j) (pA : IsPowPolAV A' A j) (pG : IsPowGrp G' G j) (U' : Unif I D' A' G') (U : Unif I D A G) (P : UnifPowOf3 pD pA pG U' U) (O : Type) [CommRing O] [StarRing O] [Module O D.toPre.X] [Module O D'.toPre.X], (∀ (a : O) (x : D'.toPre.X), pD.xe (a • x) = a • pD.xe x) → ∀ (ιD : D.OAct O) (ιD' : D'.OAct O) (ιA : A.OAct O) (ιA' : A'.OAct O) (ιG : RingAct G O) (ιG' : RingAct G' O), (∀ a i, ιD'.onB.act a ≫ pD.pw.pr i = pD.pw.pr i ≫ ιD.onB.act a) → (∀ a i, ιA'.act a ≫ pA.pr i = pA.pr i ≫ ιA.act a) → (∀ a i, ιG'.act a ≫ pG.pr i = pG.pr i ≫ ιG.act a) → U.OLinear O ιD ιA ιG → U'.OLinear O ιD' ιA' ιG' := by
  intro R _ _ I j D D' A A' G G' _ _ _ _ pD pA pG U' U P O _ _ _ _ hxe ιD ιD' ιA ιA' ιG ιG'
    hD hA hG hU
  refine ⟨fun a => ?_, fun e a => ?_, fun e a => ?_⟩
  · refine pow_hom_ext pA.toIsPowGrp fun i => ?_
    rw [Category.assoc, Category.assoc, hA, P.gen_pr, ← Category.assoc U'.gen.hom, P.gen_pr,
      ← Functor.map_comp_assoc, hG, Functor.map_comp_assoc, hU.ext, Category.assoc]
  · refine pow_pullback_hom_ext (thick R I e) pD.pw fun i => ?_
    have h₁ := P.q_pr e i
    have h₂ := hU.q_lin e a
    have h₃ := congrArg (Over.pullback (thick R I e)).map (hD a i)
    have h₄ := congrArg (Over.pullback (thick R I e)).map (hG a i)
    rw [Functor.map_comp, Functor.map_comp] at h₃ h₄
    refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
    rw [h₃, h₁, ← Category.assoc, h₄, Category.assoc, h₂, ← Category.assoc, ← h₁, Category.assoc]
  · obtain ⟨pT, hi, hc⟩ := _root_.GlobalTheory.PowTorus.torus_isPow R I j D D' A A' G G' pD pA pG U' U P e
    obtain ⟨t, ht, hti⟩ := hU.i_lin e a
    obtain ⟨t', ht'⟩ : ∃ t' : splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X ⟶
        splitTorus (Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) D'.toPre.X,
        ∀ i, t' ≫ pT.pr i = pT.pr i ≫ t :=
      ⟨Fan.IsLimit.lift pT.lim fun i => pT.pr i ≫ t, fun i => Fan.IsLimit.fac pT.lim _ i⟩
    refine ⟨t', ?_, ?_⟩
    · exact torusEndOf_pow pD.xe pT.pr hc (DistribSMul.toAddMonoidHom _ (star a))
        (DistribSMul.toAddMonoidHom _ (star a)) (fun x i => congrFun (hxe (star a) x) i) t ht t' ht'
    · refine pow_pullback_hom_ext (thick R I e) pG fun i => ?_
      have h₄ := congrArg (Over.pullback (thick R I e)).map (hG a i)
      rw [Functor.map_comp, Functor.map_comp] at h₄
      refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
      rw [h₄, hi, ← Category.assoc, hi, Category.assoc, hti, ← Category.assoc, ← ht', Category.assoc]

end GlobalTheory
end

