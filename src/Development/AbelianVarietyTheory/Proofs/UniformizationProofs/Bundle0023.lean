module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SecEqZeroAndHomEqOfThickenings
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0015
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.WeightedChartPullback.WeightIndep
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.VanishOfTermsVanish
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifBaseChangeSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.BoxLeOfComp
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0009

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AbelianPartIsoIsMonHomAndRigidified
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace AbelianPartIso

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR

theorem isMonHom_of_comp {S : Scheme.{0}} {G B B' : Over S} [GrpObj G] [GrpObj B] [GrpObj B']
    (q' : G ⟶ B') (q : G ⟶ B) (β : B' ⟶ B) [IsMonHom q'] [IsMonHom q] [Flat q'.left]
    [Surjective q'.left] (hβ : q' ≫ β = q) : IsMonHom β := by
  refine ⟨?_, ?_⟩
  · rw [← IsMonHom.one_hom q', Category.assoc, hβ, IsMonHom.one_hom]
  · have := FlatQuotient.epi_tensorHom q' q'
    rw [← cancel_epi (q' ⊗ₘ q'), ← IsMonHom.mul_hom_assoc, hβ, tensorHom_comp_tensorHom_assoc, hβ,
      IsMonHom.mul_hom]

theorem hom_eq_of_map_eq {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] {Y : Over (Spec (CommRingCat.of R))} [IsSeparated Y.hom]
    (f g : H ⟶ Y)
    (h : ∀ n, (Over.pullback (thick R I n)).map f = (Over.pullback (thick R I n)).map g) : f = g := by
  refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI H).2 Y f g fun n => ?_
  have k : ∀ f : H ⟶ Y, ((Over.pullback (thick R I n)).map f).left ≫ pullback.fst Y.hom (thick R I n) =
      pullback.fst H.hom (thick R I n) ≫ f.left := fun f => pullback.lift_fst _ _ _
  exact (k f).symm.trans ((congrArg (fun φ => φ.left ≫ pullback.fst Y.hom (thick R I n)) (h n)).trans (k g))

theorem isMonHom_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] {I : Ideal R}
    (hI : I ≤ Ideal.jacobson ⊥) {B B' : Over (Spec (CommRingCat.of R))} [GrpObj B] [GrpObj B']
    (hB : IsAbelianScheme B) (hB' : IsAbelianScheme B') (f : B' ⟶ B)
    (h : ∀ n, IsMonHom ((Over.pullback (thick R I n)).map f)) : IsMonHom f := by
  have := hB.proper
  have := hB'.smooth
  have := hB'.geomConnected
  refine ⟨?_, ?_⟩
  · have : Smooth (𝟙_ (Over (Spec (CommRingCat.of R)))).hom := inferInstanceAs (Smooth (𝟙 _))
    have : GeometricallyConnected (𝟙_ (Over (Spec (CommRingCat.of R)))).hom :=
      inferInstanceAs (GeometricallyConnected (𝟙 _))
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).one_hom
    rw [Functor.obj.η_def, Functor.obj.η_def, Category.assoc, cancel_epi, ← Functor.map_comp] at e
    exact e
  · have : Smooth (B' ⊗ B').hom := inferInstanceAs (Smooth (pullback.fst B'.hom B'.hom ≫ B'.hom))
    have : GeometricallyConnected (B' ⊗ B').hom := by
      change GeometricallyConnected (pullback.fst B'.hom B'.hom ≫ B'.hom)
      exact GeometricallyConnected.comp _ _
    refine hom_eq_of_map_eq hI _ _ _ fun n => ?_
    have e := (h n).mul_hom
    rw [Functor.obj.μ_def, Functor.obj.μ_def, Category.assoc, Functor.LaxMonoidal.μ_natural_assoc,
      cancel_epi, ← Functor.map_comp, ← Functor.map_comp] at e
    exact e

theorem fn_eq_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤)
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ (e : ℕ) (z), gs (thick R I e) z W a = gs (thick R I e) z W b) : a = b := by
  subst hW
  have hinj : Function.Injective (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  apply hinj
  rw [← sub_eq_zero, ← Ideal.mem_bot, ← Ideal.iInf_pow_eq_bot_of_isLocalRing I hI, Ideal.mem_iInf]
  intro e
  refine Ideal.pow_le_pow_right (Nat.le_succ e) (Ideal.Quotient.eq.1 ?_)
  have key : ((thick R I e).app ⊤).hom a = ((thick R I e).app ⊤).hom b := by
    refine fn_ext fun z hz => ?_
    rw [gs_pull _ _ z ⊤ trivial, gs_pull _ _ z ⊤ trivial, Category.id_comp]
    exact h e z
  have nat := fun x => congrArg (fun φ => φ.hom x)
    (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at nat
  exact (nat a).symm.trans ((congrArg _ key).trans (nat b))

theorem pmaps_of_thickenings {R : Type} [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    {I : Ideal R} (hI : I ≠ ⊤) {X X' : Scheme.{0}} {L : LB X} {L' : LB X'} (hL : L.IsLB)
    (hL' : L'.IsLB) {F : X' ⟶ X} (w : LB.Iso L' (L.pull F)) (hw : w.IsGen)
    (s' : Spec (CommRingCat.of R) ⟶ X') (s : Spec (CommRingCat.of R) ⟶ X) (hs : s' ≫ F = s)
    (a : LB.Gen (L'.pull s')) (ha : a.IsGen) (t : LB.Gen (L.pull s)) (ht : t.IsGen)
    (h : ∀ (e : ℕ) (z) (p : L.ι) (q : L'.ι), (thick R I e ≫ s) z ∈ L.U p →
      (thick R I e ≫ s') z ∈ L'.U q →
      gm (thick R I e) z ((L.pull s).U (fun _ => p)) (t.s (fun _ => p)) =
        gw w (thick R I e ≫ s') z p q *
          gm (thick R I e) z ((L'.pull s').U (fun _ => q)) (a.s (fun _ => q))) :
    PMaps w (K := PUnit) (fun _ => s') (fun _ => s) (fun _ => 1) a t (𝟙 _) := by
  subst hs
  obtain ⟨p₀, hp₀⟩ := exists_chart hL ((s' ≫ F) (IsLocalRing.closedPoint R))
  obtain ⟨q₀, hq₀⟩ := exists_chart hL' (s' (IsLocalRing.closedPoint R))
  have hp : ∀ x, (s' ≫ F) x ∈ L.U p₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map (s' ≫ F).continuous).mem_open
      (L.U p₀).isOpen hp₀
  have hq : ∀ x, s' x ∈ L'.U q₀ := fun x =>
    ((IsLocalRing.specializes_closedPoint (R := R) x).map s'.continuous).mem_open
      (L'.U q₀).isOpen hq₀
  have l₁ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L.pull (s' ≫ F)).U (fun _ => p₀) :=
    fun x _ => mem_pull.2 (hp x)
  have l₂ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤ (L'.pull s').U (fun _ => q₀) :=
    fun x _ => mem_pull.2 (hq x)
  have l₃ : (⊤ : (Spec (CommRingCat.of R)).Opens) ≤
      s' ⁻¹ᵁ ((L.pull F).U (fun _ => p₀) ⊓ L'.U q₀) :=
    fun x _ => ⟨mem_pull.2 (hp x), hq x⟩
  have ev₁ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₁ (t.s (fun _ => p₀))) =
        gm r z ((L.pull (s' ≫ F)).U (fun _ => p₀)) (t.s (fun _ => p₀)) :=
    fun Z r z => gm_res r z l₁ trivial _
  have ev₂ : ∀ (Z : Scheme.{0}) (r : Z ⟶ Spec (CommRingCat.of R)) (z : Z),
      gm r z ⊤ (res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀))) =
        gw w (r ≫ s') z p₀ q₀ * gm r z ((L'.pull s').U (fun _ => q₀)) (a.s (fun _ => q₀)) :=
    fun Z r z => (map_mul _ _ _).trans (congrArg₂ (· * ·)
      ((gm_res r z l₃ trivial _).trans (gm_pull r s' z _ (l₃ (Set.mem_univ (r z))) _))
      (gm_res r z l₂ trivial _))
  have key : res l₁ (t.s (fun _ => p₀)) =
      res l₃ (pullU s' _ (w.s (fun _ => p₀, q₀))) * res l₂ (a.s (fun _ => q₀)) := by
    refine Units.ext (fn_eq_of_thickenings hI ⊤ rfl _ _ fun e z => ?_)
    rw [gs_unit _ z ⊤ trivial, gs_unit _ z ⊤ trivial, ev₁, ev₂, h e z p₀ q₀ (hp _) (hq _)]
  intro Z r z p q hpz hqz
  have E := (ev₁ Z r z).symm.trans ((congrArg (gm r z ⊤) key).trans (ev₂ Z r z))
  have a₁ := gen_trans ht r z (j := p) (j' := fun _ => p₀) (Set.mem_iInter.2 hpz) (l₁ (Set.mem_univ _))
  have a₂ := gen_trans ha r z (j := q) (j' := fun _ => q₀) (Set.mem_iInter.2 hqz) (l₂ (Set.mem_univ _))
  have a₃ := (isGen_iff w).1 hw Z (r ≫ s') z (p PUnit.unit) p₀ (q PUnit.unit) q₀ (hpz _) (hp _)
    (hqz _) (hq _)
  rw [Category.comp_id, a₁, a₂, Fintype.prod_unique, zpow_one, a₃]
  refine (congrArg _ E).trans ?_
  simp only [trF, Fintype.prod_unique, zpow_one, Category.assoc, PUnit.default_eq_unit]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

end AbelianPartIso


open AbelianPartIso ReciprocityTheory.ChartRestriction.G.DVR in
theorem abelianPartIso_isMonHom_and_rigidified : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso D'.toPre.P.L (D.toPre.P.L.pull Φ.hom.left)), (w.IsGen ∧ ∀ e : ℕ, (U'.gt e).pG.left ≫ Φ.hom.left = (U.gt e).pG.left ∧ (∀ (Z : Scheme.{0}) (r : Z ⟶ (thickObj R I e G).left) (z : Z) (jM : D.toPre.P.L.ι) (jM' : D'.toPre.P.L.ι) (jL : U.LG.L.ι) (jL' : U'.LG.L.ι), (U.gt e).pG.left (r z) ∈ D.toPre.P.L.U jM → (U'.gt e).pG.left (r z) ∈ D'.toPre.P.L.U jM' → (fstG I e G).left (r z) ∈ U.LG.L.U jL → (fstG I e G).left (r z) ∈ U'.LG.L.U jL' → Geo.Tor.gw w (r ≫ (U'.gt e).pG.left) z jM jM' * Geo.Tor.gw (U'.w e) r z jM' (fun _ => jL') = Geo.Tor.gw (U.w e) r z jM (fun _ => jL) * Geo.Tor.gw wL (r ≫ (fstG I e G).left) z jL jL')) → (IsMonHom Φ.hom ∧ Geo.Tor.PMaps w (K := PUnit) (fun _ => eSec D'.toPre.P.A) (fun _ => eSec D.toPre.P.A) (fun _ => 1) D'.toPre.rig D.toPre.rig (𝟙 _)) := by
  intro R _ _ _ I hR D D' A A' G _ _ _ U U' wL he hwL hrig Φ w ⟨hw, H⟩
  obtain ⟨_, -, -, _⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  have hI' : I ≠ ⊤ := fun h => (IsLocalRing.maximalIdeal.isMaximal R).ne_top
    (top_le_iff.1 (h.ge.trans (hI.trans (IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top).le)))
  have hΦ : IsMonHom Φ.hom := by
    refine isMonHom_of_thickenings hI D.toPre.P.isAb D'.toPre.P.isAb Φ.hom fun e => ?_
    have := (U.gt e).q_hom
    have := (U'.gt e).q_hom
    have := (U'.gt e).q_flat
    have := (U'.gt e).q_surj
    refine isMonHom_of_comp (U'.gt e).q (U.gt e).q _ (Over.OverMorphism.ext ?_)
    refine pullback.hom_ext ?_ ?_
    · have k : ((Over.pullback (thick R I e)).map Φ.hom).left ≫
          pullback.fst D.toPre.P.A.hom (thick R I e) =
          pullback.fst D'.toPre.P.A.hom (thick R I e) ≫ Φ.hom.left := pullback.lift_fst _ _ _
      exact (Category.assoc _ _ _).trans ((congrArg ((U'.gt e).q.left ≫ ·) k).trans
        ((Category.assoc _ _ _).symm.trans (H e).1))
    · exact (Over.w _).trans (Over.w (U.gt e).q).symm
  refine ⟨hΦ, pmaps_of_thickenings hI' D.toPre.P.isLB D'.toPre.P.isLB w hw _ _
    (congrArg Over.Hom.left hΦ.one_hom) _ D'.toPre.rig_gen _ D.toPre.rig_gen
    fun e z p q hp hq => ?_⟩
  obtain ⟨j, hj⟩ := Geo.Tor.exists_chart U.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  obtain ⟨j', hj'⟩ := Geo.Tor.exists_chart U'.LG.isLB ((UnitValue.thU R I e ≫ eSec G) z)
  have e₁ := UnitValue.wv_rig U e z p j hp hj
  have e₂ := UnitValue.wv_rig U' e z q j' hq hj'
  have e₃ := (Geo.Tor.maps_iff wL _ (fun _ => eSec G) _ U'.LG.rig U.LG.rig (𝟙 _) _
    (rigPull_le (𝟙 G.left) (𝟙 _) he U.LG.L) (fun _ => rfl)).1 hrig _ (UnitValue.thU R I e) z
    (fun _ => j) (fun _ => j') (fun _ => hj) (fun _ => hj')
  have e₄ := (H e).2 _ (eSec (thickObj R I e G)) z p q j j'
    ((congrArg (fun g => g z ∈ D.toPre.P.L.U p) (UnitValue.eSec_pGl U e)).mpr hp)
    ((congrArg (fun g => g z ∈ D'.toPre.P.L.U q) (UnitValue.eSec_pGl U' e)).mpr hq)
    ((congrArg (fun g => g z ∈ U.LG.L.U j) (UnitValue.eSec_fGl (G := G) e)).mpr hj)
    ((congrArg (fun g => g z ∈ U'.LG.L.U j') (UnitValue.eSec_fGl (G := G) e)).mpr hj')
  rw [UnitValue.eSec_pGl U' e, UnitValue.eSec_fGl (G := G) e] at e₄
  rw [Category.comp_id, Fintype.prod_unique, zpow_one] at e₃
  refine e₁.symm.trans ((congrArg _ e₃).trans ((mul_assoc _ _ _).symm.trans ?_))
  exact (congrArg (· * _) e₄.symm).trans ((mul_assoc _ _ _).trans (congrArg _ e₂))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AppCompEqZeroOfGermDvd
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Geo.Tor in
theorem app_comp_eq_zero_of_germ_dvd {R : Type} [CommRing R] {X Y Z : Scheme.{0}}
    (p : X ⟶ Spec (CommRingCat.of R)) (a : Y ⟶ X) (b : Z ⟶ Y) (r : R)
    (hr : ∀ z, cst (b ≫ a ≫ p) z r = 0) (U : X.Opens) (f : Γ(X, U))
    (h : ∀ y, a y ∈ U → cst (a ≫ p) y r ∣ gs a y U f) : ((b ≫ a).app U).hom f = 0 := by
  refine fn_ext fun z hz ↦ ?_
  have hz' : b z ∈ a ⁻¹ᵁ U := hz
  have key : ∀ {W : Scheme.{0}} (c : Y ⟶ W) (V : W.Opens) (g : Γ(W, V)), c (b z) ∈ V →
      gs (b ≫ c) z V g = (b.stalkMap z).hom (gs c (b z) V g) := fun c V g hV ↦ by
    rw [← gs_pull b c z V hV, gs_stalkMap b z _ hV, gs_pull (𝟙 Y) c (b z) V hV, Category.id_comp]
  obtain ⟨t, ht⟩ := h (b z) hz'
  have h0 : (b.stalkMap z).hom (cst (a ≫ p) (b z) r) = 0 :=
    (key (a ≫ p) ⊤ _ trivial).symm.trans (hr z)
  rw [gs_pull (𝟙 Z) (b ≫ a) z U hz, Category.id_comp, key a U f hz', ht, map_mul, h0, zero_mul,
    ThickeningDivisible.gs_zero]


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Cartier EffCartierData ThickeningDetermines
  ThickeningDivisible in
theorem sec_div_of_germ_dvd (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (I : Ideal R)
    (hI : I ≤ Ideal.jacobson ⊥) (H : Over (Spec (CommRingCat.of R))) [GrpObj H] [Smooth H.hom]
    [GeometricallyConnected H.hom] (N : LB H.left) (hN : N.IsLB) (s : LB.Sec N) (r : R) (hr : r ≠ 0)
    (hs : ∀ (n : ℕ) (j : N.ι) (y : (thickObj R I n H).left), (fstG I n H).left y ∈ N.U j →
      cst (Z := (thickObj R I n H).left) ((fstG I n H).left ≫ H.hom) y r ∣
        gs (Y := (thickObj R I n H).left) (fstG I n H).left y (N.U j) (s.f j)) :
    ∃ s' : LB.Sec N, ∀ j, s.f j = resTop _ (scal H.hom r) * s'.f j := by
  let φ : R →+* R ⧸ Ideal.span {r} := Ideal.Quotient.mk _
  let q := Spec.map (CommRingCat.ofHom φ)
  let H₀ : Over (Spec (CommRingCat.of (R ⧸ Ideal.span {r}))) := (Over.pullback q).obj H
  let π : H₀.left ⟶ H.left := pullback.fst H.hom q
  have : IsClosedImmersion q := IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
  have : Smooth H₀.hom := inferInstanceAs (Smooth (pullback.snd H.hom q))
  have : GeometricallyConnected H₀.hom :=
    inferInstanceAs (GeometricallyConnected (pullback.snd H.hom q))
  have := grpObj_geometricallyIntegral_of_smooth _ H₀
  have key := isIso_of_isClosedImmersion_of_thickenings _ (I.map φ)
    (map_le_jacobson φ Ideal.Quotient.mk_surjective hI) H₀ η[H₀] (fun p ↦ inferInstance)
    _ (pullback.snd (secIdeal hN s).subschemeι π) fun n ↦ by
      have : IsClosedImmersion (thick _ (I.map φ) n) :=
        IsClosedImmersion.spec_of_surjective _ Ideal.Quotient.mk_surjective
      have : QuasiCompact (fstG (I.map φ) n H₀).left :=
        inferInstanceAs (QuasiCompact (pullback.fst H₀.hom (thick _ (I.map φ) n)))
      have : QuasiCompact π := inferInstanceAs (QuasiCompact (pullback.fst H.hom q))
      have hπ : π ≫ H.hom = H₀.hom ≫ q := pullback.condition
      let b : (thickObj _ (I.map φ) n H₀).left ⟶ (thickObj R I n H).left :=
        pullback.lift ((fstG (I.map φ) n H₀).left ≫ π)
          (pullback.snd H₀.hom (thick _ (I.map φ) n) ≫
            Spec.map (CommRingCat.ofHom (Ideal.quotientMap ((I.map φ) ^ (n + 1)) φ
            (by rw [← Ideal.map_pow]; exact Ideal.le_comap_map))))
          (by
            rw [Category.assoc, hπ, Category.assoc, ← Spec.map_comp, ← Category.assoc]
            erw [pullback.condition]
            rw [Category.assoc, ← Spec.map_comp]
            rfl)
      have hb : b ≫ (fstG I n H).left = (fstG (I.map φ) n H₀).left ≫ π := pullback.lift_fst _ _ _
      have h0 : ∀ j, (((fstG (I.map φ) n H₀).left ≫ π).app _).hom (s.f j) = 0 := fun j ↦ by
        rw [← hb]
        refine app_comp_eq_zero_of_germ_dvd H.hom _ b r (fun z ↦ ?_) _ _ (hs n j)
        rw [← Category.assoc, hb, Category.assoc, hπ, ← Category.assoc]
        exact cst_comp_eq_zero φ
          (Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self r)) _ z
      exact ⟨pullback.lift (IsClosedImmersion.lift _ ((fstG (I.map φ) n H₀).left ≫ π) (by
        rw [Scheme.IdealSheafData.ker_subschemeι]
        exact secIdeal_le_ker hN s _ h0)) _ (IsClosedImmersion.lift_fac _ _ _),
        pullback.lift_snd _ _ _⟩
  refine exists_div_sec H.hom hr s fun j x hx ↦ ?_
  obtain ⟨W, hxW, hW⟩ := exists_affine_le (V := N.U j) hx
  have h1 := constFn_dvd_of_mem_ker H.hom r (secIdeal hN s).subschemeι
    (inv (pullback.snd (secIdeal hN s).subschemeι π) ≫ pullback.fst _ _)
    (by rw [Category.assoc, pullback.condition, IsIso.inv_hom_id_assoc]) W.2
    (a := resG _ hW (s.f j)) (by
      rw [Scheme.IdealSheafData.ker_subschemeι]
      exact (ideal_locIdeal _ _ (exists_mem_chart hN) (associated_germ_sec s) W j hW).ge
        (Ideal.mem_span_singleton_self _))
  obtain ⟨c, hc⟩ := h1
  refine ⟨gs (𝟙 _) x W.1 c, ?_⟩
  have h2 := congrArg (gs (𝟙 _) x W.1) hc
  rw [gs_mul _ _ _ hxW, gs_constFn _ _ _ _ hxW, Category.id_comp] at h2
  exact (gs_res _ x hW hxW _).symm.trans h2


open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR in
theorem sec_div_of_expandsAt : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] [GeometricallyConnected G.hom] (U : UnifPre I D A G) (k : ℕ) (r : R), r ≠ 0 → ∀ (σ₀ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f₀ f : ∀ α, D.toPre.SecB k α), (∀ α, (∀ j, (f₀ α).f j = resTop _ (scal D.toPre.P.A.hom r) * (f α).f j)) → (∀ e, U.ExpandsAt e k σ₀ f₀) → ∃ σ : LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ))), (∀ j, (σ₀).f j = resTop _ (scal G.hom r) * (σ).f j) := by
  intro R _ _ I hR D A G _ _ _ U k r hr σ₀ f₀ f hf hE
  have : IsNoetherianRing R := hR.1
  have hI : I ≤ Ideal.jacobson ⊥ := have := hR.2.2.2; IsAdicComplete.le_jacobson_bot I
  have := U.smooth
  refine sec_div_of_germ_dvd R I hI G _ (linComb_isLB _ U.LG.isLB _ _) σ₀ r hr fun e j y hy ↦ ?_
  obtain ⟨S, H⟩ := (expandsAt_iff_stalks U e k σ₀ f₀).1 (hE e)
  choose J hJ using fun ψ : (thickObj R I e G).left ⟶ D.toPre.P.A.left ↦
    exists_chart D.toPre.P.isLB (ψ y)
  have hJ : Good D.toPre.P.L y J := hJ
  have hc : pGl U e ≫ D.toPre.P.A.hom = fGl I G e ≫ G.hom :=
    (Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm
  obtain ⟨jL, rfl⟩ : ∃ jL : U.LG.L.ι, j = fun _ ↦ jL :=
    ⟨j 0, funext fun i ↦ congrArg j (Subsingleton.elim i 0)⟩
  have h := (H y J hJ).2 jL (Set.mem_iInter.1 hy 0)
  refine (Units.dvd_mul_left (u := wv U e (𝟙 _) y (J (pGl U e)) jL ^ k)).1 (h.symm ▸ ?_)
  refine Finset.dvd_sum fun α _ ↦ Dvd.dvd.mul_right ⟨sval (f α) (pGl U e) y J, ?_⟩ _
  rw [← hc]
  have := gs_of_eq_sum_scal (n := 1) D.toPre.P.A.hom (pGl U e) y _ (hJ.mem (D.toPre.famφB α) _)
    (fun _ ↦ r) (a := (f₀ α).f _) (b := fun _ ↦ (f α).f _) (by rw [Fin.sum_univ_one]; exact hf α _)
  rw [Fin.sum_univ_one] at this
  exact this

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CombEqZeroIffExpansionCombEqZero
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem comb_eq_zero_iff_expansion_comb_eq_zero : ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R), AdmBase R I → ∀ (D : DegData R I) (A : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (U : UnifPre I D A G) (k : ℕ) (n : ℕ) (c : Fin n → R) (σ : Fin n → LB.Sec (LB.LinComb U.LG.L (K := Fin 1) (fun _ => 𝟙 G.left) (fun _ => (k : ℤ)))) (f : Fin n → ∀ α, D.toPre.SecB k α), (∀ i e, U.ExpandsAt e k (σ i) (f i)) → ((∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) → ∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) ∧ (GeometricallyConnected G.hom → (∀ α j, ∑ i, resTop _ (scal D.toPre.P.A.hom (c i)) * (f i α).f j = 0) → ∀ j, ∑ i, resTop _ (scal G.hom (c i)) * (σ i).f j = 0) := by
  intro R _ _ I hR D A G _ _ U k n c σ f hE
  obtain ⟨hN, -, -, hC⟩ := hR
  have hI : I ≤ Ideal.jacobson ⊥ := IsAdicComplete.le_jacobson_bot I
  let σ₀ := ExpansionLinear.secComb (fun i => scal G.hom (c i)) σ
  let f₀ : ∀ α, D.toPre.SecB k α := fun α =>
    ExpansionLinear.secComb (fun i => scal D.toPre.P.A.hom (c i)) (fun i => f i α)
  have h₀ : ∀ e, U.ExpandsAt e k σ₀ f₀ := fun e =>
    expandsAt_linear R I D A G U k e n c σ f σ₀ f₀ (fun i => hE i e) (fun _ => rfl) (fun _ _ => rfl)
  refine ⟨fun h α => ?_, fun hG h => ?_⟩
  · have := D.toPre.P.isAb.smooth
    have := D.toPre.P.isAb.geomConnected
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI D.toPre.P.A).1 _
      (DVR.linComb_isLB _ D.toPre.P.isLB _ _) (f₀ α) fun e j => ?_
    refine (ExtDiv.pG_app_eq_zero_iff (U.gt e) _ _).1
      (WeightPf.weightIndep R I D A G U e k σ₀ f₀ (fun j => ?_) (h₀ e) α j)
    exact (congrArg _ (h j)).trans (map_zero _)
  · have := U.smooth
    refine (sec_eq_zero_and_hom_eq_of_thickenings R I hI G).1 _
      (DVR.linComb_isLB _ U.LG.isLB _ _) σ₀ fun e j => ?_
    exact ClosedFibreTerm.vanish_of_terms_vanish U e k σ₀ f₀ (h₀ e)
      (fun α j => (congrArg _ (h α j)).trans (map_zero _)) j

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ConnectedSpaceOfSection
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GroupConn

theorem connectedSpace_of_section {X S : Scheme.{0}} (f : X ⟶ S) [GeometricallyConnected f]
    [ConnectedSpace S] (s : S ⟶ X) (hs : s ≫ f = 𝟙 S) : ConnectedSpace X := by

  have hsec : ∀ y : S, f (s y) = y := fun y => by
    simpa using congrArg (fun g : S ⟶ S => g y) hs
  obtain ⟨y₀⟩ := (inferInstance : Nonempty S)
  refine connectedSpace_iff_connectedComponent.mpr ⟨s y₀, Set.eq_univ_iff_forall.mpr fun x => ?_⟩
  have hbase : s (f x) ∈ connectedComponent (s y₀) :=
    (isPreconnected_range s.continuous).subset_connectedComponent ⟨y₀, rfl⟩ ⟨f x, rfl⟩
  have hfib : x ∈ connectedComponent (s (f x)) :=
    (f.isConnected_preimage_singleton (f x)).isPreconnected.subset_connectedComponent
      (show f (s (f x)) = f x from hsec (f x)) rfl
  rw [connectedComponent_eq hbase]
  exact hfib

theorem connectedSpace_tensor {S : Scheme.{0}} (G : Over S) [GrpObj G] [GeometricallyConnected G.hom]
    (Y : Over S) [ConnectedSpace Y.left] : ConnectedSpace (G ⊗ Y).left := by

  have : GeometricallyConnected (snd G Y).left :=
    show GeometricallyConnected (pullback.snd G.hom Y.hom) from inferInstance
  have hsec : (lift (toUnit Y ≫ η[G]) (𝟙 Y)).left ≫ (snd G Y).left = 𝟙 Y.left := by
    rw [← Over.comp_left, lift_snd, Over.id_left]
  exact connectedSpace_of_section (snd G Y).left _ hsec

theorem connectedSpace_group : ∀ (S : Scheme.{0}) [ConnectedSpace S] (G : Over S) [GrpObj G] [Smooth G.hom] [GeometricallyConnected G.hom], ConnectedSpace G.left ∧ ∀ (X : Type) [AddCommGroup X] [Module.Free ℤ X] (Y : Over S), ConnectedSpace Y.left → ConnectedSpace (splitTorus S X ⊗ Y).left ∧ ConnectedSpace (G ⊗ Y).left := by
  intro S _ G _ _ _
  refine ⟨connectedSpace_of_section (S := S) (X := G.left) G.hom η[G].left (Over.w _),
    fun X _ _ Y _ => ⟨?_, connectedSpace_tensor G Y⟩⟩

  have : UniqueSums X :=
    UniqueSums.of_injective_addHom (Module.Free.chooseBasis ℤ X).repr.toAddEquiv.toAddHom
      (Module.Free.chooseBasis ℤ X).repr.injective inferInstance
  exact connectedSpace_tensor (splitTorus S X) Y

end GlobalTheory.GroupConn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.GtCoordCompatOfPow
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace PowLevelCompat

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

theorem box_gen_val_along {X X' Y Z : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}
    (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {K : Type} [Fintype K] {Y₀ : Scheme.{0}}
    {φ' : K → (Y ⟶ X')} {φ : Fin j → K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ i a) (t' : LB.Gen (LB.LinComb M' φ' ε))
    (t : ∀ i, LB.Gen (LB.LinComb M (φ i) ε))
    (H : LB.Gen.Maps (LB.linCombIso w φ' ε) t'
      (GeneratorPullback.boxGen M pr φ' ε (fun i => GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i))))
    (r : Z ⟶ Y) (y : Z) {J J'} (hJ : Good M y J) (hJ' : Good M' y J') :
    (∏ a, bw w (r ≫ φ' a) y (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r y J' =
      ∏ i, val (t i) (r ≫ ρ i) y J := by
  have hm : r y ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
      LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
    ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i),
      Set.mem_iInter.2 fun a => hJ' (r ≫ φ' a)⟩
  have E := congrArg (gm r y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
    LB.wchart M' φ' (fun a => J' (r ≫ φ' a))))
    (H (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)))
  have E₁ := gm_linCombIso w φ' ε r y _ _ hm
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) E₁ (gm_res r y inf_le_right hm _))).symm.trans
    (E.symm.trans ((gm_res r y inf_le_left hm _).trans ?_))
  refine (map_prod (gm r y (LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i))))
    (fun i => res (GeneratorPullback.box_le M pr φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) i)
      ((GeneratorPullback.pullAlong M (pr i) (ρ i) (φ i) ε φ' (hψ i) (t i)).s (fun a _ => J ((r ≫ φ' a) ≫ pr i))))
      Finset.univ).trans
    (Finset.prod_congr rfl fun i _ => ?_)
  rw [val_of (t i) (r ≫ ρ i) y J (fun a => J ((r ≫ φ' a) ≫ pr i))
    (fun a => congrArg J (by rw [Category.assoc, Category.assoc, hψ]))]
  have h₁ := GeneratorPullback.box_le M pr φ' _ i hm.1
  have h₂ : ρ i (r y) ∈ LB.wchart M (φ i) (fun a => J ((r ≫ φ' a) ≫ pr i)) :=
    Set.mem_iInter.2 fun a => (congrArg (fun g => g y ∈ M.U (J ((r ≫ φ' a) ≫ pr i)))
      (show (r ≫ φ' a) ≫ pr i = (r ≫ ρ i) ≫ φ i a by rw [Category.assoc, Category.assoc, hψ])).mp (hJ _)
  exact (gm_res r y (GeneratorPullback.box_le M pr φ' _ i) hm.1 _).trans ((gm_res r y _ h₁ _).trans (gm_pull r (ρ i) y _ h₂ _))

end PowLevelCompat

end GlobalTheory
end

