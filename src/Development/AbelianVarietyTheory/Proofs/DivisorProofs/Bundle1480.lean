module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.InvariantFunctionsDescend
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1457
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatPath
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1402
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1429
public import GroundTheory.GlobalFields.Adele.Discrete
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FiniteAdeleVectorAnnihilatorsCompactOpenBasis
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1453
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1452
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1409
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1462
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSectionDescentFlatSurjectiveQuasiCompact
section
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section
namespace GlobalTheory.LocDescent

theorem gs_comp_stalkMap {W Z Y : Scheme.{0}} (x : W ⟶ Z) (g : Z ⟶ Y) (w : W) (U : Y.Opens) (h : g (x w) ∈ U)
    (a : Γ(Y, U)) : gs (x ≫ g) w U a = (x.stalkMap w).hom (gs g (x w) U a) := by
  exact (gs_eq (x ≫ g) w U h a).trans (((Scheme.Hom.germ_stalkMap_apply x (g ⁻¹ᵁ U) w h _).symm).trans
    (congrArg (x.stalkMap w).hom (gs_eq g (x w) U h a).symm))

theorem stalkMap_fromSpecStalk_injective {Z : Scheme.{0}} (z : Z) :
    Function.Injective ((Z.fromSpecStalk z).stalkMap (closedPoint (Z.presheaf.stalk z))).hom := by
  have e := Scheme.stalkClosedPointTo_fromSpecStalk z
  have h : Function.Injective (Scheme.stalkClosedPointTo (Z.fromSpecStalk z)).hom := by
    rw [e]
    exact (Iso.commRingCatIsoToRingEquiv _).injective
  exact Function.Injective.of_comp (f := (stalkClosedPointIso (Z.presheaf.stalk z)).hom.hom) h

theorem gs_appLE_top {Z Y : Scheme.{0}} (g : Z ⟶ Y) (z : Z) (U : Y.Opens) (h : ⊤ ≤ g ⁻¹ᵁ U) (a : Γ(Y, U)) :
    gs (𝟙 Z) z ⊤ ((g.appLE U ⊤ h).hom a) = gs g z U a :=
  (gs_res (𝟙 Z) z h trivial _).trans ((gs_pull (𝟙 Z) g z U (h trivial) a).trans (by rw [Category.id_comp]))

theorem gs_eq_of_local {Z Y : Scheme.{0}} (g₁ g₂ : Z ⟶ Y) (z : Z) (U : Y.Opens) (h₁ : g₁ z ∈ U) (h₂ : g₂ z ∈ U)
    (a : Γ(Y, U)) (h : gs (Z.fromSpecStalk z ≫ g₁) (closedPoint (Z.presheaf.stalk z)) U a =
      gs (Z.fromSpecStalk z ≫ g₂) (closedPoint (Z.presheaf.stalk z)) U a) : gs g₁ z U a = gs g₂ z U a := by
  have e : Z.fromSpecStalk z (closedPoint (Z.presheaf.stalk z)) = z := Scheme.fromSpecStalk_closedPoint
  have H : ∀ y : Z, y = z → gs g₁ y U a = gs g₂ y U a → gs g₁ z U a = gs g₂ z U a := by
    rintro _ rfl h
    exact h
  have m : ∀ (g : Z ⟶ Y) (y : Z), y = z → g z ∈ U → g y ∈ U := by
    rintro g _ rfl h
    exact h
  exact H _ e (stalkMap_fromSpecStalk_injective z ((gs_comp_stalkMap _ g₁ _ U (m g₁ _ e h₁) a).symm.trans
    (h.trans (gs_comp_stalkMap _ g₂ _ U (m g₂ _ e h₂) a))))

theorem trF_comp {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] (q : Y' ⟶ Y) (ψ : K → (Y ⟶ X))
    (ε : K → ℤ) (r : Z ⟶ Y') (z : Z) (j j' : K → L.ι) :
    trF (fun a => q ≫ ψ a) ε r z j j' = trF ψ ε (r ≫ q) z j j' := by
  simp only [trF, Category.assoc]

theorem exists_sec_descend : ∀ {X B H : Scheme.{0}} (L : LB X), L.IsLB → ∀ (q : H ⟶ B), Flat q → Surjective q → QuasiCompact q → ∀ {K : Type} [Fintype K] (ψ : K → (B ⟶ X)) (ε : K → ℤ) (σ : LB.Sec (LB.LinComb L (fun k => q ≫ ψ k) ε)), (∀ (S : Type) [CommRing S] [IsLocalRing S] (g₁ g₂ : Sp S ⟶ H), g₁ ≫ q = g₂ ≫ q → ∀ J, Good L (closedPoint S) J → sval σ g₁ (closedPoint S) J = sval σ g₂ (closedPoint S) J) → ∃ b : LB.Sec (LB.LinComb L ψ ε), ∀ (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z) J, Good L z J → sval σ r z J = sval b (r ≫ q) z J := by
  intro X B H L hL q _ _ _ K _ ψ ε σ hσ
  have le : ∀ j : K → L.ι, q ⁻¹ᵁ LB.wchart L ψ j ≤ LB.wchart L (fun a => q ≫ ψ a) j :=
    fun j y hy => Set.mem_iInter.2 fun a => Set.mem_iInter.1 hy a
  have desc : ∀ j : K → L.ι, ∃ a : Γ(B, LB.wchart L ψ j),
      (q.app _).hom a = (H.presheaf.map (homOfLE (le j)).op).hom (σ.f j) := by
    intro j
    refine FunDescent.exists_app_eq q _ _ fun Z g₁ g₂ h₁ h₂ hq => fn_ext fun z _ => ?_
    rw [gs_appLE_top, gs_appLE_top]
    refine gs_eq_of_local g₁ g₂ z _ (h₁ trivial) (h₂ trivial) _ ?_
    have key : ∀ (S : Type) [CommRing S] [IsLocalRing S] (k₁ k₂ : Sp S ⟶ H), k₁ ≫ q = k₂ ≫ q →
        k₁ (closedPoint S) ∈ q ⁻¹ᵁ LB.wchart L ψ j → k₂ (closedPoint S) ∈ q ⁻¹ᵁ LB.wchart L ψ j →
        gs k₁ (closedPoint S) _ ((H.presheaf.map (homOfLE (le j)).op).hom (σ.f j)) =
        gs k₂ (closedPoint S) _ ((H.presheaf.map (homOfLE (le j)).op).hom (σ.f j)) := by
      intro S _ _ k₁ k₂ hk hz' hz
      choose J hJ using fun χ : Sp S ⟶ X => exists_chart hL (χ (closedPoint S))
      have hJ' : Good L (Z := Sp S) (closedPoint S) J := hJ
      refine (gs_res _ _ (le j) hz' _).trans (Eq.trans ?_ (gs_res _ _ (le j) hz _).symm)
      refine (sec_trans σ _ _ (le j hz') (hJ'.mem _ _)).trans
        (Eq.trans ?_ (sec_trans σ _ _ (le j hz) (hJ'.mem _ _)).symm)
      refine congrArg₂ (· * ·) (congrArg Units.val ?_) (hσ S k₁ k₂ hk J hJ')
      refine (trF_comp _ _ _ _ _ _ _).trans (Eq.trans ?_ (trF_comp _ _ _ _ _ _ _).symm)
      simp only [← Category.assoc, hk]
    exact @key (Z.presheaf.stalk z) _ (Z.toLocallyRingedSpace.isLocalRing z)
      (Z.fromSpecStalk z ≫ g₁) (Z.fromSpecStalk z ≫ g₂)
      ((Category.assoc _ _ _).trans ((congrArg (Z.fromSpecStalk z ≫ ·) hq).trans (Category.assoc _ _ _).symm))
      (h₁ trivial) (h₂ trivial)
  choose a ha using desc
  have hv : ∀ j (Z : Scheme.{0}) (r : Z ⟶ H) (z : Z), q (r z) ∈ LB.wchart L ψ j →
      gs (r ≫ q) z (LB.wchart L ψ j) (a j) =
        gs r z (LB.wchart L (fun a => q ≫ ψ a) j) (σ.f j) := fun j Z r z hz =>
    (gs_pull r _ z _ hz _).symm.trans ((congrArg (gs r z _) (ha j)).trans (gs_res r z (le j) hz _))
  refine ⟨⟨a, fun j j' => FunDescent.app_injective q (LB.wchart L ψ j ⊓ LB.wchart L ψ j')
    (fn_ext fun y hy => ?_)⟩, fun Z r z J hJ => ?_⟩
  · have hy' : q y ∈ LB.wchart L ψ j ⊓ LB.wchart L ψ j' := hy
    refine (gs_pull (𝟙 _) q y _ hy' _).trans (Eq.trans ?_ (gs_pull (𝟙 _) q y _ hy' _).symm)
    refine ((gs_res (𝟙 _ ≫ q) y _ hy' _).trans ((hv j _ _ y hy'.1).trans
      (sec_trans σ (𝟙 _) y (le j hy'.1) (le j' hy'.2)))).trans (Eq.symm ?_)
    refine (gs_mul (𝟙 _ ≫ q) y _ hy' _ _).trans (congrArg₂ (· * ·)
      ((gs_unit (𝟙 _ ≫ q) y _ hy' _).trans (congrArg Units.val
        ((gm_linComb L ψ ε (𝟙 _ ≫ q) y j j' hy'.1 hy'.2).trans (trF_comp _ _ _ _ _ _ _).symm)))
      ((gs_res (𝟙 _ ≫ q) y _ hy' _).trans (hv j' _ _ y hy'.2)))
  · refine Eq.symm ?_
    rw [sval_of _ (r ≫ q) z J (fun a => J (r ≫ q ≫ ψ a)) (fun a => by rw [Category.assoc])]
    exact hv _ Z r z (Set.mem_iInter.2 fun a => hJ (r ≫ q ≫ ψ a))

end GlobalTheory.LocDescent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsStalkDerivationOfLieSheafSections
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.VB GlobalTheory.LieVB GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.NeronCurve GlobalTheory.Nef
open GlobalTheory.Twist (resM)
open scoped CategoryTheory.Obj RatFunc

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Nef

section TanDer

variable {S : Scheme.{0}} (G : Over S) [GrpObj G] {R : Type} [CommRing R] (s : S)
  (β : S.presheaf.stalk s →+* R) {n : ℕ} {V : S.Opens} (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R)

def tanVal {U : G.left.Opens} {V' : S.Opens} (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V')
    (f : Γ(G.left, U)) : R :=
  ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f)))

theorem tanVal_mono {U : G.left.Opens} {V' V'' : S.Opens} (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U)
    (hs' : s ∈ V') (k : V'' ≤ V') (hs'' : s ∈ V'') (f : Γ(G.left, U)) :
    tanVal G s β τ w (k.trans hV) (k.trans he) hs'' f = tanVal G s β τ w hV he hs' f := by
  unfold tanVal
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← resM_dUnit G he k f, dualApp_resM]
  congr 2
  exact TopCat.Presheaf.germ_res_apply _ _ _ _ _

theorem tanVal_indep {U : G.left.Opens} {V₁ V₂ : S.Opens} (hV₁ : V₁ ≤ V) (he₁ : V₁ ≤ unitSec G ⁻¹ᵁ U)
    (hs₁ : s ∈ V₁) (hV₂ : V₂ ≤ V) (he₂ : V₂ ≤ unitSec G ⁻¹ᵁ U) (hs₂ : s ∈ V₂) (f : Γ(G.left, U)) :
    tanVal G s β τ w hV₁ he₁ hs₁ f = tanVal G s β τ w hV₂ he₂ hs₂ f :=
  (tanVal_mono G s β τ w hV₁ he₁ hs₁ (inf_le_left : V₁ ⊓ V₂ ≤ V₁) ⟨hs₁, hs₂⟩ f).symm.trans
    (tanVal_mono G s β τ w hV₂ he₂ hs₂ (inf_le_right : V₁ ⊓ V₂ ≤ V₂) ⟨hs₁, hs₂⟩ f)

theorem tanVal_resG {U U' : G.left.Opens} (k : U' ≤ U) {V' : S.Opens} (hV : V' ≤ V)
    (he : V' ≤ unitSec G ⁻¹ᵁ U') (hs' : s ∈ V') (f : Γ(G.left, U)) :
    tanVal G s β τ w hV he hs' (resG _ k f) =
      tanVal G s β τ w hV (he.trans ((unitSec G).preimage_mono k)) hs' f := by
  unfold tanVal
  simp only [dUnit_resG]

variable {s}

theorem mem_inf_unitSec (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) : s ∈ V ⊓ unitSec G ⁻¹ᵁ U :=
  Opens.mem_inf.2 ⟨hs, hU⟩

def tanCan (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (f : Γ(G.left, U)) : R :=
  tanVal G s β τ w (V' := V ⊓ unitSec G ⁻¹ᵁ U) inf_le_left inf_le_right (mem_inf_unitSec G hs hU) f

theorem tanCan_eq (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) {V' : S.Opens} (hV : V' ≤ V)
    (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)) :
    tanCan G β τ w hs hU f = tanVal G s β τ w hV he hs' f :=
  tanVal_indep G s β τ w _ _ _ _ _ _ f

theorem tanCan_res (hs : s ∈ V) {U U' : G.left.Opens} (k : U' ≤ U) (hU' : unitSec G s ∈ U') (f : Γ(G.left, U)) :
    tanCan G β τ w hs hU' (resG _ k f) = tanCan G β τ w hs (k hU') f := by
  rw [tanCan, tanVal_resG]
  exact (tanCan_eq G β τ w hs (k hU') _ _ _ f).symm

theorem tanCan_germ_eq (hs : s ∈ V) {U U' : G.left.Opens} (hU : unitSec G s ∈ U) (hU' : unitSec G s ∈ U')
    (f : Γ(G.left, U)) (f' : Γ(G.left, U'))
    (h : G.left.presheaf.germ U _ hU f = G.left.presheaf.germ U' _ hU' f') :
    tanCan G β τ w hs hU f = tanCan G β τ w hs hU' f' := by
  obtain ⟨W, hW, iU, iU', e⟩ := TopCat.Presheaf.germ_eq _ _ hU hU' f f' h
  have h1 := tanCan_res G β τ w hs iU.le hW f
  have h2 := tanCan_res G β τ w hs iU'.le hW f'
  have e' : resG _ iU.le f = resG _ iU'.le f' := e
  rw [← h1, ← h2, e']

theorem tanCan_add (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (a b : Γ(G.left, U)) :
    tanCan G β τ w hs hU (a + b) = tanCan G β τ w hs hU a + tanCan G β τ w hs hU b := by
  unfold tanCan tanVal
  simp only [map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem tanCan_mul (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (a b : Γ(G.left, U))
    (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s)
    (hε : ∀ f : Γ(G.left, U), ε (G.left.presheaf.germ U _ hU f) =
      S.presheaf.germ (V ⊓ unitSec G ⁻¹ᵁ U) s (mem_inf_unitSec G hs hU) ((unitSec G).appLE U _ inf_le_right f)) :
    tanCan G β τ w hs hU (a * b) = β (ε (G.left.presheaf.germ U _ hU a)) * tanCan G β τ w hs hU b +
      β (ε (G.left.presheaf.germ U _ hU b)) * tanCan G β τ w hs hU a := by
  rw [hε, hε]
  unfold tanCan tanVal
  simp only [dUnit_mul, map_add (f := _), map_smul, smul_eq_mul, map_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => by ring

def tanStalk (hs : s ∈ V) (x : G.left.presheaf.stalk (unitSec G s)) : R :=
  tanCan G β τ w hs (TopCat.Presheaf.germ_exist _ x).choose_spec.choose
    (TopCat.Presheaf.germ_exist _ x).choose_spec.choose_spec.choose

theorem tanStalk_germ (hs : s ∈ V) {U : G.left.Opens} (hU : unitSec G s ∈ U) (f : Γ(G.left, U)) :
    tanStalk G β τ w hs (G.left.presheaf.germ U _ hU f) = tanCan G β τ w hs hU f := by
  unfold tanStalk
  apply tanCan_germ_eq
  exact (TopCat.Presheaf.germ_exist _ _).choose_spec.choose_spec.choose_spec

end TanDer

theorem germ_exist_two {X : Scheme.{0}} (p : X) (x y : X.presheaf.stalk p) :
    ∃ (U : X.Opens) (hU : p ∈ U) (a b : Γ(X, U)), X.presheaf.germ U p hU a = x ∧ X.presheaf.germ U p hU b = y := by
  obtain ⟨U₁, h₁, a, rfl⟩ := TopCat.Presheaf.germ_exist _ x
  obtain ⟨U₂, h₂, b, rfl⟩ := TopCat.Presheaf.germ_exist _ y
  exact ⟨U₁ ⊓ U₂, Opens.mem_inf.2 ⟨h₁, h₂⟩, resG _ inf_le_left a, resG _ inf_le_right b,
    TopCat.Presheaf.germ_res_apply _ _ _ _ _, TopCat.Presheaf.germ_res_apply _ _ _ _ _⟩

theorem exists_stalkDer_of_lie : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] (R : Type) [CommRing R], ∀ (s : S) (π : S.presheaf.stalk s →+* G.left.presheaf.stalk (unitSec G s)) (ε : G.left.presheaf.stalk (unitSec G s) →+* S.presheaf.stalk s) (m : G.left.presheaf.stalk (unitSec G s) →+* G.left.presheaf.stalk (unitSec G s)) (β : S.presheaf.stalk s →+* R) (n : ℕ) (V : S.Opens) (hs : s ∈ V) (τ : Fin n → Γ(Lie G, V)) (w : Fin n → R), StalkData G s π ε m → ∃ δ : G.left.presheaf.stalk (unitSec G s) →+ R, (∀ f g, δ (f * g) = β (ε f) * δ g + β (ε g) * δ f) ∧ (∀ a, δ (π a) = 0) ∧ ∀ (U : G.left.Opens) (hU : unitSec G s ∈ U) (V' : S.Opens) (hV : V' ≤ V) (he : V' ≤ unitSec G ⁻¹ᵁ U) (hs' : s ∈ V') (f : Γ(G.left, U)), δ (G.left.presheaf.germ U _ hU f) = ∑ i, w i * β (S.presheaf.germ V' s hs' (dualApp (τ i) hV (dUnit G he f))) := by
  intro S G _ R _ s π ε m β n V hs τ w hD
  have hI := _root_.GlobalTheory.Nef.stalkData_germ S G s π ε m hD
  refine ⟨AddMonoidHom.mk' (tanStalk G β τ w hs) ?_, ?_, ?_, ?_⟩
  · intro x y
    obtain ⟨U, hU, a, b, rfl, rfl⟩ := germ_exist_two (unitSec G s) x y
    rw [← map_add (f := _), tanStalk_germ, tanStalk_germ, tanStalk_germ, tanCan_add]
  · intro x y
    obtain ⟨U, hU, a, b, rfl, rfl⟩ := germ_exist_two (unitSec G s) x y
    simp only [AddMonoidHom.mk'_apply]
    rw [← map_mul, tanStalk_germ, tanStalk_germ, tanStalk_germ,
      tanCan_mul G β τ w hs hU a b ε (fun f => hI.2.1 U hU _ _ inf_le_right f)]
  · intro a
    obtain ⟨V₀, h₀, a₀, rfl⟩ := TopCat.Presheaf.germ_exist _ a
    have hU : unitSec G s ∈ G.hom ⁻¹ᵁ V₀ := by
      show (unitSec G ≫ G.hom) s ∈ V₀
      rw [sec_hom]
      exact h₀
    rw [hI.1 V₀ h₀ _ hU le_rfl a₀]
    simp only [AddMonoidHom.mk'_apply, tanStalk_germ, tanCan, tanVal, dUnit_base, map_zero, mul_zero,
      Finset.sum_const_zero]
  · intro U hU V' hV he hs' f
    simp only [AddMonoidHom.mk'_apply]
    rw [tanStalk_germ]
    exact tanCan_eq G β τ w hs hU hV he hs' f

end GlobalTheory.Nef
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaReNonneg
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

noncomputable section

namespace GlobalTheory.ThetaPosIso

theorem disc (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ] :
    ∃ D ∈ nhds (0 : κ → AF F), ∀ ξ : κ → F, (fun i => algebraMap F (AF F) (ξ i)) ∈ D → ξ = 0 := by
  have hd := GroundTheory.Global.discreteTopology_principalSubgroup F
  have ho : IsOpen ({0} : Set (AdeleRing.principalSubgroup (𝓞 F) F)) := isOpen_discrete _
  obtain ⟨t, ht, hpre⟩ := isOpen_induced_iff.mp ho
  refine ⟨Set.pi Set.univ fun _ => t, set_pi_mem_nhds Set.finite_univ fun _ _ => ht.mem_nhds ?_, ?_⟩
  · have h0 : ((0 : AdeleRing.principalSubgroup (𝓞 F) F) : AF F) ∈ t := by
      have : (0 : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := by rw [hpre]; rfl
      exact this
    simpa using h0
  · intro ξ hξ
    funext i
    have hm : algebraMap F (AF F) (ξ i) ∈ AdeleRing.principalSubgroup (𝓞 F) F := ⟨ξ i, rfl⟩
    have : (⟨_, hm⟩ : AdeleRing.principalSubgroup (𝓞 F) F) ∈ Subtype.val ⁻¹' t := hξ i (Set.mem_univ _)
    rw [hpre] at this
    have h2 : algebraMap F (AF F) (ξ i) = 0 := congrArg Subtype.val this
    exact (NumberField.AdeleRing.algebraMap_injective (𝓞 F) F) (h2.trans (map_zero _).symm)


set_option maxHeartbeats 1000000 in
theorem exists_theta_re_nonneg : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    (S : Submodule (AF F) ((κ → AF F) × (κ → AF F))),
    (∀ s ∈ S, ∀ s' ∈ S, s.1 ⬝ᵥ s'.2 = s'.1 ⬝ᵥ s.2) →
    S ≤ Submodule.span (AF F) {s | s ∈ S ∧ ∃ y z : κ → F,
      s = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))} →
    ∃ Φ ∈ schA F κ, Continuous (fun w => thetaSum F (schr ψ w Φ)) ∧
      (∀ s ∈ S, 0 ≤ (thetaSum F (schr ψ s Φ)).re) ∧ 0 < (thetaSum F (schr ψ 0 Φ)).re := by
  intro F _ _ ψ hψ κ _ S hiso hspan
  classical
  obtain ⟨P, Q, hP, hQ, hker⟩ := _root_.GlobalTheory.rational_proj_section_of_span F κ S hspan
  obtain ⟨D, hD, hDξ⟩ := disc F κ
  set PA := P.map (algebraMap F (AF F)) with hPA
  set QA := Q.map (algebraMap F (AF F)) with hQA
  obtain ⟨g, hgdef⟩ : ∃ g : (κ → AF F) → ℂ, g = fun x => ψ (⅟(2 : AF F) * (x ⬝ᵥ (QA *ᵥ x))) := ⟨_, rfl⟩
  have hg : Continuous g := by
    rw [hgdef]
    exact hψ.1.comp (continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)))
  have hg0 : 0 < (g 0).re := by simp [hgdef]
  obtain ⟨V₀, hV₀, hq⟩ := exists_nhds_zero_quarter hD
  obtain ⟨V, hV, hVm⟩ : ∃ V ∈ nhds (0 : κ → AF F), ∀ x ∈ V, x ∈ V₀ ∧ -x ∈ V₀ ∧ PA *ᵥ x ∈ D ∧ 0 < (g x).re := by
    open scoped Pointwise in
    refine ⟨((V₀ ∩ -V₀) ∩ (fun x => PA *ᵥ x) ⁻¹' D) ∩ {x | 0 < (g x).re}, ?_, fun x hx => ⟨hx.1.1.1, Set.mem_neg.mp hx.1.1.2, hx.1.2, hx.2⟩⟩
    refine Filter.inter_mem (Filter.inter_mem (Filter.inter_mem hV₀ (neg_mem_nhds_zero _ hV₀)) ?_) ?_
    · exact (continuous_const.matrix_mulVec continuous_id).tendsto' (0 : κ → AF F) 0 (by simp) hD
    · exact ((Complex.continuous_re.comp hg).tendsto 0).eventually (lt_mem_nhds hg0)
  obtain ⟨Φ, hΦS, hΦc, hΦV, hΦr, hΦ0⟩ := _root_.GlobalTheory.AdelicBumpTest.exists_nonneg_test F κ V hV
  have hsub : ∀ ξ ξ' : κ → F, (fun i => algebraMap F (AF F) ((ξ - ξ') i)) =
      (fun i => algebraMap F (AF F) (ξ i)) - (fun i => algebraMap F (AF F) (ξ' i)) := by
    intro ξ ξ'; funext i; simp [map_sub]
  have KEY : ∀ ξ : κ → F, ∀ v₁ ∈ V, ∀ v₂ ∈ V, ∀ v₃ ∈ V, ∀ v₄ ∈ V,
      (fun i => algebraMap F (AF F) (ξ i)) = v₁ - v₂ - (v₃ - v₄) → ξ = 0 := by
    intro ξ v₁ h₁ v₂ h₂ v₃ h₃ v₄ h₄ he
    apply hDξ
    rw [he, show v₁ - v₂ - (v₃ - v₄) = v₁ + -v₂ + -v₃ + v₄ by abel]
    exact hq (hVm _ h₁).1 (hVm _ h₂).2.1 (hVm _ h₃).2.1 (hVm _ h₄).1
  have hV0 : (0 : κ → AF F) ∈ V := mem_of_mem_nhds hV
  have LOC : ∀ a₀ : κ → AF F, ∃ ξ₀ : κ → F, ∀ᶠ a in nhds a₀, ∀ ξ : κ → F, ξ ≠ ξ₀ →
      Φ ((fun i => algebraMap F (AF F) (ξ i)) + a) = 0 := by
    intro a₀
    have hnear : ∀ᶠ a in nhds a₀, a - a₀ ∈ V :=
      (continuous_id.sub continuous_const).tendsto' a₀ 0 (sub_self a₀) hV
    by_cases h : ∃ ξ₀ : κ → F, ∃ v₁ ∈ V, ∃ v₂ ∈ V, (fun i => algebraMap F (AF F) (ξ₀ i)) + a₀ = v₁ - v₂
    · obtain ⟨ξ₀, v₁, h₁, v₂, h₂, he⟩ := h
      refine ⟨ξ₀, ?_⟩
      filter_upwards [hnear] with a ha ξ hne
      by_contra hz
      apply hne
      rw [← sub_eq_zero]
      refine KEY _ _ (hΦV _ hz) _ ha _ h₁ _ h₂ ?_
      rw [hsub, ← he]; abel
    · refine ⟨0, ?_⟩
      filter_upwards [hnear] with a ha ξ _
      by_contra hz
      exact h ⟨ξ, _, hΦV _ hz, _, ha, by abel⟩
  have THETA : ∀ w : (κ → AF F) × (κ → AF F), ∃ ξ₀ : κ → F, ∀ᶠ w' in nhds w,
      thetaSum F (schr ψ w' Φ) = ψ ((fun i => algebraMap F (AF F) (ξ₀ i)) ⬝ᵥ w'.2 + ⅟(2 : AF F) * (w'.1 ⬝ᵥ w'.2)) *
        Φ ((fun i => algebraMap F (AF F) (ξ₀ i)) + w'.1) := by
    intro w
    obtain ⟨ξ₀, h⟩ := LOC w.1
    refine ⟨ξ₀, ?_⟩
    filter_upwards [(continuous_fst.tendsto w).eventually h] with w' hw'
    exact tsum_eq_single ξ₀ fun ξ hne => mul_eq_zero_of_right _ (hw' ξ hne)
  have htwo : ⅟(2 : AF F) = algebraMap F (AF F) (2⁻¹ : F) := by
    refine invOf_eq_right_inv ?_
    rw [← map_ofNat (algebraMap F (AF F)) 2, ← map_mul, mul_inv_cancel₀ two_ne_zero, map_one]
  refine ⟨Φ, hΦS, ?_, ?_, ?_⟩
  · refine continuous_iff_continuousAt.2 fun w => ?_
    obtain ⟨ξ₀, h⟩ := THETA w
    refine ContinuousAt.congr ?_ (h.mono fun _ h => h.symm)
    refine Continuous.continuousAt ?_
    exact (hψ.1.comp ((continuous_const.dotProduct continuous_snd).add
      (continuous_const.mul (continuous_fst.dotProduct continuous_snd)))).mul
      (hΦc.comp (continuous_const.add continuous_fst))
  · intro s hs
    obtain ⟨ξ₀, h⟩ := THETA s
    rw [h.self_of_nhds]
    set e : κ → AF F := fun i => algebraMap F (AF F) (ξ₀ i) with he
    by_cases hz : Φ (e + s.1) = 0
    · simp [hz]
    have hx : e + s.1 ∈ V := hΦV _ hz
    have hP0 : P *ᵥ ξ₀ = 0 := by
      apply hDξ
      have h1 := (hVm _ hx).2.2.1
      simp only [Matrix.mulVec_add, hP s hs, add_zero] at h1
      convert h1 using 1
      funext i
      exact RingHom.map_mulVec _ _ _ _
    set f : κ → AF F := fun i => algebraMap F (AF F) ((Q *ᵥ ξ₀) i) with hf
    have hef : (e, f) ∈ S := hker ξ₀ hP0
    have hac : (s.1, QA *ᵥ s.1) ∈ S := hQ s hs
    have hQe : QA *ᵥ e = f := by
      funext i
      exact (RingHom.map_mulVec _ _ _ _).symm
    have h1 := hiso s hs _ hac
    have h2 := hiso _ hef s hs
    have h3 := hiso _ hef _ hac
    simp only at h1 h2 h3
    have hrat : e ⬝ᵥ f = algebraMap F (AF F) (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)) := (RingHom.map_dotProduct _ _ _).symm
    have hinv : ⅟(2 : AF F) * 2 = 1 := invOf_mul_self _
    have phase : e ⬝ᵥ s.2 + ⅟(2 : AF F) * (s.1 ⬝ᵥ s.2) =
        ⅟(2 : AF F) * ((e + s.1) ⬝ᵥ (QA *ᵥ (e + s.1))) + algebraMap F (AF F) (-(2⁻¹ * (ξ₀ ⬝ᵥ (Q *ᵥ ξ₀)))) := by
      rw [Matrix.mulVec_add, hQe, add_dotProduct, dotProduct_add, dotProduct_add, map_neg, map_mul, ← htwo, ← hrat]
      linear_combination h2 - ⅟(2 : AF F) * h3 - ⅟(2 : AF F) * h1 - (s.1 ⬝ᵥ f) * hinv
    rw [phase, AddChar.map_add_eq_mul, hψ.2.1, mul_one, Complex.mul_re, (hΦr _).1, mul_zero, sub_zero]
    have hpos := (hVm _ hx).2.2.2
    rw [hgdef] at hpos
    exact mul_nonneg (le_of_lt hpos) (hΦr _).2
  · have hz : ∀ ξ : κ → F, ξ ≠ 0 → Φ ((fun i => algebraMap F (AF F) (ξ i)) + (0 : (κ → AF F) × (κ → AF F)).1) = 0 := by
      intro ξ hne
      by_contra hz
      exact hne (KEY ξ _ (hΦV _ hz) 0 hV0 0 hV0 0 hV0 (by simp))
    have e0 : (fun i => algebraMap F (AF F) ((0 : κ → F) i)) = 0 := by funext i; simp
    have hsum : thetaSum F (schr ψ 0 Φ) = schr ψ 0 Φ (fun i => algebraMap F (AF F) ((0 : κ → F) i)) :=
      tsum_eq_single 0 fun ξ hne => mul_eq_zero_of_right _ (hz ξ hne)
    rw [hsum, e0]
    simp only [schr, Prod.fst_zero, Prod.snd_zero, dotProduct_zero, mul_zero, add_zero, AddChar.map_zero_eq_one,
      one_mul, hΦ0, Complex.one_re]
    norm_num

end GlobalTheory.ThetaPosIso
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryPairPartnerCmExtension
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF

namespace GlobalTheory.WeilPairPartnerF

theorem pair_partnerF : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → IsStdCharF (fun w : InfinitePlace F => (B.emb w).1) B.ψ (-1) →
    ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
        ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
        ∀ (a : UG (cA σ) (incM F JA)) (b : UG (cA σ) (incM F JB)),
          ∃ (g : GAF σ JS) (h : GAF σ JT), mtF σ JT h = a.1.1 ∧ mtF σ JS g = (b⁻¹).1.1ᵀ := by
  intro F E _ _ _ _ _ σ B _ _ nS nT JS JT hS _ ξ₀ hξ₀ _ JA JB ξ hA hB a b
  have hmap : ∀ {m n : Type} (X : Matrix m n (AF F ⊗[F] E)),
      X.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) = X.map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) :=
    fun X => Matrix.ext fun i j => rfl

  have ha : (a.1.val)ᵀ * incM F JA * (a.1.val).map (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA σ) = incM F JA := a.2
  set A : Matrix (Fin nT) (Fin nT) (AF F ⊗[F] E) := a.1.val with hAdef
  have hJA : incM F JA = (incM F JT)ᵀ := by
    rw [hA]; rfl
  rw [hJA] at ha
  have ha' := congrArg Matrix.transpose ha
  simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc] at ha'
  have hmemA : a.1 ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JT := by
    show Formalism.UG.cT _ a.1.val * _ * a.1.val = _
    simp only [Formalism.UG.cT, hmap]
    rw [Matrix.mul_assoc]
    exact ha'

  obtain ⟨cR, hcR⟩ : ∃ f, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ = f := ⟨_, rfl⟩
  have hb : (b.1.val)ᵀ * incM F JB * (b.1.val).map cR = incM F JB := by
    rw [← hcR, hmap]; exact b.2
  have hBB : b.1.val * (b⁻¹).1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).mul_inv
  have hBB' : (b⁻¹).1.val * b.1.val = 1 := by
    rw [Subgroup.coe_inv]; exact (b.1).inv_mul
  obtain ⟨Bm, hBdef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), b.1.val = M := ⟨_, rfl⟩
  obtain ⟨Bi, hBidef⟩ : ∃ M : Matrix (Fin nS) (Fin nS) (AF F ⊗[F] E), (b⁻¹).1.val = M := ⟨_, rfl⟩
  rw [hBdef] at hb hBB hBB'
  rw [hBidef] at hBB hBB'
  have hdet : JS.det ≠ 0 := hS.2
  have hGN := GlobalTheory.WeilPairPartner.map_mul_map_inv (inclR (F := F) (E := E) (AF F)) JS hdet
  have hNG := GlobalTheory.WeilPairPartner.map_inv_mul_map (inclR (F := F) (E := E) (AF F)) JS hdet
  have hsm : incM F (ξ₀ • JS⁻¹) = inclR (F := F) (AF F) ξ₀ • incM F JS⁻¹ :=
    GlobalTheory.WeilPairPartner.map_smul_eq _ _ _
  have hu : IsUnit (inclR (F := F) (E := E) (AF F) ξ₀) :=
    (isUnit_iff_ne_zero.mpr hξ₀).map _
  have hcore := GlobalTheory.WeilPairPartner.conj_inv_transpose cR ξ _ hu Bm Bi (incM F JB) (incM F JS)
    (incM F JS⁻¹) hb hBB hBB' (hB.trans hsm) hGN hNG
  have hTT : Biᵀ * Bmᵀ = 1 := by
    rw [← Matrix.transpose_mul, hBB, Matrix.transpose_one]
  let gU : GL (Fin nS) (AF F ⊗[F] E) :=
    ⟨Biᵀ, Bmᵀ, hTT, by rw [← Matrix.transpose_mul, hBB', Matrix.transpose_one]⟩
  have hmemB : gU ∈ Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.HR (AF F) σ JS := by
    show Formalism.UG.cT (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR (AF F) σ) Biᵀ * incM F JS * Biᵀ = incM F JS
    rw [hcR]
    simp only [Formalism.UG.cT, Matrix.transpose_map, Matrix.transpose_transpose]
    exact hcore
  refine ⟨⟨gU, hmemB⟩, ⟨a.1, hmemA⟩, rfl, ?_⟩
  show Biᵀ = ((b⁻¹).1.val)ᵀ
  rw [hBidef]

end GlobalTheory.WeilPairPartnerF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFiniteFlatAbelianSchemeHomOfQuasiInverseStatement
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isFinite_flat_abelianSchemeHom_of_quasiInverse : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A A' : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj A'] [IsCommMonObj A'], IsAbelianScheme A → IsAbelianScheme A' → ∀ (ψ : A ⟶ A') (ψ' : A' ⟶ A) (c : ℕ), c ≠ 0 → IsMonHom ψ → IsMonHom ψ' → ψ ≫ ψ' = (𝟙 A) ^ c → ψ' ≫ ψ = (𝟙 A') ^ c → IsFinite ψ.left ∧ Flat ψ.left := by
  first | (exact @GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (exact GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse) | (intros; apply GlobalTheory.IsogFiniteFlat.isFinite_and_flat_of_quasiInverse <;> assumption)
end

