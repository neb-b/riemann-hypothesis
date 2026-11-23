module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HasArcDataIff
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0058
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Degenerations.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.IsThetaPtOverMove

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaModelTorsionRationalOverFractionField
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UnitTheta

theorem torsion_descends {B V K L : Scheme.{0}} {A : Over B} {G : Over V} {H : Over K} [GrpObj A] [GrpObj G] [GrpObj H]
    {f : K ⟶ B} {j : K ⟶ V} {ψ : H.left ⟶ A.left} {π : H.left ⟶ G.left}
    (hA : IsGrpPullback H A f ψ) (hG : IsGrpPullback H G j π) (i : L ⟶ K) (n : ℕ)
    (hs : ∀ z : Over.mk (i ≫ f) ⟶ A, z ^ n = 1 → ∃ s : B ⟶ A.left, s ≫ A.hom = 𝟙 B ∧ (i ≫ f) ≫ s = z.left)
    (y : Over.mk (i ≫ j) ⟶ G) (hy : y ^ n = 1) : ∃ x : K ⟶ G.left, i ≫ x = y.left := by
  let y' : Over.mk i ⟶ H := Over.homMk (hG.1.lift y.left i (Over.w y)) (hG.1.lift_snd _ _ _)
  have e₁ : y'.left ≫ π = y.left := hG.1.lift_fst _ _ _
  have e₂ : pushHom hG (Over.mk i) y' = y := Over.OverMorphism.ext e₁
  have inj : Function.Injective (pushHom hG (Over.mk i)) := fun a b h => by
    apply Over.OverMorphism.ext
    apply hG.1.hom_ext
    · exact congrArg (fun z => z.left) h
    · rw [Over.w, Over.w]
  have e₃ : y' ^ n = 1 := inj (by rw [map_pow, e₂, map_one]; exact hy)
  obtain ⟨s, hs₁, hs₂⟩ := hs (pushHom hA (Over.mk i) y') (by rw [← map_pow, e₃, map_one])
  have w : (f ≫ s) ≫ A.hom = 𝟙 K ≫ f := by rw [Category.assoc, hs₁, Category.comp_id, Category.id_comp]
  refine ⟨hA.1.lift (f ≫ s) (𝟙 K) w ≫ π, ?_⟩
  rw [← e₁, ← Category.assoc]
  congr 1
  apply hA.1.hom_ext
  · rw [Category.assoc, hA.1.lift_fst, ← Category.assoc, hs₂]
    rfl
  · rw [Category.assoc, hA.1.lift_snd, Category.comp_id]
    exact (Over.w y').symm

theorem torsion_rational : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (m : ℕ), m ∣ S.r * S.N → ∀ y : Over.mk (spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ jK u.V) ⟶ u.G, y ^ m = 1 → ∃ x : Sp (FractionRing u.V) ⟶ u.G.left, spMap (algebraMap (FractionRing u.V) (PadicAlgCl p)) ≫ x = y.left := by
  intro o Ω _ _ _ S ρ p _ y₀ u m hm y hy
  have := u.U.gen_hom
  have hA := ((isGrpPullback_of_iso u.U.gen).comp u.cart).congr (Category.id_comp _) rfl
  refine torsion_descends hA (isGrpPullback_pullback u.G (jK u.V)) _ (S.r * S.N) (fun z hz => ?_) y ?_
  · obtain ⟨a, ha, -⟩ := ρ.pt_bij (PadicAlgCl p) _ z hz
    exact ⟨(ρ.pt a).left, Over.w (ρ.pt a), congrArg (fun t => t.left) ha⟩
  · obtain ⟨c, hc⟩ := hm
    rw [hc, pow_mul, hy, one_pow]

end GlobalTheory.UnitTheta
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniformisationChartValueFormsCorrespond
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.LN.PreForm

theorem gs_comp_stalk {X Y Z : Scheme.{0}} (r : Z ⟶ Y) (h : Y ⟶ X) (z : Z) (U : X.Opens) (hU : h (r z) ∈ U)
    (a : Γ(X, U)) : gs (r ≫ h) z U a = (r.stalkMap z).hom (gs h (r z) U a) := by
  rw [← gs_pull r h z U hU, gs_eq r z (h ⁻¹ᵁ U) hU, gs_eq h (r z) U hU]
  exact (Scheme.Hom.germ_stalkMap_apply r (h ⁻¹ᵁ U) z hU _).symm

theorem sval_comp_stalk {X Y Y' Z : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (r : Z ⟶ Y') (z : Z) {J : (Z ⟶ X) → L.ι} (hJ : Good L z J) :
    sval s (r ≫ h) z J = (r.stalkMap z).hom (sval s h (r z) (fun ψ => J (r ≫ ψ))) := by
  rw [sval_of s (r ≫ h) z J (fun k => J (r ≫ h ≫ φ k)) (fun k => by rw [Category.assoc])]
  exact gs_comp_stalk r h z _ (Set.mem_iInter.2 fun k => hJ (r ≫ h ≫ φ k)) _

theorem sval_eq_of_id {X Y Y' : Scheme.{0}} {L : LB X} {K K' : Type} [Fintype K] [Fintype K']
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} {φ' : K' → (Y' ⟶ X)} {ε' : K' → ℤ}
    (s : LB.Sec (LB.LinComb L φ ε)) (s' : LB.Sec (LB.LinComb L φ' ε')) (h : Y' ⟶ Y)
    (H : ∀ y J, Good L y J → sval s' (𝟙 Y') y J = sval s h y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y') (z : Z) (J : (Z ⟶ X) → L.ι) (hJ : Good L z J) :
    sval s' r z J = sval s (r ≫ h) z J := by
  have e := sval_comp_stalk s' (𝟙 Y') r z hJ
  rw [Category.comp_id] at e
  rw [e, sval_comp_stalk s h r z hJ, H (r z) (fun ψ => J (r ≫ ψ)) (fun ψ => hJ (r ≫ ψ))]

theorem under_iff_match {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
    (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G) : Under U U₀ ↔ Match U U₀ :=
  ⟨fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩,
    fun ⟨a, b, c, d, e, f⟩ => ⟨a.symm, b.symm, c.symm, d.symm, e.symm, f.symm⟩⟩

theorem under_exists_and_expands : Laws → Laws2 → ∀ (R : Type) [CommRing R] [IsDomain R] (I : Ideal R) (D : DegData R I) (A : PolAV (Sp (FractionRing R))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → (∀ U₀ : UnifPre I D A G, ∃ U : PreU I D.toPre A G, Under U U₀) ∧ (∀ U : PreU I D.toPre A G, ∃ U₀ : UnifPre I D A G, Under U U₀) ∧ ∀ (U : PreU I D.toPre A G) (U₀ : UnifPre I D A G), Under U U₀ → ∀ (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D.toPre (𝟙_ _) k α) (σ₀ : H0 U₀.LG.L k) (f₀ : ∀ α, D.toPre.SecB k α), (∀ σ₁ : H0 U.P.L.L k, HEq σ₁ σ₀ → ∀ z J, Good U.P.L.L z J → sval σ (𝟙 _) z J = sval σ₁ (snd (𝟙_ _) G).left z J) → (∀ α z J, Good D.toPre.P.L z J → sval (f α) (𝟙 _) z J = sval (f₀ α) (snd (𝟙_ _) D.toPre.P.A).left z J) → (U.ExpT (𝟙_ _) k σ f ↔ ∀ e, U₀.ExpandsAt e k σ₀ f₀) := by
  intro hL _ R _ _ I D A G _ _ hG
  refine ⟨fun U₀ => ?_, fun U => ?_, fun U U₀ hU k σ f σ₀ f₀ hσ hf => ?_⟩
  · obtain ⟨w, hw⟩ := U₀.ext
    obtain ⟨U, hU, -⟩ := GlobalTheory.ValueForm.exists_preU_match hL.globalFns R I D A G U₀ hG w hw
    exact ⟨U, (under_iff_match U U₀).2 hU⟩
  · obtain ⟨U₀, hU⟩ := GlobalTheory.UU.ToChart.exists_match R I D A G U
    exact ⟨U₀, (under_iff_match U U₀).2 hU⟩
  · have hM := (under_iff_match U U₀).1 hU
    have ht : H0 U₀.LG.L k = H0 U.P.L.L k := by rw [hM.LG]
    have hc : HEq (cast ht σ₀) σ₀ := cast_heq ht σ₀
    have sG : SameG (cast ht σ₀) σ := fun Z r z J hJ => sval_eq_of_id _ _ _ (hσ _ hc) Z r z J hJ
    have sB : SameB f₀ f := fun α Z r z J hJ => sval_eq_of_id _ _ _ (hf α) Z r z J hJ
    exact ⟨expandsAt_of_expT R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB,
      expT_of_expandsAt R I D A G U U₀ hM k σ₀ _ σ f₀ f hc.symm sG sB⟩

end GlobalTheory.LN.PreForm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitMapSnd
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU
open GlobalTheory.LN

noncomputable section
namespace GlobalTheory.ExpCmp
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ExpTrans GlobalTheory.UnitSec

def unitMap {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    (𝟙_ (Over S') ⊗ G').left ⟶ (𝟙_ (Over S) ⊗ G).left :=
  (snd (𝟙_ (Over S')) G').left ≫ F ≫ (λ_ G).inv.left

theorem unitMap_snd {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left) :
    unitMap F ≫ (snd (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S')) G').left ≫ F := by
  rw [unitMap, Category.assoc, Category.assoc, unit_inv_snd, Category.comp_id]

theorem eq_unitMap {S S' Z : Scheme.{0}} {G : Over S} {G' : Over S'} (F : G'.left ⟶ G.left)
    {r' : Z ⟶ (𝟙_ (Over S') ⊗ G').left} {r : Z ⟶ (𝟙_ (Over S) ⊗ G).left}
    (h : r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F) : r = r' ≫ unitMap F := by
  rw [unitMap, ← Category.assoc _ F, ← Category.assoc r', ← h, Category.assoc, snd_unit_inv, Category.comp_id]

theorem fst_unit {S : Scheme.{0}} (G : Over S) :
    (fst (𝟙_ (Over S)) G).left = (snd (𝟙_ (Over S)) G).left ≫ G.hom :=
  ((Category.comp_id _).symm.trans (Over.w (fst (𝟙_ (Over S)) G))).trans (Over.w (snd (𝟙_ (Over S)) G)).symm

variable {R V : Type} [CommRing R] [IsDomain R] [CommRing V] [IsDomain V]

theorem famφB_comp {φ : R →+* V} {D : DegPre R} {D' : DegPre V} {β : D'.P.A.left ⟶ D.P.A.left}
    (pb : IsGrpPullback D'.P.A D.P.A (spMap φ) β) {α' : D'.X} {α : D.X}
    (hc : (D'.c α').left ≫ β = spMap φ ≫ (D.c α).left) (i : Fin 4) :
    D'.famφB α' i ≫ β = β ≫ D.famφB α i := by
  have push : pushHom pb D'.P.A (cP D' _ α') = cP D _ α := Over.OverMorphism.ext (by
    show (D'.P.A.hom ≫ (D'.c α').left) ≫ β = (D'.P.A.hom ≫ spMap φ) ≫ (D.c α).left
    rw [Category.assoc, hc, Category.assoc])
  let ρ := pushHom pb D'.P.A (𝟙 _)
  have hρ : ρ.left = β := Category.id_comp _
  fin_cases i
  · exact (Category.id_comp _).trans (Category.comp_id _).symm
  · have e₁ : pushHom pb _ (𝟙 _ * cP D' _ α') = ρ ≫ (𝟙 _ * cP D _ α) := by
      rw [map_mul, push, MonObj.comp_mul, comp_cP, Category.comp_id]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb _ (cP D' _ α') = ρ ≫ cP D _ α := by rw [push, comp_cP]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)
  · have e₁ : pushHom pb D'.P.A 1 = ρ ≫ (1 : D.P.A ⟶ D.P.A) := by rw [map_one, MonObj.comp_one]
    exact (congrArg (fun q => q.left) e₁).trans (congrArg (· ≫ _) hρ)

theorem prod_fam {D : DegPre R} {T : Over (Spec (CommRingCat.of R))} (p : T ⟶ D.P.A) (k : ℕ)
    {M : Type} [CommGroup M] (ω : (T.left ⟶ D.P.A.left) → M) (α : D.X) :
    (∏ a, ω (p.left ≫ D.famφB α a) ^ DegPre.famε k a) * ∏ a, ω (D.Oφ p α a) ^ Oinvε a =
      ω p.left ^ k := by
  have a₀ : p.left ≫ D.famφB α 0 = p.left := Category.comp_id _
  have a₁ : p.left ≫ D.famφB α 1 = D.Oφ p α 0 := congrArg (fun z => z.left)
    ((MonObj.comp_mul p (𝟙 _) (cP D _ α)).trans
      (congrArg₂ (· * ·) (Category.comp_id _) (comp_cP D _ α)))
  have a₂ : p.left ≫ D.famφB α 2 = D.Oφ p α 1 :=
    congrArg (fun z => z.left) (comp_cP D p α)
  have a₃ : p.left ≫ D.famφB α 3 = D.Oφ p α 3 :=
    congrArg (fun z : _ ⟶ D.P.A => z.left) (MonObj.comp_one (M := D.P.A) p)
  have a₄ : D.Oφ p α 2 = p.left := rfl
  rw [Fin.prod_univ_four, Fin.prod_univ_four, a₀, a₁, a₂, a₃, a₄]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow, ofMul_pow, DegPre.famε, Oinvε, Matrix.cons_val]
  module

omit [IsDomain R] [IsDomain V] in
theorem exists_level {I : Ideal R} {I' : Ideal V} {φ : R →+* V} (hI : I.map φ ≤ I')
    {G : Over (Spec (CommRingCat.of R))} {G' : Over (Spec (CommRingCat.of V))} {F : G'.left ⟶ G.left}
    (hF : F ≫ G.hom = G'.hom ≫ spMap φ) (e : ℕ) :
    ∃ m : (thickObj V I' e G').left ⟶ (thickObj R I e G).left,
      m ≫ (fstG I e G).left = (fstG I' e G').left ≫ F := by
  have hle : I ^ (e + 1) ≤ (I' ^ (e + 1)).comap φ :=
    Ideal.map_le_iff_le_comap.1 (by rw [Ideal.map_pow]; exact Ideal.pow_right_mono hI _)
  refine ⟨pullback.lift ((fstG I' e G').left ≫ F)
    (pullback.snd G'.hom (thick V I' e) ≫ spMap (Ideal.quotientMap (I' ^ (e + 1)) φ hle)) ?_, pullback.lift_fst _ _ _⟩
  have e2 : (fstG I' e G').left ≫ G'.hom = pullback.snd G'.hom (thick _ I' e) ≫ thick _ I' e := pullback.condition
  rw [Category.assoc, hF, ← Category.assoc, e2, Category.assoc, Category.assoc, ← Spec.map_comp, ← Spec.map_comp]
  rfl


set_option maxHeartbeats 1600000 in
theorem expT_cmp : ∀ (R V : Type) [CommRing R] [IsDomain R] [CommRing V] [IsDomain V] (I : Ideal R) (I' : Ideal V) (φ : R →+* V), I.map φ ≤ I' → ∀ (D : DegPre R) (D' : DegPre V) (A : PolAV (Sp (FractionRing R))) (A' : PolAV (Sp (FractionRing V))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (G' : Over (Spec (CommRingCat.of V))) [GrpObj G'] [IsCommMonObj G'] (U : PreU I D A G) (U' : PreU I' D' A' G') (F : G'.left ⟶ G.left) (C : Cmp φ U U' F) (k : ℕ) (σ : U.SecGT (𝟙_ _) k) (f : ∀ α, SecBT D (𝟙_ _) k α), U.ExpT (𝟙_ _) k σ f → ∃ (σ' : U'.SecGT (𝟙_ _) k) (f' : ∀ α, SecBT D' (𝟙_ _) k α), U'.ExpT (𝟙_ _) k σ' f' ∧ (∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J') ∧ ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, gw C.v (r' ≫ famφT D' (𝟙_ _) α i) z (J (r' ≫ famφT D' (𝟙_ _) α i ≫ C.β)) (J' (r' ≫ famφT D' (𝟙_ _) α i)) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
  intro R V _ _ _ _ I I' φ hI D D' A A' G _ _ G' _ _ U U' F C k σ f hE
  classical
  have hcG : ∀ _ : Fin 1, (snd (𝟙_ _) G').left ≫ F = unitMap F ≫ (snd (𝟙_ _) G).left :=
    fun _ => (unitMap_snd F).symm
  have hcB : ∀ α i, famφT D' (𝟙_ _) α i ≫ C.β = unitMap C.β ≫ famφT D (𝟙_ _) (C.xe α) i := fun α i => by
    rw [famφT_eq, famφT_eq, ← Category.assoc (unitMap _), unitMap_snd, Category.assoc, Category.assoc,
      famφB_comp C.pbB (C.c_pr α)]
  obtain ⟨σ', hσ, -⟩ := SecPull.existsUnique_secPull _ _ _ _ U.P.L.L U'.P.L.L F U.P.L.isLB U'.P.L.isLB C.wL
    C.wL_map.gen (Fin 1) (fun _ => (snd (𝟙_ _) G').left) (fun _ => (snd (𝟙_ _) G).left) (fun _ => (k : ℤ))
    (unitMap F) hcG σ
  choose f' hf using fun α => (SecPull.existsUnique_secPull _ _ _ _ D.P.L D'.P.L C.β D.P.isLB D'.P.isLB C.v
    C.v_gen (Fin 4) (famφT D' (𝟙_ _) α) (famφT D (𝟙_ _) (C.xe α)) (DegPre.famε k)
    (unitMap C.β) (hcB α) (f (C.xe α))).exists
  have Hσ : ∀ (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ G').left) (r : Z ⟶ (𝟙_ _ ⊗ G).left), r ≫ (snd _ G).left = r' ≫ (snd _ G').left ≫ F → ∀ z J J', Good U.P.L.L z J → Good U'.P.L.L z J' → sval σ r z J = (gw C.wL (r' ≫ (snd _ G').left) z (J (r ≫ (snd _ G).left)) (J' (r' ≫ (snd _ G').left))).val ^ k * sval σ' r' z J' := by
    intro Z r' r hr z J J' hJ hJ'
    have := sec_val C.wL _ _ _ (unitMap F) hcG σ σ' r' z (hσ Z r' z) hJ hJ'
    rw [← eq_unitMap F hr, Fin.prod_univ_one, zpow_natCast, Units.val_pow_eq_pow_val, om, Category.assoc, ← hr] at this
    exact this
  have Hf : ∀ (α : D'.X) (Z : Scheme.{0}) (r' : Z ⟶ (𝟙_ _ ⊗ D'.P.A).left) (r : Z ⟶ (𝟙_ _ ⊗ D.P.A).left), r ≫ (snd _ D.P.A).left = r' ≫ (snd _ D'.P.A).left ≫ C.β → ∀ z J J', Good D.P.L z J → Good D'.P.L z J' → sval (f (C.xe α)) r z J = (∏ i : Fin 4, om C.v z J J' (r' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i).val * sval (f' α) r' z J' := by
    intro α Z r' r hr z J J' hJ hJ'
    have := sec_val C.v _ _ _ (unitMap C.β) (hcB α) (f (C.xe α)) (f' α) r' z (hf α Z r' z) hJ hJ'
    rw [← eq_unitMap C.β hr] at this
    exact this
  refine ⟨σ', f', fun e => ?_, Hσ, fun α Z r' r hr z J J' hJ hJ' => ?_⟩
  swap
  · have := Hf α Z r' r hr z J J' hJ hJ'
    simp only [om, Category.assoc] at this
    exact this
  obtain ⟨S, hS⟩ := hE e
  obtain ⟨m, hm⟩ := exists_level hI C.pb.1.w e
  refine ⟨S.map C.xe.symm.toEquiv.toEmbedding, fun Z x' rG' rB' hG' hB' _ z JG' J' hJG' hJ' => ?_⟩
  choose J hJ using fun ψ : Z ⟶ D.P.A.left => exists_chart D.P.isLB (ψ z)
  choose JG hJG using fun ψ : Z ⟶ G.left => exists_chart U.P.L.isLB (ψ z)
  have hJ : Good D.P.L z J := hJ
  have hJG : Good U.P.L.L z JG := hJG
  obtain ⟨x, hx⟩ : ∃ x : Z ⟶ (thickObj R I e G).left, x ≫ (fstG I e G).left = x' ≫ (fstG I' e G').left ≫ F :=
    ⟨x' ≫ m, by rw [Category.assoc, hm]⟩
  obtain ⟨hq, hlev⟩ := C.lev e Z x' x hx
  obtain ⟨hT, hW⟩ := hlev z J J' hJ hJ'
  have hW := hW (JG (x ≫ (fstG I e G).left)) (JG' (x' ≫ (fstG I' e G').left)) (hJG _) (hJG' _)
  have rG₁ : (rG' ≫ unitMap F) ≫ (snd _ G).left = rG' ≫ (snd _ G').left ≫ F := by
    rw [Category.assoc, unitMap_snd]
  have rB₁ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = rB' ≫ (snd _ D'.P.A).left ≫ C.β := by
    rw [Category.assoc, unitMap_snd]
  have rG₂ : (rG' ≫ unitMap F) ≫ (snd _ G).left = x ≫ (fstG I e G).left := by
    rw [rG₁, hx, ← Category.assoc, hG', Category.assoc]
  have rB₂ : (rB' ≫ unitMap C.β) ≫ (snd _ D.P.A).left = x ≫ (U.gt e).pG.left := by
    rw [rB₁, ← hq, ← Category.assoc, hB', Category.assoc]
  have rBG : (rB' ≫ unitMap C.β) ≫ (fst _ D.P.A).left = (rG' ≫ unitMap F) ≫ (fst _ G).left := by
    rw [fst_unit, fst_unit, ← Category.assoc, ← Category.assoc, rG₂, rB₂, Category.assoc, Category.assoc]
    exact congrArg (x ≫ ·) ((Over.w (U.gt e).pG).trans (Over.w (fstG I e G)).symm)
  obtain ⟨h0, hsum⟩ := hS Z x _ _ rG₂ rB₂ rBG z JG J hJG hJ
  have hF := fun α => Hf α Z rB' _ rB₁ z J J' hJ hJ'
  have Sg := Hσ Z rG' _ rG₁ z JG JG' hJG hJG'
  rw [rG₂, hG'] at Sg
  have hω : ∀ α, (∏ i : Fin 4, om C.v z J J' (rB' ≫ famφT D' (𝟙_ _) α i) ^ DegPre.famε k i) *
      ∏ i : Fin 4, gw C.v (x' ≫ D'.Oφ (U'.gt e).pG α i) z (J (x' ≫ D'.Oφ (U'.gt e).pG α i ≫ C.β))
          (J' (x' ≫ D'.Oφ (U'.gt e).pG α i)) ^ Oinvε i =
      gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k := by
    intro α
    have := prod_fam (U'.gt e).pG k (fun ψ => om C.v z J J' (x' ≫ ψ)) α
    have e₁ : ∀ i, rB' ≫ famφT D' (𝟙_ _) α i = x' ≫ (U'.gt e).pG.left ≫ D'.famφB α i := fun i => by
      rw [famφT_eq, ← Category.assoc, hB', Category.assoc]
    rw [← hq, ← Category.assoc x' _ C.β]
    refine Eq.trans (congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_)
      (Finset.prod_congr rfl fun i _ => ?_)) this
    · rw [e₁]
    · rw [← Category.assoc x' _ C.β]; rfl
  refine ⟨fun α' hα => ?_, ?_⟩
  · have hi : C.xe α' ∉ S := fun hc => hα (Finset.mem_map.2 ⟨C.xe α', hc, C.xe.symm_apply_apply α'⟩)
    exact (Units.mul_right_eq_zero _).1 ((hF α').symm.trans (h0 _ hi))
  · refine (gw C.v (x' ≫ (U'.gt e).pG.left) z (J (x ≫ (U.gt e).pG.left)) (J' (x' ≫ (U'.gt e).pG.left)) ^ k).mul_right_inj.1 ?_
    rw [← _root_.mul_assoc, ← Units.val_pow_eq_pow_val, ← Units.val_mul, ← mul_pow, hW, mul_pow, Units.val_mul,
      _root_.mul_assoc, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, ← Sg, hsum, Finset.sum_map, Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    obtain ⟨α', rfl⟩ := C.xe.surjective y
    have e₀ : C.xe.symm.toEquiv.toEmbedding (C.xe α') = α' := C.xe.symm_apply_apply α'
    rw [e₀, hF α', hT α', ← hω α', Units.val_mul, Units.val_mul]
    ring

end GlobalTheory.ExpCmp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UniversalBasisMoveBaseChange
section
set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.H1
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UnivBasisMove

open GlobalTheory.ThetaReal GlobalTheory.ThetaPtMove GlobalTheory.CommPairing GlobalTheory.ConstFam GlobalTheory.GlobalLift

variable {S S' : Scheme.{0}} {G : Over S} [GrpObj G] {A : Over S'} [GrpObj A]
  {f : S' ⟶ S} {φ : A.left ⟶ G.left} (hp : IsGrpPullback A G f φ)
  {T : Over S'} {T₀ : Over S} (τ : T.left ⟶ T₀.left) (hτ : τ ≫ T₀.hom = T.hom ≫ f)
  {L₀ : LB G.left} {L₁ : LB A.left} {w : LB.Iso L₁ (L₀.pull φ)} {a : ℤ}

def Rel (w : LB.Iso L₁ (L₀.pull φ)) (s : SecM A L₁ a T) (s₀ : SecM G L₀ a T₀) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (T ⊗ A).left) (z : Z) J J', Good L₀ z J → Good L₁ z J' →
    ThetaAct.sv s₀ (r ≫ psi hp τ hτ) z J =
      (wVal w z J J' (r ≫ (snd T A).left) ^ a).val * ThetaAct.sv s r z J'

theorem exists_rel (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s₀ : SecM G L₀ a T₀) :
    ∃ s, Rel hp τ hτ w s s₀ := by
  obtain ⟨s, hs⟩ := exists_secRel hp τ hτ hw hL₀ hL₁ (SecM.toSec G s₀)
  exact ⟨SecM.ofSec A s, hs⟩

theorem exists_rel_up [IsIso τ] (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) (s : SecM A L₁ a T) :
    ∃ s₀, Rel hp τ hτ w s s₀ := by
  obtain ⟨s₀, hs⟩ := exists_secRel_up hp τ hτ hw hL₀ hL₁ (SecM.toSec A s)
  exact ⟨SecM.ofSec G s₀, hs⟩

variable {hp τ hτ}

theorem Rel.unique_down (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s s' : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s' s₀) : s = s' :=
  ThetaAct.sv_ext hL₁ fun y J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' hL₀ y
    exact (Units.mul_right_inj _).1 ((h _ _ _ _ _ hJ hJ').symm.trans (h' _ _ _ _ _ hJ hJ'))

theorem Rel.unique_up [IsIso τ] (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB) {s : SecM A L₁ a T} {s₀ s₀' : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w s s₀') : s₀ = s₀' :=
  ThetaAct.sv_ext hL₀ fun y J hJ => by
    obtain ⟨J', hJ'⟩ := exists_good' hL₁ y
    obtain ⟨χ, -, h₂⟩ := WeilPull.exists_psi_inv hp τ hτ
    have h₂' : χ ≫ psi hp τ hτ = 𝟙 _ := h₂
    have q := (h _ χ y _ _ hJ hJ').trans (h' _ χ y _ _ hJ hJ').symm
    rwa [h₂'] at q

theorem Rel.add {s t : SecM A L₁ a T} {s₀ t₀ : SecM G L₀ a T₀}
    (h : Rel hp τ hτ w s s₀) (h' : Rel hp τ hτ w t t₀) : Rel hp τ hτ w (s + t) (s₀ + t₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_add _ _ _ _ hJ, ThetaAct.sv_add _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', h' _ _ _ _ _ hJ hJ', mul_add]

theorem Rel.smul {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (c : Γ(T₀.left, ⊤))
    (h : Rel hp τ hτ w s s₀) : Rel hp τ hτ w (τ.appTop.hom c • s) (c • s₀) :=
  fun Z r z J J' hJ hJ' => by
    rw [ThetaAct.sv_smul _ _ _ _ hJ, ThetaAct.sv_smul _ _ _ _ hJ', h _ _ _ _ _ hJ hJ', mul_left_comm,
      Category.assoc, psi_fst', ← Category.assoc]
    exact congrArg (fun x => _ * (x * _)) (gs_pull _ τ z ⊤ trivial c).symm

theorem Rel.pull {s : SecM A L₁ a T} {s₀ : SecM G L₀ a T₀} (h : Rel hp τ hτ w s s₀)
    {T' : Over S'} {T₀' : Over S} (σ : T'.left ⟶ T₀'.left) (hσ : σ ≫ T₀'.hom = T'.hom ≫ f)
    (u : T' ⟶ T) (u₀ : T₀' ⟶ T₀) (hu : σ ≫ u₀.left = u.left ≫ τ) :
    Rel hp σ hσ w (VVRank.pullM A L₁ a u s) (VVRank.pullM G L₀ a u₀ s₀) :=
  fun Z r z J J' hJ hJ' => by
    have e : psi hp σ hσ ≫ (u₀ ▷ G).left = (u ▷ A).left ≫ psi hp τ hτ := by
      refine psi_ext ?_ ?_
      · rw [Category.assoc, ← Over.comp_left, whiskerRight_fst, Over.comp_left, ← Category.assoc, psi_fst',
          Category.assoc, Category.assoc, psi_fst', hu, ← Category.assoc (u ▷ A).left, ← Over.comp_left,
          whiskerRight_fst, Over.comp_left, Category.assoc]
      · rw [Category.assoc, VVRank.whisker_snd_left, psi_snd', Category.assoc, psi_snd', ← Category.assoc,
          VVRank.whisker_snd_left]
    have q := h _ (r ≫ (u ▷ A).left) z _ _ hJ hJ'
    rw [Category.assoc, Category.assoc, ← e, VVRank.whisker_snd_left, ← Category.assoc] at q
    exact (VVRank.sv_pullS G a u₀ (SecM.toSec G s₀) _ z hJ).trans
      (q.trans (congrArg _ (VVRank.sv_pullS A a u (SecM.toSec A s) _ z hJ').symm))

theorem exists_linearEquiv (hp : IsGrpPullback A G f φ) (hw : w.IsGen) (hL₀ : L₀.IsLB) (hL₁ : L₁.IsLB)
    (a : ℤ) (T : Over S') :
    ∃ E : SecM G L₀ a (Over.mk (T.hom ≫ f)) ≃ₗ[Γ(T.left, ⊤)] SecM A L₁ a T,
      ∀ x, Rel hp (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) w (E x) x := by
  have : IsIso (C := Scheme.{0}) (X := T.left) (Y := (Over.mk (T.hom ≫ f)).left) (𝟙 T.left) := IsIso.id _
  choose D hD using exists_rel hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _) (a := a)
    hw hL₀ hL₁
  let l : SecM G L₀ a (Over.mk (T.hom ≫ f)) →ₗ[Γ(T.left, ⊤)] SecM A L₁ a T :=
    { toFun := D
      map_add' := fun x y => (hD _).unique_down hL₀ hL₁ ((hD x).add (hD y))
      map_smul' := fun c x => (hD _).unique_down hL₀ hL₁ (Rel.smul (T₀ := Over.mk (T.hom ≫ f)) (τ := 𝟙 T.left) c (hD x)) }
  refine ⟨LinearEquiv.ofBijective l ⟨fun x y e => ?_, fun s => ?_⟩, hD⟩
  · have e' : D x = D y := e
    exact (hD x).unique_up hL₀ hL₁ (e' ▸ hD y)
  · obtain ⟨s₀, hs⟩ := exists_rel_up hp (T := T) (T₀ := Over.mk (T.hom ≫ f)) (𝟙 T.left) (Category.id_comp _)
      hw hL₀ hL₁ s
    exact ⟨s₀, (hD s₀).unique_down hL₀ hL₁ hs⟩

theorem univBasis_move : ∀ (S S' : Scheme.{0}) (f : S' ⟶ S) (P : PolAV S) (P' : PolAV S') (φ : P'.A.left ⟶ P.A.left), IsGrpPullback P'.A P.A f φ → LBIso P'.L (P.L.pull φ) → ∀ (n : ℤ) (κ : Type) [Fintype κ] (T₀ : Over S) (τ : S' ⟶ T₀.left), τ ≫ T₀.hom = f → ∀ b₀ : κ → SecM P.A P.L n T₀, UnivBasis P n b₀ → ∃ b : κ → SecM P'.A P'.L n (baseOver S'), UnivBasis P' n b := by
  intro S S' f P P' φ hp hw n κ _ T₀ τ hτ b₀ hb₀
  obtain ⟨w, hw⟩ := hw
  have hτ' : τ ≫ T₀.hom = (baseOver S').hom ≫ f := hτ.trans (Category.id_comp _).symm
  choose b hb using fun i => exists_rel hp (T := baseOver S') τ hτ' hw P.isLB P'.isLB (b₀ i)
  refine ⟨b, fun T hT h => ?_⟩
  have hh : h.left = T.hom := (Category.comp_id _).symm.trans (Over.w h)
  let h₀ : Over.mk (T.hom ≫ f) ⟶ T₀ := Over.homMk (T.hom ≫ τ) (by
    change (T.hom ≫ τ) ≫ T₀.hom = T.hom ≫ f
    rw [Category.assoc, hτ])
  have : IsAffine (Over.mk (T.hom ≫ f)).left := hT
  obtain ⟨c, hc⟩ := hb₀ _ h₀
  obtain ⟨E, hE⟩ := exists_linearEquiv hp hw P.isLB P'.isLB n T
  refine ⟨Module.Basis.map (R := Γ(T.left, ⊤)) c E, fun i => ?_⟩
  refine (hE (c i)).unique_down P.isLB P'.isLB ?_
  rw [hc]
  exact (hb i).pull _ _ h h₀ ((Category.id_comp _).trans (congrArg (· ≫ τ) hh.symm))

end GlobalTheory.UnivBasisMove
end
end

