module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0062
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1888
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1924
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2210
public import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2166
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2216
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2116
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2195
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2168
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2086
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0438
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0026
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0022
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2021
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2110
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2199
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.DescGen
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2191
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2207
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0065
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierDivisorMultCharacterize
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.TopForm GlobalTheory.CechPic GlobalTheory.QCoh GlobalTheory.Discrepancy GlobalTheory.LogPair

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.MultEff

open CartierDiv

variable {X : Scheme.{0}} [IsIntegral X] [IsLocallyNoetherian X]

theorem ord_one (z : X) : Scheme.ord (1 : X.functionField) z = 0 := (unitAt_one z).ord_eq_zero

theorem mult_zero (z : X) : (0 : CartierDiv X).mult z = 0 := by
  rw [(isEqn_zero z).mult_eq, Units.val_one, ord_one]

theorem mult_neg (D : CartierDiv X) (z : X) : (-D).mult z = - D.mult z := by
  have h := mult_add D (-D) z
  rw [add_neg_cancel, mult_zero] at h
  omega

theorem ord_inv (u : X.functionFieldˣ) (z : X) :
    Scheme.ord ((u⁻¹ : X.functionFieldˣ) : X.functionField) z = - Scheme.ord (u : X.functionField) z := by
  have h := Scheme.ord_mul (x := z) u.ne_zero (u⁻¹).ne_zero
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one, ord_one] at h
  omega

theorem IsEqn.of_specializes {D : CartierDiv X} {x z : X} {g : X.functionFieldˣ} (h : D.IsEqn x g)
    (hz : z ⤳ x) : D.IsEqn z g := by
  obtain ⟨U, hU, hg⟩ := h.exists_nhds
  exact hg z (hz.mem_open U.isOpen hU)

variable [GlobalTheory.IsNormalScheme X]

theorem regAt_iff_ord (x : X) (u : X.functionFieldˣ) :
    RegAt x (u : X.functionField) ↔ ∀ z, z ⤳ x → 0 ≤ Scheme.ord (u : X.functionField) z := by
  rw [← regularAt_zero_iff, _root_.GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes X (0 : CartierDiv X) x u]
  simp only [mult_zero, add_zero]

theorem unitAt_of_ord (x : X) (u : X.functionFieldˣ)
    (h : ∀ z, z ⤳ x → Scheme.ord (u : X.functionField) z = 0) : UnitAt x (u : X.functionField) := by
  rw [unitAt_iff u.ne_zero, ← Units.val_inv_eq_inv_val, regAt_iff_ord, regAt_iff_ord]
  exact ⟨fun z hz => (h z hz).ge, fun z hz => by rw [ord_inv, h z hz, neg_zero]⟩

theorem eff_supp_eq_of_mult : ∀ (X : Scheme.{0}) [IsIntegral X] [IsLocallyNoetherian X] [GlobalTheory.IsNormalScheme X] (D : CartierDiv X), (D.Eff ↔ ∀ z, 0 ≤ D.mult z) ∧ (∀ x, x ∈ D.supp ↔ ∃ z, z ⤳ x ∧ D.mult z ≠ 0) ∧ (∀ E : CartierDiv X, (∀ z, D.mult z = E.mult z) → D = E) ∧ ∀ (x : X) (g : X.functionFieldˣ), (∀ z, z ⤳ x → Scheme.ord (g : X.functionField) z = D.mult z) → D.IsEqn x g := by
  intro X _ _ _ D
  have hEff : ∀ F : CartierDiv X, F.Eff ↔ ∀ z, 0 ≤ F.mult z := by
    intro F
    refine ⟨fun h z => ?_, fun h x => ?_⟩
    · have := (_root_.GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes X F z 1).1 (h z) z (specializes_refl z)
      simpa [Units.val_one, ord_one] using this
    · have := (_root_.GlobalTheory.RegCodimOne.regularAt_iff_forall_specializes X F x 1).2 fun z _ => by simpa [Units.val_one, ord_one] using h z
      simpa using this
  refine ⟨hEff D, fun x => ⟨fun hx => ?_, fun ⟨z, hz, hm⟩ => ?_⟩, fun E h => ?_, fun x g h => ?_⟩
  · by_contra hne
    push_neg at hne
    obtain ⟨g, hg⟩ := D.exists_isEqn x
    refine (hg.mem_supp_iff.1 hx) (unitAt_of_ord x g fun z hz => ?_)
    rw [← (IsEqn.of_specializes hg hz).mult_eq]
    exact hne z hz
  · exact hz.mem_closed D.supp.isClosed (mem_supp_of_mult_ne_zero hm)
  · have h1 : (D - E).Eff := (hEff _).2 fun z => by
      rw [sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    have h2 : (-(D - E)).Eff := (hEff _).2 fun z => by
      rw [mult_neg, sub_eq_add_neg, mult_add, mult_neg, h z]; omega
    exact sub_eq_zero.1 (h1.eq_zero h2)
  · obtain ⟨g', hg'⟩ := D.exists_isEqn x
    refine hg'.iff_unitAt.2 ?_
    have e : ((g / g' : X.functionFieldˣ) : X.functionField) = (g : X.functionField) / g' :=
      Units.val_div_eq_div_val g g'
    rw [← e]
    refine unitAt_of_ord x _ fun z hz => ?_
    have hm := (IsEqn.of_specializes hg' hz).mult_eq
    rw [Units.val_div_eq_div_val, div_eq_mul_inv, Scheme.ord_mul g.ne_zero (inv_ne_zero g'.ne_zero),
      ← Units.val_inv_eq_inv_val, ord_inv, h z hz, hm]
    ring

end GlobalTheory.Cartier.MultEff
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartierSectionsFlatBaseChangeLinearlyDisjoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc
open TensorProduct

set_option autoImplicit false
noncomputable section
namespace GlobalTheory.SecFlatBC

section Helpers

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁]

theorem zero_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) : (0 : F₁) ∈ spanBy c T :=
  ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

theorem add_mem_spanBy (c : R₁ →+* F₁) (T : Set F₁) {a b : F₁} (ha : a ∈ spanBy c T) (hb : b ∈ spanBy c T) :
    a + b ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := ha
  obtain ⟨m, r', t', ht', rfl⟩ := hb
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · simpa using ht i
    · simpa using ht' i
  · rw [Fin.sum_univ_add]; simp

theorem spanBy_mul (c : R₁ →+* F₁) (T : Set F₁) (w : F₁) :
    spanBy c ((w * ·) '' T) = (w * ·) '' spanBy c T := by
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose s hs e using ht
    refine ⟨∑ i, c (r i) * s i, ⟨n, r, s, hs, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by rw [← e i]; ring
  · rintro ⟨_, ⟨n, r, t, ht, rfl⟩, rfl⟩
    refine ⟨n, r, fun i => w * t i, fun i => ⟨_, ht i, rfl⟩, ?_⟩
    dsimp only
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

end Helpers

theorem fnOf_algX {R : Type} [CommRing R] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp R) (U : X.Opens)
    (hg : genericPoint X ∈ U) (a : R) :
    GlobalTheory.Cartier.fnOf U hg (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U a) = GlobalTheory.Desc.cst p a := by
  simp only [ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX, GlobalTheory.Desc.cst, RingHom.comp_apply]
  have := X.presheaf.germ_res_apply (homOfLE (show U ≤ p ⁻¹ᵁ ⊤ from le_top)) (genericPoint X) hg
    ((p.app ⊤).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a))
  exact this

theorem span_chart {R R₁ : Type} [CommRing R] [CommRing R₁] {ρ : R →+* R₁} {X Y V : Scheme.{0}} [IsIntegral X]
    [IsIntegral Y] {p : X ⟶ Sp R} {q : Y ⟶ Sp R₁} {i : V ⟶ Y} [IsOpenImmersion i] {φ : V ⟶ X}
    {θ : X.functionField →+* Y.functionField} (H : IsPullback φ (i ≫ q) p (spMap ρ)) (hP : PFF i φ θ)
    {U : X.Opens} (hU : IsAffineOpen U) (hg : genericPoint X ∈ U) :
    spanBy (GlobalTheory.Desc.cst q) (θ '' Set.range (GlobalTheory.Cartier.fnOf U hg)) =
      {v | ∀ z : V, φ z ∈ U → GlobalTheory.Cartier.RegAt (i z) v} := by
  letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U).toAlgebra
  letI := ρ.toAlgebra
  obtain ⟨β, -, hβ, hr⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U hU hg
  rw [← hr]
  ext v; constructor
  · rintro ⟨n, r, t, ht, rfl⟩
    choose a ha e using ht
    choose b hb using ha
    refine ⟨∑ j, b j ⊗ₜ[R] r j, ?_⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [hβ, hb, e, _root_.mul_comm]
  · rintro ⟨x, rfl⟩
    induction x using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact zero_mem_spanBy _ _
    | tmul b r =>
      refine ⟨1, fun _ => r, fun _ => θ (GlobalTheory.Cartier.fnOf U hg b), fun _ => ⟨_, ⟨b, rfl⟩, rfl⟩, ?_⟩
      rw [hβ, Fin.sum_univ_one, _root_.mul_comm]
    | add x y hx hy => rw [map_add]; exact add_mem_spanBy _ _ hx hy

theorem sections_linDisj_flatBaseChange : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁), ρ.Flat → ∀ (X Y V : Scheme.{0}) [IsIntegral X] [IsIntegral Y] (p : X ⟶ Sp R) (q : Y ⟶ Sp R₁) (i : V ⟶ Y) [IsOpenImmersion i] (φ : V ⟶ X) (θ : X.functionField →+* Y.functionField), QuasiCompact p → QuasiSeparated p → IsPullback φ (i ≫ q) p (spMap ρ) → PFF i φ θ → ∀ (D : CartierDiv X) (D₁ : CartierDiv Y), PPull i φ θ D D₁ → LinDisj (GlobalTheory.Desc.cst p) (GlobalTheory.Desc.cst q) θ ∧ ∀ k : ℕ, {v | ∀ z : V, (k • D₁).RegularAt (i z) v} = spanBy (GlobalTheory.Desc.cst q) (θ '' Sec D k) := by
  intro R R₁ _ _ ρ hρ X Y V _ _ p q i _ φ θ _ _ H hP D D₁ hD
  letI : Algebra R X.functionField := (GlobalTheory.Desc.cst p).toAlgebra
  letI : Algebra R R₁ := ρ.toAlgebra
  haveI : Module.Flat R R₁ := hρ
  obtain ⟨U₀, hU₀, hg₀, -⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens
    (show genericPoint X ∈ (⊤ : X.Opens) from trivial)
  have hc : ∀ a : R, θ (algebraMap R X.functionField a) = GlobalTheory.Desc.cst q (algebraMap R R₁ a) := by
    intro a
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    obtain ⟨β, -, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    have e : (algebraMap R Γ(X, U₀) a) ⊗ₜ[R] (1 : R₁) = (1 : Γ(X, U₀)) ⊗ₜ[R] (algebraMap R R₁ a) := by
      rw [Algebra.algebraMap_eq_smul_one, Algebra.algebraMap_eq_smul_one a, TensorProduct.smul_tmul]
    have e' := congrArg β e
    simp only [hβ, _root_.map_one, _root_.mul_one, _root_.one_mul] at e'
    rw [← e']
    exact congrArg θ (fnOf_algX p U₀ hg₀ a).symm
  have hinj : ∀ (n : ℕ) (u : Fin n → X.functionField) (r : Fin n → R₁),
      ∑ j, GlobalTheory.Desc.cst q (r j) * θ (u j) = 0 → ∑ j, u j ⊗ₜ[R] r j = 0 := by
    letI := (ReciprocityTheory.ChartRestriction.G.DVR.FlatBC.algX p U₀).toAlgebra
    haveI : Nonempty U₀ := ⟨⟨_, hg₀⟩⟩
    haveI : IsFractionRing Γ(X, U₀) X.functionField := functionField_isFractionRing_of_isAffineOpen X U₀ hU₀
    have hal : ∀ b, algebraMap Γ(X, U₀) X.functionField b = GlobalTheory.Cartier.fnOf U₀ hg₀ b := fun b => rfl
    haveI : IsScalarTower R Γ(X, U₀) X.functionField :=
      IsScalarTower.of_algebraMap_eq fun a => ((hal _).trans (fnOf_algX p U₀ hg₀ a)).symm
    obtain ⟨β, hβi, hβ, -⟩ := GlobalTheory.T.exists_tensor_sections_embed_functionField_regular R R₁ ρ X Y V p q i φ θ H hP U₀ hU₀ hg₀
    exact GlobalTheory.T.tensor_fraction_injective_of_tensor_injective R R₁ Γ(X, U₀) X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) β hβi
      (fun b r => (hβ b r).trans (by rw [hal]))
  refine ⟨GlobalTheory.T.linearlyDisjoint_of_flat_baseChange_embeds R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hinj, fun k => ?_⟩
  have hloc : ∀ x : X, ∃ (U : X.Opens) (g : X.functionFieldˣ), IsAffineOpen U ∧ x ∈ U ∧ ∀ y ∈ U, D.IsEqn y g := by
    intro x
    obtain ⟨W, hxW, g, hg⟩ := D.exists_isEqn_nhds x
    obtain ⟨U, hU, hxU, hUW⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 X.isBasis_affineOpens hxW
    exact ⟨U, g, hU, hxU, fun y hy => hg y (hUW hy)⟩
  choose U g hUa hxU hUg using hloc
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace p
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun x => (U x : Set X)) (fun x => (U x).isOpen)
    (fun x _ => Set.mem_iUnion.2 ⟨x, hxU x⟩)
  have cov : ∀ y : X, ∃ j : t, y ∈ U j.1 := fun y => by
    obtain ⟨a, ha, h⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    exact ⟨⟨a, ha⟩, h⟩
  haveI : Nonempty t := ⟨(cov (genericPoint X)).choose⟩
  have hgen : ∀ j : t, genericPoint X ∈ U j.1 := fun j => GlobalTheory.Cartier.gen_mem (hxU j.1)
  let N : t → Submodule R X.functionField := fun j =>
    { carrier := {u | ∀ y ∈ U j.1, (k • D).RegularAt y u}
      add_mem' := fun ha hb y hy => (ha y hy).add (hb y hy)
      zero_mem' := fun y _ => ((k • D).vanishesAt_zero y).regularAt
      smul_mem' := fun a u hu y hy => by
        rw [Algebra.smul_def]
        exact (hu y hy).regAt_mul (GlobalTheory.Cartier.regAt_fnOf (U := ⊤) trivial trivial _) }
  have hSec : Sec D k = ⋂ j, (N j : Set X.functionField) := by
    ext u; rw [Set.mem_iInter]
    exact ⟨fun h j y _ => h y, fun h y => let ⟨j, hj⟩ := cov y; h j y hj⟩
  have hG : ∀ j : t, ∀ z : V, φ z ∈ U j.1 →
      (k • D₁).IsEqn (i z) (Units.map θ.toMonoidHom (g j.1 ^ k)) := by
    intro j z hz
    rw [map_pow]
    exact (hD z _ (hUg j.1 _ hz)).nsmul k
  have hN : ∀ j : t, (N j : Set X.functionField) =
      ((((g j.1 ^ k : X.functionFieldˣ) : X.functionField)⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
    intro j; ext u; constructor
    · intro hu
      have hreg : ∀ y ∈ U j.1, GlobalTheory.Cartier.RegAt y (u * ((g j.1 ^ k : X.functionFieldˣ) : X.functionField)) :=
        fun y hy => ((hUg j.1 y hy).nsmul k).regularAt_iff.1 (hu y hy)
      obtain ⟨b, hb⟩ := GlobalTheory.Cartier.exists_fnOf_eq (hgen j) hreg
      exact ⟨_, ⟨b, rfl⟩, by dsimp only; rw [hb, _root_.mul_comm u, ← _root_.mul_assoc, inv_mul_cancel₀ (Units.ne_zero _), _root_.one_mul]⟩
    · rintro ⟨_, ⟨b, rfl⟩, rfl⟩ y hy
      dsimp only
      rw [((hUg j.1 y hy).nsmul k).regularAt_iff, _root_.mul_comm _ ((g j.1 ^ k : X.functionFieldˣ) : X.functionField),
        ← _root_.mul_assoc, mul_inv_cancel₀ (Units.ne_zero _), _root_.one_mul]
      exact GlobalTheory.Cartier.regAt_fnOf hy (hgen j) b
  have hspan : ∀ j : t, spanBy (GlobalTheory.Desc.cst q) (θ '' (N j : Set X.functionField)) =
      {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    intro j
    set G : X.functionField := ((g j.1 ^ k : X.functionFieldˣ) : X.functionField) with hGdef
    have himg : θ '' ((G⁻¹ * ·) '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) =
        (θ G⁻¹ * ·) '' (θ '' Set.range (GlobalTheory.Cartier.fnOf (U j.1) (hgen j))) := by
      rw [Set.image_image, Set.image_image]; simp only [map_mul]
    rw [hN j, himg, spanBy_mul, span_chart H hP (hUa j.1) (hgen j)]
    have hGne : G ≠ 0 := Units.ne_zero _
    have hθG : θ G ≠ 0 := (map_ne_zero θ).2 hGne
    have hval : ∀ z : V, (((Units.map θ.toMonoidHom (g j.1 ^ k)) : Y.functionFieldˣ) : Y.functionField) = θ G :=
      fun _ => rfl
    ext v; constructor
    · rintro ⟨w, hw, rfl⟩ z hz
      rw [(hG j z hz).regularAt_iff, hval z, map_inv₀, _root_.mul_comm, ← _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.one_mul]
      exact hw z hz
    · intro hv
      refine ⟨v * θ G, fun z hz => ?_, ?_⟩
      · have := (hG j z hz).regularAt_iff.1 (hv z hz)
        rwa [hval z] at this
      · show θ G⁻¹ * (v * θ G) = v
        rw [map_inv₀, _root_.mul_comm, _root_.mul_assoc, mul_inv_cancel₀ hθG, _root_.mul_one]
  have hT : {v | ∀ z : V, (k • D₁).RegularAt (i z) v} =
      ⋂ j : t, {v | ∀ z : V, φ z ∈ U j.1 → (k • D₁).RegularAt (i z) v} := by
    ext v; rw [Set.mem_iInter]
    exact ⟨fun h j z _ => h z, fun h z => let ⟨j, hj⟩ := cov (φ z); h j z hj⟩
  rw [hT, hSec, _root_.GlobalTheory.Desc.spanBy_iInter_of_flat R R₁ X.functionField Y.functionField θ (GlobalTheory.Desc.cst q) hc hinj t N]
  exact Set.iInter_congr fun j => (hspan j).symm

end GlobalTheory.SecFlatBC
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechFirstCohomologyAwayNatural
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CechAway

theorem cech_one_away_natural : ∀ (R : Type) [CommRing R] (D : Type) [CommRing D] [Algebra R D] (n : ℕ) (s : Fin n → D), Ideal.span (Set.range s) = ⊤ → ∀ d : Fin n → Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E' (θ.comp ψ) = θ (d a b E ψ)) → (∀ (a b c : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → IsUnit (ψ (s c)) → d a b E ψ + d b c E ψ = d a c E ψ) → ∃ e : Fin n → ∀ (E : Type) [CommRing E] [Algebra R E], (D →ₐ[R] E) → E, (∀ (a : Fin n) (E : Type) [CommRing E] [Algebra R E] (E' : Type) [CommRing E'] [Algebra R E'] (ψ : D →ₐ[R] E) (θ : E →ₐ[R] E'), IsUnit (ψ (s a)) → e a E' (θ.comp ψ) = θ (e a E ψ)) ∧ ∀ (a b : Fin n) (E : Type) [CommRing E] [Algebra R E] (ψ : D →ₐ[R] E), IsUnit (ψ (s a)) → IsUnit (ψ (s b)) → d a b E ψ = e b E ψ - e a E ψ := by
  first
  | exact @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary
  | (apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> assumption)
  | (intros; apply @_root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.CocycleCoboundaryNumerator.cocycle_is_coboundary ..)

end GlobalTheory.CechAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechHyperCohomologyAffineLatticeCover
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.DeRham
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoverHyp

theorem restrict_bijective : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (s : X ⟶ Sp R) (J : Type) [Finite J] [SemilatticeInf J] (U : J → X.affineOpens) (hU : Monotone U), (∀ i j, (U (i ⊓ j)).1 = (U i).1 ⊓ (U j).1) → ⨆ i, (U i).1 = ⊤ → Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op)) := by
  intro R _ X s J _ _ U hU hinf hcov
  classical
  haveI := Fintype.ofFinite J
  let B : Type := {V : X.affineOpens // ∃ i, V.1 ≤ (U i).1}
  have hne : ∀ V : B, (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).Nonempty := fun V => by
    obtain ⟨i, hi⟩ := V.2
    exact ⟨i, Finset.mem_filter.2 ⟨Finset.mem_univ _, hi⟩⟩
  let σ : B → J := fun V => (Finset.univ.filter fun i => V.1.1 ≤ (U i).1).inf' (hne V) id
  let u : J → B := fun i => ⟨U i, i, le_rfl⟩
  have hσ : ∀ V : B, V.1.1 ≤ (U (σ V)).1 := fun V =>
    Finset.inf'_induction (p := fun i => V.1.1 ≤ (U i).1) (hne V) id
      (fun a ha b hb => by rw [hinf]; exact le_inf ha hb) fun i hi => (Finset.mem_filter.1 hi).2
  have gc : GaloisConnection σ u := fun V i =>
    ⟨fun h => (hσ V).trans (hU h), fun h =>
      Finset.inf'_le (s := Finset.univ.filter fun i : J => V.1.1 ≤ (U i).1) (id : J → J)
        (Finset.mem_filter.2 ⟨Finset.mem_univ i, h⟩)⟩
  let incl : Bᵒᵖ ⥤ AffOp X := (Monotone.functor (f := (Subtype.val : B → X.affineOpens)) fun _ _ h ↦ h).op
  have b1 : Function.Bijective (pullHyp1 (CoefMap.restrict (OAff s) incl)) :=
    GlobalTheory.T.cech_hyper_cohomology_cover_refinement R X s J (fun i => (U i).1) hcov
  have b2 := _root_.GlobalTheory.AdjHyp.main R Bᵒᵖ Jᵒᵖ (incl ⋙ OAff s) gc.monotone_u.functor.op gc.monotone_l.functor.op
    gc.adjunction.op
  have e : ∀ c, pullHyp1 (CoefMap.restrict (OAff s) hU.functor.op) c =
      pullHyp1 (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op)
        (pullHyp1 (CoefMap.restrict (OAff s) incl) c) := fun c =>
    (pullHyp1_eq_of_natTrans (CoefMap.restrict (OAff s) hU.functor.op)
      ((CoefMap.restrict (OAff s) incl).comp (CoefMap.restrict (incl ⋙ OAff s) gc.monotone_u.functor.op))
      (𝟙 _) (fun T b => mp_id (OAff s) _ b) c).trans (pullHyp1_comp _ _ c)
  have := b2.comp b1
  exact (funext e : _ = _) ▸ this

end GlobalTheory.CoverHyp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterLineBundleAdditiveOfEquivariantGenerato
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

namespace GlobalTheory.CharKer

theorem isAdditive_of_isEquivGen : ∀ (K : Type) [Field K] [IsAlgClosed K] (A A' N T : Over (Sp K)) [GrpObj A] [GrpObj A'] [GrpObj N] (i : N ⟶ A) (q : A ⟶ A') (χ : Γ((N ⊗ T).left, ⊤)ˣ) (M : LB (A' ⊗ T).left) (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ), IsAbelianScheme A → IsAbelianScheme A' → IsMonHom i → IsMonHom q → IsFinite q.left → Flat q.left → Surjective q.left → IsPullback i (toUnit N) q η[A'] → IsCharacter χ → M.IsLB → IsEquivGen i q χ M e → IsAdditive M := by
  intro K _ _ A A' N T _ _ _ i q χ M e hA hA' hi hq hfin hflat hsurj hker hχ hM he
  haveI := hA
  haveI := hq
  haveI : IsCommMonObj A := IsAbelianScheme.comm
  obtain ⟨h₁, h₂, h₃⟩ := _root_.GlobalTheory.CharKer.pmap2_flat_surjective_isAffineHom _ A A' T q hflat hsurj inferInstance
  exact isAdditive_of_universal hM (_root_.GlobalTheory.CharKer.triv_of_isPullGen_of_invariant _ _ (pmap2 q T).left h₁ h₂ h₃ (addBundle M) (addGen q M e)
    (_root_.GlobalTheory.CharKer.isPullGen_addGen _ A A' T q M e he.1) (_root_.GlobalTheory.CharKer.addGen_invariant _ A A' N T i q χ M e hi hker hχ he))

end GlobalTheory.CharKer
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChartSome
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

def transl {S : Scheme.{0}} {G : Over S} [GrpObj G] (y : Over.mk (𝟙 S) ⟶ G) : G ⟶ G :=
  𝟙 G * (Over.homMk G.hom (by simp) ≫ y)

def Near.chart {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S} [GrpObj G]
    (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) : Option (Fin n) → (pullback N.U.hom π ⟶ G.left)
  | none => N.u
  | some k => N.u ≫ (transl (x k)⁻¹).left

theorem Near.chart_some {R : Type} [CommRing R] [IsLocalRing R] {S : Scheme.{0}} {π : S ⟶ Sp R} {G : Over S}
    [GrpObj G] (N : Near π G) {n : ℕ} (x : Fin n → (Over.mk (𝟙 S) ⟶ G)) (k : Fin n) :
    N.chart x (some k) = N.u ≫ (transl (x k)⁻¹).left := rfl

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChiEqOfTorsion
section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct WithConv
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB RigLB CubicalStr Theta thφ thε thK x3)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.PtExt

theorem comp_pow_pt {R : Type} [CommRing R] {A : Over (Sp R)} [GrpObj A] {T T' : Over (Sp R)} (ρ : T' ⟶ T)
    (x : T ⟶ A) (m : ℕ) : ρ ≫ x ^ m = (ρ ≫ x) ^ m :=
  MonObj.comp_pow x m ρ

theorem chi_eq_of_torsion : ∀ (R : Type) [CommRing R] (A : Over (Sp R)) [GrpObj A] [IsCommMonObj A] (n : ℕ),
    (n : R) = 0 → HasRoots (A := A) n → ∀ b : Fn0 A, IsTorsChar n b → ∀ S : SecFam A,
    (∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), IsSec n b x (S D x)) → ∀ g : Fn2 A, IsSecAdd n S g →
    ∀ (D : Type) [CommRing D] [Algebra R D] (x : Pt A D), x ^ n = 1 → chi n g D x = b D x := by
  intro R _ A _ _ n hn hR b hb S hS g hg D _ _ x hx
  obtain ⟨E, _, _, ψ, z, hff, hz⟩ := hR D x
  apply hff.injective
  change ψ (chi n g D x) = ψ (b D x)
  have hpow : ∀ i : ℕ, (z ^ i) ^ n = spOver ψ ≫ x ^ i := by
    intro i
    rw [← pow_mul, mul_comm, pow_mul, hz, comp_pow_pt]

  have hterm : ∀ i : ℕ, ψ (g D (x ^ i) x) =
      (S D (x ^ (i + 1)) E ψ (z ^ (i + 1)) - S D (x ^ i) E ψ (z ^ i)) - S D x E ψ z := by
    intro i
    have h := hg D (x ^ i) x E ψ (z ^ i) z (hpow i) hz
    rw [← pow_succ, ← pow_succ] at h
    rw [h]
  have hnE : (n : E) = 0 := by
    rw [← map_natCast (algebraMap R E), hn, map_zero]
  have hsum : ψ (chi n g D x) = S D (x ^ n) E ψ (z ^ n) - S D (x ^ 0) E ψ (z ^ 0) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [chi, map_sum, hterm, Finset.sum_sub_distrib, Finset.sum_range_sub (fun i ↦ S D (x ^ i) E ψ (z ^ i)),
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, hnE, zero_mul, sub_zero]
  rw [hsum, hx, pow_zero, pow_zero]

  have h1 : (1 : Pt A E) ^ n = spOver ψ ≫ (1 : Pt A D) := by rw [one_pow, MonObj.comp_one]
  have h2 : (z ^ n) ^ n = 1 := by rw [hpow n, hx, MonObj.comp_one]
  have hs := (hS D 1).2 E ψ 1 (z ^ n) h1 h2
  rw [_root_.one_mul] at hs
  rw [hs, add_sub_cancel_left, hz]
  exact hb.1 D E ψ x hx

end GlobalTheory.PtExt
end
end

