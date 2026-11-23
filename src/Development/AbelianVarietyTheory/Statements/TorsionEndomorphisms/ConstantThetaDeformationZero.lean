module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsSecNonzeroLocusEqOfLbIso
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.AppLESurjective

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

section Defs

variable {X : Scheme.{0}} {R : Type} [CommRing R]

def IsRatioFamily {H : LB X} {m : ℕ} (s : Fin (m + 1) → H.Sec) (i : Fin (m + 1))
    (r : Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))) : Prop :=
  ∀ j k, resG X (inf_le_right : Out.nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s j).f k) =
    resG X (inf_le_left : Out.nonzeroLocus (s i) ⊓ H.U k ≤ Out.nonzeroLocus (s i)) (r j) *
      resG X (inf_le_right : Out.nonzeroLocus (s i) ⊓ H.U k ≤ H.U k) ((s i).f k)

def vanishingForms (f : X ⟶ Sp R) {H : LB X} {m : ℕ} (s : Fin (m + 1) → H.Sec) (d : ℕ) :
    Set (MvPolynomial (Fin (m + 1)) R) :=
  {F | F.IsHomogeneous d ∧ ∀ k, MvPolynomial.eval₂Hom (AbLaw.cst f (H.U k)) (fun j => (s j).f k) F = 0}

abbrev epsRed (K : Type) [CommRing K] : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom

end Defs

section CutOut

open MvPolynomial

variable {X : Scheme.{0}} {R : Type} [CommRing R] {H : LB X} {m : ℕ}

theorem ThetaDeform.eval₂_scale {σ A : Type} [CommRing A] (φ : R →+* A) (c : A) (x : σ → A) {F : MvPolynomial σ R}
    {e : ℕ} (hF : F.IsHomogeneous e) : eval₂ φ (fun j => x j * c) F = c ^ e * eval₂ φ x F := by
  rw [eval₂_eq, eval₂_eq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hd : ∑ j ∈ a.support, a j = e := by
    have := hF (mem_support_iff.1 ha)
    rw [← this, Finsupp.weight_apply, Finsupp.sum]
    simp
  simp only [mul_pow, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, hd]
  ring

def ThetaDeform.germAt (y : X) (U : X.Opens) (h : y ∈ U) : Γ(X, U) →+* X.presheaf.stalk y :=
  (X.presheaf.germ U y h).hom

theorem ThetaDeform.germAt_eq (y : X) (U : X.Opens) (h : y ∈ U) (a : Γ(X, U)) :
    ThetaDeform.germAt y U h a = gs (𝟙 X) y U a := (gs_eq (𝟙 X) y U h a).symm

theorem ThetaDeform.gs_eval (f : X ⟶ Sp R) (y : X) (U : X.Opens) (h : y ∈ U) (x : Fin (m + 1) → Γ(X, U))
    (F : MvPolynomial (Fin (m + 1)) R) : gs (𝟙 X) y U (eval₂Hom (AbLaw.cst f U) x F) =
      eval₂ ((ThetaDeform.germAt y ⊤ (TopologicalSpace.Opens.mem_top y)).comp (AbLaw.cst f ⊤)) (fun j => gs (𝟙 X) y U (x j)) F := by
  rw [← ThetaDeform.germAt_eq y U h, coe_eval₂Hom, eval₂_comp_left]
  congr 1
  · ext a
    rw [RingHom.comp_apply, RingHom.comp_apply, ThetaDeform.germAt_eq, ThetaDeform.germAt_eq,
      ← AbLaw.rs_cst f (le_top : U ≤ ⊤) a, gs_res _ y _ h]
  · ext j
    exact ThetaDeform.germAt_eq y U h _

variable {s : Fin (m + 1) → H.Sec} {i : Fin (m + 1)} {r : Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))}

theorem IsRatioFamily.gs_eq (hr : IsRatioFamily s i r) {y : X} (hy : y ∈ Out.nonzeroLocus (s i)) {k : H.ι}
    (hk : y ∈ H.U k) (j : Fin (m + 1)) :
    gs (𝟙 X) y _ ((s j).f k) = gs (𝟙 X) y _ (r j) * gs (𝟙 X) y _ ((s i).f k) := by
  have h : y ∈ Out.nonzeroLocus (s i) ⊓ H.U k := ⟨hy, hk⟩
  have e := congrArg (gs (𝟙 X) y _) (hr j k)
  rwa [gs_res _ y _ h, gs_mul _ y _ h, gs_res _ y _ h, gs_res _ y _ h] at e

theorem IsRatioFamily.self_eq_one (hr : IsRatioFamily s i r) : r i = 1 := fn_ext fun y hy => by
  obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
  refine ((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).mul_right_cancel ((hr.gs_eq hy hk i).symm.trans ?_)
  rw [← ThetaDeform.germAt_eq y _ hy 1, map_one, _root_.one_mul]

theorem IsRatioFamily.gs_form (f : X ⟶ Sp R) (hr : IsRatioFamily s i r) {y : X} (hy : y ∈ Out.nonzeroLocus (s i))
    {k : H.ι} (hk : y ∈ H.U k) {F : MvPolynomial (Fin (m + 1)) R} {e : ℕ} (hF : F.IsHomogeneous e) :
    gs (𝟙 X) y _ (eval₂Hom (AbLaw.cst f (H.U k)) (fun j => (s j).f k) F) =
      gs (𝟙 X) y _ ((s i).f k) ^ e * gs (𝟙 X) y _ (eval₂Hom (AbLaw.cst f _) r F) := by
  rw [ThetaDeform.gs_eval f y _ hk, ThetaDeform.gs_eval f y _ hy, ← ThetaDeform.eval₂_scale _ _ _ hF]
  congr 1
  exact funext fun j => hr.gs_eq hy hk j

theorem IsRatioFamily.eval_eq_zero (f : X ⟶ Sp R) (hr : IsRatioFamily s i r) {F : MvPolynomial (Fin (m + 1)) R}
    {d : ℕ} (hF : F ∈ vanishingForms f s d) : eval₂Hom (AbLaw.cst f _) r F = 0 := fn_ext fun y hy => by
  obtain ⟨k, hk⟩ := exists_chart_of_mem_nonzeroLocus hy
  have e := hr.gs_form f hy hk hF.1
  rw [hF.2 k, LBGerm.gs_zero _ y _ hk] at e
  rw [LBGerm.gs_zero _ y _ hy]
  exact (((mem_nonzeroLocus_iff_isUnit _ hk).1 hy).pow d).mul_right_eq_zero.1 e.symm

theorem mem_vanishingForms_of_ratios (f : X ⟶ Sp R) (hc : ⨆ i, Out.nonzeroLocus (s i) = ⊤)
    (r : ∀ i, Fin (m + 1) → Γ(X, Out.nonzeroLocus (s i))) (hr : ∀ i, IsRatioFamily s i (r i))
    {F : MvPolynomial (Fin (m + 1)) R} {d : ℕ} (hF : F.IsHomogeneous d)
    (h : ∀ i, eval₂Hom (AbLaw.cst f _) (r i) F = 0) : F ∈ vanishingForms f s d :=
  ⟨hF, fun k => fn_ext fun y hk => by
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 (hc.ge (Set.mem_univ y))
    rw [(hr i).gs_form f hi hk hF, h i, LBGerm.gs_zero _ y _ hi, LBGerm.gs_zero _ y _ hk, mul_zero]⟩

theorem ThetaDeform.exists_homogeneous (i : Fin (m + 1)) (p : MvPolynomial (Fin (m + 1)) R) :
    ∀ᶠ d in Filter.atTop, ∃ F : MvPolynomial (Fin (m + 1)) R, F.IsHomogeneous d ∧ MvPolynomial.X i - 1 ∣ F - p := by
  induction p using MvPolynomial.induction_on with
  | C a =>
    refine Filter.Eventually.of_forall fun d => ⟨C a * MvPolynomial.X i ^ d,
      by simpa using (isHomogeneous_C _ a).mul (isHomogeneous_X_pow i d), ?_⟩
    rw [← mul_sub_one]
    exact (sub_one_dvd_pow_sub_one _ d).mul_left _
  | add p q hp hq =>
    filter_upwards [hp, hq] with d ⟨F, hF, e⟩ ⟨G, hG, e'⟩
    exact ⟨F + G, hF.add hG, by rw [add_sub_add_comm]; exact e.add e'⟩
  | mul_X p j hp =>
    obtain ⟨e, he⟩ := Filter.eventually_atTop.1 hp
    refine Filter.eventually_atTop.2 ⟨e + 1, fun d hd => ?_⟩
    obtain ⟨d, rfl⟩ : ∃ d', d = d' + 1 := ⟨d - 1, by omega⟩
    obtain ⟨F, hF, h⟩ := he d (by omega)
    exact ⟨F * MvPolynomial.X j, hF.mul (isHomogeneous_X _ j), by rw [← sub_mul]; exact h.mul_right _⟩

end CutOut

section Families

variable {R : Type} [CommRing R]

end Families

section Point

end Point

section Zero

open Out Out.Inh Out.InhVV

section Ones

variable {X Y Z : Scheme.{0}} (L : LB X) {K K' : Type} [Fintype K] [Fintype K'] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
  {φ' : K' → (Y ⟶ X)} {ε' : K' → ℤ} {t : LB.Gen (LB.LinComb L φ ε)} {t' : LB.Gen (LB.LinComb L φ' ε')}

end Ones


end Zero

end GlobalTheory
