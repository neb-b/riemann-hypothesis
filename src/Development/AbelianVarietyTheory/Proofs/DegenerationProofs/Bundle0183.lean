module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0081
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0083
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0076
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0131
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0158
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0179

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.NonemptyGeometricSpecialFibreUniformised
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.UFib

theorem exists_fibre {R : Type} [CommRing R] [IsDomain R] (I : Ideal R) (D : DegPre R) (e : ℕ)
    (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G] (g : GtCoord I D e G) (k : Type) [Field k]
    (f : Sp k ⟶ Spec (CommRingCat.of (R ⧸ I ^ (e + 1)))) (N : ℕ) :
    ∃ (Φ : FibPre k) (r₀ : Φ.G.left ⟶ (thickObj R I e G).left) (xe : Φ.E.X ≃+ D.X) (π : Φ.E.B.left ⟶ D.P.A.left),
      IsGrpPullback Φ.G (thickObj R I e G) f r₀ ∧ IsGrpPullback Φ.E.B D.P.A (f ≫ thick R I e) π ∧
      Φ.D.q.left ≫ π = r₀ ≫ g.pG.left ∧
      (∀ χ, LBIso (Φ.E.O χ).L (LB.LinComb D.P.L (fun a => π ≫ D.Oφ (𝟙 D.P.A) (xe χ) a) Oε)) ∧
      (∀ χ, GenWt Φ.D.i (LB.pullGen D.P.L _ _ (g.t (xe χ)) r₀) χ) ∧ Nonempty (ChartPull Φ.N₀ (npw D.P.L N) π) := by
  obtain ⟨E, xe, d, π, h₁, h₂, h₃, h₄⟩ := GlobalTheory.T.exists_gtDatum_of_torusCoords R I D e G g
  obtain ⟨E', xe', d', π', k₁, k₂, k₃, k₄⟩ := GlobalTheory.T.exists_gtDatum_baseChange_maps' _ _ f E _ d
  obtain ⟨N₀, n₁, n₂, n₃, n₄⟩ := _root_.GlobalTheory.ZH.UFib.exists_affine_refinement _ E' _ (npw D.P.L N) (npw_isLB D.P.isLB N) (π' ≫ π)
  choose ch hch using n₃
  have : IsCommMonObj (thickObj R I e G) := Functor.isCommMonObj_obj
  have : IsCommMonObj ((Over.pullback f).obj (thickObj R I e G)) := Functor.isCommMonObj_obj
  have hp := isGrpPullback_pullback (thickObj R I e G) f
  refine ⟨{ E := E', G := (Over.pullback f).obj (thickObj R I e G), D := d', N₀ := N₀, isLB := n₁, aff := n₂,
            ch := ch, le := hch }, pullback.fst _ f, xe'.trans xe, π' ≫ π, hp, k₁.comp h₁, ?_, fun χ => ?_,
    fun χ Z τ y z J hJ => ?_, n₄⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ π) k₂).trans
      ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) h₂)))
  · exact (k₃ χ).trans (E'.O χ).isLB (pull_isLB (E.O _).isLB _) (DVR.linComb_isLB _ D.P.isLB _ _)
      ((h₃ (xe' χ)).chartPull (Geo.Tor.chartPullPull _ π' π' rfl)
        (chartPullSame D.P.L _ _ Oε π' fun a => Category.assoc _ _ _))
  · obtain ⟨τ₀, t₁, t₂⟩ := k₄ Z τ
    have e₁ := hp.2 Z (τ ≫ d'.i) y (τ₀ ≫ d.i) (pushPt hp.1.w y) t₁ rfl
    have e₂ := h₄ (xe' χ) _ τ₀ (pushPt hp.1.w y) z J hJ
    rw [e₁] at e₂
    exact (val_pull hJ _ _ _).trans (e₂.trans (congrArg₂ (· * ·) (t₂ χ z) (val_pull hJ _ _ _).symm))

theorem formEq_fam {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) {T : Over (Spec (CommRingCat.of R))}
    (p : T ⟶ D.P.A) (α : D.X) (N : ℕ) {Y B : Scheme.{0}} (r : Y ⟶ T.left) (q : Y ⟶ B) (π : B ⟶ D.P.A.left)
    (h : q ≫ π = r ≫ p.left) :
    FormEq (Sum.elim (fun a => q ≫ π ≫ D.famφB α a) (fun a => r ≫ D.Oφ p α a)) (Sum.elim (DegPre.famε N) Oinvε)
      (fun _ : Fin 1 => q ≫ π) (fun _ => (N : ℤ)) := by
  intro U _ F
  have a₀ : q ≫ π ≫ D.famφB α 0 = q ≫ π := congrArg (q ≫ ·) (Category.comp_id _)
  have a₁ : q ≫ π ≫ D.famφB α 1 = r ≫ D.Oφ p α 0 := by
    rw [← Category.assoc, h, Category.assoc]
    refine congrArg (r ≫ ·) ?_
    change (p ≫ (𝟙 D.P.A * (toUnit _ ≫ D.c α))).left = (p * (toUnit _ ≫ D.c α)).left
    rw [MonObj.comp_mul, Category.comp_id, ← Category.assoc, comp_toUnit]
  have a₂ : q ≫ π ≫ D.famφB α 2 = r ≫ D.Oφ p α 1 := by
    rw [← Category.assoc, h, Category.assoc]
    refine congrArg (r ≫ ·) ?_
    change (p ≫ toUnit _ ≫ D.c α).left = (toUnit _ ≫ D.c α).left
    rw [← Category.assoc, comp_toUnit]
  have a₃ : q ≫ π ≫ D.famφB α 3 = r ≫ D.Oφ p α 3 := by
    rw [← Category.assoc, h, Category.assoc]
    refine congrArg (r ≫ ·) ?_
    change (p ≫ toUnit _ ≫ η[D.P.A]).left = (toUnit _ ≫ η[D.P.A]).left
    rw [← Category.assoc, comp_toUnit]
  have a₄ : r ≫ D.Oφ p α 2 = q ≫ π := h.symm
  rw [Fintype.prod_sum_type, Fin.prod_univ_four, Fin.prod_univ_four, Fin.prod_univ_one]
  simp only [Sum.elim_inl, Sum.elim_inr]
  rw [a₀, a₁, a₂, a₃, a₄]
  change F _ ^ ((N : ℤ) - 1) * F _ ^ (1 : ℤ) * F _ ^ (-1 : ℤ) * F _ ^ (1 : ℤ) *
    (F _ ^ (-1 : ℤ) * F _ ^ (1 : ℤ) * F _ ^ (1 : ℤ) * F _ ^ (-1 : ℤ)) = _
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_zpow]
  module

theorem cst_spMap {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {Z : Scheme.{0}} (q : Z ⟶ Sp R') (z : Z)
    (a : R) : cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  refine (gs_pull q (spMap φ) z ⊤ trivial _).symm.trans (congrArg (gs q z ⊤) ?_)
  exact (congrArg (fun ψ => ψ.hom a) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom φ))).symm

theorem isLin_pullSec {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {X Y Y' : Scheme.{0}} (L : LB X)
    {K : Type} [Fintype K] (ψ : K → (Y ⟶ X)) (ε : K → ℤ) (p : Y ⟶ Sp R) (p' : Y' ⟶ Sp R') (π : Y' ⟶ Y)
    (w : π ≫ p = p' ≫ spMap φ) {I : Type} [Fintype I] (β : I → LB.Sec (LB.LinComb L ψ ε)) (a : I → R)
    (s : LB.Sec (LB.LinComb L ψ ε)) (h : IsLin p β a s) :
    IsLin p' (fun i => DVR.pullSec L ψ ε (β i) π) (fun i => φ (a i)) (DVR.pullSec L ψ ε s π) := by
  intro j
  refine fn_ext fun y hy => ?_
  have hm : (𝟙 Y' ≫ π) y ∈ LB.wchart L ψ j := DVR.wchart_comp_le ψ π j hy
  have v : ∀ s : LB.Sec (LB.LinComb L ψ ε), gs (𝟙 Y') y _ ((DVR.pullSec L ψ ε s π).f j) =
      gs (𝟙 Y' ≫ π) y (LB.wchart L ψ j) (s.f j) := fun s =>
    (gs_res (𝟙 Y') y (DVR.wchart_comp_le ψ π j) hy _).trans (gs_pull (𝟙 Y') π y _ hm _)
  refine (v s).trans ((congrArg _ (h j)).trans ((DVR.gs_fsum _ y _ hm _ _).trans
    (Eq.trans (Finset.sum_congr rfl fun i _ => ?_) (DVR.gs_fsum (𝟙 Y') y _ hy _ _).symm)))
  refine (gs_mul _ y _ hm _ _).trans (Eq.trans (congrArg₂ (· * ·) ?_ (v _).symm) (gs_mul (𝟙 Y') y _ hy _ _).symm)
  refine (gs_constFn p _ _ y hm _).trans (Eq.trans ?_ (gs_constFn p' _ (𝟙 Y') y hy _).symm)
  rw [Category.assoc, w, ← Category.assoc, cst_spMap]

def sumSec {X : Scheme.{0}} {M : LB X} {A : Type} (S : Finset A) (φ : A → M.Sec) : M.Sec where
  f l := ∑ α ∈ S, (φ α).f l
  compat i j := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, map_sum, Finset.mul_sum]
    exact Finset.sum_congr rfl fun α _ => (φ α).compat i j

theorem isPart_sumSec {k : Type} [Field k] (Φ : FibPre k) {A : Type} (e : A → Φ.E.X) (he : Function.Injective e)
    (S : Finset A) (φ : A → (Φ.H 1).Sec) (hφ : ∀ α, Φ.Pure (e α) (φ α)) (h₀ : ∀ α ∉ S, ∀ l, (φ α).f l = 0) (α : A) :
    Φ.IsPart (e α) (sumSec S φ) (φ α) := by
  refine ⟨hφ α, fun l => Eq.symm ?_⟩
  refine (WtPart.cf_sum (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) (e α) S _).trans ?_
  change ∑ β ∈ S, Φ.wt (φ β) (e α) l = _
  refine Finset.sum_eq_single α (fun β _ hne => ?_) (fun hα => ?_)
  · by_contra h
    exact hne (he (hφ β ⟨l, h⟩)).symm
  · rw [FibPre.wt, h₀ α hα l]
    exact WtPart.cf_zero (Φ.D.coord (Φ.ch l) (Φ.N₀.U l) (Φ.aff l) (Φ.le l)) _

theorem exists_good_at {X Z : Scheme.{0}} {L : LB X} (hL : L.IsLB) (z : Z) (ψ : Z ⟶ X) (j : L.ι) (h : ψ z ∈ L.U j) :
    ∃ J, Good L z J ∧ J ψ = j := by
  obtain ⟨J, hJ, e⟩ := exists_good L hL z (fun _ : Unit => ψ) (fun _ => j) (fun _ _ _ => rfl) (fun _ => h)
  exact ⟨J, hJ, e ()⟩

theorem nonempty_fibOf : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (N : ℕ), 1 ≤ N → Nonempty (u.FibOf N) := by
  intro hLL o Ω _ _ _ _ S ρ p _ y₀ u N hN
  have hloc : IsLocalHom u.j := (GlobalTheory.T.testField_finite_over_padic o Ω S ρ p y₀ u).2.1
  have : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hL := u.D.toPre.P.isLB
  let φ : u.V →+* kb p := (IsLocalRing.residue (OO p)).comp u.j
  let f₀ : u.V ⧸ IsLocalRing.maximalIdeal u.V ^ (0 + 1) →+* kb p := Ideal.Quotient.lift _ φ fun a ha => by
    rw [zero_add, pow_one] at ha
    exact (IsLocalRing.residue_eq_zero_iff _).2 (map_nonunit u.j a ha)
  have hf : spMap f₀ ≫ thick u.V (IsLocalRing.maximalIdeal u.V) 0 = spMap φ := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have hf' : spMap φ = rPt p ≫ spMap u.j := by
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
  obtain ⟨Φ, r₀, xe, π, h₁, h₂, h₃, h₄, h₅, ⟨c⟩⟩ :=
    exists_fibre (IsLocalRing.maximalIdeal u.V) u.D.toPre 0 u.G (u.U.gt 0) (kb p) (spMap f₀) N
  rw [hf] at h₂
  obtain ⟨pol, hpol⟩ := _root_.GlobalTheory.ZH.UFib.exists_pol hLL.1.polBaseChange _ Φ _ u.D.toPre _ π h₂ xe h₄ N ⟨c⟩
  let t := fun α : u.D.toPre.X => LB.pullGen u.D.toPre.P.L _ _ ((u.U.gt 0).t α) r₀
  have ht : ∀ α, (t α).IsGen := fun α => DVR.pullGen_isGen _ _ _ _ ((u.U.gt 0).t_gen α) r₀
  have hw : ∀ α, GenWt Φ.D.i (t α) (xe.symm α) := fun α => by
    obtain ⟨χ, rfl⟩ := xe.surjective α
    rw [xe.symm_apply_apply]
    exact h₅ χ
  have hF := fun α => formEq_fam u.D.toPre (u.U.gt 0).pG α N r₀ Φ.D.q.left π h₃
  let pb := fun α (β : u.D.toPre.SecB N α) => DVR.pullSec u.D.toPre.P.L (u.D.toPre.famφB α) (DegPre.famε N) β π
  choose red hred using fun α (β : u.D.toPre.SecB N α) =>
    _root_.GlobalTheory.ZH.UFib.exists_red _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) (hF α) (pb α β)
  have hpure : ∀ α β, Φ.Pure (xe.symm α) (red α β) := fun α β =>
    _root_.GlobalTheory.ZH.UFib.pure_of_red _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) _ (hw α) _ _ (hred α β)
  refine ⟨{
    Φ := Φ
    r := r₀ ≫ pullback.fst _ _
    cart := (h₁.comp (isGrpPullback_pullback u.G _)).congr (hf.trans hf') rfl
    xe := xe
    pol := pol
    dim := hpol
    red := red
    pure := hpure
    lin := fun α I _ β a gm₀ h => ?_
    basis := fun α I _ β hβ ψ hψ => ?_
    exp := fun J σ f hσ => ?_ }⟩
  · exact (_root_.GlobalTheory.ZH.UFib.isLin_iff_of_red _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) I _ _ _ _ _ (fun i => hred α (β i)) (hred α gm₀)).1
      (isLin_pullSec φ _ _ _ _ _ π h₂.1.w β a gm₀ h)
  · obtain ⟨b, hb⟩ := _root_.GlobalTheory.ZH.UFib.exists_red_of_pure _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) (hF α) _ (hw α) ψ hψ
    exact (existsUnique_congr fun a => _root_.GlobalTheory.ZH.UFib.isLin_iff_of_red _ Φ _ _ hL π N c _ _ _ _ _ _ (t α) (ht α) I _ _ _ _ a
      (fun i => hred α (β i)) hb).1
      (_root_.GlobalTheory.ZH.BasisBaseChange.basis_pullback GlobalTheory.twistBaseChange u.V u.D.toPre N hN α _ φ _ _ π h₂.1 I β hβ b)
  · choose T hT using fun i => DVR.expandsAt_val u.U.toUnifPre 0 N (σ i) (f i) (hσ i)
    have hv : ∀ α (β : u.D.toPre.SecB N α) (Z : Scheme.{0}) (r : Z ⟶ Φ.G.left) (z : Z) J', Good u.D.toPre.P.L z J' →
        ∀ l, r z ∈ Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l → J' (r ≫ Φ.D.q.left ≫ π) = c.idx l →
        gs r z (Φ.D.q.left ⁻¹ᵁ Φ.N₀.U l) ((red α β).f l) =
          sval β ((r ≫ r₀) ≫ DVR.pGl u.U.toUnifPre 0) z J' * (val (DVR.tG u.U.toUnifPre 0 α) (r ≫ r₀) z J').val := by
      intro α β Z r z J' hJ l hl e
      refine (hred α β Z r z J' hJ l hl e).trans (congrArg₂ (· * ·) ?_ (congrArg Units.val (val_pull hJ _ _ _)))
      refine (DVR.SectionScalarValuation.sval_pullSec _ _ _ _ _ z hJ).trans ?_
      rw [Category.assoc, h₃, ← Category.assoc]
    refine ⟨fun i => sumSec (T i) (fun α => red α (f i α)), fun i α =>
      isPart_sumSec Φ xe.symm xe.symm.injective (T i) _ (fun α => hpure α _) (fun α hα l => ?_) α, fun x v => ?_⟩
    · refine fn_ext fun y hy => ?_
      obtain ⟨J', hJ, e⟩ := exists_good_at hL y (𝟙 _ ≫ Φ.D.q.left ≫ π) (c.idx l) (c.le l hy)
      refine (hv α _ _ (𝟙 _) y J' hJ l hy e).trans (Eq.trans ?_ (DVR.gs_zero (𝟙 _) y _ hy).symm)
      rw [(hT i _ _ y J' hJ).1 α hα, zero_mul]
    · refine _root_.GlobalTheory.ZH.UFib.crd_of_germs_unit _ _ _ _ _ (DVR.linComb_isLB _ u.U.LG.isLB _ _) J _ σ x.left _ (fun z l l' hl hl' => ?_) v
      obtain ⟨J', hJ, e⟩ := exists_good_at hL z (x.left ≫ Φ.D.q.left ≫ π) (c.idx l) (c.le l hl)
      obtain ⟨jL, rfl⟩ : ∃ jL, l' = fun _ => jL := ⟨l' 0, funext fun i => congrArg l' (Subsingleton.elim i 0)⟩
      refine ⟨DVR.wv u.U.toUnifPre 0 (x.left ≫ r₀) z (J' ((x.left ≫ r₀) ≫ DVR.pGl u.U.toUnifPre 0)) jL ^ N,
        fun i => Eq.trans ?_ (((hT i _ (x.left ≫ r₀) z J' hJ).2 jL (Set.mem_iInter.1 hl' 0)).symm.trans ?_)⟩
      · exact (DVR.gs_fsum x.left z _ hl _ _).trans (Finset.sum_congr rfl fun α _ => hv α _ _ _ z J' hJ l hl e)
      · exact congrArg (fun q => _ * DVR.sv u.U.toUnifPre N (σ i) q z jL) (Category.assoc _ _ _)

end GlobalTheory.ZH.UFib
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ThetaConstantsIntegralUnitOfClosedFibreNonvanish
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField IsLocalRing
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex GlobalTheory.ThetaPtMove GlobalTheory.ConstFam
open GlobalTheory.Ex.OneGen GlobalTheory.UT

noncomputable section
namespace GlobalTheory.Ex.OnModel

theorem mem_nonzeroLocus_pullTo {X Y Y' : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}
    {φ' : K → (Y' ⟶ X)} (s : LB.Sec (LB.LinComb L φ ε)) (h : Y' ⟶ Y) (e : ∀ k, h ≫ φ k = φ' k) {y : Y'}
    (hy : h y ∈ nonzeroLocus s) : y ∈ nonzeroLocus (VVRank.pullTo s h e) := by
  obtain rfl : (fun k => h ≫ φ k) = φ' := funext e
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine TopologicalSpace.Opens.mem_iSup.2 ⟨j, ?_⟩
  have hle := VVRank.wchart_le_of_eq (L := L) h e j
  have q := Y'.basicOpen_res ((h.app _).hom (s.f j)) (homOfLE hle).op
  refine q.ge ⟨Set.mem_iInter.2 fun k => Set.mem_iInter.1 (Y.basicOpen_le _ hj) k, ?_⟩
  exact (Scheme.preimage_basicOpen h (s.f j)).le hj

section Base
variable {S : Scheme.{0}} (G : Over S)

def toBase : G.left ⟶ (Over.mk (𝟙 S) ⊗ G).left :=
  (lift (Over.homMk G.hom (Category.comp_id _) : G ⟶ Over.mk (𝟙 S)) (𝟙 G)).left

theorem toBase_snd : toBase G ≫ (snd (Over.mk (𝟙 S)) G).left = 𝟙 _ := by
  rw [toBase, ← Over.comp_left, lift_snd, Over.id_left]

theorem snd_hom : (snd (Over.mk (𝟙 S)) G).left ≫ G.hom = (fst (Over.mk (𝟙 S)) G).left :=
  (pullback.condition (f := 𝟙 S) (g := G.hom)).symm.trans (Category.comp_id _)

theorem comp_toBase {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left) :
    (r ≫ (snd (Over.mk (𝟙 S)) G).left) ≫ toBase G = r := by
  have a : toBase G ≫ (fst (Over.mk (𝟙 S)) G).left = G.hom := by
    rw [toBase, ← Over.comp_left, lift_fst]; rfl
  refine psi_ext ?_ ?_
  · rw [Category.assoc, a, Category.assoc]
    exact congrArg (r ≫ ·) (snd_hom G)
  · rw [Category.assoc, toBase_snd, Category.comp_id]

variable [GrpObj G] {L : LB G.left} {k : ℕ}

def down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) : H0 L k :=
  VVRank.pullTo (φ := fun _ : Fin 1 => (snd (Over.mk (𝟙 S)) G).left) (ε := fun _ => (k : ℤ)) σ (toBase G)
    fun _ => toBase_snd G

theorem sval_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {Z : Scheme.{0}} (r : Z ⟶ (Over.mk (𝟙 S) ⊗ G).left)
    (z : Z) {J} (hJ : Good L z J) :
    sval (down G σ) (r ≫ (snd (Over.mk (𝟙 S)) G).left) z J = VVRank.sv G σ r z J := by
  refine (VVRank.sval_pullTo _ _ _ _ z hJ).trans ?_
  rw [comp_toBase]

theorem mem_nonzeroLocus_down (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 S)))) {g : (Over.mk (𝟙 S) ⊗ G).left}
    (hg : g ∈ nonzeroLocus σ) : (snd (Over.mk (𝟙 S)) G).left g ∈ nonzeroLocus (down G σ) := by
  refine mem_nonzeroLocus_pullTo _ _ _ ?_
  have e := comp_toBase G (𝟙 _)
  rw [Category.id_comp] at e
  rw [← Scheme.Hom.comp_apply, e]
  exact hg

end Base

theorem isGenSec_of_down {V : Type} [CommRing V] (G : Over (Sp V)) [GrpObj G] {L : LB G.left} (hL : L.IsLB) {k : ℕ}
    (σ : LB.Sec (LPow G L (k : ℤ) (Over.mk (𝟙 (Sp V))))) (h : ∀ s : H0 L k, ∃ b : V, SecIsMul G.hom b s (down G σ)) :
    IsGenSec G L (k : ℤ) σ := by
  intro s
  obtain ⟨b, hb⟩ := h (down G s)
  let c : Γ((Over.mk (𝟙 (Sp V))).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom b
  have key : SecM.ofSec G s = c • SecM.ofSec G σ := ThetaAct.sv_ext hL fun y J hJ => by
    refine Eq.trans ?_ (ThetaAct.sv_smul _ _ _ _ hJ).symm
    refine (sval_down G s (𝟙 _) y hJ).symm.trans (Eq.trans ?_ (congrArg (_ * ·) (sval_down G σ (𝟙 _) y hJ)))
    have hz := hJ.mem (fun _ : Fin 1 => 𝟙 G.left) (𝟙 _ ≫ (snd (Over.mk (𝟙 (Sp V))) G).left)
    refine (congrArg (gs _ y _) (hb _)).trans ((gs_mul _ y _ hz _ _).trans (congrArg (· * _) ?_))
    refine (gs_res _ y le_top hz _).trans ((gs_pull _ G.hom y ⊤ trivial _).trans ?_)
    rw [Category.assoc, snd_hom]
  exact ⟨c, fun j => congrArg (fun q => q.1 j) key⟩

theorem theta_on_model : HV → AllUV fun {V} _ _ _ {ϖ} hϖ {D} Q {F} _ _ {v} hv {A} {G} _ _ U => ∀ σ : LB.Sec (LPow G U.LG.L ((1 : ℕ) : ℤ) (Over.mk (𝟙 (Sp V)))), NZ G U.LG.L (𝟙 (Sp V)) σ → IsGenSec G U.LG.L ((1 : ℕ) : ℤ) σ ∧ ∀ m : ℕ, Odd m → IsUnit (m : V) → 3 ≤ m → ∀ (ξ : Over.mk (jFK (R := V) F ≫ jK V) ⟶ Over.mk (𝟙 (Sp V))), (∀ x (c : F), ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) → 0 ≤ v c) ∧ ∃ x, ∃ c : F, ThG G U.LG.L U.LG.rig m (VVRank.pullS G _ ξ σ) x (fnOf c) ∧ v c = 0 := by
  intro hHV V _ _ _ _ hc ϖ hϖ D Q hQ F _ _ _ v hv A G _ _ hG U σ hσ
  have hL := U.LG.isLB
  have := A.isAb.comm
  obtain ⟨g, hg, hg'⟩ := hσ
  obtain ⟨hgen, hexp⟩ := GlobalTheory.T.section_nonzero_closedFibre_generates_expansion_zero hHV.1 V hc ϖ hϖ D Q hQ F v hv A G hG U (down G σ)
    ⟨_, by rw [← Scheme.Hom.comp_apply, snd_hom]; exact hg, mem_nonzeroLocus_down G σ hg'⟩
  refine ⟨isGenSec_of_down G hL σ hgen, fun m h₁ h₂ h₃ ξ => ?_⟩
  obtain ⟨w₀, ρ, w, hp, hN, hw, hr, H⟩ := GlobalTheory.T.uniformisation_generic_fibre_cartesian_to_model_bundleIso V _ D A G U.toUnifPre
  have hτ : 𝟙 (Sp F) ≫ (Over.mk (jFK (R := V) F ≫ jK V)).hom = (TFK (R := V) F).hom ≫ jK V := Category.id_comp _
  obtain ⟨th, hth⟩ := exists_secRel hp (T := TFK (R := V) F) (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) (𝟙 (Sp F)) hτ hw hL
    A.isLB (VVRank.pullS G _ ξ σ)
  obtain ⟨σ', hσ', hE⟩ := H F 1 (down G σ) th fun Z r z J J' hJ hJ' => by
    refine Eq.trans ?_ (hth Z r z J J' hJ hJ')
    refine Eq.trans ?_ ((sval_down G σ _ z hJ).trans (VVRank.sv_pullS G _ ξ σ _ z hJ).symm)
    rw [Category.assoc, VVRank.whisker_snd_left, Category.assoc, psi_snd']
  obtain ⟨ϑ, hϑ, hP⟩ := hexp σ' hσ'
  obtain ⟨k₁, x, c, k₂, k₃⟩ := _root_.GlobalTheory.Ex.OneGen.thG_val_of_prim hHV V hc ϖ hϖ D Q hQ F v hv A G hG U w₀ ρ hN th ϑ (hE ϑ hϑ) hP m h₁ h₂ h₃
  have hx : ∀ x : TFK (R := V) F ⟶ A.A, 𝟙 (Sp F) ≫ (pushHom hp (TFK (R := V) F) x).left = x.left ≫ _ :=
    fun x => Category.id_comp _
  refine ⟨fun x₀ c hc => ?_, pushHom hp (TFK (R := V) F) x, c, ?_, k₃⟩
  · let y : TFK (R := V) F ⟶ A.A := Over.homMk (hp.1.lift x₀.left (jFK (R := V) F) (Over.w x₀)) (hp.1.lift_snd _ _ _)
    have hy : 𝟙 (Sp F) ≫ x₀.left = y.left ≫ _ := (Category.id_comp _).trans (hp.1.lift_fst _ _ _).symm
    have hn : y ^ (m ^ 2) = 1 := by
      refine Over.OverMorphism.ext (hp.1.hom_ext ?_ (by rw [Over.w, Over.w]))
      refine (over_pow hp (T₀ := Over.mk (jFK (R := V) F ≫ jK V)) _ hτ hy _).symm.trans ?_
      rw [hc.1]
      exact over_one hp _ hτ
    exact k₁ y c (ThG.move hp _ hτ hw hL A.isLB hr hy hn hth hc)
  · have : IsIso (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) := IsIso.id _
    have q := ThG.up hp _ hτ hw hL A.isLB hr (hx x) (by rw [← map_pow, k₂.1, map_one]) hth k₂
    have e : inv (X := (TFK (R := V) F).left) (Y := (Over.mk (jFK (R := V) F ≫ jK V)).left) (𝟙 (Sp F)) = 𝟙 (Sp F) :=
      IsIso.inv_eq_of_hom_inv_id (Category.id_comp _)
    rw [e] at q
    exact q

end GlobalTheory.Ex.OnModel
end
end

