module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.ModerateCoefficientPositivityHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0028
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.TransvectionPeriodicity
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.FlagBasis
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsAffineLieBasisBaseChange
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.PartitionExtendByZeroAntitone
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecCuspCongr
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory.DomCongr

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private lemma isSec_of_eqOn_dom {la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r} {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) (hP : X.IsSec la P) : X.IsSec la Q := by
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsSec at hP ⊢
  obtain ⟨hd, hb, hg⟩ := hP
  refine ⟨hd.congr fun x hx => (hPQ x hx).symm, fun x hx b hb' => ?_, fun γ hγ x hx => ?_⟩
  · rw [← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_rmul X hx hb'), ← hPQ x hx, hb x hx b hb']
  · rw [← hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.AR.Up.OntoS.dom_lact X hγ hx), ← hPQ x hx, hg γ hγ x hx]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private lemma pnorm_eq_of_eqOn_dom (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.pnorm la P x = X.pnorm la Q x := by
  rw [_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.pnorm_eq, hPQ x hx]

open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
private lemma fj_eq_of_eqOn_dom (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) {P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ}
    (hPQ : ∀ x ∈ X.dom, P x = Q x) {ξ : Fin r → E} (hξ : _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm ξ ξ = 0)
    (ν : ↥X.Ψ → ℝ) {x : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r} (hx : x ∈ X.dom) :
    X.fj la ξ ν P x = X.fj la ξ ν Q x := by
  have key : ∀ s : ↥X.Ψ → ℝ, P (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x) =
      Q (X.flow ξ (fun τ ↦ ((s τ : ℝ) : ℂ)) x) :=
    fun s => hPQ _ (_root_.ReciprocityTheory.ChartRestriction.G.FD.TransvectionPeriodicity.flow_real_mem_dom X hξ s x hx)
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.fj
  simp only [key]


open NumberField in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r) in
theorem _root_.GlobalTheory.DomCongr.bddSec_cusp_congr : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E]
    (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), ∀ (la : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ),
    (∀ x ∈ X.dom, P x = Q x) → (X.IsBddSec la P → X.IsBddSec la Q) ∧
      (P ∈ X.SS la → Q ∈ X.SS la) := by
  intro E _ _ _ r X la P Q hPQ
  have hB : X.IsBddSec la P → X.IsBddSec la Q := by
    intro hP
    unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsBddSec at hP ⊢
    obtain ⟨hs, C, hC⟩ := hP
    exact ⟨isSec_of_eqOn_dom X hPQ hs, C,
      fun x hx => (pnorm_eq_of_eqOn_dom X la hPQ hx) ▸ hC x hx⟩
  refine ⟨hB, fun hP => ?_⟩
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.SS at hP ⊢
  obtain ⟨hb, hc⟩ := hP
  refine ⟨hB hb, fun ξ hξ x hx => ?_⟩
  rw [← fj_eq_of_eqOn_dom X la hPQ (by unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.Data.IsIso at hξ; exact hξ.2.1) 0 hx]
  exact hc ξ hξ x hx

end GlobalTheory.DomCongr
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.BddSecMulAndConstTermMul
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory


open NumberField in
theorem _root_.GlobalTheory.bddSec_mul_and_constTerm_mul :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r),
      ∀ (la la' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Wt X.Ψ r) (P Q : _root_.ReciprocityTheory.ChartRestriction.G.FD.Frame X.Ψ r → ℂ), X.IsBddSec la P → X.IsBddSec la' Q →
        X.IsBddSec (la + la') (P * Q) ∧ ∀ ξ, X.IsIso ξ → ∀ x ∈ X.dom,
          X.fj (la + la') ξ 0 (P * Q) x = X.fj la ξ 0 P x * X.fj la' ξ 0 Q x := by
  intro E _ _ _ r X la la' P Q hP hQ
  refine ⟨_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.bdd_mul X hP hQ, fun ξ hξ x hx => ?_⟩
  have h3e : @_root_.ReciprocityTheory.ChartRestriction.G.FD.CoefficientConvolution E _ _ _ := _root_.ReciprocityTheory.ChartRestriction.G.FD.coefficientConvolution_holds
  have hm3d : @_root_.ReciprocityTheory.ChartRestriction.G.FD.ModerateCoefficientPositivity E _ _ _ := _root_.ReciprocityTheory.ChartRestriction.G.FD.moderateCoefficientPositivity_holds
  unfold _root_.ReciprocityTheory.ChartRestriction.G.FD.CoefficientConvolution at h3e
  have hsum := h3e r X la la' P Q hP.1 hQ.1 (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.mod_of_bdd X hP) (_root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.mod_of_bdd X hQ) ξ hξ x hx 0
  have hzero : ∀ ν' ≠ (0 : ↥X.Ψ → ℝ), X.fj la ξ ν' P x * X.fj la' ξ (0 - ν') Q x = 0 := by
    intro ν' hν'
    by_contra hne
    apply hν'
    have h1 := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd X hm3d hP hξ ν' hx (left_ne_zero_of_mul hne)
    have h2 := _root_.ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra.sign_of_bdd X hm3d hQ hξ (0 - ν') hx (right_ne_zero_of_mul hne)
    funext τ
    have a := h1 τ
    have b := h2 τ
    simp only [zero_sub, Pi.neg_apply] at b
    simp only [Pi.zero_apply]
    linarith
  have hs := hasSum_single (f := fun ν' => X.fj la ξ ν' P x * X.fj la' ξ (0 - ν') Q x) 0 hzero
  simpa using hsum.unique hs

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvalIsHomogeneousMemCuspForms
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem multiset_prod_mem_cuspForms {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (X : Data E r) (la : Wt X.Ψ r) {N : ℕ} (w : Fin N → Frame X.Ψ r → ℂ)
    (hw : ∀ i, w i ∈ X.SS la) (s : Multiset (Fin N)) (hs : s ≠ 0) :
    (s.map w).prod ∈ X.SS (s.card • la) := by
  induction s using Multiset.induction_on with
  | empty => exact absurd rfl hs
  | cons a s ih =>
    by_cases h0 : s = 0
    · subst h0
      simpa using hw a
    · have h := (siegelSpaceAlgebra_holds (E := E) r X (s.card • la) la 0).2.1 _ (ih h0) _ (hw a).1
      rw [Multiset.map_cons, Multiset.prod_cons, Multiset.card_cons, succ_nsmul, mul_comm]
      exact h

theorem eval_isHomogeneous_mem_cuspForms :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r),
      ∀ (la : Wt X.Ψ r) (N d : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (p : MvPolynomial (Fin N) ℂ),
        (∀ i, w i ∈ X.SS la) → 0 < d → p.IsHomogeneous d →
        (fun x => MvPolynomial.eval (fun i => w i x) p) ∈ X.SS (d • la) := by
  intro E _ _ _ r X la N d w p hw hd hp
  obtain ⟨⟨h0, hadd, hsmul⟩, -⟩ := siegelSpaceAlgebra_holds (E := E) r X (d • la) (d • la) 0
  have hmon : ∀ m ∈ p.support, (m.toMultiset.map w).prod ∈ X.SS (d • la) := by
    intro m hm
    have hc : m.toMultiset.card = d := by
      rw [Finsupp.card_toMultiset]
      have := hp (MvPolynomial.mem_support_iff.1 hm)
      simpa [Finsupp.weight_apply, Finsupp.sum] using this
    have := multiset_prod_mem_cuspForms X la w hw m.toMultiset (by
      intro h; rw [h] at hc; simp at hc; omega)
    rwa [hc] at this
  have heq : (fun x => MvPolynomial.eval (fun i => w i x) p) =
      ∑ m ∈ p.support, p.coeff m • (m.toMultiset.map w).prod := by
    funext x
    rw [MvPolynomial.eval_eq, Finset.sum_apply]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Pi.smul_apply, smul_eq_mul, Finsupp.toMultiset_map, Finsupp.prod_toMultiset,
      Finsupp.prod_mapDomain_index (by simp) (by intros; rw [pow_add])]
    simp [Finsupp.prod, Finset.prod_apply]
  rw [heq]
  exact Finset.sum_induction _ (fun P => P ∈ X.SS (d • la)) (fun a b ha hb => hadd a ha b hb) h0
    (fun m hm => hsmul _ _ (hmon m hm))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsChartLieBasisMatrices
section
noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.ModelChart

theorem exists_open_isDomain (X : Scheme.{0}) [GlobalTheory.IsNormalScheme X] [IsLocallyNoetherian X] (x : X) :
    ∃ W : X.Opens, x ∈ W ∧ ∀ U : X.Opens, x ∈ U → U ≤ W → IsDomain Γ(X, U) := by
  let Z : irreducibleComponents X := ⟨_, irreducibleComponent_mem_irreducibleComponents x⟩
  refine ⟨GlobalTheory.IsNormalScheme.component Z, mem_irreducibleComponent, fun U hx hU => ?_⟩
  have : Nonempty U.toScheme := ⟨⟨x, hx⟩⟩
  have : IsIntegral U.toScheme := isIntegral_of_isOpenImmersion (X.homOfLE hU)
  have e : Γ(U.toScheme, ⊤) ≅ Γ(X, U) := U.topIso
  exact e.commRingCatIsoToRingEquiv.symm.toMulEquiv.isDomain _

theorem res_mem_secOn {X : Scheme.{0}} (L : LB X) {V W : X.Opens} (h : W ≤ V) {θ : ∀ i, Γ(X, V ⊓ L.U i)}
    (hθ : θ ∈ secOn L V) : (fun i => resG X (inf_le_inf_right _ h) (θ i)) ∈ secOn L W := by
  intro i j
  have e := congrArg (resG X (inf_le_inf_right _ (inf_le_inf_right _ h) :
    W ⊓ L.U i ⊓ L.U j ≤ V ⊓ L.U i ⊓ L.U j)) (hθ i j)
  rw [map_mul] at e
  simpa only [resG, ← CommRingCat.comp_apply, ← Functor.map_comp, ← op_comp, homOfLE_comp] using e

theorem isTangent_comp_hom {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] {v : epsR R ⟶ G} (hv : IsTangent v)
    (a : G ⟶ G) [IsMonHom a] : IsTangent (v ≫ a) := by
  unfold IsTangent at hv ⊢
  rw [Over.comp_left, ← Category.assoc, hv, ← Over.comp_left, IsMonHom.one_hom]

theorem spMap_dualMapR_id (R : Type) [CommRing R] :
    spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R)) = 𝟙 _ := by
  have : ReciprocityTheory.ChartRestriction.G.Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
    refine RingHom.ext fun x => ?_
    ext <;> simp [ReciprocityTheory.ChartRestriction.G.Chart.dualMapR]
  rw [this]
  exact Spec.map_id _

theorem exists_chart_lieBasis_matrices :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (O : Type) [CommRing O] [IsNoetherianRing O] (β : O →+* c.F) (Y : Model Xo c β), PushInvertible Y.t.G Y.t.PP.L → ∀ x : Y.X, ∃ (U : Y.X.Opens) (hU : IsAffineOpen U), x ∈ U ∧ IsDomain Γ(Y.X, U) ∧ (∃ θ ∈ secOn Y.t.PP.L (Y.t.G.hom ⁻¹ᵁ U), ∀ y ∈ U, ∃ (g : Y.t.G.left) (i : Y.t.PP.L.ι), Y.t.G.hom g = y ∧ g ∈ Y.t.G.left.basicOpen (θ i)) ∧ ∃ (n : ℕ) (v₀ : Fin n → (Sp (DualNumber Γ(Y.X, U)) ⟶ Y.t.G.left)) (ρ : 𝓞 E → Matrix (Fin n) (Fin n) Γ(Y.X, U)), ∀ (R' : Type) [CommRing R'] (f : Γ(Y.X, U) →+* R') (t' : SAB H (Sp R')) (m : SABMap t' Y.t (spMap f ≫ hU.fromSpec)), ∃ v' : Fin n → (epsR R' ⟶ t'.G), (∀ j, (v' j).left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ v₀ j) ∧ IsLieBasis v' ∧ ∀ a j, IsLieComb (fun i => f (ρ a i j)) v' (v' j ≫ t'.act.act a) := by
  intro E _ _ _ H D l Xo c O _ _ β Y hP x
  have := projProper _ _ _ Y.proj
  have : IsLocallyNoetherian Y.X := LocallyOfFiniteType.isLocallyNoetherian Y.s
  have : GlobalTheory.IsNormalScheme Y.X := GlobalTheory.IsNormalScheme.of_pred Y.normal
  have := Y.t.semi.smooth
  obtain ⟨W, hxW, hW⟩ := exists_open_isDomain Y.X x
  obtain ⟨V, hxV, θ, hθ, -, nz⟩ := hP x
  obtain ⟨U, hU, hxU, hUW, n, v₀, hv⟩ := GlobalTheory.exists_affine_lieBasis_baseChange Y.X Y.t.G x (W ⊓ V) ⟨hxW, hxV⟩
  have hUV : U ≤ V := hUW.trans inf_le_right
  refine ⟨U, hU, hxU, hW U hxU (hUW.trans inf_le_left),
    ⟨_, res_mem_secOn _ (Y.t.G.hom.preimage_mono hUV) hθ, fun y hy => ?_⟩, ?_⟩
  · obtain ⟨g, i, rfl, hg⟩ := nz y (hUV hy)
    refine ⟨g, i, rfl, ?_⟩
    show g ∈ Y.t.G.left.basicOpen (Y.t.G.left.presheaf.map (homOfLE _).op (θ i))
    rw [Scheme.basicOpen_res]
    exact ⟨⟨hy, (Y.t.G.left.basicOpen_le _ hg).2⟩, hg⟩
  obtain ⟨t₀, ⟨m₀⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 (Sp Γ(Y.X, U)) hU.fromSpec
  have c₀ : IsGrpPullback t₀.G Y.t.G (spMap (RingHom.id Γ(Y.X, U)) ≫ hU.fromSpec) m₀.φ := by
    have e : spMap (RingHom.id Γ(Y.X, U)) = 𝟙 _ := Spec.map_id _
    rw [e, Category.id_comp]
    exact m₀.cart
  obtain ⟨u, hu, hb⟩ := hv _ (RingHom.id _) t₀.G m₀.φ c₀
  simp only [spMap_dualMapR_id, Category.id_comp] at hu
  have ex : ∀ a j, ∃ r : Fin n → Γ(Y.X, U), IsLieComb r u (u j ≫ t₀.act.act a) := fun a j =>
    have := t₀.act.hom a
    (hb.2 _ (isTangent_comp_hom (hb.1 j) _)).exists
  choose r hr using ex
  refine ⟨n, v₀, fun a i j => r a j i, fun R' _ f t' m => ?_⟩
  obtain ⟨v', hv', hb'⟩ := hv R' f t'.G m.φ m.cart
  refine ⟨v', hv', hb', fun a j => ?_⟩
  have hp := m₀.cart.1
  let F : t'.G.left ⟶ t₀.G.left := hp.lift m.φ (t'.G.hom ≫ spMap f) (by rw [m.cart.1.w, Category.assoc])
  have hF : F ≫ m₀.φ = m.φ := hp.lift_fst _ _ _
  have hw : F ≫ t₀.G.hom = t'.G.hom ≫ spMap f := hp.lift_snd _ _ _
  have hc : IsGrpPullback t'.G t₀.G (spMap f) F := m₀.cart.cancel (hF ▸ m.cart) hw
  have lies : ∀ (w' : epsR R' ⟶ t'.G) (w : epsR Γ(Y.X, U) ⟶ t₀.G),
      w'.left ≫ m.φ = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left ≫ m₀.φ →
      w'.left ≫ F = spMap (ReciprocityTheory.ChartRestriction.G.Chart.dualMapR f) ≫ w.left := fun w' w h => by
    apply hp.hom_ext
    · rw [Category.assoc, hF, h, Category.assoc]
    · rw [Category.assoc, hw, ← Category.assoc, Over.w, Category.assoc, Over.w]
      exact (GlobalTheory.LieCombBaseChange.dualMap_over f).symm
  refine (GlobalTheory.lieComb_baseChange _ _ f t₀.G t'.G F hc n u _ (r a j) v' _
    (fun k => lies _ _ (by rw [hv', hu])) (hr a j)).1 (lies _ _ ?_)
  rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, m.act, m₀.act, ← Category.assoc, hv',
    ← Category.assoc (u j).left, hu, Category.assoc]

end GlobalTheory.ModelChart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.ExistsSecPullNonzeroOnFibres
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory


open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.H1 in
theorem exists_sec_pull_nonzero_on_fibres :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (S S' : Scheme.{0}) (t : SAB H S) (t' : SAB H S') (f : S' ⟶ S) (m : SABMap t' t f) (U : S.Opens), ⊤ ≤ f ⁻¹ᵁ U → ∀ θ ∈ secOn t.PP.L (t.G.hom ⁻¹ᵁ U), (∀ y ∈ U, ∃ (g : t.G.left) (i : t.PP.L.ι), t.G.hom g = y ∧ g ∈ t.G.left.basicOpen (θ i)) → ∃ (w : LB.Iso t'.PP.L (t.PP.L.pull m.φ)) (θ' : LB.Sec t'.PP.L), IsRigIso m.cm t'.PP t.PP w ∧ (∀ (j : t.PP.L.ι) (k : t'.PP.L.ι) (W : t'.G.left.Opens) (h₁ : W ≤ m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U j)) (h₂ : W ≤ (t.PP.L.pull m.φ).U (fun _ => j) ⊓ t'.PP.L.U k), (m.φ.appLE _ _ h₁).hom (θ j) = resG _ h₂ (w.s (fun _ => j, k)).val * resG _ (h₂.trans inf_le_right) (θ'.f k)) ∧ ∀ y' : S', ∃ (g : t'.G.left) (i : t'.PP.L.ι), t'.G.hom g = y' ∧ g ∈ t'.G.left.basicOpen (θ'.f i) := by
  intro E _ _ _ H S S' t t' f m U hU θ₀ hθ₀ nz
  have mem : ∀ x, m.φ x ∈ t.G.hom ⁻¹ᵁ U := fun x => (congrArg (fun q => q x ∈ U) m.cart.1.w).mpr
    (hU (show t'.G.hom x ∈ (⊤ : S'.Opens) from trivial))
  have le : ∀ j, m.φ ⁻¹ᵁ t.PP.L.U j ≤ m.φ ⁻¹ᵁ (t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U j) := fun j x hx => ⟨mem x, hx⟩
  have ev : ∀ y j, m.φ y ∈ t.PP.L.U j → gs (𝟙 _) y _ ((m.φ.appLE _ _ (le j)).hom (θ₀ j)) = gs m.φ y _ (θ₀ j) :=
    fun y j h => (gs_appLE m.φ _ _ (le j) (𝟙 _) y h _).trans (by rw [Category.id_comp])
  obtain ⟨w, g1, r1, -⟩ := m.lin
  obtain ⟨θ, hθ⟩ := sec_down ((isGen_iff w).1 g1) t.PP.isLB t'.PP.isLB (fun j => (m.φ.appLE _ _ (le j)).hom (θ₀ j))
    fun y j j' h h' => by
      have hm : m.φ y ∈ t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U j ⊓ t.PP.L.U j' := ⟨⟨mem y, h⟩, h'⟩
      have e := congrArg (gs m.φ y _) (hθ₀ j j')
      rw [gs_res _ y _ hm, gs_mul _ y _ hm, gs_res _ y _ hm, gs_res _ y _ hm,
        gs_unit _ y (t.PP.L.U j ⊓ t.PP.L.U j') ⟨h, h'⟩] at e
      exact (ev y j h).trans (e.trans (congrArg _ (ev y j' h').symm))
  refine ⟨w, θ, ⟨g1, r1⟩, fun j k W h₁ h₂ => fn_ext fun y hy => ?_, fun y' => ?_⟩
  · have e := hθ _ (𝟙 _) y j k (h₁ hy).2 (h₂ hy).2
    rw [ev y j (h₁ hy).2] at e
    rw [gs_appLE m.φ _ _ h₁ (𝟙 _) y hy, Category.id_comp, e, gs_mul _ y _ hy, gs_res _ y _ hy]
    exact congrArg₂ (· * ·) ((gs_res (𝟙 _) y h₂ hy _).trans (gs_unit (𝟙 _) y _ (h₂ hy) _)).symm rfl
  · obtain ⟨g₀, i, hg₀, hb₀⟩ := nz (f y') (hU (show y' ∈ (⊤ : S'.Opens) from trivial))
    obtain ⟨g, hg₁, hg₂⟩ := Scheme.exists_preimage_of_isPullback m.cart.1 g₀ y' hg₀
    obtain rfl : m.φ g = g₀ := hg₁
    have hgi : m.φ g ∈ t.G.hom ⁻¹ᵁ U ⊓ t.PP.L.U i := t.G.left.basicOpen_le _ hb₀
    obtain ⟨k₀, hk₀⟩ := exists_chart t'.PP.isLB g
    have un : IsUnit (gs (𝟙 _) g _ (θ.f k₀)) := by
      have u₀ : IsUnit (gs (𝟙 _) (m.φ g) _ (θ₀ i)) := by
        rw [gs_eq (𝟙 _) (m.φ g) _ hgi]; exact (t.G.left.mem_basicOpen _ _ hgi).1 hb₀
      have u₁ : IsUnit (gs m.φ g _ (θ₀ i)) := by rw [gs_stalkMap m.φ g _ hgi]; exact u₀.map _
      rw [← ev g i hgi.2, hθ _ (𝟙 _) g i k₀ hgi.2 hk₀] at u₁
      exact isUnit_of_mul_isUnit_right u₁
    exact ⟨g, k₀, hg₂, (t'.G.left.mem_basicOpen _ _ hk₀).2 (by rwa [gs_eq _ _ _ hk₀] at un)⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.FinrankHostDivTwo
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

namespace GlobalTheory.FlagDim

theorem finrank_host_div_two (D : D7) : Module.finrank ℚ D.host.E / 2 = D.R.f := by
  have h : (Module.finrank ℚ D.host.E : ℝ) = 2 * (D.R.f : ℝ) := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    push_cast
    ring
  have h' : Module.finrank ℚ D.host.E = 2 * D.R.f := by exact_mod_cast h
  omega

theorem fnFG_fnTrdeg_record : ∀ (D : D7) (Q : Par D), Q.PinDat → ∀ j, InR D j → FnFG (Q.Xo j) Q.c ∧ FnTrdeg (Q.Xo j) Q.c (WeightFamilies.dimY D j) := by
  intro D Q hP j hj
  obtain ⟨hp, hq, -⟩ := hP j hj
  have h := fnFG_fnTrdeg D.host.E Q.H (Q.Dw j) Q.l (Q.Xo j) Q.c
  rw [finrank_host_div_two] at h
  have e : WeightFamilies.dimY D j = D.R.f * ((Q.Dw j).p * (Q.Dw j).q + (Q.Dw j).p * ((Q.Dw j).p - 1) / 2 +
      (Q.Dw j).q * ((Q.Dw j).q - 1) / 2) := by
    rw [hp, hq]; rfl
  rw [e]
  exact h

end GlobalTheory.FlagDim
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.IsBddSecOfIntegral
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD

namespace GlobalTheory

theorem isBddSec_of_integral : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ (la : Wt X.Ψ r) (N k m : ℕ) (w : Fin N → Frame X.Ψ r → ℂ) (cf : ℕ → MvPolynomial (Fin N) ℂ) (g : Frame X.Ψ r → ℂ), (∀ i, X.IsBddSec la (w i)) → (∀ i < m, (cf i).IsHomogeneous ((m - i) * k)) → X.IsSec (k • la) g → (∀ x ∈ X.dom, g x * g x ^ m + ∑ i ∈ Finset.range m, (g x * MvPolynomial.eval (fun s => w s x) (cf i)) * g x ^ i = 0) → X.IsBddSec (k • la) g := by
  intro E _ _ _ r X la N k m w cf g hw hcf hg heq
  refine ⟨hg, ?_⟩
  choose B hB using fun i => (hw i).2
  obtain ⟨C, hC0, hC⟩ := IntegralCusp.exists_root_bound N k m cf hcf
  refine ⟨C * (∑ i, |B i|) ^ k, fun x hx => ?_⟩
  have h2 := hC _ _ (heq x hx)
  set ν := X.nfac la x with hν
  have hν0 : 0 ≤ ν := Formalism.L2.PjFree.pnorm_fac_nonneg _ _ _
  have h3 : ‖fun i => w i x‖ * ν ≤ ∑ i, |B i| := by
    rw [mul_comm, ← Real.norm_of_nonneg hν0, ← norm_smul,
      pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => abs_nonneg _)]
    intro i
    rw [Pi.smul_apply, norm_smul, Real.norm_of_nonneg hν0, mul_comm]
    exact ((hB i x hx).trans (le_abs_self _)).trans
      (Finset.single_le_sum (f := fun i => |B i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i))
  show ‖g x‖ * X.nfac _ x ≤ _
  rw [IntegralCusp.nfac_nsmul X la (k • la) k (fun τ i => by simp), ← hν]
  calc _ ≤ C * ‖fun i => w i x‖ ^ k * ν ^ k :=
        mul_le_mul_of_nonneg_right h2 (by positivity)
    _ = C * (‖fun i => w i x‖ * ν) ^ k := by ring
    _ ≤ _ := by gcongr

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GenericRegularity.SecGeneratesOfNeZeroOnClosedFibre
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory
namespace SecLineGen

theorem constFn_mul' {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V) (U : X.Opens)
    (a b : V) : constFn π U (a * b) = constFn π U a * constFn π U b := by
  first
  | exact map_mul _ a b
  | (unfold constFn; exact map_mul _ a b)
  | (simp only [constFn, map_mul])
  | (unfold constFn; simp)
  | (unfold constFn Sp; done)

theorem apply_mem_basicOpen_of_mem {V : Type} [CommRing V] {X : Scheme.{0}} (π : X ⟶ Sp V)
    (U : X.Opens) (a : V) (g : X) (hg : g ∈ X.basicOpen (constFn π U a)) :
    π g ∈ PrimeSpectrum.basicOpen a := by
  unfold constFn at hg
  have h0 := Scheme.basicOpen_appLE π U ⊤ (fun _ _ => trivial)
    ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a)
  have hg' : g ∈ U ⊓ π ⁻¹ᵁ ((Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a)) := by
    rw [← h0]
    exact hg
  have h2 : π g ∈ (Sp V).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of V)).inv a) := hg'.2
  have h3 := AlgebraicGeometry.basicOpen_eq_of_affine (R := CommRingCat.of V) a
  first
  | (rw [h3] at h2; exact h2)
  | (unfold Sp at h2; rw [h3] at h2; exact h2)
  | exact h3 ▸ h2
  | (unfold Sp at h2; done)

end SecLineGen


open SecLineGen in
theorem sec_generates_of_ne_zero_on_closed_fibre :
    ∀ (V : Type) [CommRing V] [IsLocalRing V] (X : Scheme.{0}) (π : X ⟶ Sp V) (L : LB X) (θ θ' : LB.Sec L), (∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn π _ a * θ.f i) → (∃ (g : X) (i : L.ι), π g = IsLocalRing.closedPoint V ∧ g ∈ X.basicOpen (θ'.f i)) → (∃ u : Vˣ, ∀ i, θ'.f i = constFn π _ (u : V) * θ.f i) ∧ ∀ σ : LB.Sec L, ∃! a : V, ∀ i, σ.f i = constFn π _ a * θ'.f i := by
  intro V _ _ X π L θ θ' hθ hpt
  obtain ⟨g, i, hgc, hgi⟩ := hpt
  obtain ⟨a, ha, -⟩ := hθ θ'

  have hmem : g ∈ X.basicOpen (constFn π (L.U i) a) := by
    have h := hgi
    rw [ha i, Scheme.basicOpen_mul] at h
    exact h.1

  have hu : IsUnit a := by
    by_contra hna
    have h1 := SecLineGen.apply_mem_basicOpen_of_mem π _ a g hmem
    rw [hgc] at h1
    have h2 : a ∉ (IsLocalRing.closedPoint V).asIdeal := (PrimeSpectrum.mem_basicOpen _ _).1 h1
    have hmax : a ∈ IsLocalRing.maximalIdeal V := (IsLocalRing.mem_maximalIdeal a).2 hna
    first | exact h2 hmax | exact h2 (by simpa using hmax)
  obtain ⟨u, rfl⟩ := hu
  refine ⟨⟨u, fun j => ha j⟩, ?_⟩
  intro σ
  obtain ⟨b, hb, hbu⟩ := hθ σ
  refine ⟨b * ↑u⁻¹, ?_, ?_⟩
  · intro j
    rw [hb j, ha j, ← _root_.mul_assoc, ← SecLineGen.constFn_mul', _root_.mul_assoc b, Units.inv_mul, _root_.mul_one]
  · intro c hc
    have key : c * ↑u = b := hbu (c * ↑u) (fun j => by
      rw [hc j, ha j, ← _root_.mul_assoc, ← SecLineGen.constFn_mul'])
    rw [← key, _root_.mul_assoc, Units.mul_inv, _root_.mul_one]

end GlobalTheory
end

