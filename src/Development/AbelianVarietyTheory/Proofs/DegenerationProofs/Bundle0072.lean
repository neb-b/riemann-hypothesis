module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ToFSurjectiveFractionRing
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsLineBundleGeneratorExtendingDensePart
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsDiscreteValuationRingStalkGeneric
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ValUnitNeZero
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0064

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitCarries
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.ParTranslate
open GlobalTheory.UT GlobalTheory.FieldBaseChange GlobalTheory.ThetaScalar GlobalTheory.ThetaTranslate ReciprocityTheory.ChartRestriction.G.DVR

theorem toStk_onto {F : Type} [Field F] (z : Sp F) : Function.Surjective (toStk z) := fun a => by
  obtain ⟨U, hU, f, rfl⟩ := (Sp F).presheaf.exists_germ_eq a
  obtain rfl : U = ⊤ := eq_top_iff.2 fun y _ => (Subsingleton.elim (α := PrimeSpectrum F) z y) ▸ hU
  obtain ⟨x, rfl⟩ := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of F)).inv).2 f
  exact ⟨x, rfl⟩

theorem isAdd_comm {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F]
    [Algebra (FractionRing R) F] {g g' g'' : GtPtF D F} (h : g.IsAdd g' g'') : g'.IsAdd g g'' := by
  rw [isAdd_iff] at h ⊢
  refine ⟨h.1.trans (mul_comm _ _), fun χ y J hJ => ?_⟩
  have C : IsCub (th D (T := TF (R := R) F) y J) := isCub_cubV D.cub hJ
  rw [C.s12, h.2 χ y J hJ, mul_comm]

section
variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
  [IsCommMonObj G] (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (k : ℕ)
  (w : W0 U)

abbrev Carries (t : SecA A F k) (σ : U.SecGF F k) : Prop :=
  GeneratorPullback.IsoRelM A.L U.LG.L U.gen.hom.left (pullback.fst G.hom (jK R)) w
    (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left k
    (snd (TFK (R := R) F) A.A).left (U.genF F).left t (UnifPre.gFK (G := G) F) (𝟙 _) σ

theorem exists_carries (hw : w.IsGen) (σ : U.SecGF F k) : ∃ t, Carries U F k w t σ := by
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n ≫ U.genF F = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  have hn' : U.genF F ≫ n = 𝟙 _ := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n]
  obtain ⟨-, i₂⟩ := isoRelM_bijective (k := k) (m := (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left)
    (g₁ := (snd (TFK (R := R) F) A.A).left) (h₁ := (U.genF F).left) A.isLB U.LG.isLB hw
    (congrArg (fun q => q.left) (lift_snd _ _ : U.genF F ≫ snd _ _ = _)) n.left
    (congrArg (fun q => q.left) hn) (congrArg (fun q => q.left) hn')
  exact (i₂ σ).exists

theorem exists_unit_carries (a : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (l : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l) (y : Sp F)
    (J : (Sp F ⟶ A.A.left) → A.L.ι) (hJ : Good A.L y J) :
    ∃ c : ((Sp F).presheaf.stalk y)ˣ, ∀ t σ, Carries U F k w t σ →
      toStk y (valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ.f (fun _ => l))) =
        c.val * secVal t (show Sp F ⟶ _ from (ptSecT A.A (a ≫ U.gen.hom)).left) y J := by
  let r : Sp F ⟶ (UnifPre.GF (G := G) F).left := (lift (𝟙 (TFK (R := R) F)) a).left
  let r' : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e₀ : r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = a.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) a)
  have e₁ : r ≫ (U.genF F).left = r' := by
    have : lift (𝟙 (TFK (R := R) F)) a ≫ U.genF F = ptSecT A.A (a ≫ U.gen.hom) := by
      apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
    exact congrArg (fun q => q.left) this
  have e₂ : r' ≫ (snd (TFK (R := R) F) A.A).left =
      (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left := by
    rw [e₀]
    exact congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) (a ≫ U.gen.hom))
  have m₂ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ pullback.fst G.hom (jK R)) y ∈
      U.LG.L.U l := by
    rw [e₀]
    exact (top_le_iff_mem _ _ y).1 hl
  have m₁ : ((r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) ≫ U.gen.hom.left) y ∈
      A.L.U (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) := by
    rw [← e₂]
    exact hJ _
  refine ⟨isoVal w (r ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left) y l
    (J (r' ≫ (snd (TFK (R := R) F) A.A).left)) ^ (k : ℤ), fun t σ h => ?_⟩
  have H := (isoRelM_iff w _ k _ h.1 _ h.2.1 t σ).1 h (Sp F) r y l _ m₂ m₁
  rw [Category.comp_id, e₁] at H
  exact (toStk_valF_gs r _ y (mem_wchart.2 fun _ => m₂) _).trans H

theorem exists_const_actVal (θ : ThetaGrp A.A A.L (k : ℤ) (TFK (R := R) F))
    (a a' : TFK (R := R) F ⟶ (Over.pullback (jK R)).obj G) (h : a' ≫ U.gen.hom = θ.pt * (a ≫ U.gen.hom))
    (l l' : U.LG.L.ι)
    (hl : ⊤ ≤ (show Sp F ⟶ G.left from a.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l)
    (hl' : ⊤ ≤ (show Sp F ⟶ G.left from a'.left ≫ pullback.fst G.hom (jK R)) ⁻¹ᵁ U.LG.L.U l') :
    ∃ c : F, c ≠ 0 ∧ ∀ t t' σ σ', Carries U F k w t σ → Carries U F k w t' σ' → ActVal θ t t' →
      valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a).left) _ (σ'.f (fun _ => l)) =
        c * valF (show Sp F ⟶ _ from (lift (𝟙 (TFK (R := R) F)) a').left) _ (σ.f (fun _ => l')) := by
  let y : Sp F := IsLocalRing.closedPoint F
  obtain ⟨J, hJ⟩ := GlobalTheory.UT.CoefBasic.exists_good' A.isLB y
  obtain ⟨c, hc⟩ := exists_unit_carries U F k w a l hl y J hJ
  obtain ⟨c', hc'⟩ := exists_unit_carries U F k w a' l' hl' y J hJ
  let r : Sp F ⟶ (TFK (R := R) F ⊗ A.A).left := (ptSecT A.A (a ≫ U.gen.hom)).left
  have e : r ≫ (translT A.A θ.pt).left = (ptSecT A.A (a' ≫ U.gen.hom)).left := by
    rw [h]
    exact congrArg (fun q => q.left) (ptSecT_translT (a ≫ U.gen.hom) θ.pt)
  obtain ⟨d, hd⟩ := toStk_onto y (c * thetaVal θ r y J * c'⁻¹).val
  refine ⟨d, fun h0 => ?_, fun t t' σ σ' h₁ h₂ h₃ => (toStk y).injective ?_⟩
  · have : Nontrivial ((Sp F).presheaf.stalk y) := inferInstance
    rw [h0, map_zero] at hd
    exact Units.ne_zero _ hd.symm
  · have a₁ := h₃ (Sp F) r y J hJ
    rw [e] at a₁
    rw [map_mul, hd, hc t' σ' h₂, hc' t σ h₁, Units.val_mul, Units.val_mul, _root_.mul_assoc,
      Units.inv_mul_cancel_left, _root_.mul_assoc]
    exact congrArg _ a₁

end

theorem parAt_translate : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (k : ℕ) (pk : QkPt u.D.toPre (PadicAlgCl p) k) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A) (a a' : u.PtC) (g g' : GtPtF u.D.toPre (PadicAlgCl p)), 1 ≤ k → QkToAkU u.U.toUnifPre (PadicAlgCl p) k pk x → a' ≫ u.U.gen.hom = x * (a ≫ u.U.gen.hom) → GtPtF.IsAdd pk.g g g' → u.ParAt k a g → u.ParAt k a' g' := by
  intro hL o Ω _ _ _ _ S ρ p _ y₀ u k pk x a a' g g' hk hx ha hg hpar w' hw' l' hl'
  have hG := hL.1.globalFns
  have : CharZero u.V :=
    ((algebraMap (FractionRing u.V) (PadicAlgCl p)).comp (algebraMap u.V (FractionRing u.V))).charZero
  have hA : AdmBase u.V (IsLocalRing.maximalIdeal u.V) := ⟨inferInstance, inferInstance, inferInstance, u.complete⟩
  obtain ⟨w₀, hw₀⟩ := u.U.toUnifPre.ext
  obtain ⟨v, hv⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k pk.g.b
  obtain ⟨ω₀, h₀⟩ := exists_normalisation (D := u.D.toPre) (F := PadicAlgCl p) k g.b
  obtain ⟨ω₁, h₁, -, hco⟩ := CoefPhi.coef_phi hL u.V _ hA u.D (PadicAlgCl p) k hk pk v hv g g' (isAdd_comm hg) ω₀ h₀
  replace hco := hco 1 k le_rfl (mul_one k).symm pk (one_smul _ _).symm rfl v ω₀ ω₁
    ⟨hv, fun _ _ _ => (pow_one _).symm⟩ ⟨h₀, fun _ _ _ => (pow_one _).symm⟩ ⟨h₁, fun _ _ _ => (pow_one _).symm⟩
  obtain ⟨c₁, hc₁, -, hfr⟩ := ((CoefBasic.coef_basic u.V u.D.toPre (PadicAlgCl p) k g').2.2 ω₁ h₁).2.2.1 w' hw'
  obtain ⟨θ, rfl, hθ⟩ := exists_theta_actVal u.U (PadicAlgCl p) hG hL.1.kerPow hk pk x hx w₀ hw₀ v hv
  obtain ⟨l, hl⟩ := exists_chart u.U.LG.isLB (u.toG a (IsLocalRing.closedPoint (PadicAlgCl p)))
  replace hl := (top_le_iff_mem _ _ _).2 hl
  obtain ⟨κ, hκ, hsum⟩ := hpar ω₀ h₀ l hl
  obtain ⟨c₂, hc₂, hval⟩ := exists_const_actVal u.U.toUnifPre (PadicAlgCl p) k w₀ θ a a' ha l l' hl hl'
  obtain ⟨e, he⟩ := GlobalTheory.exists_linearEquiv_expandsF hG u.U (PadicAlgCl p) hk w₀ hw₀
  refine ⟨c₁ * (κ * c₂), mul_ne_zero hc₁ (mul_ne_zero hκ hc₂), fun σ s hs => ?_⟩
  obtain ⟨t, ht⟩ := exists_carries u.U.toUnifPre (PadicAlgCl p) k w₀ hw₀ σ
  obtain ⟨t', ht'⟩ := exists_actVal u.A.isLB θ t
  have hE : u.U.toUnifPre.ExpandsF (PadicAlgCl p) k w₀ t' (e t') := (he _ _).2 rfl
  have hΦ := (hθ t t' s (e t') ⟨σ, ht, hs⟩ hE).2 ht'
  obtain ⟨σ', hσ', hs'⟩ := hE
  have H := hsum σ' _ hs'
  rw [hval t t' σ σ' ht hσ' ht', ← (Equiv.addRight pk.y).hasSum_iff] at H
  have H' := H.mul_left c₁
  rw [_root_.mul_assoc, _root_.mul_assoc]
  refine (congrArg (HasSum · _) (funext fun χ => ?_)).mp H'
  exact (congrArg (c₁ * ·) (hco s _ hΦ χ)).trans (hfr s χ).symm

end GlobalTheory.ZH.ParTranslate
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsUnitExtendOfGeneric
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

set_option backward.isDefEq.respectTransparency false

namespace GlobalTheory.GenericExtend

theorem eq_of_valR_eq {Y : Scheme.{0}} [IsReduced Y] {V : Y.Opens} {f g : Γ(Y, V)}
    (H : ∀ x ∈ V, ∃ (K : Type) (_ : Field K) (h : Sp K ⟶ Y), (∀ o, h o = x) ∧
      valR h V f = valR h V g) : f = g := by
  rw [← sub_eq_zero, ← basicOpen_eq_bot_iff, eq_bot_iff]
  intro x hx
  exfalso
  have hxV := Y.basicOpen_le _ hx
  obtain ⟨K, _, h, ho, hv⟩ := H x hxV
  have h₁ : ⊤ ≤ h ⁻¹ᵁ V := fun o _ ↦ show h o ∈ V from (ho o).symm ▸ hxV
  have h₂ := (Points.le_preimage_basicOpen_iff h h₁ (f - g)).1
    fun o _ ↦ show h o ∈ Y.basicOpen (f - g) from (ho o).symm ▸ hx
  rw [Points.valR_eq h V h₁, Points.valR_eq h V h₁] at hv
  rw [Points.valR_eq h V h₁, map_sub, hv, sub_self] at h₂
  exact not_isUnit_zero h₂

theorem compat_of_valF {Q Y : Scheme.{0}} [IsReduced Q] {N : LB Y} {J : Q ⟶ Y}
    {τ : ∀ a, Γ(Q, J ⁻¹ᵁ N.U a)ˣ}
    (H : ∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ Q), Set.range (h ≫ J) ⊆ N.U a →
      Set.range (h ≫ J) ⊆ N.U b →
      valF h _ (τ a).val = valF (h ≫ J) _ (N.g a b).val * valF h _ (τ b).val) :
    Compat N J τ := by
  intro Z r z a b ha hb
  have l₁ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U a := J.preimage_mono inf_le_left
  have l₂ : J ⁻¹ᵁ (N.U a ⊓ N.U b) ≤ J ⁻¹ᵁ N.U b := J.preimage_mono inf_le_right
  have key : res l₁ (τ a) = pullU J _ (N.g a b) * res l₂ (τ b) := by
    refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Q.residueField x, inferInstance,
      Q.fromSpecResidueField x, fun o ↦ Scheme.fromSpecResidueField_apply x o, ?_⟩)
    have ho : ∀ o, (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) o = x :=
      fun o ↦ Scheme.fromSpecResidueField_apply x o
    generalize (Q.fromSpecResidueField x : Sp (Q.residueField x) ⟶ Q) = h at ho
    have h₁ : ⊤ ≤ h ⁻¹ᵁ J ⁻¹ᵁ (N.U a ⊓ N.U b) := fun o _ ↦
      show h o ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) from (ho o).symm ▸ hx
    have := H a b _ h (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).1)
      (by rintro _ ⟨o, rfl⟩; exact (h₁ (x := o) trivial).2)
    rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp,
      ← Points.valR_res h l₁ h₁, ← Points.valR_res h l₂ h₁, ← Points.valR_mul _ _ h₁] at this
    exact this
  have hz : r z ∈ J ⁻¹ᵁ (N.U a ⊓ N.U b) := ⟨ha, hb⟩
  have := congrArg (gm r z _) key
  rwa [map_mul, gm_res r z l₁ hz, gm_res r z l₂ hz, gm_pull r J z _ hz] at this

theorem exists_unit_extend_of_generic : ∀ (X P : Scheme.{0}) [IsLocallyNoetherian X] (Ω : Type) [Field Ω] (j : Sp Ω ⟶ X), ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → IsPreimmersion j → Flat j → IsDominant j → ∀ (p : P ⟶ X) (e : X ⟶ P) (N : LB P), e ≫ p = 𝟙 X → Smooth p → GeometricallyIntegral p → N.IsLB → ∀ τ : ∀ a, Γ(pullback p j, pullback.fst p j ⁻¹ᵁ N.U a)ˣ, (∀ (a b : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → Set.range (h ≫ pullback.fst p j) ⊆ N.U b → valF h _ (τ a).val = valF (h ≫ pullback.fst p j) _ (N.g a b).val * valF h _ (τ b).val) → (∀ a, ∃ u : Γ(X, e ⁻¹ᵁ N.U a)ˣ, ∀ h : Sp Ω ⟶ pullback p j, h ≫ pullback.fst p j = j ≫ e → Set.range (j ≫ e) ⊆ N.U a → valF h _ (τ a).val = valF j _ u.val) → ∃ σ : ∀ a, Γ(P, N.U a)ˣ, ∀ (a : N.ι) (K : Type) [Field K] (h : Sp K ⟶ pullback p j), Set.range (h ≫ pullback.fst p j) ⊆ N.U a → valF (h ≫ pullback.fst p j) _ (σ a).val = valF h _ (τ a).val := by
  intro X P _ Ω _ j hX _ _ _ p e N he _ _ hN τ H₁ H₂
  have := GlobalTheory.IsNormalScheme.of_pred hX
  have := isNormalScheme_of_smooth p
  have := LocallyOfFiniteType.isLocallyNoetherian p
  have : QuasiCompact j := ⟨fun U _ _ ↦ TopologicalSpace.NoetherianSpace.isCompact _⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant j
  have hJ := (pullback.fst p j).app_injective
  have := DvrModel.isIntegral_of_geometricallyIntegral (IsPullback.of_hasPullback p j)
  have hτ : Compat N (pullback.fst p j) τ := compat_of_valF H₁
  choose ρ hρ using H₂
  let eU : Sp Ω ⟶ pullback p j := pullback.lift (j ≫ e) (𝟙 _) (by simp [he])
  have w : eU ≫ pullback.fst p j = j ≫ e := pullback.lift_fst _ _ _
  have hπ : eU ≫ pullback.snd p j = 𝟙 _ := pullback.lift_snd _ _ _
  have hτρ : ∀ (Z : Scheme.{0}) (κ : Z ⟶ Sp Ω) (z : Z) (a : N.ι),
      e (j (κ z)) ∈ N.U a → gm (κ ≫ eU) z (pullback.fst p j ⁻¹ᵁ N.U a) (τ a) =
        gm (κ ≫ j) z (e ⁻¹ᵁ N.U a) (ρ a) := by
    intro Z κ z a ha
    have hle : j ⁻¹ᵁ e ⁻¹ᵁ N.U a ≤ eU ⁻¹ᵁ pullback.fst p j ⁻¹ᵁ N.U a := by
      rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, w]
    have h₁ : ⊤ ≤ (𝟙 (Sp Ω) :) ⁻¹ᵁ j ⁻¹ᵁ e ⁻¹ᵁ N.U a := fun o _ ↦
      show e (j o) ∈ N.U a from Subsingleton.elim (κ z) o ▸ ha
    have key : res hle (pullU eU _ (τ a)) = pullU j _ (ρ a) := by
      refine Units.ext (eq_of_valR_eq fun x hx ↦ ⟨Ω, inferInstance, 𝟙 _,
        fun o ↦ Subsingleton.elim _ _, ?_⟩)
      have := hρ a eU w (by rintro _ ⟨o, rfl⟩; exact h₁ (x := o) trivial)
      rw [Points.valF_eq_valR, Points.valF_eq_valR] at this
      refine (Points.valR_res _ hle h₁ _).trans ?_
      refine (Points.valR_comp (𝟙 _) eU _ _).symm.trans ?_
      refine Eq.trans ?_ (Points.valR_comp (𝟙 _) j _ _)
      rwa [Category.id_comp, Category.id_comp]
    have := congrArg (gm κ z _) key
    rwa [gm_res_pullU κ eU z hle ha, gm_pull κ j z _ ha] at this
  have key : ∀ a, ∀ y ∈ N.U a, Order.coheight y ≤ 1 → y ∉ Set.range (pullback.fst p j) →
      ExtAt (pullback.fst p j) (N.U a) (τ a).val y ∧
        ExtAt (pullback.fst p j) (N.U a) ((τ a)⁻¹).val y := fun a y ha h1 hy ↦ by
    refine extAt_of_coheight_eq_one j p he hN w hπ hτ hτρ y
      (le_antisymm (coheight_apply_le_one p h1) (ENat.one_le_iff_ne_zero.2 fun h0 ↦ hy ?_)) a ha
    rw [Scheme.Pullback.range_fst]
    obtain ⟨ξ, hξ, hξy⟩ := exists_specializes_mem_range j (p y)
    exact (Flat.generalizingMap j).stableUnderGeneralization_range
      (show p y ⤳ ξ from Order.coheight_eq_zero.1 h0 hξy) hξ
  choose s hs using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).1
  choose s' hs' using fun a ↦ exists_app_eq _ hJ _ _ fun y ha h1 hy ↦ (key a y ha h1 hy).2
  have hm : ∀ a, s a * s' a = 1 := fun a ↦ hJ _ (by
    change ((pullback.fst p j).app _).hom _ = ((pullback.fst p j).app _).hom _
    rw [map_mul, map_one, hs, hs', Units.mul_inv])
  refine ⟨fun a ↦ ⟨s a, s' a, hm a, (mul_comm _ _).trans (hm a)⟩, fun a K _ h _ ↦ ?_⟩
  rw [Points.valF_eq_valR, Points.valF_eq_valR, Points.valR_comp]
  exact congrArg _ (hs a)

end GlobalTheory.GenericExtend
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsZpowMulIsUnitOfMem
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH GlobalTheory.ZH.FrameNorm

set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace GlobalTheory.ZH.FrameNorm
open CrdCalc TopologicalSpace

section Points
variable {K C : Type} [Field K] [Field C] [IsAlgClosed C] {Y : Scheme.{0}} {q : Y ⟶ Sp K} [LocallyOfFiniteType q]
  {σ : K →+* C}


variable (q σ) in
theorem exists_point_mem {Z : Set Y} (hZ : IsLocallyClosed Z) (hne : Z.Nonempty) :
    ∃ x : Sp C ⟶ Y, x ≫ q = spMap σ ∧ ∀ w, x w ∈ Z := by
  have hs : Surjective (spMap σ) := ⟨fun y ↦ by
    obtain ⟨z⟩ : Nonempty ↥(Sp C) := inferInstance
    exact ⟨z, Subsingleton.elim _ _⟩⟩
  have hJ : JacobsonSpace ↥(pullback q (spMap σ)) :=
    LocallyOfFiniteType.jacobsonSpace (pullback.snd q (spMap σ))
  obtain ⟨y, hy⟩ := hne
  obtain ⟨z₀, rfl⟩ := (pullback.fst q (spMap σ)).surjective y
  obtain ⟨z, hzZ, hz⟩ := nonempty_inter_closedPoints (Z := pullback.fst q (spMap σ) ⁻¹' Z) ⟨z₀, hy⟩
    (hZ.preimage (pullback.fst q (spMap σ)).continuous)
  replace hz : IsClosed {z} := hz
  refine ⟨pointOfClosedPoint (pullback.snd q (spMap σ)) z hz ≫ pullback.fst _ _,
    by rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc], fun w => ?_⟩
  rw [Scheme.Hom.comp_apply, pointOfClosedPoint_apply]
  exact hzZ

theorem eq_of_val_eq [IsReduced Y] {W : Y.Opens} {r s : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r = valR x W s) : r = s := by
  rw [← sub_eq_zero]
  refine eq_zero_of_basicOpen_eq_bot _ (eq_bot_iff.2 fun y hy => ?_)
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ (Y.basicOpen (r - s)).isOpen.isLocallyClosed ⟨y, hy⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => Y.basicOpen_le _ (hm w)
  have := ((isUnit_valR_iff x W hW (r - s)).2 fun w _ => hm w).ne_zero
  rw [valR_eq x W hW, map_sub, ← valR_eq, ← valR_eq, h x hx hW, sub_self] at this
  exact (this rfl).elim

theorem isUnit_of_val_ne_zero {W : Y.Opens} {r : Γ(Y, W)}
    (h : ∀ x : Sp C ⟶ Y, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → valR x W r ≠ 0) : IsUnit r := by
  refine RingedSpace.isUnit_of_isUnit_germ _ _ _ fun y hy => (Scheme.mem_basicOpen _ _ y hy).1 ?_
  by_contra hn
  obtain ⟨x, hx, hm⟩ := exists_point_mem q σ
    (W.isOpen.isLocallyClosed.inter (Y.basicOpen r).isOpen.isClosed_compl.isLocallyClosed) ⟨y, hy, hn⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ W := fun w _ => (hm w).1
  obtain ⟨w⟩ : Nonempty ↥(Sp C) := inferInstance
  exact (hm w).2 ((isUnit_valR_iff x W hW r).1 (h x hx hW).isUnit (show w ∈ (⊤ : (Sp C).Opens) from trivial))

theorem exists_glue [IsReduced Y] {I : Type} (W : Y.Opens) (T : I → Y.Opens) (F : I → (Sp C ⟶ Y) → C)
    (hT : ∀ z, ∃ m, z ∈ T m) (hF : ∀ m, Reg q σ (W ⊓ T m) (F m))
    (h : ∀ m m' x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F m x = F m' x) :
    ∃ r : Γ(Y, W), ∀ m x, x ≫ q = spMap σ → ⊤ ≤ x ⁻¹ᵁ W → ⊤ ≤ x ⁻¹ᵁ T m → F m x = valR x W r := by
  choose u hu using hF
  obtain ⟨r, hr, -⟩ := Y.sheaf.existsUnique_gluing' (fun m => W ⊓ T m) W (fun _ => homOfLE inf_le_left)
    (fun y hy => Opens.mem_iSup.2 ((hT y).imp fun _ hm => ⟨hy, hm⟩)) u
    (fun m m' => eq_of_val_eq (q := q) (σ := σ) (W := W ⊓ T m ⊓ (W ⊓ T m')) fun x hx hW =>
      (valR_res x inf_le_left hW _).trans ((hu m x hx fun _ hz => (hW hz).1).symm.trans
        ((h m m' x hx (fun _ hz => (hW hz).1.1) (fun _ hz => (hW hz).1.2) fun _ hz => (hW hz).2.2).trans
          ((hu m' x hx fun _ hz => (hW hz).2).trans (valR_res x inf_le_right hW _).symm))))
  refine ⟨r, fun m x hx hW hm => ?_⟩
  have hh : ⊤ ≤ x ⁻¹ᵁ (W ⊓ T m) := fun _ hz => ⟨hW hz, hm hz⟩
  rw [hu m x hx hh, ← hr m]
  exact valR_res x inf_le_left hh r

end Points


open GlobalTheory.PrimeSection in
theorem exists_zpow_mul_isUnit_of_mem {X : Scheme.{0}} {t : Γ(X, ⊤)} {ξ : X}
    (hη : ∀ x : X, x ∉ X.basicOpen t ↔ ξ ⤳ x)
    (hp : ∀ U : X.Opens, IsAffineOpen U → ξ ∈ U → Prime (X.presheaf.map (homOfLE (le_top : U ≤ ⊤)).op t))
    [IsIntegral X] [IsLocallyNoetherian X] {A : Type} {U : A → X.Opens} {g : ∀ a b, Γ(X, U a ⊓ U b)}
    {a₀ : A} (h₀ : ξ ∈ U a₀) (hg : ∀ a b, IsUnit (g a b)) (τ : Γ(X, X.basicOpen t)ˣ)
    (hτ : (τ : Γ(X, X.basicOpen t)) = X.presheaf.map (homOfLE le_top).op t)
    {r : ∀ a, Γ(X, U a ⊓ X.basicOpen t)}
    (hr : ∀ a b, X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_left)).op (r a) =
      X.presheaf.map (homOfLE (inf_le_left : U a ⊓ U b ⊓ X.basicOpen t ≤ U a ⊓ U b)).op (g a b) *
        X.presheaf.map (homOfLE (inf_le_inf_right _ inf_le_right)).op (r b))
    (hru : ∀ a, IsUnit (r a)) :
    ∃ n : ℤ, ∃ s : ∀ a, Γ(X, U a), (∀ a, IsUnit (s a)) ∧
      ∀ a, X.presheaf.map (homOfLE inf_le_left).op (s a) =
        X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a := by
  obtain ⟨hdvr, hirr⟩ := isDiscreteValuationRing_stalk hη hp
  have hD : genericPoint X ∈ X.basicOpen t := genericPoint_mem_basicOpen (ne_zero hp)
  have hx₀ : X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀) (r a₀) ≠ 0 := ((hru a₀).map _).ne_zero
  have hτn : ∀ n : ℤ, X.presheaf.germ _ _ hD (↑(τ ^ n) : Γ(X, X.basicOpen t)) =
      algebraMap _ X.functionField (X.presheaf.germ ⊤ ξ trivial t) ^ n := fun n ↦ by
    rw [algebraMap_germ, ← germ_res (le_top : X.basicOpen t ≤ ⊤) hD, ← hτ]
    let φ : Γ(X, X.basicOpen t) →+* X.functionField := (X.presheaf.germ _ _ hD).hom
    change φ _ = φ _ ^ n
    rw [← MonoidHom.coe_coe, ← Units.coe_map, map_zpow, Units.val_zpow_eq_zpow_val]
    rfl
  obtain ⟨n, ⟨u, hu, hn⟩, -⟩ :=
    GlobalTheory.PrimeElement.existsUnique_zpow_mul_eq_unit (K := X.functionField) hirr hx₀
  have : ∀ a, ∃ s : Γ(X, U a), X.presheaf.map (homOfLE inf_le_left).op s =
      X.presheaf.map (homOfLE inf_le_right).op (↑(τ ^ n) : Γ(X, X.basicOpen t)) * r a :=
    fun a ↦ exists_res_eq hη hp _ fun h ↦
      ⟨X.presheaf.germ (U a ⊓ U a₀) ξ ⟨h, h₀⟩ (g a a₀) * u, by
        rw [map_mul, map_mul, hn, germ_res, hτn, algebraMap_germ,
          germ_eq_mul_germ hr (a := a) _ (genericPoint_mem_inf hp h₀)]
        ring⟩
  choose s hs using this
  have hs₀ : ξ ∈ X.basicOpen (s a₀) := by
    rw [X.mem_basicOpen _ ξ h₀]
    convert hu
    apply IsFractionRing.injective _ X.functionField
    have := congrArg (X.presheaf.germ _ _ (genericPoint_mem_inf hp h₀)) (hs a₀)
    rw [map_mul, germ_res, germ_res, hτn] at this
    rw [algebraMap_germ, hn, this]
  refine ⟨n, s, fun b ↦ isUnit_of_isUnit_res hη hp ?_ fun h ↦
    mem_basicOpen_of_compatible hg (compatible_of_res_eq hD hr _ hs) h hs₀, hs⟩
  rw [hs b]
  exact ((Units.isUnit _).map _).mul (hru b)


open GlobalTheory.DvrModel GlobalTheory.PrimeSection in
theorem norm_const : ∀ (p : ℕ) [Fact p.Prime] (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (K : Type) [Field K] [Algebra V K] [IsFractionRing V K] (σ : K →+* PadicAlgCl p) (jV : V →+* OO p), (∀ a, (jV a : PadicAlgCl p) = σ (algebraMap V K a)) → IsLocalHom jV → ∀ (H HK : Scheme.{0}) (f : H ⟶ Sp V) (j : HK ⟶ H) (q : HK ⟶ Sp K), Smooth f → GeometricallyIntegral f → IsPullback j q f (spMap (algebraMap V K)) → ∀ (A I : Type) (U : A → H.Opens) (T : I → HK.Opens) (F : A → I → (Sp (PadicAlgCl p) ⟶ HK) → PadicAlgCl p), (∀ z, ∃ m, z ∈ T m) → (∀ a m, Reg q σ (j ⁻¹ᵁ U a ⊓ T m) (F a m)) → (∀ a m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → F a m x ≠ 0) → (∀ a m m' x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ⊤ ≤ x ⁻¹ᵁ T m' → F a m x = F a m' x) → (∀ a a', ∃ g : Γ(H, U a ⊓ U a')ˣ, ∀ m x, x ≫ q = spMap σ → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a → ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a' → ⊤ ≤ x ⁻¹ᵁ T m → F a m x = valR (x ≫ j) (U a ⊓ U a') g.val * F a' m x) → ∃ κ : ℝ, 0 < κ ∧ ∀ a m (c : Sp (OO p) ⟶ H) x, c ≫ f = spMap jV → x ≫ j = gPt p ≫ c → x ≫ q = spMap σ → ⊤ ≤ c ⁻¹ᵁ U a → ⊤ ≤ x ⁻¹ᵁ T m → ‖F a m x‖ = κ := by
  intro p _ V _ _ _ K _ _ _ σ jV hj hloc H HK f j q hsm hgi hK A I U T F hT hreg hne h₁ h₂
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have hs := IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V)))
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hK
  have := GlobalTheory.DvrModel.isIntegral_of_geometricallyIntegral hs
  have := isOpenImmersion_generic hK
  have := GlobalTheory.DvrModel.isIntegral hK
  have := GlobalTheory.DvrModel.isLocallyNoetherian f
  have : LocallyOfFiniteType q := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType) hK inferInstance
  have hη := notMem_basicOpen_iff_specializes hϖ hs
  by_cases hA : ∃ a₀, pullback.fst f (Spec.map (CommRingCat.ofHom (IsLocalRing.residue V))) (genericPoint _) ∈ U a₀
  swap
  · refine ⟨1, one_pos, fun a m c x hc _ _ ha _ => (hA ⟨a, mem_of_notMem_basicOpen hη
      (ha (show IsLocalRing.closedPoint (OO p) ∈ (⊤ : (Sp (OO p)).Opens) from trivial)) ?_⟩).elim⟩
    rw [notMem_basicOpen_iff f hϖ, ← Scheme.Hom.comp_apply, hc]
    exact IsLocalRing.comap_closedPoint jV
  obtain ⟨a₀, h₀⟩ := hA
  choose r hr using fun a => exists_glue (j ⁻¹ᵁ U a) T (F a) hT (hreg a) (h₁ a)
  choose g hg using h₂
  have hpt : ∀ x : Sp (PadicAlgCl p) ⟶ HK, ∃ m, ⊤ ≤ x ⁻¹ᵁ T m := fun x =>
    (hT _).imp fun m hm => (top_le_iff x _).2 hm
  have hru : ∀ a, IsUnit (r a) := fun a => isUnit_of_val_ne_zero (q := q) (σ := σ) fun x hx hW => by
    obtain ⟨m, hm⟩ := hpt x
    rw [← hr a m x hx hW hm]
    exact hne a m x hx hW hm
  have h0 : algebraMap V K ϖ ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective V K)).2 hϖ.ne_zero
  let φ : K →+* Γ(HK, ⊤) := q.appTop.hom.comp (Scheme.ΓSpecIso (.of K)).inv.hom
  obtain ⟨r', τ', hτ', hr', -, hu', E⟩ := exists_transport (opensRange_generic hϖ hK)
    (g := fun a b => (g a b).val) (fun a => rfl) r
    (fun a b => eq_of_val_eq (q := q) (σ := σ) fun x hx hW => by
      obtain ⟨m, hm⟩ := hpt x
      have ha : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := fun _ hz => (hW hz).1
      have hb : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U b := fun _ hz => (hW hz).2
      refine (valR_res x inf_le_left hW _).trans (((hr a m x hx ha hm).symm.trans (hg a b m x hx ha hb hm)).trans
        (Eq.symm ((valR_mul x _ hW _ _).trans (congrArg₂ (· * ·) (GlobalTheory.Points.valR_appLE x j _ hW _) ?_))))
      exact (valR_res x inf_le_right hW _).trans (hr b m x hx hb hm).symm)
    (Units.map φ.toMonoidHom (Units.mk0 _ h0)) (appTop_cst hK.w ϖ).symm
  obtain ⟨n, s, hsu, hs'⟩ := exists_zpow_mul_isUnit_of_mem hη (prime_res_generic hϖ hs) h₀
    (fun a b => (g a b).isUnit) τ' hτ' hr' fun a => hu' a (hru a)
  have hpos : 0 < ‖σ (algebraMap V K ϖ)‖ ^ n := zpow_pos (norm_pos_iff.2 ((map_ne_zero σ).2 h0)) n
  refine ⟨(‖σ (algebraMap V K ϖ)‖ ^ n)⁻¹, inv_pos.2 hpos, fun a m c x hc hx hq ha hm => ?_⟩
  have hW : ⊤ ≤ x ⁻¹ᵁ j ⁻¹ᵁ U a := by
    show ⊤ ≤ (x ≫ j) ⁻¹ᵁ U a
    rw [hx]
    exact fun _ _ => ha trivial
  have e := congrArg (valR x _) ((E n a (s a)).1 (hs' a))
  have e₁ : valR x ⊤ (Units.map φ.toMonoidHom (Units.mk0 _ h0)).val = σ (algebraMap V K ϖ) :=
    (GlobalTheory.Points.valR_comp x q ⊤ _).symm.trans (by
      rw [hq]
      exact GlobalTheory.Points.valR_specMap (CommRingCat.ofHom σ) _)
  have e₂ : ((valR c (U a) (s a) : OO p) : PadicAlgCl p) = σ (algebraMap V K ϖ) ^ n * F a m x := by
    rw [hr a m x hq hW hm, ← e₁, ← val_zpow x (U := ⊤) (fun _ _ => trivial)]
    refine Eq.trans ?_ ((e.trans (valR_mul x _ hW _ _)).trans (congrArg (· * _) (valR_res x le_top hW _)))
    refine Eq.trans ?_ (GlobalTheory.Points.valR_appLE x j _ hW _).symm
    rw [hx]
    exact ((valR_spMap (OO p).subtype c _ ha).2 _).symm
  have e₃ : ‖((valR c (U a) (s a) : OO p) : PadicAlgCl p)‖ = 1 := by
    have hu : IsUnit (valR c (U a) (s a)) := by
      rw [valR_eq c _ ha]
      exact (hsu a).map _
    obtain ⟨d, hd⟩ := hu.exists_right_inv
    have e' := congrArg (fun z : OO p => ‖(z : PadicAlgCl p)‖) hd
    simp only [MulMemClass.coe_mul, norm_mul, OneMemClass.coe_one, norm_one] at e'
    exact le_antisymm ((mem_OO_iff _).1 (Subtype.prop _))
      (e'.ge.trans (mul_le_of_le_one_right (norm_nonneg _) ((mem_OO_iff _).1 d.2)))
  rw [e₂, norm_mul, norm_zpow] at e₃
  exact eq_inv_of_mul_eq_one_right e₃

end GlobalTheory.ZH.FrameNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeightsStatement
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isoFree_perp_labelKernel_weights : Laws → Laws2 → UTorsSt → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (p : ℕ) [Fact p.Prime] (y₀ : S.R →+* PadicAlgCl p) (u : ρ.UTest p y₀) (yy : S.Gam →+ u.D.toPre.X ⧸ (nsmulAddMonoidHom (S.r * S.N) : u.D.toPre.X →+ u.D.toPre.X).range), Function.Surjective yy → (∀ (a : S.Gam) (pk : QkPt u.D.toPre (PadicAlgCl p) (S.r * S.N)) (x : TFK (R := u.V) (PadicAlgCl p) ⟶ u.A.A), QkToAkU u.U.toUnifPre (PadicAlgCl p) (S.r * S.N) pk x → x.left ≫ u.φ = spMap y₀ ≫ (ρ.pt a).left → yy a = QuotientAddGroup.mk pk.y) → S.IsoFree (S.perp yy.ker) ∧ ∃ wt : u.D.toPre.X →+ (S.perp yy.ker →+ ZMod S.N), ∀ (x : S.Gam) (α : u.D.toPre.X), yy x = QuotientAddGroup.mk α → ∀ t : S.perp yy.ker, wt α t = ZMod.castHom (dvd_mul_left S.N S.r) (ZMod S.N) (eStd S.g _ t x) := by
  first | exact @GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights | exact GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights | (intros; apply GlobalTheory.ZH.TorusPerp.isoFree_perp_and_weights <;> assumption)
end

