module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0009
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SmoothIsMultiplicative

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PullAlLinearCombination
section
set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.PullComb

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {D : DegData V (maximalIdeal V)}
  {F : Type} [Field F] [Algebra (FractionRing V) F] {O : Type} [Ring O] [StarRing O] [Module O D.toPre.X]

theorem aF_fst (oa : D.toPre.OAct O) (a : O) :
    (aF D F oa a).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = (fst (TF (R := V) F) D.toPre.P.A).left := by
  rw [← Over.comp_left]
  unfold aF
  rw [lift_fst]

theorem gen_val (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (χ : D.toPre.X)
    {u u' : LB.Gen (LB.LinComb D.toPre.P.L (pullφ D F oa a χ) (pullε k N))} (hu : u.IsGen) (hu' : u'.IsGen)
    {K : Type} [Fintype K] {φ : K → ((TF (R := V) F).left ⟶ D.toPre.P.A.left)} {ε : K → ℤ}
    {t : LB.Gen (LB.LinComb D.toPre.P.L φ ε)}
    (c : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u (DegPre.zF D.toPre F).left) t)
    (c' : LB.Gen.Corr D.toPre.P.L _ _ _ _ (LB.pullGen D.toPre.P.L _ _ u' (DegPre.zF D.toPre F).left) t)
    (Z : Scheme.{0}) (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) (J) (hJ : Good D.toPre.P.L z J) :
    val u r z J = val u' r z J := by
  have hβ : Function.Surjective (β_ (TF (R := V) F) D.toPre.P.A).hom.left.appTop.hom := by
    intro x
    refine ⟨(β_ (TF (R := V) F) D.toPre.P.A).inv.left.appTop.hom x, ?_⟩
    have hid : (β_ (TF (R := V) F) D.toPre.P.A).hom.left ≫ (β_ (TF (R := V) F) D.toPre.P.A).inv.left = 𝟙 _ := by
      rw [← Over.comp_left, Iso.hom_inv_id, Over.id_left]
    have hx := congrArg (fun g => g.appTop.hom x) hid
    first
      | simpa [Scheme.Hom.appTop] using hx
      | (simp only [Scheme.Hom.comp_appTop, Scheme.Hom.id_appTop, CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at hx; exact hx)
  have hp : Function.Surjective (fst (TF (R := V) F) D.toPre.P.A).left.appTop.hom := by
    have h1 := surj_comp hβ (surj_snd hG D.toPre.P.isAb (TF (R := V) F))
    rwa [← Over.comp_left, braiding_hom_snd] at h1
  have he : (DegPre.zF D.toPre F).left ≫ (fst (TF (R := V) F) D.toPre.P.A).left = 𝟙 _ := by
    rw [← Over.comp_left]
    unfold DegPre.zF
    rw [lift_fst, Over.id_left]
  refine gen_unique D.toPre.P.isLB _ _ he hp hu hu' ?_ Z r z J hJ
  intro y J' hJ'
  have e1 := val_pull hJ' u (DegPre.zF D.toPre F).left (𝟙 _)
  have e2 := val_pull hJ' u' (DegPre.zF D.toPre F).left (𝟙 _)
  rw [Category.id_comp] at e1 e2
  rw [← e1, ← e2, val_corr hJ' c, val_corr hJ' c']

private lemma sval_add_of_good {k : ℕ} (s s' : Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) :
    sval ((s + s').s α) r z J = sval (s.s α) r z J + sval (s'.s α) r z J := by
  unfold sval
  exact (congrArg (gs r z _) (ReciprocityTheory.ChartRestriction.G.DVR.add_f s s' α _)).trans (gs_add _ _ _ (hJ.mem _ r) _ _)

theorem pull_add (hG : GlobalFnsSt) (oa : D.toPre.OAct O) (a : O) (k N : ℕ) {s s' : Fam D.toPre F k}
    {t t' : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) (h' : PullAl D F oa a k N s' t') :
    PullAl D F oa a k N (s + s') (t + t') := by
  obtain ⟨h1, h2⟩ := h
  obtain ⟨h1', h2'⟩ := h'
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hr⟩ := h1 χ
    obtain ⟨u', hu', hc', hr'⟩ := h1' χ
    refine ⟨u, hu, hc, ?_⟩
    refine (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 ?_
    intro y J hJ
    have e1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hr _ (𝟙 _) y J hJ
    have e2 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u').1 hr' _ (𝟙 _) y J hJ
    have e3 := gen_val hG oa a k N χ hu' hu hc' hc _ (𝟙 _) y J hJ
    rw [sval_add_of_good _ _ _ _ _ hJ, sval_add_of_good _ _ _ _ _ hJ, e1, e2, e3, add_mul]
  · rw [ReciprocityTheory.ChartRestriction.G.DVR.add_f, h2 β hβ j, h2' β hβ j, add_zero]

private lemma sval_smul_eq_gs_gF_mul_of_good {k : ℕ} (ζ : F) (s : Fam D.toPre F k) (α : D.toPre.X) {Z : Scheme.{0}}
    (r : Z ⟶ (DegPre.BF D.toPre F).left) (z : Z) {J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι}
    (hJ : Good D.toPre.P.L z J) :
    sval ((ζ • s).s α) r z J = gs r z ⊤ (gF D.toPre F ζ) * sval (s.s α) r z J := by
  unfold sval
  refine (congrArg (gs r z _) (ReciprocityTheory.ChartRestriction.G.DVR.smul_f ζ s α _)).trans ?_
  refine (gs_mul _ _ _ (hJ.mem _ r) _ _).trans ?_
  congr 1
  exact gs_res r z le_top (hJ.mem _ r) _

private lemma gs_aF_gF_eq_gs_gF (oa : D.toPre.OAct O) (a : O) (ζ : F) (y : (DegPre.BF D.toPre F).left) :
    gs (𝟙 _ ≫ (aF D F oa a).left) y ⊤ (gF D.toPre F ζ) = gs (𝟙 _) y ⊤ (gF D.toPre F ζ) := by
  have k1 : ∀ f : (DegPre.BF D.toPre F).left ⟶ (DegPre.BF D.toPre F).left,
      gs f y ⊤ (gF D.toPre F ζ) = gs (f ≫ (fst (TF (R := V) F) D.toPre.P.A).left) y ⊤
        ((Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom ζ) :=
    fun f => gs_pull f _ y ⊤ (by simp) _
  rw [k1, k1, Category.assoc, aF_fst]

theorem pull_smul (oa : D.toPre.OAct O) (a : O) (k N : ℕ) (ζ : F) {s : Fam D.toPre F k}
    {t : Fam D.toPre F (k * N)} (h : PullAl D F oa a k N s t) : PullAl D F oa a k N (ζ • s) (ζ • t) := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun χ => ?_, fun β hβ j => ?_⟩
  · obtain ⟨u, hu, hc, hr⟩ := h1 χ
    refine ⟨u, hu, hc, (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).2 ?_⟩
    intro y J hJ
    have e1 := (secRel_iff D.toPre.P.isLB _ _ _ _ _ _ _ _ _ u).1 hr _ (𝟙 _) y J hJ
    rw [sval_smul_eq_gs_gF_mul_of_good _ _ _ _ _ hJ, sval_smul_eq_gs_gF_mul_of_good _ _ _ _ _ hJ, e1, gs_aF_gF_eq_gs_gF, _root_.mul_assoc]
  · rw [ReciprocityTheory.ChartRestriction.G.DVR.smul_f, h2 β hβ j, mul_zero]

theorem main : GlobalFnsSt → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V)) (F : Type) [Field F] [Algebra (FractionRing V) F] (O : Type) [Ring O] [StarRing O] [Module O D.toPre.X] (oa : D.toPre.OAct O) (a : O) (k N n : ℕ), 0 < n → ∀ (c : Fin n → F) (s : Fin n → Fam D.toPre F k) (s' : Fin n → Fam D.toPre F (k * N)), (∀ l, PullAl D F oa a k N (s l) (s' l)) → PullAl D F oa a k N (∑ l, c l • s l) (∑ l, c l • s' l) := by
  intro hG V _ _ _ D F _ _ O _ _ _ oa a k N n hn c s s' hs
  have key : ∀ S : Finset (Fin n), S.Nonempty →
      PullAl D F oa a k N (∑ l ∈ S, c l • s l) (∑ l ∈ S, c l • s' l) := by
    intro S hS
    induction hS using Finset.Nonempty.cons_induction with
    | singleton l =>
      rw [Finset.sum_singleton, Finset.sum_singleton]
      exact pull_smul oa a k N (c l) (hs l)
    | cons l S hl hS ih =>
      rw [Finset.sum_cons, Finset.sum_cons]
      exact pull_add hG oa a k N (pull_smul oa a k N (c l) (hs l)) ih
  exact key Finset.univ ⟨⟨0, hn⟩, Finset.mem_univ _⟩

end GlobalTheory.PullComb
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
section
namespace GlobalTheory

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

private theorem relDim_eq_of_smoothOfRelativeDimension_grp {X Y : Scheme.{0}} (f : X ⟶ Y) (n m : ℕ) (x : X)
    (hn : SmoothOfRelativeDimension n f) (hm : SmoothOfRelativeDimension m f) : n = m := by
  obtain ⟨U, hU, V, hV, hx, e, h⟩ := hn.exists_isStandardSmoothOfRelativeDimension x
  obtain ⟨s, hs, hQ⟩ :=
    HasRingHomProperty.appLE (@SmoothOfRelativeDimension m) f hm ⟨U, hU⟩ ⟨V, hV⟩ e
  have hp := (hV.primeIdealOf ⟨x, hx⟩).isPrime
  obtain ⟨t, ht, htp⟩ : ∃ t ∈ s, t ∉ (hV.primeIdealOf ⟨x, hx⟩).asIdeal := by
    by_contra! H
    exact hp.ne_top (eq_top_iff.2 (hs ▸ Ideal.span_le.2 H))
  have : Nontrivial (Localization.Away t) := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    have h0 : algebraMap Γ(X, V) (Localization.Away t) 1 = 0 := Subsingleton.elim _ _
    rw [IsLocalization.map_eq_zero_iff (Submonoid.powers t)] at h0
    obtain ⟨⟨c, k, rfl⟩, hc⟩ := h0
    have hc' : t ^ k = 0 := by simpa using hc
    exact htp (hp.mem_of_pow_mem k (by rw [hc']; exact Ideal.zero_mem _))
  have hn' := (RingHom.isStandardSmoothOfRelativeDimension_stableUnderCompositionWithLocalizationAway n).2
    (Localization.Away t) t _ h
  have hm' := hQ t ht
  let := ((algebraMap Γ(X, V) (Localization.Away t)).comp (f.appLE U V e).hom).toAlgebra
  have : Algebra.IsStandardSmoothOfRelativeDimension n Γ(Y, U) (Localization.Away t) := hn'
  have a1 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) n
  have : Algebra.IsStandardSmoothOfRelativeDimension m Γ(Y, U) (Localization.Away t) := hm'
  have a2 := Algebra.IsStandardSmoothOfRelativeDimension.rank_kaehlerDifferential
    (R := Γ(Y, U)) (S := Localization.Away t) m
  exact_mod_cast a1.symm.trans a2

private theorem exists_limit_fan_smooth_relDim_mul {S : Scheme.{0}} (A : Over S) (g : ℕ) (hA : SmoothOfRelativeDimension g A.hom) :
    ∀ k : ℕ, ∃ c : Fan (fun _ : Fin k => A), Nonempty (IsLimit c) ∧
      SmoothOfRelativeDimension (k * g) c.pt.hom := by
  intro k
  induction k with
  | zero =>
    refine ⟨Fan.mk (𝟙_ (Over S)) (fun i => Fin.elim0 i), ⟨Fan.IsLimit.mk _
      (fun s => CartesianMonoidalCategory.toUnit s.pt) (fun _ i => Fin.elim0 i)
      (fun _ _ _ => CartesianMonoidalCategory.toUnit_unique _ _)⟩, ?_⟩
    rw [zero_mul]
    show SmoothOfRelativeDimension 0 (𝟙 S)
    infer_instance
  | succ k ih =>
    obtain ⟨c, ⟨hc⟩, hsm⟩ := ih
    refine ⟨extendFan (f := fun _ : Fin (k + 1) => A) c
      (BinaryFan.mk (CartesianMonoidalCategory.fst A c.pt) (CartesianMonoidalCategory.snd A c.pt)),
      ⟨extendFanIsLimit (fun _ : Fin (k + 1) => A) hc
        (CartesianMonoidalCategory.tensorProductIsBinaryProduct A c.pt)⟩, ?_⟩
    have : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension (k * g)) :=
      smoothOfRelativeDimension_isStableUnderBaseChange (k * g)
    have h1 : SmoothOfRelativeDimension (k * g) (pullback.fst A.hom c.pt.hom) :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback
        (IsPullback.of_hasPullback A.hom c.pt.hom).flip hsm
    have h2 := smoothOfRelativeDimension_comp (n := k * g) (m := g) (pullback.fst A.hom c.pt.hom) A.hom
    rw [Nat.succ_mul]
    exact h2

theorem rank_and_g_of_isPowDeg : ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R)
    (pD : IsPowDeg D' D j), D'.rank = j * D.rank ∧ D'.P.g = j * D.P.g := by
  intro R _ _ j D D' pD
  rcases pD with ⟨pw, w, wg, wr, xe, cpr, wpsi⟩
  refine ⟨?_, ?_⟩
  · have e : D'.X ≃ₗ[ℤ] (Fin j → D.X) := xe.toIntLinearEquiv
    unfold DegPre.rank
    rw [e.finrank_eq, Module.finrank_pi_fintype]
    simp
  · rcases pw with ⟨pr, hom, lim⟩
    obtain ⟨c, ⟨hc⟩, hsm⟩ := exists_limit_fan_smooth_relDim_mul D.P.A D.P.g D.P.5 j
    let e := IsLimit.conePointUniqueUpToIso lim hc
    have hw : e.hom.left ≫ c.pt.hom = D'.P.A.hom := Over.w e.hom
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    have h3 := smoothOfRelativeDimension_comp (n := 0) (m := j * D.P.g) e.hom.left c.pt.hom
    rw [hw, zero_add] at h3
    let := D'.P.2
    have p : (𝟙_ (Over (Spec (CommRingCat.of R)))).left := (inferInstance : Nonempty (PrimeSpectrum R)).some
    exact relDim_eq_of_smoothOfRelativeDimension_grp D'.P.A.hom _ _ ((η[D'.P.A]).left p) D'.P.5 h3

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RatioTrans
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.CubBox

open ReciprocityTheory.ChartRestriction.G.Geo.Tor TopologicalSpace

section Box

variable {X X' Y Y₀ : Scheme.{0}} {M : LB X} {M' : LB X'} {j : ℕ} {pr : Fin j → (X' ⟶ X)}

theorem bw_trans {Z : Scheme.{0}} (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) (ψ : Z ⟶ X') (z : Z)
    {jN jN' : Fin j → M.ι} {k k' : M'.ι} (h₁ : ψ z ∈ LB.wchart M pr jN) (h₁' : ψ z ∈ LB.wchart M pr jN')
    (h₂ : ψ z ∈ M'.U k) (h₂' : ψ z ∈ M'.U k') :
    bw w ψ z jN k = (∏ i, gm (ψ ≫ pr i) z (M.U (jN i) ⊓ M.U (jN' i)) (M.g (jN i) (jN' i))) *
      (gm ψ z (M'.U k ⊓ M'.U k') (M'.g k k'))⁻¹ * bw w ψ z jN' k' := by
  have hm : ψ z ∈ LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k') := ⟨⟨h₁, h₂⟩, h₁', h₂'⟩
  have e := congrArg (gm ψ z (LB.wchart M pr jN ⊓ M'.U k ⊓ (LB.wchart M pr jN' ⊓ M'.U k'))) (hw (jN, k) (jN', k'))
  have d := gm_div M' (LB.LinComb M pr (fun _ => 1)) ψ z (jN, k) (jN', k') hm
  have l := gm_linComb M pr (fun _ => 1) ψ z jN jN' h₁ h₁'
  simp only [zpow_one] at l
  refine (gm_res ψ z _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (d.trans (congrArg₂ (· * ·) l rfl)) (gm_res ψ z _ hm _))))

variable {K : Type} [Fintype K]

def ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ}
    (ρ : Fin j → (Y ⟶ Y₀)) (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε))
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (jN : K → Fin j → M.ι) (jM : K → M'.ι) : (Z.presheaf.stalk z)ˣ :=
  (∏ a, bw w (r ≫ φ' a) z (jN a) (jM a) ^ ε a) * gm r z (LB.wchart M' φ' jM) (t'.s jM) *
    (∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)))⁻¹

theorem chart_le {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a) (jN : K → Fin j → M.ι) (i : Fin j) :
    LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ≤ ρ i ⁻¹ᵁ LB.wchart M φ (fun a => jN a i) := fun y hy =>
  Set.mem_iInter.2 fun a => (congrArg (fun g : Y ⟶ X => g y ∈ M.U (jN a i)) (hψ i a)).mp
    (Set.mem_iInter.1 (Set.mem_iInter.1 hy a) i)

theorem ratio_trans (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) (hw : w.IsGen) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) {jN jN' : K → Fin j → M.ι} {jM jM' : K → M'.ι}
    (h : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)
    (h' : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN' ⊓ LB.wchart M' φ' jM') :
    ratio w ρ t' t r z jN jM = ratio w ρ t' t r z jN' jM' := by
  have e₁ : ∀ a, bw w (r ≫ φ' a) z (jN a) (jM a) = _ := fun a => bw_trans w hw (r ≫ φ' a) z (jN' := jN' a) (k' := jM' a)
    (Set.mem_iInter.1 h.1 a) (Set.mem_iInter.1 h'.1 a) (Set.mem_iInter.1 h.2 a) (Set.mem_iInter.1 h'.2 a)
  have e₂ := gen_trans ht' r z h.2 h'.2
  have e₃ : ∀ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => jN a i)) (t.s (fun a => jN a i)) = _ := fun i =>
    gen_trans ht (r ≫ ρ i) z (j' := fun a => jN' a i) (chart_le hψ jN i h.1) (chart_le hψ jN' i h'.1)
  have e₄ : ∏ i, trF (L := M) φ ε (r ≫ ρ i) z (fun a => jN a i) (fun a => jN' a i) =
      ∏ a, (∏ i, gm ((r ≫ φ' a) ≫ pr i) z (M.U (jN a i) ⊓ M.U (jN' a i)) (M.g (jN a i) (jN' a i))) ^ ε a := by
    unfold trF
    rw [Finset.prod_comm]
    refine Finset.prod_congr rfl fun a _ => ?_
    rw [← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Category.assoc, Category.assoc, hψ]
  unfold ratio
  rw [Finset.prod_congr rfl fun a _ => congrArg (· ^ ε a) (e₁ a), e₂, Finset.prod_congr rfl fun i _ => e₃ i,
    Finset.prod_mul_distrib, e₄]
  simp only [mul_zpow, inv_zpow, Finset.prod_mul_distrib, Finset.prod_inv_distrib, trF]
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem exists_ratio (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1))) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)} (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    (t' : LB.Gen (LB.LinComb M' φ' ε)) (t : LB.Gen (LB.LinComb M φ ε)) (jN : K → Fin j → M.ι) (jM : K → M'.ι) :
    ∃ u : Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ,
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z),
        r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM →
        gm r z _ u = ratio w ρ t' t r z jN jM := by
  refine ⟨@id (Γ(Y, LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' jN ⊓ LB.wchart M' φ' jM)ˣ)
      ((LB.linCombIso w φ' ε).s (jN, jM)) * res inf_le_right (t'.s jM) *
      (∏ i, res (inf_le_left.trans (chart_le hψ jN i)) (pullU (ρ i) _ (t.s (fun a => jN a i))))⁻¹,
    fun Z r z hz => ?_⟩
  refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_linCombIso w φ' ε r z jN jM hz) (gm_res r z _ hz _))) ((map_inv _ _).trans (congrArg (·⁻¹)
      ((map_prod _ _ _).trans (Finset.prod_congr rfl fun i _ => ?_)))))
  exact (gm_res r z _ hz _).trans (gm_pull r (ρ i) z _ (chart_le hψ jN i hz.1) _)

theorem box_unique {S₀ : Scheme.{0}} (hM : M.IsLB) (hM' : M'.IsLB) (w : LB.Iso M' (LB.LinComb M pr (fun _ => 1)))
    (hw : w.IsGen) {φ' : K → (Y ⟶ X')} {φ : K → (Y₀ ⟶ X)} {ε : K → ℤ} {ρ : Fin j → (Y ⟶ Y₀)}
    (hψ : ∀ i a, φ' a ≫ pr i = ρ i ≫ φ a)
    {t' : LB.Gen (LB.LinComb M' φ' ε)} (ht' : t'.IsGen) {t : LB.Gen (LB.LinComb M φ ε)} (ht : t.IsGen)
    (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _) (hp : Function.Surjective p.appTop.hom)
    (h : ∀ y J J', Good M y J → Good M' y J' →
      (∏ a, bw w (e ≫ φ' a) y (fun i => J ((e ≫ φ' a) ≫ pr i)) (J' (e ≫ φ' a)) ^ ε a) * val t' e y J' =
        ∏ i, val t (e ≫ ρ i) y J)
    (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J') (hJ : Good M z J) (hJ' : Good M' z J') :
    (∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' =
      ∏ i, val t (r ≫ ρ i) z J := by
  choose u hu using fun q : (K → Fin j → M.ι) × (K → M'.ι) => exists_ratio w hψ t' t q.1 q.2
  obtain ⟨s, hs⟩ := glue_unit (⊤ : Y.Opens)
    (fun q : (K → Fin j → M.ι) × (K → M'.ι) =>
      LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' q.1 ⊓ LB.wchart M' φ' q.2) (fun _ => le_top)
    (fun y _ => by
      choose a ha using fun k i => exists_chart hM (pr i (φ' k y))
      choose b hb using fun k => exists_chart hM' (φ' k y)
      exact Opens.mem_iSup.2 ⟨(a, b), Set.mem_iInter.2 fun k => Set.mem_iInter.2 (ha k), Set.mem_iInter.2 hb⟩) u
    (fun q q' y hy => (hu q _ (𝟙 Y) y hy.1).trans ((ratio_trans w hw hψ ht' ht (𝟙 Y) y hy.1 hy.2).trans
      (hu q' _ (𝟙 Y) y hy.2).symm))
  obtain ⟨a, ha⟩ := hp s.val
  have key : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (J J'), Good M z J → Good M' z J' →
      ((∏ a, bw w (r ≫ φ' a) z (fun i => J ((r ≫ φ' a) ≫ pr i)) (J' (r ≫ φ' a)) ^ ε a) * val t' r z J' *
        (∏ i, val t (r ≫ ρ i) z J)⁻¹).val = gs (r ≫ p) z ⊤ a := by
    intro Z r z J J' hJ hJ'
    have hm : r z ∈ LB.wchart (LB.LinComb M pr (fun _ => 1)) φ' (fun a i => J ((r ≫ φ' a) ≫ pr i)) ⊓
        LB.wchart M' φ' (fun a => J' (r ≫ φ' a)) :=
      ⟨Set.mem_iInter.2 fun a => Set.mem_iInter.2 fun i => hJ ((r ≫ φ' a) ≫ pr i), hJ'.mem _ r⟩
    have v : ∏ i, val t (r ≫ ρ i) z J = ∏ i, gm (r ≫ ρ i) z (LB.wchart M φ (fun a => J ((r ≫ φ' a) ≫ pr i)))
        (t.s (fun a => J ((r ≫ φ' a) ≫ pr i))) := Finset.prod_congr rfl fun i _ =>
      val_of t _ z J _ (fun a => by rw [Category.assoc, Category.assoc, hψ])
    rw [v]
    have w₁ := (hu (fun a i => J ((r ≫ φ' a) ≫ pr i), fun a => J' (r ≫ φ' a)) Z r z hm).symm.trans
      ((congrArg (gm r z _) (hs _).symm).trans (gm_res r z le_top hm s))
    exact (congrArg Units.val w₁).trans ((gs_unit r z ⊤ trivial _).symm.trans
      ((congrArg (gs r z ⊤) ha.symm).trans (gs_pull r p z ⊤ trivial a)))
  have a1 : a = 1 := fn_ext fun y _ => by
    choose I hI using fun χ : S₀ ⟶ X => exists_chart hM (χ y)
    choose I' hI' using fun χ : S₀ ⟶ X' => exists_chart hM' (χ y)
    have := key _ e y I I' hI hI'
    rw [h y I I' hI hI', mul_inv_cancel, he] at this
    rw [← this, gs_eq _ y ⊤ trivial, map_one, map_one, Units.val_one]
  have := key Z r z J J' hJ hJ'
  rw [a1, gs_eq _ z ⊤ trivial, map_one, map_one] at this
  exact mul_inv_eq_one.1 (Units.ext this)

end Box

theorem cubV_box : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] (j : ℕ) (D D' : DegPre R) (pD : IsPowDeg D' D j) (T : Over (Spec (CommRingCat.of R))) (z : T.left) (J J'), Geo.Tor.Good D.P.L z J → Geo.Tor.Good D'.P.L z J' → ∀ x x' y : T ⟶ D'.P.A, (let om := fun p : T ⟶ D'.P.A => bw pD.w p.left z (fun i => J (p.left ≫ (pD.pw.pr i).left)) (J' p.left); Geo.Tor.cubV D'.cub z J' x x' y * (om (x * x' * y) * (om (x * x'))⁻¹ * (om (x * y))⁻¹ * (om (x' * y))⁻¹ * om x * om x' * om y * (om 1)⁻¹) = ∏ i, Geo.Tor.cubV D.cub z J (x ≫ pD.pw.pr i) (x' ≫ pD.pw.pr i) (y ≫ pD.pw.pr i)) := by
  intro hG R _ _ j D D' pD T z J J' hJ hJ' x x' y om
  let ρ : Fin j → ((G3 D'.P.A).left ⟶ (G3 D.P.A).left) := fun i => (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i).left
  have hψ : ∀ i a, thφ D'.P.A (x3 D'.P.A) a ≫ (pD.pw.pr i).left = ρ i ≫ thφ D.P.A (x3 D.P.A) a := fun i a =>
    letI := pD.pw.hom i
    (CubeMap.ofHom (pD.pw.pr i)).psum_comm a.down
  have hρ : ∀ {T : Over (Spec (CommRingCat.of R))} (a b c : T ⟶ D'.P.A) i, (lift a (lift b c)).left ≫ ρ i =
      (lift (a ≫ pD.pw.pr i) (lift (b ≫ pD.pw.pr i) (c ≫ pD.pw.pr i))).left := fun a b c i => by
    show (lift a (lift b c) ≫ (pD.pw.pr i ⊗ₘ pD.pw.pr i ⊗ₘ pD.pw.pr i)).left = _
    rw [lift_map, lift_map]
  let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 D'.P.A := lift 1 (lift 1 1)
  have sj : Function.Surjective
      ((snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom).appTop.hom :=
    surj_comp (surj_snd hG D'.P.isAb _) (surj_comp (surj_snd hG D'.P.isAb _) (hG _ _ D'.P.isAb).2)
  have he : e.left ≫ (snd D'.P.A (D'.P.A ⊗ D'.P.A)).left ≫ (snd D'.P.A D'.P.A).left ≫ D'.P.A.hom = 𝟙 _ := by
    rw [Over.w, Over.w]; exact Over.w e
  have key := box_unique (pr := fun i => (pD.pw.pr i).left) D.P.isLB D'.P.isLB pD.w pD.w_gen (ε := thε) hψ
    D'.cub.isGen D.cub.isGen _ e.left he sj (fun s I I' hI hI' => by
      have C' : IsCub (cubV D'.cub s I') := isCub_cubV D'.cub hI'
      have C : IsCub (cubV D.cub (T := 𝟙_ (Over (Spec (CommRingCat.of R)))) s I) := isCub_cubV D.cub hI
      have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) 1 1
        (fun q => bw pD.w q s (fun i => I (q ≫ (pD.pw.pr i).left)) (I' q))
      rw [_root_.mul_one, _root_.mul_one] at p
      refine (congrArg₂ (· * ·) p (C'.face 1 1)).trans (Eq.trans (by simp) (Finset.prod_eq_one fun i _ => ?_).symm)
      have := pD.pw.hom i
      have o : (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ D'.P.A) ≫ pD.pw.pr i = 1 := by simp [Hom.one_def]
      rw [show e.left ≫ ρ i = _ from hρ 1 1 1 i, o]
      exact C.face 1 1) _ (lift x (lift x' y)).left z J J' hJ hJ'
  have p := prod_cub x x' y (fun q => bw pD.w q z (fun i => J (q ≫ (pD.pw.pr i).left)) (J' q))
  refine (mul_comm _ _).trans ((congrArg₂ (· * ·) p rfl).symm.trans (key.trans (Finset.prod_congr rfl fun i _ => ?_)))
  rw [hρ]; rfl

end GlobalTheory.CubBox
end
end

