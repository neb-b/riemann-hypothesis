module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Definitions.Degenerations.RigGen
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0111
public import Development.AbelianVarietyTheory.Definitions.Degenerations.LocTheta
public import Development.AbelianVarietyTheory.Statements.SemistableTorsion.UTorsSt
public import Development.AbelianVarietyTheory.PublishedTheorems.SemistableReduction₂.SemistableReductionSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0073
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemRangeCompIffOfIsClosedImmersion
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0109
public import Development.AbelianVarietyTheory.Definitions.Degenerations.BaseFacts
public import Development.AbelianVarietyTheory.Definitions.Degenerations.IsAffineSplitTorusLeft
public import Development.AbelianVarietyTheory.Definitions.Degenerations.CompanionTheory
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.HomGenericPoint
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0114
public import Development.AbelianVarietyTheory.Definitions.Degenerations.PullChartIsLB
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0106
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LineBundleSpreadsOutFromGenericFibreProper
section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

noncomputable section

namespace GlobalTheory.GenSpread

set_option backward.isDefEq.respectTransparency false

theorem isLB_of_gm {Y : Scheme.{0}} (L : LB Y) (hc : ∀ y : Y, ∃ i, y ∈ L.U i)
    (h : ∀ (y : Y) i j k, y ∈ L.U i → y ∈ L.U j → y ∈ L.U k →
      gm (𝟙 Y) y _ (L.g i j) * gm (𝟙 Y) y _ (L.g j k) = gm (𝟙 Y) y _ (L.g i k)) : L.IsLB := {
  cover := top_le_iff.1 fun y _ => Opens.mem_iSup.2 (hc y)
  g_self i := unit_ext fun y hy => by
    refine (gm_res (𝟙 Y) y _ hy _).trans ?_
    rw [map_one]
    exact mul_eq_left.1 (h y i i i hy hy hy)
  cocycle i j k := unit_ext fun y hy =>
    ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res (𝟙 Y) y _ hy _) (gm_res (𝟙 Y) y _ hy _))).trans
      ((h y i j k hy.1.1 hy.1.2 hy.2).trans (gm_res (𝟙 Y) y _ hy _).symm) }

section Limit

variable {I : Type} [SmallCategory I] [IsCofiltered I]
  (D : I ⥤ Scheme.{0}) {X : Scheme.{0}} (π : ∀ i, X ⟶ D.obj i)
  (w : ∀ {i j} (f : i ⟶ j), π i ≫ D.map f = π j) (hc : IsLimit (schemeConeOfFamily D π w))
  [∀ {i j} (f : i ⟶ j), IsAffineHom (D.map f)]


include hc in
theorem exists_isLB_of_isLimit {i : I} [CompactSpace (D.obj i)] (M : LB (D.obj i)) [Finite M.ι]
    (hM : ∀ a b c, IsCompact ((M.U a ⊓ M.U b ⊓ M.U c : (D.obj i).Opens) : Set (D.obj i)))
    (hcov : ∀ y : X, ∃ a, π i y ∈ M.U a)
    (h : ∀ (y : X) a b c, π i y ∈ M.U a → π i y ∈ M.U b → π i y ∈ M.U c →
      gm (π i) y _ (M.g a b) * gm (π i) y _ (M.g b c) = gm (π i) y _ (M.g a c)) :
    ∃ (j : I) (f : j ⟶ i), (M.pull (D.map f)).IsLB := by
  have l₁ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U b := fun a b c => inf_le_left
  have l₂ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U b ⊓ M.U c := fun a b c _ hy => ⟨hy.1.2, hy.2⟩
  have l₃ : ∀ a b c, M.U a ⊓ M.U b ⊓ M.U c ≤ M.U a ⊓ M.U c := fun a b c _ hy => ⟨hy.1.1, hy.2⟩
  have val : ∀ {Z : Scheme.{0}} (r : Z ⟶ D.obj i) (z : Z) a b c, r z ∈ M.U a ⊓ M.U b ⊓ M.U c →
      gm r z _ (res (l₁ a b c) (M.g a b) * res (l₂ a b c) (M.g b c)) =
        gm r z _ (M.g a b) * gm r z _ (M.g b c) := fun r z a b c hz =>
    (map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_res r z _ hz _) (gm_res r z _ hz _))
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : M.ι × M.ι × M.ι) k g =>
      pullU (D.map g) _ (res (l₁ p.1 p.2.1 p.2.2) (M.g _ _) * res (l₂ p.1 p.2.1 p.2.2) (M.g _ _)) =
        pullU (D.map g) _ (res (l₃ p.1 p.2.1 p.2.2) (M.g _ _)))
    (by
      intro p k g k' g' h
      rw [D.map_comp]
      exact congrArg (pullU (D.map g') _) h)
    (by
      rintro ⟨a, b, c⟩
      exact exists_pullU_eq D π w hc (hM a b c) _ _ fun y hy =>
        (val (π i) y a b c hy).trans ((h y a b c hy.1.1 hy.1.2 hy.2).trans (gm_res _ y _ hy _).symm))
  obtain ⟨j', f', hj'⟩ := exists_map_preimage_le_map_preimage D _ hc (U := ⊤) (V := ⨆ a, M.U a)
    isCompact_univ (fun y _ => Opens.mem_iSup.2 (hcov y))
  obtain ⟨k, g, g', hg⟩ := IsCofiltered.cospan f f'
  refine ⟨k, g ≫ f, isLB_of_gm _ (fun y => ?_) fun y a b c ha hb hc' => ?_⟩
  · obtain ⟨a, ha⟩ := Opens.mem_iSup.1 (hj' (show D.map g' y ∈ D.map f' ⁻¹ᵁ ⊤ from trivial))
    refine ⟨fun _ => a, mem_pull.2 ?_⟩
    rw [hg, D.map_comp]
    exact ha
  · rw [gm_pull_g M _ (𝟙 _) y a b ha hb, gm_pull_g M _ (𝟙 _) y b c hb hc', gm_pull_g M _ (𝟙 _) y a c ha hc',
      Category.id_comp]
    have hy : D.map (g ≫ f) y ∈ M.U (a PUnit.unit) ⊓ M.U (b PUnit.unit) ⊓ M.U (c PUnit.unit) :=
      ⟨⟨mem_pull.1 ha, mem_pull.1 hb⟩, mem_pull.1 hc'⟩
    rw [D.map_comp] at hy ⊢
    have e := congrArg (gm (D.map g) y _) (hj (a PUnit.unit, b PUnit.unit, c PUnit.unit))
    exact (val _ y _ _ _ hy).symm.trans ((gm_pull (D.map g) (D.map f) y _ hy _).symm.trans (e.trans
      ((gm_pull (D.map g) (D.map f) y _ hy _).trans (gm_res _ y _ hy _))))


include hc in
theorem exists_lb_of_isLimit {i : I} [CompactSpace (D.obj i)] [CompactSpace X]
    (hsep : ∀ U V : (D.obj i).Opens, IsAffineOpen U → IsAffineOpen V → IsAffineOpen (U ⊓ V))
    (hπ : Topology.IsInducing (π i)) (L₀ : LB X) (hL : L₀.IsLB) :
    ∃ (j : I) (L : LB (D.obj j)), L.IsLB ∧ LBIso L₀ (L.pull (π j)) := by
  have loc : ∀ x : X, ∃ (V : (D.obj i).Opens) (c : L₀.ι),
      IsAffineOpen V ∧ π i x ∈ V ∧ π i ⁻¹ᵁ V ≤ L₀.U c := by
    intro x
    obtain ⟨c, hc⟩ := exists_chart hL x
    obtain ⟨W, hW, hW'⟩ := hπ.isOpen_iff.1 (L₀.U c).isOpen
    have hx : π i x ∈ W := hW'.ge hc
    obtain ⟨_, ⟨V, hV, rfl⟩, hx, hle⟩ := (D.obj i).isBasis_affineOpens.exists_subset_of_mem_open hx hW
    exact ⟨V, c, hV, hx, fun y hy => hW'.le (hle hy)⟩
  choose V c hV hx hle using loc
  obtain ⟨σ, hσ⟩ := CompactSpace.elim_nhds_subcover (fun x => ((π i ⁻¹ᵁ V x : X.Opens) : Set X))
    (fun x => (π i ⁻¹ᵁ V x).isOpen.mem_nhds (hx x))
  have cov : ∀ x : X, ∃ a : σ, π i x ∈ V a := fun x => by
    obtain ⟨a, ha, hx⟩ := Set.mem_iUnion₂.1 (hσ.ge (Set.mem_univ x))
    exact ⟨⟨a, ha⟩, hx⟩
  have le : ∀ {j k : I} (f : j ⟶ i) (g : k ⟶ j) (U : (D.obj i).Opens),
      D.map (g ≫ f) ⁻¹ᵁ U ≤ D.map g ⁻¹ᵁ (D.map f ⁻¹ᵁ U) := fun f g U => by
    rw [D.map_comp, Scheme.Hom.comp_preimage]
  have l : ∀ a b, π i ⁻¹ᵁ (V a ⊓ V b) ≤ L₀.U (c a) ⊓ L₀.U (c b) := fun a b _ hy => ⟨hle a hy.1, hle b hy.2⟩
  obtain ⟨j, f, hj⟩ := exists_common_refinement (i := i)
    (fun (p : σ × σ) j f => ∃ t : Γ(D.obj j, D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2))ˣ, ∀ y : X,
      y ∈ π i ⁻¹ᵁ (V p.1 ⊓ V p.2) →
      gm (π j) y (D.map f ⁻¹ᵁ (V p.1 ⊓ V p.2)) t = gm (𝟙 X) y _ (res (l p.1 p.2) (L₀.g _ _)))
    (by
      rintro p j f k g ⟨t, ht⟩
      refine ⟨res (le f g _) (pullU (D.map g) _ t), fun y hy => ?_⟩
      have hy' := cone_preimage_le D π w (g ≫ f) _ hy
      refine (gm_res_pullU (π k) (D.map g) y (le f g (V p.1 ⊓ V p.2)) hy' t).trans ?_
      rw [w g]
      exact ht y hy)
    (fun p => exists_unit_π_eq D π w hc (hsep _ _ (hV _) (hV _)) _)
  choose t ht using hj
  let M : LB (D.obj j) := ⟨σ, fun a => D.map f ⁻¹ᵁ V a, fun a b => t (a, b)⟩
  have mem : ∀ (y : X) (a : σ), π j y ∈ M.U a ↔ π i y ∈ V a := fun y a => by
    rw [← w f]; rfl
  have val : ∀ (y : X) (a b : σ), π j y ∈ M.U a → π j y ∈ M.U b →
      gm (π j) y _ (M.g a b) = gm (𝟙 X) y _ (L₀.g (c a) (c b)) := fun y a b ha hb =>
    have hy : y ∈ π i ⁻¹ᵁ (V a ⊓ V b) := ⟨(mem y a).1 ha, (mem y b).1 hb⟩
    (ht (a, b) y hy).trans (gm_res _ y _ hy _)
  have : CompactSpace (D.obj j) := QuasiCompact.compactSpace_of_compactSpace (D.map f)
  have : Finite M.ι := inferInstanceAs (Finite σ)
  obtain ⟨k, g, hk⟩ := exists_isLB_of_isLimit D π w hc M
    (fun a b e => ((hsep _ _ (hsep _ _ (hV a) (hV b)) (hV e)).preimage (D.map f)).isCompact)
    (fun y => (cov y).imp fun a ha => (mem y a).2 ha)
    (fun y a b e ha hb he => by
      rw [val y a b ha hb, val y b e hb he, val y a e ha he]
      exact gm_cocycle hL (𝟙 X) y (hle a ((mem y a).1 ha)) (hle b ((mem y b).1 hb)) (hle e ((mem y e).1 he)))
  have mem' : ∀ (y : X) J, y ∈ ((M.pull (D.map g)).pull (π k)).U J → π j y ∈ M.U (J PUnit.unit PUnit.unit) :=
    fun y J hy => by
      rw [← w g]
      have hy' : π k y ∈ (M.pull (D.map g)).U (J PUnit.unit) := mem_pull.1 hy
      exact (mem_pull (F := D.map g)).1 hy'
  refine ⟨k, _, hk, (lbIso_of_chartPull (B' := (M.pull (D.map g)).pull (π k))
    ⟨fun J => c (J PUnit.unit PUnit.unit).1, fun J y hy => hle _ ((mem y _).1 (mem' y J hy)),
      fun y J J' hJ hJ' => ?_⟩ hL).symm⟩
  rw [gm_pull_g _ _ (𝟙 _) y J J' hJ hJ', Category.id_comp,
    gm_pull_g M _ (π k) y _ _ (mem_pull.1 hJ) (mem_pull.1 hJ'), w g]
  exact val y _ _ (mem' y J hJ) (mem' y J' hJ')

end Limit

theorem exists_lb {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    {X X₀ : Scheme.{0}} (f : X ⟶ Sp R) [QuasiCompact f] [IsSeparated f] {φ : X₀ ⟶ X} {f₀ : X₀ ⟶ Sp K}
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) {L₀ : LB X₀} (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') := by
  obtain ⟨p₁, h₁⟩ := exists_isPullback_stalk h
  obtain ⟨hc⟩ := StalkLimit.nonempty_isLimit h₁
  obtain ⟨V₀⟩ : Nonempty (StalkLimit.AffNhd (genericPoint (Sp R))) := IsCofiltered.nonempty
  have : IsAffine V₀.1.toScheme := V₀.2.2
  have : CompactSpace ((StalkLimit.diagram _ f).obj V₀) :=
    QuasiCompact.compactSpace_of_compactSpace (pullback.snd f V₀.1.ι)
  have : QuasiCompact f₀ := MorphismProperty.of_isPullback (P := @QuasiCompact) h inferInstance
  have : CompactSpace X₀ := QuasiCompact.compactSpace_of_compactSpace f₀
  have : IsPreimmersion φ := MorphismProperty.of_isPullback (P := @IsPreimmersion) h₁.flip inferInstance
  have hs : (pullback f V₀.1.ι).IsSeparated :=
    ⟨by rw [← terminal.comp_from (pullback.snd f V₀.1.ι)]; infer_instance⟩
  have : ((StalkLimit.diagram _ f).obj V₀).IsSeparated := hs
  have hi : Topology.IsInducing ((StalkLimit.cone h₁).π.app V₀) := by
    refine Topology.IsInducing.of_comp (g := pullback.fst f V₀.1.ι) (Scheme.Hom.continuous _)
      (Scheme.Hom.continuous _) ?_
    have := φ.isEmbedding.isInducing
    rw [← StalkLimit.cone_π_fst h₁ V₀] at this
    exact this
  obtain ⟨V, L, hL', H⟩ := exists_lb_of_isLimit (StalkLimit.diagram _ f) (fun V => (StalkLimit.cone h₁).π.app V)
    (fun i => (StalkLimit.cone h₁).w i) hc (i := V₀) (fun U W hU hW => hU.inf hW) hi L₀ hL
  obtain ⟨a, ha, Ha⟩ := exists_forall_mem V.2.1
  refine ⟨a, ha, fun R' _ g hg X' π f' e => ?_⟩
  obtain ⟨l, hl⟩ := exists_lift_open f V.1 e (Ha R' g hg)
  refine ⟨L.pull l, pull_isLB hL' _, fun φ' hφ' => ?_⟩
  have : (StalkLimit.cone h₁).π.app V = φ' ≫ l := by
    rw [← cancel_mono (pullback.fst f V.1.ι), Category.assoc, hl, hφ', StalkLimit.cone_π_fst]
  exact LBIso.trans hL (pull_isLB hL' _) (pull_isLB (pull_isLB hL' _) _) H (lbIso_pull_pull hL' φ' this)

theorem lineBundle_spreads_out (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K]
    [IsFractionRing R K] (X X₀ : Scheme.{0}) (f : X ⟶ Sp R) (f₀ : X₀ ⟶ Sp K) (φ : X₀ ⟶ X)
    (h : IsPullback φ f₀ f (spMap (algebraMap R K))) (_ : Flat f) (_ : IsProper f) (L₀ : LB X₀) (hL : L₀.IsLB) :
    ∃ a : R, a ≠ 0 ∧ ∀ (R' : Type) [CommRing R'] (g : R →+* R'), IsUnit (g a) →
      ∀ (X' : Scheme.{0}) (π : X' ⟶ X) (f' : X' ⟶ Sp R'), π ≫ f = f' ≫ spMap g →
        ∃ L' : LB X', L'.IsLB ∧ ∀ φ' : X₀ ⟶ X', φ' ≫ π = φ → LBIso L₀ (L'.pull φ') :=
  exists_lb f h hL

end GlobalTheory.GenSpread
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SecGenericEqMulTheta
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ZH ReciprocityTheory.ChartRestriction.G.Out Classical
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.ZH.ThetaLine
open GlobalTheory.Points

variable {B : Scheme.{0}} (A : Over B) (L : LB A.left) (a : ℤ)

theorem le_chart {T : Over B} {K : Type} [CommRing K] (q : Sp K ⟶ (T ⊗ A).left) (j : L.ι)
    (h : Set.range (q ≫ (snd T A).left) ⊆ L.U j) : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T).U (fun _ => j) :=
  fun y _ => Set.mem_iInter.2 fun _ => h ⟨y, rfl⟩

theorem valR_pull [GrpObj A] {T T' : Over B} {h : T' ⊗ A ⟶ T ⊗ A} {hh : h ≫ snd T A = snd T' A}
    {s : LB.Sec (LPow A L a T)} {s' : LB.Sec (LPow A L a T')} (H : IsPullSec A L a h hh s s')
    {K : Type} [CommRing K] (q : Sp K ⟶ (T' ⊗ A).left) (j : Fin 1 → L.ι) (hq : ⊤ ≤ q ⁻¹ᵁ (LPow A L a T').U j) :
    valR q _ (s'.f j) = valR (q ≫ h.left) _ (s.f j) := by
  rw [H j, valR_res q _ hq, valR_comp]

theorem valR_of_basis {Ω : Type} [CommRing Ω] (t : Sp Ω ⟶ B) {m : ℕ} (hm : m = 1)
    {b : Fin m → LB.Sec (LPow A L a (Over.mk t))} (hb : IsSecBasis _ b) :
    ∃ b₀ : LB.Sec (LPow A L a (Over.mk t)), ∀ s : LB.Sec (LPow A L a (Over.mk t)), ∃ c : Ω,
      ∀ (K : Type) [CommRing K] (β : Ω →+* K) (q : Sp K ⟶ (Over.mk t ⊗ A).left) (j : Fin 1 → L.ι),
        q ≫ (fst (Over.mk t) A).left = spMap β → ⊤ ≤ q ⁻¹ᵁ (LPow A L a (Over.mk t)).U j →
        valR q _ (s.f j) = β c * valR q _ (b₀.f j) := by
  subst hm
  refine ⟨b 0, fun s => ?_⟩
  obtain ⟨r, hr, -⟩ := hb s
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0), fun K _ β q j hq hj => ?_⟩
  rw [hr j, Fin.sum_univ_one, valR_mul q _ hj, valR_res q _ hj]
  congr 1
  have e := valR_comp q (fst (Over.mk t) A).left ⊤ (r 0)
  refine e.symm.trans ?_
  rw [hq]
  have e2 := valR_specMap (C := K) (A := CommRingCat.of Ω) (CommRingCat.ofHom β)
    ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom.hom (r 0))
  refine Eq.trans ?_ e2
  exact congrArg (valR (spMap β) ⊤) ((Scheme.ΓSpecIso (CommRingCat.of Ω)).hom_inv_id_apply (r 0)).symm

theorem valR_ne_zero [GrpObj A] {T : Over B} {s : LB.Sec (LPow A L a T)} {z : T ⟶ A}
    {τ : LB.Gen (LB.LinComb L (Y := T.left) (K := Fin 1) (fun _ => z.left) (fun _ => a))} {v : Γ(T.left, ⊤)}
    (H : IsValueAt A L a s z τ v) {K : Type} [Field K] (x : Sp K ⟶ T.left) (j : L.ι)
    (hj : Set.range (x ≫ z.left) ⊆ L.U j) (hv : valR x ⊤ v ≠ 0) :
    valR (x ≫ (ptSecT A z).left) _ (s.f fun _ => j) ≠ 0 := by
  have hx : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => z.left) (fun _ => j) :=
    fun y _ => Set.mem_iInter.2 fun _ => hj ⟨y, rfl⟩
  have e := congrArg (valR x _) (H fun _ => j)
  rw [valR_res x _ hx, valR_mul x _ hx, valR_res x _ hx] at e
  rw [valR_comp]
  refine e.trans_ne (mul_ne_zero hv ?_)
  rw [valR_eq x _ hx]
  exact ((τ.s fun _ => j).isUnit.map _).ne_zero

end GlobalTheory.ZH.ThetaLine


open GlobalTheory.Points GlobalTheory.ZH.ThetaLine in
theorem GlobalTheory.ZH.sec_generic_eq_mul_theta : Laws → Laws2 → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (s : LB.Sec (LPow ρ.P.A ρ.P.L 1 (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)))), ∃ c : Ω, ∀ (K : Type) [Field K] (β : Ω →+* K) (q : Sp K ⟶ ((Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ⊗ ρ.P.A).left) (r : Sp K ⟶ (baseOver (Sp S.R) ⊗ ρ.P.A).left) (jP : ρ.P.L.ι), q ≫ (fst (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left = spMap β → r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left = q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left → Set.range (q ≫ (snd (Over.mk (spMap S.R.val.toRingHom) : Over (Sp S.R)) ρ.P.A).left) ⊆ ρ.P.L.U jP → valF q _ (s.f fun _ => jP) = β c * valF r _ (ρ.th₁.f fun _ => jP) := by
  intro _ hL2 o Ω _ _ _ _ S ρ s
  let t₀ : Sp Ω ⟶ Sp S.R := spMap S.R.val.toRingHom
  let h : (Over.mk t₀ : Over (Sp S.R)) ⟶ baseOver (Sp S.R) := Over.homMk t₀ (Category.comp_id t₀)
  obtain ⟨th, hth⟩ : ∃ th, IsPullSec ρ.P.A ρ.P.L 1 (h ▷ ρ.P.A) (whiskerRight_snd h ρ.P.A) ρ.th₁ th :=
    (GlobalTheory.LN.PolFrames.exists_pullSec ρ.P.A ρ.P.L 1 h ρ.th₁).imp fun _ H => H.1
  obtain ⟨b, hb⟩ := GlobalTheory.PowBasis.exists_basis_pow hL2.secTwist ρ.P 1 le_rfl Ω t₀
  obtain ⟨b₀, hb₀⟩ := valR_of_basis ρ.P.A ρ.P.L 1 t₀ (one_pow _) hb
  obtain ⟨c, hc⟩ := hb₀ s
  obtain ⟨d, hd⟩ := hb₀ th
  have hd0 : d ≠ 0 := by
    obtain ⟨a, ha⟩ := S.th_ne
    obtain ⟨j, hj⟩ := exists_chart ρ.P.isLB ((t₀ ≫ (ρ.pt a).left) (IsLocalRing.closedPoint Ω))
    have hj' : Set.range (t₀ ≫ (ρ.pt a).left) ⊆ ρ.P.L.U j := by
      rintro _ ⟨y, rfl⟩
      rw [Subsingleton.elim y (IsLocalRing.closedPoint Ω)]
      exact hj
    have hne := valR_ne_zero ρ.P.A ρ.P.L 1 (ρ.th_val a) t₀ j hj'
      ((valR_specMap (C := Ω) (A := CommRingCat.of S.R) (CommRingCat.ofHom S.R.val.toRingHom) _).trans_ne ha)
    let x : Sp Ω ⟶ ((Over.mk t₀ : Over (Sp S.R)) ⊗ ρ.P.A).left := (ptSecT ρ.P.A (h ≫ ρ.pt a)).left
    have hx1 : x ≫ (fst (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = spMap (RingHom.id Ω) :=
      (congrArg CommaMorphism.left (lift_fst (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))).trans (Spec.map_id _).symm
    have hx2 : x ≫ (snd (Over.mk t₀ : Over (Sp S.R)) ρ.P.A).left = t₀ ≫ (ρ.pt a).left :=
      congrArg CommaMorphism.left (lift_snd (𝟙 (Over.mk t₀ : Over (Sp S.R))) (h ≫ ρ.pt a))
    have hx3 : x ≫ (h ▷ ρ.P.A).left = t₀ ≫ (ptSecT ρ.P.A (ρ.pt a)).left := by
      have : ptSecT ρ.P.A (h ≫ ρ.pt a) ≫ h ▷ ρ.P.A = h ≫ ptSecT ρ.P.A (ρ.pt a) := by
        simp [ptSecT]
      exact congrArg CommaMorphism.left this
    have hxj := le_chart ρ.P.A ρ.P.L 1 x j (hx2 ▸ hj')
    rintro rfl
    apply hne
    rw [← hx3, ← valR_pull ρ.P.A ρ.P.L 1 hth x _ hxj, hd Ω _ x _ hx1 hxj, map_zero, zero_mul]
  refine ⟨c / d, fun K _ β q r j hq hr hj => ?_⟩
  have hqj := le_chart ρ.P.A ρ.P.L 1 q j hj
  have hrq : r = q ≫ (h ▷ ρ.P.A).left := by
    have h2 : r ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left =
        (q ≫ (h ▷ ρ.P.A).left) ≫ (snd (baseOver (Sp S.R)) ρ.P.A).left := by
      rw [hr, Category.assoc, ← Over.comp_left, whiskerRight_snd]
    have w : (fst (baseOver (Sp S.R)) ρ.P.A).left =
        (snd (baseOver (Sp S.R)) ρ.P.A).left ≫ ρ.P.A.hom :=
      (Category.comp_id _).symm.trans (pullback.condition (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom))
    refine pullback.hom_ext (f := 𝟙 (Sp S.R)) (g := ρ.P.A.hom) ?_ h2
    change r ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left = _ ≫ (fst (baseOver (Sp S.R)) ρ.P.A).left
    rw [w, ← Category.assoc, h2]
    simp only [Category.assoc]
  change valR q _ _ = β (c / d) * valR r _ _
  rw [hrq, ← valR_pull ρ.P.A ρ.P.L 1 hth q _ hqj, hc K β q _ hq hqj, hd K β q _ hq hqj, map_div₀,
    ← _root_.mul_assoc, div_mul_cancel₀ _ ((map_ne_zero β).2 hd0)]

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DegenerationProofs.SpecialFibreImageTestIndependent
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Out GlobalTheory.ZH Classical
attribute [local instance] SplitExt.free SplitExt.finite MvPolynomial.gradedAlgebra

noncomputable section
namespace GlobalTheory.ZH.TestFib

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {S : ThetaSys o Ω} {ρ : S.Real} {M : RatModel o Ω}
  {U₀ : M.Z.Opens} {EE : M.Lat S.J} {Q : Clos ρ M U₀ EE} {p : ℕ} [Fact p.Prime]

theorem level_ne_zero (S : ThetaSys o Ω) (y : Sp (OO p) ⟶ M.Z) : ((S.r * S.N : ℕ) : kb p) ≠ 0 := by
  have h := S.unit.map (Spec.preimage (rPt p ≫ y ≫ M.s)).hom
  rw [map_natCast] at h
  exact h.ne_zero

variable {y : Sp (OO p) ⟶ M.Z} {y₀ : S.R →+* PadicAlgCl p} {t : ρ.GeoTest p y₀} {c : Q.Fac y t.u}

abbrev mb (tm : Q.TMap t c) : Matrix S.J S.J (kb p) :=
  tm.m.map fun a => IsLocalRing.residue (OO p) (t.u.j a)

theorem isUnit_det_mb (tm : Q.TMap t c) : IsUnit (mb tm).det := by
  have h := tm.unit.map ((IsLocalRing.residue (OO p)).comp t.u.j)
  rw [RingHom.map_det] at h
  exact h

theorem crd_image (tm : Q.TMap t c) (x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left) (hx : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _)
    (v : S.J → kb p) (hv : Crd (t.mod.Φ.H 1) t.mod.F x₀ v) :
    (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧
      Crd (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι) (Q.σ tm.l) ((x₀ ≫ t.mod.r) ≫ tm.f) ((mb tm).mulVec v) := by
  have h1 : (x₀ ≫ t.mod.r) ≫ t.u.G.hom = rPt p ≫ spMap t.u.j := by
    rw [Category.assoc, t.mod.cart.1.w, ← Category.assoc, hx]
    exact Category.id_comp _
  refine ⟨h1, tm.crd (kb p) ((IsLocalRing.residue (OO p)).comp t.u.j) _ v (h1.trans ?_)
    (t.mod.red (Over.homMk x₀ hx) v hv)⟩
  exact (Spec.map_comp _ _).symm

theorem image_over (tm : Q.TMap t c) (c' : Sp (kb p) ⟶ t.u.G.left) (h : c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j) :
    (c' ≫ tm.f) ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := by
  rw [Category.assoc, tm.f_over, ← Category.assoc, h, Category.assoc, c.fac]

theorem mem_cone_iff [ArithBase o Ω] (hL : GlobalTheory.UT.LL) (hB : BaseFacts S M U₀ EE) (tm : Q.TMap t c) (hS : S.Big)
    (v : S.J → kb p) :
    v ∈ cone t.mod.Φ.G.hom (t.mod.Φ.H 1) t.mod.F ↔ (∃ i, t.cls i = 0 ∧ v i ≠ 0) ∧
      ∀ (d : ℕ) (Pf : MvPolynomial S.J (kb p)), d ≤ S.N ^ S.g * S.g.factorial → Pf.IsHomogeneous d →
        (∀ w ∈ Q.Tors (rPt p ≫ y) tm.l, MvPolynomial.eval w Pf = 0) →
        MvPolynomial.eval ((mb tm).mulVec v) Pf = 0 := by
  haveI : IsAlgClosed (kb p) := (GlobalTheory.ZJ.kb_isAlgClosed_and_conj p).1
  have hsm : SmoothOfRelativeDimension S.g t.mod.Φ.G.hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback t.mod.cart.1 t.mod.smooth
  have hbig : Big S.g S.N (S.r * S.N) := ⟨(_root_.GlobalTheory.ZH.utest_dim_and_split hL o Ω S ρ p y₀ t.u).2.2.2.1, hS.1, hS.2.1⟩
  have key := _root_.GlobalTheory.ZH.FibCone.mem_cone_iff hL.1 hL.2.1 (kb p) t.mod.Φ S.g S.N (S.r * S.N) _ S.J _ t.mod.F t.mod.pol hbig
    t.mod.good t.mod.dim (level_ne_zero S y) hsm
    (fun d hd => (Mod.hilb_special_le_generic p _ _ _ _ _ 0 _ _ _ _ _ _ t.mod d).trans
      (_root_.GlobalTheory.ZH.FormCount.hilb_generic_le hL o Ω S ρ p y₀ t.u S.J t.σ d hd)) v
  obtain ⟨T₁, T₂⟩ := _root_.GlobalTheory.ZH.TorsCrd.tors_crd hL o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS
  have hinv : ∀ w, (mb tm)⁻¹.mulVec ((mb tm).mulVec w) = w := fun w => by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_det_mb tm), Matrix.one_mulVec]
  refine key.trans (and_congr (exists_congr fun i => and_congr (map_eq_zero_iff _ t.mod.xe.symm.injective) Iff.rfl)
    ⟨fun H d Pf hd hPf hT => ?_, fun H d Pf hd hPf hT => ?_⟩)
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm) hPf
    rw [← hev]
    refine H d F hd hF fun x hx => ?_
    obtain ⟨w, hw, hw'⟩ := T₁ x hx
    exact ⟨w, hw, (hev w).trans (hT _ hw')⟩
  · obtain ⟨F, hF, hev⟩ := InFibChart.exists_subst (mb tm)⁻¹ hPf
    rw [← hinv v, ← hev]
    refine H d F hd hF fun w hw => ?_
    obtain ⟨x, w₀, hx, hw₀, rfl⟩ := T₂ w hw
    obtain ⟨w₁, hw₁, h0⟩ := hT x hx
    obtain ⟨u, hu⟩ := CrdCalc.crd_unique hw₁ hw₀
    rw [hev, hinv, show w₀ = fun j => (u : kb p) * w₁ j from funext hu, InFibChart.eval_scale _ _ hPf, h0, mul_zero]

theorem image_special_fibre_iff : GlobalTheory.UT.LL → ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (S : ThetaSys o Ω) (ρ : S.Real) (M : RatModel o Ω) (U₀ : M.Z.Opens) (EE : M.Lat S.J), BaseFacts S M U₀ EE → ∀ (Q : Clos ρ M U₀ EE) (p : ℕ) [Fact p.Prime] (y : Sp (OO p) ⟶ M.Z) (y₀ : S.R →+* PadicAlgCl p) (t : ρ.GeoTest p y₀) (c : Q.Fac y t.u) (tm : Q.TMap t c), S.Big → ∀ x : Sp (kb p) ⟶ Q.P.left, x ≫ Q.P.hom = rPt p ≫ y → ((∃ c' : Sp (kb p) ⟶ t.u.G.left, c' ≫ t.u.G.hom = rPt p ≫ spMap t.u.j ∧ c' ≫ tm.f ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x) ↔ (⊤ ≤ x ⁻¹ᵁ Q.G ∧ Q.InFib x)) := by
  intro hL o Ω _ _ _ _ S ρ M U₀ EE hB Q p _ y y₀ t c tm hS x hx
  constructor
  · rintro ⟨c', hc', rfl⟩
    let x₀ : Sp (kb p) ⟶ t.mod.Φ.G.left := t.mod.cart.1.lift c' (𝟙 _) (hc'.trans (Category.id_comp _).symm)
    have h₁ : x₀ ≫ t.mod.r = c' := t.mod.cart.1.lift_fst _ _ _
    have h₂ : x₀ ≫ t.mod.Φ.G.hom = 𝟙 _ := t.mod.cart.1.lift_snd _ _ _
    obtain ⟨v, hv⟩ := CrdCalc.crd_exists (t.mod.Φ.H_isLB 1) t.mod.F x₀
    have hcr := (crd_image tm x₀ h₂ v hv).2
    rw [h₁] at hcr
    have hov := image_over tm c' hc'
    obtain ⟨k₁, k₂⟩ := (mem_cone_iff hL hB tm hS v).1 ⟨x₀, h₂, hv⟩
    rw [← Category.assoc]
    refine ⟨(_root_.GlobalTheory.ZH.TestCrit.le_preimage_G_iff_test o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS _ v hov hcr).2 k₁,
      InFibChart.inFib_of_chart o Ω S ρ M U₀ EE hB Q _ tm.l _ _ hcr ?_⟩
    rw [hov]
    exact k₂
  · rintro ⟨hG, hF⟩
    obtain ⟨x', rfl⟩ : ∃ x' : Sp (kb p) ⟶ (Q.P.hom ⁻¹ᵁ Q.W tm.l).toScheme, x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι = x := by
      refine ⟨IsOpenImmersion.lift _ x ?_, IsOpenImmersion.lift_fac _ _ _⟩
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨w, rfl⟩
      have e : Q.P.hom (x w) = y (rPt p w) :=
        (Scheme.Hom.comp_apply _ _ _).symm.trans
          ((congrArg (fun f : Sp (kb p) ⟶ M.Z => f w) hx).trans (Scheme.Hom.comp_apply _ _ _))
      show Q.P.hom (x w) ∈ Q.W tm.l
      rw [e]
      exact ((IsLocalRing.specializes_closedPoint (rPt p w)).map y.continuous).mem_open (Q.W tm.l).isOpen tm.mem
    have hLB : (Q.O1.pull (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι).IsLB := LB.isLB_pull Q.isLB _
    obtain ⟨w, hw⟩ := CrdCalc.crd_exists hLB (Q.σ tm.l) x'
    obtain ⟨v, rfl⟩ : ∃ v, (mb tm).mulVec v = w := ⟨(mb tm)⁻¹.mulVec w, by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_det_mb tm), Matrix.one_mulVec]⟩
    have hx' : x' ≫ (Q.P.hom ⁻¹ᵁ Q.W tm.l).ι ≫ Q.P.hom = rPt p ≫ y := (Category.assoc _ _ _).symm.trans hx
    have k₂ := hF tm.l x' _ rfl hw
    rw [hx] at k₂
    obtain ⟨x₀, h₂, hv⟩ := (mem_cone_iff hL hB tm hS v).2
      ⟨(_root_.GlobalTheory.ZH.TestCrit.le_preimage_G_iff_test o Ω S ρ M U₀ EE hB Q p y y₀ t c tm hS x' v hx' hw).1 hG, k₂⟩
    obtain ⟨h₁, hcr⟩ := crd_image tm x₀ h₂ v hv
    refine ⟨x₀ ≫ t.mod.r, h₁, ?_⟩
    have e : ((x₀ ≫ t.mod.r) ≫ tm.f) ≫ (Q.P.hom ∣_ Q.W tm.l) = x' ≫ (Q.P.hom ∣_ Q.W tm.l) := by
      rw [← cancel_mono (Q.W tm.l).ι, Category.assoc, Category.assoc x', morphismRestrict_ι, hx']
      exact image_over tm _ h₁
    rw [← Category.assoc, ImmSep.eq_of_crd_eq _ _ _ _ _ _ _ hLB (Q.imm tm.l) (kb p) _ x' _
      (by rw [← Category.assoc, e, Category.assoc]) hcr hw]

end GlobalTheory.ZH.TestFib
end
end

