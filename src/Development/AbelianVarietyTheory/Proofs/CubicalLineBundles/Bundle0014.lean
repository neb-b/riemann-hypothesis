module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsLineBundleExtension
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.UniqueFactorizationMonoidOfIsRegularRingOfIsLoca
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.Bundle0018

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsRigidifiedExtensionOfGenericFibre
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.ExtendLineBundle

noncomputable section

namespace GlobalTheory.GenericFibreExtend

theorem exists_specializes_of_mem_closure {X : Type*} [TopologicalSpace X] [NoetherianSpace X]
    [QuasiSober X] {O F : Set X} (hO : IsOpen O) (hF : IsClosed F) {y : X}
    (hy : y ∈ closure (O ∩ F)) : ∃ z ∈ O ∩ F, z ⤳ y := by
  obtain ⟨S, hS, hc, hi, hU⟩ := NoetherianSpace.exists_finite_set_isClosed_irreducible hF
  have h1 : O ∩ F ⊆ ⋃ s ∈ {s ∈ S | (s ∩ O).Nonempty}, s := by
    rintro x ⟨hxO, hxF⟩
    rw [hU] at hxF
    obtain ⟨s, hs, hx⟩ := hxF
    exact Set.mem_biUnion (show s ∈ {s ∈ S | (s ∩ O).Nonempty} from ⟨hs, x, hx, hxO⟩) hx
  have h2 : IsClosed (⋃ s ∈ {s ∈ S | (s ∩ O).Nonempty}, s) :=
    (hS.subset (Set.sep_subset _ _)).isClosed_biUnion fun s hs => hc s hs.1
  obtain ⟨s, ⟨hs, hsO⟩, hys⟩ := Set.mem_iUnion₂.1 (closure_minimal h1 h2 hy)
  obtain ⟨z, hz⟩ := QuasiSober.sober (hi s hs) (hc s hs)
  refine ⟨z, ⟨(hz.mem_open_set_iff hO).2 hsO, ?_⟩, hz.specializes hys⟩
  rw [hU]
  exact ⟨s, hs, hz.mem⟩

variable {X Y : Scheme.{0}} [IsIntegral X] [IsIntegral Y]

theorem exists_equations' (L : LB Y) (hL : L.IsLB) : ∃ f : L.ι → Y.functionFieldˣ,
    ∀ i k, genericPoint Y ∈ L.U i → genericPoint Y ∈ L.U k →
      unitVal _ (L.g i k) = f i / f k := by
  by_cases h : ∃ i₀, genericPoint Y ∈ L.U i₀
  · obtain ⟨i₀, h₀⟩ := h
    refine ⟨fun i => unitVal _ (L.g i i₀), fun i k hi hk => ?_⟩
    have hη : genericPoint Y ∈ L.U i ⊓ L.U k ⊓ L.U i₀ := ⟨⟨hi, hk⟩, h₀⟩
    have e := congrArg (unitVal _) (hL.cocycle i k i₀)
    rw [map_mul, unitVal_res _ hη, unitVal_res _ hη, unitVal_res _ hη] at e
    exact eq_div_iff_mul_eq'.2 e
  · exact ⟨1, fun i _ hi => (h ⟨i, hi⟩).elim⟩

theorem isGen_of_equations' (M N : LB Y) (a : M.ι → Y.functionFieldˣ) (b : N.ι → Y.functionFieldˣ)
    (ha : ∀ i k, genericPoint Y ∈ M.U i → genericPoint Y ∈ M.U k →
      unitVal _ (M.g i k) = a i / a k)
    (hb : ∀ i k, genericPoint Y ∈ N.U i → genericPoint Y ∈ N.U k →
      unitVal _ (N.g i k) = b i / b k)
    (s : ∀ p : M.ι × N.ι, Γ(Y, M.U p.1 ⊓ N.U p.2)ˣ)
    (hs : ∀ p, genericPoint Y ∈ (M.U p.1 ⊓ N.U p.2) → unitVal _ (s p) = a p.1 / b p.2) :
    LB.Gen.IsGen (⟨s⟩ : LB.Iso N M) := by
  intro (p : M.ι × N.ι) (q : M.ι × N.ι)
  refine ExtendLineBundle.unit_ext (U := M.U p.1 ⊓ N.U p.2 ⊓ (M.U q.1 ⊓ N.U q.2)) fun h => ?_
  have hp := h.1
  have hq := h.2
  have e₁ := ha p.1 q.1 hp.1 hq.1
  have e₂ := hb p.2 q.2 hp.2 hq.2
  have key : ∀ (V : Y.Opens) (_ : genericPoint Y ∈ V) (l₁ : V ≤ M.U p.1 ⊓ N.U p.2)
      (l₂ : V ≤ M.U p.1 ⊓ M.U q.1) (l₃ : V ≤ N.U p.2 ⊓ N.U q.2) (l₄ : V ≤ M.U q.1 ⊓ N.U q.2),
      unitVal V (res l₁ (s p)) =
        unitVal V (res l₂ (M.g p.1 q.1) * (res l₃ (N.g p.2 q.2))⁻¹ * res l₄ (s q)) := by
    intro V h l₁ l₂ l₃ l₄
    rw [map_mul, map_mul, map_inv, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h,
      unitVal_res _ h, e₁, e₂, hs p hp, hs q hq]
    rw [inv_div, mul_right_comm, div_mul_div_cancel, div_mul_div_cancel]
  exact key _ h _ _ _ _

variable (j : Y ⟶ X) (hη : j (genericPoint Y) ⤳ genericPoint X)

def fieldMap : X.functionField →+* Y.functionField :=
  (X.presheaf.stalkSpecializes hη ≫ j.stalkMap (genericPoint Y)).hom

theorem fieldMap_germ {U : X.Opens} (h : genericPoint X ∈ U) (h' : genericPoint Y ∈ j ⁻¹ᵁ U)
    (s : Γ(X, U)) :
    fieldMap j hη (X.presheaf.germ U _ h s) = Y.presheaf.germ (j ⁻¹ᵁ U) _ h' (j.app U s) := by
  change j.stalkMap _ (X.presheaf.stalkSpecializes hη (X.presheaf.germ U _ h s)) = _
  rw [TopCat.Presheaf.germ_stalkSpecializes_apply]
  exact Scheme.Hom.germ_stalkMap_apply j U _ _ s

theorem exists_fieldMap_eq [IsPreimmersion j] {y : Y} {u : Y.functionField}
    (hu : u ∈ localSubring y) : ∃ t ∈ localSubring (j y), fieldMap j hη t = u := by
  obtain ⟨a, rfl⟩ := hu
  obtain ⟨b, rfl⟩ := j.stalkMap_surjective y a
  obtain ⟨U, hx, s, rfl⟩ := X.presheaf.exists_germ_eq b
  refine ⟨_, germ_mem hx (genericPoint_mem hx) s, ?_⟩
  have hy : y ∈ j ⁻¹ᵁ U := hx
  rw [fieldMap_germ j hη _ (genericPoint_mem hy), ← algebraMap_germ hy]
  exact congrArg _ (Scheme.Hom.germ_stalkMap_apply j U _ _ s).symm

theorem fieldMap_surjective [IsPreimmersion j] : Function.Surjective (fieldMap j hη) := by
  intro u
  obtain ⟨U, hx, s, rfl⟩ := Y.presheaf.exists_germ_eq (x := genericPoint Y) u
  obtain ⟨t, -, ht⟩ := exists_fieldMap_eq j hη (germ_mem hx hx s)
  exact ⟨t, ht⟩

theorem fieldMap_mem_iff [IsPreimmersion j] {y : Y} {t : X.functionField} :
    fieldMap j hη t ∈ localSubring y ↔ t ∈ localSubring (j y) := by
  constructor
  · intro h
    obtain ⟨t', ht', e⟩ := exists_fieldMap_eq j hη h
    rwa [← (fieldMap j hη).injective e]
  · intro h
    obtain ⟨U, hx, s, rfl⟩ := exists_section_of_mem h
    have hy : y ∈ j ⁻¹ᵁ U := hx
    rw [fieldMap_germ j hη _ (genericPoint_mem hy)]
    exact germ_mem hy _ _

def unitMap : X.functionFieldˣ →* Y.functionFieldˣ := Units.map (fieldMap j hη).toMonoidHom

theorem unitMap_mem_iff [IsPreimmersion j] {y : Y} {t : X.functionFieldˣ} :
    unitMap j hη t ∈ localUnits y ↔ t ∈ localUnits (j y) := by
  rw [mem_localUnits, mem_localUnits, ← fieldMap_mem_iff j hη, ← fieldMap_mem_iff j hη, map_inv₀]
  rfl

theorem unitMap_surjective [IsPreimmersion j] : Function.Surjective (unitMap j hη) := by
  intro u
  obtain ⟨t, ht⟩ := fieldMap_surjective j hη u
  have h0 : t ≠ 0 := by
    rintro rfl
    exact u.ne_zero (ht.symm.trans (map_zero _))
  exact ⟨Units.mk0 t h0, Units.ext ht⟩

theorem unitVal_pullU {U : X.Opens} (h' : genericPoint Y ∈ j ⁻¹ᵁ U) (a : Γ(X, U)ˣ) :
    unitVal (j ⁻¹ᵁ U) (pullU j U a) = unitMap j hη (unitVal U a) := by
  have h : genericPoint X ∈ U := genericPoint_mem (x := j (genericPoint Y)) h'
  apply Units.ext
  rw [val_unitVal h']
  change _ = fieldMap j hη (unitVal U a).val
  rw [val_unitVal h, fieldMap_germ j hη h h']
  rfl

theorem unitVal_pull (M : LB X) (p q : PUnit → M.ι)
    (h : genericPoint Y ∈ (LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q)) :
    unitVal _ ((M.pull j).g p q) = unitMap j hη (unitVal _ (M.g (p ⟨⟩) (q ⟨⟩))) := by
  have hle : LB.wchart M (fun _ => j) p ⊓ LB.wchart M (fun _ => j) q ≤
      j ⁻¹ᵁ (M.U (p ⟨⟩) ⊓ M.U (q ⟨⟩)) := fun y hy =>
    ⟨LB.wchart_le M (fun _ => j) p ⟨⟩ hy.1, LB.wchart_le M (fun _ => j) q ⟨⟩ hy.2⟩
  have e : (M.pull j).g p q = res hle (pullU j _ (M.g (p ⟨⟩) (q ⟨⟩))) := by
    change (∏ _k : PUnit.{1}, (res hle (pullU j _ (M.g (p _k) (q _k)))) ^ (1 : ℤ)) = _
    rw [Fintype.prod_unique, zpow_one]
  rw [e]
  refine (unitVal_res _ h _).trans (unitVal_pullU j hη ?_ _)
  exact ⟨LB.wchart_le M (fun _ => j) p ⟨⟩ h.1, LB.wchart_le M (fun _ => j) q ⟨⟩ h.2⟩

omit [IsIntegral Y] in
theorem isOpen_localUnits (t : X.functionFieldˣ) : IsOpen {x : X | t ∈ localUnits x} := by
  rw [isOpen_iff_eventually]
  intro x hx
  have := mem_localUnits.1 hx
  filter_upwards [eventually_mem this.1, eventually_mem this.2] with y h1 h2
  exact mem_localUnits.2 ⟨h1, h2⟩

end GlobalTheory.GenericFibreExtend

namespace GlobalTheory

open GenericFibreExtend

theorem exists_lineBundle_extension_of_generalizing (X Y : Scheme.{0}) [IsIntegral X]
    [IsIntegral Y] [IsLocallyNoetherian X] [CompactSpace X] (j : Y ⟶ X) [IsPreimmersion j]
    (hj : GeneralizingMap j)
    (hX : ∀ x : X, UniqueFactorizationMonoid (X.presheaf.stalk x)) (L : LB Y) (hL : L.IsLB) :
    ∃ L' : LB X, L'.IsLB ∧ LBIso (L'.pull j) L := by
  have : IsNoetherian X := {}
  have hη : j (genericPoint Y) ⤳ genericPoint X := by
    obtain ⟨y, -, hy⟩ := hj (genericPoint_specializes (j (genericPoint Y)))
    rw [← hy]
    exact (genericPoint_specializes y).map j.continuous
  have : NoetherianSpace Y := j.isEmbedding.isInducing.noetherianSpace
  obtain ⟨f', hf'⟩ := exists_equations' L hL
  choose f hf using fun i => unitMap_surjective j hη (f' i)
  have hfu : ∀ i k y, y ∈ L.U i → y ∈ L.U k → f i / f k ∈ localUnits (j y) := fun i k y hi hk => by
    rw [← unitMap_mem_iff j hη, map_div, hf, hf,
      ← hf' i k (genericPoint_mem hi) (genericPoint_mem hk)]
    exact unitVal_mem (U := L.U i ⊓ L.U k) ⟨hi, hk⟩ _
  choose V hVo hV using fun i => j.isEmbedding.isInducing.isOpen_iff.1 (L.U i).isOpen
  have hV' : ∀ i y, j y ∈ V i ↔ y ∈ L.U i := fun i y => Set.ext_iff.1 (hV i) y
  obtain ⟨ι, hι⟩ := (NoetherianSpace.isCompact (Set.univ : Set Y)).elim_finite_subcover
    (fun i => (L.U i : Set Y)) (fun i => (L.U i).isOpen) (fun y _ => by
      have : y ∈ ⨆ i, L.U i := hL.cover ▸ trivial
      exact Set.mem_iUnion.2 (Opens.mem_iSup.1 this))
  let Z : ι × ι → Set X := fun p => (V p.1 ∩ V p.2) ∩ {x : X | f p.1 / f p.2 ∈ localUnits x}ᶜ
  let W : Set X := ⋂ p, (closure (Z p))ᶜ
  have hWo : IsOpen W := isOpen_iInter_of_finite fun p => isClosed_closure.isOpen_compl
  have hW : ∀ y, j y ∈ W := fun y => Set.mem_iInter.2 fun p hp => by
    obtain ⟨z, hz, hzy⟩ := exists_specializes_of_mem_closure ((hVo _).inter (hVo _))
      (isOpen_localUnits _).isClosed_compl hp
    obtain ⟨y', -, rfl⟩ := hj hzy
    exact hz.2 (hfu _ _ y' ((hV' _ _).1 hz.1.1) ((hV' _ _).1 hz.1.2))
  obtain ⟨T, h₀, hT, hc⟩ := exists_compatible_cover hX
    (T₀ := Set.range fun i : ι => ((⟨V i ∩ W, (hVo i).inter hWo⟩ : X.Opens), f i)) (by
      rintro _ ⟨i, rfl⟩ _ ⟨k, rfl⟩ x hi hk
      by_contra h
      exact Set.mem_iInter.1 hi.2 (i, k) (subset_closure ⟨⟨hi.1, hk.1⟩, h⟩))
  choose g hg using fun p q : T => exists_unit (U := p.1.1 ⊓ q.1.1) (t := p.1.2 / q.1.2)
    fun y hy => hT _ p.2 _ q.2 y hy.1 hy.2
  let L' : LB X := ⟨T, fun p => p.1.1, g⟩
  choose s hs using fun p : L.ι × (PUnit → T) => exists_unit
    (U := L.U p.1 ⊓ LB.wchart L' (fun _ => j) p.2)
    (t := f' p.1 / unitMap j hη (p.2 ⟨⟩).1.2) fun y hy => by
      obtain ⟨i, hi, hyi⟩ := Set.mem_iUnion₂.1 (hι (Set.mem_univ y))
      rw [← hf, ← map_div, unitMap_mem_iff]
      have := mul_mem (hfu p.1 i y hy.1 hyi) (hT _ (h₀ ⟨⟨i, hi⟩, rfl⟩) _ (p.2 ⟨⟩).2 (j y)
        ⟨(hV' _ _).2 hyi, hW y⟩ (LB.wchart_le L' (fun _ => j) p.2 ⟨⟩ hy.2))
      rwa [div_mul_div_cancel] at this
  refine ⟨L', ⟨?_, fun p => ExtendLineBundle.unit_ext fun h => ?_,
    fun p q r => ExtendLineBundle.unit_ext fun h => ?_⟩,
    ⟨s⟩, isGen_of_equations' L (L'.pull j) f' (fun p => unitMap j hη (p ⟨⟩).1.2) hf'
      (fun p q hp hq => ?_) s hs⟩
  · refine top_unique fun x _ => ?_
    obtain ⟨p, hp, hx⟩ := hc x
    exact Opens.mem_iSup.2 ⟨⟨p, hp⟩, hx⟩
  · rw [unitVal_res _ h, map_one]
    exact (hg p p ⟨h, h⟩).trans (div_self' _)
  · rw [map_mul, unitVal_res _ h, unitVal_res _ h, unitVal_res _ h]
    exact (congrArg₂ (· * ·) (hg p q h.1) (hg q r ⟨h.1.2, h.2⟩)).trans
      ((div_mul_div_cancel _ _ _).trans (hg p r ⟨h.1.1, h.2⟩).symm)
  · refine (unitVal_pull j hη L' p q ⟨hp, hq⟩).trans ?_
    rw [← map_div]
    refine congrArg _ (hg (p ⟨⟩) (q ⟨⟩) (genericPoint_mem (x := j (genericPoint Y)) ?_))
    exact ⟨LB.wchart_le L' (fun _ => j) p ⟨⟩ hp, LB.wchart_le L' (fun _ => j) q ⟨⟩ hq⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsWeierstrassCoordinatesOnLine
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.UnifCoord

open Filter Topology

theorem exists_xyt {g : ℕ} (V : WeierstrassCurve ℂ) (Λ : Submodule ℤ (Fin g → ℂ))
    [DiscreteTopology Λ] (P : (Fin g → ℂ) → Fin 3 → ℂ) (F : Fin 3 → Fin 3 → (Fin g → ℂ) → ℂ)
    (hE : ∀ z, V.toProjective.Equation (P z))
    (ho : ∀ i, IsOpen {z | P z i ≠ 0}) (hd : ∀ i j, DifferentiableOn ℂ (F i j) {z | P z i ≠ 0})
    (hF : ∀ i j z, P z i ≠ 0 → F i j z * P z i = P z j) (hΛ : ∀ z, P z 2 = 0 ↔ z ∈ Λ)
    (hper : ∀ i j z l, l ∈ Λ → F i j (z + l) = F i j z) (h0 : P 0 0 = 0) (h1 : P 0 1 ≠ 0)
    (w : Fin g → ℂ) (hw : fderiv ℂ (F 1 0) 0 w = -1) :
    w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, DifferentiableOn ℂ x {z | z • w ∈ Λ}ᶜ ∧
      DifferentiableOn ℂ y {z | z • w ∈ Λ}ᶜ ∧
      (∀ l : ℂ, l • w ∈ Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧
      (∀ z : ℂ, z • w ∉ Λ → V.toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧
      deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧
      Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  have hw0 : w ≠ 0 := by
    rintro rfl
    simp at hw
  have hlin : Differentiable ℂ (fun z : ℂ => z • w) := by fun_prop
  have hcont : Tendsto (fun z : ℂ => z • w) (𝓝 0) (𝓝 0) := by
    simpa using hlin.continuous.tendsto 0
  have hd2 : ∀ j, DifferentiableOn ℂ (fun z : ℂ => F 2 j (z • w)) {z | z • w ∈ Λ}ᶜ := fun j =>
    (hd 2 j).comp hlin.differentiableOn fun z hz h => hz ((hΛ _).1 h)
  have hn1 : {z | P z 1 ≠ 0} ∈ 𝓝 (0 : Fin g → ℂ) := (ho 1).mem_nhds h1
  have hev1 : ∀ᶠ z : ℂ in 𝓝 0, P (z • w) 1 ≠ 0 := hcont hn1
  have hoff : ∀ᶠ z : ℂ in 𝓝[≠] 0, P (z • w) 2 ≠ 0 := by
    have h : ({0} : Set Λ) ∈ 𝓝 (0 : Λ) := (isOpen_discrete _).mem_nhds rfl
    rw [nhds_subtype_eq_comap, mem_comap] at h
    obtain ⟨s, hs, hs'⟩ := h
    have h' : ∀ᶠ z : ℂ in 𝓝 0, z • w ∈ s := hcont hs
    filter_upwards [mem_nhdsWithin_of_mem_nhds h', self_mem_nhdsWithin] with z hz hz0 h2
    have := hs' (show (⟨z • w, (hΛ _).1 h2⟩ : Λ) ∈ Subtype.val ⁻¹' s from hz)
    have e : z • w = 0 := congrArg Subtype.val this
    exact hz0 ((smul_eq_zero.1 e).resolve_right hw0)
  have hda : ∀ j, DifferentiableAt ℂ (F 1 j) 0 := fun j => (hd 1 j).differentiableAt hn1
  have h2 : P 0 2 = 0 := (hΛ 0).2 Λ.zero_mem
  refine ⟨hw0, fun z => F 2 0 (z • w), fun z => F 2 1 (z • w), fun z => -F 1 0 (z • w), hd2 0, hd2 1,
    fun l hl z => ?_, fun z hz => ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [add_smul, hper _ _ _ _ hl, and_self]
  · have hz2 : P (z • w) 2 ≠ 0 := fun h => hz ((hΛ _).1 h)
    rw [← WeierstrassCurve.Projective.equation_some,
      ← WeierstrassCurve.Projective.equation_smul _ (isUnit_iff_ne_zero.2 hz2)]
    convert hE (z • w) using 1
    ext i
    fin_cases i
    · simpa [mul_comm] using hF 2 0 _ hz2
    · simpa [mul_comm] using hF 2 1 _ hz2
    · simp
  · refine AnalyticAt.neg (DifferentiableOn.analyticAt (s := {z : ℂ | P (z • w) 1 ≠ 0}) ?_ hev1)
    exact (hd 1 0).comp hlin.differentiableOn fun z hz => hz
  · have := hF 1 0 0 h1
    rw [h0, mul_eq_zero] at this
    simp [this.resolve_right h1]
  · have h3 : HasDerivAt (fun z : ℂ => z • w) w 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).smul_const w
    have h4 : HasFDerivAt (F 1 0) (fderiv ℂ (F 1 0) 0) ((0 : ℂ) • w) := by
      rw [zero_smul]; exact (hda 0).hasFDerivAt
    have h5 := (h4.comp_hasDerivAt (0 : ℂ) h3).neg
    rw [hw, neg_neg] at h5
    exact h5.deriv
  · filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2
    apply mul_right_cancel₀ hz2
    have a := hF 1 0 _ hz1
    have b := hF 2 0 _ hz2
    have c := hF 2 1 _ hz2
    linear_combination -(F 1 0 (z • w)) * c - a + b
  · have hs0 : F 1 2 0 = 0 := by
      have := hF 1 2 0 h1
      rw [h2, mul_eq_zero] at this
      exact this.resolve_right h1
    have hs : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝 0) := by
      have := (hda 2).continuousAt.tendsto.comp hcont
      rw [hs0] at this
      exact this.mono_left nhdsWithin_le_nhds
    have hprod : ∀ᶠ z : ℂ in 𝓝[≠] 0, F 1 2 (z • w) * F 2 1 (z • w) = 1 := by
      filter_upwards [mem_nhdsWithin_of_mem_nhds hev1, hoff] with z hz1 hz2
      apply mul_right_cancel₀ hz2
      have a := hF 1 2 _ hz1
      have c := hF 2 1 _ hz2
      linear_combination (F 1 2 (z • w)) * c + a
    have hs' : Tendsto (fun z : ℂ => F 1 2 (z • w)) (𝓝[≠] 0) (𝓝[≠] 0) :=
      tendsto_nhdsWithin_iff.2 ⟨hs, hprod.mono fun z hz => left_ne_zero_of_mul_eq_one hz⟩
    refine (tendsto_norm_inv_nhdsNE_zero_atTop.comp hs').congr' ?_
    filter_upwards [hprod] with z hz
    simp only [Function.comp_apply]
    rw [eq_inv_of_mul_eq_one_right hz]

theorem top_le_ptHom_preimage_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ)
    (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P) (i : Fin 3) :
    ⊤ ≤ ptHom W f P hP ⁻¹ᵁ coordOpen W i ↔ P i ≠ 0 := by
  rw [ptHom_preimage_coordOpen]
  constructor
  · intro h h0
    rw [h0, PrimeSpectrum.basicOpen_zero] at h
    exact h (Set.mem_univ (default : PrimeSpectrum ℂ))
  · intro h p _ hp
    exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp (isUnit_iff_ne_zero.2 h))

theorem eq_zero_and_ne_zero {V : WeierstrassCurve ℂ} {P : Fin 3 → ℂ} (hP : IsUnimodularSol V P)
    (h2 : P 2 = 0) : P 0 = 0 ∧ P 1 ≠ 0 := by
  have h0 : P 0 = 0 := WeierstrassCurve.Projective.X_eq_zero_of_Z_eq_zero hP.equation h2
  refine ⟨h0, fun h1 => ?_⟩
  have h : Ideal.span (Set.range P) ≤ ⊥ := by
    rw [Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h0
    · exact h1
    · exact h2
  rw [hP.span_eq_top] at h
  exact top_ne_bot (le_bot_iff.1 h)

theorem ptHom_eq_zero_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ)
    (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P) :
    P 2 = 0 ↔ ptHom W f P hP = spMap f ≫ zero W := by
  rw [SpecMap_zero]
  constructor
  · intro h2
    obtain ⟨h0, h1⟩ := eq_zero_and_ne_zero hP h2
    rw [← ptHom_smul W f ![0, 1, 0] (isUnimodularSol_zero _) (isUnit_iff_ne_zero.2 h1)]
    refine ptHom_congr W _ _ _ rfl ?_ _
    ext i
    fin_cases i <;> simp [h0, h2]
  · intro e
    by_contra h2
    have := (top_le_ptHom_preimage_iff W f P hP 2).2 h2
    rw [e, top_le_ptHom_preimage_iff] at this
    exact this rfl

theorem exists_coord_on_line : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (f : R →+* ℂ) (A : Over (Sp ℂ)) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR ℂ ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap ℂ (DualNumber ℂ)).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h → ∀ (L₁ : LB A.left) (g : ℕ) (u : HolUnif A L₁ g) (w : Fin g → ℂ), u.IsDiff w v → w ≠ 0 ∧ ∃ x y t : ℂ → ℂ, DifferentiableOn ℂ x {z | z • w ∈ u.Λ}ᶜ ∧ DifferentiableOn ℂ y {z | z • w ∈ u.Λ}ᶜ ∧ (∀ l : ℂ, l • w ∈ u.Λ → ∀ z, x (z + l) = x z ∧ y (z + l) = y z) ∧ (∀ z : ℂ, z • w ∉ u.Λ → (W.map f).toAffine.Equation (x z) (y z)) ∧ AnalyticAt ℂ t 0 ∧ t 0 = 0 ∧ deriv t 0 = 1 ∧ (∀ᶠ z in nhdsWithin 0 {0}ᶜ, t z * y z = -x z) ∧ Filter.Tendsto (fun z => ‖y z‖) (nhdsWithin 0 {0}ᶜ) Filter.atTop := by
  intro R _ W f A _ φ v h hpb he hv L₁ g u w hw
  obtain ⟨c, hc, -⟩ := GlobalTheory.CoordFn.exists_coordFn R W
  have hover : ∀ z, (u.ex z).left ≫ A.hom = 𝟙 (Sp ℂ) := fun z => Over.w (u.ex z)
  have hpt : ∀ z, ∃ (P : Fin 3 → ℂ) (hP : IsUnimodularSol (W.map f) P),
      (u.ex z).left ≫ φ = ptHom W f P hP := fun z =>
    exists_eq_ptHom_of_isLocalRing R W ℂ f ((u.ex z).left ≫ φ) (by
      rw [Category.assoc, hpb.w, ← Category.assoc, hover]
      exact Category.id_comp _)
  choose P hP hPe using hpt
  have hmem : ∀ z i, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i) ↔ P z i ≠ 0 := fun z i => by
    rw [← top_le_ptHom_preimage_iff W f (P z) (hP z), ← hPe, Scheme.Hom.comp_preimage]
  have hset : ∀ i, {z | P z i ≠ 0} = {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W i)} :=
    fun i => Set.ext fun z => (hmem z i).symm
  have hΛ : ∀ z, P z 2 = 0 ↔ z ∈ u.Λ := fun z => by
    rw [ptHom_eq_zero_iff W f (P z) (hP z), ← hPe, ← he, ← u.ker]
    constructor
    · intro e
      have e' : u.ex z = η[A] :=
        Over.OverMorphism.ext (hpb.hom_ext e ((hover z).trans (Over.w η[A]).symm))
      rw [e', Hom.one_def]
      simp
    · intro e
      rw [e, Hom.one_def]
      simp [eSec]
  have h00 := eq_zero_and_ne_zero (hP 0) ((hΛ 0).2 u.Λ.zero_mem)
  have := u.discrete
  refine exists_xyt (W.map f) u.Λ P (fun i j z => valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i)
    ((φ.app (coordOpen W i)).hom (c i j))) (fun z => (hP z).equation)
    (fun i => hset i ▸ (u.hol _ 0).1) (fun i j => hset i ▸ (u.hol _ _).2) (fun i j z hz => ?_) hΛ
    (fun i j z l hl => ?_) h00.1 h00.2 w ?_
  · have hz' := (top_le_ptHom_preimage_iff W f (P z) (hP z) i).2 hz
    have e : valAt' (u.ex z).left (φ ⁻¹ᵁ coordOpen W i) ((φ.app (coordOpen W i)).hom (c i j)) =
        valAt' (ptHom W f (P z) (hP z)) (coordOpen W i) (c i j) :=
      (valAt'_comp (u.ex z).left φ _ _).trans (congrArg (fun k => valAt' k _ _) (hPe z))
    beta_reduce
    rw [e, valAt'_eq_valAt _ hz']
    exact hc i j ℂ f (P z) (hP z) hz'
  · simp only [u.ex_add, (u.ker l).2 hl, _root_.mul_one]
  · have h1 : ⊤ ≤ ptHom W ((algebraMap ℂ (DualNumber ℂ)).comp f) ![DualNumber.eps, -1, 0] h ⁻¹ᵁ
        coordOpen W 1 := by
      rw [ptHom_preimage_coordOpen]
      intro p _ hp
      exact p.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hp isUnit_one.neg)
    have h2 : ⊤ ≤ v.left ⁻¹ᵁ (φ ⁻¹ᵁ coordOpen W 1) := by
      rw [← Scheme.Hom.comp_preimage, hv]
      exact h1
    rw [← hw _ h2]
    have e := hc 1 0 _ _ _ h h1
    have e2 : ∀ (k : Sp (DualNumber ℂ) ⟶ scheme W) (hk : ⊤ ≤ k ⁻¹ᵁ coordOpen W 1),
        v.left ≫ φ = k → (v.left.appLE (φ ⁻¹ᵁ coordOpen W 1) ⊤ h2).hom
          ((φ.app (coordOpen W 1)).hom (c 1 0)) = (k.appLE (coordOpen W 1) ⊤ hk).hom (c 1 0) := by
      rintro _ hk rfl
      rw [Scheme.Hom.comp_appLE]
      rfl
    rw [e2 _ h1 hv]
    have e3 := congrArg TrivSqZeroExt.snd e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, mul_neg, _root_.mul_one,
      TrivSqZeroExt.snd_neg, DualNumber.snd_eps] at e3
    exact neg_eq_iff_eq_neg.1 e3

end GlobalTheory.UnifCoord
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.TensorMapFiniteOfSplit
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TensorFinite

variable {S : Scheme.{0}}



set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct in
attribute [local instance] Over.cartesianMonoidalCategory in
variable {S : Scheme.{0}} in
theorem _root_.GlobalTheory.TensorFinite.isFinite_tensorHom {X Y X' Y' : Over S} (f : X ⟶ Y) (g : X' ⟶ Y') (hf : IsFinite f.left)
    (hg : IsFinite g.left) : IsFinite (f ⊗ₘ g).left := by
  rw [Over.tensorHom_left]
  exact MorphismProperty.pullbackMap (P := @IsFinite) hf hg (Over.w f).symm (Over.w g).symm

end GlobalTheory.TensorFinite
end
end

