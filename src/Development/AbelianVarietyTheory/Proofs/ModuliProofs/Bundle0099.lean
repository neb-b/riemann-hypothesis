module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyCubicalPull
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.PolPull

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {G : Over S} {G' : Over S'}
  {φ : G'.left ⟶ G.left} {L : LB G.left} {L' : LB G'.left}

theorem isCommMonObj_of_isGrpPullback [GrpObj G] [GrpObj G'] [IsCommMonObj G]
    (h : IsGrpPullback G' G f φ) : IsCommMonObj G' := by
  rw [isCommMonObj_iff_isMulCommutative]
  intro T
  refine ⟨⟨fun x y => Over.OverMorphism.ext (h.1.hom_ext ?_ (by rw [Over.w, Over.w]))⟩⟩
  rw [← h.2 T x y (pushPt h.1.w x) (pushPt h.1.w y) rfl rfl,
    ← h.2 T y x (pushPt h.1.w y) (pushPt h.1.w x) rfl rfl, _root_.mul_comm]

theorem isAbelianScheme_of_isGrpPullback [GrpObj G] [GrpObj G'] (hG : IsAbelianScheme G)
    (h : IsGrpPullback G' G f φ) : IsAbelianScheme G' := by
  have := hG.comm
  exact
    { comm := isCommMonObj_of_isGrpPullback h
      smooth := MorphismProperty.of_isPullback (P := @Smooth) h.1 hG.smooth
      proper := MorphismProperty.of_isPullback (P := @IsProper) h.1 hG.proper
      geomConnected := MorphismProperty.of_isPullback (P := @GeometricallyConnected) h.1 hG.geomConnected }

theorem relAmple_restrict (h : IsPullback φ G'.hom G.hom f) (hL : L.IsLB) (hL' : L'.IsLB)
    (e : LBIso L' (L.pull φ)) (hA : Out.RelAmple G L) (V : S.Opens) (hV : IsAffineOpen V) :
    Out.RelAmple (Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) := by
  have H : IsPullback ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (G'.hom ∣_ (f ⁻¹ᵁ V)) G.hom ((f ⁻¹ᵁ V).ι ≫ f) :=
    (isPullback_morphismRestrict G'.hom (f ⁻¹ᵁ V)).flip.paste_horiz h
  obtain ⟨w, hw⟩ : LBIso (L'.pull (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι) (L.pull ((G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ)) :=
    LBIso.chartPull (chartPullPull L' _ _ rfl)
      (chartPullSame L (fun _ : PUnit => (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι ≫ φ) (fun _ => φ) (fun _ => 1) _ fun _ => rfl) e
  let i := (G'.hom ⁻¹ᵁ (f ⁻¹ᵁ V)).ι
  have hPull : (L'.pull i).IsLB := by
    refine ⟨top_le_iff.1 ?_, ?_, ?_⟩
    · intro y _
      obtain ⟨j, hj⟩ := exists_chart hL' (i y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => j, mem_pull.2 hj⟩
    · intro J
      refine unit_ext fun y hy => ?_
      rw [gm_res (𝟙 _) y _ hy, map_one, gm_pull_g L' i (𝟙 _) y J J hy hy]
      exact gm_self hL' i y (mem_pull.1 hy)
    · intro I J K
      refine unit_ext fun y hy => ?_
      rw [map_mul, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy, gm_res (𝟙 _) y _ hy,
        gm_pull_g L' i (𝟙 _) y I J hy.1.1 hy.1.2,
        gm_pull_g L' i (𝟙 _) y J K hy.1.2 hy.2,
        gm_pull_g L' i (𝟙 _) y I K hy.1.1 hy.2]
      exact gm_cocycle hL' i y (mem_pull.1 hy.1.1) (mem_pull.1 hy.1.2) (mem_pull.1 hy.2)
  exact relAmple_pull (A' := Over.mk (G'.hom ∣_ (f ⁻¹ᵁ V))) H hL hPull
    ((isGen_iff w).1 hw) V hV (fun y => y.2) hA

theorem pol_pull_of_relAmple_local
    (hloc : ∀ (S : Scheme.{0}) (A : Over S) (L : LB A.left), L.IsLB → QuasiCompact A.hom → QuasiSeparated A.hom →
      (∀ s : S, ∃ (U : S.Opens) (_ : s ∈ U),
        Out.RelAmple (Over.mk (A.hom ∣_ U)) (L.pull (A.hom ⁻¹ᵁ U).ι)) → Out.RelAmple A L) :
    ∀ (S S' : Scheme.{0}) (G : Over S) (G' : Over S') [GrpObj G] [GrpObj G'] (f : S' ⟶ S) (φ : G'.left ⟶ G.left) (L : LB G.left) (L' : LB G'.left), L.IsLB → L'.IsLB → IsAbelianScheme G → IsGrpPullback G' G f φ → LBIso L' (L.pull φ) → IsAbelianScheme G' ∧ (Out.RelAmple G L → Out.RelAmple G' L') ∧ (Out.KTriv G L → Out.KTriv G' L') := by
  intro S S' G G' _ _ f φ L L' hL hL' hG h e
  have hG' := isAbelianScheme_of_isGrpPullback hG h
  have := hG'.proper
  refine ⟨hG', fun hA => hloc S' G' L' hL' inferInstance inferInstance fun s => ?_, fun hK => ?_⟩
  · obtain ⟨V, hV, hs, -⟩ := exists_isAffineOpen_mem_and_subset (X := S) (U := ⊤) (x := f s) trivial
    exact ⟨f ⁻¹ᵁ V, hs, relAmple_restrict h.1 hL hL' e hA V hV⟩
  · obtain ⟨w, hw⟩ := e
    exact kTriv_pull h hL hL' ((isGen_iff w).1 hw) hK

end GlobalTheory.PolPull
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfProper
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

section Pts

variable {k : Type} [Field k] [IsAlgClosed k]

theorem hom_ext_pts {X Y : Over (Sp k)} (hX : Smooth X.hom) [IsSeparated Y.hom] {f g : X ⟶ Y}
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ X, x ≫ f = x ≫ g) : f = g := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ X.hom hX).1
  exact Over.OverMorphism.ext (ComplexPoints.hom_ext_of_points X.hom Y.hom (by rw [Over.w, Over.w]) fun x hx =>
    congrArg (fun q => q.left) (h (Over.homMk x hx)))

theorem exists_lift_pt {S : Scheme.{0}} {A B : Over S} (ψ : A ⟶ B) [LocallyOfFiniteType ψ.left] [Surjective ψ.left]
    (t : Sp k ⟶ S) (y : Over.mk t ⟶ B) : ∃ x : Over.mk t ⟶ A, x ≫ ψ = y := by
  let y' : Sp k ⟶ B.left := y.left
  obtain ⟨z, -⟩ := (pullback.snd ψ.left y').surjective (default : PrimeSpectrum k)
  obtain ⟨x, hx, -⟩ := ComplexPoints.exists_point_mem (pullback.snd ψ.left y') (Z := Set.univ)
    isClosed_univ.isLocallyClosed ⟨z, trivial⟩
  have e : (x ≫ pullback.fst ψ.left y') ≫ ψ.left = y' := by
    rw [Category.assoc, pullback.condition, reassoc_of% hx]
  exact ⟨Over.homMk (x ≫ pullback.fst ψ.left y') (by rw [← Over.w ψ, ← Category.assoc, e]; exact Over.w y),
    Over.OverMorphism.ext e⟩

theorem exists_fac {A B Y : Over (Sp k)} [GrpObj A] [GrpObj B] [GrpObj Y] (hA : Smooth A.hom) [IsSeparated Y.hom]
    (ψ₀ : A ⟶ B) [IsMonHom ψ₀] [Etale ψ₀.left] [Surjective ψ₀.left] [QuasiCompact ψ₀.left] (ψ : A ⟶ Y) [IsMonHom ψ]
    (h : ∀ x : 𝟙_ (Over (Sp k)) ⟶ A, x ≫ ψ₀ = 1 → x ≫ ψ = 1) : ∃ α : B ⟶ Y, ψ₀ ≫ α = ψ := by
  let R : Over (Sp k) := Over.mk (pullback.fst ψ₀.left ψ₀.left ≫ A.hom)
  let p₁ : R ⟶ A := Over.homMk (pullback.fst _ _) rfl
  let p₂ : R ⟶ A := Over.homMk (pullback.snd _ _) (by
    show _ = pullback.fst ψ₀.left ψ₀.left ≫ A.hom
    rw [← Over.w ψ₀, ← pullback.condition_assoc])
  have e₀ : p₁ ≫ ψ₀ = p₂ ≫ ψ₀ := Over.OverMorphism.ext pullback.condition
  have e : p₁ ≫ ψ = p₂ ≫ ψ := hom_ext_pts (inferInstanceAs (Smooth (pullback.fst ψ₀.left ψ₀.left ≫ A.hom))) fun x => by
    have := h ((x ≫ p₁) * (x ≫ p₂)⁻¹) (by
      rw [MonObj.mul_comp, GrpObj.inv_comp, Category.assoc, e₀, Category.assoc, mul_inv_cancel])
    rw [MonObj.mul_comp, GrpObj.inv_comp, mul_inv_eq_one, Category.assoc, Category.assoc] at this
    exact this
  have e' : pullback.fst ψ₀.left ψ₀.left ≫ ψ.left = pullback.snd ψ₀.left ψ₀.left ≫ ψ.left :=
    congrArg (fun q => q.left) e
  have hd : ∀ {Z : Scheme.{0}} (g₁ g₂ : Z ⟶ A.left), g₁ ≫ ψ₀.left = g₂ ≫ ψ₀.left → g₁ ≫ ψ.left = g₂ ≫ ψ.left :=
    fun g₁ g₂ hg => by
      rw [← pullback.lift_fst g₁ g₂ hg, Category.assoc, e', pullback.lift_snd_assoc]
  have f := EffectiveEpi.fac ψ₀.left ψ.left hd
  refine ⟨Over.homMk (EffectiveEpi.desc ψ₀.left ψ.left hd) ?_, Over.OverMorphism.ext f⟩
  rw [← cancel_epi ψ₀.left, reassoc_of% f, Over.w, Over.w]

theorem isIso_of_mono {A B : Over (Sp k)} (α : A ⟶ B) [IsProper A.hom] [IsSeparated B.hom] (hB : Smooth B.hom)
    [Mono α.left] (h : ∀ y : 𝟙_ (Over (Sp k)) ⟶ B, ∃ x, x ≫ α = y) : IsIso α := by
  have := (isReduced_isNormalScheme_isLocallyNoetherian_of_smooth_over_field k _ B.hom hB).1
  have : IsProper (α.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper α.left := IsProper.of_comp α.left B.hom
  have : IsClosedImmersion α.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : Surjective α.left := ComplexPoints.surjective_of_geomPoints_lift B.hom (𝟙 (Sp k)) α.left
    α.left.isClosedEmbedding.isClosed_range fun y hy => by
      obtain ⟨x, hx⟩ := h (Over.homMk y hy)
      exact ⟨x.left, congrArg (fun q => q.left) hx⟩
  have : IsIso α.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map α) := ‹_›
  exact isIso_of_reflects_iso α (Over.forget _)


omit [IsAlgClosed k] in
theorem toUnit_comp_injective {K : Type} [Field K] (x : Sp K ⟶ Sp k) (A : Over (Sp k)) :
    Function.Injective (fun z : 𝟙_ (Over (Sp k)) ⟶ A => toUnit (Over.mk x) ≫ z) := by
  have : Surjective x := ⟨fun z => ⟨(default : PrimeSpectrum K), Subsingleton.elim (α := PrimeSpectrum k) _ _⟩⟩
  have : Epi x := Flat.epi_of_flat_of_surjective x
  intro a b h
  have e : (toUnit (Over.mk x)).left = x := by simp
  have h' : (toUnit (Over.mk x)).left ≫ a.left = (toUnit (Over.mk x)).left ≫ b.left := congrArg (fun q => q.left) h
  rw [e] at h'
  exact Over.OverMorphism.ext ((cancel_epi x).1 h')

theorem exists_of_torsion (hM : Out.MulNSt) (P : Out.PolAV (Sp k)) {K : Type} [Field K] [IsAlgClosed K]
    (x : Sp K ⟶ Sp k) {n : ℕ} (hk : (n : k) ≠ 0) (hK : (n : K) ≠ 0) (z : Over.mk x ⟶ P.A) (hz : z ^ n = 1) :
    ∃ z₀ : 𝟙_ (Over (Sp k)) ⟶ P.A, toUnit (Over.mk x) ≫ z₀ = z := by
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact hk Nat.cast_zero)
  have c₁ : Nat.card {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} = n ^ (2 * P.g) := (hM _ P n hn).2.2.2.2 k (𝟙 _) hk
  have c₂ := (hM _ P n hn).2.2.2.2 K x hK
  have : Finite {y : Over.mk x ⟶ P.A // y ^ n = 1} := Nat.finite_of_card_ne_zero (by rw [c₂]; positivity)
  let F : {x : 𝟙_ (Over (Sp k)) ⟶ P.A // x ^ n = 1} → {y : Over.mk x ⟶ P.A // y ^ n = 1} := fun a =>
    ⟨toUnit _ ≫ a.1, by rw [← MonObj.comp_pow, a.2, MonObj.comp_one]⟩
  have hF : Function.Bijective F := (Nat.bijective_iff_injective_and_card F).2
    ⟨fun a b h => Subtype.ext (toUnit_comp_injective x _ (congrArg Subtype.val h)), c₁.trans c₂.symm⟩
  obtain ⟨a, ha⟩ := hF.2 ⟨z, hz⟩
  exact ⟨a.1, congrArg Subtype.val ha⟩

end Pts

theorem exists_ptsEquiv {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G'] {f : S' ⟶ S}
    {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) (T : Over S') (y : T.left ⟶ S) (e : T.hom ≫ f = y) :
    ∃ ρ : (T ⟶ G') ≃* (Over.mk y ⟶ G), ∀ x, (ρ x).left = x.left ≫ φ := by
  subst e
  refine ⟨MulEquiv.ofBijective (pushHom h T) ⟨fun a b e => Over.OverMorphism.ext
    (h.1.hom_ext (congrArg (fun q => q.left) e) (by rw [Over.w, Over.w])), fun z => ?_⟩, fun _ => rfl⟩
  exact ⟨Over.homMk (h.1.lift z.left T.hom (Over.w z)) (h.1.lift_snd _ _ _), Over.OverMorphism.ext (h.1.lift_fst _ _ _)⟩

theorem unitOn_bijective (R : Type) [CommRing R] : Function.Bijective (unitOn (R := R)) :=
  (Units.mapEquiv (Scheme.ΓSpecIso (CommRingCat.of R)).symm.commRingCatIsoToRingEquiv.toMulEquiv).bijective

theorem unitOn_pow {R : Type} [CommRing R] (c : Rˣ) (n : ℕ) : unitOn (c ^ n) = unitOn c ^ n := map_pow _ _ _

theorem unitOn_one {R : Type} [CommRing R] : unitOn (1 : Rˣ) = 1 := map_one _

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem isAbelianScheme_of_proper {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) : IsAbelianScheme t.G :=
  ⟨inferInstance, t.semi.smooth, hp, t.semi.geomConnected⟩

theorem exists_dim {k : Type} [Field k] (t : SAB H (Sp k)) : ∃ g, SmoothOfRelativeDimension g t.G.hom := by
  have := t.semi.smooth
  have := t.semi.geomConnected
  have : ConnectedSpace t.G.left :=
    GeometricallyConnected.geometrically_connectedSpace (f := t.G.hom) (𝟙 _) (𝟙 _) t.G.hom
      (IsPullback.of_horiz_isIso ⟨by simp⟩)
  exact exists_dim_of_preconnected t.G.hom (eSec t.G (default : PrimeSpectrum k))

abbrev polOf {S : Scheme.{0}} (t : SAB H S) (hp : IsProper t.G.hom) (ha : Out.RelAmple t.G t.PP.L)
    (hk : Out.KTriv t.G t.PP.L) {g : ℕ} (hg : SmoothOfRelativeDimension g t.G.hom) : Out.PolAV S where
  A := t.G
  isAb := isAbelianScheme_of_proper t hp
  g := g
  smoothDim := hg
  L := t.PP.L
  isLB := t.PP.isLB
  rigid := ⟨t.PP.rig, t.PP.rigGen⟩
  sym := fun _ => ⟨⊤, trivial, by
    obtain ⟨-, ws, gs', -⟩ := t.sym
    exact gen_of_iso ((isGen_iff ws).1 gs') _⟩
  ample := ha
  ktriv := hk

end GlobalTheory.HeckePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsPullCubicalOfIso
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.HeckePoint

open TopologicalSpace

theorem exists_unit_ratio {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K] {φ : K → (Y ⟶ X)}
    {ε : K → ℤ} (a b : LB.Gen (LB.LinComb L φ ε)) (ha : a.IsGen) (hb : b.IsGen) :
    ∃ u : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι), r z ∈ LB.wchart L φ q →
      gm r z (LB.wchart L φ q) (a.s q) = gm r z ⊤ u * gm r z (LB.wchart L φ q) (b.s q) := by
  have v : ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (q : K → L.ι),
      gm r z (LB.wchart L φ q) (a.s q * (b.s q)⁻¹) =
        gm r z (LB.wchart L φ q) (a.s q) * (gm r z (LB.wchart L φ q) (b.s q))⁻¹ := fun Z r z q =>
    (map_mul _ _ _).trans (congrArg _ (map_inv _ _))
  obtain ⟨u, hu⟩ := glue_unit ⊤ (LB.wchart L φ) (fun _ => le_top) (fun y _ => by
      choose q hq using fun k => exists_chart hL (φ k y)
      exact Opens.mem_iSup.2 ⟨q, Set.mem_iInter.2 hq⟩) (fun q => a.s q * (b.s q)⁻¹) (fun q q' y hy => by
      refine (v _ _ y q).trans (Eq.trans ?_ (v _ _ y q').symm)
      rw [gen_trans ha (𝟙 Y) y hy.1 hy.2, gen_trans hb (𝟙 Y) y hy.1 hy.2, mul_inv, _root_.mul_mul_mul_comm,
        mul_inv_cancel, _root_.one_mul])
  refine ⟨u, fun Z r z q hq => ?_⟩
  rw [← gm_res r z (le_top : LB.wchart L φ q ≤ ⊤) hq u, hu q]
  exact ((congrArg (· * _) (v Z r z q)).trans (inv_mul_cancel_right _ _)).symm

theorem isPullCubical_of_iso (hG : Out.GlobalFnsSt) {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [IsCommMonObj G']
    [GrpObj G] [IsCommMonObj G] (hA : IsAbelianScheme G') (α : G' ⟶ G) [IsMonHom α] {L' : RigLB G'} {L : RigLB G}
    (c' : CubicalStr G' L') (c : CubicalStr G L) (h : LBIso L'.L (L.L.pull α.left)) :
    (CubeMap.ofHom α).IsPullCubical c' c := by
  obtain ⟨w, hw⟩ := h
  have hw' := (isGen_iff w).1 hw
  obtain ⟨a, ha, hm⟩ := DegPull.exists_pmaps (K := PUnit) hw' L.isLB L'.isLB (φ' := fun _ => eSec G')
    (φ := fun _ => eSec G) (ε := fun _ => 1) (𝟙 _) (fun _ => (CubeMap.ofHom α).e_comm) L.rig L.rigGen
  obtain ⟨u, hu⟩ := exists_unit_ratio L'.isLB a L'.rig ha L'.rigGen
  let w₁ : LB.Iso L'.L (L.L.pull α.left) :=
    ⟨fun p => w.s p * res (U := G'.hom ⁻¹ᵁ ⊤) (fun _ _ => trivial) (pullU G'.hom ⊤ u)⟩
  have g₁ : ∀ (Y : Scheme.{0}) (f : Y ⟶ G'.left) (y : Y) j k, α.left (f y) ∈ L.L.U j → f y ∈ L'.L.U k →
      gw w₁ f y j k = gw w f y j k * gm (f ≫ G'.hom) y ⊤ u := fun Y f y j k hj hk =>
    (map_mul _ _ _).trans (congrArg _ ((gm_res f y _ (show f y ∈ (L.L.pull α.left).U (fun _ => j) ⊓ L'.L.U k from
      ⟨mem_pull.2 hj, hk⟩) _).trans (gm_pull f G'.hom y ⊤ trivial u)))
  have hw₁ : PGen w₁ := fun Y f y j j' k k' hj hj' hk hk' => by
    rw [g₁ Y f y j k hj hk, g₁ Y f y j' k' hj' hk', hw' Y f y j j' k k' hj hj' hk hk', _root_.mul_assoc]
  refine (isPullCubical_iff _ c c').2 ⟨w₁, hw₁, fun Z r z p q hp hq => ?_, ?_⟩
  · refine (hm Z r z p q hp hq).trans ?_
    have e : (r ≫ eSec G') ≫ G'.hom = r := by
      rw [Category.assoc, show eSec G' ≫ G'.hom = 𝟙 _ from Over.w η[G'], Category.comp_id]
    have e₂ := g₁ Z (r ≫ eSec G') z _ _ (hp default) (hq default)
    rw [e] at e₂
    rw [hu Z r z q (Set.mem_iInter.2 hq), Fintype.prod_unique, Fintype.prod_unique, zpow_one, zpow_one]
    exact (_root_.mul_assoc _ _ _).symm.trans (congrArg (· * _) e₂.symm)
  · let e : 𝟙_ (Over S) ⟶ G3 G' := lift 1 (lift 1 1)
    have s₁ := (hG _ _ hA).2
    have hψ : ∀ I : thK, thφ G' (x3 G') I ≫ α.left = (CubeMap.ofHom α).F3 ≫ thφ G (x3 G) I :=
      fun I => (CubeMap.ofHom α).psum_comm I.down
    refine EvenPull.pmaps_of_section (φ' := thφ G' (x3 G')) (φ := thφ G (x3 G)) (ε := thε) hw₁ L.isLB L'.isLB
      (CubeMap.ofHom α).F3 hψ c'.t c'.isGen
      c.t c.isGen (G3 G').hom e.left (Over.w e) (AbLaw.Cube.surj_tensor hG hA (AbLaw.Cube.surj_tensor hG hA s₁))
      (fun y J J' hJ hJ' => ?_)
    have a₁ : e.left ≫ (CubeMap.ofHom α).F3 = (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left := by
      show (e ≫ (α ⊗ₘ α ⊗ₘ α)).left = _
      simp only [e, lift_map, MonObj.one_comp]
    have b₁ : val c.t (lift (1 : 𝟙_ (Over S) ⟶ G) (lift 1 1)).left y J = 1 := by
      have v := val_corr hJ (c.face 0) (lift (1 : 𝟙_ (Over S) ⟶ G) 1).left
      rw [val_one] at v
      have vp := val_pull (φ := thφ G (x3 G)) (ε := thε) hJ c.t (faceMap G 0).left (lift (1 : 𝟙_ (Over S) ⟶ G) 1).left
      rw [vp] at v
      have eq : (lift (1 : 𝟙_ (Over S) ⟶ G) 1) ≫ faceMap G 0 = lift 1 (lift 1 1) := by
        simp [faceMap, x2, pzero, comp_lift, Hom.one_def]
      rw [← Over.comp_left, eq] at v
      exact v
    have b₂ : val c'.t (lift (1 : 𝟙_ (Over S) ⟶ G') (lift 1 1)).left y J' = 1 := by
      have v := val_corr hJ' (c'.face 0) (lift (1 : 𝟙_ (Over S) ⟶ G') 1).left
      rw [val_one] at v
      have vp := val_pull (φ := thφ G' (x3 G')) (ε := thε) hJ' c'.t (faceMap G' 0).left (lift (1 : 𝟙_ (Over S) ⟶ G') 1).left
      rw [vp] at v
      have eq : (lift (1 : 𝟙_ (Over S) ⟶ G') 1) ≫ faceMap G' 0 = lift 1 (lift 1 1) := by
        simp [faceMap, x2, pzero, comp_lift, Hom.one_def]
      rw [← Over.comp_left, eq] at v
      exact v
    have b₃ := prod_cub (1 : 𝟙_ (Over S) ⟶ G') 1 1 (fun ψ => gw w₁ ψ y (J (ψ ≫ α.left)) (J' ψ))
    refine Eq.trans ((congrArg (fun q => val (L := L.L) (φ := thφ G (x3 G)) (ε := thε) c.t q y J) a₁).trans b₁)
      (Eq.symm ?_)
    refine (congrArg₂ (· * ·) b₃ b₂).trans ?_
    simp

theorem mono_of_kTriv {S : Scheme.{0}} {G' G : Over S} [GrpObj G'] [GrpObj G] (α : G' ⟶ G) [IsMonHom α]
    {L' : LB G'.left} {L : LB G.left} (hL' : L'.IsLB) (hL : L.IsLB) (h : LBIso L' (L.pull α.left))
    (hK : Out.KTriv G' L') : Mono α.left := by
  obtain ⟨w, hw⟩ := h
  have key : ∀ (R : Type) [CommRing R] (t : Sp R ⟶ S) (x : Over.mk t ⟶ G'), x ≫ α = 1 → x = 1 := by
    intro R _ t x hx
    refine hK R t x fun p => ⟨⊤, trivial, ?_⟩
    let φ' : Fin 2 → ((Over.mk t ⊗ G').left ⟶ G'.left) :=
      ![(lift (fst (Over.mk t) G' ≫ x) (snd (Over.mk t) G') ≫ μ[G']).left, (snd (Over.mk t) G').left]
    have e : φ' 0 ≫ α.left = φ' 1 ≫ α.left := by
      show (((fst (Over.mk t) G' ≫ x) * snd (Over.mk t) G') ≫ α).left = (snd (Over.mk t) G' ≫ α).left
      rw [MonObj.mul_comp, Category.assoc, hx, MonObj.comp_one, _root_.one_mul]
    obtain ⟨t₁, h₁, -⟩ := exists_gen hL (φ' := fun k => φ' k ≫ α.left) (ε' := ![1, -1]) (fun U _ k => by
      rw [Fin.prod_univ_two]; simp [e]) (LB.oneGen L (Y := (Over.mk t ⊗ G').left)) AbLaw.Cube.oneGen_isGen
    obtain ⟨t₂, h₂⟩ := exists_down ((isGen_iff w).1 hw) hL hL' t₁ h₁
    exact gen_chartPull (chartPullPull _ _ _ rfl) t₂ h₂
  refine ⟨fun {Z} f g hfg => ?_⟩
  refine Scheme.Cover.hom_ext Z.affineCover _ _ fun i => ?_
  have hs : g ≫ G'.hom = f ≫ G'.hom := by rw [← Over.w α, reassoc_of% hfg]
  let j : Spec (CommRingCat.of (Z.affineOpenCover.X i)) ⟶ Z := Z.affineCover.f i
  let x : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ f) (Category.assoc _ _ _)
  let y : Over.mk (j ≫ f ≫ G'.hom) ⟶ G' := Over.homMk (j ≫ g) (by rw [Category.assoc, hs]; rfl)
  have e : x ≫ α = y ≫ α := Over.OverMorphism.ext (by
    show (j ≫ f) ≫ _ = (j ≫ g) ≫ _
    rw [Category.assoc, hfg, Category.assoc])
  have := key _ _ (x * y⁻¹) (by rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel])
  exact congrArg (fun q => q.left) (mul_inv_eq_one.1 this)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem iso_of_lam {S : Scheme.{0}} (t' t : SAB H S) (α : t'.G ⟶ t.G) [IsMonHom α]
    (hact : ∀ a, t'.act.act a ≫ α = α ≫ t.act.act a)
    (h : LBIso (abelian₂ t'.G (lbPow t'.PP.L 1)) (abelian₂ t'.G (t.PP.L.pull α.left))) :
    LBIso t'.PP.L (t.PP.L.pull α.left) := by
  let U : t'.G ⟶ G2 t'.G := lift (𝟙 _) (t'.act.act H.w0)
  have ps : ∀ I : Finset (Fin 2), U ≫ psum t'.G (x2 t'.G) I = psum t'.G ![𝟙 _, t'.act.act H.w0] I := fun I =>
    (psum_hom (preHom U) (x2 t'.G) I).trans (congrArg (fun q => psum t'.G q I) (funext fun i => by
      fin_cases i <;> simp [preHom, U, x2]))
  have pa : ∀ I : Finset (Fin 2), psum t'.G ![𝟙 _, t'.act.act H.w0] I ≫ α = α ≫ psum t.G ![𝟙 _, t.act.act H.w0] I :=
    fun I => (psum_hom (MonoidHom.mk' (fun z : t'.G ⟶ t'.G => z ≫ α) fun a b => MonObj.mul_comp a b α) _ I).trans
      ((congrArg (fun q => psum t.G q I) (funext fun i => by
        fin_cases i <;> simp [preHom, hact])).trans (psum_hom (preHom α) ![𝟙 _, t.act.act H.w0] I).symm)
  have h₁ : LBIso (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (lbPow t'.PP.L 1))
      (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm)
      (chartPullSame _ _ _ _ U.left fun I => congrArg (fun q => q.left) (ps I.down).symm) h
  have h₂ : LBIso (t'.PP.L.pull (𝟙 _)) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t'.PP.L.pull (𝟙 _))) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ (𝟙 _) fun I => by simp) t'.prim
  have h₃ : LBIso (t.PP.L.pull α.left) (cubeLB t'.G ![𝟙 _, t'.act.act H.w0] (t.PP.L.pull α.left)) :=
    LBIso.chartPull (chartPullPull _ _ _ rfl) (chartPullLinComb _ _ _ _ _ α.left fun I =>
      congrArg (fun q => q.left) (pa I.down)) t.prim
  have i₁ : (t'.PP.L.pull (𝟙 _)).IsLB := DVR.linComb_isLB _ t'.PP.isLB _ _
  have i₂ : (t.PP.L.pull α.left).IsLB := DVR.linComb_isLB _ t.PP.isLB _ _
  have h₄ := LBIso.trans i₁ (DVR.linComb_isLB _ i₂ _ _) i₂
    (LBIso.trans i₁ (DVR.linComb_isLB _ i₁ _ _) (DVR.linComb_isLB _ i₂ _ _) h₂ h₁) h₃.symm
  exact LBIso.chartPull (chartPullUnpull _ _ rfl) (chartPullId _) h₄

theorem pow_eq_one_of_weilIs (hK : Out.KerPowSt) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : Out.PolAV S)
    {T : Over S} [Unique T.left] {n : ℕ} (hn : 0 < n) {x y : T ⟶ P.A} {c : Γ(T.left, ⊤)ˣ}
    (h : Out.WeilIs P.A P.L n x y c) : x ^ n = 1 ∧ y ^ n = 1 := by
  obtain ⟨V, hV, ⟨θx, θy, hx, hy⟩, -⟩ := h default
  have key : ∀ θ : Out.ThetaGrp P.A P.L n (Out.overRes V), θ.pt ^ n = 1 := fun θ =>
    (hK S P n hn _ θ.pt).1 fun p => ⟨⊤, trivial, gen_chartPull (chartPullPull _ _ _ rfl) θ.φ θ.isGen⟩
  have hs : Surjective V.ι := ⟨fun z => ⟨⟨default, hV⟩, Subsingleton.elim _ _⟩⟩
  have he : Epi V.ι := Flat.epi_of_flat_of_surjective _
  have key₂ : ∀ z : T ⟶ P.A, (Out.overResι V ≫ z) ^ n = 1 → z ^ n = 1 := fun z hz => by
    rw [← MonObj.comp_pow, ← MonObj.comp_one (Out.overResι V)] at hz
    exact Over.OverMorphism.ext ((cancel_epi V.ι).1 (congrArg (fun q => q.left) hz))
  exact ⟨key₂ x (hx ▸ key θx), key₂ y (hy ▸ key θy)⟩

end GlobalTheory.HeckePoint
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SymmetricLocalOnBaseCover
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.CoverGlue

theorem sym_inv_comm {S S' : Scheme.{0}} {G : Over S} {G' : Over S'} [GrpObj G] [GrpObj G']
    {f : S' ⟶ S} {φ : G'.left ⟶ G.left} (h : IsGrpPullback G' G f φ) :
    (GrpObj.inv : G' ⟶ G').left ≫ φ = φ ≫ (GrpObj.inv : G ⟶ G).left := by
  have e := congrArg (fun z => z.left) (map_inv (pushHom h G') (𝟙 G'))
  have e₁ : (𝟙 G' : G' ⟶ G')⁻¹ = GrpObj.inv := by rw [Hom.inv_def, Category.id_comp]
  rw [e₁, Hom.inv_def] at e
  refine e.trans ?_
  show ((𝟙 G' : G' ⟶ G').left ≫ φ) ≫ _ = _
  rw [Over.id_left, Category.id_comp]

theorem sym_of_cover (S : Scheme.{0}) (I : Type) (U : I → S.Opens) (A : Over S) [GrpObj A]
    (G : ∀ i, Over (U i).toScheme) [∀ i, GrpObj (G i)] (ψ : ∀ i, (G i).left ⟶ A.left) (hU : iSup U = ⊤)
    (hψ : ∀ i, IsGrpPullback (G i) A (U i).ι (ψ i)) (L : LB A.left) (M : ∀ i, LB (G i).left) (hL : L.IsLB)
    (hM : ∀ i, (M i).IsLB) (hw : ∀ i, LBIso (M i) (L.pull (ψ i))) (hs : ∀ i, Out.Sym (G i) (M i)) :
    Out.Sym A L := by
  intro s
  obtain ⟨i, hi⟩ : ∃ i, s ∈ U i := TopologicalSpace.Opens.mem_iSup.1 (by rw [hU]; trivial)
  obtain ⟨V, hV, c, hc⟩ := hs i ⟨s, hi⟩
  obtain ⟨w, hw⟩ := hw i
  refine ⟨(U i).ι ''ᵁ V, ⟨⟨s, hi⟩, hV, rfl⟩, ?_⟩
  have hp := (hψ i).1

  obtain ⟨b, hb⟩ : ∃ b : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ V.toScheme,
      b ≫ V.ι ≫ (U i).ι = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom :=
    ⟨IsOpenImmersion.lift (V.ι ≫ (U i).ι) _ (by
      rintro _ ⟨y, rfl⟩
      obtain ⟨z, hz, e⟩ := y.2
      exact ⟨⟨z, hz⟩, e⟩), IsOpenImmersion.lift_fac _ _ _⟩
  have sq : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι ≫ A.hom = (b ≫ V.ι) ≫ (U i).ι := by rw [Category.assoc, hb]
  let m := hp.lift _ _ sq
  have m₁ : m ≫ ψ i = (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι := hp.lift_fst _ _ _
  have m₂ : m ≫ (G i).hom = b ≫ V.ι := hp.lift_snd _ _ _
  obtain ⟨n, hn⟩ : ∃ n : (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).toScheme ⟶ ((G i).hom ⁻¹ᵁ V).toScheme,
      n ≫ ((G i).hom ⁻¹ᵁ V).ι = m :=
    ⟨IsOpenImmersion.lift _ m (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      exact (congrArg (fun q => q y ∈ V) m₂).mpr (b y).2), IsOpenImmersion.lift_fac _ _ _⟩
  obtain ⟨c₂, h₂, -⟩ := exists_up ((isGen_iff w).1 hw) hL (hM i) c hc
  refine gen_chartPull (chartPullSame L _ _ _ n fun k => ?_) c₂ h₂
  fin_cases k
  · show _ ≫ _ = n ≫ (_ ≫ _) ≫ ψ i
    rw [Category.assoc, sym_inv_comm (hψ i), ← Category.assoc n, hn, ← Category.assoc m, m₁]
  · show (A.hom ⁻¹ᵁ ((U i).ι ''ᵁ V)).ι = n ≫ ((G i).hom ⁻¹ᵁ V).ι ≫ ψ i
    rw [← Category.assoc n, hn, m₁]

end GlobalTheory.CoverGlue
end

