module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0012
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
public import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.GenericExistsUniqueOActOfIsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0107
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0100
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0192
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0112
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0101
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0113
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0028
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0191
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0129
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0035
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0033
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0134
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
public import Development.AutomorphicSpectrum.Proofs.GeometryProofs.Bundle0040
public import GroundTheory.HeightsAndTheta.Heights.IntegralModels.Bundle0004

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianFiniteCoverTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open scoped CategoryTheory.Obj

namespace GlobalTheory.CompanionTheory.Ar.StratOpen

theorem charZero_of_point {k : Type} [Field k] (x : Sp k ⟶ Sp ℚ) : CharZero k :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

theorem core (hE : GlobalTheory.Published.SemiAbelianHomExtension) (Z : Scheme.{0}) [IsIntegral Z] [AlgebraicGeometry.IsNoetherian Z]
    (s : Z ⟶ Sp ℚ) (G : Over Z) [GrpObj G] (hG : IsSemiAbelian G) (g : ℕ) (hg : SmoothOfRelativeDimension g G.hom)
    (Z' : Scheme.{0}) [IsIntegral Z'] (π : Z' ⟶ Z) (hfin : IsFinite π) (hsurj : Surjective π) (hnorm : ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z')
    (L' : Type) [Field L'] (j : Sp L' ⟶ Z') (hj : GlobalTheory.IsGenericPointHom j)
    (τ : TorusExtension ((Over.pullback (j ≫ π)).obj G)) (m : ℕ) (P : Fin m → (Over.mk (j ≫ π) ⟶ G))
    (hPi : Function.Injective P) (hP2 : ∀ i, P i ^ 2 = 1)
    (hcount : letI := τ.addCommGroup; m * 2 ^ Module.finrank ℤ τ.X = 2 ^ (2 * g)) :
    ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  have hsm := hG.smooth
  have hsep := hG.separated
  have hG' : IsSemiAbelian ((Over.pullback π).obj G) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · have := hG.comm
      infer_instance
    · have := hG.smooth
      change Smooth (pullback.snd G.hom π)
      infer_instance
    · have := hG.separated
      change IsSeparated (pullback.snd G.hom π)
      infer_instance
    · have := hG.quasiCompact
      change QuasiCompact (pullback.snd G.hom π)
      infer_instance
    · have := hG.geomConnected
      change GeometricallyConnected (pullback.snd G.hom π)
      infer_instance
    · intro Ω _ _ q
      obtain ⟨E⟩ := hG.fibres Ω (q ≫ π)
      exact ⟨torusExtOfIso (pullCompIso q π G) E⟩
  have hsep' := hG'.separated
  have hLN : IsLocallyNoetherian Z' := LocallyOfFiniteType.isLocallyNoetherian π
  have hCS : CompactSpace Z' := QuasiCompact.compactSpace_of_compactSpace π
  have hN' : AlgebraicGeometry.IsNoetherian Z' := {}
  let τ' : TorusExtension ((Over.pullback j).obj ((Over.pullback π).obj G)) := torusExtOfIso (pullCompIso j π G) τ
  letI := τ'.addCommGroup
  haveI := τ'.free
  haveI := τ'.finite
  obtain ⟨u, hu, hmono⟩ := GlobalTheory.T.torus_extension_split_map hE Z' hnorm ((Over.pullback π).obj G) hG' L' j hj τ'
  obtain ⟨V₁, hV₁, hC⟩ := _root_.GlobalTheory.CompanionTheory.Ar.KerSpread.injective_on_points_of_generic Z' ((Over.pullback π).obj G) τ'.X u L' j hj hmono
  obtain ⟨V₂, hV₂, hD⟩ := _root_.GlobalTheory.CompanionTheory.Ar.pts_spread Z' Z π G L' j hj m P hPi hP2
  have hVne : ((V₁ ⊓ V₂ : Z'.Opens) : Set Z').Nonempty :=
    nonempty_preirreducible_inter V₁.isOpen V₂.isOpen hV₁ hV₂
  obtain ⟨U, hU, hUV⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Strat.preimage_le_of_finite_surjective Z Z' π hfin hsurj (V₁ ⊓ V₂) hVne
  have hm : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · exact absurd hcount.symm (by simp)
    · exact h
  refine ⟨Z', inferInstance, π, (Over.pullback π).obj G, inferInstance, pullback.fst G.hom π, τ'.X, τ'.addCommGroup, τ'.free, τ'.finite, u, U, hfin, hsurj, hnorm, isGrpPullback_pullback G π, hu, hU, ?_⟩
  intro k _ x hx
  have hxV : ∀ W : Z'.Opens, V₁ ⊓ V₂ ≤ W → ⊤ ≤ x ⁻¹ᵁ W := fun W hW y _ => hW (hUV (hx trivial))
  have mono : ∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' τ'.X), t ≫ u = 1 → t = 1 := by
    intro A _ g t ht
    refine hC A (spMap g ≫ x) (fun y _ => ?_) t ht
    have h1 := hxV V₁ inf_le_left (show (spMap g) y ∈ (⊤ : (Sp k).Opens) from trivial)
    simpa using h1
  refine ⟨mono, ?_⟩
  intro Gk _ ψ hψ τk
  letI := τk.grpB
  letI := τk.addCommGroup
  haveI := τk.free
  haveI := τk.finite
  obtain ⟨Q, hQi, hQ2⟩ := hD k x (hxV V₂ inf_le_right)
  have h2 : ((2 : ℕ) : k) ≠ 0 := by
    haveI : CharZero k := charZero_of_point (x ≫ π ≫ s)
    exact Nat.cast_ne_zero.2 two_ne_zero
  have hle := GlobalTheory.T.two_torsion_card_bound Z G hG g hg k h2 (x ≫ π) Gk (ψ ≫ pullback.fst G.hom π) (hψ.comp (isGrpPullback_pullback G π)) τk m Q hQi hQ2
  have hrk : Module.finrank ℤ τk.X ≤ Module.finrank ℤ τ'.X := by
    have h3 : m * 2 ^ Module.finrank ℤ τk.X ≤ m * 2 ^ Module.finrank ℤ τ'.X := hle.trans hcount.ge
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 (Nat.le_of_mul_le_mul_left h3 hm)
  intro A _ gg p
  exact GlobalTheory.T.torus_extension_rank_bound Z' ((Over.pullback π).obj G) τ'.X u k x mono Gk ψ hψ τk hrk A gg p

theorem strat_open : GlobalTheory.Published.SemiAbelianHomExtension → ∀ (Z : Scheme.{0}) [IsIntegral Z] (s : Z ⟶ Sp ℚ) [LocallyOfFiniteType s] [QuasiCompact s] (G : Over Z) [GrpObj G], IsSemiAbelian G → ∃ (Z' : Scheme.{0}) (_ : IsIntegral Z') (π : Z' ⟶ Z) (G' : Over Z') (_ : GrpObj G') (φ : G'.left ⟶ G.left) (X : Type) (_ : AddCommGroup X) (_ : Module.Free ℤ X) (_ : Module.Finite ℤ X) (u : splitTorus Z' X ⟶ G') (U : Z.Opens), IsFinite π ∧ Surjective π ∧ ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme Z' ∧ IsGrpPullback G' G π φ ∧ IsMonHom u ∧ (U : Set Z).Nonempty ∧ ∀ (k : Type) [Field k] (x : Sp k ⟶ Z'), ⊤ ≤ (x ≫ π) ⁻¹ᵁ U → (∀ (A : Type) [CommRing A] (g : k →+* A) (t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X), t ≫ u = 1 → t = 1) ∧ ∀ (Gk : Over (Sp k)) [GrpObj Gk] (ψ : Gk.left ⟶ G'.left), IsGrpPullback Gk G' x ψ → ∀ τ : TorusExtension Gk, letI := τ.grpB; ∀ (A : Type) [CommRing A] (g : k →+* A) (p : Over.mk (spMap g) ⟶ Gk), p ≫ τ.q = 1 ↔ ∃ t : Over.mk (spMap g ≫ x) ⟶ splitTorus Z' X, (t ≫ u).left = p.left ≫ ψ := by
  intro hE Z _ s _ _ G _ hG
  have hLN : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian s
  have hCS : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace s
  have hN : AlgebraicGeometry.IsNoetherian Z := {}
  have hsm := hG.smooth
  have hsep := hG.separated
  have hfq := hG.quasiCompact
  let z : Sp Z.functionField ⟶ Z := Z.fromSpecStalk (genericPoint Z)
  have hz : GlobalTheory.IsGenericPointHom z := GlobalTheory.IsGenericPointHom.fromSpecStalk Z
  haveI : CharZero Z.functionField := charZero_of_point (z ≫ s)
  obtain ⟨g, hg⟩ := GlobalTheory.CompanionTheory.Ar.RootHt.ArchB.smoothGrp_relDim Z Z.functionField z G (fun q => by
    have : genPt z = genericPoint Z := by
      have := hz.range_eq
      have h2 : genPt z ∈ Set.range z := ⟨_, rfl⟩
      rw [this] at h2
      exact h2
    rw [this]
    exact genericPoint_specializes q)
  obtain ⟨L', _, _, hfd, hB⟩ := GlobalTheory.T.torus_extension_two_torsion Z G hG g hg Z.functionField z
  obtain ⟨Z', _, π, j, hfin, hsurj, hnorm, hj, hjπ⟩ := _root_.GlobalTheory.CompanionTheory.Ggeo.normalisation_finite_cover Z s Z.functionField z hz L'
  rw [← hjπ] at hB
  obtain ⟨τ, m, P, hPi, hP2, hcount⟩ := hB
  exact core hE Z s G hG g hg Z' π hfin hsurj hnorm L' j hj τ m P hPi hP2 hcount

end GlobalTheory.CompanionTheory.Ar.StratOpen
end

-- bundled from Development.AutomorphicSpectrum.Proofs.GeometryProofs.SemiabelianLieLatticeAgree
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.LieStalk

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.LieStalk

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X}

theorem exists_model (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    ∃ (Ep : Type) (_ : AddCommGroup Ep) (_ : Module (regAt ξ p) Ep) (Mp : LieModel G (regPt h p) Ep)
      (j : Ep →ₗ[regAt ξ p] E), IsBaseChange Ω j ∧
        ∀ e, (M.pt (j e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange X G (regAt ξ p) Ω (regPt h p) E
    (castPt (spMap_algebraMap_regPt h p).symm M)
  exact ⟨Ep, i1, i2, Mp, j, hb, fun e =>
    (castPt_pt_left (spMap_algebraMap_regPt h p).symm M (j e)).symm.trans (hj e)⟩

theorem lat_fin (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (p : Cpt ξ) :
    Module.Finite (regAt ξ p) (M.lat p) ∧ Module.Projective (regAt ξ p) (M.lat p) ∧
      Submodule.span Ω (M.lat p : Set E) = ⊤ := by
  obtain ⟨Ep, i1, i2, Mp, j, hb, hj⟩ := exists_model h G M p
  have hr := _root_.GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range X Ω ξ h G E M p Ep Mp j hj
  obtain ⟨hf, hp⟩ := _root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective X G (regAt ξ p) (regPt h p) Ep Mp
  haveI := _root_.GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt X Ω ξ h p
  have hl : IsLocalizedModule (nonZeroDivisors (regAt ξ p)) j :=
    (isLocalizedModule_iff_isBaseChange (nonZeroDivisors (regAt ξ p)) Ω j).mpr hb
  have hinj : Function.Injective j := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro m hm
    obtain ⟨c, hc⟩ := (IsLocalizedModule.eq_zero_iff (nonZeroDivisors (regAt ξ p)) j).1 hm
    have hreg := Module.Flat.isSMulRegular_of_nonZeroDivisors (M := Ep) c.2
    exact hreg (show (c : regAt ξ p) • m = (c : regAt ξ p) • 0 by rw [smul_zero]; exact hc)
  have hMeq : M.lat p = LinearMap.range j := SetLike.coe_injective (hr.trans (LinearMap.coe_range j).symm)
  let e : Ep ≃ₗ[regAt ξ p] M.lat p := (LinearEquiv.ofInjective j hinj).trans (LinearEquiv.ofEq _ _ hMeq.symm)
  refine ⟨Module.Finite.equiv e, Module.Projective.of_equiv e, ?_⟩
  rw [eq_top_iff]
  intro v _
  refine hb.inductionOn v (motive := fun v => v ∈ Submodule.span Ω (M.lat p : Set E)) (fun m => ?_)
    (fun s n hn => Submodule.smul_mem _ s hn) (fun a b ha hb => add_mem ha hb)
  exact Submodule.subset_span (by rw [hr]; exact ⟨m, rfl⟩)

theorem dualMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    (dualMap g).comp (dualMap f) = dualMap (g.comp f) := by
  apply RingHom.ext
  intro a
  ext <;> simp [dualMap]

theorem lat_gen (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1) :
    M.lat q = Submodule.span (regAt ξ q) (M.lat p : Set E) := by
  obtain ⟨Eq, i1, i2, Mq, jq, hbq, hjq⟩ := exists_model h G M q
  letI : Algebra (regAt ξ p) (regAt ξ q) := (regIncl hs).toAlgebra
  letI : Module (regAt ξ p) Eq := Module.compHom Eq (regIncl hs)
  haveI : IsScalarTower (regAt ξ p) (regAt ξ q) Eq := ⟨fun a b c => by
    change (regIncl hs a * b) • c = regIncl hs a • (b • c)
    rw [mul_smul]⟩
  obtain ⟨Ep, i3, i4, Mp, j, hb, hj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieBaseChange.exists_isBaseChange X G (regAt ξ p) (regAt ξ q) (regPt h p) Eq
    (castPt (spMap_regIncl_regPt h hs).symm Mq)
  let jp : Ep →ₗ[regAt ξ p] E :=
    { toFun := fun e => jq (j e)
      map_add' := fun a b => by simp
      map_smul' := fun c e => by
        rw [map_smul]
        change jq (regIncl hs c • j e) = _
        rw [map_smul]
        rfl }
  have hjp : ∀ e, (M.pt (jp e)).left = spMap (dualMap (algebraMap (regAt ξ p) Ω)) ≫ (Mp.pt e).left := by
    intro e
    have h1 := hjq (j e)
    have h2 := (castPt_pt_left (spMap_regIncl_regPt h hs).symm Mq (j e)).symm.trans (hj e)
    have h3 : (dualMap (algebraMap (regAt ξ q) Ω)).comp (dualMap (algebraMap (regAt ξ p) (regAt ξ q))) =
        dualMap (algebraMap (regAt ξ p) Ω) := dualMap_comp _ _
    refine h1.trans ?_
    rw [h2, ← h3]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp, Category.assoc]
  have hrp := _root_.GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range X Ω ξ h G E M p Ep Mp jp hjp
  have hrq := _root_.GlobalTheory.CompanionTheory.Ar.LieStalk.lat_eq_range X Ω ξ h G E M q Eq Mq jq hjq
  have hMq : M.lat q = LinearMap.range jq := SetLike.coe_injective (hrq.trans (LinearMap.coe_range jq).symm)
  rw [hrp, hMq]
  apply le_antisymm
  · rintro _ ⟨w, rfl⟩
    refine hb.inductionOn w (motive := fun w => jq w ∈ Submodule.span (regAt ξ q) (Set.range jp)) (fun m => ?_)
      (fun s n hn => by rw [map_smul]; exact Submodule.smul_mem _ s hn)
      (fun a b ha hb => by rw [map_add]; exact add_mem ha hb)
    exact Submodule.subset_span ⟨m, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨e, rfl⟩
    exact ⟨j e, rfl⟩

theorem mem_localizedIn_iff (h : IsCptGen ξ) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {E : Type}
    [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) {p q : Cpt ξ} (hs : q.1 ⤳ p.1)
    (P : PrimeSpectrum (regAt ξ p)) (hu : ∀ s : regAt ξ p, s ∉ P.asIdeal → (s : Ω)⁻¹ ∈ regAt ξ q)
    (hd : ∀ a ∈ regAt ξ q, ∃ s : regAt ξ p, s ∉ P.asIdeal ∧ (s : Ω) * a ∈ regAt ξ p) (v : E) :
    v ∈ GroundTheory.Heights₂.Heights.Model.localizedIn P.asIdeal (M.lat p) ↔ v ∈ M.lat q := by
  have hg := lat_gen h G M hs
  constructor
  · rintro ⟨s, hsP, hv⟩
    have h0 : (s : Ω) ≠ 0 := fun h0 => hsP (by
      have : s = 0 := Subtype.ext h0
      rw [this]; exact zero_mem _)
    have h1 : (s : Ω) • v ∈ M.lat q := by rw [hg]; exact Submodule.subset_span hv
    have h2 := (M.lat q).smul_mem (⟨_, hu s hsP⟩ : regAt ξ q) h1
    have h3 : (⟨_, hu s hsP⟩ : regAt ξ q) • (s : Ω) • v = v := by
      rw [Subring.smul_def, smul_smul]
      simp [h0]
    rwa [h3] at h2
  · intro hv
    rw [hg] at hv
    induction hv using Submodule.span_induction with
    | mem w hw => exact ⟨1, fun h1 => P.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 h1), by simpa using hw⟩
    | zero => exact zero_mem _
    | add a b _ _ ha hb => exact add_mem ha hb
    | smul a w _ hw =>
      obtain ⟨s, hsP, hsw⟩ := hw
      obtain ⟨t, htP, hta⟩ := hd a a.2
      refine ⟨t * s, fun hm => (P.isPrime.mem_or_mem hm).elim htP hsP, ?_⟩
      have e : (t * s) • a • w = (⟨_, hta⟩ : regAt ξ p) • s • w := by
        simp only [Subring.smul_def, smul_smul, Subring.coe_mul]
        congr 1
        ring
      rw [e]
      exact (M.lat p).smul_mem _ hsw

theorem lat_eq_of_normal : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X), IsCptGen ξ → ∀ (G G' : Over X) [GrpObj G] [GrpObj G'] (GΩ : Over (Sp Ω)) [GrpObj GΩ] (φ : GΩ.left ⟶ G.left) (φ' : GΩ.left ⟶ G'.left), IsSemiAbelian G → IsSemiAbelian G' → IsGrpPullback GΩ G ξ φ → IsGrpPullback GΩ G' ξ φ' → ∀ (E : Type) [AddCommGroup E] [Module Ω E] (M : LieModel G ξ E) (M' : LieModel G' ξ E), (∀ e, ∃ v : epsAt (𝟙 (Sp Ω)) ⟶ GΩ, v.left ≫ φ = (M.pt e).left ∧ v.left ≫ φ' = (M'.pt e).left) → IsLocallyNoetherian X → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme X → M.lat = M'.lat := by
  intro X Ω _ ξ hξ G G' _ _ GΩ _ φ φ' hS hS' hP hP' E _ _ M M' hv hN hnorm
  funext p
  haveI := hS.comm
  haveI := hS.smooth
  haveI := hS'.comm
  haveI := hS'.smooth
  haveI := _root_.GlobalTheory.CompanionTheory.Ar.LieStalk.isFractionRing_regAt X Ω ξ hξ p
  obtain ⟨hdom, hic⟩ := hnorm p.1
  haveI : IsDomain (regAt ξ p) := inferInstance
  haveI : IsNoetherianRing (X.presheaf.stalk p.1) := inferInstance
  haveI : IsNoetherianRing (regAt ξ p) := isNoetherianRing_of_ringEquiv _ (regIso hξ p)
  haveI : IsIntegrallyClosed (regAt ξ p) := IsIntegrallyClosed.of_equiv (regIso hξ p)
  haveI : FiniteDimensional Ω E := (_root_.GlobalTheory.CompanionTheory.Ar.lieModel_finite_projective X G Ω ξ E M).1
  obtain ⟨f1, p1, s1⟩ := lat_fin hξ G M p
  obtain ⟨f2, p2, s2⟩ := lat_fin hξ G' M' p
  refine GroundTheory.Heights₂.Heights.Model.LatticesAgree.proof GroundTheory.Heights₂.Heights.Model.HeightOneIntersection.proof (regAt ξ p) Ω E (M.lat p) (M'.lat p) f1 p1 f2 p2 s1 s2 ?_
  intro P hP1
  obtain ⟨q, hs, hdvr, hu, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.LieStalk.HeightOne.exists_generisation_of_height_eq_one X Ω ξ hξ hN hnorm p P hP1
  have hq := _root_.GlobalTheory.CompanionTheory.Ar.DvrExtension.lat_eq_of_dvr X Ω ξ hξ G G' GΩ φ φ' hS hS' hP hP' E M M' hv q hdvr
  ext v
  rw [mem_localizedIn_iff hξ G M hs P hu hd, mem_localizedIn_iff hξ G' M' hs P hu hd, hq]

end GlobalTheory.CompanionTheory.Ar.LieStalk
end
end

