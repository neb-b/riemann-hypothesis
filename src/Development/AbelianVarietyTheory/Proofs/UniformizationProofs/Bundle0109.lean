module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Definitions.Uniformization.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueTorusCompat
public import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0078
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsFormalTorusPointsSemiAbelianModel
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0106
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingEquiv
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdIso
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0089
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0101
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0130

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CubWeilNondegenerateGeneric
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.NondegGen

theorem card_hom_lattice (X U : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommGroup U] :
    Nat.card (Multiplicative X →* U) = Nat.card U ^ Module.finrank ℤ X := by
  have e1 : (Multiplicative X →* U) ≃ (X →ₗ[ℤ] Additive U) :=
    (MonoidHom.toAdditiveRight).trans (addMonoidHomLequivInt ℤ).toEquiv
  have e2 := ((Module.finBasis ℤ X).constr ℤ (M' := Additive U)).toEquiv
  rw [Nat.card_congr (e1.trans e2.symm), Nat.card_fun, Nat.card_congr (Additive.toMul : Additive U ≃ U)]
  simp

theorem card_roots (W F : Type) [CommRing W] [Field F] [IsAlgClosed F] (φ : W →+* F) (hφ : Function.Injective φ)
    (N : ℕ) (hN : (N : F) ≠ 0) (h : ∀ z : F, z ^ N = 1 → z ∈ φ.range) : Nat.card (rootsOfUnity N W) = N := by
  haveI : NeZero (N : F) := ⟨hN⟩
  haveI : NeZero N := ⟨fun e => hN (by simp [e])⟩
  refine Eq.trans (Nat.card_congr ?_) (HasEnoughRootsOfUnity.natCard_rootsOfUnity F N)
  refine (Equiv.ofBijective (restrictRootsOfUnity φ N) ⟨fun a b e => ?_, fun z => ?_⟩)
  · have := congrArg (fun u : rootsOfUnity N F => ((u : Fˣ) : F)) e
    simp only [restrictRootsOfUnity_coe_apply] at this
    exact Subtype.ext (Units.ext (hφ this))
  · have hz : ((z : Fˣ) : F) ^ N = 1 := (mem_rootsOfUnity' N _).1 z.2
    obtain ⟨w, hw⟩ := h _ hz
    have hw1 : w ^ N = 1 := hφ (by rw [map_pow, hw, hz, map_one])
    refine ⟨rootsOfUnity.mkOfPowEq w hw1, Subtype.ext (Units.ext ?_)⟩
    rw [restrictRootsOfUnity_coe_apply]
    exact hw

theorem card_hom_torsion (X W : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] [CommRing W] (N : ℕ) :
    Nat.card (powMonoidHom N : (Multiplicative X →* Wˣ) →* _).ker =
      Nat.card (rootsOfUnity N W) ^ Module.finrank ℤ X := by
  rw [← card_hom_lattice]
  refine Nat.card_congr ⟨fun c => c.1.codRestrict _ fun x => ?_, fun c => ⟨(rootsOfUnity N W).subtype.comp c, ?_⟩,
    fun c => rfl, fun c => rfl⟩
  · exact DFunLike.congr_fun (MonoidHom.mem_ker.1 c.2) x
  · exact MonoidHom.mem_ker.2 (MonoidHom.ext fun x => (c x).2)

theorem card_torsion_ext {GW BF C : Type} [CommGroup GW] [Group BF] [CommGroup C] (N : ℕ) (τ : GW →* BF)
    (j : C →* GW) (hj : Function.Injective j) (hker : ∀ y, τ y = 1 ↔ ∃ c, y = j c)
    (hs : ∀ x, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x) :
    Nat.card (powMonoidHom N : GW →* GW).ker =
      Nat.card (powMonoidHom N : C →* C).ker * Nat.card {x : BF // x ^ N = 1} := by
  let f := τ.comp (powMonoidHom N : GW →* GW).ker.subtype
  have h1 : Nat.card f.ker * Nat.card f.range = Nat.card (powMonoidHom N : GW →* GW).ker := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [← h1]
  congr 1
  · symm
    refine Nat.card_congr (Equiv.ofBijective (fun c => ⟨⟨j c.1, ?_⟩, (hker _).2 ⟨c.1, rfl⟩⟩) ⟨fun a b e => ?_, fun y => ?_⟩)
    · show j c.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg j c.2).trans (map_one j)
    · exact Subtype.ext (hj (congrArg (fun u => u.1.1) e))
    · obtain ⟨c, hc⟩ := (hker y.1.1).1 y.2
      refine ⟨⟨c, hj ?_⟩, Subtype.ext (Subtype.ext hc.symm)⟩
      show j (c ^ N) = _
      rw [map_pow, ← hc, map_one]
      exact y.1.2
  · refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ⟨?_, fun hx => ?_⟩)
    · rintro ⟨y, rfl⟩
      show τ y.1 ^ N = 1
      rw [← map_pow]
      exact (congrArg τ y.2).trans (map_one τ)
    · obtain ⟨y, hy, e⟩ := hs x hx
      exact ⟨⟨y, hy⟩, e⟩

theorem eq_one_of_cubWeil_one {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] {L : RigLB G}
    {c : CubicalStr G L} {N : ℕ} {T : Over S} {y : T ⟶ G} {ζ} (h : CubWeil c N 1 y ζ) : ζ = 1 := by
  have h2 := (GlobalTheory.UU.cubWeil_basic S G L c N T).2.1 1 1 y ζ ζ h h
  rw [_root_.mul_one] at h2
  exact mul_eq_left.1 (h2.unique h)

end GlobalTheory.UU.NondegGen


open GlobalTheory.UU.NondegGen in
theorem GlobalTheory.UU.cubWeil_nondegenerate_generic :
    (∀ (k : Type) [Field k] [IsAlgClosed k] (B : Over (Sp k)) [GrpObj B] (g n : ℕ), IsAbelianScheme B → SmoothOfRelativeDimension g B.hom → (n : k) ≠ 0 → Nat.card {x : (𝟙_ (Over (Sp k)) ⟶ B) // x ^ n = 1} = n ^ (2 * g)) → Laws → AllSet fun {V} _ _ _ {_} {_} _ _ s => ∀ (t : Tower s) (a : t.Alg) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F] [Algebra.IsAlgebraic (FractionRing V) F] (N : ℕ), 1 ≤ N → ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → (∀ y : TF (R := V) F ⟶ a.B, y ^ N = 1 → CubWeil a.M.c N x y 1) → x = 1 := by
  intro hcard hL V _ _ _ A G _ _ s t a F _ _ _ _ N hN x hx horth
  obtain ⟨W, _, _, _, φ, hφ, hcomp, hW, hloc, hroots, hlift⟩ := GlobalTheory.T.torsion_lift_abelianPart_finite_extension hcard V A G s t a F N hN
  haveI : CharZero V := s.cdvr.2.2
  haveI : CharZero F := charZero_of_injective_ringHom
    (f := (algebraMap (FractionRing V) F).comp (algebraMap V (FractionRing V)))
    ((algebraMap (FractionRing V) F).injective.comp (IsFractionRing.injective V _))
  have hNF : (N : F) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  haveI := s.semi.separated
  haveI := a.isAb.proper
  let SW : Over (Spec (CommRingCat.of V)) := Over.mk (Spec.map (CommRingCat.ofHom (algebraMap V W)))
  let σ : TF (R := V) F ⟶ SW := Over.homMk (Spec.map (CommRingCat.ofHom φ)) (by
    show Spec.map (CommRingCat.ofHom φ) ≫ Spec.map (CommRingCat.ofHom (algebraMap V W)) =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing V) F)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap V (FractionRing V)))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hcomp])
  choose ρf hρ hρu using fun y : SW ⟶ G => _root_.GlobalTheory.UU.PointImage.main V A G s t a W hW hloc y
  let ρ : (SW ⟶ G) →* (SW ⟶ a.B) := MonoidHom.mk' ρf fun y y' =>
    (hρu _ _ ((_root_.GlobalTheory.UU.image_one_mul_inv V A G s t a W y y' (ρf y) (ρf y')).2 (hρ y) (hρ y')).1).symm
  obtain ⟨ι', hι, hιs⟩ := _root_.GlobalTheory.UU.exists_formalTorus_points V A G s t W hW hloc
  let pG : (SW ⟶ G) →* (TF (R := V) F ⟶ G) := preHom σ
  let pB : (SW ⟶ a.B) →* (TF (R := V) F ⟶ a.B) := preHom σ
  have hpG : Function.Injective pG := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ G W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  have hpB : Function.Injective pB := fun y y' e =>
    GlobalTheory.over_points_ext_of_injective _ a.B W F φ hφ _ y y' (congrArg (fun q => q.left) e)
  let τ := pB.comp ρ
  have hker : ∀ y, τ y = 1 ↔ ∃ c, y = ι' c := fun y => by
    have e1 : τ y = 1 ↔ ρ y = 1 := map_eq_one_iff pB hpB
    have e2 := _root_.GlobalTheory.UU.image_eq_one_iff_torus_point V A G s t a W hW hloc y
    rw [e1]
    constructor
    · intro h
      obtain ⟨c, hc⟩ := e2.1 (by have := hρ y; rw [show ρf y = 1 from h] at this; exact this)
      exact ⟨c, (hιs y c).2 hc⟩
    · rintro ⟨c, hc⟩
      exact (hρu y 1 (e2.2 ⟨c, (hιs y c).1 hc⟩)).symm
  have hs : ∀ x : TF (R := V) F ⟶ a.B, x ^ N = 1 → ∃ y, y ^ N = 1 ∧ τ y = x := fun x hx => by
    obtain ⟨y, b, hy, hb, e⟩ := hlift x hx
    refine ⟨y, hy, ?_⟩
    have : ρ y = b := (hρu y b hb).symm
    show pB (ρ y) = x
    rw [this]
    exact Over.OverMorphism.ext e
  obtain ⟨g', hg'⟩ := GlobalTheory.AbelianDim.exists_relDim V a.B a.isAb
  have hdim := (_root_.GlobalTheory.UU.Tower.dim_eq_add_finrank V A G s t g').2 a hg'
  have hB : Nat.card {x : TF (R := V) F ⟶ a.B // x ^ N = 1} = N ^ (2 * g') :=
    GlobalTheory.card_torsion_geometricPoint_of_field hcard _ a.B a.isAb g' hg' F _ N hNF
  have hC := card_hom_torsion s.X W N
  rw [card_roots W F φ hφ N hNF hroots] at hC
  have hH := card_torsion_ext N τ ι' hι hker hs
  rw [hC, hB] at hH
  have hρN : ∀ y : SW ⟶ G, y ^ N = 1 → ρ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]

  have hpair : ∀ y y' : SW ⟶ G, y ^ N = 1 → y' ^ N = 1 → CubWeil a.M.c N (τ y) (τ y') 1 →
      CubWeil s.P.c N (pG y) (pG y') 1 := fun y y' hy hy' h => by
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil s.P.c hy hy'
    have h1 := (_root_.GlobalTheory.UU.ImagePairing.cubWeil_image V A G s t a W hW hloc N y y' (ρ y) (ρ y') ζ (hρ y) (hρ y') (hρN y hy) (hρN y' hy') hζ).comp σ
    have h2 := hζ.comp σ
    rw [h1.unique h] at h2
    exact h2
  have hτN : ∀ y : SW ⟶ G, y ^ N = 1 → τ y ^ N = 1 := fun y hy => by rw [← map_pow, hy, map_one]
  obtain ⟨y, hy, rfl⟩ := hs x hx
  have hmem := GlobalTheory.UU.mem_of_cubWeil_orthogonal hL V A G s F N hN
    ((powMonoidHom N : (Multiplicative s.X →* Wˣ) →* _).ker.map (pG.comp ι'))
    ((powMonoidHom N : (SW ⟶ G) →* _).ker.map pG) ?_ ?_ ?_ ?_ (pG y) (by rw [← map_pow, hy, map_one]) ?_
  · obtain ⟨c, -, hc⟩ := hmem
    exact (hker y).2 ⟨c, (hpG hc).symm⟩
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rintro _ ⟨c, hc, rfl⟩
    rw [← map_pow]
    exact (congrArg _ hc).trans (map_one _)
  · rw [Subgroup.card_map_of_injective (f := pG.comp ι') (hpG.comp hι), Subgroup.card_map_of_injective hpG, hH, hC, hdim]
    ring
  · rintro _ ⟨c, hc, rfl⟩ _ ⟨y', hy', rfl⟩
    have hcN : ι' c ^ N = 1 := by
      rw [← map_pow]
      exact (congrArg _ hc).trans (map_one _)
    refine hpair (ι' c) y' hcN hy' ?_
    rw [(hker _).2 ⟨c, rfl⟩]
    obtain ⟨ζ, hζ, -⟩ := existsUnique_cubWeil a.M.c (one_pow N) (hτN y' hy')
    rwa [eq_one_of_cubWeil_one hζ] at hζ
  · rintro _ ⟨y', hy', rfl⟩
    exact hpair y y' hy hy' (horth _ (hτN y' hy'))
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsIsoOfSectionRingAutOfRelAmple
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_iso_of_sectionRing_aut_of_relAmple : ∀ (K : Type) [CommRing K] (X : Over (Spec (CommRingCat.of K))) [IsProper X.hom] (L : LB X.left), L.IsLB → RelAmple X L → ∀ θ : ∀ n : ℕ, 1 ≤ n → (H0 L n ≃ H0 L n), (∀ (n : ℕ) (hn : 1 ≤ n) (c : K) (a b d : H0 L n), (∀ j, d.f j = a.f j + resTop _ (scal X.hom c) * b.f j) → ∀ j, (θ n hn d).f j = (θ n hn a).f j + resTop _ (scal X.hom c) * (θ n hn b).f j) → (∀ (n m : ℕ) (hn : 1 ≤ n) (hm : 1 ≤ m) (a : H0 L n) (b : H0 L m) (d : H0 L (n + m)), (∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from d.f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from a.f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from b.f j)) → ∀ j : Fin 1 → L.ι, (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ (n + m) (hn.trans (Nat.le_add_right n m)) d).f j) = (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ n hn a).f j) * (show Γ(X.left, LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) j) from (θ m hm b).f j)) → ∃ Φ₀ : X ≅ X, ∃ w : LB.Iso L (L.pull Φ₀.hom.left), w.IsGen ∧ ∀ (n : ℕ) (hn : 1 ≤ n) (a : H0 L n), (∀ (Z : Scheme.{0}) (r : Z ⟶ X.left) (z : Z) (p : Fin 1 → L.ι) (q : Fin 1 → L.ι), (∀ κ, (Φ₀.hom.left) ((fun _ : Fin 1 => 𝟙 X.left) κ (r z)) ∈ L.U (p κ)) → (∀ κ, (fun _ : Fin 1 => 𝟙 X.left) κ (r z) ∈ L.U (q κ)) → Geo.Tor.gs (r ≫ Φ₀.hom.left) z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) p) ((θ n hn a).f p) = (∏ κ, Geo.Tor.gw w (r ≫ (fun _ : Fin 1 => 𝟙 X.left) κ) z (p κ) (q κ) ^ (fun _ : Fin 1 => (n : ℤ)) κ).val * Geo.Tor.gs r z (LB.wchart L (fun _ : Fin 1 => 𝟙 X.left) q) ((a).f q)) := by
  intro K _ X _ L hL hA θ hlin hmul
  have h := isAmpleLB_of_relAmple_of_isAffine X hL hA
  have := h.compactSpace
  have := h.quasiSeparatedSpace
  obtain ⟨-, m, hm, M, s, hs⟩ := isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA 1 le_rfl
  have hN : 1 ≤ 1 * m := by omega
  have haff := (isAffineOpen_nonzeroLocus_of_relAmple K X L hL hA (1 * m) hN).1
  obtain ⟨Φ, hΦ⟩ := exists_iso_of_sectionRing_equiv K X X L L hL hL θ hlin hmul
    ⟨1 * m, hN, H0 L (1 * m), id,
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup (fun a : H0 L (1 * m) => nonzeroLocus a) (s i))),
      top_le_iff.1 (hs.ge.trans (iSup_le fun i => le_iSup_of_le ((θ (1 * m) hN).symm (s i))
        (congrArg nonzeroLocus ((θ (1 * m) hN).apply_symm_apply (s i))).ge)),
      fun a => ⟨haff _, haff _⟩⟩
  exact ⟨Φ, exists_iso_of_sectionRing K X X L L hL hL θ hlin hmul Φ.hom.left hΦ
    (exists_sec_succ_of_relAmple K X L hL hA)⟩

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecOfLbIso
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UU.EffSpecial

theorem exists_sec_of_lbIso {Y : Scheme.{0}} {A B : LB Y} (hA : A.IsLB) (hB : B.IsLB) (h : LBIso A B)
    (hs : ∃ s : LB.Sec B, ∃ j, s.f j ≠ 0) : ∃ s : LB.Sec A, ∃ j, s.f j ≠ 0 := by
  obtain ⟨u, hu⟩ := h
  obtain ⟨t, b, hb⟩ := hs
  refine ⟨DVR.secOfIso t hu hA hB, ?_⟩
  by_contra hn
  push_neg at hn
  refine hb (fn_ext fun y hy => ?_)
  obtain ⟨a, ha⟩ := exists_chart hA y
  have e := (DVR.secOfIso_spec t hu hA hB a b).symm
  rw [hn a] at e
  have e' := (DVR.isoCand_rs u t a b le_rfl).symm.trans ((congrArg (DVR.rs le_rfl) (e.trans (map_zero _))).trans
    (map_zero _))
  have e'' := (Units.mul_right_eq_zero _).1 e'
  have hm : (𝟙 Y : Y ⟶ Y) y ∈ A.U a ⊓ B.U b := ⟨ha, hy⟩
  refine (gs_res (𝟙 Y) y inf_le_right hm _).symm.trans ((congrArg (gs (𝟙 Y) y _) e'').trans ?_)
  rw [gs_eq _ y _ hm, gs_eq _ y _ hy, map_zero, map_zero, map_zero, map_zero]

theorem lbIso_pw {Y : Scheme.{0}} {A B : LB Y} (h : LBIso A B) (t : ℤ) : LBIso (AbLaw.pw A t) (AbLaw.pw B t) := by
  obtain ⟨w, hw⟩ := h
  refine ⟨⟨fun p => w.s p ^ t⟩, fun p q => ?_⟩
  have e := congrArg (· ^ t) (hw p q)
  simp only [mul_zpow, ← map_zpow] at e
  refine e.trans (congrArg₂ (· * ·) ?_ rfl)
  exact (mul_zpow _ _ t).trans (congrArg₂ (· * ·) (map_zpow _ _ t).symm
    ((inv_zpow _ t).trans (congrArg (·⁻¹) (map_zpow _ _ t).symm)))

theorem ne_zero_of_mem {Y : Scheme.{0}} {M : LB Y} (s : LB.Sec M) {y : Y} (hy : y ∈ nonzeroLocus s) :
    ∃ j, s.f j ≠ 0 := by
  obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
  refine ⟨j, fun e => ?_⟩
  rw [e, Scheme.basicOpen_zero] at hj
  exact hj

theorem isIntegral_special {V : Type} [CommRing V] [IsLocalRing V]
    (B : Over (Spec (CommRingCat.of (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1))))) [GrpObj B]
    (hB : IsAbelianScheme B) : IsIntegral B.left := by
  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
  have := forall_geometricallyIntegral_of_smooth_of_geometricallyConnected _ _ B.hom hB.smooth hB.geomConnected
  exact GeometricallyIntegral.geometrically_isIntegral (f := B.hom) _ _ _ (IsPullback.of_id_fst (f := B.hom))

theorem exists_sec_special : Laws → AllSet fun {V} _ _ _ {A} {G} _ _ s => ∀ t : Tower s, ∃ (k : ℕ) (σ : LB.Sec (pw (t.l 0).D.M.L.L k)), 1 ≤ k ∧ ∃ j, σ.f j ≠ 0 := by
  intro hL V _ _ _ A G _ _ s t
  have := s.cdvr.1
  have := s.semi.smooth
  have := s.semi.separated
  have := s.semi.quasiCompact
  have := s.semi.geomConnected
  obtain ⟨d, hd, n, a, ha, -⟩ := (GlobalTheory.Unif.relAmple_iff_veryAmpleBy _ A.A A.L A.isLB).1 A.ample
  have hP := s.P.L.isLB

  have h₁ : ∃ σ : LB.Sec ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V))), ∃ j, σ.f j ≠ 0 := by
    have iso : LBIso ((AbLaw.pw s.P.L.L d).pull (pullback.fst G.hom (jK V)))
        ((AbLaw.pw A.L d).pull s.gen.hom.left) := by
      rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
      exact lbIso_pw (LBIso.symm ⟨s.wA, s.wA_gen⟩) d
    obtain ⟨w, hw⟩ := iso
    let y : ((Over.pullback (jK V)).obj G).left :=
      s.gen.inv.left (eSec A.A (IsLocalRing.closedPoint (FractionRing V)))
    have hy : s.gen.hom.left y ∈ ⨆ i, nonzeroLocus (a i) := by rw [ha]; trivial
    obtain ⟨i, hi⟩ := TopologicalSpace.Opens.mem_iSup.1 hy
    obtain ⟨⟨σ, hσ, -⟩, H⟩ := SecPullIso.section_pull _ _ s.gen.hom.left _ _ w (isLB_pw A.isLB d)
      (pull_isLB (isLB_pw hP d) _) hw (a i)
    exact ⟨σ, ne_zero_of_mem σ (y := y) (by rw [H σ hσ]; exact hi)⟩

  have h₂ := GlobalTheory.SpreadSec.exists_ne_zero_closed_fibre V G _ (isLB_pw hP d) h₁
  obtain ⟨w, hw⟩ := (t.l 0).lev
  have hM := (t.l 0).D.M.L.isLB
  have hE := (t.l 0).Pe.L.isLB
  have h₃ : ∃ σ : LB.Sec ((AbLaw.pw (t.l 0).D.M.L.L d).pull (t.l 0).Q.q.left), ∃ j, σ.f j ≠ 0 := by
    refine exists_sec_of_lbIso (pull_isLB (isLB_pw hM d) _) (pull_isLB (isLB_pw hP d) _) ?_ h₂
    rw [TrivLocus.pull_pw, TrivLocus.pull_pw]
    exact lbIso_pw (LBIso.trans (pull_isLB hM _) hE (pull_isLB hP _)
      (LBIso.symm ⟨_, (t.l 0).D.map.gen⟩) ⟨w, hw.gen⟩) d

  have hm : (IsLocalRing.maximalIdeal V ^ (0 + 1)).IsMaximal := by
    rw [zero_add, pow_one]; infer_instance
  have : IsLocalRing (V ⧸ IsLocalRing.maximalIdeal V ^ (0 + 1)) :=
    letI := Ideal.Quotient.field (IsLocalRing.maximalIdeal V ^ (0 + 1))
    inferInstance
  obtain ⟨O, hO, hu, h₄⟩ := _root_.GlobalTheory.exists_sec_primitive_twist hL.globalFns _ _ _ (t.l 0).Q _ (isLB_pw hM d) h₃
  have := isIntegral_special (t.l 0).Q.B (t.l 0).Q.isAb
  obtain ⟨σ, hσ⟩ := SymSec.exists_sec_sq _ (t.l 0).Q.B (t.l 0).D.M d O hO hu h₄
  exact ⟨2 * d, σ, by omega, hσ⟩

end GlobalTheory.UU.EffSpecial
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSymmetricVeryAmpleBy
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SymVeryAmple


open GlobalTheory.CechPic in
theorem exists_of_involution {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of R))
    (σ : X ⟶ X) (hσ : σ ≫ σ = 𝟙 X) (h : IsProjBy f) :
    ∃ (H : LB X) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy f H s ∧
      Triv (LB.LinComb H (K := Fin 2) ![σ, 𝟙 X] ![1, -1]) := by
  obtain ⟨L, hL, m, s, hs⟩ := h
  have : IsProper f := isProper_of_veryAmpleBy hs
  have : IsIso σ := ⟨σ, hσ, hσ⟩
  have hA : IsAmpleLB L := isAmpleLB_of_veryAmpleBy hs
  have hP : IsAmpleLB (L.pull σ) := hA.pull_of_isAffineHom σ
  have hN : (tens L (L.pull σ)).IsLB := isLB_tens hL hP.isLB
  have hT : IsAmpleLB (tens L (L.pull σ)) := by
    refine hA.tensor hP hN ((cls_eq_zero_iff (LB.isLB_div (LB.isLB_div hN hL) hP.isLB)).1 ?_)
    rw [cls_div (LB.isLB_div hN hL) hP.isLB, cls_div hN hL, cls_tens hL hP.isLB]
    abel
  obtain ⟨n, -, M, t, ht⟩ := hT.exists_veryAmpleBy f
  have hH := isLB_lbPow hN n
  refine ⟨_, M, t, hH, ht, (cls_eq_zero_iff (LB.isLB_linComb hH _ _)).1 ?_⟩
  rw [cls_linComb hH, Fin.sum_univ_two, cls_lbPow hN, cls_tens hL hP.isLB, cls_pull hL]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_id, map_nsmul, map_add (f := _), ← pull_comp, hσ]
  rw [add_comm (pull σ (cls L hL)), one_zsmul, neg_one_zsmul, Category.id_comp, add_neg_cancel]

theorem exists_symmetric_veryAmpleBy : ∀ (R : Type) [CommRing R] (B : Over (Spec (CommRingCat.of R))) [GrpObj B] [IsCommMonObj B], IsAbelianScheme B → IsProjBy B.hom → ∃ (H : LB B.left) (n : ℕ) (s : Fin (n + 1) → LB.Sec H), H.IsLB ∧ VeryAmpleBy B.hom H s ∧ Triv (LB.LinComb H (K := Fin 2) ![(ι[B]).left, 𝟙 B.left] ![1, -1]) := by
  intro R _ B _ _ _ h
  refine exists_of_involution B.hom _ ?_ h
  rw [← Over.comp_left, GrpObj.inv_comp_inv, Over.id_left]

end GlobalTheory.SymVeryAmple
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsProperAndRelAmpleLPow
section
noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem isProper_and_relAmple_lPow :
    ∀ (F : Type) [CommRing F] (S : Scheme.{0}) (P : PolAV S) (t : Spec (CommRingCat.of F) ⟶ S) [IsLocalRing F] (N : ℕ), 1 ≤ N → IsProper (fst (Over.mk t) P.A).left ∧ RelAmple (S := Spec (CommRingCat.of F)) (Over.mk (fst (Over.mk t) P.A).left) (LPow P.A P.L (N : ℤ) (Over.mk t)) := by
  intro F _ S P t _ N hN
  have hP := P.isAb.proper
  have H : IsPullback (snd (Over.mk t) P.A).left (fst (Over.mk t) P.A).left P.A.hom t :=
    (IsPullback.of_hasPullback t P.A.hom).flip
  have hp : IsProper (fst (Over.mk t) P.A).left := MorphismProperty.of_isPullback (P := @IsProper) H hP
  refine ⟨hp, ?_⟩
  have hp' : IsProper (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left).hom := hp
  have hL := LB.isLB_pull P.isLB (snd (Over.mk t) P.A).left
  have hM : (LPow P.A P.L (N : ℤ) (Over.mk t)).IsLB := LB.isLB_linComb P.isLB _ _
  have h₁ := (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hL).1
    (AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample H)
  refine (relAmple_iff_isAmpleLB_of_isAffine
    (Over.mk (X := Spec (CommRingCat.of F)) (fst (Over.mk t) P.A).left) hM).2
    (((isAmpleLB_pow_iff hL hN).2 h₁).of_lbIso hM ?_)
  exact LBIso.chartPull (CoprimeTorsion.chartPullLPow P.A P.L (Over.mk t) N) (chartPullPowPull P.L _ N)
    (lbIso_refl (isLB_lbPow P.isLB N))

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.VeryAmpleByPwOfAffineLoci
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbLaw

theorem veryAmpleBy_pw_of_affine_loci : ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (f : X ⟶ Spec (CommRingCat.of R)) [IsProper f] (H : LB X) (n : ℕ) (t : Fin (n + 1) → LB.Sec H), H.IsLB → (⨆ i, nonzeroLocus (t i) = ⊤) → (∀ i, IsAffineOpen (nonzeroLocus (t i))) → ∃ d : ℕ, 1 ≤ d ∧ ∃ (n' : ℕ) (s : Fin (n' + 1) → LB.Sec (pw H d)), VeryAmpleBy f (pw H d) s := by
  intro R _ X f _ H n t hH hc ha
  have h : IsAmpleLB H :=
    isAmpleLB_of_cover hH le_rfl (fun i => secToPow (t i) 1)
      (by simp only [nonzeroLocus_secToPow _ le_rfl, hc])
      fun i => (nonzeroLocus_secToPow (t i) le_rfl).symm ▸ ha i
  have : IsProper (Over.mk f).hom := ‹IsProper f›
  exact (Unif.relAmple_iff_veryAmpleBy R (Over.mk f) H hH).1
    ((relAmple_iff_isAmpleLB_of_isAffine (Over.mk f) hH).2 h)

end GlobalTheory.AbLaw
end

