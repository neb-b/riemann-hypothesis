module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.TanLoc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0008
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsUnivRingBc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ChartAway
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj

namespace ReciprocityTheory.ChartRestriction.G.Chart

attribute [local instance] Over.cartesianMonoidalCategory

variable {S : Type} [CommRing S] (G : Over (Spec (CommRingCat.of S))) [GrpObj G]

abbrev Gs (s : S) : Over (Spec (CommRingCat.of (Localization.Away s))) :=
  (Over.pullback (fB S (Localization.Away s))).obj G


set_option backward.isDefEq.respectTransparency.types false in
theorem chart_away (U : G.left.Opens) (hU : IsAffineOpen U) (s : S)
    (hs : ∀ x : Spec (CommRingCat.of S), s ∉ x.asIdeal → (η[G]).left x ∈ U) : Nonempty (Chart (Gs G s)) := by
  have hP := ReciprocityTheory.ChartRestriction.G.Geo.Tor.isGrpPullback_pullback G (fB S (Localization.Away s))
  have key : (η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s)) =
      fB S (Localization.Away s) ≫ (η[G]).left := by
    have h1 := congrArg (fun m => m.left)
      (map_one (ReciprocityTheory.ChartRestriction.G.Geo.Tor.pushHom hP
        (Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))))))
    simp only [one_left'] at h1
    change (1 : Over.mk (𝟙 (Spec (CommRingCat.of (Localization.Away s)))) ⟶ Gs G s).left ≫
      pullback.fst G.hom (fB S (Localization.Away s)) = _ at h1
    rw [one_left'] at h1
    simp
  have hs' : ∀ y : Spec (CommRingCat.of (Localization.Away s)),
      s ∉ ((fB S (Localization.Away s)).base y).asIdeal := by
    intro y hy
    have hu : IsUnit (algebraMap S (Localization.Away s) s) :=
      IsLocalization.Away.algebraMap_isUnit s
    have hmem : algebraMap S (Localization.Away s) s ∈ y.asIdeal := hy
    exact y.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu)
  have hf : IsAffineHom (fB S (Localization.Away s)) := inferInstance
  have : IsAffineHom (pullback.fst G.hom (fB S (Localization.Away s))) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback G.hom (fB S (Localization.Away s))).flip hf
  refine ⟨⟨pullback.fst G.hom (fB S (Localization.Away s)) ⁻¹ᵁ U, hU.preimage _, ?_⟩⟩
  intro y _
  have hk : (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) =
      (η[G]).left.base ((fB S (Localization.Away s)).base y) := by
    change ((η[Gs G s]).left ≫ pullback.fst G.hom (fB S (Localization.Away s))).base y =
      (fB S (Localization.Away s) ≫ (η[G]).left).base y
    rw [key]
  show (pullback.fst G.hom (fB S (Localization.Away s))).base ((η[Gs G s]).left.base y) ∈ U
  rw [hk]
  exact hs _ (hs' y)

theorem exists_cover : ∃ (n : ℕ) (s : Fin n → S), Ideal.span (Set.range s) = ⊤ ∧ ∀ i, Nonempty (Chart (Gs G (s i))) := by
  classical
  have htop : Ideal.span {t : S | Nonempty (Chart (Gs G t))} = ⊤ := by
    by_contra hne
    obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal _ hne
    let p : Spec (CommRingCat.of S) := ⟨M, hM.isPrime⟩
    obtain ⟨U, hU, hpU, -⟩ := exists_isAffineOpen_mem_and_subset
      (show (η[G]).left p ∈ (⊤ : G.left.Opens) by simp)
    obtain ⟨V, ⟨t, rfl⟩, hpV, hVle⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp
      (PrimeSpectrum.isBasis_basic_opens (R := S)))
      (show p ∈ ((η[G]).left ⁻¹ᵁ U : (Spec (CommRingCat.of S)).Opens) from hpU)
    have hc : Nonempty (Chart (Gs G t)) := chart_away G U hU t (fun x hx => hVle hx)
    exact hpV (hle (Ideal.subset_span hc))
  obtain ⟨T, hsub, hspan⟩ := (Ideal.span_eq_top_iff_finite _).mp htop
  refine ⟨T.card, fun i => (T.equivFin.symm i : S), ?_, ?_⟩
  · have hr : Set.range (fun i => (T.equivFin.symm i : S)) = (T : Set S) := by
      ext x
      constructor
      · rintro ⟨i, rfl⟩
        exact (T.equivFin.symm i).2
      · intro hx
        exact ⟨T.equivFin ⟨x, hx⟩, by simp⟩
    rw [hr]
    exact hspan
  · intro i
    exact hsub (T.equivFin.symm i).2

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVGrp
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]

theorem extV_genIso (t : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V)))) :
    ∃ io : genFibre V t.G ≅ tK.G, IsMonHom io.hom ∧
      io.hom.left ≫ m.φ = pullback.fst t.G.hom (specMap V (FractionRing V)) :=
  grpPullback_iso (isGrpPullback_pullback t.G _) m.cart

theorem extV_genIso' (t : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V)))) :
    ∃ ko : tK.G ≅ genFibre V t.G, IsMonHom ko.hom ∧
      ko.hom.left ≫ pullback.fst t.G.hom (specMap V (FractionRing V)) = m.φ :=
  grpPullback_iso m.cart (isGrpPullback_pullback t.G _)

theorem extV_unique (hHom : HomExtDvrSt) (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V)))) (g₁ g₂ : t.G ⟶ t'.G) [IsMonHom g₁] [IsMonHom g₂]
    (h : m.φ ≫ g₁.left = m.φ ≫ g₂.left) : g₁ = g₂ := by
  obtain ⟨io, -, hio⟩ := extV_genIso t tK m
  have hmap : (Over.pullback (specMap V (FractionRing V))).map g₁ =
      (Over.pullback (specMap V (FractionRing V))).map g₂ := by
    have A : ∀ g : t.G ⟶ t'.G, ((Over.pullback (specMap V (FractionRing V))).map g).left ≫
        pullback.fst t'.G.hom (specMap V (FractionRing V)) =
          pullback.fst t.G.hom (specMap V (FractionRing V)) ≫ g.left := fun g => pullback.lift_fst _ _ _
    have B : ∀ g : t.G ⟶ t'.G, ((Over.pullback (specMap V (FractionRing V))).map g).left ≫
        pullback.snd t'.G.hom (specMap V (FractionRing V)) =
          pullback.snd t.G.hom (specMap V (FractionRing V)) := fun g => pullback.lift_snd _ _ _
    apply Over.OverMorphism.ext
    apply pullback.hom_ext
    · rw [A, A, ← hio, Category.assoc, Category.assoc, h]
    · rw [B, B]
  obtain ⟨ψ₀, -, hu⟩ := hHom V t.G t'.G t.semi t'.semi ((Over.pullback (specMap V (FractionRing V))).map g₁)
    inferInstance
  exact (hu g₁ ⟨inferInstance, rfl⟩).trans (hu g₂ ⟨inferInstance, hmap.symm⟩).symm

theorem extV_exists (hHom : HomExtDvrSt) (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
    (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))) :
    ∃ ψ : t.G ⟶ t'.G, IsMonHom ψ ∧ m.φ ≫ ψ.left = m'.φ := by
  obtain ⟨io, hiom, hio⟩ := extV_genIso t tK m
  obtain ⟨ko, -, hko⟩ := extV_genIso' t tK m
  obtain ⟨ko', hko'm, hko'⟩ := extV_genIso' t' tK m'
  have := hiom
  have := hko'm
  obtain ⟨ψ, ⟨hψm, hψ⟩, -⟩ := hHom V t.G t'.G t.semi t'.semi (io.hom ≫ ko'.hom) inferInstance
  have hkoio : ko.hom ≫ io.hom = 𝟙 _ := by
    apply Over.OverMorphism.ext
    apply m.cart.1.hom_ext
    · rw [Over.comp_left, Category.assoc, hio, hko, Over.id_left, Category.id_comp]
    · rw [Over.w, Over.id_left, Category.id_comp]
  refine ⟨ψ, hψm, ?_⟩
  rw [← hko, Category.assoc]
  have e : pullback.fst t.G.hom (specMap V (FractionRing V)) ≫ ψ.left =
      ((Over.pullback (specMap V (FractionRing V))).map ψ).left ≫ pullback.fst t'.G.hom (specMap V (FractionRing V)) :=
    (pullback.lift_fst _ _ _).symm
  rw [e, hψ, ← Category.assoc, ← Over.comp_left, ← Category.assoc, hkoio, Category.id_comp, hko']

theorem extV_grp (hHom : HomExtDvrSt) (t t' : SAB H (Sp V)) (tK : SAB H (Sp (FractionRing V)))
    (m : SABMap tK t (spMap (algebraMap V (FractionRing V))))
    (m' : SABMap tK t' (spMap (algebraMap V (FractionRing V)))) :
    ∃ ψ : t.G ≅ t'.G, IsMonHom ψ.hom ∧ m.φ ≫ ψ.hom.left = m'.φ ∧
      ∀ a, t.act.act a ≫ ψ.hom = ψ.hom ≫ t'.act.act a := by
  obtain ⟨ψ, hψm, hψ⟩ := extV_exists hHom t t' tK m m'
  obtain ⟨ψ', hψ'm, hψ'⟩ := extV_exists hHom t' t tK m' m
  have := hψm
  have := hψ'm
  have h1 : ψ ≫ ψ' = 𝟙 _ := extV_unique hHom t t tK m _ _ (by rw [Over.comp_left, ← Category.assoc, hψ, hψ',
    Over.id_left, Category.comp_id])
  have h2 : ψ' ≫ ψ = 𝟙 _ := extV_unique hHom t' t' tK m' _ _ (by rw [Over.comp_left, ← Category.assoc, hψ', hψ,
    Over.id_left, Category.comp_id])
  refine ⟨⟨ψ, ψ', h1, h2⟩, hψm, hψ, fun a => ?_⟩
  have ha := t.act.hom a
  have ha' := t'.act.hom a
  refine extV_unique hHom t t' tK m _ _ ?_
  show m.φ ≫ (t.act.act a ≫ ψ).left = m.φ ≫ (ψ ≫ t'.act.act a).left
  rw [Over.comp_left, Over.comp_left, ← Category.assoc, ← m.act, Category.assoc, hψ, ← Category.assoc, hψ, m'.act]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Chart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding spMap spMap_comp
open scoped CategoryTheory.Obj

variable {R : Type} [CommRing R] {G : Over (Spec (CommRingCat.of R))} [GrpObj G]

theorem chart_of_basis [IsLocalRing R] [Smooth G.hom] {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v) :
    ∃ x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin d) m) ⟶ G, IsUnivChart G d x ∧
      ∀ j, v j = spMap (dualLift (Pi.single j 1)) ≫ x 1 := by
  obtain ⟨n, x, hx⟩ := univChartLoc G
  have htan : ∀ i, IsTan (v i) := fun i => (isTan_iff _).mpr (hv.1 i)
  let M : Fin d → Fin n → R := fun i => tcoord hx (v i) (htan i)
  let L : (Fin d → R) →ₗ[R] (Fin n → R) := Fintype.linearCombination R M
  have hL : ∀ c, L c = ∑ i, c i • M i := fun c => Fintype.linearCombination_apply R M c
  have hprod : ∀ c, ∃ h : IsTan (prodPts c v), tcoord hx _ h = L c := fun c => by
    obtain ⟨h, e⟩ := prodPts_tan hx c v htan
    exact ⟨h, e.trans (hL c).symm⟩
  have hbij : Function.Bijective L := by
    constructor
    · intro c c' hcc
      obtain ⟨h, e⟩ := hprod c
      obtain ⟨h', e'⟩ := hprod c'
      have hw : prodPts c v = prodPts c' v := tan_ext hx h h' (by rw [e, e', hcc])
      have ht : IsTangent (prodPts c v) := (isTan_iff _).mp h
      exact (hv.2 _ ht).unique ((isLieComb_iff c v _).mpr rfl) ((isLieComb_iff c' v _).mpr hw)
    · intro t
      have hw := isTan_dualLift hx t
      obtain ⟨c, hc, -⟩ := hv.2 _ ((isTan_iff _).mp hw)
      refine ⟨c, ?_⟩
      obtain ⟨h, e⟩ := hprod c
      rw [← e, ← tcoord_congr hx ((isLieComb_iff c v _).mp hc) hw h, tcoord_eq hx _ hw t rfl]
  let Le := LinearEquiv.ofBijective L hbij
  let sub {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
      JetR R (Fin b) m →ₐ[R] JetR R (Fin a) m :=
    jetLift (R := R) (RingHom.ker (jetAug R (Fin a) m)) (ker_jetAug_pow (Fin a) m)
      (fun k => ∑ i, T (Pi.single i 1) k • zR m i) (fun k => sum_smul_zR_mem m _)
  have sub_zR {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) (k : Fin b) :
      sub T m (zR m k) = ∑ i, T (Pi.single i 1) k • zR m i := by
    exact jetLift_zR _ _ _ _ k
  have sub_id {a : ℕ} (m : ℕ) :
      sub (LinearMap.id : (Fin a → R) →ₗ[R] (Fin a → R)) m = AlgHom.id R _ := by
    apply jet_ext
    intro k
    rw [sub_zR]
    simp [Pi.single_apply]
  have sub_comp {a b c : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R))
      (S : (Fin c → R) →ₗ[R] (Fin a → R)) (m : ℕ) :
      (sub S m).comp (sub T m) = sub (T.comp S) m := by
    apply jet_ext
    intro k
    rw [AlgHom.comp_apply, sub_zR, sub_zR, map_sum]
    simp_rw [map_smul, sub_zR, Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [← Finset.sum_smul]
    congr 1
    conv_rhs => rw [LinearMap.comp_apply, ← sum_single (S (Pi.single j 1))]
    simp [map_sum, map_smul, Finset.sum_apply, mul_comm]
  have sub_aug {a b : ℕ} (T : (Fin a → R) →ₗ[R] (Fin b → R)) (m : ℕ) :
      (jetAug R (Fin a) m).comp (sub T m) = jetAug R (Fin b) m := by
    apply jet_ext
    intro k
    rw [AlgHom.comp_apply, sub_zR, jetAug_zR]
    exact RingHom.mem_ker.mp (sum_smul_zR_mem m _)
  let y (m : ℕ) := spMap (sub Le.toLinearMap m) ≫ x m
  refine ⟨y, ⟨fun m => ?_, fun m => ?_, ?_⟩, fun j => Eq.symm ?_⟩
  · have trunc_zR {k : ℕ} (j : Fin k) : jetTruncR R (Fin k) m (zR (m + 1) j) = zR m j := rfl
    have ht : (jetTruncR R (Fin d) m).comp (sub Le.toLinearMap (m + 1)) =
        (sub Le.toLinearMap m).comp (jetTruncR R (Fin n) m) := by
      apply jet_ext
      intro k
      simp only [AlgHom.comp_apply, sub_zR, trunc_zR, map_sum, map_smul]
    dsimp only [y]
    rw [← Category.assoc, spMap_comp, ht, ← spMap_comp, Category.assoc, hx.1 m]
  · have zero_zR {k : ℕ} (j : Fin k) : jetZeroR R (Fin k) m (zR m j) = zR 0 j := rfl
    have hz : (jetZeroR R (Fin d) m).comp (sub Le.toLinearMap m) =
        (sub Le.toLinearMap 0).comp (jetZeroR R (Fin n) m) := by
      apply jet_ext
      intro k
      simp only [AlgHom.comp_apply, sub_zR, zero_zR, map_sum, map_smul]
    dsimp only [y]
    rw [← Category.assoc, spMap_comp, hz, ← spMap_comp, Category.assoc, hx.2.1 m, comp_one']
  · intro A _ _ aug m hA w hw
    obtain ⟨ψ, ⟨hψaug, hψw⟩, hψunique⟩ := hx.2.2 A aug m hA w hw
    have hforward : (sub Le.symm.toLinearMap m).comp (sub Le.toLinearMap m) = AlgHom.id R _ := by
      rw [sub_comp, LinearEquiv.comp_symm, sub_id]
    have hinverse : (sub Le.toLinearMap m).comp (sub Le.symm.toLinearMap m) = AlgHom.id R _ := by
      rw [sub_comp, LinearEquiv.symm_comp, sub_id]
    refine ⟨ψ.comp (sub Le.symm.toLinearMap m), ⟨?_, ?_⟩, ?_⟩
    · rw [← AlgHom.comp_assoc, hψaug, sub_aug]
    · dsimp only [y]
      rw [← Category.assoc, spMap_comp, AlgHom.comp_assoc, hforward, AlgHom.comp_id]
      exact hψw
    · rintro φ ⟨hφaug, hφw⟩
      have hφ : φ.comp (sub Le.toLinearMap m) = ψ := by
        apply hψunique
        refine ⟨?_, ?_⟩
        · rw [← AlgHom.comp_assoc, hφaug, sub_aug]
        · dsimp only [y] at hφw
          rw [hφw, ← Category.assoc, spMap_comp]
      rw [← hφ, AlgHom.comp_assoc, hinverse, AlgHom.comp_id]
  · have hLj : Le.toLinearMap (Pi.single j 1) = M j := by
      show L (Pi.single j 1) = M j
      rw [hL]
      simp [Pi.single_apply]
    have hdual : (dualLift (Pi.single j 1)).comp (sub Le.toLinearMap 1) = dualLift (M j) := by
      apply jet_ext
      intro k
      rw [AlgHom.comp_apply, sub_zR, dualLift_zR, map_sum]
      simp_rw [map_smul, dualLift_zR]
      simp [Pi.single_apply, ← hLj]
    dsimp only [y]
    rw [← Category.assoc, spMap_comp, hdual]
    exact (tcoord_spec hx (v j) (htan j)).symm

theorem basis_of_chart {n : ℕ} {x : ∀ m : ℕ, sp (R₀ := R) (JetR R (Fin n) m) ⟶ G} (hx : IsUnivChart G n x) :
    IsLieBasis (G := G) (fun i : Fin n => (spMap (dualLift (Pi.single i 1)) ≫ x 1 : epsR R ⟶ G)) := by
  let v : Fin n → (epsR R ⟶ G) := fun i => spMap (dualLift (Pi.single i 1)) ≫ x 1
  have htan : ∀ i, IsTan (v i) := fun i => isTan_dualLift hx _
  have hM : ∀ i, tcoord hx (v i) (htan i) = Pi.single i 1 := fun i => tcoord_eq hx _ _ _ rfl
  refine ⟨fun i => (isTan_iff _).mp (htan i), fun w hw => ?_⟩
  have hw' : IsTan w := (isTan_iff _).mpr hw
  have key : ∀ c, IsLieComb c v w ↔ tcoord hx w hw' = c := by
    intro c
    obtain ⟨h, e⟩ := prodPts_tan hx c v htan
    have e2 : tcoord hx _ h = c := by
      rw [e]
      simp only [hM]
      exact sum_single c
    rw [isLieComb_iff]
    constructor
    · intro hwc
      rw [tcoord_congr hx hwc hw' h, e2]
    · intro hc
      exact tan_ext hx hw' h (hc.trans e2.symm)
  exact ⟨tcoord hx w hw', (key _).mpr rfl, fun c hc => ((key c).mp hc).symm⟩

theorem isLieBasis_iso {G' : Over (Spec (CommRingCat.of R))} [GrpObj G'] (e : G' ≅ G) [IsMonHom e.hom] {n : ℕ}
    {v : Fin n → (epsR R ⟶ G')} (hv : IsLieBasis fun i => v i ≫ e.hom) : IsLieBasis v := by
  have tan : ∀ w : epsR R ⟶ G', IsTangent (w ≫ e.hom) ↔ IsTangent w := fun w => by
    have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget _).map e.hom))
    rw [IsTangent, IsTangent, ← IsMonHom.one_hom e.hom, Over.comp_left, Over.comp_left, ← Category.assoc, cancel_mono]
  have pr : ∀ u : Fin n → (epsR R ⟶ G'), (List.ofFn u).prod ≫ e.hom = (List.ofFn fun i => u i ≫ e.hom).prod := fun u =>
    (map_list_prod (IsMonHom.monoidHom e.hom (epsR R)) _).trans (by rw [List.map_ofFn]; rfl)
  have comb : ∀ c w, IsLieComb c (fun i => v i ≫ e.hom) (w ≫ e.hom) ↔ IsLieComb c v w := fun c w => by
    constructor
    · rintro ⟨u, hu, hw⟩
      refine ⟨fun i => u i ≫ e.inv, fun i => ?_, ?_⟩
      · rw [Over.comp_left, hu, Category.assoc, ← Over.comp_left, Category.assoc, e.hom_inv_id, Category.comp_id]
      · rw [← cancel_mono e.hom, pr, hw]; simp
    · rintro ⟨u, hu, rfl⟩
      exact ⟨fun i => u i ≫ e.hom, fun i => by rw [Over.comp_left, hu, Category.assoc]; rfl, pr u⟩
  refine ⟨fun i => (tan _).1 (hv.1 i), fun w hw => ?_⟩
  simpa only [comb] using hv.2 _ ((tan w).2 hw)

theorem isLieBasis_baseChange [IsLocalRing R] [Smooth G.hom] {R' : Type} [CommRing R'] (f : R →+* R')
    {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] {φ : G'.left ⟶ G.left}
    (h : IsGrpPullback G' G (Geo.Tor.spMap f) φ) {d : ℕ} {v : Fin d → (epsR R ⟶ G)} (hv : IsLieBasis v)
    {v' : Fin d → (epsR R' ⟶ G')} (hv' : ∀ j, (v' j).left ≫ φ = Geo.Tor.spMap (dualMapR f) ≫ (v j).left) :
    IsLieBasis v' := by
  let _ := f.toAlgebra
  obtain ⟨x, hx, hxv⟩ := chart_of_basis hv
  obtain ⟨x', hx', e'⟩ := tanBC_alg (R' := R') G d x hx
  obtain ⟨e, he, heφ⟩ := grpPullback_iso h (isGrpPullback_pullback G (fB R R'))
  refine isLieBasis_iso e ?_
  convert basis_of_chart hx' using 2 with j
  refine Over.OverMorphism.ext (pullback.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
  have s : (algebraMap R R' ∘ Pi.single j (1 : R) : Fin d → R') = Pi.single j 1 := by
    funext i; by_cases hij : i = j <;> simp [hij, Pi.single_apply]
  have := e' (Pi.single j 1)
  rw [s] at this
  rw [Over.comp_left, Category.assoc, heφ, hv', hxv]
  exact this.symm

end ReciprocityTheory.ChartRestriction.G.Chart
end
end

