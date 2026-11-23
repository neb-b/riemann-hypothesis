module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.Bundle0006
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
public import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.IsNsmulIffEq
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.GenCalc
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThetaVV
public import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSymmetricIffExistsGen
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

namespace SymmetricBundle

open Geo.Tor

theorem isSymmetric_of_gen {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (sy : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1])) (hsy : sy.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ sy (eSec G)) (LB.oneGen L.L)) : L.IsSymmetric := by
  have oi : eSec G ≫ (ι[G]).left = eSec G := by
    have : η[G] ≫ ι[G] = η[G] := by simp
    exact congrArg (fun q => q.left) this
  have mem : ∀ (x : G.left) (a b : L.L.ι), (ι[G]).left x ∈ L.L.U a → x ∈ L.L.U b →
      x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b] := fun x a b ha hb =>
    Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [ha, hb]
  have le : ∀ p : (PUnit → L.L.ι) × L.L.ι, (L.L.pull (ι[G]).left).U p.1 ⊓ L.L.U p.2 ≤
      LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![p.1 PUnit.unit, p.2] := fun p x hx =>
    mem x _ _ (mem_pull.1 hx.1) hx.2
  let w : LB.Iso L.L (L.L.pull (ι[G]).left) := ⟨fun p => res (le p) (sy.s ![p.1 PUnit.unit, p.2])⟩
  have hw : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (a b : L.L.ι), (ι[G]).left (f y) ∈ L.L.U a → f y ∈ L.L.U b →
      gw w f y a b = gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![a, b]) (sy.s ![a, b]) :=
    fun Y f y a b ha hb => gm_res f y (le (fun _ => a, b)) ⟨mem_pull.2 ha, hb⟩ _
  have pg : PGen w := by
    intro Y f y j j' k k' hj hj' hk hk'
    rw [hw Y f y j k hj hk, hw Y f y j' k' hj' hk', gen_trans hsy f y (mem _ _ _ hj hk) (mem _ _ _ hj' hk')]
    congr 1
    rw [trF, Fin.prod_univ_two]
    show gm (f ≫ (ι[G]).left) y _ (L.L.g j j') ^ (1 : ℤ) * gm (f ≫ 𝟙 _) y _ (L.L.g k k') ^ (-1 : ℤ) = _
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  refine ⟨oi.trans (Category.id_comp _).symm, w, (isGen_iff w).2 pg, ?_⟩
  refine (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) (oi.trans (Category.id_comp _).symm) L.L j) (fun _ => rfl)).2 ?_
  intro Z r z p q hp hq
  have hp₀ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (p PUnit.unit) := hp PUnit.unit
  have hq₀ : (r ≫ eSec G) z ∈ L.L.U (q PUnit.unit) := hq PUnit.unit
  have ri : (r ≫ eSec G) ≫ (ι[G]).left = r ≫ eSec G := by rw [Category.assoc, oi]
  have hp₁ : (r ≫ eSec G) z ∈ L.L.U (p PUnit.unit) := by rw [← ri]; exact hp₀
  have hq₁ : (ι[G]).left ((r ≫ eSec G) z) ∈ L.L.U (q PUnit.unit) := by
    have := hq₀
    rw [← ri] at this; exact this
  have one : gw w (r ≫ eSec G) z (q PUnit.unit) (q PUnit.unit) = 1 := by
    obtain ⟨J, hJ, e⟩ := exists_good L.L L.isLB z (K := PUnit) (fun _ => r ≫ eSec G) q (fun _ _ _ => rfl)
      (fun _ => hq₀)
    have a := val_corr hJ hr r
    rw [val_pull hJ, val_one, val_of sy (r ≫ eSec G) z J ![q PUnit.unit, q PUnit.unit] (fun k => by
      fin_cases k
      · exact (congrArg J ri).trans (e PUnit.unit)
      · exact (congrArg J (Category.comp_id _)).trans (e PUnit.unit))] at a
    exact (hw _ _ _ _ _ hq₁ hq₀).trans a
  rw [Category.comp_id, Fintype.prod_unique, zpow_one,
    gen_trans L.rigGen r z (j := p) (j' := q) (Set.mem_iInter.2 fun _ => hp₁) (Set.mem_iInter.2 fun _ => hq₀)]
  congr 1
  have b := pg _ (r ≫ eSec G) z (p PUnit.unit) (q PUnit.unit) (q PUnit.unit) (q PUnit.unit) hp₀ hq₁ hq₀ hq₀
  rw [one, gm_self L.isLB _ z hq₀, ri, inv_one, _root_.mul_one, _root_.mul_one] at b
  rw [trF, Fintype.prod_unique, zpow_one]
  exact b.symm

theorem gen_of_isSymmetric {S : Scheme.{0}} {G : Over S} [GrpObj G] [IsCommMonObj G] (L : RigLB G)
    (h : L.IsSymmetric) :
    ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧
      LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) := by
  obtain ⟨he, w, hw, hm⟩ := h
  have oi : eSec G ≫ (ι[G]).left = eSec G := he.trans (Category.id_comp _)
  have pg := (isGen_iff w).1 hw
  have pm := (maps_iff w (K := PUnit) (fun _ => eSec G) (fun _ => eSec G) (fun _ => 1) L.rig L.rig (𝟙 _) _
    (fun j => rigPull_le _ (𝟙 _) he L.L j) (fun _ => rfl)).1 hm
  have m₀ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      (ι[G]).left x ∈ L.L.U (j 0) := fun j x hx => Set.mem_iInter.1 hx 0
  have m₁ : ∀ (j : Fin 2 → L.L.ι) (x : G.left), x ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      x ∈ L.L.U (j 1) := fun j x hx => Set.mem_iInter.1 hx 1
  have le : ∀ j : Fin 2 → L.L.ι, LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j ≤
      (L.L.pull (ι[G]).left).U (fun _ => j 0) ⊓ L.L.U (j 1) := fun j x hx => ⟨mem_pull.2 (m₀ j x hx), m₁ j x hx⟩
  let s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]) :=
    ⟨fun j => res (le j) (w.s (fun _ => j 0, j 1))⟩
  have hs : ∀ (Y : Scheme.{0}) (f : Y ⟶ G.left) (y : Y) (j : Fin 2 → L.L.ι),
      f y ∈ LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j →
      gm f y (LB.wchart L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] j) (s.s j) = gw w f y (j 0) (j 1) :=
    fun Y f y j hj => gm_res f y (le j) hj _
  refine ⟨s, fun j j' => unit_ext fun x hx => ?_, corr_of_val L.isLB fun y J hJ => ?_⟩
  · refine ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j hx.1)).trans (Eq.trans ?_ ((map_mul _ _ _).trans
      (congrArg₂ (· * ·) (gm_linComb L.L _ _ (𝟙 _) x j j' hx.1 hx.2)
        ((gm_res (𝟙 G.left) x _ hx _).trans (hs _ (𝟙 G.left) x j' hx.2)))).symm)
    rw [pg _ (𝟙 _) x (j 0) (j' 0) (j 1) (j' 1) (m₀ _ _ hx.1) (m₀ _ _ hx.2) (m₁ _ _ hx.1) (m₁ _ _ hx.2),
      Fin.prod_univ_two]
    congr 1
    show _ = gm (𝟙 _ ≫ (ι[G]).left) x _ (L.L.g (j 0) (j' 0)) ^ (1 : ℤ) *
      gm (𝟙 _ ≫ 𝟙 _) x _ (L.L.g (j 1) (j' 1)) ^ (-1 : ℤ)
    rw [Category.comp_id, zpow_one, zpow_neg_one]
  · have ri : (𝟙 _ ≫ eSec G) ≫ (ι[G]).left = 𝟙 _ ≫ eSec G := by rw [Category.assoc, oi]
    have hq₀ : (𝟙 _ ≫ eSec G) y ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := hJ _
    have hq₁ : (ι[G]).left ((𝟙 _ ≫ eSec G) y) ∈ L.L.U (J (𝟙 _ ≫ eSec G)) := by
      have := hJ ((𝟙 _ ≫ eSec G) ≫ (ι[G]).left)
      rw [congrArg J ri] at this
      exact this
    rw [val_pull hJ, val_one, val_of s (𝟙 _ ≫ eSec G) y J ![J (𝟙 _ ≫ eSec G), J (𝟙 _ ≫ eSec G)] (fun k => by
      fin_cases k
      · exact congrArg J ri
      · exact congrArg J (Category.comp_id _)), hs _ _ _ _ (Set.mem_iInter.2 fun k => by
      fin_cases k
      exacts [hq₁, hq₀])]
    have a := pm _ (𝟙 _) y (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => J (𝟙 _ ≫ eSec G)) (fun _ => hq₁) (fun _ => hq₀)
    rw [Category.comp_id, Fintype.prod_unique, zpow_one] at a
    exact mul_eq_right.1 a.symm

end SymmetricBundle

theorem isSymmetric_iff_exists_gen : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : RigLB G), L.IsSymmetric ↔ ∃ s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![1, -1]), s.IsGen ∧ LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec G)) (LB.oneGen L.L) :=
  fun _ _ _ _ L => ⟨SymmetricBundle.gen_of_isSymmetric L,
    fun ⟨s, hs, hr⟩ => SymmetricBundle.isSymmetric_of_gen L s hs hr⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.MemOfNonempty
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT

noncomputable section

namespace GlobalTheory.IotaInj

open GlobalTheory.TorusExt

variable {R : Type} [CommRing R] [IsDomain R] {F : Type} [Field F] [Algebra (FractionRing R) F]

theorem mem_of_nonempty (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) : (jFK (R := R) F ≫ jK R) y ∈ V := by
  have h : IsDominant (jFK (R := R) F ≫ jK R) := GC.isDominant_jFR (V := R) F
  obtain ⟨y', hy'⟩ := (jFK (R := R) F ≫ jK R).denseRange.exists_mem_open V.isOpen ⟨p, hp⟩
  have : Subsingleton (Spec (CommRingCat.of F)) := inferInstanceAs (Subsingleton (PrimeSpectrum F))
  rwa [Subsingleton.elim y y']

theorem eq_zero_of_gs (y : Spec (CommRingCat.of F)) {V : (Spec (CommRingCat.of R)).Opens}
    {p : Spec (CommRingCat.of R)} (hp : p ∈ V) (a : Γ(Spec (CommRingCat.of R), V))
    (h : gs (jFK (R := R) F ≫ jK R) y V a = 0) : a = 0 := by
  by_contra ha
  have : Nonempty V := ⟨⟨p, hp⟩⟩
  have hne : (Spec (CommRingCat.of R)).basicOpen a ≠ ⊥ := fun e => ha ((basicOpen_eq_bot_iff a).1 e)
  obtain ⟨p', hp'⟩ : ∃ p', p' ∈ (Spec (CommRingCat.of R)).basicOpen a := by
    by_contra hc
    exact hne (eq_bot_iff.2 fun z hz => (hc ⟨z, hz⟩).elim)
  have hm : y ∈ (jFK (R := R) F ≫ jK R) ⁻¹ᵁ (Spec (CommRingCat.of R)).basicOpen a := mem_of_nonempty y hp'
  rw [Scheme.preimage_basicOpen, Scheme.mem_basicOpen _ _ y (mem_of_nonempty y hp)] at hm
  rw [gs_eq _ y V (mem_of_nonempty y hp)] at h
  exact hm.ne_zero h

theorem not_isUnit_germ {I : Ideal R} {V : (Spec (CommRingCat.of R)).Opens} {p : Spec (CommRingCat.of R)} (hp : p ∈ V)
    (hI : I ≤ p.asIdeal) {r : Γ(Spec (CommRingCat.of R), V)} (hr : r ∈ I.map (DegPre.toOpen V)) :
    ¬ IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom r) := by
  have key : I.map (DegPre.toOpen V) ≤ (maximalIdeal ((Spec (CommRingCat.of R)).presheaf.stalk p)).comap
      ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha hu
    have e : ((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a) =
        ((Spec (CommRingCat.of R)).presheaf.germ ⊤ p trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) :=
      TopCat.Presheaf.germ_res_apply _ _ p hp _
    have hu' : IsUnit (((Spec (CommRingCat.of R)).presheaf.germ V p hp).hom (DegPre.toOpen V a)) := hu
    rw [e] at hu'
    have hm := (Scheme.mem_basicOpen (Spec (CommRingCat.of R)) (U := ⊤) _ p trivial).2 hu'
    rw [show (Spec (CommRingCat.of R)).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom a) = _ from
      basicOpen_eq_of_affine (R := CommRingCat.of R) a] at hm
    exact hm (hI ha)
  exact key hr

theorem exists_val_psi (D : DegPre R) {I : Ideal R} {χ : D.X} (hχ : D.PsiIn χ I) (hc : (D.c χ).left = eSec D.P.A)
    (j : D.P.L.ι) {V : (Spec (CommRingCat.of R)).Opens} (hV : IsAffineOpen V) (hle : V ≤ eSec D.P.A ⁻¹ᵁ D.P.L.U j)
    (y : Spec (CommRingCat.of F)) (hy : (jFK (R := R) F ≫ jK R) y ∈ V)
    (J : (Spec (CommRingCat.of F) ⟶ D.P.A.left) → D.P.L.ι) (hj : J ((jFK (R := R) F ≫ jK R) ≫ eSec D.P.A) = j) :
    ∃ r ∈ I.map (DegPre.toOpen V), (val (D.psi χ) (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V r := by
  have hx : D.xK χ = jK R ≫ eSec D.P.A := by
    rw [← hc]; simp [DegPre.xK, ptK]
  have le' : jK R ⁻¹ᵁ V ≤ LB.wchart D.P.L (K := PUnit) (fun _ => D.xK χ) (fun _ => j) := fun x hxV =>
    Set.mem_iInter.2 fun k => by
      rw [hx]; exact hle hxV
  obtain ⟨r, hr, hψ⟩ := hχ (fun _ => j) V hV (by rw [hc]; exact hle) le'
  refine ⟨r, hr, ?_⟩
  have e := val_of (D.psi χ) (jFK (R := R) F) y J (fun _ => j) (fun _ => by
    rw [← hj]; exact congrArg J ((congrArg (jFK (R := R) F ≫ ·) hx).trans (Category.assoc _ _ _).symm))
  refine (congrArg Units.val e).trans ?_
  refine (gs_unit _ y _ (le' hy) _).symm.trans ((gs_res _ y le' hy _).symm.trans ?_)
  exact (congrArg (gs (jFK (R := R) F) y _) hψ.symm).trans (gs_pull _ (jK R) y V hy _)

theorem val_tau (D : DegPre R) (a b : D.X) {y : Spec (CommRingCat.of F)} {J} (hJ : Good D.P.L y J) :
    val (D.tau a b) (jFK (R := R) F) y J = val (D.psi (a + b)) (jFK (R := R) F) y J *
      (val (D.psi a) (jFK (R := R) F) y J)⁻¹ * (val (D.psi b) (jFK (R := R) F) y J)⁻¹ *
      (val D.rigK (jFK (R := R) F) y J)⁻¹ :=
  (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
    (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) (val_inv _ _))

theorem c_left_eq (D : DegPre R) {χ : D.X} (h : cP D (TF (R := R) F) χ = 1) : (D.c χ).left = eSec D.P.A :=
  GC.vpt_ext F D.P (Over.w (D.c χ)) (Over.w η[D.P.A]) (congrArg CommaMorphism.left h)

attribute [local instance] gtGroup

theorem eq_zero_of_iota {I : Ideal R} (hI : I ≠ ⊤) (D : DegData R I) (z : D.toPre.X)
    (h : iota D.tau_bimult F z = 0) : z = 0 := by
  by_contra hz
  have hL := D.toPre.P.isLB
  have c₁ : (D.toPre.c z).left = eSec D.toPre.P.A := c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, h, zero_b])
  have c₂ : (D.toPre.c (-z)).left = eSec D.toPre.P.A :=
    c_left_eq (F := F) _ (by rw [← iota_b D.tau_bimult, map_neg, h, neg_zero, zero_b])
  obtain ⟨m, hm, hIm⟩ := I.exists_le_maximal hI
  let p : Spec (CommRingCat.of R) := (⟨m, hm.isPrime⟩ : PrimeSpectrum R)
  obtain ⟨j, hj⟩ := exists_chart hL (eSec D.toPre.P.A p)
  obtain ⟨V, hV, hp, hle⟩ : ∃ V : (Spec (CommRingCat.of R)).Opens, IsAffineOpen V ∧ p ∈ V ∧
      V ≤ eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j := by
    obtain ⟨_, ⟨V, hV, rfl⟩, hp, hle⟩ := (Spec (CommRingCat.of R)).isBasis_affineOpens.exists_subset_of_mem_open
      (show p ∈ ((eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j : (Spec (CommRingCat.of R)).Opens) : Set _) from hj)
      (eSec D.toPre.P.A ⁻¹ᵁ D.toPre.P.L.U j).isOpen
    exact ⟨V, hV, hp, hle⟩
  let y : Spec (CommRingCat.of F) := (⊥ : PrimeSpectrum F)
  have hy := mem_of_nonempty (R := R) y hp
  obtain ⟨J, hJ, hJj⟩ := exists_good D.toPre.P.L hL y (K := PUnit)
    (fun _ => (jFK (R := R) F ≫ jK R) ≫ eSec D.toPre.P.A) (fun _ => j) (fun _ _ _ => rfl) (fun _ => hle hy)
  obtain ⟨r, hr, e₁⟩ := exists_val_psi D.toPre (D.psi_pos z hz) c₁ j hV hle y hy J (hJj PUnit.unit)
  obtain ⟨r', -, e₂⟩ := exists_val_psi D.toPre (D.psi_pos (-z) (neg_ne_zero.2 hz)) c₂ j hV hle y hy J (hJj PUnit.unit)
  have τ : ∀ χ, val (D.toPre.tau z χ) (jFK (R := R) F) y J = 1 := fun χ => by
    have e := iota_val (F := F) D.tau_bimult z χ (y := y) hJ
    rw [h, zero_val χ hJ] at e
    exact e.symm
  have hle' : V ≤ LB.wchart D.toPre.P.L (K := PUnit) (fun _ => eSec D.toPre.P.A) (fun _ => j) := fun x hx =>
    Set.mem_iInter.2 fun _ => hle hx
  obtain ⟨u, e₃⟩ : ∃ u : Γ(Spec (CommRingCat.of R), V),
      (val D.toPre.rigK (jFK (R := R) F) y J).val = gs (jFK (R := R) F ≫ jK R) y V u := by
    refine ⟨((Spec (CommRingCat.of R)).presheaf.map (homOfLE hle').op).hom (D.toPre.rig.s (fun _ => j)).val, ?_⟩
    have a₁ : val D.toPre.rigK (jFK (R := R) F) y J = val (L := D.toPre.P.L) (φ := fun _ : PUnit => eSec D.toPre.P.A)
        (ε := fun _ => 1) D.toPre.rig (jFK (R := R) F ≫ jK R) y J := val_pull hJ _ _ _
    rw [a₁, val_of _ _ y J (fun _ => j) (fun _ => hJj PUnit.unit)]
    exact (gs_unit _ y _ (hle' hy) _).symm.trans (gs_res _ y hle' hy _).symm
  have t₀ := τ 0
  have t₁ := τ (-z)
  rw [val_tau _ _ _ hJ, add_zero] at t₀
  rw [val_tau _ _ _ hJ, add_neg_cancel] at t₁
  have t : val (D.toPre.psi z) (jFK (R := R) F) y J * (val (D.toPre.psi (-z)) (jFK (R := R) F) y J *
      (val D.toPre.rigK (jFK (R := R) F) y J * val D.toPre.rigK (jFK (R := R) F) y J)) = 1 := by
    have a₀ := congrArg Additive.ofMul t₀
    have a₁ := congrArg Additive.ofMul t₁
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_one] at a₀ a₁ ⊢
    linear_combination (norm := abel) -a₀ - a₁
  have t' := congrArg Units.val t
  rw [Units.val_mul, Units.val_mul, Units.val_mul, e₁, e₂, e₃, ← gs_mul _ y V hy, ← gs_mul _ y V hy, ← gs_mul _ y V hy,
    Units.val_one] at t'
  have one : r * (r' * (u * u)) - 1 = 0 := eq_zero_of_gs y hp _ (by
    rw [gs_eq _ y V hy] at t' ⊢
    rw [map_sub, map_sub, map_one, map_one, t', sub_self])
  exact not_isUnit_germ hp hIm hr ((IsUnit.of_mul_eq_one _ (sub_eq_zero.1 one)).map _)

theorem main : LL → AllD fun {R} _ _ {I} D F _ _ => ∀ (y y' : D.toPre.X) (g : GtPtF D.toPre F), GtPtF.IsIota y g → GtPtF.IsIota y' g → y = y' := by
  intro _ R _ _ _ I hA D F _ _ _ y y' g h h'
  have hI : I ≠ ⊤ := by
    rintro rfl
    have := hA.2.2.2
    exact not_subsingleton R (IsHausdorff.subsingleton (R := R) (M := R) inferInstance)
  rw [isIota_iff_eq D.tau_bimult] at h h'
  exact sub_eq_zero.1 (eq_zero_of_iota (F := F) hI D _ (by rw [map_sub, ← h, ← h', sub_self]))

end GlobalTheory.IotaInj

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RigidifiedIsoRespectsCubeAndSymmetry
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.RigidIsoCube

theorem surjective_appTop_of_baseChange {Y S Y' S' : Scheme.{0}} {q : Y' ⟶ Y} {p' : Y' ⟶ S'} {p : Y ⟶ S} {j : S' ⟶ S}
    (h : IsPullback q p' p j) [Flat p] [QuasiCompact j] [IsSchemeTheoreticallyDominant j] (e : S ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hs : Function.Surjective p'.appTop.hom) : Function.Surjective p.appTop.hom := by
  have : IsSchemeTheoreticallyDominant q := IsSchemeTheoreticallyDominant.of_isPullback h.flip
  have : QuasiCompact q := MorphismProperty.of_isPullback h.flip ‹_›
  have inj : Function.Injective q.appTop.hom := q.app_injective ⊤
  have cmp : ∀ {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (x : Γ(C, ⊤)),
      f.appTop.hom (g.appTop.hom x) = (f ≫ g).appTop.hom x := fun f g x => by
    rw [Scheme.Hom.comp_appTop]; rfl
  intro a
  obtain ⟨c, hc⟩ := hs (q.appTop.hom a)
  let e' : S' ⟶ Y' := h.lift (j ≫ e) (𝟙 _) (by rw [Category.assoc, he, Category.comp_id, Category.id_comp])
  have h₁ : e' ≫ q = j ≫ e := h.lift_fst _ _ _
  have h₂ : e' ≫ p' = 𝟙 _ := h.lift_snd _ _ _
  have hc' : c = j.appTop.hom (e.appTop.hom a) := by
    have := congrArg e'.appTop.hom hc
    rw [cmp, cmp, h₁, h₂, Scheme.Hom.id_appTop] at this
    rw [cmp]; exact this
  refine ⟨e.appTop.hom a, inj ?_⟩
  rw [← hc, hc', cmp q p, cmp p' j, h.w]

theorem surjective_snd_of_generic (hG : GlobalFnsSt) {S S' : Scheme.{0}} (k : S' ⟶ S) [QuasiCompact k]
    [IsSchemeTheoreticallyDominant k] (G : Over S) [GrpObj G] [Flat G.hom] {A : Over S'} [GrpObj A]
    (hA : IsAbelianScheme A) {g : A.left ⟶ G.left} (hg : IsPullback g A.hom G.hom k) (T : Over S) [Flat T.hom] :
    Function.Surjective (snd G T).left.appTop.hom := by
  let T' : Over S' := Over.mk (pullback.snd T.hom k)
  have : IsSchemeTheoreticallyDominant (pullback.fst T.hom k) :=
    IsSchemeTheoreticallyDominant.of_isPullback (IsPullback.of_hasPullback T.hom k).flip
  have big : IsPullback (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom) G.hom
      (pullback.fst T.hom k ≫ T.hom) := by
    rw [pullback.condition]
    exact (IsPullback.of_hasPullback A.hom T'.hom).paste_horiz hg
  have sq : IsPullback (pullback.lift (pullback.fst A.hom T'.hom ≫ g) (pullback.snd A.hom T'.hom ≫ pullback.fst T.hom k)
      (by rw [big.w, Category.assoc])) (pullback.snd A.hom T'.hom) (pullback.snd G.hom T.hom) (pullback.fst T.hom k) :=
    IsPullback.of_right (by rw [pullback.lift_fst]; exact big) (pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback G.hom T.hom)
  have : Flat (snd G T).left := inferInstanceAs (Flat (pullback.snd G.hom T.hom))
  refine surjective_appTop_of_baseChange (p := (snd G T).left) sq (lift (1 : T ⟶ G) (𝟙 T)).left ?_ (surj_snd hG hA T')
  exact congrArg (fun q => q.left) (lift_snd (1 : T ⟶ G) (𝟙 T))

theorem pmaps_of_section {X X' Y S₀ : Scheme.{0}} {L : LB X} {L' : LB X'} {F : X' ⟶ X} {K : Type} [Fintype K]
    {w : LB.Iso L' (L.pull F)} (hw : PGen w) (hL : L.IsLB) (hL' : L'.IsLB) {φ' : K → (Y ⟶ X')}
    {φ : K → (Y ⟶ X)} {ε : K → ℤ} (a : LB.Gen (LB.LinComb L' φ' ε)) (ha : a.IsGen) (t : LB.Gen (LB.LinComb L φ ε))
    (ht : t.IsGen) (hψ : ∀ k, φ' k ≫ F = φ k) (p : Y ⟶ S₀) (e : S₀ ⟶ Y) (he : e ≫ p = 𝟙 _)
    (hp : Function.Surjective p.appTop.hom)
    (h : ∀ (y : S₀) J J', Good L y J → Good L' y J' → val t e y J =
      (∏ k, gw w (e ≫ φ' k) y (J ((e ≫ φ' k) ≫ F)) (J' (e ≫ φ' k)) ^ ε k) * val a e y J') :
    PMaps w φ' φ ε a t (𝟙 Y) := by
  obtain rfl : φ = fun k => φ' k ≫ F := funext fun k => (hψ k).symm
  obtain ⟨t₁, ht₁, hv⟩ := exists_up hw hL hL' a ha
  have key := gen_unique hL p e he hp ht ht₁ (fun y J hJ => by
    choose J' hJ' using fun ψ : S₀ ⟶ X' => exists_chart hL' (ψ y)
    have v := hv _ e y _ _ (Good.mem hJ _ e) (Good.mem hJ' _ e)
    refine (h y J J' hJ hJ').trans (Eq.trans (congrArg₂ (· * ·) ?_ rfl) v.symm)
    simp only [pw, Category.assoc])
  intro Z r z i q hi hq
  rw [Category.comp_id]
  have hi' : r z ∈ LB.wchart L (fun k => φ' k ≫ F) i := Set.mem_iInter.2 hi
  choose J hJ using fun ψ : Z ⟶ X => exists_chart hL (ψ z)
  exact ((gen_trans ht r z hi' (Good.mem hJ _ r)).trans ((congrArg _ (key Z r z J hJ)).trans
    (gen_trans ht₁ r z hi' (Good.mem hJ _ r)).symm)).trans (hv Z r z i q hi' (Set.mem_iInter.2 hq))

end GlobalTheory.RigidIsoCube

namespace GlobalTheory


open RigidIsoCube in
theorem rigidified_iso_respects_cube_and_symmetry : GlobalFnsSt → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] (I : Ideal R), AdmBase R I → ∀ (D D' : DegData R I) (A A' : PolAV (Spec (CommRingCat.of (FractionRing R)))) (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : UnifPre I D A G) (U' : UnifPre I D' A' G) (wL : LB.Iso U'.LG.L (U.LG.L.pull (𝟙 G.left))) (he : eSec G ≫ 𝟙 G.left = 𝟙 _ ≫ eSec G), wL.IsGen → LB.Gen.Maps (LB.linCombIso wL (K := PUnit) (fun _ => eSec G) (fun _ => 1)) U'.LG.rig (rigPullOf (𝟙 G.left) (𝟙 _) he U.LG.L U.LG.rig) → (Geo.Tor.PMaps wL (thφ G (x3 G)) (thφ G (x3 G)) thε U'.cubG.t U.cubG.t (𝟙 _) ∧ Geo.Tor.PMaps wL (K := Fin 2) ![(ι[G]).left, 𝟙 G.left] ![(ι[G]).left, 𝟙 G.left] ![1, -1] U'.symG U.symG (𝟙 G.left)) := by
  intro hG R _ _ _ I _ D D' A A' G _ _ _ U U' wL _ hw _
  have := U.smooth
  have : IsDominant (jK R) := ⟨(PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).2
    (((RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R (FractionRing R))).le.trans bot_le)⟩
  have := IsSchemeTheoreticallyDominant.of_isDominant (jK R)
  have hg : IsPullback (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) A.A.hom G.hom (jK R) := by
    have : IsIso U.gen.inv.left := inferInstanceAs (IsIso ((Over.forget _).map U.gen.inv))
    have s : IsPullback U.gen.inv.left A.A.hom (pullback.snd G.hom (jK R)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨(Over.w U.gen.inv).trans (Category.comp_id _).symm⟩
    simpa using s.paste_horiz (IsPullback.of_hasPullback G.hom (jK R))
  have s₁ : Function.Surjective G.hom.appTop.hom :=
    surjective_appTop_of_baseChange hg (eSec G) (Over.w η[G]) (hG _ _ A.isAb).2
  have : Flat (G ⊗ G).hom := by rw [Over.tensorObj_hom]; infer_instance
  have sj : Function.Surjective ((snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom).appTop.hom :=
    surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _)
      (surj_comp (surjective_snd_of_generic hG (jK R) G A.isAb hg _) s₁)
  have pg := (isGen_iff wL).1 hw
  constructor
  · let e : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G3 G := lift 1 (lift 1 1)
    have he : e.left ≫ (snd G (G ⊗ G)).left ≫ (snd G G).left ≫ G.hom = 𝟙 _ := by
      rw [Over.w, Over.w]; exact Over.w e
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB (φ' := thφ G (x3 G)) (φ := thφ G (x3 G)) (ε := thε)
      U'.cubG.t U'.cubG.isGen U.cubG.t U.cubG.isGen (fun _ => Category.comp_id _) _ e.left he sj fun y J J' hJ hJ' => ?_
    have p := prod_cub (1 : 𝟙_ (Over (Spec (CommRingCat.of R))) ⟶ G) 1 1
      (fun q => gw wL q y (J (q ≫ 𝟙 _)) (J' q))
    rw [_root_.mul_one, _root_.mul_one] at p
    refine ((isCub_cubV U.cubG hJ).face 1 1).trans
      (Eq.trans ?_ (congrArg₂ (· * ·) p ((isCub_cubV U'.cubG hJ').face 1 1)).symm)
    group
  · have oi : eSec G ≫ (ι[G]).left = eSec G := by
      have : η[G] ≫ ι[G] = η[G] := by simp
      exact congrArg (fun q => q.left) this
    refine pmaps_of_section pg U.LG.isLB U'.LG.isLB U'.symG U'.symG_gen U.symG U.symG_gen
      (fun _ => Category.comp_id _) G.hom (eSec G) (Over.w η[G]) s₁ fun y J J' hJ hJ' => ?_
    have a := val_corr hJ U.symG_rig (𝟙 _)
    rw [val_pull hJ, val_one, Category.id_comp] at a
    have b := val_corr hJ' U'.symG_rig (𝟙 _)
    rw [val_pull hJ', val_one, Category.id_comp] at b
    rw [a, b, Fin.prod_univ_two]
    show 1 = gw wL (eSec G ≫ (ι[G]).left) y (J ((eSec G ≫ (ι[G]).left) ≫ 𝟙 _)) (J' (eSec G ≫ (ι[G]).left)) ^ (1 : ℤ) *
      gw wL (eSec G ≫ 𝟙 _) y (J ((eSec G ≫ 𝟙 _) ≫ 𝟙 _)) (J' (eSec G ≫ 𝟙 _)) ^ (-1 : ℤ) * 1
    simp only [oi, Category.comp_id]
    simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjMul
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

theorem rosatiAdj_mul : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A] (L : RigLB A) (c : CubicalStr A L) (f g f' g' : A ⟶ A), RosatiAdj A L.L f g → RosatiAdj A L.L f' g' → RosatiAdj A L.L (f * f') (g * g') := by
  intro S A _ _ L c f g f' g' h h' s
  obtain ⟨U, hs, t, ht⟩ := h s
  obtain ⟨U', hs', t', ht'⟩ := h' s
  refine ⟨U ⊓ U', ⟨hs, hs'⟩, ?_⟩
  let W : (A ⊗ A).left.Opens := (A ⊗ A).hom ⁻¹ᵁ (U ⊓ U')
  have l : W ≤ (A ⊗ A).hom ⁻¹ᵁ U := fun _ hy => hy.1
  have l' : W ≤ (A ⊗ A).hom ⁻¹ᵁ U' := fun _ hy => hy.2
  let T : Over S := Over.mk (W.ι ≫ (A ⊗ A).hom)
  let ρ : T ⟶ A ⊗ A := Over.homMk W.ι rfl
  obtain ⟨x, y, hxy⟩ : ∃ x y : T ⟶ A, (lift x y).left = W.ι :=
    ⟨ρ ≫ fst A A, ρ ≫ snd A A, congrArg (fun q => q.left) (lift_comp_fst_snd ρ)⟩
  have pr : ∀ (a b : A ⟶ A) (V : Type) [CommGroup V] (k : (T.left ⟶ A.left) → V) (Y : Scheme.{0})
      (m : T.left ⟶ Y) (n : Y ⟶ (A ⊗ A).left), m ≫ n = W.ι →
      ∏ i, k (m ≫ n ≫ rosatiφ A a b i) ^ rosatiε i =
      k ((x ≫ a) * y).left * (k (x ≫ a).left)⁻¹ * (k y.left)⁻¹ * (k (x * (y ≫ b)).left)⁻¹ * k x.left *
        k (y ≫ b).left := fun a b V _ k Y m n e =>
    (Finset.prod_congr rfl fun i _ => by rw [← Category.assoc, e, hxy]).trans (prod_ros a b x y k)
  obtain ⟨u, hu, -⟩ := exists_gen L.isLB (φ' := fun i => W.ι ≫ rosatiφ A (f * f') (g * g') i) (ε' := rosatiε)
    (fun V _ k => by
      refine (DVR.prod_sum₂ (K := Fin 6 ⊕ Fin 6) (K' := thK ⊕ thK) (U := V) _
        (DVR.prod_sum₂ (K := Fin 6) (K' := Fin 6) (U := V) _
          (pr f g V k _ _ _ (Scheme.homOfLE_ι _ l)) (pr f' g' V k _ _ _ (Scheme.homOfLE_ι _ l')))
        (DVR.prod_sum₂ (K := thK) (K' := thK) (U := V) _ (prod_cub (x ≫ f) (x ≫ f') y k)
          (DVR.prod_neg _ _ (prod_cub x (y ≫ g) (y ≫ g') k)))).trans ?_
      refine Eq.trans ?_ ((pr (f * f') (g * g') V k _ (𝟙 _) W.ι (Category.id_comp _)).symm.trans
        (Finset.prod_congr rfl fun i _ => by rw [Category.id_comp]))
      rw [MonObj.comp_mul, MonObj.comp_mul, _root_.mul_assoc x]
      apply Additive.ofMul.injective
      simp only [ofMul_mul, ofMul_inv]
      abel)
    (LB.mulGen L.L _ _ _ _
      (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ t ((A ⊗ A).left.homOfLE l))
        (LB.pullGen L.L _ _ t' ((A ⊗ A).left.homOfLE l')))
      (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (x ≫ f) (lift (x ≫ f') y)).left)
        (LB.invGen L.L _ _ (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift x (lift (y ≫ g) (y ≫ g'))).left))))
    (DVR.mulGen_isGen _ _ _ _ _ _ _
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ ht _) (DVR.pullGen_isGen _ _ _ _ ht' _))
      (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _)
        (DVR.invGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ c.isGen _))))
  exact ⟨u, hu⟩

end GlobalTheory
end

