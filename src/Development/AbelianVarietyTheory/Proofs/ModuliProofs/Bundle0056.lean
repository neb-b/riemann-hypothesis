module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.FiniteHomogeneousInf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CoordOfHasWeight
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsSectionCoordinateVectorOfLocallyOnRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section
namespace GlobalTheory.ZM

theorem stalkMap_germ_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) (W : Y.Opens) (W' : Z.Opens) (h : W' ≤ f ⁻¹ᵁ W)
    (z : Z) (hz : z ∈ W') (s : Γ(Y, W)) :
    (f.stalkMap z).hom ((Y.presheaf.germ W (f z) (h hz)).hom s) =
      (Z.presheaf.germ W' z hz).hom ((f.appLE W W' h).hom s) := by
  have e : Y.presheaf.germ W (f z) (h hz) ≫ f.stalkMap z = f.appLE W W' h ≫ Z.presheaf.germ W' z hz := by
    erw [Scheme.Hom.germ_stalkMap]
    rw [Scheme.Hom.appLE, Category.assoc, TopCat.Presheaf.germ_res]
  exact congrArg (fun g => g.hom s) e

theorem sec_eq_of_openImm {Y : Scheme.{0}} (W : Y.Opens) (s t : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (_ : IsOpenImmersion f) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ (f.appLE W W' h).hom s = (f.appLE W W' h).hom t) : s = t := by
  apply TopCat.Presheaf.section_ext Y.sheaf W s t
  intro p hp
  obtain ⟨Z, f, _, z, W', h, hz, rfl, e⟩ := H p hp
  apply (ConcreteCategory.injective_of_mono_of_preservesPullback (f.stalkMap z))
  have e1 := stalkMap_germ_appLE f W W' h z hz s
  have e2 := stalkMap_germ_appLE f W W' h z hz t
  rw [e] at e1
  exact e1.trans e2.symm

theorem sec_isUnit_of_pull {Y : Scheme.{0}} (W : Y.Opens) (s : Γ(Y, W))
    (H : ∀ p ∈ W, ∃ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (W' : Z.Opens)
      (h : W' ≤ f ⁻¹ᵁ W), z ∈ W' ∧ f z = p ∧ IsUnit ((f.appLE W W' h).hom s)) : IsUnit s := by
  apply Y.toRingedSpace.isUnit_of_isUnit_germ W s
  intro p hp
  obtain ⟨Z, f, z, W', h, hz, rfl, u⟩ := H p hp
  apply isUnit_of_map_unit (f.stalkMap z).hom
  rw [stalkMap_germ_appLE f W W' h z hz]
  exact u.map _

def spConst (R : Type) [CommRing R] (W : (Sp R).Opens) : R →+* Γ(Sp R, W) :=
  (resG (Sp R) (le_top : W ≤ ⊤)).comp (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

theorem appLE_spConst {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (W : (Sp R).Opens)
    (W' : (Sp R').Opens) (h : W' ≤ spMap φ ⁻¹ᵁ W) (r : R) :
    ((spMap φ).appLE W W' h).hom (spConst R W r) = spConst R' W' (φ r) := by
  have key : (Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.map (homOfLE (le_top : W ≤ ⊤)).op ≫
      (spMap φ).appLE W W' h =
      CommRingCat.ofHom φ ≫ (Scheme.ΓSpecIso (CommRingCat.of R')).inv ≫
        (Sp R').presheaf.map (homOfLE (le_top : W' ≤ ⊤)).op := by
    rw [Scheme.Hom.map_appLE, ← Category.assoc, Scheme.ΓSpecIso_inv_naturality, Category.assoc]
    rfl
  exact congrArg (fun g => g.hom r) key

private theorem mem_pull_U_iff' {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j : PUnit → M.ι) (p : T) :
    p ∈ (M.pull y).U j ↔ y p ∈ M.U (j PUnit.unit) := by
  unfold LB.pull LB.LinComb LB.wchart
  simp only [TopologicalSpace.Opens.mem_mk, Set.mem_iInter, Set.mem_preimage]
  exact ⟨fun h => h _, fun h _ => h⟩

private theorem appLE_appLE_lemma_2 {X Y Z : Scheme.{0}} (f : Z ⟶ Y) (g : Y ⟶ X) (U : X.Opens) (V : Y.Opens)
    (V' : Z.Opens) (hV : V ≤ g ⁻¹ᵁ U) (hV' : V' ≤ f ⁻¹ᵁ V) (h3 : V' ≤ (f ≫ g) ⁻¹ᵁ U) (s : Γ(X, U)) :
    (f.appLE V V' hV').hom ((g.appLE U V hV).hom s) = ((f ≫ g).appLE U V' h3).hom s := by
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]

private theorem appLE_resG_eq_resG_appLE {Y Z : Scheme.{0}} (f : Z ⟶ Y) {V1 V2 : Y.Opens} {W1 W2 : Z.Opens}
    (hV : V1 ≤ V2) (hW : W1 ≤ W2) (h1 : W1 ≤ f ⁻¹ᵁ V1) (h2 : W2 ≤ f ⁻¹ᵁ V2) (s : Γ(Y, V2)) :
    (f.appLE V1 W1 h1).hom (resG Y hV s) = resG Z hW ((f.appLE V2 W2 h2).hom s) := by
  simp only [resG]
  rw [← RingHom.comp_apply, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE, ← RingHom.comp_apply,
    ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]

private theorem pull_g_coe_eq_appLE_g {X T : Scheme.{0}} (M : LB X) (y : T ⟶ X) (j j' : PUnit → M.ι)
    (h : (M.pull y).U j ⊓ (M.pull y).U j' ≤ y ⁻¹ᵁ (M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) :
    (((M.pull y).g j j' : (Γ(T, (M.pull y).U j ⊓ (M.pull y).U j'))ˣ) : Γ(T, (M.pull y).U j ⊓ (M.pull y).U j')) =
      (y.appLE _ _ h).hom (M.g (j PUnit.unit) (j' PUnit.unit) : Γ(X, M.U (j PUnit.unit) ⊓ M.U (j' PUnit.unit))) := by
  unfold LB.pull LB.LinComb
  simp [pullU, res, Scheme.Hom.appLE]
  rfl

theorem secCoord_of_locally (X : Scheme.{0}) (M : LB X) (I : Type) (th : I → M.Sec) (R : Type) [CommRing R]
    (x : Sp R ⟶ X) (v : I → R) (_hM : M.IsLB) (hv : Ideal.span (Set.range v) = ⊤)
    (H : ∀ p : Sp R, ∃ (R' : Type) (_ : CommRing R') (φ : R →+* R'), IsOpenImmersion (spMap φ) ∧
      p ∈ Set.range (spMap φ) ∧ SecCoord M th (spMap φ ≫ x) (fun i => φ (v i))) :
    SecCoord M th x v := by
  have h1 : (1 : R) ∈ Ideal.span (Set.range v) := by rw [hv]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := Finsupp.mem_ideal_span_range_iff_exists_finsupp.1 h1
  have W1 : ∀ j : PUnit → M.ι, (M.pull x).U j ≤ x ⁻¹ᵁ M.U (j PUnit.unit) :=
    fun j p hp => (mem_pull_U_iff' M x j p).1 hp
  have W2 : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (j : PUnit → M.ι),
      (M.pull (spMap φ ≫ x)).U j ≤ spMap φ ⁻¹ᵁ (M.pull x).U j :=
    fun φ j z hz => (mem_pull_U_iff' M x j _).2 ((mem_pull_U_iff' M _ j z).1 hz)
  let t : ∀ j : PUnit → M.ι, Γ(Sp R, (M.pull x).U j) := fun j =>
    c.sum (fun i a => spConst R _ a * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit)))
  have pt : ∀ {R' : Type} [CommRing R'] (φ : R →+* R') (τ' : (M.pull (spMap φ ≫ x)).Gen),
      (∀ i j h, ((spMap φ ≫ x).appLE (M.U (j PUnit.unit)) ((M.pull (spMap φ ≫ x)).U j) h).hom
          ((th i).f (j PUnit.unit)) = spConst R' _ (φ (v i)) * (τ'.s j).val) →
      ∀ j, ((spMap φ).appLE _ _ (W2 φ j)).hom (t j) = (τ'.s j).val := by
    intro R' _ φ τ' hco j
    have e1 : ∀ i, ((spMap φ).appLE _ _ (W2 φ j)).hom
        (spConst R _ (c i) * (x.appLE _ _ (W1 j)).hom ((th i).f (j PUnit.unit))) =
        spConst R' _ (φ (c i) * φ (v i)) * (τ'.s j).val := by
      intro i
      rw [map_mul, appLE_spConst, appLE_appLE_lemma_2 (spMap φ) x _ _ _ (W1 j) (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp), map_mul, _root_.mul_assoc]
      exact congrArg (spConst R' _ (φ (c i)) * ·) (hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp))
    have e2 : ∑ i ∈ c.support, φ (c i) * φ (v i) = 1 := by
      have := congrArg φ hc
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_one, Finsupp.sum, map_sum] at this
      simpa [map_mul] using this
    show ((spMap φ).appLE _ _ (W2 φ j)).hom (∑ i ∈ c.support, _) = _
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_congr rfl (fun i _ => e1 i), ← Finset.sum_mul, ← map_sum, e2, map_one, _root_.one_mul]
  have hu : ∀ j, IsUnit (t j) := by
    intro j
    apply sec_isUnit_of_pull
    intro p hp
    obtain ⟨R', _, φ, _, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, z, (M.pull (spMap φ ≫ x)).U j, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [pt φ τ' hco j]; exact (τ'.s j).isUnit
  unfold SecCoord
  refine ⟨⟨fun j => (hu j).unit⟩, ?_, ?_⟩
  · intro i j
    apply Units.ext
    show resG _ inf_le_left (t i) = ((M.pull x).g i j).val * resG _ inf_le_right (t j)
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', hg, hco⟩ := H p
    have Wi : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
        spMap φ ⁻¹ᵁ ((M.pull x).U i ⊓ (M.pull x).U j) := fun z hz => ⟨W2 φ i hz.1, W2 φ j hz.2⟩
    refine ⟨Sp R', spMap φ, hoi, z, _, Wi, ?_, rfl, ?_⟩
    · exact ⟨(mem_pull_U_iff' M _ i z).2 ((mem_pull_U_iff' M x i _).1 hp.1),
        (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp.2)⟩
    · rw [map_mul, appLE_resG_eq_resG_appLE (spMap φ) inf_le_left inf_le_left Wi (W2 φ i),
        appLE_resG_eq_resG_appLE (spMap φ) inf_le_right inf_le_right Wi (W2 φ j), pt φ τ' hco i, pt φ τ' hco j]
      have h3 : (M.pull (spMap φ ≫ x)).U i ⊓ (M.pull (spMap φ ≫ x)).U j ≤
          (spMap φ ≫ x) ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
        fun q hq => ⟨(mem_pull_U_iff' M _ i q).1 hq.1, (mem_pull_U_iff' M _ j q).1 hq.2⟩
      rw [pull_g_coe_eq_appLE_g M x i j (fun q hq => ⟨W1 i hq.1, W1 j hq.2⟩)]
      erw [appLE_appLE_lemma_2 (spMap φ) x _ _ _ _ Wi h3, ← pull_g_coe_eq_appLE_g M (spMap φ ≫ x) i j h3]
      exact congrArg Units.val (hg i j)
  · intro i j h
    show _ = spConst R _ (v i) * t j
    apply sec_eq_of_openImm
    intro p hp
    obtain ⟨R', _, φ, hoi, ⟨z, rfl⟩, τ', _, hco⟩ := H p
    refine ⟨Sp R', spMap φ, hoi, z, _, W2 φ j, ?_, rfl, ?_⟩
    · exact (mem_pull_U_iff' M _ j z).2 ((mem_pull_U_iff' M x j _).1 hp)
    · rw [map_mul, appLE_spConst, pt φ τ' hco j, appLE_appLE_lemma_2 (spMap φ) x _ _ _ h (W2 φ j)
        (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)]
      exact hco i j (fun p hp => (mem_pull_U_iff' M _ j p).1 hp)

end GlobalTheory.ZM
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.LineBundleTrivialIsoDescendField
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace GlobalTheory

namespace FieldDescentGen

variable {X₀ X : Scheme.{0}}

theorem pull_le (M : LB X₀) (φ : X ⟶ X₀) (j : PUnit → M.ι) : (M.pull φ).U j ≤ φ ⁻¹ᵁ M.U (j PUnit.unit) :=
  fun _ hy => mem_pull.1 hy

def secPull (M : LB X₀) (φ : X ⟶ X₀) (s : M.Sec) : (M.pull φ).Sec where
  f j := (φ.appLE _ _ (pull_le M φ j)).hom (s.f (j PUnit.unit))
  compat i j := by
    have h : (M.pull φ).U i ⊓ (M.pull φ).U j ≤ φ ⁻¹ᵁ (M.U (i PUnit.unit) ⊓ M.U (j PUnit.unit)) :=
      fun _ hy => ⟨pull_le M φ i hy.1, pull_le M φ j hy.2⟩
    have e := congrArg (φ.appLE _ _ h).hom (s.compat (i PUnit.unit) (j PUnit.unit))
    rw [map_mul] at e
    have g : ((M.pull φ).g i j : Γ(X, (M.pull φ).U i ⊓ (M.pull φ).U j)) =
        (φ.appLE _ _ h).hom (M.g (i PUnit.unit) (j PUnit.unit)) := by
      have gu : (M.pull φ).g i j = res h (pullU φ _ (M.g (i PUnit.unit) (j PUnit.unit))) :=
        (Fintype.prod_unique fun k : PUnit => (res h (pullU φ _ (M.g (i k) (j k)))) ^ (1 : ℤ)).trans (zpow_one _)
      exact congrArg Units.val gu
    rw [g]
    simp only [← CommRingCat.comp_apply, Scheme.Hom.appLE_map, Scheme.Hom.map_appLE] at e ⊢
    exact e

theorem exists_ratio {L : LB X} (hL : L.IsLB) (t : L.Gen) (ht : t.IsGen) (s : L.Sec) :
    ∃ u : Γ(X, ⊤), ∀ j, s.f j =
      (X.presheaf.map (homOfLE (le_top : L.U j ≤ ⊤)).op).hom u * (t.s j).val := by
  obtain ⟨u, hu⟩ := Out.TLinPf.glue L.U hL.cover (fun j => s.f j * ((t.s j)⁻¹).val) (fun i j => by
    have e : res (inf_le_right : L.U i ⊓ L.U j ≤ L.U j) (t.s j)⁻¹ =
        L.g i j * res (inf_le_left : L.U i ⊓ L.U j ≤ L.U i) (t.s i)⁻¹ := by
      rw [map_inv, map_inv, ht i j, mul_inv, mul_inv_cancel_left]
    have e' : (X.presheaf.map (homOfLE (inf_le_right : L.U i ⊓ L.U j ≤ L.U j)).op).hom ((t.s j)⁻¹).val =
        (L.g i j).val * (X.presheaf.map (homOfLE (inf_le_left : L.U i ⊓ L.U j ≤ L.U i)).op).hom ((t.s i)⁻¹).val :=
      congrArg Units.val e
    rw [map_mul, map_mul, s.compat i j, e']
    ring)
  exact ⟨u, fun j => by rw [hu j, _root_.mul_assoc, Units.inv_mul, _root_.mul_one]⟩

theorem isUnit_of_surjective (φ : X ⟶ X₀) [Surjective φ] {U : X₀.Opens} {V : X.Opens} (h : V ≤ φ ⁻¹ᵁ U)
    (h' : φ ⁻¹ᵁ U ≤ V) (a : Γ(X₀, U)) (ha : IsUnit ((φ.appLE U V h).hom a)) : IsUnit a := by
  refine RingedSpace.isUnit_of_isUnit_germ X₀.toLocallyRingedSpace.toRingedSpace U a fun x hx => ?_
  obtain ⟨y, rfl⟩ := φ.surjective x
  have hy : y ∈ X.basicOpen ((φ.appLE U V h).hom a) := by
    rw [X.basicOpen_of_isUnit ha]; exact h' hx
  rw [Scheme.basicOpen_appLE] at hy
  exact (X₀.mem_basicOpen a _ hx).1 hy.2

def chartDiv (M N : LB X₀) (φ : X ⟶ X₀) :
    ChartPull ((LB.div N M).pull φ) (LB.div (N.pull φ) (M.pull φ)) (𝟙 X) where
  idx J := (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
  le J y hy := ⟨mem_pull.2 (mem_pull.1 hy).1, mem_pull.2 (mem_pull.1 hy).2⟩
  g y J J' hj hj' := by
    have a := mem_pull.1 hj
    have a' := mem_pull.1 hj'
    refine (gm_pull_g (LB.div N M) φ (𝟙 X) y J J' hj hj').trans
      ((gm_div M N (𝟙 X ≫ φ) y (J PUnit.unit) (J' PUnit.unit) ⟨a, a'⟩).trans (Eq.symm ?_))
    refine (gm_div (M.pull φ) (N.pull φ) (𝟙 X) y (fun _ => (J PUnit.unit).1, fun _ => (J PUnit.unit).2)
      (fun _ => (J' PUnit.unit).1, fun _ => (J' PUnit.unit).2)
      ⟨⟨mem_pull.2 a.1, mem_pull.2 a.2⟩, mem_pull.2 a'.1, mem_pull.2 a'.2⟩).trans ?_
    exact congrArg₂ (fun u v => u * v⁻¹)
      (gm_pull_g N φ (𝟙 X) y _ _ (mem_pull.2 a.1) (mem_pull.2 a'.1))
      (gm_pull_g M φ (𝟙 X) y _ _ (mem_pull.2 a.2) (mem_pull.2 a'.2))

theorem exists_gen {K₀ K : Type} [Field K₀] [Field K] (i : K₀ →+* K) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K)
    (φ : X ⟶ X₀) [Smooth p₀] [IsProper p₀] [GeometricallyConnected p₀] (H : IsPullback φ p p₀ (spMap i))
    (M : LB X₀) (hM : M.IsLB) (t : (M.pull φ).Gen) (ht : t.IsGen) : ∃ t : M.Gen, t.IsGen := by
  have hb : Function.Bijective p.appTop.hom := GlobalTheory.bijective_appTop_of_smooth_of_isProper_of_geometricallyConnected K X p
    (MorphismProperty.of_isPullback (P := @Smooth) H inferInstance)
    (MorphismProperty.of_isPullback (P := @IsProper) H inferInstance)
    (MorphismProperty.of_isPullback (P := @GeometricallyConnected) H inferInstance)
  have hF : IsField Γ(X, ⊤) :=
    ((Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.trans
      (RingEquiv.ofBijective p.appTop.hom hb)).symm.toMulEquiv.isField (Field.toIsField K)
  have : Surjective φ := ((GlobalTheory.FieldBaseChange.epi_and_isMonHom_iff K₀ K i).1 X₀ X p₀ p φ H).2.2.1
  have hP := LB.isLB_pull hM φ
  let ts : (M.pull φ).Sec := ⟨fun j => (t.s j).val, fun a b => congrArg Units.val (ht a b)⟩
  obtain ⟨n, c, s, hs⟩ := GlobalTheory.SectionsDescent.main K₀ K i X₀ X p₀ p φ M hM H ts
  choose u hu using fun a => exists_ratio hP t ht (secPull M φ (s a))
  have hne : ∃ a, u a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    have := hF.nontrivial
    refine one_ne_zero (Out.TLinPf.eq_local (M.pull φ).U hP.cover 1 0 fun j => ?_)
    have h0 : (t.s j).val = 0 := by
      refine (hs j (pull_le M φ j)).trans (Finset.sum_eq_zero fun a _ => ?_)
      have e : (φ.appLE _ _ (pull_le M φ j)).hom ((s a).f (j PUnit.unit)) = _ := hu a j
      rw [e, hcon a, map_zero, zero_mul, mul_zero]
    rw [map_one, map_zero, ← (t.s j).mul_inv, h0, zero_mul]
  obtain ⟨a, ha⟩ := hne
  obtain ⟨v, hv⟩ := hF.mul_inv_cancel ha
  have hua : IsUnit (u a) := IsUnit.of_mul_eq_one v hv
  have hunit : ∀ k, IsUnit ((s a).f k) := fun k =>
    isUnit_of_surjective φ (pull_le M φ fun _ => k) (fun _ hy => mem_pull.2 hy) _ (by
      have e : (φ.appLE _ _ (pull_le M φ fun _ => k)).hom ((s a).f k) = _ := hu a fun _ => k
      rw [e]
      exact (hua.map _).mul (Units.isUnit _))
  exact ⟨⟨fun k => (hunit k).unit⟩, fun k l => Units.ext ((s a).compat k l)⟩

end FieldDescentGen


open FieldDescentGen in
theorem lb_gen_iso_descend_field : ∀ (K₀ K : Type) [Field K₀] [Field K] (i : K₀ →+* K) (X₀ X : Scheme.{0}) (p₀ : X₀ ⟶ Sp K₀) (p : X ⟶ Sp K) (φ : X ⟶ X₀), Smooth p₀ → IsProper p₀ → GeometricallyConnected p₀ → IsPullback φ p p₀ (spMap i) → (∀ M : LB X₀, M.IsLB → (∃ t : (M.pull φ).Gen, t.IsGen) → ∃ t : M.Gen, t.IsGen) ∧ ∀ M N : LB X₀, M.IsLB → N.IsLB → LBIso (M.pull φ) (N.pull φ) → LBIso M N := by
  intro K₀ K _ _ i X₀ X p₀ p φ h₁ h₂ h₃ H
  refine ⟨fun M hM ⟨t, ht⟩ => exists_gen i p₀ p φ H M hM t ht, fun M N hM hN ⟨w, hw⟩ => ?_⟩
  exact exists_gen i p₀ p φ H (LB.div N M) (LB.isLB_div hN hM) _
    (GtBaseChange.genPull_isGen (chartDiv M N φ) hw)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.MorphismsGenericSpreadOut
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.GenericSpread

theorem exists_away_of_fg {R K : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (S : Subalgebra R K) (hS : S.FG) :
    ∃ (f : R) (_ : f ≠ 0) (g : S →ₐ[R] Localization.Away f) (l : Localization.Away f →ₐ[R] K),
      ∀ x, l (g x) = x := by
  classical
  obtain ⟨t, rfl⟩ := hS
  choose p hp using fun x : K => IsLocalization.surj (nonZeroDivisors R) x
  set f : R := ∏ x ∈ t, ((p x).2 : R) with hf_def
  have hf0 : f ≠ 0 := Finset.prod_ne_zero_iff.mpr fun x _ => nonZeroDivisors.ne_zero (p x).2.2
  have hfK : IsUnit (algebraMap R K f) :=
    ((map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr hf0).isUnit
  have hpow : ∀ y : Submonoid.powers f, IsUnit (algebraMap R K y) := by
    rintro ⟨_, n, rfl⟩
    simpa using hfK.pow n
  let l : Localization.Away f →ₐ[R] K :=
    ⟨IsLocalization.lift (M := Submonoid.powers f) (S := Localization.Away f) hpow,
      fun r => IsLocalization.lift_eq hpow r⟩
  have hl : Function.Injective l := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro z hz
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective (Submonoid.powers f) z
    have h1 := congrArg l (IsLocalization.mk'_spec (Localization.Away f) a s)
    rw [map_mul, hz, zero_mul, AlgHom.commutes] at h1
    have ha : a = 0 := (IsFractionRing.injective R K) (by rw [← h1, map_zero])
    subst ha
    exact IsLocalization.mk'_zero s
  have hle : Algebra.adjoin R (↑t : Set K) ≤ l.range := by
    rw [Algebra.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, AlgHom.mem_range]
    have hdvd : ((p x).2 : R) ∣ f := Finset.dvd_prod_of_mem _ (Finset.mem_coe.mp hx)
    have hu : IsUnit (algebraMap R (Localization.Away f) ((p x).2 : R)) :=
      isUnit_of_dvd_unit (map_dvd _ hdvd) (IsLocalization.Away.algebraMap_isUnit f)
    refine ⟨algebraMap R _ (p x).1 * ↑hu.unit⁻¹, ?_⟩
    have hne : algebraMap R K ((p x).2 : R) ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero (p x).2.2)
    apply mul_right_cancel₀ hne
    calc l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹) * algebraMap R K ((p x).2 : R)
        = l (algebraMap R _ (p x).1 * ↑hu.unit⁻¹ * algebraMap R _ ((p x).2 : R)) := by
          rw [map_mul l _ (algebraMap R _ _), AlgHom.commutes]
      _ = l (algebraMap R _ (p x).1) := by rw [_root_.mul_assoc, IsUnit.val_inv_mul, _root_.mul_one]
      _ = algebraMap R K (p x).1 := AlgHom.commutes l _
      _ = x * algebraMap R K ((p x).2 : R) := (hp x).symm
  refine ⟨f, hf0, (AlgEquiv.ofInjective l hl).symm.toAlgHom.comp (Subalgebra.inclusion hle), l,
    fun x => ?_⟩
  show l ((AlgEquiv.ofInjective l hl).symm (Subalgebra.inclusion hle x)) = x
  rw [← AlgEquiv.ofInjective_apply l hl, AlgEquiv.apply_symm_apply]
  rfl

end GlobalTheory.GenericSpread

namespace GlobalTheory

theorem morphisms_generic_spread_out :
    ∀ (R K : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] [Field K] [Algebra R K] [IsFractionRing R K] (B Z : Scheme.{0}) (pB : B ⟶ Sp R) (pZ : Z ⟶ Sp R) (I : Type) [Finite I] (u : I → (pullback pB (spMap (algebraMap R K)) ⟶ Z)), QuasiCompact pB → QuasiSeparated pB → LocallyOfFinitePresentation pZ → (∀ i, u i ≫ pZ = pullback.fst _ _ ≫ pB) → ∃ (f : R) (_ : f ≠ 0) (u' : I → (pullback pB (spMap (algebraMap R (Localization.Away f))) ⟶ Z)), ∀ i, u' i ≫ pZ = pullback.fst _ _ ≫ pB ∧ ∀ j : pullback pB (spMap (algebraMap R K)) ⟶ pullback pB (spMap (algebraMap R (Localization.Away f))), j ≫ pullback.fst _ _ = pullback.fst _ _ → j ≫ u' i = u i := by
  intro R K _ _ _ _ _ _ B Z pB pZ I _ u hqc hqs hlfp hu
  have := hqc
  have := hqs
  have := hlfp
  obtain ⟨S, ψ, hSfg, -, hψ⟩ :=
    GlobalTheory.Spread.exists_fg_forall_comp_eq pB pZ u hu ⊥ Subalgebra.fg_bot
  obtain ⟨f, hf0, g, l, hgl⟩ := GlobalTheory.GenericSpread.exists_away_of_fg S hSfg
  have hmono : Mono (spMap (algebraMap R (Localization.Away f))) := inferInstance
  refine ⟨f, hf0, fun i => GlobalTheory.Spread.bcMap pB g ≫ ψ i, fun i => ⟨?_, fun j hj => ?_⟩⟩
  · rw [Category.assoc, (hψ i).1, ← Category.assoc, GlobalTheory.Spread.bcMap_fst]
  · have hj2 : j ≫ pullback.snd _ _ = pullback.snd _ _ ≫ spMap l.toRingHom := by
      apply (cancel_mono (spMap (algebraMap R (Localization.Away f)))).mp
      rw [Category.assoc, Category.assoc, GlobalTheory.Spread.spMap_algHom_comp, ← pullback.condition,
        ← pullback.condition, ← Category.assoc, hj]
    have hjb : j = GlobalTheory.Spread.bcMap pB l := GlobalTheory.Spread.eq_bcMap pB l hj hj2
    rw [hjb, ← Category.assoc, GlobalTheory.Spread.bcMap_comp_of_eq pB g l S.val hgl]
    exact (hψ i).2

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothGenericFibreOfAffineOpens
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.ZM

namespace GlobalTheory

theorem smoothOfRelativeDimension_genericFibre_of_affine :
    ∀ (o : Type) [CommRing o] [IsDomain o] (X : Scheme.{0}) (s : X ⟶ Sp o) (d : ℕ), (∀ (R : Type) [CommRing R] [Algebra o R] (x : Sp R ⟶ X), IsOpenImmersion x → x ≫ s = spMap (algebraMap o R) → SmoothOfRelativeDimension d (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)))) → SmoothOfRelativeDimension d (pullback.snd s (spMap (algebraMap o (FractionRing o)))) := by
  intro o _ _ X s d h
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension d) :=
    HasRingHomProperty.instIsZariskiLocalAtSource
  refine IsZariskiLocalAtSource.of_openCover (P := @SmoothOfRelativeDimension d)
    (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))) fun i => ?_
  let R : CommRingCat.{0} := X.affineOpenCover.X i
  let x : Spec R ⟶ X := X.affineOpenCover.f i
  have hx : IsOpenImmersion x := X.affineOpenCover.map_prop i
  let φ : CommRingCat.of o ⟶ R := Spec.preimage (x ≫ s)
  letI : Algebra o R := φ.hom.toAlgebra
  have hφ : x ≫ s = spMap (algebraMap o R) := (Spec.map_preimage (x ≫ s)).symm
  have H := h R x hx hφ
  have sq := isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct o (FractionRing o) R)
  have sq' : IsPullback (Spec.map (CommRingCat.ofHom
      (Algebra.TensorProduct.includeRight (R := o) (A := FractionRing o) (B := R)).toRingHom))
      (spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R))) (x ≫ s)
      (spMap (algebraMap o (FractionRing o))) := by
    rw [hφ]
    exact sq.flip
  have e : (Scheme.Pullback.openCoverOfLeft X.affineOpenCover.openCover s
      (spMap (algebraMap o (FractionRing o)))).f i ≫ pullback.snd s _ =
      sq'.isoPullback.inv ≫ spMap (algebraMap (FractionRing o) (FractionRing o ⊗[o] R)) := by
    rw [IsPullback.isoPullback_inv_snd]
    exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)
  rw [e]
  have : MorphismProperty.RespectsIso (@SmoothOfRelativeDimension d) := hloc.1
  exact @MorphismProperty.RespectsIso.precomp _ _ (@SmoothOfRelativeDimension d) this _ _ _
    sq'.isoPullback.inv sq'.isoPullback.isIso_inv _ H

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.SmoothOfRelativeDimensionOfIsPullbackIsDominant
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory

theorem smoothOfRelativeDimension_of_isPullback_isDominant :
    ∀ (X U Y Y' : Scheme.{0}) (j : U ⟶ X) (p : Y ⟶ X) (p' : Y' ⟶ U) (φ : Y' ⟶ Y) (g : ℕ),
      IsPullback φ p' p j → IsDominant j → Smooth p → SmoothOfRelativeDimension g p' →
        SmoothOfRelativeDimension g p := by
  intro X U Y Y' j p p' φ g hpb hj hp hg
  have := hp
  have key : ∀ y : Y, ∃ W : Y.Opens, y ∈ W ∧ SmoothOfRelativeDimension g (W.ι ≫ p) := by
    intro y
    obtain ⟨n, W, hyW, hn⟩ := ReciprocityTheory.ChartRestriction.G.H1.exists_dim p y
    have hopen : IsOpen (p '' (W : Set Y)) := p.isOpenMap _ W.isOpen
    obtain ⟨u, w, hwW, hwu⟩ := hj.denseRange.exists_mem_open hopen ⟨p y, y, hyW, rfl⟩
    obtain ⟨z, hz1, -⟩ := Scheme.Pullback.exists_preimage_pullback w u hwu
    have h1 : φ (hpb.isoPullback.inv z) = w := by
      rw [← Scheme.Hom.comp_apply, hpb.isoPullback_inv_fst, hz1]
    have hng := ReciprocityTheory.ChartRestriction.G.H1.dim_base hpb hn hg (hpb.isoPullback.inv z) (h1 ▸ hwW)
    subst hng
    exact ⟨W, hyW, hn⟩
  choose W hyW hW using key
  have hloc : IsZariskiLocalAtSource (@SmoothOfRelativeDimension.{0} g) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (P := @SmoothOfRelativeDimension.{0} g)
  refine IsZariskiLocalAtSource.of_iSup_eq_top (P := @SmoothOfRelativeDimension.{0} g) W ?_ hW
  rw [eq_top_iff]
  intro y _
  exact TopologicalSpace.Opens.mem_iSup.mpr ⟨y, hyW y⟩

end GlobalTheory
end

