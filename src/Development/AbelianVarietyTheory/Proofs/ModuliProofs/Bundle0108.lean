module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0001
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrimitiveRegularOnSectionNonzeroLocus
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0102
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Splits
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GtBaseChangeSt
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsInKNeOne
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RatioTranslate
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsNonvanishing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.AlgebraicCoboundaryOfHolomorphicCoboundary
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct ContDiff
open GlobalTheory.KS

namespace GlobalTheory.KS

theorem top_le_preimage_of_mem {X : Scheme.{0}} (x : Sp ℂ ⟶ X) (p : Sp ℂ) (U : X.Opens)
    (hp : x p ∈ U) : ⊤ ≤ x ⁻¹ᵁ U := by
  intro q _
  obtain rfl : q = p := Subsingleton.elim q p
  exact hp

theorem algebraic_coboundary_of_holomorphic_coboundary : Out.Laws → ∀ (P₀ : Out.PolAV (Sp ℂ)) (u : HolUnif P₀.A P₀.L P₀.g) (Hm : Matrix (Fin P₀.g) (Fin P₀.g) ℂ) (χ : u.Λ → ℂ), GoodU u Hm χ → ∀ (I : Type) (O : I → P₀.A.left.Opens) (c : ∀ i i', Γ(P₀.A.left, O i ⊓ O i')) (h : I → (Fin P₀.g → ℂ) → ℂ), ⨆ i, O i = ⊤ → (∀ i, DifferentiableOn ℂ (h i) {z | ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i} ∧ ∀ (l : u.Λ) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → h i (z + l) = h i z) → (∀ i i' z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (O i ⊓ O i') → valAt' (u.ex z).left (O i ⊓ O i') (c i i') = h i' z - h i z) → ∀ i, ∃ a : Γ(P₀.A.left, O i), ∀ z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ O i → valAt' (u.ex z).left (O i) a = h i z := by
  intro hL P₀ u Hm χ hU I O c h hcov hhol hcoc i

  refine (_root_.GlobalTheory.existsUnique_section_of_locally_regular P₀ u Hm χ hU (O i) (h i) ?_).exists
  intro z hz
  obtain ⟨p⟩ : Nonempty (Sp ℂ) := inferInstance
  have hy : (u.ex z).left p ∈ O i := hz (Set.mem_univ p)
  obtain ⟨n, σ, hyσ, hσ⟩ := _root_.GlobalTheory.exists_nonzeroLocus_le hL P₀ (O i) _ hy
  obtain ⟨a, ha⟩ := _root_.GlobalTheory.primitive_regular_on_nonzeroLocus P₀ u Hm χ hU I O c h hcov hhol hcoc i n σ hσ
  exact ⟨Out.nonzeroLocus σ, a, hσ, top_le_preimage_of_mem _ p _ hyσ, ha⟩

end GlobalTheory.KS
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStructureAndSymmetricOfCubeGenStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct Pointwise
theorem _root_.GlobalTheory.T.cubicalStructure_and_symmetric_of_cube_gen : ∀ (X : Scheme.{0}) (G : Over X) [GrpObj G] [IsCommMonObj G] (L : RigLB G), IsSemiAbelian G → (IsReduced X ∧ genericPoints X ⊆ abLocus G) → ((∃ t : (Theta G L.L).Gen, t.IsGen) → Nonempty (CubicalStr G L)) ∧ (LBIso L.L (L.L.pull (GrpObj.inv (X := G)).left) → L.IsSymmetric) := by
  first | exact @GlobalTheory.CubeGen.cubical_and_symmetric | exact GlobalTheory.CubeGen.cubical_and_symmetric | (intros; apply GlobalTheory.CubeGen.cubical_and_symmetric <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfBiadditiveSliceTrivialEighthPower
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.FormBundleKer


open GlobalTheory.CechPic in
theorem eq_one_of_slice_trivial : ∀ (W : Matrix (Fin 8) (Fin 8) ℤ) (S : Scheme.{0}) (G A : Over S) [GrpObj G] [IsCommMonObj G] [GrpObj A] [IsCommMonObj A] (pr : Fin 8 → (G ⟶ A)) (L : LB G.left) (P : LB (G2 A).left), (∀ u, IsMonHom (pr u)) → (∀ (T : Over S) (y : Fin 8 → (T ⟶ A)), ∃! x : T ⟶ G, ∀ u, x ≫ pr u = y u) → L.IsLB → P.IsLB → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → (∀ (T : Over S) (x x' y : T ⟶ A), (∃ t : (LB.LinComb P (K := Fin 3) ![(lift (x * x') y).left, (lift x y).left, (lift x' y).left] ![1, -1, -1]).Gen, t.IsGen) ∧ ∃ t : (LB.LinComb P (K := Fin 3) ![(lift y (x * x')).left, (lift y x).left, (lift y x').left] ![1, -1, -1]).Gen, t.IsGen) → LBIso L (LB.LinComb P (K := Fin 8 × Fin 8) (fun uv => (lift (pr uv.1) (pr uv.2)).left) (fun uv => W uv.1 uv.2)) → Out.KTriv G L → ∀ (T : Over S) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro W S G A _ _ _ _ pr L P hpr huniv hL hP hsym hbi hLP hK T x hx
  let p : ∀ {T' : Over S}, (T' ⟶ A) → (T' ⟶ A) → Pic T'.left := fun a b => pull (lift a b).left (cls P hP)
  have padd : ∀ {T' : Over S} (a a' b : T' ⟶ A), p (a * a') b = p a b + p a' b := fun {T'} a a' b => by
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 (hbi T' a a' b).1
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    simp only [p]
    abel
  have psym : ∀ {T' : Over S} (a b : T' ⟶ A), p a b = p b a := fun {T'} a b => by
    have e : cls P hP = pull (lift (snd A A) (fst A A)).left (cls P hP) :=
      (cls_eq_iff hP (pull_isLB hP _)).2 hsym
    have k : (lift b a).left ≫ (lift (snd A A) (fst A A)).left = (lift a b).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd]
    show pull (lift a b).left (cls P hP) = pull (lift b a).left (cls P hP)
    rw [← k, pull_comp, ← e]
  have pone : ∀ {T' : Over S} (b : T' ⟶ A), p 1 b = 0 := fun b => by
    have := padd 1 1 b
    rw [_root_.mul_one] at this
    exact left_eq_add.1 this
  have px : ∀ {T' : Over S} (τ : T' ⟶ T) (y : T' ⟶ A), p (τ ≫ x) y = 0 := fun τ y => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 hx
    rw [cls_pull hP] at e
    have k : (lift y τ).left ≫ (lift (snd A T ≫ x) (fst A T)).left = (lift (τ ≫ x) y).left := by
      rw [← Over.comp_left, comp_lift, lift_fst, lift_snd_assoc]
    show pull (lift (τ ≫ x) y).left (cls P hP) = 0
    rw [← k, pull_comp, e, map_zero]
  have hl : ∀ {T' : Over S} (z : T' ⟶ G), pull z.left (cls L hL) =
      ∑ uv : Fin 8 × Fin 8, W uv.1 uv.2 • p (z ≫ pr uv.1) (z ≫ pr uv.2) := fun z => by
    have e := (cls_eq_iff hL (LB.isLB_linComb hP _ _)).2 hLP
    rw [cls_linComb hP] at e
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e, map_sum]
    refine Finset.sum_congr rfl fun uv _ => ?_
    rw [map_zsmul, ← pull_comp, ← Over.comp_left, comp_lift]
  obtain ⟨x', hx', -⟩ := huniv T fun v => if v = 0 then x else 1
  have pz : ∀ u (y : T ⊗ G ⟶ A), p ((fst T G ≫ x') ≫ pr u) y = 0 := fun u y => by
    rw [Category.assoc, hx']
    split_ifs
    · exact px _ _
    · rw [MonObj.comp_one]; exact pone _
  have key : pull (Out.translPt G x').left (cls L hL) = pull (snd T G).left (cls L hL) := by
    have e : Out.translPt G x' = (fst T G ≫ x') * snd T G := rfl
    rw [hl, hl, e]
    refine Finset.sum_congr rfl fun uv _ => ?_
    have := hpr uv.1
    have := hpr uv.2
    rw [MonObj.mul_comp, MonObj.mul_comp, padd, pz, zero_add, psym, padd, pz, zero_add, psym]
  have H : KerPow.HasGen L (K := Fin 2) ![(Out.translPt G x').left, (snd T G).left] ![1, -1] := by
    refine (cls_eq_zero_iff (LB.isLB_linComb hL _ _)).1 ?_
    rw [cls_linComb hL, Fin.sum_univ_two]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, key, one_smul, neg_smul, add_neg_cancel]
  have h1 : x' = 1 := KerPow.eq_one_of_locGen hK x' fun _ => ⟨⊤, trivial, H.pull _ fun _ => rfl⟩
  have h0 := hx' 0
  have := hpr 0
  rw [h1, MonObj.one_comp, if_pos rfl] at h0
  exact h0.symm

end GlobalTheory.FormBundleKer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.EqOneOfTriv
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.UU
open scoped CategoryTheory.Obj

namespace GlobalTheory.GoodPol

theorem eq_one_of_pow_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (hn : IsUnit (n : O))
    {z : O} (hz : z ^ n = 1) (h : IsLocalRing.residue O z = 1) : z = 1 := by
  have e := mul_geom_sum z n
  rw [hz, sub_self] at e
  refine sub_eq_zero.1 ((mul_eq_zero.1 e).resolve_right fun h0 => ?_)
  have e' := congrArg (IsLocalRing.residue O) h0
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_pow, h, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, _root_.mul_one,
    map_zero] at e'
  exact (hn.map (IsLocalRing.residue O)).ne_zero ((map_natCast _ n).trans e')

theorem unit_eq_one {O : Type} [CommRing O] [IsDomain O] [IsLocalRing O] {n : ℕ} (hn : IsUnit (n : Γ(Sp O, ⊤)))
    {z : Γ(Sp O, ⊤)ˣ} (hz : z ^ n = 1)
    (h : Units.map (spMap (IsLocalRing.residue O)).appTop.hom.toMonoidHom z = 1) : z = 1 := by
  let e := (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
  have hn' : IsUnit (n : O) := by simpa using hn.map e
  have h₁ : e z.val = 1 := by
    refine eq_one_of_pow_eq_one hn' ?_ ?_
    · rw [← map_pow, ← Units.val_pow_eq_pow_val, hz, Units.val_one, map_one]
    · have h₂ := congrArg (fun q => q.hom z.val)
        (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (IsLocalRing.residue O)))
      have h₃ : (spMap (IsLocalRing.residue O)).appTop.hom z.val = 1 := congrArg Units.val h
      exact h₂.symm.trans ((congrArg (Scheme.ΓSpecIso _).hom.hom h₃).trans (map_one _))
  exact Units.ext (e.injective (h₁.trans (map_one e).symm))

theorem eq_one_of_triv (hL : Out.Laws) {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : RigLB A} (c : CubicalStr A L) (O K : Type) [CommRing O] [IsDomain O]
    [ValuationRing O] [Field K] [IsAlgClosed K] [Algebra O K] [IsFractionRing O K] (p : Sp O ⟶ S)
    {pk : Sp (IsLocalRing.ResidueField O) ⟶ S} (hpk : pk = spMap (IsLocalRing.residue O) ≫ p) {n : ℕ}
    (hn : IsUnit (n : Γ(S, ⊤)))
    (hgen : ∀ x : Over.mk (spMap (algebraMap O K) ≫ p) ⟶ A, Triv (Out.translDiff A L.L x) → x = 1)
    (x : Over.mk pk ⟶ A) (hx : x ^ n = 1) (ht : Triv (Out.translDiff A L.L x)) : x = 1 := by
  subst hpk
  have := hA.proper
  let ρK : Over.mk (spMap (algebraMap O K) ≫ p) ⟶ Over.mk p := Over.homMk (spMap (algebraMap O K)) rfl
  let ρk : Over.mk (spMap (IsLocalRing.residue O) ≫ p) ⟶ Over.mk p := Over.homMk (spMap (IsLocalRing.residue O)) rfl
  have inj : ∀ y y' : Over.mk p ⟶ A, ρK ≫ y = ρK ≫ y' → y = y' := fun y y' e =>
    over_points_ext_of_injective S A O K _ (IsFractionRing.injective O K) p y y' (congrArg (fun q => q.left) e)
  have hnO : IsUnit (n : Γ(Sp O, ⊤)) := by simpa using hn.map p.appTop.hom
  have hnK : (n : K) ≠ 0 := by
    have h₁ : IsUnit (n : O) := by
      simpa using hnO.map (Scheme.ΓSpecIso (CommRingCat.of O)).commRingCatIsoToRingEquiv
    simpa using (h₁.map (algebraMap O K)).ne_zero

  obtain ⟨X, hX, hXx⟩ : ∃ X : Over.mk p ⟶ A, X ^ n = 1 ∧ ρk ≫ X = x := by
    obtain ⟨-, -, het⟩ := GrpTangent.finiteEtale_mulN_torsion A (hG := hA) hn
    obtain ⟨z, hz, -⟩ := LatticeTorsion.existsUnique_torsion A n x hx
    obtain ⟨y, hy, hy'⟩ := (valuationRing_henselian_and_lift_of_isAlgClosed O K).2.2 _
      (pullback.snd (torsion A n).hom p) inferInstance
      (pullback.lift z.left (spMap (IsLocalRing.residue O)) (Over.w z)) (pullback.lift_snd _ _ _)
    let w : Over.mk p ⟶ torsion A n := Over.homMk (y ≫ pullback.fst _ _) (by
      show (y ≫ _) ≫ _ = p
      rw [Category.assoc, pullback.condition, ← Category.assoc, hy, Category.id_comp])
    have hw : ρk ≫ w = z := Over.OverMorphism.ext (by
      show spMap (IsLocalRing.residue O) ≫ y ≫ _ = _
      rw [← Category.assoc, hy', pullback.lift_fst])
    refine ⟨w ≫ torsion.ι A n, ?_, by rw [← Category.assoc, hw, hz]⟩
    rw [← MonObj.comp_pow, LatticeTorsion.torsionι_pow_eq_one, MonObj.comp_one]
  have hE : ValuativeCriterion.Existence A.hom := by
    have h : UniversallyClosed A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  obtain ⟨-, hfin, het, hsurj⟩ := abelianScheme_id_pow_finite_etale_surjective S A n hA hn
  have hXK : (ρK ≫ X) ^ n = 1 := by rw [← MonObj.comp_pow, hX, MonObj.comp_one]
  have key : ρK ≫ X = 1 := by
    refine hgen _ (CubNondeg.main hL S A hA L c K _ n hnK hfin inferInstance hsurj _ hXK fun y hy => ?_)
    obtain ⟨l, hl₁, hl₂⟩ := (hE { R := O, K := K, commSq := ⟨Over.w y⟩, .. }).exists_lift
    let Y : Over.mk p ⟶ A := Over.homMk l hl₂
    have hYy : ρK ≫ Y = y := Over.OverMorphism.ext hl₁
    have hY : Y ^ n = 1 := inj _ _ (by rw [MonObj.comp_pow, hYy, hy, MonObj.comp_one])
    obtain ⟨ex, -, pow, pull, -⟩ := cubWeil_basic S A L c n (Over.mk p)
    obtain ⟨ζ, hζ, -⟩ := ex X Y hX hY
    have hYk : (ρk ≫ Y) ^ n = 1 := by rw [← MonObj.comp_pow, hY, MonObj.comp_one]
    have h₁ := pull _ ρk X Y ζ hζ
    rw [hXx] at h₁
    have h₂ := KerPair.cubWeil_of_gen hL.globalFns S A hA L c n _ x (ρk ≫ Y) hx hYk ht
    have h₃ := ((cubWeil_basic S A L c n _).1 x (ρk ≫ Y) hx hYk).unique h₁ h₂
    have h₄ : ζ = 1 := unit_eq_one hnO (pow X Y ζ hζ).2 h₃
    have h₅ := pull _ ρK X Y ζ hζ
    rwa [h₄, map_one, hYy] at h₅
  rw [← hXx, inj X 1 (key.trans (MonObj.comp_one _).symm), MonObj.comp_one]

end GlobalTheory.GoodPol
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsBasisOnAny
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TopologicalSpace
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Out

namespace GlobalTheory.PushInv

open LBGerm

theorem exists_basisOn_any {S : Scheme.{0}} (hS : SecBaseChangeAnySt) (P : PolAV S) (x : S) :
    ∃ V : S.Opens, x ∈ V ∧ ∃ θ ∈ secOn P.L (P.A.hom ⁻¹ᵁ V), IsBasisOn P.A P.L V θ := by
  obtain ⟨V, hV, b, hb⟩ := hS S P 1 le_rfl x
  have hq : Unique (Fin (1 ^ P.g)) := by rw [one_pow]; infer_instance
  let T : Over S := overRes (T := baseOver S) V
  have hT : T.hom = V.ι := Category.comp_id _
  haveI : IsOpenImmersion T.hom := by rw [hT]; exact inferInstanceAs (IsOpenImmersion V.ι)
  haveI : IsOpenImmersion (snd T P.A).left := inferInstanceAs (IsOpenImmersion (pullback.snd T.hom P.A.hom))
  have hr : ∀ g : P.A.left, P.A.hom g ∈ V → g ∈ Set.range (snd T P.A).left := fun g hg => by
    rw [range_snd, hT]
    exact ⟨⟨_, hg⟩, rfl⟩
  choose θ hθ using fun i => exists_lift (snd T P.A).left (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) (fun g hg => hr g hg.1)
    ((LPow P.A P.L (1 : ℕ) T).U (fun _ => i)) (fun z hz => (mem_chart _ _ _ _ _ _).2 hz.2)
    ((b hq.default).f (fun _ => i))
  refine ⟨V, hV, θ, mem_secOn_of_germ θ fun g i j hg hi hj => ?_, fun R _ q hqV => ?_⟩
  · obtain ⟨z, rfl⟩ := hr g hg
    apply stalk_inj (snd T P.A).left z
    have hi' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => i)).2 hi
    have hj' := (mem_chart P.A P.L T (1 : ℕ) z (fun _ => j)).2 hj
    rw [map_mul, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U i) ⟨hg, hi⟩, ← gs_stalkMap _ z (P.A.hom ⁻¹ᵁ V ⊓ P.L.U j) ⟨hg, hj⟩,
      ← gm_comp _ (𝟙 _) z (P.L.U i ⊓ P.L.U j) ⟨hi, hj⟩, Category.comp_id]
    have e₁ := hθ i _ (𝟙 _) z ⟨hg, hi⟩
    have e₂ := hθ j _ (𝟙 _) z ⟨hg, hj⟩
    have e₃ := gm_lpow P.A P.L T (𝟙 _) z _ _ hi' hj'
    rw [Category.id_comp] at e₁ e₂ e₃
    rw [e₁, e₂, gs_compat (b hq.default) (𝟙 _) z hi' hj', e₃]
  · obtain ⟨t, rfl⟩ : ∃ t : Spec (CommRingCat.of R) ⟶ T.left, t ≫ T.hom = q :=
      ⟨IsOpenImmersion.lift T.hom q (by rw [hT]; exact hqV.trans (Scheme.Opens.range_ι V).ge), IsOpenImmersion.lift_fac _ _ _⟩
    choose b' hb' using fun i => exists_pull P.A P.L (1 : ℕ) (homAt t ▷ P.A) (whiskerRight_snd (homAt t) P.A) (b i)
    obtain ⟨hli, hsp⟩ := hb R t b' hb'
    have e : (homAt t ▷ P.A).left ≫ (snd T P.A).left = (snd (baseAt t) P.A).left :=
      congrArg CommaMorphism.left (whiskerRight_snd (homAt t) P.A)
    have val : ∀ (z : (baseAt t ⊗ P.A).left) i, (snd (baseAt t) P.A).left z ∈ P.L.U i →
        gs (𝟙 _) z _ ((b' hq.default).f (fun _ => i)) = gs (snd (baseAt t) P.A).left z _ (θ i) := fun z i hi => by
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have hV' : P.A.hom ((snd (baseAt t) P.A).left z) ∈ V := by
        rw [← Scheme.Hom.comp_apply, w_snd, Scheme.Hom.comp_apply]
        exact hqV ⟨_, rfl⟩
      have hm : (snd T P.A).left ((homAt t ▷ P.A).left z) ∈ P.A.hom ⁻¹ᵁ V ⊓ P.L.U i := by
        rw [← Scheme.Hom.comp_apply, e]; exact ⟨hV', hi⟩
      have e₁ := hθ i _ (homAt t ▷ P.A).left z hm
      rw [e] at e₁
      rw [e₁, hb' hq.default (fun _ => i)]
      exact (gs_appLE (homAt t ▷ P.A).left _ _ _ (𝟙 _) z hi' _).trans (by rw [Category.id_comp])
    refine ⟨fun s => ?_, fun r h0 => ?_⟩
    · rw [Set.range_unique] at hsp
      obtain ⟨r, hr⟩ := Submodule.mem_span_singleton.1 (hsp.ge (Submodule.mem_top (x := SecM.ofSec P.A s)))
      refine ⟨r, fun z i hi => ?_⟩
      have hi' := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).2 hi
      have := gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hi'
      rw [hr] at this
      exact this.trans (congrArg _ (val z i hi))
    · refine Fintype.linearIndependent_iff.1 hli (fun _ => r) ?_ hq.default
      rw [Fintype.sum_unique]
      refine Subtype.ext (funext fun j => fn_ext fun z hz => ?_)
      obtain ⟨i, rfl⟩ : ∃ i, j = fun _ => i := ⟨j 0, funext fun k => by rw [Subsingleton.elim k 0]⟩
      have hi := (mem_chart P.A P.L (baseAt t) (1 : ℕ) z (fun _ => i)).1 hz
      refine (gs_smul P.A P.L (baseAt t) _ r (SecM.ofSec P.A (b' hq.default)) (fun _ => i) z hz).trans ?_
      exact ((congrArg _ (val z i hi)).trans (h0 z i hi)).trans (gs_zero _ z _ hz).symm

theorem pushInvertible_any : Out.SecBaseChangeAnySt → Out.GlobalSectionsRankAlgClosed →
    ∀ (S : Scheme.{0}) (Q : Out.PolAV S), PushInvertible Q.A Q.L := by
  intro hS _ S P x
  obtain ⟨V, hV, θ, hθ, H⟩ := exists_basisOn_any hS P x
  haveI := P.smoothDim
  haveI : Smooth P.A.hom := SmoothOfRelativeDimension.smooth P.g _
  refine ⟨V, hV, θ, hθ, fun W hW s hs => ?_, exists_nonvanishing H⟩
  have e : ∀ (a : Γ(S, W)) (g : P.A.left) i, P.A.hom g ∈ W → g ∈ P.L.U i →
      gs (𝟙 _) g _ ((P.A.hom.appLE W (P.A.hom ⁻¹ᵁ W ⊓ P.L.U i) inf_le_left).hom a *
        resG P.A.left (inf_le_inf_right _ (P.A.hom.preimage_mono hW)) (θ i)) =
      gs P.A.hom g W a * gs (𝟙 _) g _ (θ i) := fun a g i hg hi => by
    have hm : g ∈ P.A.hom ⁻¹ᵁ W ⊓ P.L.U i := ⟨hg, hi⟩
    rw [gs_mul (𝟙 _) g _ hm, gs_res (𝟙 _) g _ hm, gs_appLE _ _ _ _ (𝟙 _) g hm, Category.id_comp]
  obtain ⟨a, ha⟩ := exists_coeff H hW hs
  refine ⟨a, fun i => fn_ext fun g hg => (ha g i hg.1 hg.2).trans (e a g i hg.1 hg.2).symm, fun a' ha' => ?_⟩
  exact eq_of_mul H hW _ _ fun g i hg hi =>
    ((e a' g i hg hi).symm.trans (congrArg _ (ha' i).symm)).trans (ha g i hg hi)

end GlobalTheory.PushInv
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsHeckeQuotientTriple
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G G' T T' : Over S} [GrpObj G] [GrpObj G']

def lam (c : Pic G.left) (x y : T ⟶ G) : Pic T.left :=
  pull (x * y).left c - pull x.left c - pull y.left c + pull (1 : T ⟶ G).left c

theorem cls_cube_two {L : LB G.left} (hL : L.IsLB) (x y : T ⟶ G) (h : (cubeLB G ![x, y] L).IsLB) :
    cls _ h = lam (cls L hL) x y := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 2))) = {∅, {0}, {1}, {0, 1}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 2) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * 1).left (cls L hL) + ((-1 : ℤ) ^ 0) • pull (x * (y * 1)).left (cls L hL))) =
      lam (cls L hL) x y := by
    simp only [_root_.mul_one, lam]
    norm_num
    abel
  exact e

theorem cls_cube_three [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (x y z : T ⟶ G)
    (h : (cubeLB G ![x, y, z] L).IsLB) :
    cls _ h = lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
  refine (cls_linComb hL _ _ h).trans ?_
  rw [← Equiv.sum_comp Equiv.ulift.symm,
    show (Finset.univ : Finset (Finset (Fin 3))) = {∅, {0}, {1}, {2}, {0, 1}, {0, 2}, {1, 2}, {0, 1, 2}} by decide,
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]
  have e : ((-1 : ℤ) ^ 3) • pull (1 : T ⟶ G).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (x * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 2) • pull (y * 1).left (cls L hL) + (((-1 : ℤ) ^ 2) • pull (z * 1).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (x * (y * 1)).left (cls L hL) + (((-1 : ℤ) ^ 1) • pull (x * (z * 1)).left (cls L hL) +
      (((-1 : ℤ) ^ 1) • pull (y * (z * 1)).left (cls L hL) +
        ((-1 : ℤ) ^ 0) • pull (x * (y * (z * 1))).left (cls L hL))))))) =
      lam (cls L hL) (x * y) z - lam (cls L hL) x z - lam (cls L hL) y z := by
    simp only [_root_.mul_one, lam, _root_.mul_assoc]
    norm_num
    abel
  exact e

theorem pull_lam (h : T' ⟶ T) (c : Pic G.left) (x y : T ⟶ G) :
    pull h.left (lam c x y) = lam c (h ≫ x) (h ≫ y) := by
  simp only [lam, map_add (f := _), map_sub, ← pull_comp, ← Over.comp_left, MonObj.comp_mul, MonObj.comp_one]

theorem lam_pull (ψ : G ⟶ G') [IsMonHom ψ] (c : Pic G'.left) (x y : T ⟶ G) :
    lam (pull ψ.left c) x y = lam c (x ≫ ψ) (y ≫ ψ) := by
  simp only [lam, ← pull_comp, ← Over.comp_left, MonObj.mul_comp, MonObj.one_comp]

theorem lam_nsmul (n : ℕ) (c : Pic G.left) (x y : T ⟶ G) : lam (n • c) x y = n • lam c x y := by
  simp only [lam, map_nsmul, nsmul_add, nsmul_sub]

theorem lam_one_left (c : Pic G.left) (y : T ⟶ G) : lam c 1 y = 0 := by
  simp only [lam, _root_.one_mul]; abel

theorem lam_one_right (c : Pic G.left) (x : T ⟶ G) : lam c x 1 = 0 := by
  simp only [lam, _root_.mul_one]; abel

variable [IsCommMonObj G]

theorem lam_comm (c : Pic G.left) (x y : T ⟶ G) : lam c x y = lam c y x := by
  simp only [lam, _root_.mul_comm x y]; abel

theorem lam_mul_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x y z : T ⟶ G) :
    lam (cls L hL) (x * y) z = lam (cls L hL) x z + lam (cls L hL) y z := by
  have h₀ := (cls_eq_zero_iff (N := Theta G L) (LB.isLB_linComb hL _ _)).2 hΘ
  have h₁ := (cls_cube_three hL (fst _ _) (snd _ _ ≫ fst _ _) (snd G (G ⊗ G) ≫ snd _ _)
    (LB.isLB_linComb hL _ _)).symm.trans h₀
  have h₂ := congrArg (pull (lift x (lift y z)).left) h₁
  simp only [map_sub, map_zero, pull_lam, MonObj.comp_mul, lift_fst, lift_snd_assoc, lift_snd] at h₂
  rw [sub_sub, sub_eq_zero] at h₂
  exact h₂

theorem lam_pow_left {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) (x ^ n) z = n • lam (cls L hL) x z := by
  induction n with
  | zero => rw [pow_zero, lam_one_left, zero_nsmul]
  | succ n ih => rw [pow_succ, lam_mul_left hL hΘ, ih, succ_nsmul]

theorem lam_pow_right {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen) (x z : T ⟶ G) (n : ℕ) :
    lam (cls L hL) x (z ^ n) = n • lam (cls L hL) x z := by
  rw [lam_comm, lam_pow_left hL hΘ, lam_comm]

theorem sym_of_isSymmetric (L : RigLB G) (h : L.IsSymmetric) : Out.Sym G L.L := by
  obtain ⟨_, w, hw, -⟩ := h
  have e := (cls_eq_iff L.isLB (pull_isLB L.isLB _)).2 ⟨w, hw⟩
  rw [cls_pull L.isLB] at e
  refine fun s => ⟨⊤, trivial, (cls_eq_zero_iff (LB.isLB_linComb L.isLB _ _)).1 ?_⟩
  rw [cls_linComb L.isLB, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pull_comp, ← e, one_smul, neg_smul, add_neg_cancel]

end Pairing

theorem dense_image_points {k : Type} [Field k] [IsAlgClosed k] {A B : Over (Sp k)} [LocallyOfFiniteType A.hom]
    (f : A ⟶ B) [Surjective f.left] (P : Set (𝟙_ (Over (Sp k)) ⟶ B)) (hP : ∀ u : 𝟙_ (Over (Sp k)) ⟶ A, u ≫ f ∈ P) :
    Dense (⋃ x ∈ P, Set.range x.left) := by
  have : JacobsonSpace A.left := LocallyOfFiniteType.jacobsonSpace A.hom
  have hd : Dense (closedPoints A.left) := dense_iff_closure_eq.2 closure_closedPoints
  refine (f.left.surjective.denseRange.dense_image f.left.continuous hd).mono ?_
  rintro _ ⟨a, ha, rfl⟩
  let u : 𝟙_ (Over (Sp k)) ⟶ A := Over.homMk (pointOfClosedPoint A.hom a ha) (pointOfClosedPoint_comp A.hom a ha)
  refine Set.mem_iUnion₂.2 ⟨u ≫ f, hP u, ⟨(default : PrimeSpectrum k), ?_⟩⟩
  exact congrArg f.left (pointOfClosedPoint_apply A.hom a ha _)

end GlobalTheory.CechPic

namespace GlobalTheory

open CechPic

end GlobalTheory
end
end

