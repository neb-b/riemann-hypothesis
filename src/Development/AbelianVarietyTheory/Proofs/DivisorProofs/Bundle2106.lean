module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2024
public import Development.AbelianVarietyTheory.PublishedTheorems.RelativeAmpleness.RelAmpleAndKTrivIff
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0156
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0167
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0109
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteAlgebraSplittingNormForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0194
public import Formalism.LocalToGlobal.GroupLattices.PerfectRings.IsLocalRingOfComplete
public import Development.AbelianVarietyTheory.Definitions.Divisors.ThetaSetupStructureMapComp
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ColumnCompatibleSelection
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0052
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0151

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NondegeneratePairingOfGenericFibre
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.NondegSpread
open GlobalTheory.CechPic

theorem pairing_add_and_symm : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A →
    ∀ (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    LBIso P (P.pull (lift (snd A A) (fst A A)).left) →
    Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) →
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) ∧
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) := by
  intro S A _ _ hA P hP r₁ r₂ hs ha
  have hG : Out.GlobalFnsSt := GlobalTheory.globalFns_holds
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  refine ⟨fun T x x' y => ?_, fun T x y => ?_⟩
  · obtain ⟨t, ht⟩ := (GlobalTheory.Biadditive.biadditive_of_triv_axes hG S A _ hA hD ha P hP r₁ r₂ T x x' y).1
    have e := (cls_eq_zero_iff (LB.isLB_linComb hP _ _)).2 ⟨t, ht⟩
    rw [cls_linComb hP, Fin.sum_univ_three] at e
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
      Matrix.tail_cons, one_smul, neg_smul] at e
    rw [← sub_eq_zero, ← e]
    abel
  · have e := (cls_eq_iff hP (pull_isLB hP _)).2 hs
    rw [cls_pull hP] at e
    conv_lhs => rw [e]
    rw [← pull_comp, ← Over.comp_left, comp_lift, lift_fst, lift_snd]

theorem over_hom_ext_of_local : ∀ (S : Scheme.{0}) (T X : Over S) (a b : T ⟶ X),
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧ Out.overResι V ≫ a = Out.overResι V ≫ b) → a = b := by
  intro S T X a b h
  choose V hV e using h
  apply Over.OverMorphism.ext
  exact Scheme.hom_ext_of_forall _ _ fun p => ⟨V p, hV p, congrArg (fun q => q.left) (e p)⟩

theorem hom_ext_of_generic_points : ∀ (O K : Type) [CommRing O] [IsDomain O] [Field K] [Algebra O K] [IsFractionRing O K] (H X : Over (Sp O))
    [IsSeparated X.hom] (a b : H ⟶ X), IsFinite H.hom → Flat H.hom →
    (∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ z : T ⟶ H, z ≫ a = z ≫ b) → a = b := by
  intro O K _ _ _ _ _ H X _ a b hfin hflat h
  have := GlobalTheory.schemeTheoreticallyDominant_fractionField O K
  have : IsSchemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) :=
    .of_isPullback (IsPullback.of_hasPullback H.hom (spMap (algebraMap O K))).flip
  let T : Over (Sp O) := Over.mk (pullback.fst H.hom (spMap (algebraMap O K)) ≫ H.hom)
  let z : T ⟶ H := Over.homMk (pullback.fst _ _) rfl
  refine GlobalTheory.over_ext_of_schemeTheoreticallyDominant (pullback.fst H.hom (spMap (algebraMap O K))) ?_
  exact congrArg (fun q => q.left) (h T (pullback.snd _ _) pullback.condition z)

theorem cls_translDiff : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A) (h : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB),
    CechPic.cls _ h = CechPic.pull (fst T A).left (CechPic.pull (lift x x).left (CechPic.cls P hP)) + CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) := by
  intro S A _ P hP hB hS T x h
  have hD : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  have dg : ∀ g : T ⊗ A ⟶ A, CechPic.pull g.left (CechPic.cls _ hD) =
      CechPic.pull (lift g g).left (CechPic.cls P hP) := fun g => by
    rw [cls_pull hP, ← pull_comp, ← Over.comp_left, comp_lift, Category.comp_id]
  have hm : lift (fst T A ≫ x) (snd T A) ≫ μ[A] = (fst T A ≫ x) * snd T A := rfl
  refine (cls_linComb hD (![(lift (fst T A ≫ x) (snd T A) ≫ μ[A]).left, (snd T A).left] : Fin 2 → _) ![1, -1] h).trans ?_
  rw [Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, one_smul, neg_smul]
  rw [hm, dg, dg, hB, hS _ (fst T A ≫ x) (_ * _), hS _ (snd T A) (_ * _), hB, hB, ← pull_comp,
    ← Over.comp_left, comp_lift, MonObj.comp_pow, pow_two, hB, hS _ (snd T A) (fst T A ≫ x)]
  abel

theorem memKL_of_pairing_sq : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    ∀ (T : Over S) (x : T ⟶ A), CechPic.pull (lift (fst T A ≫ x ^ 2) (snd T A)).left (CechPic.cls P hP) = 0 →
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x := by
  intro S A _ P hP hB hS T x h0 p
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have e := cls_translDiff S A P hP hB hS T x hM
  rw [h0, add_zero] at e
  obtain ⟨N, hN, hc⟩ := cls_surj (CechPic.pull (lift x x).left (CechPic.cls P hP))
  have e' : cls (N.pull (fst T A).left) (pull_isLB hN _) = cls _ hM := by rw [cls_pull hN, hc, e]
  obtain ⟨u, hu⟩ := (cls_eq_iff _ _).1 e'
  exact GlobalTheory.CubeLawCompare.locally_trivial_of_iso_pull (fst T A).left _ hN u hu p

theorem exists_local_triv_sq_of_memKL : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] (P : LB (A ⊗ A).left) (hP : P.IsLB),
    (∀ (T : Over S) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over S) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) →
    ∀ (T : Over S) (x : T ⟶ A), MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → ∀ p : T.left,
    ∃ V : T.left.Opens, p ∈ V ∧ ∃ t : (P.pull (lift (snd A (Out.overRes V) ≫ Out.overResι V ≫ x ^ 2) (fst A (Out.overRes V))).left).Gen, t.IsGen := by
  intro S A _ P hP hB hS r₂ T x hx p
  obtain ⟨V, hV, c, hc⟩ := hx p
  refine ⟨V, hV, ?_⟩
  have hD := pull_isLB hP (lift (𝟙 A) (𝟙 A)).left
  have hM : (Out.translDiff A (P.pull (lift (𝟙 A) (𝟙 A)).left) x).IsLB := LB.isLB_linComb hD _ _
  have nat : ∀ {Y Z : Over S} (g : Y ⟶ Z) (a b : Z ⟶ A), CechPic.pull g.left (CechPic.pull (lift a b).left (CechPic.cls P hP)) = CechPic.pull (lift (g ≫ a) (g ≫ b)).left (CechPic.cls P hP) :=
    fun g a b => by rw [← pull_comp, ← Over.comp_left, comp_lift]
  have ax : ∀ {Y : Over S} (a : Y ⟶ A), CechPic.pull (lift a (1 : Y ⟶ A)).left (CechPic.cls P hP) = 0 := fun a => by
    have e := (cls_eq_zero_iff (pull_isLB hP _)).2 r₂
    rw [cls_pull hP] at e
    have e' := congrArg (CechPic.pull a.left) e
    rwa [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, MonObj.comp_one, Category.comp_id] at e'
  let Vo := Out.overRes V
  let u : Vo ⟶ T := Out.overResι V
  let W := (fst T A).left ⁻¹ᵁ V
  let U : Vo ⊗ A ⟶ T ⊗ A := lift (fst Vo A ≫ u) (snd Vo A)
  have k₁ : U ≫ fst T A = fst Vo A ≫ u := lift_fst _ _
  have k₂ : U ≫ snd T A = snd Vo A := lift_snd _ _
  obtain ⟨n, hn⟩ : ∃ n : (Vo ⊗ A).left ⟶ W.toScheme, n ≫ W.ι = U.left :=
    ⟨IsOpenImmersion.lift _ U.left (by
      rintro _ ⟨y, rfl⟩
      rw [Scheme.Opens.range_ι]
      show (U ≫ fst T A).left y ∈ V
      rw [k₁]
      show V.ι ((fst Vo A).left y) ∈ V
      have hy := Set.mem_range_self (f := V.ι) ((fst Vo A).left y)
      rwa [Scheme.Opens.range_ι] at hy), IsOpenImmersion.lift_fac _ _ _⟩
  have e0 := (cls_eq_zero_iff (pull_isLB hM _)).2 ⟨c, hc⟩
  rw [cls_pull hM, cls_translDiff S A P hP hB hS T x hM] at e0
  have e1 := congrArg (CechPic.pull n) e0
  rw [map_zero, ← pull_comp, hn, map_add (f := _), ← pull_comp, ← Over.comp_left, nat, nat] at e1
  simp only [← Category.assoc, k₁, k₂] at e1
  simp only [Category.assoc] at e1
  have e2 := congrArg (CechPic.pull (lift (𝟙 Vo) (1 : Vo ⟶ A)).left) e1
  rw [map_zero, map_add (f := _), nat, nat, lift_fst_assoc, lift_snd, Category.id_comp, ax, add_zero] at e2
  have e3 : CechPic.pull (fst Vo A).left (CechPic.pull (lift (u ≫ x) (u ≫ x)).left (CechPic.cls P hP)) = 0 := by rw [e2, map_zero]
  rw [nat] at e3
  rw [e3, zero_add] at e1
  have e4 := congrArg (CechPic.pull (lift (snd A Vo) (fst A Vo)).left) e1
  rw [map_zero, nat, lift_fst_assoc, lift_snd] at e4
  refine (cls_eq_zero_iff (pull_isLB hP _)).1 ?_
  rw [cls_pull hP]
  exact e4

theorem eq_one_of_generic_nondeg : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left),
    P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H gen T t ht x hx
  obtain ⟨T, ⟨⟨⟩⟩, hT⟩ := T
  change T ⟶ Sp K at t
  change T ⟶ Sp O at hT
  change hT = t ≫ _ at ht
  subst ht
  let T' : Over (Sp K) := Over.mk t
  obtain ⟨x', rfl⟩ := GlobalTheory.SiegelPull.push_surjective h T' x
  rw [← map_one (pushHom h T')]
  congr 1
  apply gen T' x'
  obtain ⟨u, hu⟩ := H
  obtain ⟨c, hc⟩ := hx
  let f := spMap (algebraMap O K)
  let B : Over (Sp O) := Over.mk ((A' ⊗ T').hom ≫ f)
  let a : B ⟶ A := Over.homMk ((fst A' T').left ≫ φ) (by
    show (fst A' T').left ≫ φ ≫ A.hom = (A' ⊗ T').hom ≫ f
    rw [h.1.w, ← Category.assoc, Over.w (fst A' T')])
  let b : B ⟶ Over.mk (t ≫ f) := Over.homMk (snd A' T').left (by
    show (snd A' T').left ≫ t ≫ f = (A' ⊗ T').hom ≫ f
    rw [← Category.assoc]
    exact congrArg (· ≫ f) (Over.w (snd A' T')))
  let χ : (A' ⊗ T').left ⟶ (A ⊗ Over.mk (t ≫ f)).left := (lift a b).left
  have c₁ : χ ≫ (fst A (Over.mk (t ≫ f))).left = (fst A' T').left ≫ φ :=
    congrArg (fun q => q.left) (lift_fst a b)
  have c₂ : χ ≫ (snd A (Over.mk (t ≫ f))).left = (snd A' T').left :=
    congrArg (fun q => q.left) (lift_snd a b)
  have sqr : (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂ =
      χ ≫ (lift (snd A (Over.mk (t ≫ f)) ≫ pushHom h T' x') (fst A (Over.mk (t ≫ f)))).left :=
    (Category.id_comp _).symm.trans (GlobalTheory.SiegelPull.lift_sq sq (T := B) (𝟙 _) _ _ χ _ _
      (by rw [Category.id_comp, Over.comp_left, Over.comp_left, ← Category.assoc χ, c₂, Category.assoc]; rfl)
      (by rw [Category.id_comp, c₁]))
  obtain ⟨c₂', h₂⟩ := gen_chartPull (chartPullSame P (fun _ : PUnit => (lift (snd A' T' ≫ x') (fst A' T')).left ≫ φ₂)
    _ _ χ fun _ => sqr) c hc
  exact exists_down ((isGen_iff u).1 hu) hP hP' c₂' h₂

theorem sq_eq_one_of_memKL_generic : ∀ (O K : Type) [CommRing O] [Field K] [Algebra O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A']
    (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left),
    IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left)
    (hP : P.IsLB), P'.IsLB → LBIso P' (P.pull φ₂) →
    (∀ (T : Over (Sp O)) (x x' y : T ⟶ A), CechPic.pull (lift (x * x') y).left (CechPic.cls P hP) = CechPic.pull (lift x y).left (CechPic.cls P hP) + CechPic.pull (lift x' y).left (CechPic.cls P hP)) →
    (∀ (T : Over (Sp O)) (x y : T ⟶ A), CechPic.pull (lift x y).left (CechPic.cls P hP) = CechPic.pull (lift y x).left (CechPic.cls P hP)) →
    (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) →
    ∀ (T : Over (Sp O)) (t : T.left ⟶ Sp K), T.hom = t ≫ spMap (algebraMap O K) → ∀ x : T ⟶ A,
    MemKL A (P.pull (lift (𝟙 A) (𝟙 A)).left) x → x ^ 2 = 1 := by
  intro O K _ _ _ A _ A' _ φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht x hx
  refine over_hom_ext_of_local _ T A (x ^ 2) 1 fun p => ?_
  obtain ⟨V, hV, hg⟩ := exists_local_triv_sq_of_memKL _ A P hP hB hS r₂ T x hx p
  refine ⟨V, hV, ?_⟩
  rw [MonObj.comp_one]
  exact eq_one_of_generic_nondeg O K A A' φ φ₂ h sq P P' hP hP' H gen (Out.overRes V) (V.ι ≫ t)
    (by simp only [Out.overRes, Over.mk_hom, ht, Category.assoc]) _ hg

theorem nondeg_of_generic : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsNoetherianRing O] [Field K] [Algebra O K] [IsFractionRing O K] (A : Over (Sp O)) [GrpObj A] (A' : Over (Sp K)) [GrpObj A'] (φ : A'.left ⟶ A.left) (φ₂ : (A' ⊗ A').left ⟶ (A ⊗ A).left), IsAbelianScheme A → IsGrpPullback A' A (spMap (algebraMap O K)) φ → IsSquare φ φ₂ → ∀ (P : LB (A ⊗ A).left) (P' : LB (A' ⊗ A').left), P.IsLB → P'.IsLB → LBIso P' (P.pull φ₂) → (∃ t : (P.pull (lift (1 : A ⟶ A) (𝟙 A)).left).Gen, t.IsGen) → (∃ t : (P.pull (lift (𝟙 A) (1 : A ⟶ A)).left).Gen, t.IsGen) → LBIso P (P.pull (lift (snd A A) (fst A A)).left) → Out.RelAmple A (P.pull (lift (𝟙 A) (𝟙 A)).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A'), (∃ t : (P'.pull (lift (snd A' T ≫ x) (fst A' T)).left).Gen, t.IsGen) → x = 1) → ∀ (T : Over (Sp O)) (x : T ⟶ A), (∃ t : (P.pull (lift (snd A T ≫ x) (fst A T)).left).Gen, t.IsGen) → x = 1 := by
  intro O K _ _ _ _ _ _ A _ A' _ φ φ₂ hA h sq P P' hP hP' H r₁ r₂ hs ha gen T y hy
  haveI := hA.comm
  haveI := hA.proper
  have hL : (P.pull (lift (𝟙 A) (𝟙 A)).left).IsLB := pull_isLB hP _
  obtain ⟨hB, hS⟩ := pairing_add_and_symm _ A hA P hP r₁ r₂ hs ha
  obtain ⟨H₀, _, i, -, -, hfin, hflat, hZ⟩ := GlobalTheory.kernel_finiteFlat_subgroup O A hA _ hL ha
  have hi : i ^ 2 = 1 := by
    refine hom_ext_of_generic_points O K H₀ A (i ^ 2) 1 hfin hflat fun T t ht z => ?_
    rw [MonObj.comp_pow, MonObj.comp_one]
    exact sq_eq_one_of_memKL_generic O K A A' φ φ₂ h sq P P' hP hP' H hB hS r₂ gen T t ht (z ≫ i) ((hZ T _).2 ⟨z, rfl⟩)
  obtain ⟨-, hfl, hsu⟩ := GlobalTheory.MulAmple.finite_flat_surjective_pow GlobalTheory.abelianSchemeLaws_all.1 O A hA _ hL ha 2
    (by norm_num)
  obtain ⟨T', e, x, he, he', hx⟩ := GlobalTheory.DivisibleHom.exists_lift_point ((𝟙 A) ^ 2) y
  have hx2 : x ^ 2 = e ≫ y := by rw [← hx, MonObj.comp_pow, Category.comp_id]
  have hmem : MemKL A _ x := memKL_of_pairing_sq _ A P hP hB hS T' x (by
    obtain ⟨t, ht⟩ := hy
    have e0 := (cls_eq_zero_iff (pull_isLB hP _)).2 ⟨t, ht⟩
    rw [cls_pull hP] at e0
    have e1 := congrArg (CechPic.pull (lift (snd T' A) (fst T' A ≫ e)).left) e0
    rw [map_zero, ← pull_comp, ← Over.comp_left, comp_lift, lift_snd_assoc, lift_fst] at e1
    rw [hx2]
    exact e1)
  obtain ⟨w, hw⟩ := (hZ T' x).1 hmem
  apply GlobalTheory.DivisibleHom.cancel_of_flat_surjective e
  rw [← hx2, ← hw, ← MonObj.comp_pow, hi, MonObj.comp_one, MonObj.comp_one]

end GlobalTheory.NondegSpread
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptySquareZeroSmoothLiftSystemOfIsFun
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential MonoidalCategory CartesianMonoidalCategory MonObj
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.LiftSys GlobalTheory.Obs
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.Obs

theorem rho_id_eq {R R₀ : Type} [CommRing R] [CommRing R₀] {I : Ideal R} (hI : I ^ 2 = 0) {π : R →+* R₀}
    {C : Type} [Category.{0} C] {F : C ⥤ CommAlgCat.{0} R₀} (L : Pre I π F) (hL : L.IsFun) (T : C) (y : L.B T) :
    L.ρ (𝟙 T) y = y := by
  set e := L.ρ (𝟙 T) with he
  have idem : ∀ x, e (e x) = e x := fun x ↦ by
    have := hL (𝟙 T) (𝟙 T) x
    rw [Category.comp_id] at this
    exact this.symm
  have hJ := LiftSys.map_sq hI (L.B T)
  have memJ : ∀ x, x - e x ∈ I.map (algebraMap R (L.B T)) := fun x ↦ by
    rw [← L.ker]
    rw [map_sub, L.nat, mp_id, sub_self]
  have sq0 : ∀ u v, u ∈ I.map (algebraMap R (L.B T)) → v ∈ I.map (algebraMap R (L.B T)) → u * v = 0 := by
    intro u v hu hv
    have : u * v ∈ I.map (algebraMap R (L.B T)) ^ 2 := by
      rw [pow_two]; exact Ideal.mul_mem_mul hu hv
    rw [hJ] at this
    simpa using this
  have fix : ∀ z ∈ I.map (algebraMap R (L.B T)), e z = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨i, -, rfl⟩ := hx
      exact e.commutes i
    | zero => exact map_zero e
    | add x w _ _ hx hw => rw [map_add (f := _), hx, hw]
    | smul b x hxm hx =>
      rw [smul_eq_mul, map_mul, hx]
      have := sq0 _ _ (memJ b) hxm
      rw [sub_mul] at this
      exact (sub_eq_zero.1 this).symm
  have h1 := fix _ (memJ y)
  rw [map_sub, idem, sub_self] at h1
  exact (sub_eq_zero.1 h1.symm).symm

theorem nonempty_sys_of_isFun : ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (I : Ideal R) (hI : I ^ 2 = 0) (π : R →+* R₀) (hπ : Function.Surjective π) (hk : RingHom.ker π = I) (X₀ : Scheme.{0}) (s₀ : X₀ ⟶ Sp R₀) (L : Pre I π (OAff s₀)), L.IsFun → Nonempty (Sys I π s₀) := by
  intro R R₀ _ _ I hI π _ _ X₀ s₀ L hL
  exact ⟨{
    F := {
      obj := L.B
      map := fun a ↦ CommAlgCat.ofHom (L.ρ a)
      map_id := fun T ↦ CommAlgCat.hom_ext (AlgHom.ext fun y ↦ rho_id_eq hI L hL T y)
      map_comp := fun a b ↦ CommAlgCat.hom_ext (AlgHom.ext fun x ↦ hL a b x) }
    p := L.p
    semi := L.semi
    nat := fun a b ↦ L.nat a b
    surj := L.surj
    ker := L.ker
    smooth := L.smooth }⟩

end GlobalTheory.Obs
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCoefficientIdealMapCompleteDvrEqProdLifts
section
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LocM


open MvPolynomial in
theorem GlobalTheory.NormSheaf.normIdeal_map_eq_prod_lifts : ∀ (A B K L : Type) [CommRing A] [IsDomain A] [IsIntegrallyClosed A] [CommRing B] [IsDomain B]
    [Field K] [Field L] [CharZero K] [Algebra A K] [Algebra B L] [Algebra K L] [FiniteDimensional K L]
    [IsFractionRing A K] [IsFractionRing B L] (φ : A →+* B), φ.Finite →
    (algebraMap K L).comp (algebraMap A K) = (algebraMap B L).comp φ → ∀ (J : Ideal B)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [CharZero V],
    IsAdicComplete (maximalIdeal V) V → ∀ h : A →+* V,
    ∃ (V' : Type) (_ : CommRing V') (_ : IsDomain V') (_ : IsDiscreteValuationRing V') (_ : CharZero V')
      (f : V →+* V') (ψ : Fin (Module.finrank K L) → (B →+* V')), IsAdicComplete (maximalIdeal V') V' ∧
      Function.Injective f ∧ IsLocalHom f ∧ (∀ j, (ψ j).comp φ = f.comp h) ∧
      (GlobalTheory.NormSheaf.normIdeal A K L B J).map (f.comp h) = ∏ j, J.map (ψ j) := by
  intro A B K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ φ hφ hcomp J V _ _ _ _ hV h
  obtain ⟨R, _, _, hinj, hfin, σ, hσ, hP⟩ := _root_.GlobalTheory.NormSheaf.exists_finite_split_normForm A B K L φ hφ hcomp
  obtain ⟨V', _, _, _, _, f, ρ, hV', hf, hloc, hρ⟩ := _root_.GlobalTheory.exists_lift_to_complete_dvr_of_finite A R hinj hfin V hV h
  let ψ : Fin (Module.finrank K L) → (B →+* V') := fun j => ρ.comp (σ j)
  refine ⟨V', inferInstance, inferInstance, inferInstance, inferInstance, f, ψ, hV', hf, hloc, ?_, ?_⟩
  · intro j
    show (ρ.comp (σ j)).comp φ = f.comp h
    rw [RingHom.comp_assoc, hσ j, hρ]
  have key : ∀ (m : ℕ) (g : Fin m → B) (P : MvPolynomial (Fin m) A),
      P.map (algebraMap A R) = ∏ j, ∑ i, C (σ j (g i)) * X i →
      Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) =
        ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by
    intro m g P hPR
    rw [← _root_.GlobalTheory.GaussContentLinearForms.span_coeff_prod_linear V' _ m (fun j i => ψ j (g i))]
    have hE : (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V') = (P.map (algebraMap A R)).map ρ := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [hPR]; simp [map_prod, map_sum, ψ]
    have hfun : (fun s => (f.comp h) (P.coeff s)) =
        fun s => (∏ j, ∑ i, C (ψ j (g i)) * X i : MvPolynomial (Fin m) V').coeff s := by
      funext s
      rw [hE, MvPolynomial.map_map, MvPolynomial.coeff_map, hρ]
    rw [hfun]
  unfold GlobalTheory.NormSheaf.normIdeal
  rw [Ideal.map_span]
  apply le_antisymm
  · rw [Ideal.span_le]
    rintro _ ⟨a, ⟨m, g, hgJ, s, hs⟩, rfl⟩
    obtain ⟨P, hPK, hPR⟩ := hP m g
    have ha : a = P.coeff s := IsFractionRing.injective A K (by rw [hs, ← hPK, MvPolynomial.coeff_map])
    have hmem : (f.comp h) a ∈ Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) :=
      Ideal.subset_span ⟨s, by rw [ha]⟩
    rw [key m g P hPR] at hmem
    have hle : ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) ≤ ∏ j, J.map (ψ j) :=
      Finset.prod_le_prod' (fun j _ => Ideal.span_le.2 (by
        rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)))
    exact hle hmem
  · have hfg : ∀ j, ∃ t : Finset V', (↑t : Set V') ⊆ ψ j '' (J : Set B) ∧ J.map (ψ j) = Ideal.span (↑t : Set V') := by
      intro j
      have h1 : (J.map (ψ j)).FG := IsNoetherian.noetherian _
      rw [Ideal.map] at h1 ⊢
      exact (Submodule.fg_span_iff_fg_span_finset_subset _).1 h1
    choose t ht hspan using hfg
    have hpre : ∀ (x : Σ j, (t j : Set V')), ∃ b ∈ J, ψ x.1 b = x.2 := by
      rintro ⟨j, x, hx⟩
      obtain ⟨b, hb, e⟩ := ht j hx
      exact ⟨b, hb, e⟩
    choose pre hpreJ hpreψ using hpre
    let e := Fintype.equivFin (Σ j, (t j : Set V'))
    let g : Fin (Fintype.card (Σ j, (t j : Set V'))) → B := fun i => pre (e.symm i)
    have hgJ : ∀ i, g i ∈ J := fun i => hpreJ _
    obtain ⟨P, hPK, hPR⟩ := hP _ g
    have hj : ∀ j, Ideal.span (Set.range fun i => ψ j (g i)) = J.map (ψ j) := by
      intro j
      apply le_antisymm
      · rw [Ideal.span_le]; rintro _ ⟨i, rfl⟩; exact Ideal.mem_map_of_mem _ (hgJ i)
      · rw [hspan j, Ideal.span_le]
        intro x hx
        apply Ideal.subset_span
        refine ⟨e ⟨j, x, hx⟩, ?_⟩
        simp only [g, Equiv.symm_apply_apply]
        exact hpreψ ⟨j, x, hx⟩
    calc ∏ j, J.map (ψ j) = ∏ j, Ideal.span (Set.range fun i => ψ j (g i)) := by simp_rw [hj]
      _ = Ideal.span (Set.range fun s => (f.comp h) (P.coeff s)) := (key _ g P hPR).symm
      _ ≤ _ := by
        rw [Ideal.span_le]
        rintro _ ⟨s, rfl⟩
        apply Ideal.subset_span
        exact ⟨P.coeff s, ⟨_, g, hgJ, s, by rw [← hPK, MvPolynomial.coeff_map]⟩, rfl⟩
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormLocalEquationEqUniformiserPowClassicalPoint
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc

namespace GlobalTheory.Poinc.EqNormAt

theorem spectrumMap_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := by
  simp only [spMap, ← Spec.map_comp]
  rfl

theorem norm_val_eqAt : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] (M : RatModel o Ω) (D : GlobalTheory.EffCartierData M.Z) (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V] (ϖ : V) (a : ℕ) (ξ : Sp V ⟶ M.Z) (p : ℕ) [Fact p.Prime] (ι : FractionRing V →+* PadicAlgCl p) (j : V →+* OO p), (∀ x, ‖ι x‖ ≤ 1 ↔ x ∈ Set.range (algebraMap V (FractionRing V))) → (∀ v, (j v : PadicAlgCl p) = ι (algebraMap V (FractionRing V) v)) → idlAlong D.idealSheaf ξ = Ideal.span {ϖ ^ a} → ∀ f, EqAt M D (ξ (closedPoint V)) f → ‖M.val (gPt p ≫ spMap j ≫ ξ) f‖ = ‖ι (algebraMap V (FractionRing V) ϖ)‖ ^ a := by
  intro o Ω _ _ _ M D V _ _ _ ϖ a ξ p _ ι j hι hj hid f hf
  obtain ⟨i, hxi, rfl⟩ := hf
  set z := ξ (closedPoint V) with hz
  set e : V := (Scheme.stalkClosedPointTo ξ).hom ((M.Z.presheaf.germ _ z hxi).hom (D.f i)) with he
  have key : Ideal.span {e} = Ideal.span {ϖ ^ a} := by
    rw [← hid, idlAlong, D.stalkId_idealSheaf i z hxi, Ideal.map_span, Set.image_singleton]
  obtain ⟨u, hu⟩ := (Ideal.span_singleton_eq_span_singleton).1 key

  have hval : M.val (gPt p ≫ spMap j ≫ ξ) (valF M.pt (D.U i) (D.f i)) = ((j e : OO p) : PadicAlgCl p) := by
    rw [← Category.assoc, gPt, spectrumMap_comp, RatModel.val_spMap_comp _ ξ (specializes_rfl : z ⤳ z)
      ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩]
    have hv : M.valLoc ξ z specializes_rfl ⟨valF M.pt (D.U i) (D.f i), RatModel.valF_mem_O hxi _⟩ = e := by
      simp only [RatModel.valLoc, RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingEquiv.coe_toRingHom,
        ← RatModel.stalkEquiv_germ hxi, RingEquiv.symm_apply_apply, TopCat.Presheaf.stalkSpecializes_refl,
        Category.id_comp, he]
      rw [Category.id_comp]
    rw [RingHom.comp_apply, hv]
    rfl
  rw [hval, hj]
  have hunit : ∀ w : Vˣ, ‖ι (algebraMap V (FractionRing V) (w : V))‖ = 1 := by
    intro w
    have h1 := (hι _).2 ⟨(w : V), rfl⟩
    have h2 := (hι _).2 ⟨((w⁻¹ : Vˣ) : V), rfl⟩
    have h3 : ‖ι (algebraMap V (FractionRing V) (w : V))‖ * ‖ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V))‖ = 1 := by
      rw [← norm_mul, ← map_mul, ← map_mul, Units.mul_inv, map_one, map_one, norm_one]
    nlinarith [norm_nonneg (ι (algebraMap V (FractionRing V) (w : V))),
      norm_nonneg (ι (algebraMap V (FractionRing V) ((w⁻¹ : Vˣ) : V)))]
  have he' : e = ϖ ^ a * ((u⁻¹ : Vˣ) : V) := by
    rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [he', map_mul, map_mul, norm_mul, hunit, mul_one, map_pow, map_pow, norm_pow]

end GlobalTheory.Poinc.EqNormAt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartitionSelectionEvaluation
section
open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem.Top GlobalTheory.Fc

namespace GlobalTheory.Fc.RowsParts

variable {Bd : BdT} {𝒜 : FamClass} {σ : RawSel Bd 𝒜} {eps : ℝ} {Fm : FamP eps} {hc : 𝒜 Fm}

theorem ev_prem {p : Prop} {q : ℝ → BdP Bd} (h : p → ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc (q C)) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ C, C0 ≤ C → Ind.Ev σ Fm hc fun D O c b => p → q C D O c b := by
  by_cases hp : p
  · obtain ⟨C0, h0, h⟩ := h hp
    refine ⟨C0, h0, fun C hC => ?_⟩
    obtain ⟨x0, h⟩ := h C hC
    exact ⟨x0, fun x hx hle i _ => h x hx hle i⟩
  · exact ⟨0, le_rfl, fun _ _ => ⟨0, fun _ _ _ _ h => absurd h hp⟩⟩

end GlobalTheory.Fc.RowsParts

namespace GlobalTheory.Fc

open RowsParts

end GlobalTheory.Fc
end

