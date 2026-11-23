module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0475
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0478
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0430
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0305
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0306
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0476
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0489
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0480
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0456
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0465
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCover
public import Development.AbelianVarietyTheory.Definitions.Divisors.DlogRatioVolumeFormNeZero
public import ReciprocityTheory.L2DbarEstimates.IsLocalHomeomorph
public import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0477

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AcyclicResolutionComputesEtaleCohomologyStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.acyclic_resolution_computes_etale_cohomology : ∀ (R : Type) [CommRing R] (F : Shv R) (C : Cx R) [C.IsStrictlyGE 0] (ε : sgl F ⟶ C) [QuasiIso ε] (u : C ⟶ res R F), ε ≫ u = resAug F → (∀ (t : ℤ) (P : PSh) (n : ℤ), 0 < n → Subsingleton (H R (disc.obj P) (C.X t) n)) → ∀ (E : Spc) (n : ℤ), Function.Bijective (cpush ((chains R).obj E) u n) := by
  first
  | exact @GlobalTheory.EtC.acycRes_computes
  | exact GlobalTheory.EtC.acycRes_computes
  | (intros; apply GlobalTheory.EtC.acycRes_computes <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicPrimitiveVectorCompactRescale
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC
open scoped TensorProduct

namespace GlobalTheory.EtC.GeomZero

theorem res_comp {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (k : W ⟶ V) (g : V ⟶ U) (y : Sec F U) :
    Sec.res (k ≫ g) y = Sec.res k (Sec.res g y) := by
  simp [Sec.res]

theorem res_nsmul {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) (n : ℕ) (t : Sec F U) :
    Sec.res g (n • t) = n • Sec.res g t := map_nsmul ((F.obj.map g.op).hom) n t

theorem res_zero {R : Type} [CommRing R] {F : Shv R} {V U : Scheme.{0}} (g : V ⟶ U) :
    Sec.res g (0 : Sec F U) = 0 := map_zero ((F.obj.map g.op).hom)

theorem q_dvd_nsmul {q : ℕ} {i : ℤ} {U : Scheme.{0}} (t : Sec (tw q i) U) (k : ℕ) : (q * k) • t = 0 := by
  rw [← Nat.cast_smul_eq_nsmul (ULift.{1} (ZMod q))]
  have : ((q * k : ℕ) : ULift.{1} (ZMod q)) = 0 := by
    apply ULift.ext
    simp
  rw [this]
  exact zero_smul _ t

theorem eq_zero_of_geom : ∀ (q : ℕ) [NeZero q] (R : Type) [CommRing R], IsUnit (q : R) → ∀ (j : ℤ)
    (a : Ht q (sp R) 0 j), (∀ (K : Type) [Field K] [IsAlgClosed K] (f : R →+* K), pull _ (spMap f) _ 0 a = 0) → a = 0 := by
  intro q _ R _ _ j a ha
  obtain ⟨-, e, he, -⟩ := _root_.GlobalTheory.EtC.etale_cohomology_vanishing_negative_degree_zero (ZMod q) (tw q j)
  obtain ⟨s, rfl⟩ := (e (Spec (CommRingCat.of R))).surjective a
  have hgeo : ∀ (K : Type) [Field K] [IsAlgClosed K] (φ : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of R)),
      Sec.res φ s = 0 := by
    intro K _ _ φ
    have h := ha K (Spec.preimage φ).hom
    have hφ : Spec.map (CommRingCat.ofHom (Spec.preimage φ).hom) = φ := by
      rw [CommRingCat.ofHom_hom, Spec.map_preimage]
    rw [spMap, hφ, he] at h
    exact (map_eq_zero_iff _ (e _).injective).1 h
  have hs : s = 0 := by
    refine (sec_ext_glue (ZMod q) (tw q j) (Spec (CommRingCat.of R))).1 s 0 ?_
    refine (loc_iff_etale_affine_points (Spec (CommRingCat.of R)) (fun _ g => Sec.res g s = Sec.res g 0)
      (fun V W g k h => by rw [res_comp, res_comp, h])).2 ?_
    intro x
    have stab : ∀ (V W : Scheme.{0}) (g : V ⟶ Spec (CommRingCat.of R)) (k : W ⟶ V),
        (Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) →
        (Sec.res (k ≫ g) s = 0 ∨ ∃ (ζ : Prim q Γ(W, ⊤)) (c : ℕ), Sec.res (k ≫ g) s = c • twGen j ζ) := by
      rintro V W g k (h | ⟨ζ, c, h⟩)
      · left; rw [res_comp, h, res_zero]
      · right; exact ⟨ζ.map k.appTop.hom, c, by rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1]⟩
    obtain ⟨V, g, hV, hg, hx, hP⟩ := (loc_iff_etale_affine_points (Spec (CommRingCat.of R))
      (fun V g => Sec.res g s = 0 ∨ ∃ (ζ : Prim q Γ(V, ⊤)) (c : ℕ), Sec.res g s = c • twGen j ζ) stab).1
      ((GlobalTheory.T.tateTwist_sections_locally_generated q j).1 _ s) x
    refine ⟨V, g, hV, hg, hx, ?_⟩
    show Sec.res g s = Sec.res g 0
    rw [res_zero]
    rcases hP with h | ⟨ζ, c, h⟩
    · exact h
    · obtain ⟨v, -⟩ := hx
      let ψ : Spec (CommRingCat.of (AlgebraicClosure (V.residueField v))) ⟶ V :=
        Spec.map (CommRingCat.ofHom (algebraMap (V.residueField v) (AlgebraicClosure (V.residueField v)))) ≫
          V.fromSpecResidueField v
      have h0 := hgeo (AlgebraicClosure (V.residueField v)) (ψ ≫ g)
      rw [res_comp, h, res_nsmul, (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.2.1] at h0
      haveI : Nonempty (Spec (CommRingCat.of (AlgebraicClosure (V.residueField v)))) := inferInstance
      obtain ⟨k, rfl⟩ := (GlobalTheory.T.tateTwist_sections_locally_generated q j).2.2.1 _ _ _ h0
      rw [h]
      exact q_dvd_nsmul _ k
  rw [hs, map_zero]

end GlobalTheory.EtC.GeomZero
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockOneDetHermitianGram
section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace GlobalTheory.EtC.MVEtale

theorem mv_etale_mid : ∀ (q : ℕ) (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∀ (n i : ℤ) (x : Ht q (sp (Localization.Away f)) n i) (y : Ht q (sp A') n i), pull _ (spMap (Localization.awayMap (algebraMap A A') f)) _ _ x = pull _ (spMap (algebraMap A' (Localization.Away (algebraMap A A' f)))) _ _ y → ∃ b : Ht q (sp A) n i, pull _ (spMap (algebraMap A (Localization.Away f))) _ _ b = x ∧ pull _ (spMap (algebraMap A A')) _ _ b = y := by
  intro q A A' _ _ _ _ f h1 h2 n i x y hxy
  obtain ⟨w, hS⟩ := chains_shortExact (ZMod q) A A' f h1 h2
  obtain ⟨d, hd, -⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective (ZMod q) (res (ZMod q) (tw q i)) (_root_.GlobalTheory.EtC.ResBasic.res_basic (ZMod q) (tw q i)).2.1
  obtain ⟨e1, -, -⟩ := hd _ hS n
  have hb := cpull_biprod_bijective (ZMod q) ((chains (ZMod q)).obj (sp (Localization.Away f)))
    ((chains (ZMod q)).obj (sp A')) (res (ZMod q) (tw q i))
  obtain ⟨P, hP⟩ := (hb n).2 (x, y)
  have h0 : cpull (biprod.lift ((chains (ZMod q)).map (spMap (Localization.awayMap (algebraMap A A') f)))
      (-(chains (ZMod q)).map (spMap (algebraMap A' (Localization.Away (algebraMap A A' f))))))
      (res (ZMod q) (tw q i)) n P = 0 := by
    rw [cpull_lift_neg]
    have hP1 := congrArg Prod.fst hP
    have hP2 := congrArg Prod.snd hP
    simp only at hP1 hP2
    rw [hP1, hP2]
    exact sub_eq_zero.2 hxy
  obtain ⟨b, hb'⟩ := (e1 P).1 h0
  refine ⟨b, ?_, ?_⟩
  · have := congrArg Prod.fst (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.fst hP)
  · have := congrArg Prod.snd (cpull_desc_pair ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A'))) (res (ZMod q) (tw q i)) n b)
    simp only at this
    have hb1 : cpull (biprod.desc ((chains (ZMod q)).map (spMap (algebraMap A (Localization.Away f))))
      ((chains (ZMod q)).map (spMap (algebraMap A A')))) (res (ZMod q) (tw q i)) n b = P := hb'
    rw [hb1] at this
    exact this.symm.trans (congrArg Prod.snd hP)

end GlobalTheory.EtC.MVEtale
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechConerveChainsQuasiIsoOfLocallySurjective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC

theorem chains_cech_conerve_quasiIso : ∀ (R : Type) [CommRing R] (T : Type 1) [Category.{0} T] [HasFiniteWidePushouts T] (Ψ : T ⥤ PShᵒᵖ), (∀ n : ℕ, PreservesColimitsOfShape (WidePushoutShape (Fin (n + 1))) Ψ) → ∀ (U V : T) (g : U ⟶ V), Presheaf.IsLocallySurjective Scheme.etaleTopology.{0} (Ψ.map g).unop → QuasiIso ((chains R).map (lev Ψ (coAug g))) := by
  intro R _ T _ _ Ψ hΨ U V g hg
  obtain ⟨e, he, hc⟩ := GlobalTheory.T.cechConerve_map_eq_cechNerve_of_preservesWidePushouts T Ψ hΨ U V g
  have h2 := _root_.GlobalTheory.EtC.quasiIso_chains_cech_of_isLocallySurjective R _ _ (Ψ.map g).unop hg
  let h : ((Arrow.mk (Ψ.map g).unop).cechNerve : Spc) ⟶ disc.obj (Ψ.obj U).unop :=
    (Arrow.mk (Ψ.map g).unop).augmentedCechNerve.hom
  have key : lev Ψ (coAug g) = e ≫ h := hc.symm
  have h2' : QuasiIso ((chains R).map h) := h2
  rw [key, Functor.map_comp]
  haveI : IsIso ((chains R).map e) := inferInstance
  exact quasiIso_comp _ _
end GlobalTheory.EtC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChernClassKummerClassAdditiveStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chernClass_kummerClass_additive : GlobalTheory.EtC.DivisorAdditivity := by
  first | (exact @GlobalTheory.EtC.a6add_holds) | (exact GlobalTheory.EtC.a6add_holds) | (intros; apply GlobalTheory.EtC.a6add_holds  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassGroupDedekindAlgClosedDivisible
section
open Polynomial

namespace GlobalTheory.PicDiv

theorem classGroup_divisible : ∀ (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDomain B]
    [IsDedekindDomain B] [Algebra k B] [Algebra.FiniteType k B] (q : ℕ), (q : k) ≠ 0 →
    ∀ c : ClassGroup B, ∃ d : ClassGroup B, d ^ q = c := by
  intro k B _ _ _ _ _ _ _ q hq c
  obtain ⟨d, hd⟩ := GlobalTheory.T.pic_divisible_dedekind_finiteType_algClosed k B q (Ne.isUnit hq) (ClassGroup.equivPic B c)
  refine ⟨(ClassGroup.equivPic B).symm d, ?_⟩
  apply (ClassGroup.equivPic B).injective
  rw [map_pow, MulEquiv.apply_symm_apply, hd]

end GlobalTheory.PicDiv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmTypeProdNormSqEqAbsNormSpan
section
open NumberField MeasureTheory

namespace GlobalTheory.CMTypeNorm

theorem place_bijective {K : Type} [Field K] [NumberField K] {I : Type} {φ : I → K →+* ℂ} (h : GlobalTheory.CMVal.IsCMType φ) :
    Function.Bijective fun i => InfinitePlace.mk (φ i) := by
  constructor
  · intro i j hij
    obtain ⟨k, -, hk⟩ := h (φ j)
    have hj : j = k := hk j (Or.inl rfl)
    have hi : i = k := by
      apply hk i
      rcases InfinitePlace.mk_eq_iff.mp hij with h1 | h1
      · exact Or.inl h1.symm
      · exact Or.inr h1.symm
    rw [hi, hj]
  · intro w
    obtain ⟨k, hk, -⟩ := h w.embedding
    refine ⟨k, ?_⟩
    show InfinitePlace.mk (φ k) = w
    rw [← InfinitePlace.mk_embedding w, InfinitePlace.mk_eq_iff]
    rcases hk with h1 | h1
    · exact Or.inl h1.symm
    · exact Or.inr h1.symm

theorem prod_norm_sq_eq_absNorm :
    ∀ (K : Type) [Field K] [NumberField K] [NumberField.IsTotallyComplex K] (I : Type) [Fintype I] (φ : I → K →+* ℂ),
      GlobalTheory.CMVal.IsCMType φ → ∀ α : 𝓞 K,
        ∏ i, ‖φ i (α : K)‖ ^ 2 = ((Ideal.absNorm (Ideal.span {α}) : ℕ) : ℝ) := by
  intro K _ _ _ I _ φ h α
  have h1 : ∏ i, ‖φ i (α : K)‖ ^ 2 = ∏ w : InfinitePlace K, w (α : K) ^ w.mult := by
    refine Fintype.prod_bijective _ (place_bijective h) _ _ fun i => ?_
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  rw [h1, InfinitePlace.prod_eq_abs_norm, Ideal.absNorm_span_singleton, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

end GlobalTheory.CMTypeNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologyContinuousBaseChangeOfLevelsStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cohomologyContinuous_base_change_of_levels : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (I : Type) [SmallCategory I] [IsCofiltered I] (G : I ⥤ Over S) (c : Cone G), (∀ k : SimplexCategoryᵒᵖ, ∃ (X : Scheme.{0}) (r : X ⟶ S) (e : yoneda.obj X ≅ E.obj k), e.hom ≫ p.app k = yoneda.map r ∧ ContCone R F ((bc (sch.map r)).mapCone c)) → ContCone R F ((bc p).mapCone c) := by
  first | (exact @GlobalTheory.EtC.CcStep.cc_step) | (exact GlobalTheory.EtC.CcStep.cc_step) | (intros; apply GlobalTheory.EtC.CcStep.cc_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryModuleEqTopFormsOfFiniteCoverStatement
section
open GlobalTheory.PD GlobalTheory.CechDR KaehlerDifferential
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.complementaryModule_eq_topForms_of_finiteCover : ∀ (k F K : Type) [Field k] [CharZero k] [Field F] [Field K] [Algebra k F] [Algebra k K] [Algebra F K] [IsScalarTower k F K] [FiniteDimensional F K] (d : ℕ) (u : Fin d → F), AlgebraicIndependent k u → ∀ (A : Subalgebra k F) [IsFractionRing A F], A = Algebra.adjoin k (Set.range u) → ∀ (B : Subalgebra k K), B = (integralClosure A K).restrictScalars k → Algebra.Smooth k B → ∀ τ : DR k K →ₗ[K] K, τ (ExteriorAlgebra.ιMulti K d fun j => D k K (algebraMap F K (u j))) = 1 → ∀ z : K, (∀ b : B, Algebra.trace F K (z * b) ∈ A) ↔ ∃ y ∈ omB k K B d, τ y = z := by
  first | (exact @GlobalTheory.ComplementaryForms.complementary_eq_topForms) | (exact GlobalTheory.ComplementaryForms.complementary_eq_topForms) | (intros; apply GlobalTheory.ComplementaryForms.complementary_eq_topForms  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianPosSemidefOfLeviFormNonneg
section
open Filter Topology MeasureTheory Metric ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y ComplexConjugate
open scoped ComplexOrder

namespace GlobalTheory

theorem cHess_posSemidef_of_levi_nonneg (n : ℕ) (φ : V n → ℝ) (z : V n) (hf : ContDiffAt ℝ 2 φ z)
    (hL : ∀ ξ : Fin n → ℂ, 0 ≤ (leviV n (fun v => (φ v : ℂ)) z ξ).re) :
    (cHess n (fun v => (φ v : ℂ)) z).PosSemidef := by
  classical
  set g : V n → ℂ := fun v => ((φ v : ℝ) : ℂ) with hg
  have hg2 : ContDiffAt ℝ 2 g z := Complex.ofRealCLM.contDiff.contDiffAt.comp z hf
  have hgc : (fun w => conj (g w)) = g := funext fun w => by simp [g]
  have hH : (cHess n g z).IsHermitian := by
    ext j k
    simp only [Matrix.conjTranspose_apply, cHess, Matrix.of_apply]
    show conj (wd n k (wdb n j g) z) = wd n j (wdb n k g) z
    have h1 : (fun w => conj (wdb n j g w)) = wd n j g := by
      funext w
      rw [← ChartWirtingerDerivatives.wd_conj' n j g w, hgc]
    rw [← ChartWirtingerDerivatives.wdb_conj' n k (wdb n j g) z, h1, comm_wd_wdb g z hg2 j k]
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun y => ?_
  have hre : dotProduct (star y) (Matrix.mulVec (cHess n g z) y) =
      leviV n g z (fun k => conj (y k)) := by
    simp only [dotProduct, Matrix.mulVec, leviV, cHess, Matrix.of_apply, Finset.mul_sum,
      Pi.star_apply, Complex.conj_conj]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    simp only [Complex.star_def]
    ring
  have him := hH.im_star_dotProduct_mulVec_self y
  refine Complex.le_def.2 ⟨?_, ?_⟩
  · rw [hre]; exact hL _
  · simpa using him.symm

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupChernKummerPullbackNaturalityStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_chern_kummer_pullback_naturality : GlobalTheory.EtC.DivisorNaturality := by
  first | (exact @GlobalTheory.EtC.a6nat_holds) | (exact GlobalTheory.EtC.a6nat_holds) | (intros; apply GlobalTheory.EtC.a6nat_holds  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CupVanishesOnTwoMemberCoverStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cup_vanishes_on_two_member_cover : GlobalTheory.EtC.DivisorSupportCondition := by
  first | (exact @GlobalTheory.EtC.a6supp) | (exact GlobalTheory.EtC.a6supp) | (intros; apply GlobalTheory.EtC.a6supp  <;> assumption)
end

