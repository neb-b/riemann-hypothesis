module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0435
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0427
public import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0408
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0434
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0411
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0407
public import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0440
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0402
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TangentBijectionOfValues
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftHom
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCoinductionAugmentationCompDEqZero
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0441
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0436
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0019

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenPartProjectionMatrixMapMulVecOfEigenvectorStatement
section
open Matrix NumberField GlobalTheory.UPel.HT GlobalTheory.UPel.HT.LieLin GlobalTheory.UPel.HT.LieLin.RankIdeal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eigenPartProjectionMatrix_map_mulVec_of_eigenvector : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (B : Type) [CommRing B]
    (βB : R →+* B) (n : ℕ) (M : 𝓞 D.F →+* Matrix (Fin n) (Fin n) B) (K : Type) [CommRing K] (g : B →+* K)
    (i : Fin D.a) (v : Fin n → K), (∀ c : 𝓞 D.F, (M c).map g *ᵥ v = g (βB (b.t i c)) • v) →
      (projMat b βB M i).map g *ᵥ v = v := by
  first | (exact @GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (exact GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig) | (intros; apply GlobalTheory.UPel.HT.LieLin.RankIdeal.projMat_map_mulVec_of_eig  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfUpwardFamilyStandardCover
section
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CatCoh.Desc.VandermondeTwoBasis

theorem sep_of_covBy : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), [Quiver.IsThin C] → [Quiver.IsThin C'] → Desc.HasLoc F → (∀ (t₁ t₂ : C') (S : C), (G.obj t₁ ⟶ S) → (G.obj t₂ ⟶ S) → ∃ (n : ℕ) (b : Fin n → F.obj S), Ideal.span (Set.range b) = ⊤ ∧ ∀ (i : Fin n) (S' : C) (u : S ⟶ S'), IsUnit (mp F u (b i)) → ∃ t₃, Nonempty (t₁ ⟶ t₃) ∧ Nonempty (t₂ ⟶ t₃) ∧ Nonempty (G.obj t₃ ⟶ S')) → ∀ (t : C') (Sg : ∀ t', (t ⟶ t') → Prop), (∀ t' t'' (a : t ⟶ t') (b : t' ⟶ t''), Sg t' a → Sg t'' (a ≫ b)) → Desc.VandermondeTwoBasis.CovBy F (fun S ↦ ∃ (t' : C') (a : t ⟶ t'), Sg t' a ∧ Nonempty (G.obj t' ⟶ S)) (G.obj t) → Desc.Sep (G ⋙ F) Sg := by
  intro R _ C _ C' _ F G _ _ H _ t Sg _ hcov
  obtain ⟨n, b, hb, hc⟩ := hcov
  intro x hx
  refine Desc.sep_std H hb x fun S u ⟨i, hi⟩ ↦ ?_
  obtain ⟨t', a, ha, ⟨w⟩⟩ := hc i S u hi
  have e : u = G.map a ≫ w := Subsingleton.elim _ _
  have h0 : mp F (G.map a) x = 0 := hx t' a ha
  rw [e, mp_comp, h0, map_zero]

end GlobalTheory.CatCoh.Desc.VandermondeTwoBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyEquivalenceBasicPropertiesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleCohomologyEquivalence_basic_properties : ∀ (R : Type) [CommRing R] (F : Shv R), (∀ (E E' : Spc) (f : E ⟶ E'), IsIso f → Eqv R f F) ∧ (∀ (E E' E'' : Spc) (f : E ⟶ E') (g : E' ⟶ E''), (Eqv R f F → Eqv R g F → Eqv R (f ≫ g) F) ∧ (Eqv R f F → Eqv R (f ≫ g) F → Eqv R g F) ∧ (Eqv R g F → Eqv R (f ≫ g) F → Eqv R f F)) ∧ (∀ (E E' : Spc) (f : E ⟶ E'), QuasiIso ((chains R).map f) → Eqv R f F) ∧ ∀ (E E' : Spc) (f : E ⟶ E'), Eqv R f F → (AcycF R E F ↔ AcycF R E' F) := by
  first | (exact @GlobalTheory.EtC.eqv_basic) | (exact GlobalTheory.EtC.eqv_basic) | (intros; apply GlobalTheory.EtC.eqv_basic  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleMayerVietorisFreeSequenceExactStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etale_mayerVietoris_free_sequence_exact : ∀ (R : Type) [CommRing R] (A A' : Type) [CommRing A] [CommRing A'] [Algebra A A'] [Algebra.Etale A A'] (f : A), (∀ a' : A', ∃ a : A, a' - algebraMap A A' a ∈ Ideal.span {algebraMap A A' f}) → (∀ a : A, algebraMap A A' a ∈ Ideal.span {algebraMap A A' f} → a ∈ Ideal.span {f}) → ∃ w, (ShortComplex.mk (biprod.lift ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (Localization.awayMap (algebraMap A A') f))))) (-(free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A' (Localization.Away (algebraMap A A' f)))))))) (biprod.desc ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A (Localization.Away f)))))) ((free R).map (yoneda.map (Spec.map (CommRingCat.ofHom (algebraMap A A')))))) w).Exact := by
  first | (exact @GlobalTheory.EtC.MVExact.mv_exact) | (exact GlobalTheory.EtC.MVExact.mv_exact) | (intros; apply GlobalTheory.EtC.MVExact.mv_exact <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSheafOfRingFunctorIsFinitaryStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSheafOfRingFunctor_isFinitary : ∀ (R : Type) [CommRing R] (M : CommRingCat.{0} ⥤ ModuleCat.{1} (ULift.{1} R)), PreservesFilteredColimitsOfSize.{0, 0} M → Finitary (ofRings R M) := by
  first
  | exact @GlobalTheory.ofRings_finitary
  | exact GlobalTheory.ofRings_finitary
  | (intros; apply GlobalTheory.ofRings_finitary <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyBaseChangeCoprodBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC

namespace GlobalTheory.EtC.BcCoprod

theorem bc_map_fst {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E) = pullback.fst p (sch.map V.hom) := by
  simp only [bc, pullback.map]
  set_option synthInstance.maxHeartbeats 200000 in
    simpa only [Category.comp_id] using pullback.lift_fst _ _ _

theorem bc_map_snd {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    (bc p).map g ≫ (pullback.snd p (sch.map U.hom) : (bc p).obj U ⟶ _) = pullback.snd p (sch.map V.hom) ≫ sch.map g.left := by
  set_option synthInstance.maxHeartbeats 200000 in
    simp only [bc, pullback.map]
  set_option synthInstance.maxHeartbeats 200000 in
    exact pullback.lift_snd _ _ _

theorem isPullback_bc {E : Spc} {S : Scheme.{0}} (p : E ⟶ sch.obj S) {V U : Over S} (g : V ⟶ U) :
    IsPullback ((bc p).map g) (pullback.snd p (sch.map V.hom)) (pullback.snd p (sch.map U.hom)) (sch.map g.left) := by
  have h2 : sch.map g.left ≫ sch.map U.hom = sch.map V.hom := by
    rw [← sch.map_comp, Over.w g]
  have outer : IsPullback ((bc p).map g ≫ (pullback.fst p (sch.map U.hom) : (bc p).obj U ⟶ E))
      (pullback.snd p (sch.map V.hom)) p (sch.map g.left ≫ sch.map U.hom) := by
    rw [bc_map_fst p g, h2]
    exact IsPullback.of_hasPullback p (sch.map V.hom)
  exact IsPullback.of_right outer (bc_map_snd p g) (IsPullback.of_hasPullback p (sch.map U.hom))

theorem main : ∀ (R : Type) [CommRing R] (F : Shv R) (S : Scheme.{0}) (E : Spc) (p : E ⟶ sch.obj S) (U : Over S) (ι : Type) (V : ι → Over S) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U.left (fun i => (j i).left)) → ∀ n : ℤ, Function.Bijective (fun (x : H R ((bc p).obj U) F n) (i : ι) => pull R ((bc p).map (j i)) F n x) := by
  intro R _ F S E p U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F ((bc p).obj U) ι (fun i => (bc p).obj (V i)) (fun i => (bc p).map (j i)) (fun k => ?_) n
  refine GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U.left ι (fun i => (V i).left) (fun i => (j i).left) hc (((bc p).obj U).obj k)
    ((pullback.snd p (sch.map U.hom)).app k) (fun i => ((bc p).obj (V i)).obj k)
    (fun i => ((bc p).map (j i)).app k) (fun i => (pullback.snd p (sch.map (V i).hom)).app k) (fun i => ?_)
  exact (isPullback_bc p (j i)).map ((evaluation _ _).obj k)

end GlobalTheory.EtC.BcCoprod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceCohomologyCoprodSchemesBijective
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC

namespace GlobalTheory

theorem coh_coprod_bijective : ∀ (R : Type) [CommRing R] (F : Shv R) (U : Scheme.{0}) (ι : Type) (V : ι → Scheme.{0}) (j : ∀ i, V i ⟶ U), IsColimit (Cofan.mk U j) → ∀ n : ℤ, Function.Bijective (fun (x : H R (sch.obj U) F n) (i : ι) => pull R (sch.map (j i)) F n x) := by
  intro R _ F U ι V j hc n
  refine GlobalTheory.T.etaleSpaceCohomology_levelwise_coproduct_bijective R F (sch.obj U) ι (fun i => sch.obj (V i)) (fun i => sch.map (j i)) ?_ n
  intro k
  exact GlobalTheory.T.freeEtaleSheaf_presheaf_over_coproduct_eq_sum R U ι V j hc (yoneda.obj U) (𝟙 _) (fun i => yoneda.obj (V i)) (fun i => yoneda.map (j i))
    (fun _ => 𝟙 _) (fun i => IsPullback.of_vert_isIso (by simp))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleSpaceDescentLocalEquivalenceStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex TensorProduct GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.etaleSpace_descent_local_equivalence : ∀ (R : Type) [CommRing R] (F : Shv R) (T : Type 1) [Category.{0} T] (Cov : MorphismProperty T) [Cov.IsStableUnderComposition] (Φ Φ' : T ⥤ Spcᵒᵖ) (α : Φ' ⟶ Φ), Refines Cov (fun U X a => Hyp R Φ a ∧ Hyp R Φ' a) → (∀ (U : T) (n : ℤ) (x : H R (Φ.obj U).unop F n), ∃ (V : T) (g : U ⟶ V), Cov g ∧ ∃ y : H R (Φ'.obj V).unop F n, pull R (α.app V).unop F n y = pull R (Φ.map g).unop F n x) → (∀ (U : T) (n : ℤ) (y : H R (Φ'.obj U).unop F n), pull R (α.app U).unop F n y = 0 → ∃ (V : T) (g : U ⟶ V), Cov g ∧ pull R (Φ'.map g).unop F n y = 0) → ∀ U, Eqv R (α.app U).unop F := by
  first | (exact @GlobalTheory.EtC.Descent.main) | (exact GlobalTheory.EtC.Descent.main) | (intros; apply GlobalTheory.EtC.Descent.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EvalRingPointDualNumberSndLinearDerivation
section
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.TangentOrigin

noncomputable section

namespace GlobalTheory.DualEval

theorem spMap_comp_ring {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  simp only [spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]

theorem evalPt_of_eq {R R' : Type} [CommRing R] [CommRing R'] {X : Scheme.{0}} (φ : R →+* R')
    (G' : Sp R ⟶ X) (x : Sp R' ⟶ X) (O : X.Opens) (h0 : ⊤ ≤ G' ⁻¹ᵁ O) (hx : ⊤ ≤ x ⁻¹ᵁ O)
    (e : x = spMap φ ≫ G') (f : Γ(X, O)) : evalPt x O hx f = φ (evalPt G' O h0 f) := by
  subst e
  exact evalPt_spMap_comp φ G' O h0 hx f

theorem snd_of_mul_eq {K : Type} [Field K] (u t s : DualNumber K) (ht : t.fst ≠ 0)
    (e : u * t = s) : u.snd = (s.snd - s.fst / t.fst * t.snd) / t.fst := by
  have e1 : u.fst * t.fst = s.fst := by rw [← e]; rfl
  have e2 : u.fst * t.snd + u.snd * t.fst = s.snd := by rw [← e, DualNumber.snd_mul]
  have hu : u.fst = s.fst / t.fst := by rw [eq_div_iff ht, e1]
  rw [eq_div_iff ht, ← e2, hu]
  ring

end GlobalTheory.DualEval

namespace GlobalTheory.DualEval

attribute [local instance] RingHom.ker_isPrime

section Lift

variable {S K : Type} [CommRing S] [Field K] (ψ : S →+* K)

theorem isUnit_of_lifts (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
    (y : (RingHom.ker ψ).primeCompl) : IsUnit (φ y) := by
  refine TrivSqZeroExt.isUnit_iff_isUnit_fst.2 ?_
  rw [hφ]
  exact Ne.isUnit fun h0 => y.2 (by simpa [RingHom.mem_ker] using h0)

def liftAt (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    Localization.AtPrime (RingHom.ker ψ) →+* DualNumber K :=
  IsLocalization.lift (M := (RingHom.ker ψ).primeCompl) (isUnit_of_lifts ψ φ hφ)

theorem liftAt_comp (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    (liftAt ψ φ hφ).comp (algebraMap S (Localization.AtPrime (RingHom.ker ψ))) = φ :=
  IsLocalization.lift_comp _

theorem liftAt_mk'_mul (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t) * φ t = φ s := by
  have := congrArg (liftAt ψ φ hφ)
    (IsLocalization.mk'_spec (Localization.AtPrime (RingHom.ker ψ)) s t)
  rw [map_mul] at this
  unfold liftAt at this ⊢
  rw [IsLocalization.lift_eq, IsLocalization.lift_eq] at this
  exact this

theorem psi_ne_zero (t : (RingHom.ker ψ).primeCompl) : ψ t ≠ 0 := fun h0 =>
  t.2 (by simpa [RingHom.mem_ker] using h0)

theorem liftAt_mk'_snd (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) (s : S)
    (t : (RingHom.ker ψ).primeCompl) :
    (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).snd =
      ((φ s).snd - ψ s / ψ t * (φ t).snd) / ψ t := by
  have := snd_of_mul_eq _ _ _ (by rw [hφ]; exact psi_ne_zero ψ t) (liftAt_mk'_mul ψ φ hφ s t)
  rw [hφ, hφ] at this
  exact this

theorem liftAt_isLocalHom (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s) :
    IsLocalHom ((TrivSqZeroExt.fstHom K K K).toRingHom.comp (liftAt ψ φ hφ)) := by
  refine ⟨fun x hx => ?_⟩
  obtain ⟨⟨s, t⟩, rfl⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl x
  rw [IsLocalization.AtPrime.isUnit_mk'_iff]
  intro hs
  have e1 : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst *
      ψ t = ψ s := by
    rw [← hφ, ← hφ, ← liftAt_mk'_mul ψ φ hφ s t]
    rfl
  have hs0 : ψ s = 0 := by simpa [RingHom.mem_ker] using hs
  rw [hs0] at e1
  have hne : (liftAt ψ φ hφ (IsLocalization.mk' (Localization.AtPrime (RingHom.ker ψ)) s t)).fst
      ≠ 0 := hx.ne_zero
  exact hne ((mul_eq_zero.1 e1).resolve_right (psi_ne_zero ψ t))

end Lift

theorem evalPt_snd_sum {X : Scheme.{0}} {S K : Type} [CommRing S] [Field K] (G : Sp S ⟶ X)
    (ψ : S →+* K) {ι : Type} [Fintype ι] (θc : ι → (S →+* DualNumber K)) (θ : S →+* DualNumber K)
    (m : ι → K) (h1 : ∀ a s, (θc a s).fst = ψ s) (h2 : ∀ s, (θ s).fst = ψ s)
    (h3 : ∀ s, (θ s).snd = ∑ a, m a * (θc a s).snd) (O : X.Opens) (f : Γ(X, O))
    (h : ⊤ ≤ (spMap θ ≫ G) ⁻¹ᵁ O) (h' : ∀ a, ⊤ ≤ (spMap (θc a) ≫ G) ⁻¹ᵁ O) :
    (evalPt (spMap θ ≫ G) O h f).snd = ∑ a, m a * (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd := by
  classical
  let L := Localization.AtPrime (RingHom.ker ψ)
  let alg : S →+* L := algebraMap S L
  let fstR : DualNumber K →+* K := (TrivSqZeroExt.fstHom K K K).toRingHom
  let G' : Sp L ⟶ X := spMap alg ≫ G
  haveI := liftAt_isLocalHom ψ θ h2
  have hm : IsLocalRing.closedPoint L ∈ G' ⁻¹ᵁ O := by
    rw [← IsLocalRing.comap_closedPoint (fstR.comp (liftAt ψ θ h2))]
    have hmor : spMap (fstR.comp (liftAt ψ θ h2)) ≫ G' = spMap fstR ≫ spMap θ ≫ G := by
      rw [← Category.assoc, ← Category.assoc, ← spMap_comp_ring, ← spMap_comp_ring,
        RingHom.comp_assoc, liftAt_comp]
    let pt : Sp K := IsLocalRing.closedPoint K
    have key : (spMap (fstR.comp (liftAt ψ θ h2)) ≫ G') pt ∈ O := by
      rw [hmor]
      exact h (Set.mem_univ ((spMap fstR) pt))
    exact key
  have h0 : ⊤ ≤ G' ⁻¹ᵁ O := ((IsLocalRing.closed_point_mem_iff (U := G' ⁻¹ᵁ O)).1 hm).ge
  have hval : ∀ (φ : S →+* DualNumber K) (hφ : ∀ s, (φ s).fst = ψ s)
      (hx : ⊤ ≤ (spMap φ ≫ G) ⁻¹ᵁ O),
      evalPt (spMap φ ≫ G) O hx f = liftAt ψ φ hφ (evalPt G' O h0 f) := by
    intro φ hφ hx
    refine evalPt_of_eq _ G' _ O h0 hx ?_ f
    rw [← Category.assoc, ← spMap_comp_ring, liftAt_comp]
  obtain ⟨⟨s, t⟩, hst⟩ := IsLocalization.mk'_surjective (RingHom.ker ψ).primeCompl (evalPt G' O h0 f)
  have hA : ∀ a, (evalPt (spMap (θc a) ≫ G) O (h' a) f).snd =
      (((θc a) s).snd - ψ s / ψ t * ((θc a) t).snd) / ψ t := fun a => by
    rw [hval (θc a) (h1 a) (h' a), ← hst, liftAt_mk'_snd]
  rw [hval θ h2 h, ← hst, liftAt_mk'_snd]
  simp_rw [hA, h3, Finset.mul_sum, ← Finset.sum_sub_distrib,
    Finset.sum_div]
  refine Finset.sum_congr rfl fun a _ => ?_
  ring

end GlobalTheory.DualEval
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoinducedSheafInjectiveResolutionFreeExact
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem GlobalTheory.EtC.coindRes_exists : ∀ (R S : Type) [CommRing R] [CommRing S] (φ : R →+* S) (J : Shv R) [Injective J], (∀ P : PSh, Module.Injective (ULift.{1} R) ((free R).obj P ⟶ J)) → ∃ (C : Cx R) (ε : sgl ((restr φ).obj ((coind φ).obj J)) ⟶ C), C.IsStrictlyGE 0 ∧ (∀ t, Injective (C.X t)) ∧ QuasiIso ε ∧ ∀ (P : PSh) (n : ℤ), 0 < n → Subsingleton (CohomologyClass (sgl ((free R).obj P)) C n) := by
  intro R S _ _ φ J _ hJ
  haveI := GlobalTheory.T.etaleCoinductionComplexAugmentation_quasiIso R S φ J hJ
  let I : InjectiveResolution ((restr φ).obj ((coind φ).obj J)) :=
    { cocomplex := coindCx φ J
      injective := fun n => GlobalTheory.T.injective_etaleSheafOfLinearMapsFromModule R J ((scalarsRes φ).complex.X n)
      ι := coindAug φ J }
  refine ⟨I.cochainComplex, I.ι', inferInstance, inferInstance, inferInstance, ?_⟩
  intro P n hn
  obtain ⟨k, rfl⟩ : ∃ k : ℕ, n = (k : ℤ) + 1 := ⟨(n - 1).toNat, by omega⟩
  refine ⟨fun x y => ?_⟩
  suffices h : ∀ x : CohomologyClass (sgl ((free R).obj P)) I.cochainComplex ((k : ℤ) + 1), x = 0 by
    rw [h x, h y]
  intro x
  obtain ⟨α, rfl⟩ := x.mk_surjective
  obtain ⟨f, hf, rfl⟩ := Cocycle.fromSingleMk_surjective α ((k : ℤ) + 1) (zero_add _) ((k : ℤ) + 1 + 1) rfl
  rw [CohomologyClass.mk_eq_zero_iff, Cocycle.fromSingleMk_mem_coboundaries_iff _ _ _ _ _ (k : ℤ) rfl]
  have hex : ∀ b, ((scalarsRes φ).complex.d (k + 1) k).hom b = 0 → ∃ a, ((scalarsRes φ).complex.d (k + 2) (k + 1)).hom a = b := by
    intro b hb
    exact ((ShortComplex.moduleCat_exact_iff _).1 ((scalarsRes φ).exact_succ k)) b hb
  have hd1 := I.cochainComplex_d ((k : ℤ) + 1) ((k : ℤ) + 1 + 1) (k + 1) (k + 2) (by simp) (by push_cast; ring)
  rw [hd1] at hf
  have h2 : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫ I.cocomplex.d (k + 1) (k + 2) = 0 := by
    rw [← cancel_mono (I.cochainComplexXIso ((k : ℤ) + 1 + 1) (k + 2) (by push_cast; ring)).inv]
    simpa using hf
  have hf' : (f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom) ≫
      (homSh J).map ((scalarsRes φ).complex.d (k + 2) (k + 1)).op = 0 := by
    rw [← coindCx_d]
    exact h2
  obtain ⟨g, hg⟩ := GlobalTheory.T.exists_lift_etaleSheafOfLinearMaps_exact R J ((free R).obj P) (hJ P) _ _ _ _ _ hex _ hf'
  refine ⟨g ≫ (I.cochainComplexXIso (k : ℤ) k rfl).inv, ?_⟩
  rw [I.cochainComplex_d (k : ℤ) ((k : ℤ) + 1) k (k + 1) rfl (by simp)]
  erw [Category.assoc, Iso.inv_hom_id_assoc]
  have hg' : g ≫ I.cocomplex.d k (k + 1) = f ≫ (I.cochainComplexXIso ((k : ℤ) + 1) (k + 1) (by simp)).hom := by
    rw [← hg, ← coindCx_d]
    rfl
  erw [← Category.assoc, hg', Category.assoc, Iso.hom_inv_id, Category.comp_id]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConnectingCocycleHypercohomologyLesStatement
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_connecting_cocycle_hypercohomology_les : ∀ (R : Type) [CommRing R] (S : ShortComplex (Shv R)), S.ShortExact →
  ∃ z : Cocycle (res R S.X₃) (res R S.X₁) 1,
    (∀ (K : Cx R) (n : ℤ),
      Function.Exact (HK.post R K S.f n) (HK.post R K S.g n) ∧
      Function.Exact (HK.post R K S.g n) (HK.ext R K z n (n + 1) rfl) ∧
      Function.Exact (HK.ext R K z n (n + 1) rfl) (HK.post R K S.f (n + 1))) ∧
    ∃ s : ℤˣ, ∀ (φ : S.X₂ ⟶ (res R S.X₁).X 0) (ψ : S.X₃ ⟶ (res R S.X₁).X 1),
      S.f ≫ φ = resι R S.X₁ → S.g ≫ ψ = φ ≫ (res R S.X₁).d 0 1 →
      ∀ w : Cocycle (sgl S.X₃) (res R S.X₁) 1, sglι S.X₃ ≫ w.1.v 0 1 (zero_add 1) = ψ →
        CohomologyClass.mk (zcomp (Cocycle.ofHom (resAug S.X₃)) z (zero_add 1)) = s • CohomologyClass.mk w := by
  first | (exact @GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (exact GlobalTheory.EtC.LesChar.exists_connecting_cocycle) | (intros; apply GlobalTheory.EtC.LesChar.exists_connecting_cocycle  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinrankQuotientSpanModEqOne
section
open Polynomial

namespace GlobalTheory

theorem isLocalization_fractionRing_of_finite_polynomial (k A : Type) [Field k] [CommRing A] [IsDomain A]
    [Algebra k[X] A] [Module.Finite k[X] A] [FaithfulSMul k[X] A] :
    IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) (FractionRing A) := by
  have hinj : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  have hle : Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X]) ≤ nonZeroDivisors A := by
    rintro _ ⟨p, hp, rfl⟩
    exact mem_nonZeroDivisors_of_ne_zero
      ((map_ne_zero_iff _ hinj).mpr (nonZeroDivisors.ne_zero hp))
  refine
    { map_units := fun y => IsLocalization.map_units (FractionRing A) ⟨y.1, hle y.2⟩
      surj := fun z => ?_
      exists_of_eq := fun {x y} hxy => ⟨1, by rw [IsFractionRing.injective A (FractionRing A) hxy]⟩ }
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) z
  have hb0 : (b : A) ≠ 0 := nonZeroDivisors.ne_zero b.2
  have hne := Ideal.comap_ne_bot_of_integral_mem (R := k[X]) hb0 (Ideal.mem_span_singleton_self (b : A))
    (Algebra.IsIntegral.isIntegral _)
  obtain ⟨p, hpI, hp0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨c, hc⟩ := Ideal.mem_span_singleton'.mp hpI
  refine ⟨⟨c * a, ⟨_, ⟨p, mem_nonZeroDivisors_of_ne_zero hp0, rfl⟩⟩⟩, ?_⟩
  simp only
  rw [← hc, map_mul, map_mul, ← hab]
  ring

end GlobalTheory

namespace GlobalTheory

theorem exists_finrank_quotient_span_mod_eq_one :
    ∀ (k A : Type) [Field k] [IsAlgClosed k] [CommRing A] [IsDomain A] [Algebra k A] [Algebra k[X] A]
      [IsScalarTower k k[X] A] [Module.Finite k[X] A] [Module.Free k[X] A] (N : ℕ), 1 ≤ N →
      ∃ f : A, f ≠ 0 ∧ Module.finrank k (A ⧸ Ideal.span {f}) % N = 1 % N := by
  intro k A _ _ _ _ _ _ _ _ _ N hN
  have : FaithfulSMul k[X] A := inferInstance
  have hinjA : Function.Injective (algebraMap k[X] A) := FaithfulSMul.algebraMap_injective k[X] A
  set L := FractionRing A
  have hinjL : Function.Injective (algebraMap k[X] L) := by
    rw [IsScalarTower.algebraMap_eq k[X] A L]
    exact (IsFractionRing.injective A L).comp hinjA
  have : FaithfulSMul k[X] L := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinjL
  letI : Algebra (RatFunc k) L := RatFunc.liftAlgebra k L
  have : IsLocalization (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) L :=
    isLocalization_fractionRing_of_finite_polynomial k A
  have : Module.Finite (RatFunc k) L :=
    Module.Finite.of_isLocalization k[X] A (Rₚ := RatFunc k) (Sₚ := L) (nonZeroDivisors k[X])
  have hC1 : GlobalTheory.NeedB.IsFirstChernClassOfLineBundle (RatFunc k) :=
    GlobalTheory.is_c1_of_finite_of_tsen_lang_systems (RatFunc k) (RatFunc k) (GlobalTheory.tsenLang_ratFunc k)
  obtain ⟨h, hh⟩ := GlobalTheory.norm_surjective_of_is_c1 (RatFunc k) L hC1 RatFunc.X RatFunc.X_ne_zero
  obtain ⟨⟨x, ⟨_, ⟨m, hm0, rfl⟩⟩⟩, hx⟩ :=
    IsLocalization.surj (Algebra.algebraMapSubmonoid A (nonZeroDivisors k[X])) h
  have hm0' : m ≠ 0 := nonZeroDivisors.ne_zero hm0
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  set g : A := x * algebraMap k[X] A (m ^ M) with hg
  have hgL : algebraMap A L g
      = h * algebraMap (RatFunc k) L (algebraMap k[X] (RatFunc k) (m ^ (M + 1))) := by
    simp only at hx
    rw [hg, map_mul, ← hx, ← IsScalarTower.algebraMap_apply, ← IsScalarTower.algebraMap_apply,
      ← IsScalarTower.algebraMap_apply, pow_succ, map_mul]
    ring
  have hnorm : Algebra.norm k[X] g = X * (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L := by
    apply IsFractionRing.injective k[X] (RatFunc k)
    rw [← Algebra.norm_localization k[X] (Rₘ := RatFunc k) (Sₘ := L) (nonZeroDivisors k[X]) g, hgL, map_mul, hh,
      Algebra.norm_algebraMap, map_mul, RatFunc.algebraMap_X, ← map_pow]
  have hp : (m ^ (M + 1)) ^ Module.finrank (RatFunc k) L ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hm0')
  have hg0 : g ≠ 0 := by
    intro h0
    rw [h0, Algebra.norm_zero] at hnorm
    exact mul_ne_zero X_ne_zero hp hnorm.symm
  refine ⟨g, hg0, ?_⟩
  rw [finrank_quotient_span_eq_natDegree_norm (Module.Free.chooseBasis k[X] A) hg0, hnorm,
    natDegree_mul X_ne_zero hp, natDegree_X, natDegree_pow, natDegree_pow, mul_left_comm,
    Nat.add_mul_mod_self_left]

end GlobalTheory
end

