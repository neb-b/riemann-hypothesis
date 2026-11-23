module

public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDimEqOne
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0011
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
public import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2518
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2257
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2372
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2509
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2446
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2463
public import Development.AbelianVarietyTheory.Definitions.Divisors.DivPowerCompatTwoFormDerivativeCompOneForm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0425
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsMatrixForm
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricallyIntegralIffGeometricallyConnectedOf

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteEtaleSubgroupSchemeOfGaloisStablePoi
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinEtSubgroup

variable {K : Type} [Field K]

theorem discreteTopology_of_isFinite (X : Over (Sp K)) [IsFinite X.hom] : DiscreteTopology X.left := by
  have : IsLocallyArtinian (Sp K) := inferInstanceAs (IsLocallyArtinian (Spec (CommRingCat.of K)))
  have : IsLocallyArtinian X.left := IsLocallyArtinian.of_locallyQuasiFinite X.hom
  infer_instance

theorem exists_pt_of_finiteEtale (X : Over (Sp K)) [IsFinite X.hom] [Etale X.hom] (x : X.left) :
    ∃ y : ptOver K (AlgebraicClosure K) ⟶ X, x ∈ Set.range y.left := by
  let Ω := AlgebraicClosure K
  let t : Sp Ω ⟶ Sp K := spMap (algebraMap K Ω)
  obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := X.hom) (g := t) x
    (IsLocalRing.closedPoint Ω) (Subsingleton.elim (α := PrimeSpectrum K) _ _)
  obtain ⟨s, hs, -, hx⟩ := (FinEt.isSplitOfRank_iff _ _).mp
    (FinEt.isSplitOfRank_of_isSepClosed (pullback.snd X.hom t) (pullback.snd X.hom t z))
  obtain ⟨i, w, hw⟩ := (hx z).exists
  refine ⟨Over.homMk (s i ≫ pullback.fst X.hom t) ?_, w, ?_⟩
  · change (s i ≫ pullback.fst X.hom t) ≫ X.hom = t
    rw [Category.assoc, pullback.condition, ← Category.assoc, hs, Category.id_comp]
  · change (s i ≫ pullback.fst X.hom t) w = x
    rw [Scheme.Hom.comp_apply, hw, hz]

theorem exists_gal_of_apply_eq (X : Over (Sp K)) (a b : ptOver K (AlgebraicClosure K) ⟶ X)
    (p : Sp (AlgebraicClosure K)) (h : a.left p = b.left p) :
    ∃ σ : AlgebraicClosure K ≃ₐ[K] AlgebraicClosure K, a = specAut σ ≫ b := by
  let Ω := AlgebraicClosure K
  obtain ⟨⟨q, φ⟩, ha⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective a.left
  obtain ⟨⟨q', ψ⟩, hb⟩ := (Scheme.SpecToEquivOfField Ω X.left).symm.surjective b.left
  simp only [Scheme.SpecToEquivOfField_symm_apply] at ha hb
  have hq : q = q' := by
    have h1 : (Spec.map φ ≫ X.left.fromSpecResidueField q) p =
        (Spec.map ψ ≫ X.left.fromSpecResidueField q') p := by rw [ha, hb]; exact h
    simpa only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply] using h1
  subst hq
  let c : CommRingCat.of K ⟶ X.left.residueField q := Spec.preimage (X.left.fromSpecResidueField q ≫ X.hom)
  have hc : Spec.map c = X.left.fromSpecResidueField q ≫ X.hom := Spec.map_preimage _
  have key : ∀ (χ : X.left.residueField q ⟶ CommRingCat.of Ω)
      (u : ptOver K Ω ⟶ X), Spec.map χ ≫ X.left.fromSpecResidueField q = u.left →
      c ≫ χ = CommRingCat.ofHom (algebraMap K Ω) := by
    intro χ u hu
    apply Spec.map_injective
    rw [Spec.map_comp, hc, ← Category.assoc, hu]
    exact Over.w u
  have hφ := key φ a ha
  have hψ := key ψ b hb
  letI : Algebra K (X.left.residueField q) := c.hom.toAlgebra
  letI : Algebra (X.left.residueField q) Ω := ψ.hom.toAlgebra
  haveI : IsScalarTower K (X.left.residueField q) Ω := IsScalarTower.of_algebraMap_eq fun x =>
    (congrArg (fun f => f.hom x) hψ).symm
  let φ' : X.left.residueField q →ₐ[K] Ω :=
    { φ.hom with commutes' := fun x => congrArg (fun f => f.hom x) hφ }
  let σ₀ : Ω →ₐ[K] Ω := φ'.liftNormal Ω
  have hσ₀ : ∀ x, σ₀ (ψ.hom x) = φ.hom x := fun x => φ'.liftNormal_commutes Ω x
  let σ : Ω ≃ₐ[K] Ω := AlgEquiv.ofBijective σ₀ (Algebra.IsAlgebraic.algHom_bijective σ₀)
  refine ⟨σ, Over.OverMorphism.ext ?_⟩
  change a.left = spMap (σ : Ω →+* Ω) ≫ b.left
  rw [← ha, ← hb, ← Category.assoc]
  congr 1
  rw [spMap, ← Spec.map_comp]
  congr 1
  ext x
  exact (hσ₀ x).symm

theorem exists_finiteEtale_subgroup_of_points : ∀ (K : Type) [Field K] (A : AbVar K) (G : Subgroup A.Pt), Finite G → ((Nat.card G : ℕ) : K) ≠ 0 → (∀ (σ : Gal K) (x : A.Pt), x ∈ G → galPts A.X σ x ∈ G) → ∃ (H : Over (Sp K)) (_ : GrpObj H) (i : H ⟶ A.X), IsMonHom i ∧ Mono i ∧ IsFinite H.hom ∧ Etale H.hom ∧ ∀ x : A.Pt, x ∈ G ↔ ∃ y, y ≫ i = x := by
  intro K _ A G _ hn hgal
  classical
  let Ω := AlgebraicClosure K
  let n := Nat.card G
  have hu : IsUnit (n : Γ(Sp K, ⊤)) := by
    simpa using (isUnit_iff_ne_zero.2 hn).map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  obtain ⟨-, hTf, hTe⟩ := GrpTangent.finiteEtale_mulN_torsion A.X (hG := A.ab) hu
  let T := torsion A.X n
  let ι₀ : T ⟶ A.X := torsion.ι A.X n
  have hι₀ : ι₀ ^ n = 1 := by
    rw [← GrpTangent.comp_mulN]
    refine pullback.condition.trans ?_
    rw [Hom.one_def]
    congr 1
    exact toUnit_unique _ _
  haveI : IsSplitMono η[A.X] := IsSplitMono.mk' ⟨toUnit _, toUnit_unique _ _⟩
  haveI : Mono ι₀ := inferInstanceAs (Mono (pullback.fst _ _))
  have hpow : ∀ x ∈ G, x ^ n = 1 := fun x hx =>
    congrArg Subtype.val (pow_card_eq_one' (G := G) (x := ⟨x, hx⟩))
  let lt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X), x ^ n = 1 → (S ⟶ T) := fun x hx =>
    pullback.lift x (toUnit _) (by rw [GrpTangent.comp_mulN, hx, Hom.one_def])
  have hlt : ∀ {S : Over (Sp K)} (x : S ⟶ A.X) (hx : x ^ n = 1), lt x hx ≫ ι₀ = x :=
    fun x hx => pullback.lift_fst _ _ _
  let U : Set T.left := {t | ∃ (x : A.Pt) (hx : x ∈ G) (p : Sp Ω), (lt x (hpow x hx)).left p = t}
  haveI := discreteTopology_of_isFinite T
  let V : T.left.Opens := ⟨U, isOpen_discrete U⟩
  let H : Over (Sp K) := Over.mk (V.ι ≫ T.hom)
  let j : H ⟶ T := Over.homMk V.ι rfl
  obtain ⟨ν, hνj⟩ : ∃ ν : H ⟶ A.X, ν = j ≫ ι₀ := ⟨_, rfl⟩
  haveI : IsClosedImmersion V.ι := .of_isPreimmersion _ (by
    rw [Scheme.Opens.range_ι]; exact isClosed_discrete _)
  haveI hHf : IsFinite H.hom := by change IsFinite (V.ι ≫ T.hom); infer_instance
  haveI hHe : Etale H.hom := by change Etale (V.ι ≫ T.hom); infer_instance
  haveI : Mono j := (Over.forget _).mono_of_mono_map (by change Mono V.ι; infer_instance)
  haveI : Mono ν := hνj ▸ mono_comp _ _
  have hν : ν ^ n = 1 := by
    rw [hνj, ← MonObj.comp_pow, hι₀, MonObj.comp_one]
  have lift : ∀ {S : Over (Sp K)} (f : S ⟶ A.X) (hf : f ^ n = 1),
      (∀ s : S.left, ∃ y : ptOver K Ω ⟶ S, s ∈ Set.range y.left) →
      (∀ y : ptOver K Ω ⟶ S, y ≫ f ∈ G) → ∃ g : S ⟶ H, g ≫ ν = f := by
    intro S f hf hS hG
    have hr : Set.range (lt f hf).left ⊆ Set.range V.ι := by
      rintro _ ⟨s, rfl⟩
      obtain ⟨y, p, rfl⟩ := hS s
      rw [Scheme.Opens.range_ι]
      have e : y ≫ lt f hf = lt (y ≫ f) (hpow _ (hG y)) := by
        rw [← cancel_mono ι₀, hlt (y ≫ f) (hpow _ (hG y)), Category.assoc, hlt f hf]
      refine ⟨y ≫ f, hG y, p, ?_⟩
      rw [← e]
      rfl
    let g : S ⟶ H := Over.homMk (IsOpenImmersion.lift V.ι (lt f hf).left hr) (by
      change IsOpenImmersion.lift V.ι (lt f hf).left hr ≫ V.ι ≫ T.hom = S.hom
      rw [← Category.assoc, IsOpenImmersion.lift_fac]
      exact Over.w _)
    have hg : g ≫ j = lt f hf := Over.OverMorphism.ext (IsOpenImmersion.lift_fac _ _ _)
    exact ⟨g, by rw [hνj, ← Category.assoc, hg, hlt f hf]⟩
  have hP : ∀ y : ptOver K Ω ⟶ H, y ≫ ν ∈ G := by
    intro y
    obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
    have hmem : (y ≫ j).left p ∈ U := by
      have h1 : V.ι (y.left p) ∈ Set.range V.ι := ⟨_, rfl⟩
      rw [Scheme.Opens.range_ι] at h1
      exact h1
    obtain ⟨x, hx, p', hp'⟩ := hmem
    rw [Subsingleton.elim p' p] at hp'
    obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq T (y ≫ j) (lt x (hpow x hx)) p hp'.symm
    have e : y ≫ ν = galPts A.X σ x := by
      show y ≫ ν = specAut σ ≫ x
      rw [hνj, ← Category.assoc, hσ, Category.assoc, hlt x (hpow x hx)]
    rw [e]
    exact hgal σ x hx

  have hone : η[A.X] = 1 := by
    rw [Hom.one_def, toUnit_unique (toUnit _) (𝟙 _), Category.id_comp]
  obtain ⟨e, he⟩ := lift η[A.X] (by rw [hone, one_pow])
    (fun s => ⟨toUnit _, by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      exact ⟨p, Subsingleton.elim (α := PrimeSpectrum K) _ _⟩⟩)
    (fun y => by
      have : y ≫ η[A.X] = 1 := by rw [Hom.one_def, toUnit_unique (toUnit _) y]
      rw [this]; exact one_mem G)
  have hmul : (ν ⊗ₘ ν) ≫ μ[A.X] = (fst H H ≫ ν) * (snd H H ≫ ν) := by
    rw [Hom.mul_def, ← lift_map, lift_fst_snd, Category.id_comp]
  haveI : IsFinite (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  haveI : Etale (H ⊗ H).hom := by rw [Over.tensorObj_hom]; infer_instance
  have hν' : ∀ {S : Over (Sp K)} (g : S ⟶ H), (g ≫ ν) ^ n = 1 := fun g => by
    rw [← MonObj.comp_pow ν n g, hν, MonObj.comp_one]
  obtain ⟨m, hm⟩ := lift ((ν ⊗ₘ ν) ≫ μ[A.X])
    (by rw [hmul, mul_pow, hν' (fst H H), hν' (snd H H), _root_.one_mul])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [hmul, MonObj.comp_mul, ← Category.assoc, ← Category.assoc]
      exact mul_mem (hP (y ≫ fst H H)) (hP (y ≫ snd H H)))
  obtain ⟨i, hi⟩ := lift (ν ≫ ι[A.X]) (by rw [← Hom.inv_def, inv_pow, hν, inv_one])
    (exists_pt_of_finiteEtale _)
    (fun y => by
      rw [← Hom.inv_def, GrpObj.comp_inv]
      exact inv_mem (hP y))
  obtain ⟨gH, hνH⟩ := ReducedSubgroup.exists_grpObj_of_mono ν e m i he hm hi
  refine ⟨H, gH, ν, hνH, inferInstance, hHf, hHe, fun x => ⟨fun hx => ?_, ?_⟩⟩
  · obtain ⟨g, hg⟩ := lift x (hpow x hx) (fun s => ⟨𝟙 _, s, rfl⟩) (fun y => by
      obtain ⟨p⟩ : Nonempty (Sp Ω) := inferInstance
      obtain ⟨σ, hσ⟩ := exists_gal_of_apply_eq (ptOver K Ω) y (𝟙 _) p
        (Subsingleton.elim (α := PrimeSpectrum Ω) _ _)
      rw [hσ, Category.comp_id]
      exact hgal σ x hx)
    exact ⟨g, hg⟩
  · rintro ⟨y, rfl⟩
    exact hP y

end GlobalTheory.FinEtSubgroup
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteExtensionMumfordBundlePolarisation
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.MumDesc


set_option maxHeartbeats 1000000 in
theorem exists_polAV_field : ∀ (K : Type) [Field K] [CharZero K] (A : Over (Sp K)) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ PP : LB (G2 A).left, PP.IsLB → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 2) ![(lift (snd A A) (fst A A) : G2 A ⟶ G2 A).left, 𝟙 (G2 A).left] ![1, -1]), u.IsGen) → (∃ u : LB.Gen (LB.LinComb PP (K := Fin 3) ![(lift (fst A (A ⊗ A) * (snd A (A ⊗ A) ≫ fst A A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (lift (fst A (A ⊗ A)) (snd A (A ⊗ A) ≫ snd A A) : A ⊗ (A ⊗ A) ⟶ G2 A).left, (snd A (A ⊗ A) : A ⊗ (A ⊗ A) ⟶ G2 A).left] ![1, -1, -1]), u.IsGen) → Out.RelAmple A (PP.pull (lift (𝟙 A) (𝟙 A) : A ⟶ G2 A).left) → (∀ (T : Over (Sp K)) (x : T ⟶ A), (∃ t : LB.Gen (PP.pull (lift (snd A T ≫ x) (fst A T) : A ⊗ T ⟶ G2 A).left), t.IsGen) → x = toUnit T ≫ η[A]) → ∃ (E : Type) (_ : Field E) (_ : Algebra K E), FiniteDimensional K E ∧ IsGalois K E ∧ ∃ (A₁ : PolAV (Sp E)) (gen : (Over.pullback (spMap (algebraMap K E))).obj A ≅ A₁.A), IsMonHom gen.hom ∧ ∀ κ : (G2 ((Over.pullback (spMap (algebraMap K E))).obj A)).left ⟶ (G2 A).left, Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K E))) κ → LBIso (abelian₂ ((Over.pullback (spMap (algebraMap K E))).obj A) (A₁.L.pull gen.hom.left)) (PP.pull κ) := by
  intro K _ _ A _ _ hA PP hPP hs ha hm hk
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap K (AlgebraicClosure K)))).obj A)).left ⟶ (G2 A).left,
      Geo.Tor.IsSquare (pullback.fst A.hom (spMap (algebraMap K (AlgebraicClosure K)))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare (isGrpPullback_pullback A _).1.w⟩
  obtain ⟨L, hL, hS, hI, hM, hT⟩ := GlobalTheory.T.exists_principalPolarisation_mumfordBundle_algClosure K A hA PP hPP hs ha hm hk (AlgebraicClosure K) κ hκ
  exact _root_.GlobalTheory.MumDescent.exists_galois_polAV K A hA PP hPP (AlgebraicClosure K) κ hκ L hL hS hI hM hT


set_option maxHeartbeats 1000000 in
theorem exists_extLam_finExt : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsAbelianScheme ((Over.pullback (jK R)).obj G) → ∀ PP : LB (G2 G).left, PP.IsLB → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 2) ![(lift (snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) (fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : G2 ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, 𝟙 (G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∃ u : LB.Gen (LB.LinComb (PP.pull κ₀) (K := Fin 3) ![(lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) * (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ fst ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (lift (fst ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G))) (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ≫ snd ((Over.pullback (jK R)).obj G) ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left, (snd ((Over.pullback (jK R)).obj G) (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⊗ (((Over.pullback (jK R)).obj G) ⊗ ((Over.pullback (jK R)).obj G)) ⟶ G2 ((Over.pullback (jK R)).obj G)).left] ![1, -1, -1]), u.IsGen) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → Out.RelAmple ((Over.pullback (jK R)).obj G) ((PP.pull κ₀).pull (lift (𝟙 ((Over.pullback (jK R)).obj G)) (𝟙 ((Over.pullback (jK R)).obj G)) : ((Over.pullback (jK R)).obj G) ⟶ G2 ((Over.pullback (jK R)).obj G)).left)) → (∀ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left, Geo.Tor.IsSquare (G' := ((Over.pullback (jK R)).obj G)) (G := G) (pullback.fst G.hom (jK R)) κ₀ → ∀ (T : Over (Sp (FractionRing R))) (x : T ⟶ ((Over.pullback (jK R)).obj G)), (∃ t : LB.Gen ((PP.pull κ₀).pull (lift (snd ((Over.pullback (jK R)).obj G) T ≫ x) (fst ((Over.pullback (jK R)).obj G) T) : ((Over.pullback (jK R)).obj G) ⊗ T ⟶ G2 ((Over.pullback (jK R)).obj G)).left), t.IsGen) → x = toUnit T ≫ η[((Over.pullback (jK R)).obj G)]) → ∃ (R' : Type) (_ : CommRing R') (_ : IsDomain R') (_ : IsLocalRing R') (ρ : R →+* R') (G₁ : Over (Sp R')) (_ : GrpObj G₁) (_ : IsCommMonObj G₁) (β : G₁.left ⟶ G.left) (β₂ : (G2 G₁).left ⟶ (G2 G).left) (A₁ : PolAV (Sp (FractionRing R'))) (gen₁ : (Over.pullback (jK R')).obj G₁ ≅ A₁.A), FinExt ρ ∧ IsGrpPullback G₁ G (spMap ρ) β ∧ Geo.Tor.IsSquare β β₂ ∧ IsMonHom gen₁.hom ∧ ExtLam G₁ (A₁.L.pull gen₁.hom.left) (PP.pull β₂) := by
  intro R _ _ _ hR G _ _ hab PP hPP hsym hadd hamp hker
  have hp := isGrpPullback_pullback G (jK R)
  obtain ⟨κ₀, hκ₀⟩ : ∃ κ₀ : (G2 ((Over.pullback (jK R)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (jK R)) κ₀ := ⟨_, GlobalTheory.LamPull.exists_isSquare hp.1.w⟩
  haveI : CharZero R := hR.2
  haveI : CharZero (FractionRing R) :=
    charZero_of_injective_algebraMap (IsFractionRing.injective R (FractionRing R))
  obtain ⟨E, _, _, hfd, hgal, A₁, gen, hgen, hLam⟩ :=
    exists_polAV_field (FractionRing R) ((Over.pullback (jK R)).obj G) hab (PP.pull κ₀) (pull_isLB hPP κ₀)
      (hsym κ₀ hκ₀) (hadd κ₀ hκ₀) (hamp κ₀ hκ₀) (hker κ₀ hκ₀)
  obtain ⟨R', _, _, _, ρ, t, hρ, ht⟩ := _root_.GlobalTheory.GalClosure.exists_finExt_fractionRing_of_galois R hR E hfd hgal
  haveI := hgen
  have hsq : (spMap t) ≫ (spMap (algebraMap (FractionRing R) E)) ≫ jK R = jK R' ≫ spMap ρ := by
    simp only [jK, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    exact ht r
  have hE := isGrpPullback_pullback ((Over.pullback (jK R)).obj G) (spMap (algebraMap (FractionRing R) E))
  have hβ := isGrpPullback_pullback G (spMap ρ)
  have hp₁ := isGrpPullback_pullback ((Over.pullback (spMap ρ)).obj G) (jK R')
  have hc := (hp₁.comp hβ).congr hsq.symm rfl
  have hAEG := hE.comp hp
  have w1 : (pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ)) ≫ G.hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) ≫ (spMap (algebraMap (FractionRing R) E))) ≫ jK R := by
    simpa only [Category.assoc] using hc.1.w
  let a : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (jK R)).obj G).left := pullback.lift _ _ w1
  have w2 : a ≫ ((Over.pullback (jK R)).obj G).hom =
      (((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t)) ≫ (spMap (algebraMap (FractionRing R) E)) := by
    exact (pullback.lift_snd _ _ w1).trans (Category.assoc _ _ _).symm
  let φ₁ : ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).left ⟶
      ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).left := pullback.lift _ _ w2
  have hφ₁fst : φ₁ ≫ pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E)) ≫ pullback.fst G.hom (jK R) =
      pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ) := by
    simp only [φ₁, a, pullback.lift_fst_assoc, pullback.lift_fst]
  have hφ₁w : φ₁ ≫ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)).hom =
      ((Over.pullback (jK R')).obj ((Over.pullback (spMap ρ)).obj G)).hom ≫ (spMap t) := pullback.lift_snd _ _ _
  have hφ := hAEG.cancel (hc.congr rfl hφ₁fst.symm) hφ₁w
  obtain ⟨hL, -, -, -, -⟩ := GlobalTheory.firstFiveLaws
  obtain ⟨A₀, g, hg, hgL⟩ := GlobalTheory.ArcDataDescent.exists_polPull hL.polBaseChange (spMap t) A₁
  have h1 := (hφ.comp (isGrpPullback_of_iso gen)).congr (Category.comp_id _) rfl
  obtain ⟨e, he, heg⟩ := grpPullback_iso h1 hg
  obtain ⟨β₂, hβ₂⟩ : ∃ β₂ : (G2 ((Over.pullback (spMap ρ)).obj G)).left ⟶ (G2 G).left,
      Geo.Tor.IsSquare (pullback.fst G.hom (spMap ρ)) β₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hβ.1.w⟩
  refine ⟨R', inferInstance, inferInstance, inferInstance, ρ, (Over.pullback (spMap ρ)).obj G, inferInstance, inferInstance,
    pullback.fst G.hom (spMap ρ), β₂, A₀, e, ?_, ?_, ?_, ?_, ?_⟩
  · exact hρ
  · exact hβ
  · exact hβ₂
  · exact he
  refine ⟨pull_isLB hPP β₂, fun κ₂' hκ₂' => ?_⟩
  have hL1 : (A₁.L.pull gen.hom.left).IsLB := pull_isLB A₁.isLB _
  have hL0 : (A₀.L.pull e.hom.left).IsLB := pull_isLB A₀.isLB _
  have hNL : LBIso (A₀.L.pull e.hom.left) ((A₁.L.pull gen.hom.left).pull φ₁) :=
    LBIso.trans hL0 (pull_isLB A₁.isLB _) (pull_isLB hL1 φ₁)
      (GlobalTheory.ArcDataDescent.lbIso_pull hgL e.hom.left heg.symm)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull A₁.isLB gen.hom.left φ₁ rfl).symm
  obtain ⟨φ₂, hφ₂⟩ : ∃ φ₂, Geo.Tor.IsSquare φ₁ φ₂ := ⟨_, GlobalTheory.LamPull.exists_isSquare hφ.1.w⟩
  have h₁ := GlobalTheory.LamPull.lbIso_lam_pull hφ hL1 hL0 hNL hφ₂
  obtain ⟨κ, hκ⟩ : ∃ κ : (G2 ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G))).left ⟶ (G2 ((Over.pullback (jK R)).obj G)).left, Geo.Tor.IsSquare (pullback.fst ((Over.pullback (jK R)).obj G).hom (spMap (algebraMap (FractionRing R) E))) κ :=
    ⟨_, GlobalTheory.LamPull.exists_isSquare hE.1.w⟩
  have hΛ : (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left)).IsLB :=
    DVR.linComb_isLB _ hL1 _ _
  have hLK : LBIso (abelian₂ ((Over.pullback (spMap (algebraMap (FractionRing R) E))).obj ((Over.pullback (jK R)).obj G)) (A₁.L.pull gen.hom.left))
      (PP.pull (κ ≫ κ₀)) :=
    LBIso.trans hΛ (pull_isLB (pull_isLB hPP _) κ) (pull_isLB hPP _) (hLam κ hκ)
      (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP κ₀ κ rfl)
  have h₂ := GlobalTheory.ArcDataDescent.lbIso_pull hLK φ₂ (ψ := φ₂ ≫ κ ≫ κ₀) rfl
  have hsq2 : φ₂ ≫ κ ≫ κ₀ = κ₂' ≫ β₂ := by
    apply GlobalTheory.LamPull.isSquare_unique
      (φ := pullback.fst ((Over.pullback (spMap ρ)).obj G).hom (jK R') ≫ pullback.fst G.hom (spMap ρ))
    · constructor
      · simp only [Category.assoc, hκ₀.1, reassoc_of% hκ.1, reassoc_of% hφ₂.1, hφ₁fst]
      · simp only [Category.assoc, hκ₀.2, reassoc_of% hκ.2, reassoc_of% hφ₂.2, hφ₁fst]
    · constructor
      · simp only [Category.assoc, hβ₂.1, reassoc_of% hκ₂'.1]
      · simp only [Category.assoc, hβ₂.2, reassoc_of% hκ₂'.2]
  rw [hsq2] at h₂
  have h₃ : LBIso (PP.pull (κ₂' ≫ β₂)) ((PP.pull β₂).pull κ₂') :=
    (GlobalTheory.ArcDataDescent.lbIso_pull_pull hPP β₂ κ₂' rfl).symm
  exact LBIso.trans (DVR.linComb_isLB _ hL0 _ _) (pull_isLB hΛ φ₂) (pull_isLB (pull_isLB hPP β₂) κ₂') h₁
    (LBIso.trans (pull_isLB hΛ φ₂) (pull_isLB hPP _) (pull_isLB (pull_isLB hPP β₂) κ₂') h₂ h₃)

end GlobalTheory.MumDesc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteModificationIntegralElementsRegular
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.Mum

theorem exists_finSub_of_isIntegralElem : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens)
    (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) →
    (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) →
    ∃ F : ∀ V : M.S.Opens, Subring Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ V), IsFinSub M.gp F ∧ ∀ m, b m ∈ F (U m) := by
  classical
  intro R _ _ _ M n U b hU hb
  haveI := M.proper
  haveI : IsLocallyNoetherian M.S := LocallyOfFiniteType.isLocallyNoetherian M.π
  haveI : CompactSpace M.S := QuasiCompact.compactSpace_of_compactSpace M.π
  haveI : M.S.IsSeparated := ⟨by rw [← terminal.comp_from M.π]; infer_instance⟩

  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun V : M.S.affineOpens => (V.1 : Set M.S))
    (fun V => V.1.isOpen) (by
      intro x _
      obtain ⟨_, ⟨V, hV, rfl⟩, hx, -⟩ := M.S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
      exact Set.mem_iUnion.2 ⟨⟨V, hV⟩, hx⟩)
  let r := s.card
  let Vc : Fin r → M.S.Opens := fun i => (s.equivFin.symm i).1.1
  have hVa : ∀ i, IsAffineOpen (Vc i) := fun i => (s.equivFin.symm i).1.2
  have hcov : (⨆ i, Vc i) = ⊤ := by
    refine eq_top_iff.2 fun x _ => ?_
    obtain ⟨V, hV, hx⟩ := Set.mem_iUnion₂.1 (hs (Set.mem_univ x))
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨s.equivFin ⟨V, hV⟩, by simpa [Vc] using hx⟩
  have hloc : ∀ (i : Fin r) (m : Fin n), ∃ t : Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i),
      (∀ y ∈ t, (M.gp.app (Vc i)).hom.IsIntegralElem y) ∧
      resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m) (b m) ∈ Subring.closure (Set.range (M.gp.app (U m ⊓ Vc i)).hom ∪
        resK M.gp (inf_le_right : U m ⊓ Vc i ≤ Vc i) '' (t : Set _)) := by
    intro i m
    refine _root_.GlobalTheory.Mum.mem_closure_of_isIntegralElem_affine_le M.gp (Vc i) (U m ⊓ Vc i) inf_le_right (hVa i) ((hU m).inf (hVa i)) _ ?_
    obtain ⟨p, hp, hpe⟩ := hb m
    refine ⟨p.map (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom, hp.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    have hc : (M.gp.app (U m ⊓ Vc i)).hom.comp (M.S.presheaf.map (homOfLE (inf_le_left : U m ⊓ Vc i ≤ U m)).op).hom =
        (resK M.gp (inf_le_left : U m ⊓ Vc i ≤ U m)).comp (M.gp.app (U m)).hom := by
      ext a; exact (resK_app M.gp _ a).symm
    rw [hc, ← Polynomial.hom_eval₂, hpe, map_zero]
  choose t ht hbt using hloc
  let T : ∀ i, Finset Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ Vc i) := fun i => Finset.univ.biUnion (t i)
  refine ⟨finFam M.gp Vc T, ⟨fun V _ a => finFam_range _ _ _ _ a, fun V V' hle _ _ x hx => finFam_res _ _ _ V V' hle x hx,
    fun V hV f x hx => _root_.GlobalTheory.Mum.finFam_basicOpen_loc M.gp Vc T V hV f x hx, fun V hV => _root_.GlobalTheory.Mum.finFam_finite M.gp Vc T hcov ?_ V hV⟩, ?_⟩
  · intro i y hy
    obtain ⟨m, -, hm⟩ := Finset.mem_biUnion.1 (show y ∈ Finset.univ.biUnion (t i) from hy)
    exact ht i m y hm
  · intro m
    rw [mem_finFam]
    intro i
    refine Subring.closure_mono ?_ (hbt i m)
    rintro _ (h | ⟨z, hz, rfl⟩)
    · exact Or.inl h
    · exact Or.inr ⟨z, show z ∈ Finset.univ.biUnion (t i) from Finset.mem_biUnion.2 ⟨m, Finset.mem_univ _, hz⟩, rfl⟩

theorem finiteModif_regular : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (M : Modif R) (n : ℕ) (U : Fin n → M.S.Opens) (b : ∀ m, Γ(Sp (FractionRing R), M.gp ⁻¹ᵁ U m)), (∀ m, IsAffineOpen (U m)) → (∀ m, (M.gp.app (U m)).hom.IsIntegralElem (b m)) → ∃ (M' : Modif R) (h : M'.S ⟶ M.S) (hgp : M'.gp ≫ h = M.gp), IsFinite h ∧ h ≫ M.π = M'.π ∧ ∀ m, ∃ c : Γ(M'.S, h ⁻¹ᵁ U m), (M'.gp.appLE (h ⁻¹ᵁ U m) (M.gp ⁻¹ᵁ U m) (le_preimage_of_comp_eq M.gp M'.gp h hgp (U m))).hom c = b m := by
  intro R _ _ _ M n U b hU hb
  obtain ⟨F, hF, hbF⟩ := exists_finSub_of_isIntegralElem R M n U b hU hb
  haveI : IsIntegral M.S := M.integral
  haveI : IsDominant M.gp := M.dominant
  obtain ⟨S', h, gp', hgp, hfin, hint, hdom, hsec⟩ := _root_.GlobalTheory.Mum.exists_finite_of_isFinSub M.gp F hF
  haveI := M.proper
  let M' : Modif R :=
    { S := S', π := h ≫ M.π, proper := inferInstance, integral := hint, gp := gp',
      gp_π := by rw [← Category.assoc, hgp, M.gp_π], dominant := hdom }
  exact ⟨M', h, hgp, hfin, rfl, fun m => hsec (U m) (hU m) (b m) (hbF m)⟩

end GlobalTheory.Mum
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFreeThickeningLevelFinitelyManyElements
section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry KaehlerDifferential DividedPowers ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
  GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR GlobalTheory.CxCoh GlobalTheory.PDA GlobalTheory.PDForm GlobalTheory.SmoothLift

namespace GlobalTheory.PDForm.FreeFin

variable {R : Type} [CommRing R] {I : Ideal R} {κ : DividedPowers I} {X : Scheme.{0}} {t : X ⟶ Sp R}

theorem isFree_id (n : ℕ) (T : Thick κ t) (hT : IsLev T.δ n) :
    IsFree n (𝟙 T) (Fin.elim0 : Fin 0 → T.B) := by
  refine ⟨hT, fun i ↦ i.elim0, fun S _ a c _ ↦ ⟨a, ⟨Category.id_comp a, fun i ↦ i.elim0⟩, ?_⟩⟩
  rintro g ⟨hg, -⟩
  rw [← hg, Category.id_comp]

theorem isFree_cons (n m : ℕ) {T F F' : Thick κ t} (u : T ⟶ F) (τ : Fin m → F.B) (hu : IsFree n u τ)
    (u' : F ⟶ F') (τ' : Unit → F'.B) (hu' : IsFree n u' τ') :
    IsFree n (u ≫ u') (Fin.cons (τ' ()) (fun i ↦ u'.φ (τ i)) : Fin (m + 1) → F'.B) := by
  obtain ⟨-, hτ, hU⟩ := hu
  obtain ⟨hF', hτ', hU'⟩ := hu'
  refine ⟨hF', fun i ↦ Fin.cases (hτ' ()) (fun j ↦ Thick.Hom.mem u' (hτ j)) i, ?_⟩
  intro S hS a c hc
  obtain ⟨g₁, ⟨hg₁a, hg₁c⟩, hg₁u⟩ := hU S hS a (fun j ↦ c j.succ) (fun j ↦ hc j.succ)
  obtain ⟨g, ⟨hga, hgc⟩, hgu⟩ := hU' S hS g₁ (fun _ ↦ c 0) (fun _ ↦ hc 0)
  refine ⟨g, ⟨?_, fun i ↦ ?_⟩, ?_⟩
  · rw [Category.assoc, hga, hg₁a]
  · refine Fin.cases ?_ (fun j ↦ ?_) i
    · simpa using hgc ()
    · simp only [Fin.cons_succ]
      rw [← Thick.comp_φ, hga, hg₁c]
  · rintro g' ⟨hg'a, hg'c⟩
    have h1 : u' ≫ g' = g₁ := by
      refine hg₁u _ ⟨by rw [← Category.assoc, hg'a], fun j ↦ ?_⟩
      have := hg'c j.succ
      simp only [Fin.cons_succ] at this
      rw [Thick.comp_φ, this]
    refine hgu _ ⟨h1, fun _ ↦ ?_⟩
    simpa using hg'c 0

theorem exists_free : ∀ (R : Type) [CommRing R] (I : Ideal R) (κ : DividedPowers I) (X : Scheme.{0})
    (t : X ⟶ Sp R) (n m : ℕ) (T : Thick κ t), IsLev T.δ (n + 1) →
    ∃ (F : Thick κ t) (u : T ⟶ F) (τ : Fin m → F.B), IsFree (n + 1) u τ ∧ (KK κ t).QAt u := by
  intro R _ I κ X t n m T hT
  induction m with
  | zero => exact ⟨T, 𝟙 T, Fin.elim0, isFree_id _ T hT, QAtFormal.qAt_ident _ T⟩
  | succ m ih =>
    obtain ⟨F, u, τ, hu, hq⟩ := ih
    obtain ⟨F', u', τ', hu', hq'⟩ := _root_.GlobalTheory.PDForm.exists_isFree_one_qAt R I κ X t n F hu.1
    exact ⟨F', u ≫ u', _, isFree_cons (n + 1) m u τ hu u' τ' hu', QAtFormal.qAt_comp _ u u' hq hq'⟩

end GlobalTheory.PDForm.FreeFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLiftOfEtaleSurjective
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.HTLat GlobalTheory.Published.AbVarRed GlobalTheory.CechPic GlobalTheory.AV GlobalTheory.AV.AbVar
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem exists_lift_of_etale_surjective : ∀ (K : Type) [Field K] [IsAlgClosed K] (X Y : Scheme.{0}) (π : Y ⟶ X), Etale π → Surjective π → ∀ x : Sp K ⟶ X, ∃ y : Sp K ⟶ Y, y ≫ π = x := by
  intro K _ _ X Y π hE hS x
  haveI := hE
  haveI := hS
  have : LocallyOfFiniteType π := inferInstance
  let t : Sp K := IsLocalRing.closedPoint K
  obtain ⟨w, hw⟩ := π.surjective (x t)
  obtain ⟨y, -, -⟩ := Scheme.Pullback.exists_preimage_pullback w t hw
  have : JacobsonSpace ↥(pullback π x) := LocallyOfFiniteType.jacobsonSpace (pullback.snd π x)
  obtain ⟨y', -, hy'⟩ := nonempty_inter_closedPoints (Z := (Set.univ : Set ↥(pullback π x)))
    ⟨y, trivial⟩ isOpen_univ.isLocallyClosed
  have hc : IsClosed {y'} := hy'
  refine ⟨pointOfClosedPoint (pullback.snd π x) y' hc ≫ pullback.fst π x, ?_⟩
  rw [Category.assoc, pullback.condition, pointOfClosedPoint_comp_assoc]

end GlobalTheory
end

