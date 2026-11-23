module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.ChainOfKernelsUnique
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsIsoIffBijectiveOverAlgClosed
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0019
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ConstPullback
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1304
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1346
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1354
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsProbabilityMeasureAutQuotientNormalized
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.MeasurableSetSatFrames
public import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.Bundle0030
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0466
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0739
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0486
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0499
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1231
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1340
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1310

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiberEqCardSectionsMulLength
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FinSchemeRank

theorem length_self_eq_of_ringEquiv {R S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    Module.length R R = Module.length S S := by
  letI : Algebra R S := e.toRingHom.toAlgebra
  let f : R ≃ₗ[R] S :=
    { e with map_smul' := fun r x => by simp [Algebra.smul_def, RingHom.algebraMap_toAlgebra] }
  rw [f.length_eq]
  exact Module.length_eq_of_surjective (S := R) (R := S) (M := S) e.surjective

theorem finrank_eq_length_of_isLocalRing (k : Type*) [Field k] [IsAlgClosed k] (A : Type*) [CommRing A]
    [IsLocalRing A] [Algebra k A] [Module.Finite k A] :
    (Module.finrank k A : ℕ∞) = Module.length A A := by
  haveI : IsLocalHom (algebraMap k A) :=
    ⟨fun a ha => isUnit_iff_ne_zero.mpr fun h => by simp [h] at ha⟩
  haveI : Module.Finite k (IsLocalRing.ResidueField A) :=
    Module.Finite.of_surjective (IsScalarTower.toAlgHom k A (IsLocalRing.ResidueField A)).toLinearMap
      IsLocalRing.residue_surjective
  have hb : Function.Bijective (algebraMap k (IsLocalRing.ResidueField A)) :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral
  have h1 : Module.length k (IsLocalRing.ResidueField A) = 1 := by
    rw [Module.length_eq_finrank,
      ← (AlgEquiv.ofBijective (Algebra.ofId k _) hb).toLinearEquiv.finrank_eq, Module.finrank_self]
    rfl
  rw [← Module.length_eq_finrank, IsLocalRing.length_restrictScalars k A A,
    ← Module.length_eq_of_surjective (S := k) (R := IsLocalRing.ResidueField k)
      (M := IsLocalRing.ResidueField A) IsLocalRing.residue_surjective, h1, _root_.mul_one]

theorem finrank_eq_card_mul (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [Algebra k B]
    [Module.Finite k B] (m : ℕ∞)
    (hm : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m) :
    (Module.finrank k B : ℕ∞) = Nat.card (PrimeSpectrum B) * m := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  letI := Fintype.ofFinite (PrimeSpectrum B)
  have h : ∀ p : PrimeSpectrum B, (Module.finrank k (Localization.AtPrime p.asIdeal) : ℕ∞) = m := by
    intro p
    haveI : Module.Finite k (Localization.AtPrime p.asIdeal) :=
      Module.Finite.of_surjective (Algebra.algHom k B (Localization.AtPrime p.asIdeal)).toLinearMap
        (IsArtinianRing.localization_surjective p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal))
    rw [← hm p, finrank_eq_length_of_isLocalRing k]
  rw [IsArtinianRing.finrank_eq_sum_primeSpectrum B k, Nat.cast_sum]
  simp only [h, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]

theorem card_algHom_eq_card_primeSpectrum (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B]
    [Algebra k B] [Module.Finite k B] :
    Nat.card (B →ₐ[k] k) = Nat.card (PrimeSpectrum B) := by
  haveI : IsArtinianRing B := IsArtinianRing.of_finite k B
  let F : (B →ₐ[k] k) → PrimeSpectrum B := fun φ => ⟨RingHom.ker φ, RingHom.ker_isPrime _⟩
  refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
  · intro φ ψ h
    have h' : RingHom.ker φ = RingHom.ker ψ := congrArg PrimeSpectrum.asIdeal h
    ext b
    have : b - algebraMap k B (φ b) ∈ RingHom.ker φ := by simp [RingHom.mem_ker]
    rw [h', RingHom.mem_ker, map_sub, AlgHom.commutes, sub_eq_zero] at this
    exact this.symm
  · intro p
    haveI : p.asIdeal.IsMaximal := Ideal.isMaximal_of_isPrime p.asIdeal
    letI : Field (B ⧸ p.asIdeal) := Ideal.Quotient.field _
    have hb : Function.Bijective (algebraMap k (B ⧸ p.asIdeal)) :=
      IsAlgClosed.algebraMap_bijective_of_isIntegral
    let e := AlgEquiv.ofBijective (Algebra.ofId k (B ⧸ p.asIdeal)) hb
    refine ⟨(e.symm : (B ⧸ p.asIdeal) →ₐ[k] k).comp (Ideal.Quotient.mkₐ k p.asIdeal), ?_⟩
    ext x
    change x ∈ RingHom.ker _ ↔ x ∈ p.asIdeal
    simp [RingHom.mem_ker, Ideal.Quotient.eq_zero_iff_mem]

theorem finrank_eq_card_sections_mul : ∀ (k : Type) [Field k] [IsAlgClosed k] (P : Scheme.{0}) (q : P ⟶ Sp k),
    IsFinite q → ∀ (m : ℕ∞), (∀ x : P, Module.length (P.presheaf.stalk x) (P.presheaf.stalk x) = m) →
    ∀ z : Sp k, (q.finrank z : ℕ∞) = (Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} : ℕ∞) * m := by
  intro k _ _ P q hq m hm z
  haveI := hq
  haveI : IsAffine P := isAffine_of_isAffineHom q
  let B : Type := Γ(P, ⊤)
  letI : Algebra k B := ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ q.appTop).hom.toAlgebra
  let q' : Spec (CommRingCat.of B) ⟶ Sp k := Spec.map (CommRingCat.ofHom (algebraMap k B))
  have hq1 : P.isoSpec.hom ≫ q' = q := GlobalTheory.IwLevel.FiberCard.isoSpec_hom_specMap_appTop' q
  have hq2 : q' = P.isoSpec.inv ≫ q := by rw [← hq1, Iso.inv_hom_id_assoc]
  haveI : IsFinite q' := by rw [hq2]; infer_instance
  haveI : Module.Finite k B :=
    RingHom.finite_algebraMap.mp ((IsFinite.SpecMap_iff _).mp (inferInstanceAs (IsFinite q')))
  haveI : Flat q' := Flat.SpecMap_iff.mpr (RingHom.flat_algebraMap_iff.mpr inferInstance)
  haveI : Flat q := by rw [← hq1]; infer_instance
  have hrk : q.finrank z = Module.finrank k B := by
    rw [← hq1, Scheme.Hom.finrank_comp_left_of_isIso]
    refine (Scheme.Hom.finrank_SpecMap_algebraMap k B z).trans ?_
    rw [Module.rankAtStalk_eq_finrank_of_free]
    rfl
  have hsec : Nat.card {s : Sp k ⟶ P // s ≫ q = 𝟙 _} = Nat.card (B →ₐ[k] k) := by
    let F : {s : Sp k ⟶ P // s ≫ q = 𝟙 _} → (B →ₐ[k] k) := fun s =>
      { (Spec.preimage (s.1 ≫ P.isoSpec.hom)).hom with
        commutes' := fun c => by
          have h : CommRingCat.ofHom (algebraMap k B) ≫ Spec.preimage (s.1 ≫ P.isoSpec.hom) = 𝟙 _ := by
            apply Spec.map_injective
            rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, Category.assoc]
            exact (congrArg (s.1 ≫ ·) hq1).trans s.2
          exact congrArg (fun u => u.hom c) h }
    refine Nat.card_congr (Equiv.ofBijective F ⟨?_, ?_⟩)
    · intro s₁ s₂ h
      apply Subtype.ext
      have h1 : Spec.preimage (s₁.1 ≫ P.isoSpec.hom) = Spec.preimage (s₂.1 ≫ P.isoSpec.hom) := by
        ext c
        exact congrArg (fun u : B →ₐ[k] k => u c) h
      have h2 := congrArg Spec.map h1
      rw [Spec.map_preimage, Spec.map_preimage] at h2
      simpa using congrArg (· ≫ P.isoSpec.inv) h2
    · intro φ
      let s : Sp k ⟶ P := Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ P.isoSpec.inv
      have hs' : s ≫ P.isoSpec.hom = Spec.map (CommRingCat.ofHom φ.toRingHom) := by simp [s]
      have hs : s ≫ q = 𝟙 _ := by
        rw [← hq1, ← Category.assoc, hs', ← Spec.map_comp, ← Spec.map_id]
        congr 1
        ext c
        exact φ.commutes c
      refine ⟨⟨s, hs⟩, ?_⟩
      ext b
      change (Spec.preimage (s ≫ P.isoSpec.hom)).hom b = φ b
      rw [hs', Spec.preimage_map]
      rfl
  have hstalk : ∀ p : PrimeSpectrum B,
      Module.length (Localization.AtPrime p.asIdeal) (Localization.AtPrime p.asIdeal) = m := by
    intro p
    have hU := isAffineOpen_top P
    have hp : hU.fromSpec p ∈ (⊤ : P.Opens) := by simp
    letI : Algebra B (P.presheaf.stalk (hU.fromSpec p)) :=
      TopCat.Presheaf.algebra_section_stalk P.presheaf ⟨hU.fromSpec p, hp⟩
    haveI : IsLocalization p.asIdeal.primeCompl (P.presheaf.stalk (hU.fromSpec p)) :=
      hU.isLocalization_stalk' p hp
    rw [← hm (hU.fromSpec p)]
    exact length_self_eq_of_ringEquiv (IsLocalization.algEquiv p.asIdeal.primeCompl
      (Localization.AtPrime p.asIdeal) (P.presheaf.stalk (hU.fromSpec p))).toRingEquiv
  rw [hrk, hsec, card_algHom_eq_card_primeSpectrum k B]
  exact finrank_eq_card_mul k B m hstalk

end GlobalTheory.FinSchemeRank
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankFiniteFlatTorsionSubschemeEqCardPoints
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionRank

theorem etale_pullback_snd {S : Scheme.{0}} (A : Over S) [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) (K : Over S) (i : K ⟶ A) (c : ℕ) [Mono i] [IsFinite K.hom]
    [Flat K.hom] (hi : i ^ c = 1) (k : Type) [Field k] (hc : (c : k) ≠ 0) (y : Sp k ⟶ S) :
    Etale (pullback.snd K.hom y) := by
  let A' := (Over.pullback y).obj A
  let K' := (Over.pullback y).obj K
  let i' : K' ⟶ A' := (Over.pullback y).map i
  have hA' : IsAbelianScheme A' := Out.TLinPf.isAb_pullback y A hA
  have := hA'.comm
  have := hA'.smooth
  have hc' : IsUnit (c : Γ(Sp k, ⊤)) := by
    have := (Ne.isUnit hc).map (Scheme.ΓSpecIso (CommRingCat.of k)).inv.hom
    simpa using this
  have hTe : Etale (torsion A' c).hom := GrpTangent.etale_torsion A' hc'
  have hi' : i' ^ c = 1 := by
    have h := map_pow (Over.pullback y).homMonoidHom i c
    rw [hi, map_one] at h
    exact h.symm
  obtain ⟨j, hj, -⟩ := GlobalTheory.LatticeTorsion.existsUnique_torsion A' c i' hi'
  have : Mono i' := inferInstance
  have hjm : Mono j := mono_of_mono_fac hj
  have hjml : Mono j.left := inferInstanceAs (Mono ((Over.forget _).map j))
  have hju : FormallyUnramified j.left := inferInstance
  have hKu : FormallyUnramified K'.hom := by
    rw [← Over.w j]
    exact MorphismProperty.comp_mem @FormallyUnramified _ _ hju inferInstance
  have : Flat K'.hom := by change Flat (pullback.snd K.hom y); infer_instance
  have : IsFinite K'.hom := by change IsFinite (pullback.snd K.hom y); infer_instance
  have : LocallyOfFinitePresentation K'.hom := inferInstance
  exact Etale.of_formallyUnramified_of_flat K'.hom

theorem finrank_eq_card : ∀ (S : Scheme.{0}) (A : Over S) [GrpObj A] [IsCommMonObj A], IsAbelianScheme A → ∀ (K : Over S) (i : K ⟶ A) (c : ℕ), Mono i → IsFinite K.hom → Flat K.hom → i ^ c = 1 → ∀ (k : Type) [Field k] [IsAlgClosed k], (c : k) ≠ 0 → ∀ (y : Sp k ⟶ S) (z : Sp k), K.hom.finrank (y z) = Nat.card (Over.mk y ⟶ K) := by
  intro S A _ _ hA K i c hi hfin hfl hic k _ _ hc y z
  have het := etale_pullback_snd A hA K i c hic k hc y
  obtain ⟨-, hcard⟩ := GlobalTheory.FinEt.card_points_eq_finrank (pullback.snd K.hom y) (𝟙 (Sp k)) z
  have hz : (𝟙 (Sp k) : Sp k ⟶ Sp k) z = z := rfl
  rw [hz, Scheme.Hom.finrank_pullback_snd] at hcard
  rw [← hcard]
  refine Nat.card_congr
    { toFun := fun x => Over.homMk (x.1 ≫ pullback.fst K.hom y) (by
        change (x.1 ≫ pullback.fst K.hom y) ≫ K.hom = y
        rw [Category.assoc, pullback.condition, ← Category.assoc, x.2, Category.id_comp])
      invFun := fun g => ⟨pullback.lift g.left (𝟙 _) (by
        rw [Category.id_comp]; exact Over.w g), pullback.lift_snd _ _ _⟩
      left_inv := fun x => Subtype.ext (pullback.hom_ext (pullback.lift_fst _ _ _)
        ((pullback.lift_snd _ _ _).trans x.2.symm))
      right_inv := fun g => Over.OverMorphism.ext (pullback.lift_fst _ _ _) }

end GlobalTheory.TorsionRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FixPartEqBotOfLt
section
noncomputable section

namespace GlobalTheory.IndLine

open NumberField GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def IsKFix (B : Base F E) (om : Rep σ Y W) (f : SInf F (Fin n × Fin d)) : Prop :=
  ∀ k ∈ KInf σ Y B.emb, Acts (evI F) (om (k, 1)) f f

def fixPart (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (m : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Submodule.span ℂ {f | f ∈ fockDeg M B.ψ B.emb m ∧ IsKFix B om f}

def fixDeg (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) : ℕ :=
  sInf {m | ∃ f ∈ fockDeg M B.ψ B.emb m, f ≠ 0 ∧ IsKFix B om f}

def KStabUp (B : Base F E) (om : Rep σ Y W) (H : Submodule ℂ (SInf F (Fin n × Fin d))) : Prop :=
  ∀ k ∈ KInf σ W B.emb, ∀ f ∈ H, ∀ f₁ : SInf F (Fin n × Fin d), Acts (evI F) (om (1, k)) f f₁ → f₁ ∈ H

theorem fixPart_le_pol (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) (m : ℕ) :
    fixPart B M om m ≤ M.Pol B.ψ B.emb :=
  Submodule.span_le.2 fun _ hf => fockDeg_le_pol M B.ψ B.emb m hf.1

theorem fixPart_eq_bot_of_lt (B : Base F E) (M : Model σ Y W) (om : Rep σ Y W) {m : ℕ} (hm : m < fixDeg B M om) :
    fixPart B M om m = ⊥ := by
  rw [fixPart, Submodule.span_eq_bot]
  intro f hf
  by_contra h
  exact Nat.notMem_of_lt_sInf hm ⟨f, hf.1, h, hf.2⟩

end GlobalTheory.IndLine
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagQuotientIntegralEqUniversalConstMul
section
open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates GlobalTheory.LevGeo GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume
open scoped ENNReal

namespace GlobalTheory.FlagQuotHaar

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem haarChart_exists (X : Data E r) : ∃ c : ℝ≥0∞, c ≠ 0 ∧ c ≠ ⊤ ∧ HaarChart X c := GlobalTheory.T.exists_haarIntegral_eq_unitriangularChart X

theorem haar_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) (φ : Frame X'.Ψ r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ g, φ (trF X X' e (frameOf X g)) ∂haarR X = ∫⁻ g, φ (frameOf X' g) ∂haarR X' := _root_.GlobalTheory.FlagQuotHaar.lintegral_trF_frameOf X X' e hp φ hφ

theorem muF_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) (φ : Frame X'.Ψ r → ℝ≥0∞) (hφ : Measurable φ) :
    ∫⁻ z, φ (trF X X' e (cpt X (baseFr X) z)) ∂muF X (baseFr X) =
      ∫⁻ z, φ (cpt X' (baseFr X') z) ∂muF X' (baseFr X') := GlobalTheory.T.lintegral_transportHermitianFrame_chartMeasure X X' e hp φ hφ

theorem test_exists (X : Data E r) : ∃ φ : Frame X.Ψ r → ℝ≥0∞, Measurable φ ∧
    (∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (rmul x b) = φ x) ∧
    ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ 0 ∧ ∫⁻ z, φ (cpt X (baseFr X) z) ∂muF X (baseFr X) ≠ ⊤ :=
  _root_.GlobalTheory.FlagQuotHaar.TestFn.exists_invariant_test X

theorem isFundamentalDomain_sat (X : Data E r) {c : ℝ≥0∞} (hc : HaarChart X c) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) (Λ : Subgroup (RealGrp X))
    (hΛ : ∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) :
    IsFundamentalDomain Λ (frameOf X ⁻¹' GlobalTheory.Unfold.satFrames X x0 FF) (haarR X) := _root_.GlobalTheory.FundFrames.isFundamentalDomain_satFrames X hc ho hF Λ hΛ

theorem trF_rmul {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (y b : Frame X.Ψ r) :
    trF X X' e (rmul y b) = rmul (trF X X' e y) (fun τ' => b (e.symm τ')) := by
  funext τ'
  show (mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * (mat y (e.symm τ') * mat b (e.symm τ')) :
      Matrix (Fin r) (Fin r) ℂ) =
    mat (baseFr X') τ' * (mat (baseFr X) (e.symm τ'))⁻¹ * mat y (e.symm τ') * mat b (e.symm τ')
  simp only [Matrix.mul_assoc]

theorem continuous_trF {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) : Continuous (trF X X' e) := by
  refine continuous_pi fun τ' => ?_
  have hM : Continuous fun y : Frame X.Ψ r => mat y (e.symm τ') := continuous_apply _
  exact continuous_const.matrix_mul hM

theorem trF_mem_dom {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (e : X.Ψ ≃ X'.Ψ) (hp : X.p0 = X'.p0) {y : Frame X.Ψ r} (hy : y ∈ X.dom) : trF X X' e y ∈ X'.dom := by
  intro τ'
  set τ := e.symm τ'
  have hb := GlobalTheory.PeterssonCompare.det_baseFr X τ
  have hb' := GlobalTheory.PeterssonCompare.det_baseFr X' τ'
  set M : Matrix (Fin r) (Fin r) ℂ := (mat (baseFr X) τ)⁻¹ * mat y τ
  have hy' : mat y τ = mat (baseFr X) τ * M := (Matrix.mul_nonsing_inv_cancel_left _ _ hb.isUnit).symm
  have ht : mat (trF X X' e y) τ' = mat (baseFr X') τ' * M := by
    show mat (baseFr X') τ' * (mat (baseFr X) τ)⁻¹ * mat y τ = mat (baseFr X') τ' * ((mat (baseFr X) τ)⁻¹ * mat y τ)
    rw [Matrix.mul_assoc]
  have hg : gram τ'.1 X'.Gm (mat (trF X X' e y) τ') = gram τ.1 X.Gm (mat y τ) := by
    rw [ht, hy', FrameDegreeData.gram_mul, FrameDegreeData.gram_mul, baseFr_mem X τ, baseFr_mem X' τ', hp]
  refine ⟨?_, fun i => ?_⟩
  · rw [ht, Matrix.det_mul]
    refine mul_ne_zero hb' ?_
    intro h0
    apply (hy τ).1
    rw [hy', Matrix.det_mul, h0, mul_zero]
  · have := (hy τ).2 i
    unfold dmin at this ⊢
    rw [hg, ← hp]
    exact this

theorem haarChart_unique {E' : Type} [Field E'] [NumberField E'] [IsCMField E'] (X : Data E r) (X' : Data E' r)
    (hp : X.p0 = X'.p0) (hn : X.Ψ.card = X'.Ψ.card) {c c' : ℝ≥0∞} (hc : HaarChart X c) (hc' : HaarChart X' c') :
    c = c' := by
  have e : X.Ψ ≃ X'.Ψ := Fintype.equivOfCardEq (by simpa using hn)
  obtain ⟨φ, hφm, hφB, h0, htop⟩ := test_exists X'
  have hm : Measurable (fun y => φ (trF X X' e y)) := hφm.comp (continuous_trF X X' e).measurable
  have hB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, φ (trF X X' e (rmul x b)) = φ (trF X X' e x) := by
    intro x hx b hb
    rw [trF_rmul]
    exact hφB _ (trF_mem_dom X X' e hp hx) _ fun τ' => hb (e.symm τ')
  have h1 := hc _ hm hB
  rw [haar_trF X X' e hp φ hφm, hc' φ hφm hφB, muF_trF X X' e hp φ hφm] at h1
  exact ((ENNReal.mul_left_inj h0 htop).1 h1).symm

theorem countable_image (X : Data E r) {Λ : Subgroup (RealGrp X)}
    (hΛ : ∀ s, s ∈ Λ ↔ ∃ γ ∈ X.Γ, lact γ (baseFr X) = frameOf X s) : Countable Λ := by
  haveI := FundSetPf.countable_GL (E := E) (r := r)
  choose f hf using fun s : Λ => (hΛ s.1).1 s.2
  refine Function.Injective.countable (f := f) fun s t h => Subtype.ext ?_
  apply GlobalTheory.PeterssonCompare.frameOf_injective X
  rw [← (hf s).2, ← (hf t).2, h]

theorem quotInt_eq_of_haarChart (X : Data E r) {c : ℝ≥0∞} (hc : HaarChart X c) {x0 : Frame X.Ψ r}
    (ho : IsOrth X x0) {FF : Set (V (nd X))} (hF : IsFundSet X x0 FF) {Φ : Frame X.Ψ r → ℝ≥0∞}
    (hΦ : Measurable Φ) (hΓ : ∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x)
    (hB : ∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) :
    quotInt X Φ = c * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  classical
  obtain ⟨Λ, hΛ, -⟩ := GlobalTheory.ArithImage.exists_discrete_image E r X
  haveI := countable_image X hΛ
  set S := GlobalTheory.Unfold.satFrames X x0 FF
  have hS : MeasurableSet S := GlobalTheory.Unfold.measurableSet_satFrames X ho hF.1 hF.2.1
  rw [GlobalTheory.PeterssonCompare.quotInt_eq X hΛ (isFundamentalDomain_sat X hc ho hF Λ hΛ) hΓ]
  have hpre : MeasurableSet (frameOf X ⁻¹' S) := GlobalTheory.PeterssonCompare.measurable_frameOf X hS
  rw [← lintegral_indicator hpre]
  have e1 : (frameOf X ⁻¹' S).indicator (fun g => Φ (frameOf X g)) = fun g => S.indicator Φ (frameOf X g) := by
    funext g; by_cases h : frameOf X g ∈ S <;> simp [h]
  have hIB : ∀ x ∈ X.dom, ∀ b ∈ Bor X.Ψ r, S.indicator Φ (rmul x b) = S.indicator Φ x := by
    intro x hx b hb
    rw [Set.indicator_apply, Set.indicator_apply, GlobalTheory.Unfold.rmul_mem_satFrames_iff X x0 FF x hb, hB b hb x hx]
  have hbo : IsOrth X (baseFr X) := fun τ => baseFr_mem X τ
  rw [e1, hc _ (hΦ.indicator hS) hIB,
    GlobalTheory.FrameMeasureClosed.measInv_holds r X (baseFr X) x0 hbo ho _ (hΦ.indicator hS) hIB,
    ← lintegral_indicator hF.1]
  congr 1
  refine lintegral_congr fun z => ?_
  rw [Set.indicator_apply, Set.indicator_apply, GlobalTheory.Unfold.cpt_mem_satFrames_iff X ho]

end

end GlobalTheory.FlagQuotHaar

open GlobalTheory.FlagQuotHaar in
theorem GlobalTheory.FlagQuotHaar.quotInt_eq_const_mul : ∀ (r p0 n : ℕ), ∃ κ : ℝ≥0∞, κ ≠ 0 ∧ κ ≠ ⊤ ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (X : Data E r), X.p0 = p0 → X.Ψ.card = n → ∀ (x0 : Frame X.Ψ r) (FF : Set (V (nd X))) (Φ : Frame X.Ψ r → ℝ≥0∞), IsOrth X x0 → IsFundSet X x0 FF → Measurable Φ → (∀ γ ∈ X.Γ, ∀ x ∈ X.dom, Φ (lact γ x) = Φ x) → (∀ b ∈ Bor X.Ψ r, ∀ x ∈ X.dom, Φ (rmul x b) = Φ x) → GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHaarVolume.quotInt X Φ = κ * ∫⁻ z in FF, Φ (cpt X x0 z) ∂(muF X x0) := by
  intro r p0 n
  by_cases h : ∃ (E : Type) (_ : Field E) (_ : NumberField E) (_ : IsCMField E) (X : Data E r),
      X.p0 = p0 ∧ X.Ψ.card = n
  · obtain ⟨E₁, _, _, _, X₁, hp₁, hn₁⟩ := h
    obtain ⟨c₁, h0, htop, hc₁⟩ := haarChart_exists X₁
    refine ⟨c₁, h0, htop, fun E _ _ _ X hp hn x0 FF Φ ho hF hΦ hΓ hB => ?_⟩
    obtain ⟨c, -, -, hc⟩ := haarChart_exists X
    rw [quotInt_eq_of_haarChart X hc ho hF hΦ hΓ hB,
      haarChart_unique X X₁ (hp.trans hp₁.symm) (hn.trans hn₁.symm) hc hc₁]
  · refine ⟨1, one_ne_zero, ENNReal.one_ne_top, fun E _ _ _ X hp hn => ?_⟩
    exact absurd ⟨E, inferInstance, inferInstance, inferInstance, X, hp, hn⟩ h
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfFiniteFlatGeometricFibresOverBase
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped NumberField CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem flat_of_isFinite_of_flat_geometric_fibres_over :
    ∀ (S : Scheme.{0}) (X Y : Over S) (f : X ⟶ Y), Flat X.hom → LocallyOfFinitePresentation X.hom →
    LocallyOfFinitePresentation Y.hom → IsFinite f.left →
    (∀ (k : Type) [Field k] [IsAlgClosed k] (t : Sp k ⟶ S), Flat ((Over.pullback t).map f).left) →
    Flat f.left :=
  fun S X Y f h1 h0 h2 h3 H =>
    flat_of_isFinite_of_finitePresentation_of_flat_geometric_fibres S X Y f h1 h0 h2 h3 H

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockVacuumEquationsInArchimedeanDarbouxCoordinatStatement
section
open scoped TensorProduct Matrix GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift GlobalTheory.VacLn
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.fockVacuumEquations_in_archimedeanDarbouxCoordinates : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (α β κ : Type) [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ] (P Q R S : ℕ)
    (τ : ∀ w : InfinitePlace F, EmbOver E w) (JA : Matrix α α (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (JB : Matrix β β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)))
    (d : Darboux (symp (R := AF F) (cA σ) (-1) JA JB) κ) (a b : ℂ) (A : InfinitePlace F → Matrix α (Ix P Q) ℂ)
    (C : InfinitePlace F → Matrix β (Ix R S) ℂ) (ε : InfinitePlace F → ℤˣ), IsCMExt F E σ → Framed τ JA JB a b A C →
    ∃ (J e : ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)) →ₗ[ℝ]
        ((κ → mixedEmbedding.mixedSpace F) × (κ → mixedEmbedding.mixedSpace F)))
      (e' : (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F)),
      (∀ y, J (J y) = -y) ∧ (∀ y, e (e y) = e y) ∧ (∀ y, J (e y) = e (J y)) ∧ (∀ y, (e y).1 = e' y.1) ∧
      (∀ y x, trPair F κ x (e y).2 = trPair F κ (e' x) y.2) ∧
      ∀ y, ∃ (u u' u₁ : Matrix α β (_root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))) (c : InfinitePlace F → Matrix (Ix P Q) (Ix R S) ℂ),
        At (evI F) u ∧ At (evI F) u' ∧ At (evI F) u₁ ∧ (∀ w, u.map (piInf (τ w)) = A w * c w * (C w)ᵀ) ∧
        (∀ w, u'.map (piInf (τ w)) = A w * ((((ε w : ℤ) : ℂ) * Complex.I) • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        (∀ w, u₁.map (piInf (τ w)) = A w * (Complex.I • (Jm P Q * c w * Jm R S)) * (C w)ᵀ) ∧
        coord d u = y ∧ coord d u' = J (y - (2 : ℝ) • e y) ∧ coord d u₁ = J y := by
  first | exact @GlobalTheory.VacBridge.exists_bridge | exact GlobalTheory.VacBridge.exists_bridge | (intros; apply GlobalTheory.VacBridge.exists_bridge <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeisenbergMatrixMulStatement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.UnipMass
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.heisenberg_matrix_mul : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), (∀ a, σ (σ a) = a) → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), (∀ i j, σ (J j i) = -J i j) → ∀ (x u u' : Fin n → _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)) (c c' : _root_.GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E)), hA σ J x x = 0 → hA σ J u x = 0 → hA σ J u' x = 0 → nmat σ J x u c * nmat σ J x u' c' = nmat σ J x (u + u') (c + c' - hA σ J u' u) := by
  first | exact @GlobalTheory.UnipMass.nmat_mul_nmat | exact GlobalTheory.UnipMass.nmat_mul_nmat | (intros; apply GlobalTheory.UnipMass.nmat_mul_nmat <;> assumption)
end

