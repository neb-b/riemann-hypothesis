module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsPrincipalMapOfAlgHom
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0043
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0032
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0361
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0398
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0201
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.IsOpenOfMemIrreducibleComponentsOfFinite
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramesExist
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0028
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0585
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0583
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UnifPreCharacterGroupIso
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0492
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.UniformisationTrivialisationsCorrespond
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0582
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0576
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0579
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEqAddOfRedVEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0566

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostPlacesRayField
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.Host GlobalTheory.EX GlobalTheory.EX.OB GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.Top.Bl

theorem hostPins_wpt : GlobalTheory.NT.RayField → ∀ (𝒮 : Slots) (K : Ctx) (q : WPt 𝒮 K), GlobalTheory.Mem.HD.HostPins (q.w.D q.Z) q.O.ex.nch := by
  intro hR 𝒮 K q
  obtain ⟨B, f, T, w, Z, O, x⟩ := q
  have hmu := x.what₂.mu
  have key := GlobalTheory.Mem.Top.TupTieW.tupTied_of_muIsW (w.st Z) f T x.Wt w.I.xi hmu
  have hδ : w.δ.ray ≤ B.KsC := w.exact.lower.1
  have hQ : ∀ v ∈ x.Wt, O.ex.nch.Q v = T.Q v := fun v hv => (x.n.Q v hv).1
  refine ⟨fun u i => (w.D Z).T_ne_g u i, ?_, fun v hv v' hv' u => ?_, B.galLL, GlobalTheory.Mem.HD.exists_hilbert_le_O hR B w.δ hδ⟩
  · exact key.2.1.subset fun v hv => (key.1 v).1 hv
  · have hvW := (key.1 v).1 hv
    rw [hQ v hvW] at hv'
    have e : ((w.D Z).mem u).A.T = B.T u := (w.st Z).C.A_T u
    have hp : (B.T u).Prime := e ▸ ((w.D Z).mem u).A.T_prime
    rw [e]
    exact GlobalTheory.Mem.HD.twistConductor_not_over_levelPrimes B T v hv' u hp

end GlobalTheory.Mem.Top.Bl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIntegralAppOfUniversallyClosed
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

noncomputable section

namespace GlobalTheory.GenPush

theorem isIntegral_of_isIso_comp {A B C D : CommRingCat.{0}} (k : A ⟶ B) (f : B ⟶ C) (m : C ⟶ D) [IsIso k]
    [IsIso m] (h : (k ≫ f ≫ m).hom.IsIntegral) : f.hom.IsIntegral := by
  have e : f = inv k ≫ (k ≫ f ≫ m) ≫ inv m := by simp
  rw [e, CommRingCat.hom_comp, CommRingCat.hom_comp]
  refine RingHom.IsIntegral.trans _ _ ?_ (RingHom.IsIntegral.trans _ _ h ?_)
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv k)).2
  · exact RingHom.isIntegral_of_surjective _ (ConcreteCategory.bijective_of_isIso (inv m)).2

theorem isIntegral_app_of_universallyClosed {Z₁ Z₂ : Scheme.{0}} (ρ : Z₁ ⟶ Z₂) [UniversallyClosed ρ]
    (U : Z₂.Opens) (hU : IsAffineOpen U) : (ρ.app U).hom.IsIntegral := by
  have : IsAffine U.toScheme := hU
  have h := isIntegral_appTop_of_universallyClosed (ρ ∣_ U)
  rw [morphismRestrict_appTop] at h
  have e : U.ι ''ᵁ ⊤ = U := by simp
  rw [ρ.app_eq e, Category.assoc, Category.assoc, ← Functor.map_comp] at h
  simp only [eqToHom_op, eqToHom_map, eqToHom_trans] at h
  have hi : ∀ {A B : CommRingCat.{0}} (p : A = B), IsIso (eqToHom p) := fun p => by
    subst p; rw [eqToHom_refl]; infer_instance
  refine @isIntegral_of_isIso_comp _ _ _ _ _ _ _ ?_ ?_ h
  · exact hi _
  · exact hi _

theorem exists_app_eq_of_isIntegralElem {T Z : Scheme.{0}} [GlobalTheory.IsNormalScheme Z] [IsLocallyNoetherian Z]
    (j : T ⟶ Z) [IsOpenImmersion j] (hj : Dense (Set.range j)) (U : Z.Opens)
    (s : Γ(T, j ⁻¹ᵁ U)) (hs : (j.app U).hom.IsIntegralElem s) : ∃ h : Γ(Z, U), j.app U h = s :=
  _root_.GlobalTheory.glue_of_dense_openImmersion j hj U s fun u hu => _root_.GlobalTheory.exists_section_of_isIntegralElem_of_isOpenImmersion j hj U s hs u hu

section Models

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H}
  {Xo : Moduli D l} {c : Coeff l}

end Models

end GlobalTheory.GenPush
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsMonHomOfSquaredDegenerationDataFunctionalEquat
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.LN GlobalTheory
open MonoidalCategory CartesianMonoidalCategory MonObj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PsiFourth

theorem key : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], IsCN R → ∀ (D D' : DegData R (maximalIdeal R)), ∀ (Φ : D'.toPre.P.A ≅ D.toPre.P.A) (w : LB.Iso (LB.LinComb D'.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D'.toPre.P.A.left) (fun _ => 2)) ((LB.LinComb D.toPre.P.L (K := Fin 1) (fun _ => 𝟙 D.toPre.P.A.left) (fun _ => 2)).pull Φ.hom.left)), w.IsGen → IsMonHom Φ.hom → ∀ xe : D'.toPre.X ≃+ D.toPre.X, (∀ x : D'.toPre.X, D'.toPre.c (2 • x) ≫ Φ.hom = D.toPre.c (xe (2 • x))) → ∀ (f : ∀ α : D.toPre.X, D.toPre.SecB 2 α) (f' : ∀ α : D'.toPre.X, D'.toPre.SecB 2 α), (∀ (mu α : D.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D.toPre.P.A) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → sval (f (α + 2 • mu)) y.left z J = sval (f α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (mu α : D'.toPre.X) (T : Over (Sp R)) (κ : T ⟶ TF (R := R) (FractionRing R)) (y : T ⟶ D'.toPre.P.A) (z : T.left) (J : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D'.toPre.P.L z J → sval (f' (α + 2 • mu)) y.left z J = sval (f' α) (y * ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre T mu).left z J * (ReciprocityTheory.ChartRestriction.G.DVR.uVal D'.toPre (FractionRing R) 2 α (ReciprocityTheory.ChartRestriction.G.DVR.cP D'.toPre _ mu) (CartesianMonoidalCategory.lift κ y) z J * val (DegPre.famMult D'.toPre (FractionRing R) 2 mu α) κ.left z J).val) → (∀ (β : D'.toPre.X) (Z : Scheme.{0}) (ρ : Z ⟶ D'.toPre.P.A.left) (z : Z) (J : (Z ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (Z ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → sval (f (xe (2 • β))) (ρ ≫ Φ.hom.left) z J ^ 2 = (∏ κ, ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) (ρ ≫ D'.toPre.famφB (2 • β) κ) ^ DegPre.famε 2 κ).val * sval (f' (2 • β)) ρ z J' ^ 2) → (∀ (T : Over (Sp R)) (z : T.left) (J : (T.left ⟶ D.toPre.P.A.left) → D.toPre.P.L.ι) (J' : (T.left ⟶ D'.toPre.P.A.left) → D'.toPre.P.L.ι), Geo.Tor.Good D.toPre.P.L z J → Geo.Tor.Good D'.toPre.P.L z J' → ∀ (Ω : (T ⟶ D'.toPre.P.A) → (T.left.presheaf.stalk z)ˣ), Ω = (fun x => ExpTrans.om w z (fun q _ => J q) (fun q _ => J' q) x.left) → ∀ (a b c : T ⟶ D'.toPre.P.A), cubV D.toPre.cub z J (a ≫ Φ.hom) (b ≫ Φ.hom) (c ≫ Φ.hom) ^ 2 = Ω (a * b * c) * (Ω (a * b))⁻¹ * (Ω (a * c))⁻¹ * (Ω (b * c))⁻¹ * Ω a * Ω b * Ω c * (Ω 1)⁻¹ * cubV D'.toPre.cub z J' a b c ^ 2) → (¬ ∀ j, (f 0).f j = 0) → ∀ (y : D'.toPre.X) (r r' : R), PsiCoord D.toPre (xe (2 • y)) r → PsiCoord D'.toPre (2 • y) r' → Associated (r ^ 4) (r' ^ 4) := by
  intro R _ _ _ hR D D' Φ w hw hΦ xe hc f f' hf hf' hcorr hcub hne y r r' hr hr'
  have := D.toPre.P.isAb.smooth
  have := D.toPre.P.isAb.geomConnected
  haveI : IsIntegral (DegPre.BF D.toPre (FractionRing R)).left :=
    (geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres D.toPre.P.A.hom).geometrically_isIntegral
      (TF (R := R) (FractionRing R)).hom _ _ (IsPullback.of_hasPullback _ D.toPre.P.A.hom).flip
  have ne : ∀ J, Geo.Tor.Good D.toPre.P.L (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J →
      sval (f 0) (DegPre.prB D.toPre (FractionRing R)).left (genericPoint (DegPre.BF D.toPre (FractionRing R)).left) J ≠ 0 := by
    intro J hJ h0
    apply hne
    have hL := D.toPre.P.isLB
    have inj := PullIntegral.prB_app_injective D.toPre (FractionRing R)
    have e₀ := ThetaScalar.eq_zero_of_germ (H1.SectionArithmetic.pullSec (f 0) (DegPre.prB D.toPre (FractionRing R)).left) _ hJ
      (by rw [H1.SectionArithmetic.sval_pullSec _ _ _ _ hJ, Category.id_comp, h0])
    exact fun j => PullIntegral.sec_ext_of_inj hL _ inj (s' := ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero) (fun y J hJ => by
      have := ThetaScalar.sval_eq_zero _ e₀ (𝟙 _) y hJ
      rw [H1.SectionArithmetic.sval_pullSec _ _ _ y hJ] at this
      rw [this]
      exact (ThetaScalar.sval_eq_zero ReciprocityTheory.ChartRestriction.G.DVR.SecOps.secZero (fun _ => rfl) _ y hJ).symm) j
  exact GlobalTheory.T.psi_coordinates_fourthPower_associated R D D' Φ w hw (xe (2 • y)) (2 • y) _
    (fun J J' hJ hJ' => GlobalTheory.T.weightTwoFactor_sq_values_correspond R D D' Φ w hΦ xe hc f f' hf hf' hcorr hcub y _ J J' hJ hJ'
      inferInstance (ne J hJ)) r r' hr hr'

end GlobalTheory.PsiFourth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictFaceOfSmoothConePolyhedralFan
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.FaceStrict

theorem exists_retract_balForms : ∀ (O : Type) [CommRing O] [Module.Finite ℤ O] (bar : O → O) (X : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X], ∃ ρ : LinearMap.BilinForm ℤ X →ₗ[ℤ] balForms bar X, ∀ β : balForms bar X, ρ β = β := by
  intro O _ _ bar X _ _ _
  classical
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, π, hπ⟩ := Module.Finite.exists_fin' ℤ X
  let P : LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    { toFun := fun β => β.compl₁₂ π π, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  have hP : Function.Injective P := fun β β' h => by
    ext a b
    obtain ⟨a, rfl⟩ := hπ a
    obtain ⟨b, rfl⟩ := hπ b
    exact LinearMap.congr_fun₂ h a b
  haveI : Module.Finite ℤ (LinearMap.BilinForm ℤ X) := Module.Finite.of_injective P hP
  haveI : NoZeroSMulDivisors ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := by
    refine ⟨fun {k x} hkx => ?_⟩
    obtain ⟨β, rfl⟩ := Submodule.mkQ_surjective _ x
    rw [Submodule.mkQ_apply, ← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hkx
    by_cases hk : k = 0
    · exact Or.inl hk
    right
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    obtain ⟨h1, h2⟩ := hkx
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · have := h1 y z
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hk this
    · have := h2 a y z
      simp only [LinearMap.smul_apply, smul_eq_mul] at this
      exact mul_left_cancel₀ hk this
  haveI : Module.Free ℤ (LinearMap.BilinForm ℤ X ⧸ balForms bar X) := Module.free_of_finite_type_torsion_free'
  obtain ⟨σ, hσ⟩ := Module.projective_lifting_property (balForms bar X).mkQ LinearMap.id (Submodule.mkQ_surjective _)
  have hmem : ∀ x, (LinearMap.id - σ ∘ₗ (balForms bar X).mkQ :
      LinearMap.BilinForm ℤ X →ₗ[ℤ] LinearMap.BilinForm ℤ X) x ∈ balForms bar X := by
    intro x
    rw [← Submodule.Quotient.mk_eq_zero]
    have := LinearMap.congr_fun hσ ((balForms bar X).mkQ x)
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at this
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, Submodule.Quotient.mk_sub]
    rw [← Submodule.mkQ_apply (balForms bar X) (σ _), this]
    exact sub_self _
  refine ⟨(LinearMap.id - σ ∘ₗ (balForms bar X).mkQ).codRestrict (balForms bar X) hmem, fun β => ?_⟩
  · apply Subtype.ext
    simp only [LinearMap.codRestrict_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply,
      Submodule.mkQ_apply, (Submodule.Quotient.mk_eq_zero _).2 β.2, map_zero, sub_zero]

theorem exists_decomp_bounded : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X →
    ∃ b : ℝ, ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → ∃ (n : ℕ) (u : Fin n → LinearMap.BilinForm ℤ X) (c : Fin n → ℝ),
      (∀ i, u i ∈ balForms bar X) ∧ (∀ i y, 0 ≤ u i y y) ∧ (∀ i, φ.evalZ (u i) ≤ b) ∧ (∀ i, 0 ≤ c i) ∧
      toReal β = ∑ i, c i • toReal (u i) ∧ φ.evalZ β = ∑ i, c i * φ.evalZ (u i) := by
  intro O _ _ _ _ bar φ X _ _ _ hP
  classical
  obtain ⟨S, hS, hcov⟩ := hP.finite
  refine ⟨∑ x ∈ hS.toFinset, |φ.evalZ x|, fun β hβ hp => ?_⟩
  have hR : toReal β ∈ psdCone (bar := bar) (X := X) := by
    simpa using ConeSub.sum_smul_toReal_mem_psdCone O bar X 1 ![β] ![1] (fun i => by fin_cases i; simpa using hβ)
      (fun i y => by fin_cases i; simpa using hp y) (fun i => by fin_cases i; simp)
  obtain ⟨e, n, γ', c, hcell, hS', hc, he⟩ := hcov _ hR
  refine ⟨n, fun i => pull e.symm.toLinearMap (γ' i), c, fun i => pull_mem _ (hcell.mem i),
    fun i y => hcell.nonneg i _, fun i => ?_, hc, ?_, ?_⟩
  · rw [evalZ_pull φ e.symm.surjective]
    exact (le_abs_self _).trans (Finset.single_le_sum (f := fun x => |φ.evalZ x|) (fun x _ => abs_nonneg _)
      (hS.mem_toFinset.2 (hS' i)))
  · ext a b
    have := LinearMap.congr_fun₂ he (e.symm a) (e.symm b)
    simpa [LinearMap.sum_apply] using this
  · rw [← evalR_toReal, ← evalR_pullR φ (r := e.toLinearMap) e.surjective, he,
      (linearOn_iff φ γ').1 hcell.linear c hc]
    simp [evalZ_pull φ e.symm.surjective]

theorem isStrict_face_of_isCone : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O)
    (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X], IsPolyFanOn bar φ X → Dominates bar X →
    ∀ (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (s : Fin m' ↪ Fin m), IsCone bar φ γ →
    IsStrict bar φ fun i => γ (s i) := by
  intro O _ _ _ _ bar φ X _ _ _ hP hD m m' γ s hγ
  classical
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  obtain ⟨ρ, hρ⟩ := exists_retract_balForms O bar X
  obtain ⟨ψ, hψ⟩ := hγ.basis.exists_dual
  set T : Finset (Fin m) := Finset.univ.filter fun i => i ∉ Set.range s with hT
  set h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ := (∑ i ∈ T, ψ i) ∘ₗ ρ with hh
  have hγh : ∀ i, h (γ i) = if i ∈ T then 1 else 0 := fun i => by
    have e : ρ (γ i) = ⟨γ i, hγ.mem i⟩ := hρ ⟨γ i, hγ.mem i⟩
    simp only [hh, LinearMap.comp_apply, e, LinearMap.sum_apply, hψ]
    simp
  have hpos : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 → 0 < ℓ β := fun β hβ hp h0 => by
    have e1 := h2 β hβ hp
    have e2 := hP.pos β hβ hp h0
    have e3 : (0 : ℝ) < N := by exact_mod_cast hN
    have : (0 : ℝ) < ℓ β := lt_of_lt_of_le (mul_pos e3 e2) e1
    exact_mod_cast this
  obtain ⟨C, hC⟩ := hD ℓ (-h) hpos
  obtain ⟨b, hb⟩ := exists_decomp_bounded O bar φ X hP
  set B : ℕ := ⌈b⌉₊ with hB
  set K : ℕ := C + C * N * B + 1 with hK
  have cell : ∀ u ∈ balForms bar X, (∀ y, 0 ≤ u y y) → φ.evalZ u ≤ b →
      0 ≤ (K : ℝ) * ((ℓ u : ℝ) - N * φ.evalZ u) + h u ∧
      ((K : ℝ) * ((ℓ u : ℝ) - N * φ.evalZ u) + h u = 0 → (ℓ u : ℝ) = N * φ.evalZ u ∧ h u = 0) := by
    intro u hu hp hub
    obtain ⟨n, hn⟩ := hP.integral u hu hp
    have hle : (N : ℝ) * φ.evalZ u ≤ ℓ u := h2 u hu hp
    rw [hn] at hle hub ⊢
    have hle' : (N : ℤ) * n ≤ ℓ u := by exact_mod_cast hle
    have hnB : n ≤ (B : ℤ) := by
      have : (n : ℝ) ≤ B := hub.trans (Nat.le_ceil b)
      exact_mod_cast this
    have hCu := hC u hu hp
    rw [LinearMap.neg_apply] at hCu
    rcases (sub_nonneg.2 hle').eq_or_lt with ha | ha
    · have heq : (ℓ u : ℤ) = N * n := by linarith
      obtain ⟨k, c, hk, hc⟩ := h3 u hu hp (by rw [hn]; exact_mod_cast heq.symm)
      have hhu : 0 ≤ h u := by
        have e := congrArg h hc
        set_option synthInstance.maxHeartbeats 100000 in
          simp only [map_nsmul, map_sum, hγh] at e
        have hs : 0 ≤ ∑ i, c i • (if i ∈ T then (1 : ℤ) else 0) :=
          Finset.sum_nonneg fun i _ => by split_ifs <;> simp
        rw [← e, nsmul_eq_mul] at hs
        by_contra hneg
        push_neg at hneg
        have : (k : ℤ) * h u < 0 := mul_neg_of_pos_of_neg (by exact_mod_cast hk) hneg
        linarith
      have e1 : (ℓ u : ℝ) = N * n := by exact_mod_cast heq
      have e2 : (0 : ℝ) ≤ h u := by exact_mod_cast hhu
      refine ⟨by rw [e1]; linarith, fun h0 => ⟨e1, ?_⟩⟩
      rw [e1] at h0
      have : ((h u : ℤ) : ℝ) = 0 := by linarith
      exact_mod_cast this
    · have key : (1 : ℤ) ≤ K * (ℓ u - N * n) + h u := by
        have hK' : (K : ℤ) = C + C * N * B + 1 := by simp [hK]
        rw [hK']
        have a1 : (0 : ℤ) ≤ (C * N * B + 1) * (ℓ u - N * n - 1) := mul_nonneg (by positivity) (by linarith)
        have a2 : (0 : ℤ) ≤ C * N * (B - n) := mul_nonneg (by positivity) (by linarith)
        nlinarith
      have : (1 : ℝ) ≤ K * ((ℓ u : ℝ) - N * n) + h u := by exact_mod_cast key
      exact ⟨by linarith, fun h0 => by linarith⟩
  have dec : ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) →
      0 ≤ (K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β ∧
      ((K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β = 0 → (ℓ β : ℝ) = N * φ.evalZ β ∧ h β = 0) := by
    intro β hβ hp
    obtain ⟨n, u, c, hu, hup, hub, hc, hR, hφ⟩ := hb β hβ hp
    have lin : ∀ g : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ, (g β : ℝ) = ∑ i, c i * g (u i) := fun g => by
      have := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) Function.injective_id g (u := u) (w := ![β]) (a := c)
        (b := ![1]) (by simpa using hR.symm)
      simpa using this.symm
    have hF : (K : ℝ) * ((ℓ β : ℝ) - N * φ.evalZ β) + h β =
        ∑ i, c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) := by
      have e : ∀ i, c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) =
          K * (c i * ℓ (u i)) - K * N * (c i * φ.evalZ (u i)) + c i * h (u i) := fun i => by ring
      simp only [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← lin, ← hφ]
      ring
    have hF0 : ∀ i, 0 ≤ c i * ((K : ℝ) * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) + h (u i)) := fun i =>
      mul_nonneg (hc i) (cell (u i) (hu i) (hup i) (hub i)).1
    refine ⟨hF ▸ Finset.sum_nonneg fun i _ => hF0 i, fun h0 => ?_⟩
    rw [hF] at h0
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hF0 i).1 h0
    have hz' : ∀ i, c i * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) = 0 ∧ c i * (h (u i) : ℝ) = 0 := fun i => by
      rcases mul_eq_zero.1 (hz i (Finset.mem_univ _)) with h5 | h5
      · simp [h5]
      · obtain ⟨e1, e2⟩ := (cell (u i) (hu i) (hup i) (hub i)).2 h5
        simp [e1, e2]
    have e1 : (ℓ β : ℝ) - N * φ.evalZ β = ∑ i, c i * ((ℓ (u i) : ℝ) - N * φ.evalZ (u i)) := by
      rw [lin ℓ, hφ, Finset.mul_sum, ← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    have e2 := lin h
    rw [Finset.sum_eq_zero fun i _ => (hz' i).1] at e1
    rw [Finset.sum_eq_zero fun i _ => (hz' i).2] at e2
    exact ⟨by linarith, by exact_mod_cast e2⟩
  refine ⟨K * N, K • ℓ + h, Nat.mul_pos (by omega) hN, fun j => ?_, fun β hβ hp => ?_, fun β hβ hp he => ?_⟩
  · have hs : s j ∉ T := by simp [hT]
    simp only [LinearMap.add_apply, LinearMap.smul_apply, hγh, if_neg hs, nsmul_eq_mul, add_zero]
    push_cast
    rw [h1]
    ring
  · have := (dec β hβ hp).1
    simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul]
    push_cast
    linarith
  · simp only [LinearMap.add_apply, LinearMap.smul_apply, nsmul_eq_mul] at he
    push_cast at he
    obtain ⟨e1, e2⟩ := (dec β hβ hp).2 (by linarith)
    obtain ⟨k, c, hk, hc⟩ := h3 β hβ hp e1.symm
    have hzT : ∀ i ∈ T, c i = 0 := by
      have e := congrArg h hc
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_nsmul, map_sum, hγh, e2, smul_zero] at e
      have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => by split_ifs <;> simp).1 e.symm
      intro i hi
      have := hz i (Finset.mem_univ _)
      rw [if_pos hi, nsmul_eq_mul, mul_one] at this
      exact_mod_cast this
    refine ⟨k, fun j => c (s j), hk, ?_⟩
    rw [hc]
    have e3 : ∑ i, c i • γ i = ∑ i ∈ Finset.univ.map s, c i • γ i :=
      (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
        rw [hzT i (by simpa [hT, Finset.mem_map] using hi), zero_smul]).symm
    rw [e3, Finset.sum_map]

end GlobalTheory.PolFan.FaceStrict
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LieGramEqGramOf
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory.Toroidal GlobalTheory.FlagBundle GlobalTheory.ShFam GlobalTheory.CxPts GlobalTheory.ProjVar

namespace GlobalTheory.LieBase

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} {Z : Model Xo c β}
  {F : Type} [Field F] {σ : c.F →+* ℂ}


open Classical in
def gramOf (e : F ≃+* c.F) (G : EigMet Z σ) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ A : Mat Dw.mult X.Fn) (y : CxPts X.str (σ.comp e.toRingHom)) : Mat Dw.mult ℂ :=
  if h : ∃ g : EigFrame Z σ ((cxOf e σ hj y).1 ≫ genι Z), FrameAt e f₀ A₀ A y g then
    fun τ => (G.gram (cxOf e σ hj y) h.choose τ)ᵀ
  else 0

theorem lieGram_eq_gramOf (e : F ≃+* c.F) {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) {X : Var F} {j : X.X ⟶ gen Z}
    (hj : j ≫ genStr Z ≫ spMap e.toRingHom = X.str) (f₀ : EigFrame Z (constF e X) (genericPt X ≫ j ≫ genι Z))
    (A₀ : Mat Dw.mult X.Fn) : lieGram e U hj f₀ A₀ = gramOf e (hodgeMet Z U) hj f₀ A₀ := rfl

end GlobalTheory.LieBase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LinearFormFromFinsupp
section
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell

noncomputable section

namespace GlobalTheory.PolCell

variable {X : Type} [AddCommGroup X]

theorem linW_single_apply (p : X × X) (k : ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (Finsupp.single p k) β = k * β p.1 p.2 := by
  rw [linW_apply, Finsupp.sum_single_index (by simp)]

theorem linW_add_apply (w v : (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (w + v) β = linW w β + linW v β := by
  simp only [linW_apply]
  exact Finsupp.sum_add_index' (fun _ => by simp) (fun _ _ _ => by ring)

theorem linW_finset_sum_apply {ι : Type} (s : Finset ι) (g : ι → (X × X) →₀ ℤ) (β : LinearMap.BilinForm ℤ X) :
    linW (∑ i ∈ s, g i) β = ∑ i ∈ s, linW (g i) β := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [linW_apply]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, linW_add_apply, ih]

theorem bilin_eq_zero_of_mem_torsion_left (β : LinearMap.BilinForm ℤ X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) (y : X) : β t y = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := LinearMap.map_smul₂ β (n : ℤ) t y
  rw [hn, map_zero, LinearMap.zero_apply, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

theorem bilin_eq_zero_of_mem_torsion_right (β : LinearMap.BilinForm ℤ X) (x : X) {t : X}
    (ht : t ∈ Submodule.torsion ℤ X) : β x t = 0 := by
  obtain ⟨n, hn⟩ := (Submodule.mem_torsion_iff t).mp ht
  rw [Submonoid.smul_def] at hn
  have h := (β x).map_smul (n : ℤ) t
  rw [hn, map_zero, eq_comm, smul_eq_zero] at h
  exact h.resolve_left (nonZeroDivisors.coe_ne_zero n)

theorem exists_linW_eq : ∀ (X : Type) [AddCommGroup X] [Module.Finite ℤ X] (ℓ : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ),
    ∃ w : (X × X) →₀ ℤ, linW w = ℓ := by
  intro X _ _ ℓ
  classical
  let T := Submodule.torsion ℤ X
  let b := Module.Free.chooseBasis ℤ (X ⧸ T)
  let e : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X := fun i => (T.mkQ_surjective (b i)).choose
  have he : ∀ i, T.mkQ (e i) = b i := fun i => (T.mkQ_surjective (b i)).choose_spec
  let c : Module.Free.ChooseBasisIndex ℤ (X ⧸ T) → X →ₗ[ℤ] ℤ := fun i => (b.coord i).comp T.mkQ
  have hdec : ∀ x, x - ∑ i, c i x • e i ∈ T := by
    intro x
    refine (Submodule.Quotient.mk_eq_zero T).mp ?_
    change T.mkQ _ = 0
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum]
    simp only [map_smul, he, c, LinearMap.comp_apply, Module.Basis.coord_apply]
    rw [b.sum_repr, sub_self]
  have hβ : ∀ β : LinearMap.BilinForm ℤ X,
      β = ∑ i, ∑ j, β (e i) (e j) • (c i).smulRight (c j) := by
    intro β
    ext x y
    have h1 : β x y = β (∑ i, c i x • e i) y := by
      have := bilin_eq_zero_of_mem_torsion_left β (hdec x) y
      rwa [map_sub, LinearMap.sub_apply, sub_eq_zero] at this
    have h2 : ∀ x', β x' y = β x' (∑ j, c j y • e j) := by
      intro x'
      have := bilin_eq_zero_of_mem_torsion_right β x' (hdec y)
      rwa [map_sub, sub_eq_zero] at this
    rw [h1, h2]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.smulRight_apply, smul_eq_mul]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  refine ⟨∑ i, ∑ j, Finsupp.single (e i, e j) (ℓ ((c i).smulRight (c j))), ?_⟩
  ext β
  rw [linW_finset_sum_apply]
  conv_rhs => rw [hβ β]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, map_smul, smul_eq_mul, linW_finset_sum_apply, linW_single_apply]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

end GlobalTheory.PolCell
end
end

