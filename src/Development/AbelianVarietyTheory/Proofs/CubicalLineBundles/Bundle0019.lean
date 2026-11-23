module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsHomOfLinearScalingHermForm
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EqZeroOfSumEmbeddingSmul
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.Bundle0005
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KernelPolarisationTrivialOfSectionsVanishZero
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.ToMatrixTrFormBaseChange
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0013

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsIntegralDerivativeCurveHomGoodReduction
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace HomIntegral

theorem isLieComb_single_iff {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G] (c : R) (v w : epsR R ⟶ G) :
    IsLieComb ![c] ![v] w ↔ w.left = spMap (epsScaleR c) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro h
    exact ⟨fun _ => w, fun i => by fin_cases i; exact h, by simp⟩

theorem isLieComb_fibre {R R' : Type} [CommRing R] [CommRing R'] {g : R →+* R'} {G H : Over (Sp R)} [GrpObj H]
    {G' H' : Over (Sp R')} [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hψ : IsPullback ψ H'.hom H.hom (spMap g)) {F : G ⟶ H} {f : G' ⟶ H'} (hf : f.left ≫ ψ = φ ≫ F.left)
    {v : epsR R ⟶ G} {t : epsR R ⟶ H} {v' : epsR R' ⟶ G'} {t' : epsR R' ⟶ H'} (hv : IsVecOver g φ v v')
    (ht : IsVecOver g ψ t t') {b : R} (h : IsLieComb ![b] ![t] (v ≫ F)) : IsLieComb ![g b] ![t'] (v' ≫ f) := by
  rw [isLieComb_single_iff] at h ⊢
  unfold IsVecOver at hv ht
  refine hψ.hom_ext ?_ ?_
  · rw [Over.comp_left] at h
    rw [Over.comp_left, Category.assoc, hf, ← Category.assoc, hv, Category.assoc, h, Category.assoc, ht,
      ← Category.assoc, ← Category.assoc]
    congr 1
    refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
    congr 1
    ext a <;> simp [Chart.dualMapR, epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  · rw [Over.w, Category.assoc, Over.w t']
    refine Eq.trans ?_ (spMap_comp_spMap _ _).symm
    change spMap _ = spMap _
    congr 1
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]

theorem exists_extension {S S' : Scheme.{0}} {j : S' ⟶ S} {G H : Over S} [GrpObj G] [GrpObj H]
    (h : ∀ f : (Over.pullback j).obj G ⟶ (Over.pullback j).obj H, IsMonHom f →
      ∃! F : G ⟶ H, IsMonHom F ∧ (Over.pullback j).map F = f)
    {G' H' : Over S'} [GrpObj G'] [GrpObj H'] {φ : G'.left ⟶ G.left} {ψ : H'.left ⟶ H.left}
    (hφ : IsGrpPullback G' G j φ) (hψ : IsGrpPullback H' H j ψ) (f : G' ⟶ H') [IsMonHom f] :
    ∃ F : G ⟶ H, IsMonHom F ∧ f.left ≫ ψ = φ ≫ F.left := by
  obtain ⟨a, ha, ha'⟩ := grpPullback_iso hφ (isGrpPullback_pullback G j)
  obtain ⟨b, hb, hb'⟩ := grpPullback_iso hψ (isGrpPullback_pullback H j)
  obtain ⟨F, ⟨hF, e⟩, -⟩ := h (a.inv ≫ f ≫ b.hom) inferInstance
  refine ⟨F, hF, ?_⟩
  have e₁ : ((Over.pullback j).map F).left ≫ pullback.fst H.hom j = pullback.fst G.hom j ≫ F.left :=
    pullback.lift_fst _ _ _
  have e₂ : f ≫ b.hom = a.hom ≫ (Over.pullback j).map F := by rw [e, Iso.hom_inv_id_assoc]
  rw [← ha', ← hb', ← Category.assoc, ← Over.comp_left, e₂, Over.comp_left, Category.assoc, Category.assoc]
  exact congrArg (a.hom.left ≫ ·) e₁

end HomIntegral


open HomIntegral in
theorem isIntegral_of_hom_derivative : (∀ (T K : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [Field K] [Algebra T K] [IsFractionRing T K] (G G' : Over (Sp T)) [GrpObj G] [GrpObj G'], IsSemiAbelian G → IsSemiAbelian G' → ∀ f : (Over.pullback (spMap (algebraMap T K))).obj G ⟶ (Over.pullback (spMap (algebraMap T K))).obj G', IsMonHom f → ∃! F : G ⟶ G', IsMonHom F ∧ (Over.pullback (spMap (algebraMap T K))).map F = f) → Out.PolBaseChangeSt → ∀ (M : Type) [Field M] [NumberField M] (P Q : Out.PolAV (Sp (𝓞 M))) (v : epsR (𝓞 M) ⟶ P.A) (t : epsR (𝓞 M) ⟶ Q.A) (a : M), IsTangent v → (∀ (R' : Type) [CommRing R'] (f' : (𝓞 M) →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' Q P' φ' → IsVecOver f' φ' t v' → IsLieBasis ![v']) → (∀ (P₁ Q₁ : Out.PolAV (Sp M)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR M ⟶ P₁.A) (t₁ : epsR M ⟶ Q₁.A), IsPolFibre (algebraMap (𝓞 M) M) P P₁ φ₁ → IsPolFibre (algebraMap (𝓞 M) M) Q Q₁ ψ₁ → IsVecOver (algebraMap (𝓞 M) M) φ₁ v v₁ → IsVecOver (algebraMap (𝓞 M) M) ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![a] ![t₁] (v₁ ≫ f₁)) → IsIntegral ℤ a := by
  intro hext hB M _ _ P Q v t a hv ht hf
  have key : ∀ 𝔭 : IsDedekindDomain.HeightOneSpectrum (𝓞 M),
      a ∈ Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors := by
    intro 𝔭
    set T := Localization.subalgebra.ofField M _ 𝔭.asIdeal.primeCompl_le_nonZeroDivisors with hT
    have : IsDiscreteValuationRing T :=
      IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 M) 𝔭.ne_bot T
    have : IsFractionRing T M := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization 𝔭.asIdeal.primeCompl T M
    have e : (algebraMap T M).comp (algebraMap (𝓞 M) T) = algebraMap (𝓞 M) M :=
      (IsScalarTower.algebraMap_eq _ _ _).symm
    obtain ⟨P₀, φ₀, hP₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) P
    obtain ⟨Q₀, ψ₀, hQ₀⟩ := exists_isPolFibre hB (algebraMap (𝓞 M) T) Q
    obtain ⟨P₁, φ₁, hP₁⟩ := exists_isPolFibre hB (algebraMap T M) P₀
    obtain ⟨Q₁, ψ₁, hQ₁⟩ := exists_isPolFibre hB (algebraMap T M) Q₀
    obtain ⟨v₀, hv₀, -⟩ := existsUnique_isVecOver hP₀.2.1.1 v
    obtain ⟨t₀, ht₀, -⟩ := existsUnique_isVecOver hQ₀.2.1.1 t
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hP₁.2.1.1 v₀
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hQ₁.2.1.1 t₀
    have hP := e ▸ PolFibre.comp hP₀ hP₁
    have hQ := e ▸ PolFibre.comp hQ₀ hQ₁
    have hv' := e ▸ (PolFibre.vec_iff hP₀.2.1.1 hP₁.2.1.1.w hv₀).1 hv₁
    have ht' := e ▸ (PolFibre.vec_iff hQ₀.2.1.1 hQ₁.2.1.1.w ht₀).1 ht₁
    obtain ⟨f, hfm, hfa⟩ := hf P₁ Q₁ _ _ v₁ t₁ hP hQ hv' ht'
    obtain ⟨F, hF, hFf⟩ := exists_extension (hext T M P₀.A Q₀.A (isSemiAbelian_of_isAbelianScheme _ P₀.isAb)
      (isSemiAbelian_of_isAbelianScheme _ Q₀.isAb)) hP₁.2.1 hQ₁.2.1 f
    have tv₀ := hv₀.isTangent hP₀.2.1 hv
    obtain ⟨c, hc, -⟩ := (ht T _ Q₀ ψ₀ t₀ hQ₀ ht₀).2 _ (isTangent_comp_of_isMonHom F v₀ tv₀)
    have ec : c = ![c 0] := by funext i; fin_cases i; rfl
    rw [ec] at hc
    have h₁ := isLieComb_fibre hQ₁.2.1.1 hFf hv₁ ht₁ hc
    have u := ((ht M _ Q₁ _ t₁ hQ ht').2 _
      (isTangent_comp_of_isMonHom f v₁ (hv₁.isTangent hP₁.2.1 tv₀))).unique hfa h₁
    have ea : a = algebraMap T M (c 0) := congrFun u 0
    rw [ea]
    exact (c 0).2
  have h := Algebra.mem_iInf.2 key
  rw [IsDedekindDomain.HeightOneSpectrum.iInf_localization_eq_bot, Algebra.mem_bot] at h
  obtain ⟨x, rfl⟩ := h
  exact x.isIntegral_coe

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.KTrivOfUnimodular
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorKernel

open GlobalTheory.CechPic

section Local

variable {Y Y' B : Scheme.{0}}

def LocZero (π : Y ⟶ B) (c : Pic Y) : Prop :=
  ∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∀ (Z : Scheme.{0}) (f : Z ⟶ Y), (∀ z, π (f z) ∈ V) → pull f c = 0

theorem LocZero.add {π : Y ⟶ B} {c d : Pic Y} (hc : LocZero π c) (hd : LocZero π d) : LocZero π (c + d) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  obtain ⟨V', hV', H'⟩ := hd p
  refine ⟨V ⊓ V', ⟨hV, hV'⟩, fun Z f hf => ?_⟩
  rw [map_add (f := _), H Z f fun z => (hf z).1, H' Z f fun z => (hf z).2, add_zero]

theorem LocZero.pull {π : Y ⟶ B} {c : Pic Y} (hc : LocZero π c) (k : Y' ⟶ Y) :
    LocZero (k ≫ π) (pull k c) := by
  intro p
  obtain ⟨V, hV, H⟩ := hc p
  exact ⟨V, hV, fun Z f hf => (pull_comp f k c).symm.trans (H Z (f ≫ k) hf)⟩

theorem locZero_base (π : Y ⟶ B) (d : Pic B) : LocZero π (pull π d) := by
  obtain ⟨D, hD, rfl⟩ := cls_surj d
  intro p
  obtain ⟨i, hi⟩ := exists_chart hD p
  refine ⟨D.U i, hi, fun Z f hf => (pull_comp f π _).symm.trans ?_⟩
  exact (cls_eq_zero_iff (pull_isLB hD (f ≫ π))).2
    (BoxKernel.gen_of_chart (pull_isLB hD _) (fun _ => i) fun z => mem_pull.2 (hf z))

theorem locZero_iff (π : Y ⟶ B) {M : LB Y} (hM : M.IsLB) :
    (∀ p : B, ∃ V : B.Opens, p ∈ V ∧ ∃ c : LB.Gen (M.pull (π ⁻¹ᵁ V).ι), c.IsGen) ↔ LocZero π (cls M hM) := by
  refine forall_congr' fun p => exists_congr fun V => and_congr_right fun _ => ?_
  rw [← cls_eq_zero_iff (pull_isLB hM _), cls_pull hM]
  refine ⟨fun H Z f hf => ?_, fun H => H _ _ fun z => z.2⟩
  have hr : Set.range f ⊆ Set.range (π ⁻¹ᵁ V).ι := by
    rintro _ ⟨z, rfl⟩
    rw [Scheme.Opens.range_ι]
    exact hf z
  rw [← IsOpenImmersion.lift_fac (π ⁻¹ᵁ V).ι f hr, pull_comp, H, map_zero]

end Local

section Group

variable {S : Scheme.{0}} {A T : Over S} [GrpObj A]

theorem translDiff_iff {L : LB A.left} (hL : L.IsLB) (x : T ⟶ A) :
    (∀ p : T.left, ∃ V : T.left.Opens, p ∈ V ∧
      ∃ c : LB.Gen ((Out.translDiff A L x).pull ((fst T A).left ⁻¹ᵁ V).ι), c.IsGen) ↔
      LocZero (fst T A).left (lam (cls L hL) (fst T A ≫ x) (snd T A)) := by
  have hD : (Out.translDiff A L x).IsLB := LB.isLB_linComb hL _ _
  rw [locZero_iff _ hD]
  have e : lam (cls L hL) (fst T A ≫ x) (snd T A) = cls _ hD +
      pull (fst T A).left (pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL)) := by
    have e₁ : cls _ hD = pull ((fst T A ≫ x) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) := by
      refine (cls_linComb hL _ _ hD).trans ?_
      rw [Fin.sum_univ_two]
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, one_smul, neg_smul, ← sub_eq_add_neg]
      rfl
    rw [e₁, map_sub, ← pull_comp, ← pull_comp, ← Over.comp_left, ← Over.comp_left, MonObj.comp_one, lam]
    abel
  refine ⟨fun H => e ▸ H.add (locZero_base _ _), fun H => ?_⟩
  have := H.add (locZero_base _ (-(pull (1 : T ⟶ A).left (cls L hL) - pull x.left (cls L hL))))
  rwa [e, map_neg, add_neg_cancel_right] at this

end Group

end GlobalTheory.HermTensorKernel
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.EllipticHom

theorem exists_coord {g : ℕ} (hg : g = 1) {w : Fin g → ℂ} (hw : w ≠ 0) :
    ∃ c : (Fin g → ℂ) →ₗ[ℂ] ℂ, (∀ x, c x • w = x) ∧ c w = 1 := by
  subst hg
  have hw0 : w 0 ≠ 0 := fun h => hw (funext fun i => by rw [Subsingleton.elim i 0, h]; rfl)
  refine ⟨(w 0)⁻¹ • LinearMap.proj 0, fun x => ?_, by simp [hw0]⟩
  funext i
  rw [Subsingleton.elim i 0]
  simp only [LinearMap.smul_apply, LinearMap.proj_apply, Pi.smul_apply, smul_eq_mul]
  field_simp

theorem exists_index {L L' : PeriodPair} {α : ℂ} (h : ∀ z ∈ L.lattice, α * z ∈ L'.lattice) :
    ∃ n : ℕ, Complex.normSq α * |(L.ω₁ * starRingEnd ℂ L.ω₂).im| = n * |(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| := by
  obtain ⟨p, q, h1⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₁_mem_lattice)
  obtain ⟨r, s, h2⟩ := PeriodPair.mem_lattice.1 (h _ L.ω₂_mem_lattice)
  refine ⟨(p * s - q * r).natAbs, ?_⟩
  have e : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im =
      ((p * s - q * r : ℤ) : ℝ) * (L'.ω₁ * starRingEnd ℂ L'.ω₂).im := by
    have e1 : Complex.normSq α * (L.ω₁ * starRingEnd ℂ L.ω₂).im = ((α * L.ω₁) * starRingEnd ℂ (α * L.ω₂)).im := by
      simp [Complex.normSq_apply]
      ring
    rw [e1, ← h1, ← h2]
    simp
    ring
  rw [Nat.cast_natAbs, Int.cast_abs, ← abs_mul, ← e, abs_mul, abs_of_nonneg (Complex.normSq_nonneg α)]

theorem covolume_ne_zero (L : PeriodPair) : (L.ω₁ * starRingEnd ℂ L.ω₂).im ≠ 0 := by
  intro h
  have hi := LinearIndependent.pair_iff.1 L.indep
  simp at h
  have h1 := hi L.ω₂.re (-L.ω₁.re) (by
    apply Complex.ext <;> simp <;> linarith)
  have h2 := hi L.ω₂.im (-L.ω₁.im) (by
    apply Complex.ext <;> simp <;> linarith)
  have h3 := hi 0 1 (by
    apply Complex.ext <;> simp [h1.1, h2.1])
  exact one_ne_zero h3.2

theorem multiplier_iff_exists_hom : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (R : Type) [CommRing R] (P Q : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (t : epsR R ⟶ Q.A) (s : R →+* ℂ) (L L' : PeriodPair) (α : ℂ), P.g = 1 → Q.g = 1 → IsTangent v → IsTangent t → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s P P' φ' → IsVecOver s φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L.lattice ↔ z • w' ∈ u'.Λ) → (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ Q.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s Q P' φ' → IsVecOver s φ' t v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ L'.lattice ↔ z • w' ∈ u'.Λ) → ((∀ z ∈ L.lattice, α * z ∈ L'.lattice) ↔ (∀ (P₁ Q₁ : Out.PolAV (Sp ℂ)) (φ₁ : P₁.A.left ⟶ P.A.left) (ψ₁ : Q₁.A.left ⟶ Q.A.left) (v₁ : epsR ℂ ⟶ P₁.A) (t₁ : epsR ℂ ⟶ Q₁.A), IsPolFibre s P P₁ φ₁ → IsPolFibre s Q Q₁ ψ₁ → IsVecOver s φ₁ v v₁ → IsVecOver s ψ₁ t t₁ → ∃ f₁ : P₁.A ⟶ Q₁.A, IsMonHom f₁ ∧ IsLieComb ![α] ![t₁] (v₁ ≫ f₁))) := by
  intro hU hB R _ P Q v t s L L' α hP hQ hv ht hL hL'
  constructor
  · intro hα P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, Hm, χ, Ef, hA, -, hd, -, -, hθ, hE, hEb, -⟩ := hU P₁ rig hrig
    obtain ⟨u', Hm', χ', Ef', hA', -, hd', he', -, hθ', hE', hEb', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨w0, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨w0', hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    have g1 : P₁.g = 1 := hφ.1.trans hP
    have g2 : Q₁.g = 1 := hψ.1.trans hQ
    have hH := hermForm_principal_dim_one _ u.Λ w L Hm Ef g1 w0 hΛ hA.1 (hA.2.1 w w0) hE hEb
    have hH' := hermForm_principal_dim_one _ u'.Λ w' L' Hm' Ef' g2 w0' hΛ' hA'.1 (hA'.2.1 w' w0') hE' hEb'
    obtain ⟨c, hc, hc1⟩ := exists_coord g1 w0
    obtain ⟨n, hn⟩ := exists_index hα
    let F : (Fin P₁.g → ℂ) →ₗ[ℂ] (Fin Q₁.g → ℂ) := (α • c).smulRight w'
    have hF : ∀ x, F x = (α * c x) • w' := fun x => rfl
    obtain ⟨f, hf, hFf⟩ := exists_hom_of_linear_scaling_hermForm P₁ Q₁ u u' Hm χ Hm' χ' hA hA'
      (fun k => (hθ k).2) (fun k => (hθ' k).1) F n
      (fun l hl => by
        rw [hF, ← hΛ']
        exact hα _ ((hΛ _).2 (by rwa [hc])))
      (fun x y => by
        have e := hH (c x) (c y)
        rw [hc, hc] at e
        have a1 : ((|(L.ω₁ * starRingEnd ℂ L.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L)
        have a2 : ((|(L'.ω₁ * starRingEnd ℂ L'.ω₂).im| : ℝ) : ℂ) ≠ 0 := by
          exact_mod_cast abs_ne_zero.2 (covolume_ne_zero L')
        have hn' := congrArg (fun r : ℝ => (r : ℂ)) hn
        simp only [Complex.ofReal_mul, Complex.ofReal_natCast, ← Complex.mul_conj] at hn'
        rw [hF, hF, hH', e, map_mul, ← mul_div_assoc, div_eq_div_iff a2 a1]
        linear_combination (c x * starRingEnd ℂ (c y)) * hn')
    refine ⟨f, hf, ?_⟩
    have h1 := HomLinear.isDiff_comp u u' f F hFf tv hw
    rw [hF, hc1, _root_.mul_one] at h1
    have hx := (LieMultiple.isLieComb_one_iff_comp α t₁ _).2 rfl
    have hxt : IsTangent (Chart.spMap (Chart.scaleD α) ≫ t₁) :=
      (Chart.isTan_iff _).1 (Chart.isTan_scale α ((Chart.isTan_iff _).2 tt))
    have := (he' (α • w')).unique ⟨HomLinear.isTangent_comp f tv, h1⟩
      ⟨hxt, CMNormIdentity.isDiff_of_isLieComb u' hw' α hx⟩
    rw [this]
    exact hx
  · intro h z hz
    obtain ⟨P₁, φ₁, hφ⟩ := exists_isPolFibre hB s P
    obtain ⟨Q₁, ψ₁, hψ⟩ := exists_isPolFibre hB s Q
    obtain ⟨v₁, hv₁, -⟩ := existsUnique_isVecOver hφ.2.1.1 v
    obtain ⟨t₁, ht₁, -⟩ := existsUnique_isVecOver hψ.2.1.1 t
    obtain ⟨f, hf, hl⟩ := h P₁ Q₁ φ₁ ψ₁ v₁ t₁ hφ hψ hv₁ ht₁
    obtain ⟨rig, hrig⟩ := P₁.rigid
    obtain ⟨rig', hrig'⟩ := Q₁.rigid
    obtain ⟨u, -, -, -, -, -, hd, -⟩ := hU P₁ rig hrig
    obtain ⟨u', -, -, -, -, -, hd', he', -⟩ := hU Q₁ rig' hrig'
    have tv := hv₁.isTangent hφ.2.1 hv
    have tt := ht₁.isTangent hψ.2.1 ht
    obtain ⟨w, hw, -⟩ := hd v₁ tv
    obtain ⟨w', hw', -⟩ := hd' t₁ tt
    obtain ⟨-, hΛ⟩ := hL P₁ φ₁ v₁ u w hφ hv₁ hw
    obtain ⟨-, hΛ'⟩ := hL' Q₁ ψ₁ t₁ u' w' hψ ht₁ hw'
    obtain ⟨F, -, hF, hT, -⟩ := HomLinear.exists_linear_of_isMonHom P₁.A Q₁.A P₁.isAb Q₁.isAb P₁.L Q₁.L _ _ u u'
      hd' he' f hf
    obtain ⟨tf, df⟩ := hT w v₁ tv hw
    have e : F w = α • w' := (hd' _ tf).unique df (CMNormIdentity.isDiff_of_isLieComb u' hw' α hl)
    have := hF _ ((hΛ z).1 hz)
    rw [map_smul, e, smul_smul, _root_.mul_comm] at this
    exact (hΛ' _).2 this

end GlobalTheory.EllipticHom
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw

namespace GlobalTheory.WeierstrassCurve

theorem appLE_top_eq_zero_iff {X T : Scheme.{0}} (t : T ⟶ X) {U : X.Opens} (h : ⊤ ≤ t ⁻¹ᵁ U)
    (a : Γ(X, U)) : (t.appLE U ⊤ h).hom a = 0 ↔ (t.app U).hom a = 0 := by
  have e : (t.appLE U ⊤ h).hom a = resG _ h ((t.app U).hom a) := rfl
  rw [e]
  refine ⟨fun h0 => ?_, fun h0 => by rw [h0, map_zero]⟩
  have := congrArg (resG _ (le_top : t ⁻¹ᵁ U ≤ ⊤)) h0
  rwa [Cartier.resG_resG, Cartier.resG_self, map_zero] at this

theorem appLE_originSec_eq_zero_iff {R : Type} [CommRing R] (W : WeierstrassCurve R) {T : Scheme.{0}}
    (t : T ⟶ scheme W) (i : (originLB W).ι) (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i) :
    (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔ t = t ≫ toSpec W ≫ zero W := by
  rw [appLE_top_eq_zero_iff]
  constructor
  · intro h0
    rcases i with _ | _
    · have h1 : (1 : Γ(T, t ⁻¹ᵁ coordOpen W 2)) = 0 := (map_one _).symm.trans h0
      have hT : IsEmpty T := ⟨fun p => by
        have := congrArg (T.presheaf.germ (t ⁻¹ᵁ coordOpen W 2) p (h (Set.mem_univ p))).hom h1
        rw [map_one, map_zero] at this
        exact absurd this one_ne_zero⟩
      refine (eq_comp_zero_iff W t).2 ⟨fun p _ => (hT.false p).elim, Cartier.ext_germ fun p _ => (hT.false p).elim⟩
    · exact (eq_comp_zero_iff W t).2 ⟨h, h0⟩
  · intro e
    have h0 := (secPull_originSec_eq_zero_iff W t).2 e (fun _ => i)
    have := congrArg (resG T (Cartier.pull_U (originLB W) t (fun _ => i)).ge) h0
    rw [map_zero] at this
    exact ((Cartier.resG_resG _ _ _).trans (Cartier.resG_self _ _)).symm.trans this

theorem appLE_sec_pull_originLB_eq_zero {R : Type} [CommRing R] (W : WeierstrassCurve R)
    {R' : Type} [CommRing R'] {f : Sp R' ⟶ Sp R} {Y : Scheme.{0}} {φ : Y ⟶ scheme W} {q : Y ⟶ Sp R'}
    (H : IsPullback φ q (toSpec W) f) (s : ((originLB W).pull φ).Sec) {T : Scheme.{0}} (t : T ⟶ Y)
    (j : ((originLB W).pull φ).ι) (h : ⊤ ≤ t ⁻¹ᵁ ((originLB W).pull φ).U j)
    (e : t ≫ φ = t ≫ φ ≫ toSpec W ≫ zero W) :
    (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom (s.f j) = 0 := by
  obtain ⟨c, hc, -⟩ := existsUnique_eq_appLE_mul_secPull W H s
  have h' : ⊤ ≤ (t ≫ φ) ⁻¹ᵁ (originLB W).U (j ⟨⟩) :=
    fun p hp => (Cartier.pull_U (originLB W) φ j).le (h hp)
  have h0 := (appLE_originSec_eq_zero_iff W (t ≫ φ) (j ⟨⟩) h').2 (e.trans (Category.assoc _ _ _).symm)
  have h1 : (t.appLE (((originLB W).pull φ).U j) ⊤ h).hom
      ((Cartier.secPull (originSec W) φ).f j) = 0 := by
    refine Eq.trans ?_ h0
    have := Scheme.Hom.appLE_comp_appLE t φ ((originLB W).U (j ⟨⟩)) _ ⊤
      (Cartier.pull_U (originLB W) φ j).le h
    exact congrArg (fun g => g.hom ((originSec W).f (j ⟨⟩))) this
  rw [hc j, map_mul, h1, mul_zero]

theorem originLB_polarisation (R : Type) [CommRing R] (W : WeierstrassCurve R) [GrpObj (schemeOver W)]
    (_hc : IsCommMonObj (schemeOver W)) (he : η[schemeOver W].left = zero W) :
    Out.Rigidified (schemeOver W) (originLB W) ∧ Out.Sym (schemeOver W) (originLB W) ∧
      Out.RelAmple (schemeOver W) (originLB W) ∧ Out.KTriv (schemeOver W) (originLB W) := by
  have he' : eSec (schemeOver W) = zero W := he
  have hz : ∀ (T : Scheme.{0}) (t : T ⟶ (schemeOver W).left) (i : (originLB W).ι)
      (h : ⊤ ≤ t ⁻¹ᵁ (originLB W).U i),
      (t.appLE ((originLB W).U i) ⊤ h).hom ((originSec W).f i) = 0 ↔
        t = t ≫ (schemeOver W).hom ≫ eSec (schemeOver W) := fun T t i h => by
    rw [he']
    exact appLE_originSec_eq_zero_iff W t i h
  refine ⟨?_, ?_, relAmple_originLB W, ?_⟩
  · unfold Out.Rigidified
    rw [he']
    exact ⟨_, isGen_one_pull_zero W⟩
  · exact _root_.GlobalTheory.SymOfZeroDivisor.sym_of_regular_section _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W)
      (fun i V h => ((isRegularSec_originSec W i).resG h).mem) hz
  · refine _root_.GlobalTheory.kTriv_of_sections_vanish_on_zero _ (schemeOver W) (originLB W) (originSec W) (originLB_isLB W) hz ?_
    intro R' _ f Y φ q H s T t j h e
    rw [he'] at e
    exact appLE_sec_pull_originLB_eq_zero W H s t j h e

end GlobalTheory.WeierstrassCurve
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalRootReZeroImSq
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

noncomputable section

namespace GlobalTheory.PrincipalDatum

open GlobalTheory.HostModel

variable {E : Type} [Field E] [NumberField E]

omit [NumberField E] in
theorem coe_add' (a b : 𝓞 E) : ((a + b : 𝓞 E) : E) = a + b := rfl

omit [NumberField E] in
theorem coe_mul' (a b : 𝓞 E) : ((a * b : 𝓞 E) : E) = a * b := rfl

theorem exists_clear (𝔞 : Submodule (𝓞 E) E) (h : 𝔞.FG) :
    ∃ N : ℤ, N ≠ 0 ∧ ∃ ψ : 𝔞 →ₗ[𝓞 E] 𝓞 E, ∀ x, (ψ x : E) = N * (x : E) := by
  obtain ⟨a, ⟨N, hN, rfl⟩, ha⟩ :=
    FractionalIdeal.isFractional_of_fg (S := Algebra.algebraMapSubmonoid (𝓞 E) (nonZeroDivisors ℤ)) h
  choose f hf using ha
  have hf' : ∀ x : 𝔞, ((f x x.2 : 𝓞 E) : E) = N * (x : E) := fun x => by
    have := hf x x.2
    rw [Algebra.smul_def] at this
    simpa using this
  refine ⟨N, nonZeroDivisors.ne_zero hN, ⟨⟨fun x => f x x.2, fun x y => ?_⟩, fun c x => ?_⟩, hf'⟩
  · apply RingOfIntegers.ext
    rw [coe_add', hf', hf', hf', Submodule.coe_add, mul_add]
  · apply RingOfIntegers.ext
    simp only [RingHom.id_apply, smul_eq_mul]
    rw [coe_mul', hf', hf', Submodule.coe_smul, Algebra.smul_def]
    simp only [RingOfIntegers.coe_eq_algebraMap]
    ring

section Act

variable {M : Type} [AddCommGroup M] [Module (𝓞 E) M]






end Act

variable [IsCMField E]

theorem principal_root_re_zero_im_sq (H : Host E) : H.rt0.re = 0 ∧ H.rt0.im ^ 2 = H.d := by
  first
  | exact @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq
  | (apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SquareEqNegReIm.re_eq_zero_and_im_sq ..)

end GlobalTheory.PrincipalDatum
end
end

