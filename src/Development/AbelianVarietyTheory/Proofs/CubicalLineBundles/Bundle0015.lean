module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsChartOfMemRedKer
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogCovolumeEqMeanClassGroup
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsLieCombOneIffComp
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.LieMultiple

variable {R : Type} [CommRing R] {G : Over (Sp R)} [GrpObj G]

theorem isLieComb_one_iff_comp (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x = Chart.spMap (Chart.scaleD a) ≫ v := by
  rw [Chart.isLieComb_iff]
  simp [Chart.prodPts]

theorem isLieComb_one_iff (a : R) (v x : epsR R ⟶ G) :
    IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left := by
  rw [isLieComb_one_iff_comp]
  exact ⟨fun h => by rw [h]; rfl, fun h => Over.OverMorphism.ext h⟩

theorem scale_add {v : epsR R ⟶ G} (hv : IsTangent v) (a b : R) :
    Chart.spMap (Chart.scaleD (a + b)) ≫ v =
      (Chart.spMap (Chart.scaleD a) ≫ v) * (Chart.spMap (Chart.scaleD b) ≫ v) := by
  rw [SqZero.scaleD_eq, SqZero.scaleD_eq, SqZero.scaleD_eq,
    ← SqZero.epsTo_add_comp ((Chart.isTan_iff _).2 hv) _ _ _ _ (TrivSqZeroExt.inr_mul_inr _ _ _)
      (by rw [← TrivSqZeroExt.inr_add]; exact TrivSqZeroExt.inr_mul_inr _ _ _)]
  congr 3
  exact TrivSqZeroExt.inr_add _ _ _

theorem scaleD_comp (a b : R) : (Chart.scaleD a).comp (Chart.scaleD b) = Chart.scaleD (a * b) := by
  rw [SqZero.scaleD_eq a, SqZero.epsTo_comp_scaleD, SqZero.scaleD_eq]
  congr 1
  rw [← TrivSqZeroExt.inr_smul, smul_eq_mul, _root_.mul_comm]

theorem scaleD_one : Chart.scaleD (1 : R) = AlgHom.id R _ :=
  DualNumber.algHom_ext (by rw [SqZero.scaleD_eq, SqZero.epsTo_eps]; rfl)

theorem lieMultiple_calculus : ∀ (R : Type) [CommRing R] (G G' : Over (Sp R)) [GrpObj G] [GrpObj G'] (v x y : epsR R ⟶ G) (a b : R), (IsLieComb ![a] ![v] x ↔ x.left = spMap (epsScaleR a) ≫ v.left) ∧ (IsTangent v → IsLieComb ![a] ![v] x → IsLieComb ![b] ![v] y → IsLieComb ![a + b] ![v] (x * y)) ∧ (IsLieComb ![b] ![v] x → IsLieComb ![a] ![x] y → IsLieComb ![a * b] ![v] y) ∧ (∀ f : G ⟶ G', IsLieComb ![a] ![v] x → IsLieComb ![a] ![v ≫ f] (x ≫ f)) ∧ IsLieComb ![1] ![v] v ∧ (IsTangent v → IsLieComb ![0] ![v] 1) := by
  intro R _ G G' _ _ v x y a b
  refine ⟨isLieComb_one_iff a v x, fun hv hx hy => ?_, fun hx hy => ?_, fun f hx => ?_, ?_, fun hv => ?_⟩
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hx, hy]
    exact (scale_add hv a b).symm
  · rw [isLieComb_one_iff_comp] at hx hy ⊢
    rw [hy, hx, ← scaleD_comp, ← Chart.spMap_comp]
    exact (Category.assoc _ _ _).symm
  · rw [isLieComb_one_iff_comp] at hx ⊢
    rw [hx]
    exact Category.assoc _ _ _
  · rw [isLieComb_one_iff_comp, scaleD_one, Chart.spMap_id]
    exact (Category.id_comp _).symm
  · rw [isLieComb_one_iff_comp, SqZero.scaleD_eq]
    exact (SqZero.epsTo_zero_comp ((Chart.isTan_iff _).2 hv) _ (TrivSqZeroExt.inr_zero _) _).symm

end GlobalTheory.LieMultiple
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsUnimodularSolZeroNeg
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.WeierstrassCurve
open scoped CategoryTheory.Obj UpperHalfPlane

noncomputable section

namespace GlobalTheory.WeierstrassCurve.OriginTangent

variable {R : Type} [CommRing R] (W : WeierstrassCurve R) {A : Type} [CommRing A]

theorem ptHom_origin_inj {ρ ρ' : R →+* A} {z w z' w' : A}
    (h : IsUnimodularSol (W.map ρ) ![z, -1, w]) (h' : IsUnimodularSol (W.map ρ') ![z', -1, w'])
    (e : ptHom W ρ ![z, -1, w] h = ptHom W ρ' ![z', -1, w'] h') : z = z' ∧ w = w' := by
  have e₁ := (SpecMap_originEval_chartY W ρ z w h.equation).trans
    (e.trans (SpecMap_originEval_chartY W ρ' z' w' h'.equation).symm)
  rw [cancel_mono] at e₁
  have e' : originEval W ρ z w h.equation = originEval W ρ' z' w' h'.equation :=
    congrArg (·.hom) (Spec.map_injective e₁)
  exact ⟨(originEval_originZ ..).symm.trans
      ((RingHom.congr_fun e' (originZ W)).trans (originEval_originZ ..)),
    (originEval_originW ..).symm.trans
      ((RingHom.congr_fun e' (originW W)).trans (originEval_originW ..))⟩

theorem exists_eq_ptHom_origin (ρ : R →+* A) (g : Spec (.of A) ⟶ scheme W)
    (hY : ∀ p, g p ∈ coordOpen W 1) (hg : g ≫ toSpec W = Spec.map (CommRingCat.ofHom ρ)) :
    ∃ (z w : A) (h : IsUnimodularSol (W.map ρ) ![z, -1, w]), g = ptHom W ρ ![z, -1, w] h := by
  have hr : Set.range g ⊆ Set.range (chartY W) := by
    rintro _ ⟨p, rfl⟩
    rw [← Scheme.Hom.coe_opensRange, opensRange_chartY]
    exact hY p
  obtain ⟨ψ, hψ⟩ := Spec.map_surjective (IsOpenImmersion.lift _ _ hr)
  have hl : Spec.map ψ ≫ chartY W = g := hψ ▸ IsOpenImmersion.lift_fac _ _ hr
  have hc : ψ.hom.comp (algebraMap R (OriginRing W)) = ρ := by
    rw [← hl, Category.assoc, chartY_toSpec, ← Spec.map_comp] at hg
    exact congrArg (·.hom) (Spec.map_injective hg)
  have hP : (ψ.hom ∘ ![originZ W, -1, originW W]) =
      ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    ext1 j; fin_cases j <;> simp
  have h₀ : IsUnimodularSol (W.map (algebraMap R (OriginRing W))) ![originZ W, -1, originW W] :=
    isUnimodularSol_origin (equation_originZ_originW W)
  have h₁ := h₀.map_comp ψ.hom
  have h₂ : IsUnimodularSol (W.map ρ) ![ψ.hom (originZ W), -1, ψ.hom (originW W)] := by
    rw [← hc, ← hP]; exact h₁
  refine ⟨_, _, h₂, ?_⟩
  rw [← hl]
  exact (SpecMap_ptHom W _ _ h₀ ψ.hom).trans (ptHom_congr W _ _ _ hc hP _)

theorem SpecMap_zero_origin (ρ : R →+* A) (h : IsUnimodularSol (W.map ρ) ![0, -1, 0]) :
    Spec.map (CommRingCat.ofHom ρ) ≫ zero W = ptHom W ρ ![0, -1, 0] h := by
  rw [SpecMap_zero, ← ptHom_smul W ρ _ _ isUnit_one.neg]
  exact ptHom_congr W _ _ _ rfl (by ext1 j; fin_cases j <;> simp) _

theorem isUnimodularSol_zero_neg (V : WeierstrassCurve A) : IsUnimodularSol V ![0, -1, 0] :=
  isUnimodularSol_origin (by rw [equation_origin_iff]; simp)

theorem exists_eq_ptHom_eps (f : R →+* A) (g : Spec (.of (DualNumber A)) ⟶ scheme W)
    (hg : g ≫ toSpec W =
      Spec.map (CommRingCat.ofHom ((algebraMap A (DualNumber A)).comp f)))
    (h0 : Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom) ≫ g =
      Spec.map (CommRingCat.ofHom f) ≫ zero W) :
    ∃ (c : A) (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f))
      ![TrivSqZeroExt.inr c, -1, 0]),
      g = ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h := by
  have hY : ∀ p, g p ∈ coordOpen W 1 := by
    intro p
    have hs : Function.Surjective (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom) := by
      rw [← Set.range_eq_univ, range_comap_of_surjective _ _ TrivSqZeroExt.fst_surjective,
        PrimeSpectrum.zeroLocus_eq_univ_iff]
      intro x hx
      have hx' : x.fst = 0 := hx
      refine ⟨2, ?_⟩
      ext <;> simp [pow_two, hx']
    obtain ⟨q, rfl⟩ := hs p
    have e : g (PrimeSpectrum.comap (TrivSqZeroExt.fstHom A A A).toRingHom q) =
        zero W (Spec.map (CommRingCat.ofHom f) q) := by
      exact (Scheme.Hom.comp_apply
        (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A A).toRingHom)) g q).symm.trans
        ((congrArg (fun t => t q) h0).trans
          (Scheme.Hom.comp_apply (Spec.map (CommRingCat.ofHom f)) (zero W) q))
    rw [e]
    exact (zero_preimage_coordOpen_one W).ge (Set.mem_univ _)
  obtain ⟨z, w, h, rfl⟩ := exists_eq_ptHom_origin W _ g hY hg
  have hP : ((TrivSqZeroExt.fstHom A A A).toRingHom ∘ ![z, -1, w]) = ![z.fst, -1, w.fst] := by
    ext1 j; fin_cases j <;> simp
  have h₁ := h.map_comp (TrivSqZeroExt.fstHom A A A).toRingHom
  have h₂ := h₁
  rw [hP] at h₂
  rw [SpecMap_ptHom, SpecMap_zero_origin W f (isUnimodularSol_zero_neg _),
    ptHom_congr W _ _ h₁ rfl hP h₂] at h0
  obtain ⟨hz, hw⟩ := ptHom_origin_inj W _ _ h0
  have he := (equation_origin_iff _ _ _).mp h.equation
  have hzz : z * z = 0 := by ext <;> simp [hz]
  have hzw : z * w = 0 := by ext <;> simp [hz, hw]
  have hww : w * w = 0 := by ext <;> simp [hw]
  have hw0 : w = 0 := by
    set V := W.map ((algebraMap A (DualNumber A)).comp f)
    linear_combination he + z * hzz + (V.a₁ + V.a₂ * z + V.a₄ * w) * hzw + (V.a₃ + V.a₆ * w) * hww
  have hz0 : z = TrivSqZeroExt.inr z.snd := by ext <;> simp [hz]
  have hQ : ![z, -1, w] = ![TrivSqZeroExt.inr z.snd, -1, 0] := by rw [hw0, ← hz0]
  exact ⟨z.snd, hQ ▸ h, ptHom_congr W _ _ _ rfl hQ _⟩

theorem epsScale_ptHom (f : R →+* A) (c : A)
    (h : IsUnimodularSol (W.map ((algebraMap A (DualNumber A)).comp f)) ![DualNumber.eps, -1, 0]) :
    ∃ h', spMap (epsScaleR c) ≫
        ptHom W ((algebraMap A (DualNumber A)).comp f) ![DualNumber.eps, -1, 0] h =
      ptHom W ((algebraMap A (DualNumber A)).comp f) ![TrivSqZeroExt.inr c, -1, 0] h' := by
  have hρ : (epsScaleR c).comp ((algebraMap A (DualNumber A)).comp f) =
      (algebraMap A (DualNumber A)).comp f := by
    ext a <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
  have hP : (epsScaleR c ∘ ![DualNumber.eps, -1, 0]) = ![TrivSqZeroExt.inr c, -1, 0] := by
    ext1 j; fin_cases j
    · ext <;> simp [epsScaleR]
    · simp
    · simp
  have h₁ := h.map_comp (epsScaleR c)
  rw [hρ, hP] at h₁
  exact ⟨h₁, (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ hρ hP _)⟩

theorem isLieComb_one_iff {G : Over (Sp A)} [GrpObj G] (c : Fin 1 → A) (v w : epsR A ⟶ G) :
    IsLieComb c ![v] w ↔ w.left = spMap (epsScaleR (c 0)) ≫ v.left := by
  constructor
  · rintro ⟨u, hu, rfl⟩
    simpa using hu 0
  · intro hw
    refine ⟨![w], fun i => ?_, by simp⟩
    fin_cases i
    exact hw

theorem isLieBasis_eps : ∀ (R : Type) [CommRing R] (W : WeierstrassCurve R) (R' : Type) [CommRing R'] (f : R →+* R') (A : Over (Sp R')) [GrpObj A] (φ : A.left ⟶ scheme W) (v : epsR R' ⟶ A) (h : IsUnimodularSol (W.map ((algebraMap R' (DualNumber R')).comp f)) ![DualNumber.eps, -1, 0]), IsPullback φ A.hom (toSpec W) (spMap f) → eSec A ≫ φ = spMap f ≫ zero W → v.left ≫ φ = ptHom W ((algebraMap R' (DualNumber R')).comp f) ![DualNumber.eps, -1, 0] h → IsLieBasis ![v] := by
  intro R _ W R' _ f A _ φ v h hpb he hv
  have hover : ∀ w : epsR R' ⟶ A, w.left ≫ A.hom = spMap (algebraMap R' (DualNumber R')) :=
    fun w => Over.w w
  have hη : η[A].left ≫ A.hom = 𝟙 (Sp R') := Over.w η[A]
  have he' : η[A].left ≫ φ = spMap f ≫ zero W := he
  constructor
  · intro i
    fin_cases i
    change spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ v.left = η[A].left
    refine hpb.hom_ext ?_ ?_
    · rw [Category.assoc, hv, he', SpecMap_zero_origin W f (isUnimodularSol_zero_neg _)]
      refine (SpecMap_ptHom W _ _ h _).trans (ptHom_congr W _ _ _ ?_ ?_ _)
      · ext a; simp [TrivSqZeroExt.algebraMap_eq_inl]
      · ext1 j; fin_cases j <;> simp
    · rw [Category.assoc, hover, hη, ← Spec.map_comp, ← Spec.map_id]
      congr 1
  · intro w hw
    have hw' : spMap (TrivSqZeroExt.fstHom R' R' R').toRingHom ≫ w.left = η[A].left := hw
    obtain ⟨c, hc, hwc⟩ := exists_eq_ptHom_eps W f (w.left ≫ φ)
      (by rw [Category.assoc, hpb.w, ← Category.assoc, hover, ← Spec.map_comp]; rfl)
      (by rw [← Category.assoc, hw', he'])
    have key : ∀ a : R', w.left = spMap (epsScaleR a) ≫ v.left ↔ a = c := by
      intro a
      obtain ⟨ha, hea⟩ := epsScale_ptHom W f a h
      constructor
      · intro e
        rw [e, Category.assoc, hv, hea] at hwc
        exact TrivSqZeroExt.inr_injective (ptHom_origin_inj W _ _ hwc).1
      · rintro rfl
        refine hpb.hom_ext ?_ ?_
        · rw [Category.assoc, hv, hea, hwc]
        · rw [Category.assoc, hover, hover, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
          congr 2
          ext b <;> simp [epsScaleR, TrivSqZeroExt.algebraMap_eq_inl]
    refine ⟨fun _ => c, (isLieComb_one_iff _ _ _).mpr ((key c).mpr rfl), fun c' hc' => ?_⟩
    funext i
    fin_cases i
    exact (key _).mp ((isLieComb_one_iff _ _ _).mp hc')

end GlobalTheory.WeierstrassCurve.OriginTangent
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LogPiSubMeanLogLatticeNormDisc
section
open NumberField
open scoped nonZeroDivisors UpperHalfPlane

namespace GlobalTheory

theorem IsIdealClassPoint.exists_lattice_eq {K : Type} [Field K] [NumberField K] {σ : K →+* ℂ}
    {𝔟 : (Ideal (𝓞 K))⁰} {τ : ℍ} (hτ : IsIdealClassPoint σ (ClassGroup.mk0 𝔟) τ)
    {P : PeriodPair} (hP : ∀ z, z ∈ P.lattice ↔ ∃ a ∈ (𝔟 : Ideal (𝓞 K)), z = σ (a : K)) :
    ∃ a : ℂ, a ≠ 0 ∧ ∀ x, x ∈ P.lattice ↔ ∃ m n : ℤ, a * (m * (τ : ℂ) + n) = x := by
  classical
  obtain ⟨𝔞, ω, h𝔞, hω⟩ := hτ
  set J := FractionalIdeal.mk0 K 𝔟 with hJ
  have hcl : ClassGroup.mk K (𝔞⁻¹ * J) = 1 := by
    rw [map_mul, map_inv, h𝔞, hJ, ClassGroup.mk_mk0, inv_mul_cancel]
  obtain ⟨x₀, hx₀⟩ := (ClassGroup.mk_eq_one_iff.1 hcl).principal

  have hJx : ((J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
      FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ * (𝔞 : FractionalIdeal (𝓞 K)⁰ K) := by
    have h1 : ((𝔞⁻¹ * J : (FractionalIdeal (𝓞 K)⁰ K)ˣ) : FractionalIdeal (𝓞 K)⁰ K) =
        FractionalIdeal.spanSingleton (𝓞 K)⁰ x₀ := by
      apply FractionalIdeal.coeToSubmodule_injective
      dsimp only
      rw [FractionalIdeal.coe_spanSingleton]
      exact hx₀
    have h2 : J = 𝔞 * (𝔞⁻¹ * J) := (mul_inv_cancel_left 𝔞 J).symm
    conv_lhs => rw [h2]
    rw [Units.val_mul, h1, mul_comm]
  have hmemJ : ∀ y : K, (∃ b ∈ (𝔟 : Ideal (𝓞 K)), (b : K) = y) ↔
      ∃ y' ∈ (𝔞 : FractionalIdeal (𝓞 K)⁰ K), y = x₀ * y' := by
    intro y
    rw [← FractionalIdeal.mem_singleton_mul, ← hJx, hJ, FractionalIdeal.coe_mk0,
      FractionalIdeal.mem_coeIdeal]
  have hmem : ∀ z, z ∈ P.lattice ↔ ∃ m n : ℤ, σ x₀ * ω * (m * (τ : ℂ) + n) = z := by
    intro z
    rw [hP]
    constructor
    · rintro ⟨b, hb, rfl⟩
      obtain ⟨y', hy', hby⟩ := (hmemJ _).1 ⟨b, hb, rfl⟩
      obtain ⟨m, n, hmn⟩ := (hω (σ y')).1 ⟨y', hy', rfl⟩
      exact ⟨m, n, by rw [hby, map_mul, ← hmn]; ring⟩
    · rintro ⟨m, n, rfl⟩
      obtain ⟨y', hy', hy'eq⟩ := (hω (ω * (m * (τ : ℂ) + n))).2 ⟨m, n, rfl⟩
      obtain ⟨b, hb, hbeq⟩ := (hmemJ (x₀ * y')).2 ⟨y', hy', rfl⟩
      exact ⟨b, hb, by rw [hbeq, map_mul, hy'eq]; ring⟩
  refine ⟨σ x₀ * ω, ?_, hmem⟩
  intro ha
  obtain ⟨m, n, hmn⟩ := (hmem P.ω₁).1 P.ω₁_mem_lattice
  rw [ha, zero_mul] at hmn
  exact P.indep.ne_zero 0 (by simpa using hmn.symm)

theorem log_pi_sub_mean_log_latticeNormDisc :
    ∀ (K : Type) [Field K] [NumberField K], Module.finrank ℚ K = 2 → ∀ (σ₀ : K →+* ℂ), ¬ ComplexEmbedding.IsReal σ₀ → ∀ (𝔟 : ClassGroup (𝓞 K) → nonZeroDivisors (Ideal (𝓞 K))), ∀ (Lc : ClassGroup (𝓞 K) → PeriodPair), (∀ C, ClassGroup.mk0 (𝔟 C) = C) → (∀ C z, z ∈ (Lc C).lattice ↔ ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = σ₀ (a : K)) → ∀ (σ : K →+* ℂ) (τ : ClassGroup (𝓞 K) → ℍ), (∀ C, IsIdealClassPoint σ C (τ C)) → Real.log Real.pi - (∑ C, Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 * ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖)) / (6 * Fintype.card (ClassGroup (𝓞 K))) = (∑ C, -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4)) / classNumber K := by
  intro K _ _ hK σ₀ h₀ 𝔟 Lc h𝔟 hL σ τ hτ
  classical

  have key : ∀ C, Real.log Real.pi - Real.log (|((Lc C).ω₁ * starRingEnd ℂ (Lc C).ω₂).im| ^ 6 *
      ‖(Lc C).g₂ ^ 3 - 27 * (Lc C).g₃ ^ 2‖) / 6 =
      -Real.log (4 * Real.pi * (τ C).im * ‖ModularForm.eta (τ C)‖ ^ 4) := by
    intro C
    have hτC : IsIdealClassPoint σ (ClassGroup.mk0 (𝔟 C)) (τ C) := by
      rw [h𝔟 C]
      exact hτ C
    rcases embedding_eq_or_eq_conjugate hK h₀ σ with rfl | rfl
    · obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq (hL C)
      exact log_pi_sub_log_latticeNormDisc ha h
    · have hP : ∀ z, z ∈ (conjPeriods (Lc C)).lattice ↔
          ∃ a ∈ (𝔟 C : Ideal (𝓞 K)), z = ComplexEmbedding.conjugate σ₀ (a : K) := by
        intro z
        rw [mem_conjPeriods_lattice, hL]
        refine exists_congr fun a => and_congr_right fun _ => ?_
        rw [ComplexEmbedding.conjugate_coe_eq]
        constructor
        · intro h
          rw [← h, Complex.conj_conj]
        · intro h
          rw [h, Complex.conj_conj]
      obtain ⟨a, ha, h⟩ := hτC.exists_lattice_eq hP
      have e := log_pi_sub_log_latticeNormDisc ha h
      rw [← latticeNormDisc_eq, latticeNormDisc_conjPeriods, latticeNormDisc_eq] at e
      exact e
  have hh : (Fintype.card (ClassGroup (𝓞 K)) : ℝ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  simp_rw [← key]
  rw [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Finset.sum_div]
  simp only [NumberField.classNumber]
  field_simp

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolFibreIdCompCancel
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

namespace PolFibre

variable {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R'']

theorem dualMapR_id : Chart.dualMapR (RingHom.id R) = RingHom.id _ := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem dualMapR_comp (f : R →+* R') (g : R' →+* R'') :
    (Chart.dualMapR g).comp (Chart.dualMapR f) = Chart.dualMapR (g.comp f) := by
  refine RingHom.ext fun a => ?_
  ext <;> simp [Chart.dualMapR]

theorem spMap_dual_hom (f : R →+* R') : spMap (Chart.dualMapR f) ≫ (epsR R).hom = (epsR R').hom ≫ spMap f := by
  refine (spMap_comp_spMap _ _).trans (Eq.trans ?_ (spMap_comp_spMap _ _).symm)
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

theorem lbIso_pull_comp {X Y Z : Scheme.{0}} {L : LB X} {M : LB Y} {φ : Y ⟶ X} (h : LBIso (L.pull φ) M) (ψ : Z ⟶ Y) :
    LBIso (L.pull (ψ ≫ φ)) (M.pull ψ) :=
  LBIso.chartPull (chartPullSame L _ _ _ ψ fun _ => rfl) (chartPullPull M ψ ψ rfl) h

theorem refl (P : Out.PolAV (Sp R)) : IsPolFibre (RingHom.id R) P P (𝟙 _) :=
  haveI : IsMonHom (Iso.refl P.A).hom := inferInstanceAs (IsMonHom (𝟙 _))
  ⟨rfl, (isGrpPullback_of_iso (Iso.refl P.A)).congr (Spec.map_id (CommRingCat.of R)).symm rfl,
    LBIso.chartPull (chartPullPull P.L _ (𝟙 _) rfl) (chartPullId P.L) (PolBaseChange.lbIso_refl P.isLB)⟩

theorem vec_refl {A : Over (Sp R)} (v : epsR R ⟶ A) : IsVecOver (RingHom.id R) (𝟙 _) v v := by
  unfold IsVecOver
  rw [dualMapR_id, Category.comp_id]
  exact (Category.id_comp _).symm.trans (congrArg (· ≫ v.left) (Spec.map_id (CommRingCat.of (DualNumber R))).symm)

variable {f : R →+* R'} {g : R' →+* R''} {P : Out.PolAV (Sp R)} {P' : Out.PolAV (Sp R')} {P'' : Out.PolAV (Sp R'')}
  {φ : P'.A.left ⟶ P.A.left}

theorem comp (h : IsPolFibre f P P' φ) {ψ : P''.A.left ⟶ P'.A.left} (h' : IsPolFibre g P' P'' ψ) :
    IsPolFibre (g.comp f) P P'' (ψ ≫ φ) :=
  ⟨h'.1.trans h.1, (h'.2.1.comp h.2.1).congr (spMap_comp_spMap f g) rfl,
    LBIso.trans (pull_isLB P.isLB _) (pull_isLB P'.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ) h'.2.2⟩

theorem cancel (h : IsPolFibre f P P' φ) {χ : P''.A.left ⟶ P.A.left} (h' : IsPolFibre (g.comp f) P P'' χ) :
    ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ := by
  have n := h'.2.1.congr (spMap_comp_spMap f g).symm rfl
  have w : χ ≫ P.A.hom = (P''.A.hom ≫ spMap g) ≫ spMap f := n.1.w.trans (Category.assoc _ _ _).symm
  have e₁ := h.2.1.1.lift_fst _ _ w
  have e₂ := h.2.1.1.lift_snd _ _ w
  generalize h.2.1.1.lift _ _ w = ψ at e₁ e₂
  subst e₁
  exact ⟨ψ, ⟨h'.1.trans h.1.symm, h.2.1.cancel n e₂,
    LBIso.trans (pull_isLB P'.isLB _) (pull_isLB P.isLB _) P''.isLB (lbIso_pull_comp h.2.2 ψ).symm h'.2.2⟩, rfl⟩

theorem vec_iff {A : Over (Sp R)} {A' : Over (Sp R')} {A'' : Over (Sp R'')} {φ : A'.left ⟶ A.left}
    (hφ : IsPullback φ A'.hom A.hom (spMap f)) {ψ : A''.left ⟶ A'.left} {v : epsR R ⟶ A} {v' : epsR R' ⟶ A'}
    {v'' : epsR R'' ⟶ A''} (w : ψ ≫ A'.hom = A''.hom ≫ spMap g) (h : IsVecOver f φ v v') :
    IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'' := by
  have e : (spMap (Chart.dualMapR g) ≫ v'.left) ≫ φ = spMap (Chart.dualMapR (g.comp f)) ≫ v.left := by
    rw [Category.assoc, h, ← Category.assoc, ← dualMapR_comp]
    exact congrArg (· ≫ v.left) (spMap_comp_spMap _ _)
  refine ⟨fun h' => ?_, fun h' => hφ.hom_ext ?_ ?_⟩
  · exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ φ) h').trans e)
  · exact (Category.assoc _ _ _).trans (Eq.trans h' e.symm)
  · rw [Category.assoc, Category.assoc, w, Over.w v', ← Category.assoc, Over.w v'']
    exact (spMap_dual_hom g).symm

end PolFibre

theorem polFibre_id_comp_cancel : (∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A), IsPolFibre (RingHom.id R) P P (𝟙 _) ∧ IsVecOver (RingHom.id R) (𝟙 _) v v) ∧ ∀ (R R' R'' : Type) [CommRing R] [CommRing R'] [CommRing R''] (f : R →+* R') (g : R' →+* R'') (P : Out.PolAV (Sp R)) (P' : Out.PolAV (Sp R')) (P'' : Out.PolAV (Sp R'')) (φ : P'.A.left ⟶ P.A.left), IsPolFibre f P P' φ → (∀ ψ : P''.A.left ⟶ P'.A.left, IsPolFibre g P' P'' ψ → IsPolFibre (g.comp f) P P'' (ψ ≫ φ)) ∧ (∀ χ : P''.A.left ⟶ P.A.left, IsPolFibre (g.comp f) P P'' χ → ∃ ψ, IsPolFibre g P' P'' ψ ∧ ψ ≫ φ = χ) ∧ ∀ (ψ : P''.A.left ⟶ P'.A.left) (v : epsR R ⟶ P.A) (v' : epsR R' ⟶ P'.A) (v'' : epsR R'' ⟶ P''.A), ψ ≫ P'.A.hom = P''.A.hom ≫ spMap g → IsVecOver f φ v v' → (IsVecOver g ψ v' v'' ↔ IsVecOver (g.comp f) (ψ ≫ φ) v v'') :=
  ⟨fun _ _ P v => ⟨PolFibre.refl P, PolFibre.vec_refl v⟩, fun _ _ _ _ _ _ _ _ _ _ _ _ h =>
    ⟨fun _ h' => PolFibre.comp h h', fun _ h' => PolFibre.cancel h h',
      fun _ _ _ _ w hv => PolFibre.vec_iff h.2.1.1 w hv⟩⟩

end GlobalTheory
end
end

