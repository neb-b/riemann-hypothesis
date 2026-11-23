module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0525
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0548
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonoSpMapRingOfIntegersAlt
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0547
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0543
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0026
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SumMulEqZeroOfSumToReal
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PushInvertibleModelOfIso
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0544
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.IsValLineLogNormAtIffEmbedding
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.UnifMetricScalar
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0021
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.HasSumPolyDerivMulProdAddMatrix
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.Bundle0131
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.BCTools
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HermFormPeriodsAlternatingNondegRankEqTwoMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem hermForm_conj_symm_of_isHermitian {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (z w : Fin g → ℂ) : hermForm Hm w z = star (hermForm Hm z w) := by
  simp only [hermForm, dotProduct, Matrix.mulVec, star_sum, star_mul', star_star, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  have := hH.apply i j
  rw [← this]
  simp only [star_star, Pi.star_apply]
  ring

noncomputable def hermFormImBilin {g : ℕ} (Hm : Matrix (Fin g) (Fin g) ℂ) :
    (Fin g → ℂ) →ₗ[ℝ] (Fin g → ℂ) →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ (fun y w => (hermForm Hm y w).im)
    (fun a b w => by simp [hermForm, add_dotProduct])
    (fun c a w => by simp [hermForm, smul_dotProduct, Complex.smul_im])
    (fun y a b => by simp [hermForm, Matrix.mulVec_add, dotProduct_add])
    (fun c y a => by
      simp [hermForm, star_smul, Matrix.mulVec_smul, dotProduct_smul, Complex.smul_im])

theorem hermForm_periods_alternating_nondeg :
    ∀ (g r : ℕ) (x : Fin r → Fin g → ℂ) (M : Matrix (Fin r) (Fin r) ℝ) (Hm : Matrix (Fin g) (Fin g) ℂ), LinearIndependent ℝ x → Submodule.span ℝ (Set.range x) = ⊤ → Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (hermForm Hm z z).re) → (∀ i j, (hermForm Hm (x i) (x j)).im = M i j) → Mᵀ = -M ∧ M.det ≠ 0 ∧ r = 2 * g := by
  intro g r x M Hm hli hsp hH hpos hM
  have hanti : Mᵀ = -M := by
    ext i j
    simp only [Matrix.transpose_apply, Matrix.neg_apply, ← hM]
    rw [hermForm_conj_symm_of_isHermitian Hm hH]
    simp
  refine ⟨hanti, ?_, ?_⟩
  · intro hdet
    obtain ⟨v, hv0, hv⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
    set z : Fin g → ℂ := ∑ j, v j • x j with hz
    have hz0 : z ≠ 0 := by
      intro h0
      apply hv0
      funext j
      exact Fintype.linearIndependent_iff.mp hli v h0 j
    have hxi : ∀ i, hermFormImBilin Hm (x i) z = 0 := by
      intro i
      have : hermFormImBilin Hm (x i) z = ∑ j, v j * M i j := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [hz, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [map_smul, smul_eq_mul, ← hM i j]
        rfl
      rw [this]
      have := congrFun hv i
      simpa [Matrix.mulVec, dotProduct, mul_comm] using this
    have hall : ∀ y, hermFormImBilin Hm y z = 0 := by
      have hle : Submodule.span ℝ (Set.range x) ≤ LinearMap.ker ((hermFormImBilin Hm).flip z) := by
        rw [Submodule.span_le]
        rintro _ ⟨i, rfl⟩
        simpa using hxi i
      intro y
      have hy : y ∈ Submodule.span ℝ (Set.range x) := by rw [hsp]; trivial
      simpa using hle hy
    have h1 := hall (Complex.I • z)
    have h2 : hermFormImBilin Hm (Complex.I • z) z = (hermForm Hm z z).re := by
      show (hermForm Hm (Complex.I • z) z).im = _
      simp [hermForm, smul_dotProduct]
    have := hpos z hz0
    linarith
  · have h1 := finrank_span_eq_card hli
    rw [hsp, finrank_top, Module.finrank_pi_fintype] at h1
    simp [Complex.finrank_real_complex] at h1
    omega

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsExponentialModelFiberOfUniformisationExp
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Hor.LogCh

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ShFam.Hor.LogCh

open ReciprocityTheory.ChartRestriction.G.PullbackSections.ExpRows (isDerivAt0_comp_hom isDerivAt0_unique)
open GlobalTheory.TrueCx.TorFrHolo (isDerivAt0_of_cart isHolTo_lift)

section Push

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Z : Model Xo c β) {g : ℕ}
  {ty : Fin g → (E →+* ℂ)} {σ₀ : KA l →+* ℂ} (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n)
  (P : (Fu.Di i).La →+ (Fin g → ℂ))

theorem isHolTo_ex_fixed (hP : IsPeriod (Fu.Di i) ty P) : IsHolTo Set.univ fun z => (Fu.ex i P z).left := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  exact GlobalTheory.LocLift.isHolTo_comp h1 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isHolTo_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) :
    IsHolTo Set.univ fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ := by
  have h1 := (Fu.hol i 0 Set.univ (fun _ => P) isOpen_univ
    ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2
  have h2 := isHolTo_lift Z.m0.toSABMap.cart.1 isOpen_univ (fun _ z => (Fu.ex i P z).left) (fun _ => y) h1
    (ReciprocityTheory.ChartRestriction.G.PullbackSections.ThetaHol.isHolTo_const y) (fun _ z => by rw [Over.w (Fu.ex i P z), ← hu]; rfl)
  have h3 := ReciprocityTheory.ChartRestriction.G.PullbackSections.isHolTo_comp h2 Z.m.φ
  exact GlobalTheory.LocLift.isHolTo_comp h3 isOpen_univ (β := fun z => ((0 : Fin 0 → ℂ), z)) (by fun_prop)
    fun _ _ => ⟨trivial, trivial⟩

theorem isDerivAt0_liftEx (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ)) :
    IsDerivAt0 (liftEx Z Fu y i P hu) w v :=
  isDerivAt0_of_cart Z.m0.toSABMap.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (by simpa only [liftEx_fst] using isHolTo_ex_fixed Fu i P hP) hv
    (by simpa only [liftEx_fst] using hd)

theorem isDerivAt0_ex_of_push (hP : IsPeriod (Fu.Di i) ty P)
    (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom))
    {w : Fin g → ℂ} {v : Sp (DualNumber ℂ) ⟶ Z.oF.t.G.left}
    (hv : v ≫ Z.oF.t.G.hom = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y)
    (hd : IsDerivAt0 (fun z => liftEx Z Fu y i P hu z ≫ Z.m.φ) w (v ≫ Z.m.φ)) :
    IsDerivAt0 (fun z => (Fu.ex i P z).left) w (v ≫ Z.m0.toSABMap.φ) := by
  have h := isDerivAt0_comp_hom (isDerivAt0_of_cart Z.m.cart.1 y (fun z => liftEx_snd Z Fu y i P hu z)
    (isHolTo_liftEx Z Fu y i P hP hu) hv hd) Z.m0.toSABMap.φ
  simpa only [liftEx_fst] using h

end Push

theorem isExpAt_pushEx : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (O : Type) [CommRing O] (β : O →+* c.F) (Z : Model Xo c β) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (σ₀ : KA l →+* ℂ) (Fu : FamilyUnif Xo σ₀ ty) (y : Sp ℂ ⟶ Xo.XF c) (i : Fin Fu.n) (P : (Fu.Di i).La →+ (Fin g → ℂ)) (p : Sp ℂ ⟶ Z.X) (hu : Fu.u i P = y ≫ pullback.fst Xo.s (spMap (IntermediateField.inclusion c.le).toRingHom)) (hp : y ≫ Z.jQ ≫ pullback.fst Z.s (spMap β) = p), IsPeriod (Fu.Di i) ty P → IsExpAt Z.t p (pushEx Z Fu y i P p hu hp) := by
  intro E _ _ _ H Dw l Xo c O _ β Z g ty σ₀ Fu y i P p hu hp hP
  subst hp
  obtain ⟨t1, t2, t3⟩ := GlobalTheory.isDerivAt0_ex_isTanAt E H Dw l Xo σ₀ g ty Fu i P hP
  refine ⟨fun a b => ?_, fun w => ?_, fun v hv => ?_⟩
  · let L : (Fin g → ℂ) → (Over.mk y ⟶ Z.oF.t.G) := fun z =>
      Over.homMk (liftEx Z Fu y i P hu z) (liftEx_snd Z Fu y i P hu z)
    have hL : (L (a + b)).left = (L a * L b).left := by
      refine Z.m0.toSABMap.cart.1.hom_ext ?_ ?_
      · have e1 := Z.m0.toSABMap.cart.2 (Over.mk y) (L a) (L b) (pushPt Z.m0.toSABMap.cart.1.w (L a))
          (pushPt Z.m0.toSABMap.cart.1.w (L b)) rfl rfl
        refine Eq.trans ?_ e1
        refine (liftEx_fst Z Fu y i P hu (a + b)).trans ?_
        rw [Fu.ex_add i P hP]
        exact mul_left_congr hu _ _ _ _ (liftEx_fst Z Fu y i P hu a).symm (liftEx_fst Z Fu y i P hu b).symm
      · rw [Over.w, Over.w]
    refine Over.OverMorphism.ext ?_
    have e2 := Z.m.cart.2 (Over.mk y) (L a) (L b) (pushEx Z Fu y i P _ hu rfl a) (pushEx Z Fu y i P _ hu rfl b) rfl rfl
    refine Eq.trans ?_ e2.symm
    exact congrArg (· ≫ Z.m.φ) hL
  · obtain ⟨v, hv, -⟩ := t2 w
    have ht := t1 w v hv
    obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m0.toSABMap (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [ht.1, hu, Category.assoc])
    refine ⟨v' ≫ Z.m.φ, ⟨(GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).2
      ((GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).1 ht),
      isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ⟩, fun v₂ hv₂ => ?_⟩
    exact isDerivAt0_unique hv₂.2 (isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hv) Z.m.φ)
  · obtain ⟨v', k1, rfl⟩ := GlobalTheory.ShFam.OpenReg.exists_lift Z.m (spMap (algebraMap ℂ (DualNumber ℂ)) ≫ y) v
      (by rw [hv.1, Category.assoc])
    have h1 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m rfl k1).1 hv
    have h2 := (GlobalTheory.ShFam.OpenReg.tan_iff Z.m0.toSABMap hu.symm k1).2 h1
    obtain ⟨w, hw, hw'⟩ := t3 _ h2
    exact ⟨w, isDerivAt0_comp_hom (isDerivAt0_liftEx Z Fu y i P hP hu k1 hw) Z.m.φ,
      fun w' h' => hw' w' (isDerivAt0_ex_of_push Z Fu y i P hP hu k1 h')⟩

end GlobalTheory.ShFam.Hor.LogCh
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLatBasisOfClosedBall
section
set_option autoImplicit false

namespace GlobalTheory.LatticeBasisClosedBall

theorem exists_real_coords {g : ℕ} (lam : Fin (2 * g) → Fin g → ℂ) (hli : LinearIndependent ℝ lam)
    (w : Fin g → ℂ) : ∃ c : Fin (2 * g) → ℝ, ∑ j, c j • lam j = w := by
  have hdim : Fintype.card (Fin (2 * g)) = Module.finrank ℝ (Fin g → ℂ) := by
    rw [Module.finrank_pi_fintype]
    simp [Complex.finrank_real_complex, mul_comm]
  have hspan : Submodule.span ℝ (Set.range lam) = ⊤ := hli.span_eq_top_of_card_eq_finrank' hdim
  have hw : w ∈ Submodule.span ℝ (Set.range lam) := hspan ▸ Submodule.mem_top
  exact (Submodule.mem_span_range_iff_exists_fun ℝ).1 hw

theorem isLatBasis_of_closedBall : ∀ {g : ℕ} (H : AddSubgroup (Fin g → ℂ)) (lam : Fin (2 * g) → Fin g → ℂ)
    (R : ℝ), LinearIndependent ℝ lam → (∀ j : Fin (2 * g), lam j ∈ H) → ∑ j : Fin (2 * g), ‖lam j‖ ≤ R →
    (∀ w ∈ Metric.closedBall (0 : Fin g → ℂ) R, w ∈ H →
      ∃ m : Fin (2 * g) → ℤ, w = ∑ j : Fin (2 * g), m j • lam j) →
    GlobalTheory.ShFam.Hor.LogCh.IsLatBasis (↑H : Set (Fin g → ℂ)) lam := by
  intro g H lam R hli hmem hR hball
  have hint : ∀ m : Fin (2 * g) → ℤ, ∑ j, m j • lam j ∈ H := fun m =>
    H.sum_mem fun j _ => H.zsmul_mem (hmem j) (m j)
  refine ⟨hli, fun w => ⟨fun hw => ?_, ?_⟩⟩
  · obtain ⟨c, hc⟩ := exists_real_coords lam hli w
    have hsplit : w - ∑ j, ⌊c j⌋ • lam j = ∑ j, Int.fract (c j) • lam j := by
      rw [← hc, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
    have hH : w - ∑ j, ⌊c j⌋ • lam j ∈ H := H.sub_mem hw (hint _)
    have hnorm : w - ∑ j, ⌊c j⌋ • lam j ∈ Metric.closedBall (0 : Fin g → ℂ) R := by
      rw [mem_closedBall_zero_iff, hsplit]
      refine (norm_sum_le _ _).trans (le_trans (Finset.sum_le_sum fun j _ => ?_) hR)
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
      exact mul_le_of_le_one_left (norm_nonneg _) (Int.fract_lt_one _).le
    obtain ⟨m, hm⟩ := hball _ hnorm hH
    refine ⟨fun j => m j + ⌊c j⌋, ?_⟩
    simp only [add_smul, Finset.sum_add_distrib]
    rw [← hm, sub_add_cancel]
  · rintro ⟨m, rfl⟩
    exact hint m

end GlobalTheory.LatticeBasisClosedBall
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPartOfBasisOfInjective
section
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan

namespace GlobalTheory.PolFan

theorem isPartOfBasis_of_injective {L L' : Type} [AddCommGroup L] [AddCommGroup L'] {m : ℕ} (f : L →ₗ[ℤ] L')
    (hf : Function.Injective f) {v : Fin m → L} (h : IsPartOfBasis fun i => f (v i)) : IsPartOfBasis v := by
  classical
  obtain ⟨ψ, hψ⟩ := h.exists_dual
  obtain ⟨n', b, -⟩ := h
  let π : L →ₗ[ℤ] (Fin m → ℤ) := LinearMap.pi fun i => ψ i ∘ₗ f
  let s : (Fin m → ℤ) →ₗ[ℤ] L := ∑ i, (LinearMap.proj i : (Fin m → ℤ) →ₗ[ℤ] ℤ).smulRight (v i)
  have hs : ∀ c, s c = ∑ i, c i • v i := fun c => by simp [s, LinearMap.sum_apply]
  have hπ : ∀ c, π (s c) = c := fun c => by
    ext j
    set_option synthInstance.maxHeartbeats 100000 in
      simp [π, hs, map_sum, hψ]
  let K := LinearMap.ker π
  obtain ⟨n, bK'⟩ := Submodule.basisOfPid b (K.map f)
  let bK := bK'.map (Submodule.equivMapOfInjective f hf K).symm
  have hinj : Function.Injective (s.coprod K.subtype) := by
    refine (injective_iff_map_eq_zero _).2 ?_
    rintro ⟨c, k⟩ h0
    have h1 : s c + (k : L) = 0 := by simpa using h0
    have h2 : π (k : L) = 0 := k.2
    have h3 : c = 0 := by simpa [h2, hπ] using congrArg π h1
    subst h3
    have h4 : (k : L) = 0 := by simpa using h1
    exact Prod.ext rfl (Subtype.ext h4)
  have hsurj : Function.Surjective (s.coprod K.subtype) := fun x =>
    ⟨(π x, ⟨x - s (π x), by simp [K, LinearMap.mem_ker, hπ]⟩), by simp⟩
  let E : ((Fin m → ℤ) × K) ≃ₗ[ℤ] L := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨n, ((Pi.basisFun ℤ (Fin m)).prod bK).map E, fun i => ?_⟩
  have h1 : E (Pi.single i 1, 0) = v i := by
    change (s.coprod K.subtype) (Pi.single i 1, 0) = v i
    simp [hs, Pi.single_apply]
  simpa using h1

theorem isCone_of_pull : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X X₁ : Type) [AddCommGroup X] [Module O X]
    [Module.Finite O X] [AddCommGroup X₁] [Module O X₁] [Module.Finite O X₁] (r : X →ₗ[O] X₁) (m : ℕ)
    (γ : Fin m → LinearMap.BilinForm ℤ X₁), Function.Surjective r → IsCone bar φ (fun i => pull r (γ i)) →
    IsCone bar φ γ := by
  intro O _ bar φ X X₁ _ _ _ _ _ _ r m γ hr h
  have hmem : ∀ i, γ i ∈ balForms bar X₁ := fun i => by
    refine ⟨fun y z => ?_, fun a y z => ?_⟩
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      exact (h.mem i).1 y z
    · obtain ⟨y, rfl⟩ := hr y
      obtain ⟨z, rfl⟩ := hr z
      simpa only [pull_apply, map_smul] using (h.mem i).2 a y z
  have hinj : Function.Injective (pullBal bar r) := fun β β' e =>
    Subtype.ext (LinearMap.ext₂ fun a b => by
      obtain ⟨a, rfl⟩ := hr a
      obtain ⟨b, rfl⟩ := hr b
      exact LinearMap.congr_fun₂ (congrArg Subtype.val e) a b)
  refine ⟨hmem, fun i y => ?_, isPartOfBasis_of_injective (pullBal bar r) hinj h.basis,
    (linearOn_pull_iff hr).1 h.linear, IsStrict.of_pull hr h.strict⟩
  obtain ⟨y, rfl⟩ := hr y
  exact h.nonneg i y

end GlobalTheory.PolFan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsotropicDualFamilyLinearIndependentRankEqTwoMul
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory GlobalTheory.Toroidal GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.ShFam.Hor GlobalTheory.ShFam.Hor.LogCh
open scoped Matrix CategoryTheory.Obj Topology
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.familyIsotropicDual_linearIndependent_and_card : ∀ (r d : ℕ) (M : Matrix (Fin r) (Fin r) ℝ) (e f : Fin d → Fin r → ℝ), (∀ i j, e i ⬝ᵥ M *ᵥ e j = 0) → (∀ i j, f i ⬝ᵥ M *ᵥ e j = if i = j then 1 else 0) → Submodule.span ℝ (Set.range (Sum.elim e f)) = ⊤ → LinearIndependent ℝ (Sum.elim e f) ∧ r = 2 * d := by
  intro r d M e f hiso hdual hspan
  have hli : LinearIndependent ℝ (Sum.elim e f) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hb : ∀ k, g (Sum.inr k) = 0 := by
      intro k
      have h := congrArg (fun v => v ⬝ᵥ M *ᵥ e k) hg
      simpa [add_dotProduct, sum_dotProduct, smul_dotProduct, hiso, hdual] using h
    have ha : ∀ k, g (Sum.inl k) = 0 := by
      intro k
      have hg' : ∑ i, g (Sum.inl i) • e i = 0 := by simpa [hb] using hg
      have h := congrArg (fun v => f k ⬝ᵥ M *ᵥ v) hg'
      simpa [Matrix.mulVec_sum, Matrix.mulVec_smul, dotProduct_sum, dotProduct_smul, hdual] using h
    rintro (k | k)
    · exact ha k
    · exact hb k
  refine ⟨hli, ?_⟩
  have h1 := finrank_span_eq_card hli
  rw [hspan, finrank_top, Module.finrank_fin_fun, Fintype.card_sum, Fintype.card_fin] at h1
  omega
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KeySectionEqConstMulThetaFunctionFibre
section
open AlgebraicGeometry CategoryTheory Limits NumberField TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM
open GlobalTheory.FlagMod (GChart ev tau tau_le le_preimage_comp)
open scoped LaurentSeries

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.FibreKeyTheta

variable {X : Scheme.{0}}

theorem toStk_valAt' (x : Sp ℂ ⟶ X) (U : X.Opens) (z : Sp ℂ) (h : x z ∈ U) (a : Γ(X, U)) :
    toStk z (valAt' x U a) = gs x z U a := by
  rw [valAt', dite_eq_left ((top_le_iff_mem x U z).2 h), valAt, gs_eq x z U h]
  show ((Sp ℂ).presheaf.germ ⊤ z trivial).hom ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv.hom
    ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom.hom _)) = _
  rw [Iso.hom_inv_id_apply]
  exact TopCat.Presheaf.germ_res_apply (Sp ℂ).presheaf (homOfLE ((top_le_iff_mem x U z).2 h)) z trivial _

theorem cst_id (z : Sp ℂ) (a : ℂ) : cst (𝟙 (Sp ℂ)) z a = toStk z a := by
  rw [cst, gs_eq (𝟙 (Sp ℂ)) z ⊤ trivial]
  rfl

def isoSymm {A B : LB X} (w : LB.Iso A B) : LB.Iso B A :=
  ⟨fun p => (res (fun _ hy => ⟨hy.2, hy.1⟩ : A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹⟩

theorem isoSymm_isGen {A B : LB X} (w : LB.Iso A B) (hw : w.IsGen) : (isoSymm w).IsGen := by
  have le : ∀ p : A.ι × B.ι, A.U p.1 ⊓ B.U p.2 ≤ B.U p.2 ⊓ A.U p.1 := fun p y hy => ⟨hy.2, hy.1⟩
  intro p q
  refine unit_ext fun y hy => ?_
  have hm : (𝟙 X : X ⟶ X) y ∈ B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1) := ⟨le p hy.1, le q hy.2⟩
  have e := congrArg (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1 ⊓ (B.U q.2 ⊓ A.U q.1))) (hw (p.2, p.1) (q.2, q.1))
  have e' := (gm_res _ y _ hm _).symm.trans (e.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·)
    (gm_div A B (𝟙 X) y (p.2, p.1) (q.2, q.1) hm) (gm_res _ y _ hm _))))
  have v : ∀ p : A.ι × B.ι, y ∈ A.U p.1 ⊓ B.U p.2 → gm (𝟙 X) y (A.U p.1 ⊓ B.U p.2) (res (le p) (w.s (p.2, p.1)))⁻¹ =
      (gm (𝟙 X) y (B.U p.2 ⊓ A.U p.1) (w.s (p.2, p.1)))⁻¹ := fun p hp =>
    (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ y _ hp _))
  refine ((gm_res _ y _ hy _).trans ((v p hy.1).trans (congrArg (·⁻¹) e'))).trans (Eq.symm ?_)
  refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) (gm_div B A (𝟙 X) y p q hy)
    ((gm_res _ y _ hy _).trans (v q hy.2)))).trans ?_
  rw [mul_inv, mul_inv, inv_inv, mul_comm (gm (𝟙 X) y _ (A.g p.1 q.1))]
  rfl

end GlobalTheory.FibreKeyTheta


open GlobalTheory.FibreKeyTheta in
theorem GlobalTheory.FibreKeyTheta.th_isFn_const_mul : ∀ (x : KeyIn ℂ) (S : Scheme.{0}) (G : Over S) [GrpObj G] (L : LB G.left) (y : Sp ℂ ⟶ S) (Φ : x.P.A.left ⟶ G.left) (g : ℕ) (u : HolUnif x.P.A x.P.L g) (w : LB.Iso (L.pull Φ) x.P.L) (θ : (Fin g → ℂ) → ℂ) (fr : L.ι → (Fin g → ℂ) → ℂ) (s : (L.pull (pullback.fst G.hom y)).Sec), L.IsLB → IsPullback Φ x.P.A.hom G.hom y → w.IsGen → (∃ z, θ z ≠ 0) → (∀ j z, ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → fr j z ≠ 0) → (∀ k j z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ (x.P.L.U k ⊓ (L.pull Φ).U j) → u.fr k z = valAt' (u.ex z).left (x.P.L.U k ⊓ (L.pull Φ).U j) (w.s (k, j)).val * fr (j PUnit.unit) z) → (∀ j z (p : Sp ℂ ⟶ pullback G.hom y), p ≫ pullback.fst _ _ = (u.ex z).left ≫ Φ → p ≫ pullback.snd _ _ = 𝟙 _ → ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j → valAt' p ((L.pull (pullback.fst G.hom y)).U (fun _ => j)) (s.f (fun _ => j)) = θ z * fr j z) → ∃ c₀ : ℂ, u.IsFn x.th (fun z => c₀ * θ z) := by
  intro x S G _ L y Φ g u w θ fr s hL hΦ hw hθ hfr hu hs
  classical
  let km : x.P.A.left ⟶ pullback G.hom y := pullback.lift Φ x.P.A.hom hΦ.w
  have km1 : km ≫ pullback.fst G.hom y = Φ := pullback.lift_fst _ _ _
  have km2 : km ≫ pullback.snd G.hom y = x.P.A.hom := pullback.lift_snd _ _ _
  have le : ∀ j : L.ι, Φ ⁻¹ᵁ L.U j ≤ km ⁻¹ᵁ (L.pull (pullback.fst G.hom y)).U (fun _ => j) := fun j p hp =>
    mem_pull.2 ((congrArg (fun e => e p ∈ L.U j) km1).mpr hp)
  let σ : ∀ j : L.ι, Γ(x.P.A.left, Φ ⁻¹ᵁ L.U j) := fun j => (km.appLE _ _ (le j)).hom (s.f (fun _ => j))
  have hσv : ∀ {Z : Scheme.{0}} (r : Z ⟶ x.P.A.left) (z : Z) (j : L.ι), Φ (r z) ∈ L.U j →
      gs r z _ (σ j) = gs (r ≫ km) z _ (s.f (fun _ => j)) := fun r z j h =>
    gs_appLE km _ _ (le j) r z h _
  have hσ : ∀ (p : x.P.A.left) j j', Φ p ∈ L.U j → Φ p ∈ L.U j' →
      gs (𝟙 _) p _ (σ j) = (gm Φ p (L.U j ⊓ L.U j') (L.g j j')).val * gs (𝟙 _) p _ (σ j') := by
    intro p j j' h h'
    rw [hσv _ p j h, hσv _ p j' h', Category.id_comp]
    refine (sec_trans s km p (le j h) (le j' h')).trans ?_
    congr 2
    simp [trF, km1]
  have hwD : PGen (isoSymm w) := (isGen_iff _).1 (isoSymm_isGen w hw)
  obtain ⟨s', hs'⟩ := sec_down hwD hL x.P.isLB σ hσ
  have refl : LBIso x.P.L (x.P.L.pull (𝟙 _)) :=
    LBIso.chartPull (chartPullUnpull x.P.L _ rfl) (chartPullId _)
      (exists_iso_linComb (F := 𝟙 x.P.A.left) x.P.isLB (fun _ : PUnit => 𝟙 _) (fun _ => 1) fun _ _ _ => rfl)
  obtain ⟨a, ha, -⟩ := GlobalTheory.SectionBaseChange.generates GlobalTheory.allSixLaws.1.secBaseChange x.P (t := 𝟙 _) (φ := 𝟙 _)
    (IsPullback.of_horiz_isIso ⟨by simp⟩) x.P.isLB refl x.th x.th_ne s'
  obtain ⟨pt⟩ : Nonempty (Sp ℂ) := ⟨(⊥ : PrimeSpectrum ℂ)⟩
  have key : ∀ i z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ x.P.L.U i →
      a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i) = θ z * u.fr i z := by
    intro i z hi
    have hri : (u.ex z).left pt ∈ x.P.L.U i := (top_le_iff_mem _ _ pt).1 hi
    obtain ⟨j, hj⟩ := exists_chart hL (Φ ((u.ex z).left pt))
    have hj' : ⊤ ≤ ((u.ex z).left ≫ Φ) ⁻¹ᵁ L.U j := (top_le_iff_mem _ _ pt).2 hj
    have hr0 : (u.ex z).left ≫ x.P.A.hom = 𝟙 _ := by simpa using Over.w (u.ex z)
    have hr1 : ((u.ex z).left ≫ km) ≫ pullback.snd G.hom y = 𝟙 _ := by rw [Category.assoc, km2, hr0]
    have e1 := hs j z ((u.ex z).left ≫ km) (by rw [Category.assoc, km1]) hr1 hj'
    have hm : (u.ex z).left pt ∈ x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j) := ⟨hri, mem_pull.2 hj⟩
    have e2 := hu i (fun _ => j) z ((top_le_iff_mem _ _ pt).2 hm)
    have e3 := hs' (Sp ℂ) (u.ex z).left pt j i hj hri
    rw [hσv _ pt j hj, ← toStk_valAt' ((u.ex z).left ≫ km) _ pt (le j hj), e1, ha i, gs_mul _ pt _ hri, gs_constFn _ _ _ pt hri,
      hr0] at e3
    erw [cst_id] at e3
    rw [← toStk_valAt' _ _ pt hri] at e3
    have hm' : (u.ex z).left pt ∈ (L.pull Φ).U (fun _ => j) ⊓ x.P.L.U i := ⟨mem_pull.2 hj, hri⟩
    have gwv : gw (isoSymm w) (u.ex z).left pt j i =
        (gm (u.ex z).left pt (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)))⁻¹ :=
      (map_inv _ _).trans (congrArg (·⁻¹) (gm_res _ pt _ hm' _))
    rw [gwv, Units.eq_inv_mul_iff_mul_eq] at e3
    have e3' : toStk pt (valAt' (u.ex z).left (x.P.L.U i ⊓ (L.pull Φ).U (fun _ => j)) (w.s (i, fun _ => j)).val *
        (θ z * fr j z)) = toStk pt (a * valAt' (u.ex z).left (x.P.L.U i) (x.th.f i)) := by
      rw [map_mul, map_mul (toStk pt) a]
      erw [toStk_valAt' _ _ pt hm, gs_unit _ pt _ hm]
      exact e3
    have e4 := (toStk pt).injective e3'
    rw [e2, ← e4]
    ring
  obtain ⟨z0, hz0⟩ := hθ
  obtain ⟨i0, hi0⟩ := exists_chart x.P.isLB ((u.ex z0).left pt)
  have hi0' : ⊤ ≤ (u.ex z0).left ⁻¹ᵁ x.P.L.U i0 := (top_le_iff_mem _ _ pt).2 hi0
  have ha0 : a ≠ 0 := by
    intro h0
    have e := key i0 z0 hi0'
    rw [h0, zero_mul] at e
    exact mul_ne_zero hz0 (u.fr_ne i0 z0 hi0') e.symm
  refine ⟨a⁻¹, fun i z hi => ?_⟩
  have e := key i z hi
  show _ = a⁻¹ * θ z * u.fr i z
  rw [mul_assoc, ← e, ← mul_assoc, inv_mul_cancel₀ ha0, one_mul]
end
end

