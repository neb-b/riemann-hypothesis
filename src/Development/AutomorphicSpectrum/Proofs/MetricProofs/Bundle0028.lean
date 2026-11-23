module

public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsEigFrames
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.Bundle0003
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.StabilizerCovolume.ThreeLeLevel
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GenericBlockMatrixIsBlockDiag
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.FormalDegree.CauchyBinet
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0026
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.EigenComponentPolynomialInAction
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula

variable {E : Type} [Field E] [NumberField E]

theorem emb_injective (s : 𝓞 E →+* ℂ) : Function.Injective s :=
  (RingHom.injective_iff_ker_eq_bot _).2
    (Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (eq_bot_iff.2 fun n hn => by simpa using hn))

def extend (s : 𝓞 E →+* ℂ) : E →+* ℂ := IsFractionRing.lift (K := E) (emb_injective s)

theorem extend_comp (s : 𝓞 E →+* ℂ) : (extend s).comp (algebraMap (𝓞 E) E) = s :=
  RingHom.ext fun x => by rw [RingHom.comp_apply, extend, IsFractionRing.lift_algebraMap]

def chr (t : E →+* ℂ) : 𝓞 E →* ℂ := ((t.comp (algebraMap (𝓞 E) E) : 𝓞 E →+* ℂ) : 𝓞 E →* ℂ)

theorem chr_injective : Function.Injective (chr (E := E)) := fun t t' h =>
  IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 E)) (RingHom.ext fun x => DFunLike.congr_fun h x)

theorem span_eq_top :
    Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) = ⊤ := by
  classical
  by_contra h
  obtain ⟨φ, hφ0, hφ⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 h)
  apply hφ0
  have li := (linearIndependent_monoidHom (𝓞 E) ℂ).comp (chr (E := E)) chr_injective
  have hc := Fintype.linearIndependent_iff.1 li
    (fun t => φ fun j => if t = j then 1 else 0) (by
      funext a
      have h0 : φ (fun t : E →+* ℂ => t (algebraMap (𝓞 E) E a)) = 0 :=
        hφ (Submodule.subset_span ⟨a, rfl⟩)
      rw [LinearMap.pi_apply_eq_sum_univ φ] at h0
      simpa [chr, Finset.sum_apply, mul_comm] using h0)
  refine LinearMap.ext fun w => ?_
  rw [LinearMap.pi_apply_eq_sum_univ φ w]
  simp only [hc, smul_zero, Finset.sum_const_zero, LinearMap.zero_apply]


open Classical in
theorem exists_coeffs (s : 𝓞 E →+* ℂ) : ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ),
    ∀ t : E →+* ℂ, ∑ i, c i * t (algebraMap (𝓞 E) E (a i)) = if t = extend s then 1 else 0 := by
  have hmem : (fun t : E →+* ℂ => if t = extend s then (1 : ℂ) else 0) ∈
      Submodule.span ℂ (Set.range fun (a : 𝓞 E) (t : E →+* ℂ) => t (algebraMap (𝓞 E) E a)) := by
    rw [span_eq_top]; trivial
  obtain ⟨f, hf⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 hmem
  refine ⟨f.support.card, fun i => (f.support.equivFin.symm i).1,
    fun i => f (f.support.equivFin.symm i).1, fun t => ?_⟩
  have ht := congrFun hf t
  rw [Finsupp.sum, Finset.sum_apply] at ht
  rw [← ht]
  refine (Equiv.sum_comp f.support.equivFin.symm
    (fun x : f.support => f x.1 * t (algebraMap (𝓞 E) E x.1))).trans ?_
  exact Finset.sum_coe_sort f.support (fun x => f x * t (algebraMap (𝓞 E) E x))

theorem eigComp_eq_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (s : 𝓞 E →+* ℂ),
    ∃ (N : ℕ) (a : Fin N → 𝓞 E) (c : Fin N → ℂ), ∀ (g : ℕ) (Λ : Type) [AddCommGroup Λ] [Module (𝓞 E) Λ]
      (R : RiemLat E g Λ) (z : Fin g → ℂ), eigComp R.B s z = ∑ i, c i • R.B (a i) z := by
  classical
  intro E _ _ _ s
  obtain ⟨N, a, c, h⟩ := exists_coeffs s
  refine ⟨N, a, c, ?_⟩
  intro g Λ _ _ R z
  obtain ⟨-, -, hs, hsum, -⟩ := _root_.LevelTowerAlt.riemann_lattice_eigen_projections E g Λ Unit R
  have hB : ∀ (b : 𝓞 E) (t : E →+* ℂ), R.B b (eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z) =
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b t
    have hm := (hs (t.comp (algebraMap (𝓞 E) E))).1 z
    simp only [eigSp, Submodule.mem_iInf, LinearMap.mem_ker] at hm
    have := hm b
    simpa [sub_eq_zero] using this
  have hz : ∀ b : 𝓞 E, R.B b z = ∑ t : E →+* ℂ,
      t (algebraMap (𝓞 E) E b) • eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
    intro b
    conv_lhs => rw [← hsum z]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    exact Finset.sum_congr rfl fun t _ => hB b t
  calc eigComp R.B s z
      = ∑ t : E →+* ℂ, (if t = extend s then (1 : ℂ) else 0) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp [extend_comp]
    _ = ∑ t : E →+* ℂ, (∑ i, c i * t (algebraMap (𝓞 E) E (a i))) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [h]
    _ = ∑ i, c i • ∑ t : E →+* ℂ, t (algebraMap (𝓞 E) E (a i)) •
          eigComp R.B (t.comp (algebraMap (𝓞 E) E)) z := by
        simp only [Finset.sum_smul, Finset.smul_sum, mul_smul]
        exact Finset.sum_comm
    _ = ∑ i, c i • R.B (a i) z := by simp only [hz]

end GlobalTheory.CompanionTheory.Ar.Cusp.EigFormula
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsHermitianOrthogonalProjection
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.PosFormProjection

theorem exists_orthogonal_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      ∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ,
        ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm hpos u hli z
  let A : (Fin k → ℂ) →ₗ[ℂ] (Fin k → ℂ) :=
    { toFun := fun c j => (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j)
      map_add' := by
        intro a b
        funext j
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, add_dotProduct]
      map_smul' := by
        intro a b
        funext j
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, ← Finset.smul_sum,
          smul_dotProduct] }
  have hinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro c hc
    have hw : ∀ j, (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := fun j => congrFun hc j
    have hww : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (∑ i, c i • u i) = 0 := by
      rw [star_sum, Matrix.mulVec_sum, dotProduct_sum]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [star_smul, Matrix.mulVec_smul, dotProduct_smul, hw j, smul_zero]
    have hw0 : ∑ i, c i • u i = 0 := by
      by_contra hne
      have := hpos _ hne
      rw [hww] at this
      simp at this
    funext i
    exact Fintype.linearIndependent_iff.mp hli c hw0 i
  obtain ⟨c, hc⟩ := LinearMap.injective_iff_surjective.mp hinj (fun j => z ⬝ᵥ Hm *ᵥ star (u j))
  refine ⟨c, fun j => ?_⟩
  have hcj : (∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = z ⬝ᵥ Hm *ᵥ star (u j) := congrFun hc j
  rw [sub_dotProduct, hcj, sub_self]

end GlobalTheory.CompanionTheory.Ar.PosFormProjection
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsPosDefFormOnQuotient
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.QuotUniv

theorem hermitian_transport_along_orthogonal_complement :
    ∀ (g g' : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ), Hm.IsHermitian → (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) → ∀ (S : Submodule ℂ (Fin g → ℂ)) (q : (Fin g → ℂ) →ₗ[ℂ] (Fin g' → ℂ)), Function.Surjective q → LinearMap.ker q = S → (∀ z : Fin g → ℂ, ∃ s ∈ S, ∀ v ∈ S, (z - s) ⬝ᵥ Hm *ᵥ star v = 0) → ∃ Hm' : Matrix (Fin g') (Fin g') ℂ, Hm'.IsHermitian ∧ (∀ z : Fin g' → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm' *ᵥ star z).re) ∧ ∀ x y : Fin g → ℂ, (∀ v ∈ S, x ⬝ᵥ Hm *ᵥ star v = 0) → q y ⬝ᵥ Hm' *ᵥ star (q x) = y ⬝ᵥ Hm *ᵥ star x := by
  intro g g' Hm hHm hpos S q hq hker hproj
  have hconj : ∀ x y : Fin g → ℂ, star (x ⬝ᵥ Hm *ᵥ star y) = y ⬝ᵥ Hm *ᵥ star x := by
    intro x y
    rw [← Matrix.star_dotProduct_star, Matrix.star_mulVec, star_star, hHm.eq,
      ← Matrix.dotProduct_mulVec]
  have hmemS : ∀ z, q z = 0 → z ∈ S := fun z hz => by
    rw [← hker]
    exact LinearMap.mem_ker.2 hz
  choose z hz using fun i : Fin g' => hq (Pi.single i 1)
  choose s hsS hs using fun i => hproj (z i)
  let A : Matrix (Fin g') (Fin g) ℂ := Matrix.of fun i => z i - s i
  have hAq : ∀ i, q (z i - s i) = Pi.single i 1 := by
    intro i
    have hs0 : q (s i) = 0 := by
      have : s i ∈ LinearMap.ker q := by rw [hker]; exact hsS i
      exact LinearMap.mem_ker.1 this
    rw [map_sub, hz i, hs0, sub_zero]
  have hT : ∀ u : Fin g' → ℂ, Matrix.vecMul u A = ∑ i, u i • (z i - s i) := by
    intro u
    ext a
    simp [A, Matrix.vecMul, dotProduct, Finset.sum_apply]
  have hTq : ∀ u, q (Matrix.vecMul u A) = u := by
    intro u
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hT, map_sum]
    simp_rw [map_smul, hAq]
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  have hTorth : ∀ u, ∀ v ∈ S, Matrix.vecMul u A ⬝ᵥ Hm *ᵥ star v = 0 := by
    intro u v hv
    rw [hT, sum_dotProduct]
    exact Finset.sum_eq_zero fun i _ => by rw [smul_dotProduct, hs i v hv, smul_zero]
  have hkey : ∀ u u' : Fin g' → ℂ, u ⬝ᵥ (A * Hm * A.conjTranspose) *ᵥ star u' =
      Matrix.vecMul u A ⬝ᵥ Hm *ᵥ star (Matrix.vecMul u' A) := by
    intro u u'
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec u A,
      Matrix.star_vecMul]
  have hlift : ∀ x : Fin g → ℂ, (∀ v ∈ S, x ⬝ᵥ Hm *ᵥ star v = 0) →
      Matrix.vecMul (q x) A = x := by
    intro x hx
    have hdS : Matrix.vecMul (q x) A - x ∈ S := hmemS _ (by rw [map_sub, hTq, sub_self])
    have hd0 : (Matrix.vecMul (q x) A - x) ⬝ᵥ Hm *ᵥ star (Matrix.vecMul (q x) A - x) = 0 := by
      rw [sub_dotProduct, hTorth _ _ hdS, hx _ hdS, sub_zero]
    by_contra hne
    have := hpos _ (sub_ne_zero.2 hne)
    rw [hd0, Complex.zero_re] at this
    exact lt_irrefl _ this
  refine ⟨A * Hm * A.conjTranspose, Matrix.isHermitian_mul_mul_conjTranspose A hHm, ?_, ?_⟩
  · intro u hu
    rw [hkey]
    apply hpos
    intro h0
    apply hu
    rw [← hTq u, h0, map_zero]
  · intro x y hx
    rw [hkey, hlift x hx, ← sub_eq_zero, ← sub_dotProduct, ← hconj,
      hx (Matrix.vecMul (q y) A - y) (hmemS _ (by rw [map_sub, hTq, sub_self])), star_zero]

end GlobalTheory.CompanionTheory.Ar.QuotUniv
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ExistsRealOrthogonalProjectionOfRealGram
section
open NumberField Matrix Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.Regular

namespace GlobalTheory.CompanionTheory.Ar.ProjReal

theorem orthogonal_projection_real_coefficients :
    ∀ (g k : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ),
      (∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) →
      ∀ u : Fin k → Fin g → ℂ, LinearIndependent ℂ u →
      (∀ z : Fin g → ℂ, ∃ c : Fin k → ℂ, ∀ j, (z - ∑ i, c i • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0) →
      (∀ i j, (u i ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∀ z : Fin g → ℂ, (∀ j, (z ⬝ᵥ Hm *ᵥ star (u j)).im = 0) →
      ∃ c : Fin k → ℝ, ∀ j, (z - ∑ i, (c i : ℂ) • u i) ⬝ᵥ Hm *ᵥ star (u j) = 0 := by
  intro g k Hm _ u _ hproj hu z hz
  obtain ⟨c, hc⟩ := hproj z
  refine ⟨fun i => (c i).re, fun j => ?_⟩
  have h := hc j
  simp only [sub_dotProduct, sum_dotProduct, smul_dotProduct, smul_eq_mul] at h ⊢
  apply Complex.ext
  · have h' := congrArg Complex.re h
    simp only [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu, mul_zero, sub_zero, Complex.zero_re] at h'
    simpa [Complex.sub_re, Complex.re_sum, Complex.mul_re, hu] using h'
  · simp [Complex.sub_im, Complex.im_sum, Complex.mul_im, hu, hz]

end GlobalTheory.CompanionTheory.Ar.ProjReal
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.HermitianRestrictionOrthonormalCoords
section
open NumberField Matrix GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp GroundTheory.Heights₂.Heights.LowerBoundFree

namespace GlobalTheory.CompanionTheory.Ar.HermCoords

open scoped MatrixOrder ComplexOrder

theorem posDef_of_re_pos {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re) : Hm.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hH ?_
  intro x hx
  have h := hpos (star x) (star_ne_zero.2 hx)
  rw [star_star] at h
  have him : (star x ⬝ᵥ Hm *ᵥ x).im = 0 := by
    have := hH.im_star_dotProduct_mulVec_self x
    rwa [RCLike.im_to_complex] at this
  exact Complex.pos_iff.2 ⟨h, him.symm⟩

theorem exists_factor {g : ℕ} {Hm : Matrix (Fin g) (Fin g) ℂ} (hP : Hm.PosDef) :
    ∃ T : Matrix (Fin g) (Fin g) ℂ, ∀ z z' : Fin g → ℂ,
      z' ⬝ᵥ Hm *ᵥ star z = (T *ᵥ z') ⬝ᵥ star (T *ᵥ z) := by
  obtain ⟨B, hB⟩ := CStarAlgebra.nonneg_iff_eq_star_mul_self.1 hP.posSemidef.nonneg
  rw [Matrix.star_eq_conjTranspose] at hB
  refine ⟨(Bᴴ)ᵀ, fun z z' => ?_⟩
  have hT : ((((Bᴴ)ᵀ)ᴴ)ᵀ : Matrix (Fin g) (Fin g) ℂ) = B := by
    ext i j
    simp [Matrix.transpose_apply, Matrix.conjTranspose_apply]
  rw [Matrix.star_mulVec, ← Matrix.mulVec_transpose, ← Matrix.vecMul_transpose ((Bᴴ)ᵀ) z',
    ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.transpose_transpose, hT, hB]

theorem exists_coords_of_injective {V E : Type*} [AddCommGroup V] [Module ℂ V]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (L : V →ₗ[ℂ] E) (hinj : Function.Injective L) (m : ℕ) (W : Submodule ℂ V)
    (hW : Module.finrank ℂ W = m) :
    ∃ c : V →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W,
      innerₛₗ ℂ (L z) (L z') = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  let W' : Submodule ℂ E := W.map L
  have hm : Module.finrank ℂ W' = m := by
    rw [← hW]
    exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective L hinj W)).symm
  let b : OrthonormalBasis (Fin m) ℂ W' := (stdOrthonormalBasis ℂ W').reindex (finCongr hm)
  refine ⟨LinearMap.pi fun i => innerₛₗ ℂ (b i : E) ∘ₗ L, fun z hz z' hz' => ?_⟩
  have key := b.sum_inner_mul_inner (⟨L z, Submodule.mem_map_of_mem hz⟩ : W')
    ⟨L z', Submodule.mem_map_of_mem hz'⟩
  simp only [Submodule.coe_inner] at key
  rw [innerₛₗ_apply_apply, ← key]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [LinearMap.pi_apply, LinearMap.comp_apply, innerₛₗ_apply_apply, inner_conj_symm]

theorem exists_coords (g m : ℕ) (Hm : Matrix (Fin g) (Fin g) ℂ) (hH : Hm.IsHermitian)
    (hpos : ∀ z : Fin g → ℂ, z ≠ 0 → 0 < (z ⬝ᵥ Hm *ᵥ star z).re)
    (W : Submodule ℂ (Fin g → ℂ)) (hW : Module.finrank ℂ W = m) :
    ∃ c : (Fin g → ℂ) →ₗ[ℂ] (Fin m → ℂ), ∀ z ∈ W, ∀ z' ∈ W,
      z' ⬝ᵥ Hm *ᵥ star z = ∑ i, starRingEnd ℂ (c z i) * c z' i := by
  obtain ⟨T, hT⟩ := GlobalTheory.CompanionTheory.Ar.HermCoords.exists_factor
    (GlobalTheory.CompanionTheory.Ar.HermCoords.posDef_of_re_pos hH hpos)
  let L : (Fin g → ℂ) →ₗ[ℂ] EuclideanSpace ℂ (Fin g) :=
    (WithLp.linearEquiv 2 ℂ (Fin g → ℂ)).symm.toLinearMap ∘ₗ Matrix.mulVecLin T
  have hL : ∀ z z', innerₛₗ ℂ (L z) (L z') = z' ⬝ᵥ Hm *ᵥ star z := by
    intro z z'
    rw [hT, innerₛₗ_apply_apply, EuclideanSpace.inner_eq_star_dotProduct]
    first
    | rfl
    | simp [L]
  have hinj : Function.Injective L := by
    refine (injective_iff_map_eq_zero L).2 fun z hz => ?_
    by_contra hne
    have h1 := hpos z hne
    rw [← hL z z, hz] at h1
    simp at h1
  obtain ⟨c, hc⟩ := GlobalTheory.CompanionTheory.Ar.HermCoords.exists_coords_of_injective L hinj m W hW
  exact ⟨c, fun z hz z' hz' => by rw [← hL, hc z hz z' hz']⟩

end GlobalTheory.CompanionTheory.Ar.HermCoords
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.IsBlockDiagMapGenBlock
section
noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial

section Homog

variable {K : Type} {ι : K → Type} [∀ k, Fintype (ι k)]

theorem isMultiHomog_rename_base {σ : Type} (blk : σ → Option K) {d' : NonPluckerBlocks blk → ℕ}
    {g : MRing (baseIdx ι blk)} (hg : IsMultiHomog g d') :
    open Classical in
    IsMultiHomog (rename (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) g)
      (fun k => if h : ∀ p, blk p ≠ some k then d' ⟨k, h⟩ else 0) := by
  classical
  have hinj : Function.Injective (fun q : Σ k, baseIdx ι blk k => (⟨q.1.1, q.2⟩ : Σ k, ι k)) := by
    rintro ⟨⟨k, hk⟩, a⟩ ⟨⟨k', hk'⟩, b⟩ h
    obtain ⟨rfl, h⟩ := Sigma.mk.inj_iff.mp h
    cases h
    rfl
  intro m hm k
  rw [support_rename_of_injective hinj, Finset.mem_image] at hm
  obtain ⟨m', hm', rfl⟩ := hm
  beta_reduce
  by_cases h : ∀ p, blk p ≠ some k
  · rw [dite_eq_left h, ← hg m' hm' ⟨k, h⟩]
    refine Finset.sum_congr rfl fun i _ => ?_
    exact Finsupp.mapDomain_apply_of_injective hinj m' ⟨⟨k, h⟩, i⟩
  · rw [dite_eq_right h]
    refine Finset.sum_eq_zero fun i _ => Finsupp.mapDomain_of_notMem_range _ _ ?_
    rintro ⟨⟨⟨k', hk'⟩, b⟩, e⟩
    obtain ⟨rfl, -⟩ := Sigma.mk.inj_iff.mp e
    exact h hk'

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}

end Homog

section Minors

variable {N : ℕ}

theorem minorIJ_eq_det_of_card {R : Type} [CommRing R] (h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) {r : ℕ}
    (hI : I.card = r) (hJ : J.card = r) :
    minorIJ h I J = (h.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det := by
  subst hJ
  unfold minorIJ
  rw [dite_eq_left hI]

theorem minorIJ_mul_sum {R : Type} [CommRing R] (T h : Matrix (Fin N) (Fin N) R) (I J : Finset (Fin N)) :
    minorIJ (T * h) I J = ∑ I', minorIJ T I I' * minorIJ h I' J := by
  classical
  by_cases e : I.card = J.card
  · have hm : (T * h).submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl) =
        T.submatrix (I.orderEmbOfFin e) id * h.submatrix id (J.orderEmbOfFin rfl) := by
      ext a b
      simp [Matrix.mul_apply]
    have hsum : ∑ I', minorIJ T I I' * minorIJ h I' J =
        ∑ S : {S : Finset (Fin N) // S.card = J.card}, minorIJ T I S.1 * minorIJ h S.1 J := by
      rw [← Finset.sum_filter_of_ne (s := Finset.univ) (p := fun S : Finset (Fin N) => S.card = J.card)]
      · exact Finset.sum_subtype _ (by simp) _
      · intro S _ hS
        by_contra hc
        apply hS
        rw [show minorIJ h S J = 0 by unfold minorIJ; rw [dite_eq_right hc], mul_zero]
    rw [minorIJ_eq_det_of_card _ I J e rfl, hm, ReciprocityTheory.ChartRestriction.DS.cauchyBinet, hsum]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [minorIJ_eq_det_of_card T I S.1 e S.2, minorIJ_eq_det_of_card h S.1 J S.2 rfl]
    rfl
  · have h0 : minorIJ (T * h) I J = 0 := by
      unfold minorIJ
      rw [dite_eq_right e]
    rw [h0]
    symm
    refine Finset.sum_eq_zero fun I' _ => ?_
    by_cases e' : I.card = I'.card
    · rw [show minorIJ h I' J = 0 by
        unfold minorIJ
        rw [dite_eq_right fun c => e (e'.trans c)], mul_zero]
    · rw [show minorIJ T I I' = 0 by unfold minorIJ; rw [dite_eq_right e'], zero_mul]

theorem minorIJ_block_zero {R : Type} [CommRing R] {j : ℕ} {i : Fin N} {h : Matrix (Fin N) (Fin N) R}
    (hh : IsBlockDiag j h) {I : Finset (Fin N)} (hnot : ¬ IsStepRows N j i I) :
    minorIJ h I (stepCols N j i) = 0 := by
  have hiN := i.isLt
  by_cases e : I.card = (stepCols N j i).card
  · have hsub : ¬ I ⊆ if (i : ℕ) + 1 ≤ j then wIdx N j else omIdx N j := fun hs => hnot ⟨e, hs⟩
    obtain ⟨a, haI, haB⟩ := Finset.not_subset.mp hsub
    have hr : a ∈ Set.range (I.orderEmbOfFin e) := by
      rw [Finset.range_orderEmbOfFin]
      exact haI
    obtain ⟨r, rfl⟩ := hr
    unfold minorIJ
    rw [dite_eq_left e]
    refine Matrix.det_eq_zero_of_row_eq_zero r fun c => ?_
    have hb := Finset.orderEmbOfFin_mem (stepCols N j i) rfl c
    refine hh _ _ ?_
    generalize (stepCols N j i).orderEmbOfFin rfl c = b at hb
    generalize I.orderEmbOfFin e r = a at haB
    by_cases hc : (i : ℕ) + 1 ≤ j
    · simp only [stepCols, wIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_pos hc] at hb haB
      omega
    · simp only [stepCols, omIdx, Finset.mem_filter, Finset.mem_univ, true_and, if_neg hc] at hb haB
      omega
  · unfold minorIJ
    rw [dite_eq_right e]

end Minors

section Model

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} {N j : ℕ}

end Model

end GlobalTheory.CompanionTheory.Ar.PB
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.TailLogBoundLocalIntegrableStatement
section
open MeasureTheory Filter Topology ReciprocityTheory.AnForm.M
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tail_log_bound_local_integrable : ∀ {e : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas e X) (Yo : Set X) (r : X → ℝ) (Φ : Fin e → LocPot X) (CE : ℝ), (∀ i, IsPotential A (Φ i)) → (∀ x ∈ Yo, 1 ≤ r x) → (∀ j, ∀ y ∈ (A.chart j).target, (A.chart j).symm y ∈ Yo → 0 ≤ locDens A Φ j y) → GroundTheory.Heights₂.Heights.AnalyticLimit.TailLogBound A Yo r Φ CE → ∀ (j : Fin A.n) (S : Set (Fin e → ℂ)), S ⊆ (A.chart j).target → IsCompact S → ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ → IntegrableOn (fun y => (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y) S ∧ ∫ y in S, (GroundTheory.Heights₂.Heights.AnalyticLimit.tail Yo r R₀).indicator (fun x => Real.log (r x)) ((A.chart j).symm y) * locDens A Φ j y ≤ CE * Real.log R₀ ^ (e + 1) / R₀ := by
  first | exact @GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | exact GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart | (intros; apply GlobalTheory.CompanionTheory.Metric.LocTail.tailLog_on_compact_of_chart <;> assumption)
end

