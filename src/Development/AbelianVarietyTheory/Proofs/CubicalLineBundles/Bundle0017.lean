module

public import Mathlib
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0001
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.Bundle0002
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
public import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
public import ReciprocityTheory.SemistableReduction.Bundle0008
public import Development.AbelianVarietyTheory.Statements.FundamentalDomains.KeyFormulaPowOfKeyFormula
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsSchemeTheoreticallyDominantSpecOfInjective
public import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.Bundle0016
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0022
public import Development.AbelianVarietyTheory.Proofs.GenericRegularity.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.IsLocallyConstantRankAtStalkEigenSub
public import Development.AbelianVarietyTheory.Statements.PrincipalLattices.FiniteDimensionalBase
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.MemNonzeroLocusIffPowFn
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0018
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0108

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CmPointLowerBoundOfCoefficientBound
section
open NumberField IsDedekindDomain MeasureTheory IsLocalRing Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.LamCM
open scoped nonZeroDivisors ComplexOrder

namespace GlobalTheory

theorem cmLowerBound_of_coeffBound :
    (∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (H : (K →+* ℂ) → Matrix (Fin x.P.g) (Fin x.P.g) ℂ) (La logOm : ℝ) (V : Type) [Fintype V] (c : V → Fin x.P.g) (G : MvPolynomial V K) (μ : V →₀ ℕ) (n : ℕ) (S : (K →+* ℂ) → ℝ) (Rr : ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → U.det ≠ 0 → 1 ≤ La → (∀ σ, (H σ).PosDef) → (∀ σ, abelian₂.n σ = Real.sqrt (H σ).det.re) → (∀ p : HeightOneSpectrum (𝓞 K), ∃ (cd : K) (cl : Fin x.P.g → K), IsLocGen p cd abelian₂.I ∧ (∀ j, IsLocGen p (cl j) (ℓ j).I) ∧ p.valuation K ((∏ j, cl j) * U.det) ≤ p.valuation K cd) → (∀ σ j, ReciprocityTheory.MultiplicativeHeights.hq (H σ) (ReciprocityTheory.MultiplicativeHeights.embVec σ (U j)) ≤ (La * (ℓ j).n σ) ^ 2) → (∀ j, (ℓ j).ndeg = logOm / 2) → AddMonoidAlgebra.coeff G μ ≠ 0 → AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ c μ n).I → (∀ σ, 0 < S σ) → 0 < Rr → (∀ (σ : K →+* ℂ) (z : V → ℂ), (∀ v, ‖z v‖ * (ℓ (c v)).n σ ≤ 1) → ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * Rr ^ (∑ v, μ v)) → - ((pDeg logOm + (1 / 2) * Real.log La) * ((∑ v, (μ v : ℝ)) + (x.P.g : ℝ) * n)) - (∑ v, (μ v : ℝ)) * Real.log Rr ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ)) → ReciprocityTheory.MultiplicativeHeights.LemmaHStatement → ∀ (K : Type) [Field K] [NumberField K] (x : KeyIn K) (T abelian₂ : MLine K) (B : Type) [Fintype B] [DecidableEq B] (m : B → ℕ) (e : (Σ b, Fin (m b)) ≃ Fin x.P.g) (ℓ : Fin x.P.g → MLine K) (U : Matrix (Fin x.P.g) (Fin x.P.g) K) (G : MvPolynomial (FrVar m) K) (a : ∀ b, Fin (m b) → ℕ) (n r : ℕ) (La logOm : ℝ) (S : (K →+* ℂ) → ℝ), T.Good → abelian₂.Good → (∀ p, KeyLocAt x T abelian₂ p) → (∀ σ, KeyArchAt x T abelian₂ σ) → (∀ j, (ℓ j).Good) → (∀ j, (ℓ j).ndeg = logOm / 2) → U.det ≠ 0 → G ≠ 0 → 1 ≤ La → 1 ≤ r → (∀ b, m b ≤ r) → (∀ σ, 0 < S σ) → (∀ p, Step5Loc e T.dual abelian₂ ℓ U G n p) → (∀ σ, Step5Arch e T.dual abelian₂ ℓ U G a n La (S σ) σ) → - ((pDeg logOm + (1 / 2) * Real.log La) * (((∑ b, ∑ i, a b i : ℕ) : ℝ) + (x.P.g : ℝ) * n)) - ((∑ b, ∑ i, a b i : ℕ) : ℝ) * Real.log ((r : ℝ) * La) ≤ (∑ σ : K →+* ℂ, Real.log (S σ)) / (Module.finrank ℚ K : ℝ) := by
  intro hLK hH K _ _ x T abelian₂ B _ _ m e ℓ U G a n r La logOm S hT hLam hloc harch hℓ hℓdeg hU hG hLa hr hmr hS hS5L hS5A
  classical
  obtain ⟨μ, hμ⟩ := MvPolynomial.ne_zero_iff.mp hG
  have hTd : T.dual.Good := (degree_algebraic K T T hT hT).2.2.1
  obtain ⟨σ₀⟩ : Nonempty (K →+* ℂ) := inferInstance

  have hsum : ∑ v, μ v = ∑ b, ∑ i, a b i := by
    obtain ⟨H₀, -, -, -, heq, -⟩ := hS5A σ₀
    refine subst_homogeneous B m a (MvPolynomial.map σ₀ G) (fun _ => 1) heq μ ?_
    rw [substFr_one, MvPolynomial.coeff_map]
    exact (map_ne_zero σ₀).mpr hμ
  unfold Step5Arch at hS5A
  choose Hs hHs using hS5A
  have hRr : (0 : ℝ) < (r : ℝ) * La := mul_pos (Nat.cast_pos.mpr hr) (by linarith)

  have hmem : AddMonoidAlgebra.coeff G μ ∈ (lineNN T.dual ℓ (fun v : FrVar m => e ⟨v.1, v.2.2⟩) μ n).I := by
    refine coeff_mem_of_local K x.P.g ℓ T.dual (FrVar m) _ μ n _ hTd hℓ fun p => ?_
    obtain ⟨t, cd, cl, ht, hcd, hcl, hv, V, K', _, _, _, _, _, _, f, Ub, hVc, hfin, hind, hUb, hclUb, hW⟩ := hS5L p
    refine ⟨t, cl, ht, hcl, ?_⟩
    have htn : t ^ n ≠ 0 := pow_ne_zero _ ht.1
    have hftn : f (t ^ n) ≠ 0 := (map_ne_zero f).mpr htn
    obtain ⟨w, hw⟩ := coeff_integral_local V K' B m (MvPolynomial.map f G) Ub (fun b j => f (cl (e ⟨b, j⟩)))
      (f (t ^ n)) hVc hfin hftn hUb hclUb hW μ
    have hrange : f (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) ∈
        Set.range (algebraMap V K') := by
      refine ⟨w, ?_⟩
      rw [map_div₀, map_mul, map_prod]
      simp only [map_pow]
      rw [← map_pow f t n, ← MvPolynomial.coeff_map, hw, mul_div_cancel_left₀ _ hftn]
    have h1 := (hind _).mp hrange
    calc p.valuation K (AddMonoidAlgebra.coeff G μ * ∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v)
        = p.valuation K (AddMonoidAlgebra.coeff G μ * (∏ v : FrVar m, cl (e ⟨v.1, v.2.2⟩) ^ μ v) / t ^ n) *
            p.valuation K (t ^ n) := by
          rw [← map_mul, div_mul_cancel₀ _ htn]
      _ ≤ p.valuation K (t ^ n) := mul_le_of_le_one_left' h1

  have harch' : ∀ (σ : K →+* ℂ) (z : FrVar m → ℂ),
      (∀ v, ‖z v‖ * (ℓ ((fun v : FrVar m => e ⟨v.1, v.2.2⟩) v)).n σ ≤ 1) →
      ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n ≤ S σ * ((r : ℝ) * La) ^ (∑ v, μ v) := by
    intro σ z hz
    obtain ⟨hpd, -, hbd, heq, hY⟩ := hHs σ
    have hTn : 0 < T.dual.n σ ^ n := pow_pos (hTd.2 σ) n
    have hA := ArchTie_of hH B m a (MvPolynomial.map σ G) (fun b => gramBlock e U (Hs σ) σ b) (fun _ => 1)
      (fun b j => (ℓ (e ⟨b, j⟩)).n σ) (S σ / T.dual.n σ ^ n) La r
      (fun b => gramBlock_posDef e U (Hs σ) σ b hpd hU) heq
      (fun X hX => by rw [le_div_iff₀ hTn]; exact hY X hX)
      (fun b j => (hℓ _).2 σ) (by linarith) hmr
      (fun b j => (hermitian_form_gramBlock_basis e U (Hs σ) σ b j).le.trans (hbd _)) z hz
    rw [substFr_one] at hA
    rw [hsum]
    calc ‖MvPolynomial.eval z (MvPolynomial.map σ G)‖ * T.dual.n σ ^ n
        ≤ S σ / T.dual.n σ ^ n * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) * T.dual.n σ ^ n :=
          mul_le_mul_of_nonneg_right hA hTn.le
      _ = S σ * ((r : ℝ) * La) ^ (∑ b, ∑ i, a b i) := by
          rw [div_mul_eq_mul_div, div_mul_cancel₀ _ hTn.ne']
  unfold Step5Loc at hS5L
  have key := hLK K x T abelian₂ ℓ U Hs La logOm (FrVar m) (fun v => e ⟨v.1, v.2.2⟩) G μ n S ((r : ℝ) * La)
    hT hLam hloc harch hℓ hU hLa (fun σ => (hHs σ).1) (fun σ => (hHs σ).2.1)
    (fun p => by
      obtain ⟨t, cd, cl, ht, hcd, hcl, hv, -⟩ := hS5L p
      exact ⟨cd, cl, hcd, hcl, hv⟩)
    (fun σ j => (hHs σ).2.2.1 j) hℓdeg hμ hmem hS hRr harch'
  have hc : (∑ v, (μ v : ℝ)) = ((∑ b, ∑ i, a b i : ℕ) : ℝ) := by
    rw [← hsum, Nat.cast_sum]
  rw [hc] at key
  exact key

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.CurveHomExtOfDerivativeLieBasis
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory.HomUnique

theorem hom_ext_of_lieBasis : ThetaUnifAV → Out.PolBaseChangeSt → ∀ (k : Type) [Field k] (s : k →+* ℂ) (P Q : Out.PolAV (Sp k)) (v : epsR k ⟶ P.A) (f f' : P.A ⟶ Q.A), (∀ (R' : Type) [CommRing R'] (f' : k →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) → IsMonHom f → IsMonHom f' → v ≫ f = v ≫ f' → f = f' := by
  intro hU hB k _ s P Q v f f' hv hf hf' h
  obtain ⟨P', φ, hP⟩ := exists_isPolFibre hB s P
  obtain ⟨Q', ψ, hQ⟩ := exists_isPolFibre hB s Q
  obtain ⟨v', hv', -⟩ := existsUnique_isVecOver hP.2.1.1 v
  obtain ⟨g, hg, eg⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f
  obtain ⟨g', hg', eg'⟩ := HomDescent.exists_isMonHom_pull hP.2.1 hQ.2.1 f'
  have hb := hv ℂ s P' φ v' hP hv'
  have e₁ : v' ≫ g = v' ≫ g' := by
    refine Over.OverMorphism.ext (hQ.2.1.1.hom_ext ?_ ((Over.w _).trans (Over.w _).symm))
    have hl : v.left ≫ f.left = v.left ≫ f'.left := congrArg (fun z => z.left) h
    unfold IsVecOver at hv'
    rw [Over.comp_left, Over.comp_left, Category.assoc, Category.assoc, eg, eg', ← Category.assoc, ← Category.assoc,
      hv', Category.assoc, Category.assoc, hl]
  have e₂ : g = g' := by
    refine (HomDescent.pol_countable_and_tangent_ext hU P' Q').2 g g' hg hg' fun x hx => ?_
    obtain ⟨c, hc, -⟩ := hb.2 x hx
    have ec : c = ![c 0] := by
      ext i
      fin_cases i
      rfl
    rw [ec, LieMultiple.isLieComb_one_iff_comp] at hc
    rw [hc, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) e₁
  have := P.isAb.smooth
  have := Q.isAb.proper
  have : IsSchemeTheoreticallyDominant (spMap s) :=
    ExtUnique.isSchemeTheoreticallyDominant_spec_of_injective (CommRingCat.ofHom s) s.injective
  exact ExtUnique.over_hom_ext_of_isPullback hP.2.1.1 (by rw [← eg, ← eg', e₂])

end GlobalTheory.HomUnique
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.DetCondTensorDefinite
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.TensorDet

section Algebra

noncomputable def rightAction (k O O' M : Type) [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M] : O' →+* Module.End k (k ⊗[O] M) :=
  (Module.End.baseChangeHom O k M).toRingHom.comp (Algebra.lsmul O O M : O' →ₐ[O] Module.End O M).toRingHom

variable {k O O' M : Type} [CommRing k] [CommRing O] [CommRing O'] [Algebra O k] [Algebra O O']
    [AddCommGroup M] [Module O M] [Module O' M] [IsScalarTower O O' M]

theorem rightAction_apply (a : O') :
    rightAction k O O' M a = LinearMap.baseChange k (Algebra.lsmul O O M a : M →ₗ[O] M) := rfl

theorem rightAction_tmul (a : O') (c : k) (m : M) : rightAction k O O' M a (c ⊗ₜ m) = c ⊗ₜ (a • m) := rfl

theorem nonempty_eigenSub_equiv [Algebra O' k] [IsScalarTower O O' k] {I : Type} {σ : I → O' →+* k}
    (h : EigenSplit.IsSplitting σ) (i : I) (hi : σ i = algebraMap O' k) :
    Nonempty (EigenSplit.eigenSub (rightAction k O O' M) (σ i) ≃ₗ[k] k ⊗[O'] M) := by
  classical
  let ρ := rightAction k O O' M
  let π : k ⊗[O] M →ₗ[k] k ⊗[O'] M := ((TensorProduct.mk O' k M 1).restrictScalars O).liftBaseChange k
  have hπ : ∀ m, π (1 ⊗ₜ m) = 1 ⊗ₜ m := fun m => by simp [π]
  let ρ' : O' →+* Module.End k (k ⊗[O'] M) := (algebraMap k _).comp (σ i)
  have he : EigenSplit.IsEquivariant ρ ρ' π := fun a x => by
    have : π ∘ₗ ρ a = ρ' a ∘ₗ π := by
      ext m
      simp only [TensorProduct.AlgebraTensorModule.curry_apply,
        TensorProduct.curry_apply, LinearMap.comp_apply, LinearMap.coe_restrictScalars, ρ, rightAction_tmul, hπ]
      simp [ρ', hi]
    exact congr($this x)
  let g : M →ₗ[O'] k ⊗[O] M :=
    { toFun := fun m => EigenSplit.proj h ρ i (1 ⊗ₜ m)
      map_add' := fun m n => by rw [TensorProduct.tmul_add, map_add (f := _)]
      map_smul' := fun a m => by
        rw [← rightAction_tmul, ← (EigenSplit.isEquivariant_action ρ a).proj h,
          EigenSplit.mem_eigenSub.1 (EigenSplit.proj_mem h ρ i _), hi, algebraMap_smul]
        rfl }
  let s : k ⊗[O'] M →ₗ[k] k ⊗[O] M := g.liftBaseChange k
  have h1 : s ∘ₗ π = EigenSplit.proj h ρ i := by
    ext m
    simp [hπ, s, g]
  have h2 : ∀ x, π (EigenSplit.proj h ρ i x) = π x := fun x => by
    rw [he.proj h]
    exact EigenSplit.proj_of_mem h (EigenSplit.mem_eigenSub.2 fun a => rfl)
  have h3 : π ∘ₗ s = LinearMap.id := by
    ext m
    simp [s, g, h2, hπ]
  refine ⟨LinearEquiv.ofBijective (π ∘ₗ Submodule.subtype _) ⟨(injective_iff_map_eq_zero _).2 fun x hx => ?_,
    fun y => ⟨EigenSplit.projTo h ρ i (s y), (h2 _).trans congr($h3 y)⟩⟩⟩
  refine Subtype.ext ((EigenSplit.proj_of_mem h x.2).symm.trans ?_)
  rw [← h1]
  exact (congrArg s hx).trans (map_zero s)

end Algebra

theorem injective_of_charZero {E k : Type} [Field E] [NumberField E] [Field k] [CharZero k] (τ : 𝓞 E →+* k) :
    Function.Injective τ := by
  rw [RingHom.injective_iff_ker_eq_bot, ← Ideal.absNorm_eq_zero_iff]
  simpa using RingHom.mem_ker.1 (Ideal.absNorm_mem (RingHom.ker τ))

theorem finrank_eigenSub {E k O M : Type} [Field E] [NumberField E] [Field k] [IsAlgClosed k] [CharZero k]
    [CommRing O] [Algebra O k] [Algebra O (𝓞 E)] [AddCommGroup M] [Module O M] [Module (𝓞 E) M]
    [IsScalarTower O (𝓞 E) M] (τ : 𝓞 E →+* k) (hτ : τ.comp (algebraMap O (𝓞 E)) = algebraMap O k) :
    Module.finrank k (EigenSplit.eigenSub (rightAction k O (𝓞 E) M) τ) = Module.finrank (𝓞 E) M := by
  have hs : EigenSplit.IsSplitting fun φ : E →+* k => φ.comp (algebraMap (𝓞 E) E) := by
    classical
    obtain ⟨b⟩ := EigenSplit.nonempty_basis (E := E) (NumberField.Embeddings.card E k)
    exact EigenSplit.isSplitting_of_isUnit_discr b (EigenSplit.det_sq_eq_discr_of_field Function.injective_id b)
      (by simpa using NumberField.discr_ne_zero E)
  have hi := injective_of_charZero τ
  let _ := τ.toAlgebra
  have : IsScalarTower O (𝓞 E) k := IsScalarTower.of_algebraMap_eq' hτ.symm
  have : FaithfulSMul (𝓞 E) k := (faithfulSMul_iff_algebraMap_injective _ _).2 hi
  have e : (IsFractionRing.lift hi : E →+* k).comp (algebraMap (𝓞 E) E) = τ :=
    RingHom.ext fun a => IsFractionRing.lift_algebraMap hi a
  obtain ⟨f⟩ := nonempty_eigenSub_equiv (O := O) (M := M) hs (IsFractionRing.lift hi) e
  rw [← (TensorProduct.isBaseChange (𝓞 E) M k).finrank_eq, ← f.finrank_eq, e]

theorem lieMult_of_param {k O V : Type} [Field k] [CommRing O] [AddCommGroup V] [Module k V] [Module.Finite k V]
    {A : Over (Sp k)} [GrpObj A] (act : OAct O A) (ρ : O →+* Module.End k V) (Φ : V → (epsR k ⟶ A))
    (inj : Function.Injective Φ) (tan : ∀ x, IsTangent x ↔ x ∈ Set.range Φ) (add : ∀ y z, Φ (y + z) = Φ y * Φ z)
    (smul : ∀ (c : k) y, IsLieComb ![c] ![Φ y] (Φ (c • y))) (eqv : ∀ a y, Φ (ρ a y) = Φ y ≫ act.act a)
    (τ : O →+* k) {n : ℕ} (hn : Module.finrank k (EigenSplit.eigenSub ρ τ) = n) :
    LieMult act (𝟙 (Sp k)) τ n := by
  have sm : ∀ (c : k) y x, x.left = spMap (epsScaleR c) ≫ (Φ y).left ↔ x = Φ (c • y) := fun c y x => by
    rw [← (LieMultiple.isLieComb_one_iff _ _ _).1 (smul c y)]
    exact ⟨fun h => Over.OverMorphism.ext h, fun h => by rw [h]⟩
  let F : Multiplicative V →* (epsR k ⟶ A) := MonoidHom.mk' (fun y => Φ y.toAdd) (fun y z => add _ _)
  have pr : ∀ (n : ℕ) (y : Fin n → V), (List.ofFn fun i => Φ (y i)).prod = Φ (∑ i, y i) := fun n y => by
    have := map_list_prod F (List.ofFn fun i => Multiplicative.ofAdd (y i))
    rw [List.map_ofFn, List.prod_ofFn, ← ofAdd_sum] at this
    exact this.symm
  let B := Module.finBasisOfFinrankEq k _ hn
  let j : epsPt (𝟙 (Sp k)) ≅ epsR k := Over.isoMk (Iso.refl _) (by simp)
  let e : (epsPt (𝟙 (Sp k)) ⟶ A) ≃* (epsR k ⟶ A) :=
    MulEquiv.ofBijective (preHom j.inv) (j.symm.homCongr (Iso.refl A)).symm.bijective
  have he : ∀ w, (e w).left = w.left := fun w => Category.id_comp _
  have he' : ∀ w, (e.symm w).left = w.left := fun w => by rw [← he, e.apply_symm_apply]
  have one : (1 : Over.mk (𝟙 (Sp k)) ⟶ A).left = η[A].left := Category.id_comp _
  have mem : ∀ y, y ∈ EigenSplit.eigenSub ρ τ ↔
      ∀ a, (Φ y ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ (Φ y).left := fun y => by
    rw [EigenSplit.mem_eigenSub]
    exact forall_congr' fun a => by rw [sm, ← eqv, inj.eq_iff]
  refine LiePull.basis_transport e.symm (Q := IsLieEigen act (𝟙 _) τ)
    (R' := fun c u v => u.left = spMap (epsScale c) ≫ v.left)
    (R := fun c u v => u.left = spMap (epsScaleR c) ≫ v.left)
    (P := fun w => IsTangent w ∧ ∀ a, (w ≫ act.act a).left = spMap (epsScaleR (τ a)) ≫ w.left)
    (fun w => and_congr (by rw [IsTangent, he', one]) (forall_congr' fun a => by
      rw [Over.comp_left, Over.comp_left, he']
      rfl))
    (fun c u v => by rw [he', he']; rfl) n
    ⟨fun i => Φ (B i), fun i => ⟨(tan _).2 ⟨_, rfl⟩, (mem _).1 (B i).2⟩, ?_⟩
  rintro w ⟨hw, hw'⟩
  obtain ⟨y, rfl⟩ := (tan w).1 hw
  let y' : EigenSplit.eigenSub ρ τ := ⟨y, (mem y).2 hw'⟩
  refine (existsUnique_congr fun d => ?_).1 (existsUnique_eq' (a' := B.equivFun y'))
  have e₁ : B.equivFun y' = d ↔ y = ∑ i, d i • (B i : V) := by
    rw [← LinearEquiv.eq_symm_apply, Module.Basis.equivFun_symm_apply, Subtype.ext_iff]
    simp [y']
  rw [e₁, ← inj.eq_iff, ← pr]
  constructor
  · exact fun h => ⟨_, fun i => (sm _ _ _).2 rfl, h⟩
  · rintro ⟨u, hu, h⟩
    rw [h, show u = fun i => Φ (d i • (B i : V)) from funext fun i => (sm _ _ _).1 (hu i)]

end GlobalTheory.TensorDet
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.EllipticCurveLatticeBaseChangeStable
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory
open scoped CategoryTheory.Obj UpperHalfPlane

namespace GlobalTheory

theorem curve_lattice_baseChange : ∀ (R : Type) [CommRing R] (P : Out.PolAV (Sp R)) (v : epsR R ⟶ P.A) (Lf : (R →+* ℂ) → PeriodPair) (R₁ : Type) [CommRing R₁] (f : R →+* R₁) (P₁ : Out.PolAV (Sp R₁)) (φ : P₁.A.left ⟶ P.A.left) (v₁ : epsR R₁ ⟶ P₁.A), (P.g = 1 ∧ IsLieBasis ![v] ∧ (∀ (R' : Type) [CommRing R'] (f' : R →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P P' φ' → IsVecOver f' φ' v v' → IsLieBasis ![v']) ∧ ∀ s' : R →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P P' φ' → IsVecOver s' φ' v v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ (Lf s').lattice ↔ z • w' ∈ u'.Λ)) → IsPolFibre f P P₁ φ → IsVecOver f φ v v₁ → (P₁.g = 1 ∧ IsLieBasis ![v₁] ∧ (∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' → IsLieBasis ![v']) ∧ ∀ s' : R₁ →+* ℂ, (∀ (P' : Out.PolAV (Sp ℂ)) (φ' : P'.A.left ⟶ P₁.A.left) (v' : epsR ℂ ⟶ P'.A) (u' : HolUnif P'.A P'.L P'.g) (w' : Fin P'.g → ℂ), IsPolFibre s' P₁ P' φ' → IsVecOver s' φ' v₁ v' → u'.IsDiff w' v' → w' ≠ 0 ∧ ∀ z : ℂ, z ∈ ((fun s : R₁ →+* ℂ => Lf (s.comp f)) s').lattice ↔ z • w' ∈ u'.Λ)) := by
  intro R _ P v Lf R₁ _ f P₁ φ v₁ ⟨hg, _, hfib, hlat⟩ hP₁ hv₁

  have up : ∀ (R' : Type) [CommRing R'] (f' : R₁ →+* R') (P' : Out.PolAV (Sp R')) (φ' : P'.A.left ⟶ P₁.A.left)
      (v' : epsR R' ⟶ P'.A), IsPolFibre f' P₁ P' φ' → IsVecOver f' φ' v₁ v' →
      IsPolFibre (f'.comp f) P P' (φ' ≫ φ) ∧ IsVecOver (f'.comp f) (φ' ≫ φ) v v' := by
    intro R' _ f' P' φ' v' hP' hv'
    exact ⟨PolFibre.comp hP₁ hP', (PolFibre.vec_iff hP₁.2.1.1 hP'.2.1.1.w hv₁).1 hv'⟩
  refine ⟨hP₁.1.trans hg, hfib R₁ f P₁ φ v₁ hP₁ hv₁, ?_, ?_⟩
  · intro R' _ f' P' φ' v' hP' hv'
    obtain ⟨h₁, h₂⟩ := up R' f' P' φ' v' hP' hv'
    exact hfib R' (f'.comp f) P' (φ' ≫ φ) v' h₁ h₂
  · intro s' P' φ' v' u' w' hP' hv' hd
    obtain ⟨h₁, h₂⟩ := up ℂ s' P' φ' v' hP' hv'
    exact hlat (s'.comp f) P' (φ' ≫ φ) v' u' w' h₁ h₂ hd

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsIsHomFamilyBaseChange
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory

namespace PureType

section Grp

variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left}


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
theorem _root_.GlobalTheory.PureType.exists_hom_over (hβ : β ≫ B.hom = B'.hom ≫ f)
    (hπ : IsPullback π G'.hom G.hom f) (φ : B ⟶ G) :
    ∃ φ' : B' ⟶ G', φ'.left ≫ π = β ≫ φ.left := by
  refine ⟨Over.homMk (hπ.lift (β ≫ φ.left) B'.hom ?_) (hπ.lift_snd _ _ _), ?_⟩
  · rw [Category.assoc, Over.w φ, hβ]
  · exact hπ.lift_fst _ _ _


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
theorem _root_.GlobalTheory.PureType.eq_of_comp_eq (hπ : IsPullback π G'.hom G.hom f) {T : Over S'}
    {x y : T ⟶ G'} (h : x.left ≫ π = y.left ≫ π) : x = y :=
  Over.OverMorphism.ext (hπ.hom_ext h (by simp))

variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G']


set_option autoImplicit false in
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj in
variable {S S' : Scheme.{0}} {f : S' ⟶ S} {B G : Over S} {B' G' : Over S'}
  {β : B'.left ⟶ B.left} {π : G'.left ⟶ G.left} in
variable [GrpObj B] [GrpObj G] [GrpObj B'] [GrpObj G'] in
theorem _root_.GlobalTheory.PureType.isMonHom_over (hβ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback B' B f β) (hπ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsGrpPullback G' G f π) {φ : B ⟶ G}
    [IsMonHom φ] {φ' : B' ⟶ G'} (h : φ'.left ≫ π = β ≫ φ.left) : IsMonHom φ' := by
  have key : ∀ (T : Over S') (x y : T ⟶ B'), (x * y) ≫ φ' = (x ≫ φ') * (y ≫ φ') := by
    intro T x y
    have hw : ∀ z : T ⟶ B', (z.left ≫ β) ≫ B.hom = (Over.mk (T.hom ≫ f)).hom := by
      intro z
      rw [Category.assoc, hβ.1.w, ← Category.assoc, Over.w z]
      rfl
    let x₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (x.left ≫ β) (hw x)
    let y₀ : Over.mk (T.hom ≫ f) ⟶ B := Over.homMk (y.left ≫ β) (hw y)
    have h₁ := hβ.2 T x y x₀ y₀ rfl rfl
    have h₂ := hπ.2 T (x ≫ φ') (y ≫ φ') (x₀ ≫ φ) (y₀ ≫ φ) (by simp [x₀, h]) (by simp [y₀, h])
    apply _root_.GlobalTheory.PureType.eq_of_comp_eq hπ.1
    rw [← h₂, ← MonObj.mul_comp]
    simp only [Over.comp_left, h₁, Category.assoc, h]
  have one : ∀ (T : Over S'), (1 : T ⟶ B') ≫ φ' = 1 := by
    intro T
    have := key T 1 1
    rw [_root_.mul_one] at this
    exact mul_left_cancel (a := (1 : T ⟶ B') ≫ φ') (by rw [_root_.mul_one]; exact this.symm)
  constructor
  · simpa [Hom.one_def] using one (𝟙_ _)
  · have := key (B' ⊗ B') (fst B' B') (snd B' B')
    simpa [Hom.mul_def] using this


end Grp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

end PureType

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsLbHermitian
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Serre
open scoped CategoryTheory.Obj UpperHalfPlane TensorProduct

namespace GlobalTheory.HermTensorLB

open GlobalTheory.CechPic

section Pairing

variable {S : Scheme.{0}} {G A T : Over S} [GrpObj G] [GrpObj A]

theorem lam_sum {I : Type} (s : Finset I) (c : I → Pic A.left) (x y : T ⟶ A) :
    lam (∑ i ∈ s, c i) x y = ∑ i ∈ s, lam (c i) x y := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [lam, map_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]

variable [IsCommMonObj G] {L : LB G.left} (hL : L.IsLB) (hΘ : ∃ t : LB.Gen (Theta G L), t.IsGen)
include hΘ

theorem lam_mul_right (x y z : T ⟶ G) :
    lam (cls L hL) x (y * z) = lam (cls L hL) x y + lam (cls L hL) x z := by
  rw [lam_comm, lam_mul_left hL hΘ, lam_comm _ y, lam_comm _ z]

theorem lam_lam (u v : A ⟶ G) [IsMonHom u] [IsMonHom v] (x y : T ⟶ A) :
    lam (lam (cls L hL) u v) x y =
      lam (cls L hL) (x ≫ u) (y ≫ v) + lam (cls L hL) (y ≫ u) (x ≫ v) := by
  rw [lam.eq_1 (lam (cls L hL) u v)]
  simp only [pull_lam, MonObj.mul_comp, MonObj.one_comp, lam_one_left, lam_mul_left hL hΘ,
    lam_mul_right hL hΘ]
  abel

end Pairing

end GlobalTheory.HermTensorLB
end
end

