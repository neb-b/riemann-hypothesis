module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.UnivFrame
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0023
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
public import Development.AbelianVarietyTheory.Proofs.HermitianTraceForms.ExistsIsComplEigenSubOfValuationRing
public import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ReductionSurjectiveOfIsNilpotent
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTangentModuleUniversalGroup
public import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.NormConst
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0007
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0003
public import Development.AbelianVarietyTheory.PublishedTheorems.Landherr₂.ExistsNormTensor
public import Development.AbelianVarietyTheory.Statements.HyperbolicHypotheses.HypothesesInhabitedHyperbolic
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteIntegralClosureOfEssFiniteTypeField
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsGrpPullback

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsTriangularFrameRingOverTestRing
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory

theorem exists_testRing_universal_partially_invertible (K : Type) [Field K] (σ : Type) [Finite σ]
    (D : σ → Prop) (p : TRing K) :
    ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (x : σ → A.R), (∀ i, D i → IsUnit (x i)) ∧
      ∀ (T : Type) [CommRing T] [Algebra K T] (ψ : p.R →ₐ[K] T) (t : σ → T), (∀ i, D i → IsUnit (t i)) →
        ∃! k : A.R →ₐ[K] T, k.comp π = ψ ∧ ∀ i, k (x i) = t i := by
  classical
  have := Fintype.ofFinite σ
  obtain ⟨hft, hred⟩ := (reduced_finiteType_iff_testRing K).2 p
  let P := MvPolynomial σ p.R
  let f : P := ∏ i ∈ Finset.univ.filter D, MvPolynomial.X i
  let B := Localization.Away f
  have hPred : _root_.IsReduced P := ⟨fun q hq => by
    ext i
    exact IsReduced.eq_zero _ (MvPolynomial.isNilpotent_iff.1 hq i)⟩
  have hBred : _root_.IsReduced B := isReduced_localizationPreserves (Submonoid.powers f) B hPred
  have hPft : Algebra.FiniteType K P := Algebra.FiniteType.trans hft inferInstance
  have hBft : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans hPft (IsLocalization.finiteType_of_monoid_fg (Submonoid.powers f) B)
  obtain ⟨A, ⟨e⟩⟩ := (reduced_finiteType_iff_testRing K).1 B hBft hBred
  let emb : P →ₐ[K] B := IsScalarTower.toAlgHom K P B
  let c : p.R →ₐ[K] P := IsScalarTower.toAlgHom K p.R P
  refine ⟨A, (e.symm : B →ₐ[K] A.R).comp (emb.comp c), fun i => e.symm (emb (MvPolynomial.X i)), ?_, ?_⟩
  · intro i hi
    refine IsUnit.map e.symm ?_
    have hf : IsUnit (emb f) := IsLocalization.Away.algebraMap_isUnit f
    refine isUnit_of_dvd_unit (map_dvd emb ?_) hf
    exact Finset.dvd_prod_of_mem _ (by simp [hi])
  · intro T _ _ ψ t ht
    let φ : P →ₐ[K] T := MvPolynomial.aevalTower ψ t
    have hφ : IsUnit (φ f) := by
      simp only [f, map_prod]
      refine IsUnit.prod_iff.2 fun i hi => ?_
      simp only [φ, P, MvPolynomial.aevalTower_X]
      exact ht i (by simpa using hi)
    have hφ' : ∀ y : Submonoid.powers f, IsUnit (φ y) := by
      rintro ⟨_, n, rfl⟩
      simpa using hφ.pow n
    let k₀ : B →ₐ[K] T := IsLocalization.liftAlgHom (M := Submonoid.powers f) hφ'
    have hk₀ : ∀ q, k₀ (emb q) = φ q := fun q => IsLocalization.lift_eq hφ' q
    refine ⟨k₀.comp (e : A.R →ₐ[K] B), ⟨?_, ?_⟩, ?_⟩
    · refine AlgHom.ext fun r => ?_
      change k₀ (e (e.symm (emb (c r)))) = ψ r
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_algebraMap ψ t r
    · intro i
      change k₀ (e (e.symm (emb (MvPolynomial.X i)))) = t i
      rw [AlgEquiv.apply_symm_apply, hk₀]
      exact MvPolynomial.aevalTower_X ψ t i
    · rintro k ⟨h1, h2⟩
      have h3 : ∀ q, k (e.symm (emb q)) = φ q := by
        intro q
        induction q using MvPolynomial.induction_on with
        | C r =>
          have := AlgHom.congr_fun h1 r
          exact this.trans (MvPolynomial.aevalTower_algebraMap ψ t r).symm
        | add a b ha hb => simp only [map_add (f := _), ha, hb]
        | mul_X a i ha =>
          simp only [map_mul, ha, h2]
          rw [show φ (MvPolynomial.X i) = t i from MvPolynomial.aevalTower_X ψ t i]
      have h4 : (k.comp (e.symm : B →ₐ[K] A.R)).toRingHom = k₀.toRingHom :=
        IsLocalization.ringHom_ext (Submonoid.powers f) (RingHom.ext fun q => (h3 q).trans (hk₀ q).symm)
      refine AlgHom.ext fun a => ?_
      have := RingHom.congr_fun h4 (e a)
      simpa using this

theorem exists_testRing_triRing :
    ∀ (K : Type) [Field K] (J : Type) [Fintype J] (m : J → ℕ) (p : TRing K), ∃ (A : TRing K) (π : p.R →ₐ[K] A.R) (X : ∀ τ, Matrix (Fin (m τ)) (Fin (m τ)) A.R) (s : (A.R)ˣ), TriRing m π X s := by
  intro K _ J _ m p
  classical
  obtain ⟨A, π, x, hx, hu⟩ := exists_testRing_universal_partially_invertible K
    (Option (Σ τ : J, {q : Fin (m τ) × Fin (m τ) // q.2 ≤ q.1}))
    (fun o => o.elim True fun z => z.2.1.1 = z.2.1.2) p
  refine ⟨A, π, fun τ => Matrix.of fun i j => if h : j ≤ i then x (some ⟨τ, ⟨(i, j), h⟩⟩) else 0,
    (hx none trivial).unit, ?_, ?_, ?_⟩
  · intro τ i
    simp only [Matrix.of_apply, le_refl, dif_pos]
    exact hx _ rfl
  · intro τ i j hij
    exact dif_neg (not_le.2 hij)
  · intro T _ _ ψ g a hg1 hg2
    obtain ⟨k, ⟨hk1, hk2⟩, hk3⟩ := hu T ψ (fun o => o.elim (a : T) fun z => g z.1 z.2.1.1 z.2.1.2) (by
      rintro (_ | ⟨τ, ⟨i, j⟩, h⟩) hD
      · exact a.isUnit
      · obtain rfl : i = j := hD
        exact hg1 τ i)
    refine ⟨k, ⟨hk1, fun τ => ?_, hk2 none⟩, ?_⟩
    · ext i j
      simp only [Matrix.map_apply, Matrix.of_apply]
      by_cases h : j ≤ i
      · rw [dif_pos h]
        exact hk2 _
      · rw [dif_neg h, map_zero, hg2 τ i j (not_le.1 h)]
    · rintro k' ⟨h1, h2, h3⟩
      refine hk3 k' ⟨h1, ?_⟩
      rintro (_ | ⟨τ, ⟨i, j⟩, h⟩)
      · exact h3
      · have := congrFun (congrFun (h2 τ) i) j
        simp only [Matrix.map_apply, Matrix.of_apply, dif_pos h] at this
        exact this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueCmEmbeddingEigenvectorSum
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_eigen_sum : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (N : Type) [AddCommGroup N] [Module S N] (ρ : 𝓞 E →+* Module.End S N) (m : N), ∃! f : (E →+* ℂ) → N, (∀ τ a, ρ a (f τ) = algebraMap c.F S (embK c τ a) • f τ) ∧ ∑ τ, f τ = m := by
  intro E _ _ _ H l c S _ _ N _ _ ρ m
  classical
  have hσ₀ : Function.Injective (fun τ : E →+* ℂ => embK c τ) := fun τ τ' h =>
    (EigenSplit.isSplitting_complex E).injective
      (RingHom.ext fun a => by
        have h1 := embK_coe c τ a
        have h2 := embK_coe c τ' a
        have h3 : embK c τ a = embK c τ' a := RingHom.congr_fun h a
        exact h1.symm.trans ((congrArg _ h3).trans h2))
  have hσ : EigenSplit.IsSplitting fun τ : E →+* ℂ => (algebraMap c.F S).comp (embK c τ) :=
    EigenSplit.isSplitting_of_isDomain hσ₀ (NumberField.Embeddings.card E ℂ) (algebraMap c.F S) (by
      simpa using (EigenSplit.isUnit_discr_of_charZero (E := E) c.F).map (algebraMap c.F S))
  have hI := EigenSplit.isInternal_eigenSub hσ ρ
  let A := fun τ : E →+* ℂ => EigenSplit.eigenSub ρ ((algebraMap c.F S).comp (embK c τ))
  have hsum : ∀ x : DirectSum _ (fun τ => A τ), DirectSum.coeAddMonoidHom A x = ∑ τ, (x τ : N) :=
    fun x => by
      conv_lhs => rw [← DirectSum.sum_univ_of x]
      set_option synthInstance.maxHeartbeats 100000 in
        simp [map_sum, DirectSum.coeAddMonoidHom_of]
  obtain ⟨x, hx⟩ := hI.2 m
  refine ⟨fun τ => x τ, ⟨fun τ a => EigenSplit.mem_eigenSub.1 (x τ).2 a, (hsum x).symm.trans hx⟩, ?_⟩
  rintro f ⟨hf, hm⟩
  let y : DirectSum _ (fun τ => A τ) :=
    DFinsupp.equivFunOnFintype.symm fun τ => ⟨f τ, EigenSplit.mem_eigenSub.2 (hf τ)⟩
  have hy : y = x := hI.1 (((hsum y).trans hm).trans hx.symm)
  funext τ
  rw [← hy]
  rfl

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUniqueFrameChangeByMatrices
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem existsUnique_comb_matrix {S N : Type} [CommRing S] [AddCommGroup N] [Module S N] {n : ℕ}
    (b : Fin n → N) (g : Matrix (Fin n) (Fin n) S) (hg : IsUnit g.det) (m : N)
    (h : ∃! a : Fin n → S, m = ∑ i, a i • b i) :
    ∃! a : Fin n → S, m = ∑ i, a i • ∑ j, g i j • b j := by
  have key : ∀ a : Fin n → S, ∑ i, a i • ∑ j, g i j • b j = ∑ j, (Matrix.vecMul a g) j • b j := by
    intro a
    simp only [Finset.smul_sum, smul_smul, Matrix.vecMul, dotProduct, Finset.sum_smul]
    rw [Finset.sum_comm]
  obtain ⟨a, ha, hu⟩ := h
  refine ⟨Matrix.vecMul a g⁻¹, ?_, fun a' ha' => ?_⟩
  · show m = _
    rw [key, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul g hg, Matrix.vecMul_one]
    exact ha
  · have h1 := hu (Matrix.vecMul a' g) (Eq.trans ha' (key a'))
    rw [← h1, Matrix.vecMul_vecMul, Matrix.mul_nonsing_inv g hg, Matrix.vecMul_one]

theorem existsUnique_frChg (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H)
    (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y : FrPt Xo c S)
    (g : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a : Sˣ)
    (hg : ∀ τ, IsUnit (g τ).det) : ∃! y' : FrPt Xo c S, FrChg g (a : S) y y' := by
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, hρ, hsm⟩ := _root_.GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  have hid : y.x = spMap (RingHom.id S) ≫ y.x := by
    have : spMap (RingHom.id S) = 𝟙 (Sp S) := by
      simp [spMap]
    rw [this, Category.id_comp]
  obtain ⟨-, hbc, -, hsc⟩ := _root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x hid hid
  obtain ⟨s', hs', hs'u⟩ := _root_.GlobalTheory.Frames.SecPull.existsUnique_secBC E H Dw l Xo S S (RingHom.id S) (a : S) y.x y.x hid y.s
  have heig : ∀ τ m, IsEigAt c τ (v m) ↔ ∀ z : 𝓞 E, ρ z m = algebraMap c.F S (embK c τ z) • m := by
    intro τ m
    refine forall_congr' fun z => ?_
    rw [← hρ, ← hsm, hinj.eq_iff]
  choose b hb using fun τ i => (htan (y.u τ i)).1 (y.tan τ i)
  have hbu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  have hs'f := (hbc (a : S) y.s s').1 hs'
  refine ⟨⟨y.x, y.x_over, fun τ i => v (∑ j, g τ i j • b τ j), fun τ i => (htan _).2 ⟨_, rfl⟩,
    fun τ i => ?_, fun τ w hw hwe => ?_, s', fun t => ?_⟩, ⟨rfl, fun τ i => ?_, hs'⟩, ?_⟩
  · rw [heig]
    intro z
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have := (heig τ (b τ j)).1 (by rw [hb]; exact y.eig τ j) z
    rw [map_smul, this, smul_comm]
  · have h := y.basis τ w hw hwe
    obtain ⟨m, rfl⟩ := (htan w).1 hw
    rw [hbu τ] at h
    simp only [hcomb, hinj.eq_iff] at h ⊢
    exact existsUnique_comb_matrix (b τ) (g τ) (hg τ) m h
  · obtain ⟨e, he, heu⟩ := y.gen t
    refine ⟨e * (a⁻¹ : Sˣ), fun i => ?_, fun e' he' => ?_⟩
    · rw [hs'f, ← _root_.mul_assoc, ← (hsc _ _ i).1, Units.inv_mul_cancel_right]
      exact he i
    · have := heu (e' * a) (fun i => by rw [(hsc _ _ i).1, _root_.mul_assoc, ← hs'f]; exact he' i)
      rw [← this, Units.mul_inv_cancel_right]
  · rw [hbu τ, hcomb]
  · rintro ⟨x', hx', u', ht', he', hb', t', hg'⟩ ⟨hx, hu, hs⟩
    dsimp only at hx hu hs
    subst hx
    have e1 : t' = s' := hs'u t' hs
    have e2 : u' = fun τ i => v (∑ j, g τ i j • b τ j) := by
      funext τ i
      have := hu τ i
      rw [hbu τ, hcomb] at this
      exact this
    subst e1 e2
    rfl

end GlobalTheory.Frames
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsUnitaryMatrixOfLatticeIsometry
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree
open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Frames GlobalTheory.FrameUnif
open scoped Matrix nonZeroDivisors

namespace GlobalTheory.IsoExt

theorem exists_gl_of_equiv {E : Type} [Field E] [NumberField E] {r : ℕ} {L L' : Type}
    [AddCommGroup L] [Module (𝓞 E) L] [AddCommGroup L'] [Module (𝓞 E) L']
    (φ : L →ₗ[𝓞 E] (Fin r → E)) (φ' : L' →ₗ[𝓞 E] (Fin r → E))
    (hφ : Function.Injective φ) (hspan : Submodule.span E (Set.range φ) = ⊤)
    (hφ' : Function.Injective φ') (hspan' : Submodule.span E (Set.range φ') = ⊤)
    (gam : L ≃ₗ[𝓞 E] L') : ∃ γ : GL (Fin r) E,
      ∀ v, (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ v = φ' (gam v) := by
  obtain ⟨A, hA⟩ := GlobalTheory.FrameFibre.exists_matrix φ hφ hspan (φ' ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := GlobalTheory.FrameFibre.exists_matrix φ' hφ' hspan' (φ ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v, A *ᵥ φ v = φ' (gam v) := hA
  have hB' : ∀ v, B *ᵥ φ' v = φ (gam.symm v) := hB
  have hAB : A * B = 1 := by
    apply Matrix.toLin'.injective
    refine LinearMap.ext_on_range hspan' fun v => ?_
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, ← Matrix.mulVec_mulVec, hB', hA',
      Matrix.one_mulVec, LinearEquiv.apply_symm_apply]
  exact ⟨⟨A, B, hAB, mul_eq_one_comm.1 hAB⟩, hA'⟩

theorem exists_unitary_of_isometry : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (D D' : Datum H) (r : ℕ) (ξ : E) (Gm : Matrix (Fin r) (Fin r) E) (φ : D.La →ₗ[𝓞 E] (Fin r → E)) (φ' : D'.La →ₗ[𝓞 E] (Fin r → E)) (gam : D.La ≃ₗ[𝓞 E] D'.La), cc ξ = -ξ → (Function.Injective φ ∧ Submodule.span E (Set.range φ) = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ x) (φ y))) → (Function.Injective φ' ∧ Submodule.span E (Set.range φ') = ⊤ ∧ (∀ a b, cc (Gm a b) = Gm b a) ∧ Gm.det ≠ 0 ∧ ∀ x y, ((D'.EF x y : ℤ) : ℚ) = Algebra.trace ℚ E (ξ * herm Gm (φ' x) (φ' y))) → (∀ a b, D'.EF (gam a) (gam b) = D.EF a b) → ∃ γ : GL (Fin r) E, (∀ u v, herm Gm ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u) ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v) = herm Gm u v) ∧ ∀ a, φ' (gam a) = (γ : Matrix (Fin r) (Fin r) E) *ᵥ φ a := by
  intro E _ _ _ H D D' r ξ Gm φ φ' gam _ hl hl' hiso
  obtain ⟨γ, hγ⟩ := exists_gl_of_equiv φ φ' hl.1 hl.2.1 hl'.1 hl'.2.1 gam
  refine ⟨γ, ?_, fun a => (hγ a).symm⟩
  by_cases hξ : ξ = 0
  · have h0 : ∀ x : D.La, x = 0 := fun x => by
      apply D.unimod.1
      rw [map_zero]
      refine LinearMap.ext fun y => ?_
      have h := hl.2.2.2.2 x y
      rw [hξ, zero_mul, map_zero] at h
      exact_mod_cast h
    have h1 : ∀ u : Fin r → E, u = 0 := fun u => by
      have hu : u ∈ Submodule.span E (Set.range φ) := by rw [hl.2.1]; trivial
      have hle : Submodule.span E (Set.range φ) ≤ ⊥ := Submodule.span_le.2 (by
        rintro _ ⟨x, rfl⟩
        rw [h0 x, map_zero]
        exact Submodule.zero_mem _)
      exact hle hu
    intro u v
    rw [h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ u), h1 ((γ : Matrix (Fin r) (Fin r) E) *ᵥ v), h1 u,
      h1 v]
  · exact GlobalTheory.FrameFibre.herm_of_trace φ hl.2.1 Gm γ ξ hξ fun v w => by
      rw [hγ, hγ, ← hl.2.2.2.2, ← hl'.2.2.2.2, hiso]

end GlobalTheory.IsoExt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteIntegralClosureOfIsIntegrallyClosed
section
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap)
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.AbLaw

namespace GlobalTheory.NormFin

theorem finite_of_semilinear_injective {R S N M : Type*} [CommRing R] [IsNoetherianRing R]
    [CommRing S] [AddCommGroup N] [Module R N] [AddCommGroup M] [Module S M] [Module.Finite S M]
    (φ : R →+* S) (hφ : φ.Finite) (f : N →ₛₗ[φ] M) (hf : Function.Injective f) :
    Module.Finite R N := by
  letI := φ.toAlgebra
  letI : Module R M := Module.compHom M φ
  haveI : IsScalarTower R S M := ⟨fun r s m => mul_smul (φ r) s m⟩
  haveI : Module.Finite R S := hφ
  haveI : Module.Finite R M := Module.Finite.trans S M
  let g : N →ₗ[R] M :=
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r x => f.map_smulₛₗ r x }
  exact Module.Finite.of_injective g hf

theorem finite_iterateFrobenius (k P : Type*) [Field k] [PerfectField k] [CommRing P]
    [Algebra k P] [Algebra.FiniteType k P] (p : ℕ) [ExpChar k p] [ExpChar P p] (e : ℕ) :
    (iterateFrobenius P p e).Finite := by
  refine RingHom.IsIntegral.to_finite ?_ ?_
  · intro x
    refine ⟨Polynomial.X ^ (p ^ e) - Polynomial.C x,
      Polynomial.monic_X_pow_sub_C _ (pow_ne_zero _ (expChar_ne_zero k p)), ?_⟩
    simp [iterateFrobenius_def]
  · refine RingHom.FiniteType.of_comp_finiteType (f := algebraMap k P) ?_
    have h : (iterateFrobenius P p e).comp (algebraMap k P) =
        (algebraMap k P).comp (iterateFrobenius k p e) := by
      ext x
      simp [iterateFrobenius_def]
    rw [h]
    exact (RingHom.finiteType_algebraMap.mpr inferInstance).comp
      (.of_surjective _ (bijective_iterateFrobenius k p e).2)

theorem finite_integralClosure_of_isIntegrallyClosed (k P K F : Type*) [Field k] [PerfectField k]
    [CommRing P] [IsDomain P] [IsIntegrallyClosed P] [Algebra k P] [Algebra.FiniteType k P]
    [Field K] [Algebra P K] [IsFractionRing P K] [Field F] [Algebra K F] [Algebra P F]
    [IsScalarTower P K F] [FiniteDimensional K F] : Module.Finite P (integralClosure P F) := by
  haveI : IsNoetherianRing P := Algebra.FiniteType.isNoetherianRing k P
  obtain ⟨p, hp⟩ := ExpChar.exists k
  haveI : ExpChar P p := expChar_of_injective_algebraMap (algebraMap k P).injective p
  haveI : ExpChar K p := expChar_of_injective_algebraMap (IsFractionRing.injective P K) p
  haveI : ExpChar F p := expChar_of_injective_algebraMap (algebraMap K F).injective p
  let E := separableClosure K F
  haveI : ExpChar E p := expChar_of_injective_algebraMap (algebraMap K E).injective p
  haveI : Module.Finite P (integralClosure P E) := IsIntegralClosure.finite P K E _
  haveI : IsScalarTower P E F := .of_algebraMap_eq' rfl
  let e := IsPurelyInseparable.exponent E F
  have hE : ∀ z : F, z ^ p ^ e ∈ E := fun z => by
    obtain ⟨y, hy⟩ := IsPurelyInseparable.exponent_def' E p z
    exact hy ▸ y.2
  let f : integralClosure P F →ₛₗ[iterateFrobenius P p e] integralClosure P E :=
    { toFun := fun z => ⟨⟨z.1 ^ p ^ e, hE _⟩,
        (isIntegral_algHom_iff (IsScalarTower.toAlgHom P E F) Subtype.val_injective).mp
          (IsIntegral.pow z.2 _)⟩
      map_add' := fun x y => Subtype.ext (Subtype.ext (add_pow_expChar_pow _ _ _ _))
      map_smul' := fun r x => Subtype.ext (Subtype.ext (by
        change (r • x.1) ^ p ^ e = (r ^ p ^ e) • x.1 ^ p ^ e
        rw [smul_pow])) }
  refine finite_of_semilinear_injective _ (finite_iterateFrobenius k P p e) f fun x y h => ?_
  have h1 : x.1 ^ p ^ e = y.1 ^ p ^ e := congrArg (fun w : integralClosure P E => (w.1.1 : F)) h
  exact Subtype.ext ((iterateFrobenius F p e).injective h1)

theorem finite_integralClosure_of_perfectField (k B F L : Type*) [Field k] [PerfectField k]
    [CommRing B] [IsDomain B] [Algebra k B] [Algebra.FiniteType k B] [Field F] [Algebra B F]
    [IsFractionRing B F] [Field L] [Algebra F L] [Algebra B L] [IsScalarTower B F L]
    [FiniteDimensional F L] : Module.Finite B (integralClosure B L) := by
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k B
  let P := MvPolynomial (Fin s) k
  letI : Algebra P B := g.toRingHom.toAlgebra
  haveI : Module.Finite P B := hfin
  haveI : FaithfulSMul P B := (faithfulSMul_iff_algebraMap_injective _ _).mpr hinj
  letI : Algebra P F := ((algebraMap B F).comp (algebraMap P B)).toAlgebra
  haveI : IsScalarTower P B F := .of_algebraMap_eq' rfl
  letI : Algebra P L := ((algebraMap B L).comp (algebraMap P B)).toAlgebra
  haveI : IsScalarTower P B L := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P F L := .of_algebraMap_eq fun x => IsScalarTower.algebraMap_apply B F L _
  haveI : FaithfulSMul P F := (faithfulSMul_iff_algebraMap_injective _ _).mpr
    ((IsFractionRing.injective B F).comp hinj)
  let K := FractionRing P
  letI : Algebra K F := FractionRing.liftAlgebra P F
  haveI : FiniteDimensional K F := Module.Finite.of_isLocalization P B (nonZeroDivisors P)
  letI : Algebra K L := ((algebraMap F L).comp (algebraMap K F)).toAlgebra
  haveI : IsScalarTower K F L := .of_algebraMap_eq' rfl
  haveI : IsScalarTower P K L := .of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply K F L, ← IsScalarTower.algebraMap_apply P K F,
      ← IsScalarTower.algebraMap_apply P F L]
  haveI : FiniteDimensional K L := Module.Finite.trans F L
  haveI := finite_integralClosure_of_isIntegrallyClosed k P K L
  have h : Module.Finite P ((integralClosure B L).restrictScalars P) := by
    rwa [integralClosure_restrictScalars_of_isIntegral]
  haveI : Module.Finite P (integralClosure B L) := h
  exact Module.Finite.of_restrictScalars_finite P B _

theorem finite_integralClosure_of_isAlgClosed :
    ∀ (k : Type) [Field k] [IsAlgClosed k] (B : Type) [CommRing B] [IsDomain B] [Algebra k B]
      [Algebra.FiniteType k B] (F : Type) [Field F] [Algebra B F] [IsFractionRing B F],
      Module.Finite B (integralClosure B F) :=
  fun k _ _ B _ _ _ _ F _ _ _ => finite_integralClosure_of_perfectField k B F F

end GlobalTheory.NormFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameChangeByMatricesReflAndComp
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.Frames

namespace GlobalTheory.Frames

theorem frChg_refl_and_comp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (S : Type) [CommRing S] [Algebra c.F S] (y y' y'' : FrPt Xo c S), FrChg (fun _ => 1) 1 y y ∧ ∀ (g g' : (∀ τ : E →+* ℂ, Matrix (Fin (Dw.mult τ)) (Fin (Dw.mult τ)) S)) (a a' : S), FrChg g a y y' → FrChg g' a' y' y'' → FrChg (fun τ => g' τ * g τ) (a' * a) y y'' := by
  intro E _ _ _ H Dw l Xo c S _ _ y y' y''
  have hid : y.x = spMap (RingHom.id S) ≫ y.x := by
    have : spMap (RingHom.id S) = 𝟙 (Sp S) := Spec.map_id _
    rw [this, Category.id_comp]
  obtain ⟨-, h2, -, h4⟩ := _root_.GlobalTheory.Frames.SecCalc.sec_calc E H Dw l Xo S S S (RingHom.id S) (RingHom.id S) y.x y.x y.x hid hid
  obtain ⟨N, _, _, v, ρ, hinj, htan, hcomb, -, -⟩ := _root_.GlobalTheory.TanMod.exists_tangent_module E H Dw l Xo S y.x
  have hb : ∀ τ i, ∃ m, v m = y.u τ i := fun τ i => (htan _).1 (y.tan τ i)
  choose b hb using hb
  have hu : ∀ τ, y.u τ = fun i => v (b τ i) := fun τ => funext fun i => (hb τ i).symm
  refine ⟨⟨rfl, fun τ i => ?_, ?_⟩, ?_⟩
  · rw [hu τ, hcomb]
    simp [Matrix.one_apply]
  · rw [h2]
    intro i
    rw [(h4 1 1 i).2.2, _root_.one_mul]
  · rintro g g' a a' ⟨hx, hc, hs⟩ ⟨hx', hc', hs'⟩
    obtain ⟨x', xo', u', t', e', b', s', gen'⟩ := y'
    obtain ⟨x'', xo'', u'', t'', e'', b'', s'', gen''⟩ := y''
    dsimp only at hx hx' hc hc' hs hs'
    subst hx'
    subst hx
    refine ⟨rfl, fun τ i => ?_, ?_⟩
    · have h1 : u' τ = fun j => v (∑ k, g τ j k • b τ k) := by
        funext j
        have := hc τ j
        rw [hu τ, hcomb] at this
        exact this
      have h3 := hc' τ i
      rw [h1, hcomb] at h3
      dsimp only
      rw [hu τ, hcomb, h3]
      congr 1
      simp only [Matrix.mul_apply, Finset.smul_sum, Finset.sum_smul, smul_smul]
      exact Finset.sum_comm
    · dsimp only
      rw [h2] at hs hs' ⊢
      intro i
      rw [hs' i, hs i, (h4 a' a i).1, _root_.mul_assoc]

end GlobalTheory.Frames
end

