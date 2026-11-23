module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import ReciprocityTheory.DualLattices.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0027
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsConjugateUnitaryKTypeSameWeight
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0206
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
public import Formalism.LocalRingCardinality.Bundle0007
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0175
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemClosureUnitary
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0205

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLocalHoweContractionCompactUnitary
section
open Formalism.MainNotions.S Matrix GlobalTheory.CompactHowe
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CompactHowe.Contraction

open MvPolynomial ReciprocityTheory.PGsh

theorem mem_iff {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : g ∈ UJset (allPos k) ↔ gᴴ * g = 1 := by
  have h : Formalism.REAL.Jm (allPos k) = 1 := by simp [Formalism.REAL.Jm, allPos]
  show gᴴ * Formalism.REAL.Jm (allPos k) * g = Formalism.REAL.Jm (allPos k) ↔ _
  rw [h, Matrix.mul_one]

theorem map_star_map_star {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).map star = g := by
  ext i j; simp

theorem map_star_mem {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    g.map star ∈ UJset (allPos k) := by
  rw [mem_iff] at hg ⊢
  ext i j
  have := congrArg star (congrFun (congrFun hg i) j)
  simp only [Matrix.mul_apply, star_sum, star_mul', Matrix.conjTranspose_apply, Matrix.map_apply] at this ⊢
  rw [this]
  by_cases h : i = j <;> simp [Matrix.one_apply, h]

theorem inv_transpose {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    (g⁻¹)ᵀ = g.map star := by
  rw [Matrix.inv_eq_left_inv ((mem_iff g).1 hg)]
  ext i j; simp

theorem det_map_star {k : ℕ} (g : Matrix (Fin k) (Fin k) ℂ) : (g.map star).det = star g.det := by
  rw [← Matrix.det_conjTranspose, ← Matrix.det_transpose]
  rfl

theorem star_det {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    star g.det = g.det⁻¹ := by
  have := congrArg Matrix.det ((mem_iff g).1 hg)
  rw [Matrix.det_mul, Matrix.det_conjTranspose, Matrix.det_one] at this
  exact eq_inv_of_mul_eq_one_left this

theorem conjTranspose_mem {k : ℕ} {g : Matrix (Fin k) (Fin k) ℂ} (hg : g ∈ UJset (allPos k)) :
    gᴴ ∈ UJset (allPos k) := by
  rw [mem_iff] at hg ⊢
  rw [Matrix.conjTranspose_conjTranspose]
  exact mul_eq_one_comm.1 hg

variable {N n : ℕ}

theorem fischer_swap (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (rename Prod.swap P) (rename Prod.swap Q) = fischer P Q := by
  classical
  have hinj : Function.Injective (Prod.swap : Fin N × Fin n → Fin n × Fin N) := Prod.swap_injective
  rw [fischer_eq_sum _ _ _ subset_rfl, fischer_eq_sum P Q _ subset_rfl,
    support_rename_of_injective hinj, Finset.sum_image
      (fun a _ b _ h => Finsupp.mapDomain_injective hinj h)]
  refine Finset.sum_congr rfl fun A _ => ?_
  rw [coeff_rename_mapDomain _ hinj, coeff_rename_mapDomain _ hinj]
  congr 1
  unfold fw
  rw [Finsupp.prod_mapDomain_index_inj hinj]

theorem subst2_row (h : Matrix (Fin N) (Fin N) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    subst2 h 1 P = rowSubst h P := by
  have key : subst2 h (1 : Matrix (Fin n) (Fin n) ℂ) = rowSubst h := by
    refine algHom_ext fun p => ?_
    rw [subst2_X, rowSubst_X]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single p.2]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  rw [key]

theorem subst2_col (g : Matrix (Fin n) (Fin n) ℂ) (P : MvPolynomial (Fin N × Fin n) ℂ) :
    rename Prod.swap (subst2 1 g P) = rowSubst g (rename Prod.swap P) := by
  have key : (rename Prod.swap).comp (subst2 (1 : Matrix (Fin N) (Fin N) ℂ) g) =
      (rowSubst g).comp (rename Prod.swap) := by
    refine algHom_ext fun p => ?_
    rw [AlgHom.comp_apply, AlgHom.comp_apply, rename_X, subst2_X, rowSubst_X,
      Finset.sum_eq_single p.1]
    · simp
    · intro l _ hl; simp [Matrix.one_apply_ne hl]
    · simp
  exact congrArg (fun f => f P) key

theorem fischer_subst2 (h : Matrix (Fin N) (Fin N) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (subst2 h g P) Q = fischer P (subst2 hᴴ gᴴ Q) := by
  have h1 : subst2 h g P = subst2 h 1 (subst2 1 g P) := by rw [subst2_mul]; simp
  have h2 : subst2 hᴴ gᴴ Q = subst2 1 gᴴ (subst2 hᴴ 1 Q) := by rw [subst2_mul]; simp
  rw [h1, h2, subst2_row, fischer_rowSubst, ← subst2_row, ← fischer_swap, subst2_col,
    fischer_rowSubst, ← subst2_col, fischer_swap]

theorem fischer_subst2_unitary {h : Matrix (Fin N) (Fin N) ℂ} {g : Matrix (Fin n) (Fin n) ℂ}
    (hh : h ∈ UJset (allPos N)) (hg : g ∈ UJset (allPos n)) (P Q : MvPolynomial (Fin N × Fin n) ℂ) :
    fischer (subst2 h g P) (subst2 h g Q) = fischer P Q := by
  rw [fischer_subst2, subst2_mul, (mem_iff h).1 hh, (mem_iff g).1 hg, subst2_one]

theorem exists_contraction {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [FiniteDimensional ℂ H] {H' E : Type} [AddCommGroup H'] [Module ℂ H'] [AddCommGroup E] [Module ℂ E]
    (J : H' →ₛₗ[starRingEnd ℂ] E) (Ψ : E →ₗ[ℂ] H →ₗ[ℂ] MvPolynomial (Fin N × Fin n) ℂ) :
    ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H,
      ∀ P v u, inner ℂ u (I P v) = fischer P (Ψ (J v) u) := by
  let b := stdOrthonormalBasis ℂ H
  refine ⟨LinearMap.mk₂ ℂ (fun P v => ∑ i, fischer P (Ψ (J v) (b i)) • b i) ?_ ?_ ?_ ?_, ?_⟩
  · intro P P' v
    simp only [fischer_add_left, add_smul, Finset.sum_add_distrib]
  · intro c P v
    simp only [fischer_smul_left, Finset.smul_sum, smul_smul]
  · intro P v v'
    simp only [map_add (f := _), LinearMap.add_apply, fischer_add_right, add_smul, Finset.sum_add_distrib]
  · intro c P v
    simp only [LinearMap.map_smulₛₗ, map_smul, LinearMap.smul_apply, fischer_smul_right, Finset.smul_sum,
      smul_smul, Complex.conj_conj, RingHom.id_apply]
  · intro P v u
    conv_rhs => rw [← b.sum_repr' u]
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [LinearMap.mk₂_apply, inner_sum, inner_smul_right, map_sum, map_smul, fischer_sum_right,
      fischer_smul_right, inner_conj_symm]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _

end GlobalTheory.CompactHowe.Contraction

namespace GlobalTheory.CompactHowe

open Contraction ReciprocityTheory.PGsh

theorem exists_local_contraction : ∀ (N n : ℕ) (hn : n ≤ N) (ν : Fin N → ℕ) (x₁ x₃ : ℤ) (Λ : Fin n → ℝ) (Λ' : Fin N → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (H' : Type) [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [FiniteDimensional ℂ H'] (σ' : Matrix (Fin N) (Fin N) ℂ → (H' →L[ℂ] H')), Antitone ν → (∀ b : Fin N, n ≤ (b : ℕ) → ν b = 0) → (∀ a, Λ a = (x₃ : ℝ) - ν (Fin.castLE hn (Fin.rev a))) → (∀ b, Λ' b = -(x₁ : ℝ) - ν (Fin.rev b)) → IsURepOn (UJset (allPos n)) σ → IsKTypeOf (allPos n) σ Λ ⊤ → IsURepOn (UJset (allPos N)) σ' → IsKTypeOf (allPos N) σ' Λ' ⊤ → ∃ I : MvPolynomial (Fin N × Fin n) ℂ →ₗ[ℂ] H' →ₗ[ℂ] H, I ≠ 0 ∧ ∀ h ∈ UJset (allPos N), ∀ g ∈ UJset (allPos n), ∀ P v, I ((h.det ^ x₁ * g.det ^ x₃) • subst2 h (g⁻¹)ᵀ P) (σ' h v) = σ g (I P v) := by
  intro N n hn ν x₁ x₃ Λ Λ' H _ _ _ σ H' _ _ _ σ' hν hν0 hΛ hΛ' hσ hK hσ' hK'
  obtain ⟨hτ, hτK⟩ := _root_.GlobalTheory.ConjTwist.conj_twist_isKTypeOf n Λ x₃ H σ hσ hK
  obtain ⟨hτ', hτK'⟩ := _root_.GlobalTheory.ConjTwist.conj_twist_isKTypeOf N Λ' (-x₁) H' σ' hσ' hK'
  have e1 : (fun a => ((x₃ : ℤ) : ℝ) - Λ (Fin.rev a)) = fun a => (ν (Fin.castLE hn a) : ℝ) := by
    funext a; rw [hΛ, Fin.rev_rev]; ring
  have e2 : (fun b => ((-x₁ : ℤ) : ℝ) - Λ' (Fin.rev b)) = fun b => (ν b : ℝ) := by
    funext b; rw [hΛ', Fin.rev_rev]; push_cast; ring
  rw [e1] at hτK
  rw [e2] at hτK'
  obtain ⟨E, i1, i2, i3, π, J, hJ, hπ, hπK, hπJ⟩ := _root_.GlobalTheory.ConjugateType.exists_conjugate_type N _ H' _ hτ' hτK'
  obtain ⟨Ψ, hΨ0, hΨ⟩ := _root_.GlobalTheory.CompactHoweJoint.exists_joint_intertwiner N n hn ν H _ E π hν hν0 hτ hτK hπ hπK
  obtain ⟨I, hI⟩ := exists_contraction J Ψ
  refine ⟨I, fun h0 => hΨ0 ?_, fun h hh g hg P v => ?_⟩
  · ext1 w
    ext1 u
    obtain ⟨v, rfl⟩ := hJ.2 w
    by_contra hne
    apply fischer_self_ne_zero _ hne
    rw [← hI, h0]
    simp
  · refine ext_inner_left ℂ fun w => ?_
    obtain ⟨u, rfl⟩ : ∃ u, σ g u = w := by
      refine ⟨σ gᴴ w, ?_⟩
      have := hσ.1.2 g hg _ (conjTranspose_mem hg)
      rw [mul_eq_one_comm.1 ((mem_iff g).1 hg), hσ.1.1] at this
      simpa using (congrArg (fun f => f w) this).symm
    have hiso : inner ℂ (σ g u) (σ g (I P v)) = inner ℂ u (I P v) :=
      (LinearIsometry.mk (σ g : H →ₗ[ℂ] H) (hσ.2.1 g hg)).inner_map_map u (I P v)
    rw [hiso, hI, hI, inv_transpose hg, fischer_smul_left,
      ← fischer_subst2_unitary hh (map_star_mem hg) P, ← hΨ h hh _ (map_star_mem hg), hπJ]
    simp only [map_star_map_star, det_map_star, ContinuousLinearMap.smul_apply, LinearMap.map_smulₛₗ,
      map_smul, LinearMap.smul_apply, fischer_smul_right, RingHom.id_apply, Complex.conj_conj,
      map_zpow₀, starRingEnd_apply, star_star]
    rw [star_det hh, _root_.inv_zpow', neg_neg]
    ring

end GlobalTheory.CompactHowe

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPolynomialModelCoefficientSpaceRealPoints
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum GlobalTheory.JointHarm
open scoped TensorProduct InnerProductSpace Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CoefReal

open GlobalTheory.CoefModel

theorem vact_eq_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) (g : ι → GL (Fin n) ℂ) :
    vact lam (fun τ => (g τ : Matrix (Fin n) (Fin n) ℂ)) = actP lam (invTrK g) := by
  unfold vact actP trAct
  rw [detTw_eq]
  simp only [invTrK_coe, Matrix.transpose_transpose, Matrix.det_transpose, Pi.inv_apply, Matrix.coe_units_inv,
    Matrix.det_nonsing_inv, Ring.inverse_eq_inv', _root_.zpow_neg, _root_.inv_zpow]

theorem continuous_coeff_actP {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n) {X : Type} [TopologicalSpace X]
    (A : X → ι → GL (Fin n) ℂ) (hA : ∀ τ, Continuous fun x => (A x τ : Matrix (Fin n) (Fin n) ℂ)) (F : Pol ℂ ι n)
    (m : ι × Fin n × Fin n →₀ ℕ) : Continuous fun x => AddMonoidAlgebra.coeff (actP lam (A x) F) m := by
  simp only [actP, LinearMap.smul_apply, MvPolynomial.coeff_smul, smul_eq_mul, detTw_eq, AlgHom.toLinearMap_apply, trAct]
  refine Continuous.mul (continuous_finsetProd _ fun τ _ => (hA τ).matrix_det.zpow₀ _ fun x => Or.inl ?_)
    (continuous_coeff_blockAct _ (fun τ => (hA τ).matrix_transpose) _ m)
  exact ((Matrix.isUnit_iff_isUnit_det _).1 (A x τ).isUnit).ne_zero

theorem exists_scalarExt {ι : Type} [Fintype ι] {n : ℕ} {K : Type} [Field K] (φ : K →+* ℂ) (lam : ι → DomWeight n)
    {W : Type} [AddCommGroup W] [Module ℂ W] (c0 : VV K lam →ₛₗ[φ] W)
    (h1 : LinearIndependent ℂ fun i => c0 (bVV K lam i))
    (h2 : Submodule.span ℂ (Set.range fun i => c0 (bVV K lam i)) = ⊤) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] W, ∀ v, e (mapVV φ lam v) = c0 v := by
  let b1 := Module.Basis.mk (linearIndependent_mapVV φ lam) (span_mapVV φ lam).ge
  let b2 := Module.Basis.mk h1 h2.ge
  refine ⟨b1.equiv b2 (Equiv.refl _), fun v => ?_⟩
  have : (b1.equiv b2 (Equiv.refl _)).toLinearMap.comp (mapVV φ lam) = c0 := by
    refine (bVV K lam).ext fun i => ?_
    have h := b1.equiv_apply i b2 (Equiv.refl _)
    simpa [b1, b2] using h
  exact LinearMap.congr_fun this v

variable {D : D7}

theorem exists_real_model (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank)
    (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W) (hθ : IsInfFam θ) (hc : c.Is)
    (ht : Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam)) :
    ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, (∀ v, e (mapVV D.what₂.embLL lam v) = c0 v) ∧
      ∀ u ∈ GinfC V, ∀ v, c.ρ u (e v) = e (rhoK lam (invTrK (realGL θ V u)) v) := by
  obtain ⟨e, he⟩ : ∃ e : VV ℂ lam ≃ₗ[ℂ] c.W, ∀ v, e (mapVV D.what₂.embLL lam v) = c0 v :=
    exists_scalarExt D.what₂.embLL lam c0 ht.2.1 ht.2.2
  refine ⟨e, he, fun u hu v => ?_⟩
  haveI := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have hlab : ∀ τ x, D.what₂.embLL (labLL D τ x) = tauE D τ x := fun τ x =>
    DFunLike.congr_fun (GlobalTheory.ThetaFiresProbe.labE_fixed τ) x
  have hrat : ∀ (γ : GQ V) (v : VV ℂ lam), c.ρ γ.1 (e v) = e (rhoK lam (invTrK (realGL θ V γ.1)) v) := by
    intro γ v
    obtain ⟨γE, hγ⟩ : ∃ γE, Bridge.IsRatMat V γ γE := by
      obtain ⟨γ, ⟨g, -, hg⟩⟩ := γ
      exact ⟨g, hg.symm⟩
    have e1 : (fun τ => Formalism.UG.bc D.what₂.embLL (invTrK (embGL (labLL D) γE) τ)) = invTrK (realGL θ V γ) := by
      funext τ
      apply Units.ext
      rw [bc_coe, invTrK_coe, invTrK_coe, realGL_rat hθ V γ γE hγ, embGL_inv, ← map_inv, embGL_coe, bc_coe]
      ext a b
      exact hlab _ _
    have : (c.ρ γ).comp e.toLinearMap = e.toLinearMap.comp (rhoK lam (invTrK (realGL θ V γ))) := by
      refine LinearMap.ext_on_range (span_mapVV D.what₂.embLL lam) fun i => ?_
      show c.ρ γ (e _) = e (rhoK lam (invTrK (realGL θ V γ)) _)
      rw [← e1, ← mapVV_rhoK, he, he]
      exact (ht.1 γ γE hγ _).symm
    exact LinearMap.congr_fun this v
  have hfin : ∀ k ∈ GfC V, realGL θ V k = 1 := fun k hk => funext fun τ => by
    show Formalism.UG.bc (θ τ) (infHom V k) = 1
    rw [show infHom V k = 1 from hk, map_one]
  rw [← e.symm_apply_eq]
  refine Subtype.ext (MvPolynomial.ext _ _ fun m => ?_)
  let L : c.W →ₗ[ℂ] ℂ := MvPolynomial.lcoeff ℂ m ∘ₗ (VV ℂ lam).subtype ∘ₗ e.symm.toLinearMap
  have hf : Continuous fun h => L (c.ρ h (e v)) := L.continuous_of_finiteDimensional.comp (hc.2.2.1 _)
  have hg : Continuous fun h => AddMonoidAlgebra.coeff (actP lam (invTrK (realGL θ V h)) v.1) m := by
    refine continuous_coeff_actP lam _ (fun τ => ?_) _ m
    refine (((realGL_laws hθ V).1 τ).comp continuous_inv).matrix_transpose.congr fun h => ?_
    show (realGL θ V h⁻¹ τ : Matrix (Fin V.rank) (Fin V.rank) ℂ)ᵀ = _
    rw [map_inv]
    rfl
  by_contra hne
  obtain ⟨γ, hγ, k, hk, hU, -⟩ := GlobalTheory.RealApprox.weak_approx_real V u hu _ (isOpen_ne_fun hf hg) hne
  refine hU ?_
  show L (c.ρ (γ * k) (e v)) = AddMonoidAlgebra.coeff (actP lam (invTrK (realGL θ V (γ * k))) v.1) m
  rw [map_mul, map_mul (realGL θ V), hc.1 k hk, hfin k hk, mul_one, mul_one, hrat ⟨γ, hγ⟩ v]
  simp [L, rhoK_coe]

theorem exists_poly_model : ∀ (D : D7) (V : HSp D) (θ : InfFam D) (c : CoefA V) (lam : D.what₂.Tau → DomWeight V.rank) (c0 : VV D.what₂.LL lam →ₛₗ[D.what₂.embLL] c.coef.W), IsInfFam θ → c.Is → Bridge.CoefMapTie V c.coef c0 (rhoVr (labLL D) lam) → ∀ BS : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ, (∀ τ, IsUnit (BS τ)) → ∃ j : c.W →ₗ[ℂ] Pol ℂ D.what₂.Tau V.rank, LinearMap.range j = VV ℂ lam ∧ ∀ u ∈ GinfC V, ∀ w, j (c.ρ u w) = vact lam (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) (j w) := by
  intro D V θ c lam c0 hθ hc ht BS hBS
  obtain ⟨e, -, he⟩ := exists_real_model V θ c lam c0 hθ hc ht
  choose B hB using hBS
  refine ⟨(VV ℂ lam).subtype ∘ₗ rhoK lam (invTrK B⁻¹) ∘ₗ e.symm.toLinearMap, ?_, fun u hu w => ?_⟩
  · have hs : Function.Surjective (rhoK lam (invTrK B⁻¹)) := fun x => ⟨rhoK lam (invTrK B) x, by
      rw [← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel, map_one, map_one, Module.End.one_apply]⟩
    rw [LinearMap.range_comp, LinearMap.range_comp, LinearEquiv.range, Submodule.map_top,
      LinearMap.range_eq_top.2 hs, Submodule.map_top,
      Submodule.range_subtype]
  · obtain ⟨v, rfl⟩ := e.surjective w
    have e1 : (fun τ => (BS τ)⁻¹ * compAt θ τ (Formalism.L2.Theta.mt V u) * BS τ) =
        fun τ => (((B⁻¹ * realGL θ V u * B) τ : GL (Fin V.rank) ℂ) : Matrix (Fin V.rank) (Fin V.rank) ℂ) := by
      funext τ
      rw [← hB τ, ← Matrix.coe_units_inv]
      rfl
    rw [e1, vact_eq_actP, he u hu v]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply, Submodule.subtype_apply]
    rw [← rhoK_coe, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← map_mul, ← map_mul,
      mul_inv_cancel_right]

end GlobalTheory.CoefReal

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FixedPlaceUnitaryLocalPointsEquivLocalUnitaryGro
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.Mem.Chr

namespace GlobalTheory.DefU.Inert

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

theorem conjPl_self (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) : ConjPl (IsCMField.complexConj E).toRingEquiv w w := fun k => by
  have h1 : Valued.v (algebraMap E (w.adicCompletion E) k) = w.valuation E k :=
    w.valuedAdicCompletion_eq_valuation' k
  have h2 : Valued.v (algebraMap E (w.adicCompletion E) (IsCMField.complexConj E k)) =
      w.valuation E (IsCMField.complexConj E k) := w.valuedAdicCompletion_eq_valuation' _
  have h3 := hv (algebraMap E (w.adicCompletion E) k)
  rw [hs, h1, h2] at h3
  exact h3

theorem eq_of_under_eq {w u : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (hu : u.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) : u = w := by
  rcases (under_eq_iff_conjPl (IsCMField.complexConj E) (Algebra.IsQuadraticExtension.finrank_eq_two _ _)
    (IsCMField.complexConj_ne_one E) w u).1 hu with h | h
  · exact h
  · exact (existsUnique_conjPl _ w).unique h hw

theorem continuous_finGL : Continuous (finGL E n) :=
  Continuous.units_map _ (continuous_const.add (continuous_id.matrix_map
    (continuous_const.prodMk continuous_id : Continuous fun x : Af E => ((0, x) : InfiniteAdeleRing E × Af E))))

theorem continuous_cLoc (w : HeightOneSpectrum (𝓞 E)) : Continuous (cLoc (n := n) w) :=
  (Continuous.units_map _ (continuous_id.matrix_map
    ((RestrictedProduct.continuous_eval w).comp continuous_snd))).comp continuous_subtype_val

theorem mat_ext {A B : Matrix (Fin n) (Fin n) (Ad E)} (h1 : A.map (pInf E) = B.map (pInf E))
    (h2 : ∀ v, A.map ((pLoc E v).comp (pFin E)) = B.map ((pLoc E v).comp (pFin E))) : A = B := by
  ext i j
  refine ad_ext (congrFun (congrFun h1 i) j) (FiniteAdeleRing.ext _ fun v => ?_)
  exact congrFun (congrFun (h2 v) i) j

theorem map_finGL (v : HeightOneSpectrum (𝓞 E)) (k : GL (Fin n) (Af E)) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n k) = GeneralLinearGroup.map (pLoc E v) k :=
  Units.ext (congrArg (fun g : GL (Fin n) (v.adicCompletion E) => (g : Matrix (Fin n) (Fin n) (v.adicCompletion E)))
    (congrArg (GeneralLinearGroup.map (pLoc E v)) (pFin_finGL k)))

theorem pInf_conjAd (x : Ad E) : pInf E (conjAd E x) = star (pInf E x) :=
  (infEq E).symm_apply_apply _

theorem finGL_mem (w : HeightOneSpectrum (𝓞 E)) (s : w.adicCompletion E →+* w.adicCompletion E)
    (hs : ∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x))
    (hv : ∀ x, Valued.v (s x) = Valued.v x) (g : GL (Fin n) (w.adicCompletion E))
    (hg : g ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E))) :
    finGL E n (locGL E n w g) ∈ UA E n := by
  have hg' : cT s g.val * g.val = 1 := by
    have h : cT s g.val * 1 * g.val = 1 := hg
    rwa [Matrix.mul_one] at h
  have hw := conjPl_self w s hs hv
  change cT (conjAd E) (finGL E n (locGL E n w g)).val * 1 * (finGL E n (locGL E n w g)).val = 1
  rw [Matrix.mul_one]
  generalize hh : finGL E n (locGL E n w g) = h
  have hI : h.val.map (pInf E) = 1 := by
    rw [← hh]
    exact congrArg Units.val (pInf_finGL (locGL E n w g))
  have hL : ∀ v, h.val.map ((pLoc E v).comp (pFin E)) =
      (GeneralLinearGroup.map (pLoc E v) (locGL E n w g)).val := fun v => by
    rw [← hh]
    exact congrArg Units.val (map_finGL v (locGL E n w g))
  refine mat_ext ?_ fun v => ?_
  · have hc : (cT (conjAd E) h.val).map (pInf E) = 1 := by
      refine Matrix.ext fun i j => ?_
      have h1 : pInf E (h.val j i) = (1 : Matrix (Fin n) (Fin n) (Cinf E)) j i := congrFun (congrFun hI j) i
      change pInf E (conjAd E (h.val j i)) = _
      rw [pInf_conjAd, h1]
      by_cases e : i = j
      · subst e; simp
      · simp [Matrix.one_apply, e, Ne.symm e]
    rw [Matrix.map_mul, hc, hI, Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]
  · rcases eq_or_ne v w with rfl | hvw
    · have h0 := hL v
      rw [pLoc_locGL] at h0
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = cT s g.val := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E v (pFin E (h.val j i)) = g.val j i := congrFun (congrFun h0 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = s (g.val j i)
        rw [pLoc_conjFin_eq _ v s hs hv, h1]
      rw [Matrix.map_mul, hc, h0, hg', Matrix.map_one _ (map_zero _) (map_one _)]
    · have h0 := hL v
      rw [pLoc_locGL_of_ne hvw] at h0
      have hne : conjSrc (IsCMField.complexConj E).toRingEquiv v ≠ w := fun e =>
        hvw ((existsUnique_conjPl _ w).unique (e ▸ conjPl_conjSrc _ v) hw)
      have h2 := hL (conjSrc (IsCMField.complexConj E).toRingEquiv v)
      rw [pLoc_locGL_of_ne hne] at h2
      have hc : (cT (conjAd E) h.val).map ((pLoc E v).comp (pFin E)) = 1 := by
        refine Matrix.ext fun i j => ?_
        have h1 : pLoc E (conjSrc (IsCMField.complexConj E).toRingEquiv v) (pFin E (h.val j i)) =
            (1 : Matrix (Fin n) (Fin n) _) j i := congrFun (congrFun h2 j) i
        change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (pFin E (h.val j i))) = _
        rw [pLoc_conjFin, h1]
        by_cases e : i = j
        · subst e; simp
        · simp [Matrix.one_apply, e, Ne.symm e]
      have h0' : h.val.map ((pLoc E v).comp (pFin E)) = 1 := h0
      rw [Matrix.map_mul, hc, h0', Matrix.mul_one, Matrix.map_one _ (map_zero _) (map_one _)]

theorem finGL_mem_locU {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (g : GL (Fin n) (w.adicCompletion E)) (hU : finGL E n (locGL E n w g) ∈ UA E n) :
    (⟨_, hU⟩ : UA E n) ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨pInf_finGL _, ?_⟩
  simp only [Subgroup.mem_iInf]
  intro u hu
  have hne : u ≠ w := fun e => hu (by rw [e])
  exact (map_finGL u _).trans (pLoc_locGL_of_ne hne g)

theorem finGL_cLoc {w : HeightOneSpectrum (𝓞 E)} (hw : ConjPl (IsCMField.complexConj E).toRingEquiv w w)
    (x : locU n w) : finGL E n (locGL E n w (cLoc w (x : UA E n))) = (x : UA E n).1 := by
  have hx := Subgroup.mem_inf.1 x.2
  have hx2 := hx.2
  simp only [Subgroup.mem_iInf] at hx2
  refine Units.ext (mat_ext ?_ fun v => ?_)
  · have h1 : GeneralLinearGroup.map (pInf E) (x : UA E n).1 = 1 := hx.1
    have h2 := pInf_finGL (locGL E n w (cLoc w (x : UA E n)))
    exact congrArg Units.val (h2.trans h1.symm)
  · have h1 : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (finGL E n (locGL E n w (cLoc w (x : UA E n)))) =
        GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (x : UA E n).1 := by
      refine (map_finGL v _).trans ?_
      rcases eq_or_ne v w with rfl | hvw
      · exact pLoc_locGL v _
      · rw [pLoc_locGL_of_ne hvw]
        have := hx2 v fun e => hvw (eq_of_under_eq hw e)
        exact (MonoidHom.mem_ker.1 this).symm
    exact congrArg Units.val h1

theorem locU_equiv : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E))
    (s : w.adicCompletion E →+* w.adicCompletion E),
    (∀ x : E, s (algebraMap E _ x) = algebraMap E _ (IsCMField.complexConj E x)) →
    (∀ x, Valued.v (s x) = Valued.v x) →
    ∃ e : locU n w ≃ₜ* UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)),
      ∀ x : locU n w, (e x : GL (Fin n) (w.adicCompletion E)) = cLoc w (x : UA E n) := by
  intro E _ _ _ n w s hs hv
  have hw := conjPl_self w s hs hv
  have hf : ∀ x : locU n w, cLoc w (x : UA E n) ∈ UJ s (1 : Matrix (Fin n) (Fin n) (w.adicCompletion E)) := fun x => by
    change cT s _ * 1 * _ = 1
    rw [Matrix.mul_one]
    exact cT_cLoc w s hs hv _
  refine ⟨{ toFun := fun x => ⟨cLoc w (x : UA E n), hf x⟩
            invFun := fun g => ⟨⟨finGL E n (locGL E n w g.1), finGL_mem w s hs hv g.1 g.2⟩,
              finGL_mem_locU hw g.1 _⟩
            left_inv := fun x => Subtype.ext (Subtype.ext (finGL_cLoc hw x))
            right_inv := fun g => Subtype.ext ?_
            map_mul' := fun x y => Subtype.ext (map_mul (cLoc w) (x : UA E n) y)
            continuous_toFun := Continuous.subtype_mk ((continuous_cLoc w).comp continuous_subtype_val) _
            continuous_invFun := Continuous.subtype_mk (Continuous.subtype_mk
              (continuous_finGL.comp ((CuspSub.continuous_locGL w).comp continuous_subtype_val)) _) _ }, fun _ => rfl⟩
  exact (map_finGL w _).trans (pLoc_locGL w _)

end GlobalTheory.DefU.Inert

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevOKAll
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.LevelOK

theorem levOK_all : ∀ D : D7, LevOK D := by
  intro D V β L
  obtain ⟨hO, hC, hS, U, hU, hk⟩ := GlobalTheory.Mem.LevelSmooth.level_open_compact_smooth D V β L
  refine ⟨⟨hC, ?_⟩, U, hU, fun k hkU hkG => ?_⟩
  · have : (((Lev.levA V (lev D.sp.cm (HSpace.gram V) β L)).subgroupOf (GfC V)) : Set (GfC V)) =
        Subtype.val ⁻¹' ((Subgroup.comap (Lev.finE V) (lev D.sp.cm (HSpace.gram V) β L)) : Set (GA D V)) := by
      ext x; simp [Subgroup.mem_subgroupOf, Lev.levA, x.2]
    rw [this]; exact hO.preimage continuous_subtype_val
  · obtain ⟨h1, h2⟩ := hk k hkU hkG
    exact ⟨h1, h2⟩
end GlobalTheory.Mem.LevelOK
end

