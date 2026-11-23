module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1789
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0923
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1419
public import Development.AutomorphicArithmetic.LocalEmbeddings.Bundle0001
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0008
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0007
public import Development.AutomorphicArithmetic.DivisorFrames.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearActionDualWeylTensor
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsInvariantPosDefHermitianFormAutFormUnitary
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR GlobalTheory.UnitaryBC GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative
attribute [local instance] Formalism.BasicNotions.Host.cmStar

open MeasureTheory in
theorem UpperTheory.exists_invariant_posDef_hermitian_form_autForm_unitary :
    ∀ (D : D7) [IsCMField D.host.E] (V : HSp D), V.SigOK → V.IsPosDef → ∀ (j : UA D.host.E V.rank ≃ₜ* GA D V),
        (∀ x, x ∈ ratU D.host.E V.rank ↔ j x ∈ GQ V) →
        ∃ B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ, (∀ φ, IsAutFormU φ → φ ≠ 0 → 0 < (B φ φ).re) ∧
          ∀ k ∈ finU (E := D.host.E) (n := V.rank), ∀ φ ψ, IsAutFormU φ → IsAutFormU ψ →
            B (RU D.host.E V.rank k φ) (RU D.host.E V.rank k ψ) = B φ ψ := by
  intro D _ V hs hp j hj
  classical
  obtain ⟨h1, h2, h3, h4, h5, _h6, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  obtain ⟨μ, hμ⟩ : ∃ μ : Measure (GA D V), μ.IsHaarMeasure := ⟨Measure.haar, inferInstance⟩
  obtain ⟨hR, 𝓕, h𝓕⟩ := GlobalTheory.Mem.AdelicGroupFund.rightInvariant_and_exists_fundamentalDomain D V μ hμ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact V (fun τ => GlobalTheory.RepsObj.gramAt_posDef hp hs τ)

  let N : Submodule ℂ (UA D.host.E V.rank → ℂ) :=
    { carrier := {φ | Continuous φ ∧ ∀ γ ∈ ratU D.host.E V.rank, ∀ g, φ (γ * g) = φ g}
      add_mem' := fun {a b} ha hb => ⟨ha.1.add hb.1, fun γ hγ g => by simp [ha.2 γ hγ g, hb.2 γ hγ g]⟩
      zero_mem' := ⟨continuous_const, fun _ _ _ => rfl⟩
      smul_mem' := fun c a ha => ⟨ha.1.const_smul c, fun γ hγ g => by simp [ha.2 γ hγ g]⟩ }
  have hAN : ∀ φ, IsAutFormU φ → φ ∈ N := fun φ h => ⟨h.cont, h.left⟩
  have hRN : ∀ k, ∀ φ ∈ N, RU D.host.E V.rank k φ ∈ N := by
    intro k φ h
    refine ⟨h.1.comp (continuous_mul_const k), fun γ hγ g => ?_⟩
    show φ (γ * g * k) = φ (g * k)
    rw [mul_assoc, h.2 γ hγ]
  have hLC : ∀ x ∈ N, Continuous (fun g => x (j.symm g)) ∧
      ∀ γ ∈ GQ V, ∀ g, x (j.symm (γ * g)) = x (j.symm g) := by
    intro x hx
    refine ⟨hx.1.comp j.symm.continuous, fun γ hγ g => ?_⟩
    rw [map_mul]
    exact hx.2 _ ((hj _).2 (by rwa [j.apply_symm_apply])) _
  have hI : ∀ x ∈ N, ∀ y ∈ N, IntegrableOn (fun g => star (x (j.symm g)) * y (j.symm g)) 𝓕 μ := by
    intro x hx y hy
    exact GlobalTheory.MultPetersson.integrableOn_star_mul μ 𝓕 C hμ h𝓕 hC hcov (hLC x hx).1 (hLC y hy).1 (hLC x hx).2
      (hLC y hy).2
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl N
  let P : (UA D.host.E V.rank → ℂ) →ₗ[ℂ] N := Submodule.projectionOnto N q hq
  have hPN : ∀ T, ((P T : N) : UA D.host.E V.rank → ℂ) ∈ N := fun T => (P T).2
  have hPid : ∀ T ∈ N, ((P T : N) : UA D.host.E V.rank → ℂ) = T := fun T hT =>
    congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨T, hT⟩)
  let F : (UA D.host.E V.rank → ℂ) → (UA D.host.E V.rank → ℂ) → ℂ := fun x y =>
    ∫ g in 𝓕, star ((P x).1 (j.symm g)) * (P y).1 (j.symm g) ∂μ
  let B : (UA D.host.E V.rank → ℂ) →ₗ⋆[ℂ] (UA D.host.E V.rank → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) F
    (fun x x' y => by
      simp only [F, map_add (f := _), Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x') _ (hPN y))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, RingHom.id_apply, starRingEnd_apply]
      ring)
    (fun x y y' => by
      simp only [F, map_add (f := _), Submodule.coe_add]
      rw [← integral_add (hI _ (hPN x) _ (hPN y)) (hI _ (hPN x) _ (hPN y'))]
      congr 1
      funext g
      simp only [Pi.add_apply, star_add, add_mul, mul_add])
    (fun c x y => by
      simp only [F, map_smul, Submodule.coe_smul]
      rw [smul_eq_mul, ← integral_const_mul]
      congr 1
      funext g
      simp only [Pi.smul_apply, smul_eq_mul, star_mul, RingHom.id_apply, starRingEnd_apply]
      ring)
  have hB : ∀ x ∈ N, ∀ y ∈ N, B x y = ∫ g in 𝓕, star (x (j.symm g)) * y (j.symm g) ∂μ := by
    intro x hx y hy
    show F x y = _
    simp only [F, hPid x hx, hPid y hy]
  refine ⟨B, ?_, ?_⟩
  · intro T hT' h0
    have hT := hAN T hT'
    rw [hB _ hT _ hT]
    have hre : ∫ g in 𝓕, star (T (j.symm g)) * T (j.symm g) ∂μ = ((∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ : ℝ) : ℂ) := by
      rw [← integral_complex_ofReal]
      congr 1
      funext g
      rw [Complex.star_def, Complex.conj_mul']
      push_cast
      rfl
    rw [hre, Complex.ofReal_re]
    have hnn : 0 ≤ ∫ g in 𝓕, ‖T (j.symm g)‖ ^ 2 ∂μ := integral_nonneg fun g => by positivity
    refine lt_of_le_of_ne hnn fun hz => h0 ?_
    have hi : IntegrableOn (fun g => ‖T (j.symm g)‖ ^ 2) 𝓕 μ := by
      have := (hI T hT T hT).norm
      have e2 : (fun g => ‖star (T (j.symm g)) * T (j.symm g)‖) = fun g => ‖T (j.symm g)‖ ^ 2 := by
        funext g
        rw [norm_mul, norm_star, sq]
      rw [e2] at this
      exact this
    have hae := (integral_eq_zero_iff_of_nonneg (fun g => by positivity) hi).1 hz.symm
    have := GlobalTheory.SchurConst.eq_zero_of_ae μ 𝓕 hμ h𝓕 (fun g => T (j.symm g)) (hLC T hT).1 (hLC T hT).2 (by
      filter_upwards [hae] with g hg
      simpa using hg)
    funext x
    have h := congrFun this (j x)
    simpa using h
  · intro k _hk T T' hT0 hT0'
    have hT := hAN T hT0
    have hT' := hAN T' hT0'
    rw [hB _ (hRN k T hT) _ (hRN k T' hT'), hB _ hT _ hT']
    haveI := h5
    haveI := h4
    haveI := h2
    haveI := h7
    haveI := hR
    have hmap : Measure.map (fun g => g * j k) μ = μ := map_mul_right_eq_self μ (j k)
    have hh : ∀ x : UA D.host.E V.rank → ℂ, ∀ g, RU D.host.E V.rank k x (j.symm g) = x (j.symm (g * j k)) := by
      intro x g
      rw [map_mul, j.symm_apply_apply]
      rfl
    simp only [hh]
    have hinv : ∀ γ ∈ GQ V, ∀ g, (fun g => star (T (j.symm g)) * T' (j.symm g)) (γ * g) =
        (fun g => star (T (j.symm g)) * T' (j.symm g)) g := by
      intro γ hγ g
      simp only [(hLC T hT).2 γ hγ, (hLC T' hT').2 γ hγ]
    exact (GlobalTheory.fundamentalDomain_setIntegral_mul_right (GQ V) μ 𝓕 h𝓕 (j k) hmap _ hinv (hI T hT T' hT')).2
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.ExistsThOEqOfIsLatVacThetaFun
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints GlobalTheory.Grid GlobalTheory.ChainFr GlobalTheory.SquareComm GlobalTheory.FinMatch
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Classical
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model piW chrW unifAt latAtV At SInf)
open GlobalTheory.TripleRead (thO ptO)
open GlobalTheory.AdelicU (evFin splitPrime)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem ptO_crd {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (hG : IsUnit G.det) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) :
    ptO G e (HMul.hMul (uᵀ.submatrix e.symm id) (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G)) = u := by
  have h1 : GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G * GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM G⁻¹ = (1 : Matrix (Fin m) (Fin m) (AE D)) := by
    unfold GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation.incM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM
    rw [← Matrix.map_mul, Matrix.mul_nonsing_inv _ hG, Matrix.map_one _ (map_zero _) (map_one _)]
  unfold GlobalTheory.TripleRead.ptO
  rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  ext i j
  simp

private theorem ptO_two {D : D7} {m k d : ℕ} (G : Matrix (Fin m) (Fin m) D.host.E) (e : Fin k ≃ Fin d)
    (x : Matrix (Fin d) (Fin m) (AE D)) : ptO G e (2 • x) = 2 • ptO G e x := by
  unfold GlobalTheory.TripleRead.ptO
  rw [two_nsmul, two_nsmul, Matrix.add_mul]
  rfl

private theorem isHalf_crd {D : D7} {m k d : ℕ} (H : Matrix (Fin m) (Fin m) (AE D)) (e : Fin k ≃ Fin d)
    (u : Matrix (Fin m) (Fin k) (AE D)) (a : AE D) (h : ∀ i j, a * u i j = u i j) :
    IsHalf a (HMul.hMul (uᵀ.submatrix e.symm id) H : Matrix (Fin d) (Fin m) (AE D)) := by
  intro i j
  rw [Matrix.mul_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [← mul_assoc]
  exact congrArg (· * H l j) (h l (e.symm i))

theorem UpperTheory.exists_thO_eq_of_isLatVac_thetaFun :
    ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (ε : Bool) (S X : HSp D) (d : ℕ) (e : Fin d ≃ Fin X.rank)
        (Bs : Base D.host.F D.host.E) (Vs : Spc D.host.F D.host.E S.rank) (Ws : Spc D.host.F D.host.E d)
        (M : Model D.sp.cm.sig Vs Ws), IsPair ψ ε S X e Bs Vs Ws M → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛX : Submodule (𝓞 D.host.E) (Fin X.rank → D.host.E)),
        IsLat e Vs Ws ΛS ΛX →
        ∀ f₀ : WO (sgn ε S) X → ℂ, IsThetaFunO ψ (sgn ε S) X f₀ → IsLatVac (heisO ψ (sgn ε S) X) (latO (sgn ε S) X (ΛS : Set (Fin S.rank → D.host.E)) (ΛX : Set (Fin X.rank → D.host.E)) fun _ => True) f₀ →
        ∃ g : SInf D.host.F (Fin S.rank × Fin d), f₀ = thO M ψ (sgn ε S).gram e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g M.vac) := by
  intro D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL f₀ hth hvac
  obtain ⟨-, hrho, -, -, hinj, hon⟩ := UpperTheory.thetaOperator_intertwines_heisenberg D ψ ε S X d e Bs Vs Ws M hP
  obtain ⟨hlat, -⟩ := UpperTheory.ptO_sgn_mem_latAtV_iff_mem_latO D ψ ε S X d e Bs Vs Ws M hP ΛS ΛX hL
  obtain ⟨Ψ, hΨ, rfl⟩ := (hon f₀).1 hth
  obtain ⟨r, s, hV⟩ := hP.herm
  obtain ⟨r', s', hW⟩ := hP.skew
  have hψ := hP.psi
  subst hψ
  have hG : IsUnit (show Matrix (Fin S.rank) (Fin S.rank) D.host.E from (sgn ε S).gram).det :=
    GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit (sgn ε S)
  have hfix : ∀ y : WO (sgn ε S) X, heisO Bs.ψ (sgn ε S) X y (thO M Bs.ψ (sgn ε S).gram e Ψ) = thO M Bs.ψ (sgn ε S).gram e Ψ →
      M.co.rho Bs.ψ (ptO (sgn ε S).gram e y) Ψ = Ψ := fun y hy =>
    hinj _ (GlobalTheory.HeisSchA.rho_mem_schA M Bs.ψ hP.base.std _ Ψ hΨ) _ hΨ ((hrho Ψ y).trans hy)
  obtain ⟨g, hg⟩ := UpperTheory.exists_eq_pure_vacuum_of_lattice_invariant D.host.F D.host.E D.sp.cm.sig Bs S.rank d Vs Ws M r s r' s' hP.base hV hW hP.good Ψ hΨ
    (fun v γ hγ => by
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have h2 := hfix _ (hvac.1 _ h1)
      have h3 := (ptO_two (D := D) _ e _).trans (congrArg (2 • ·) h0)
      exact h3 ▸ h2)
    (fun v t γ hγ ht => by
      obtain ⟨a, ha, haz⟩ := UpperTheory.exists_splitIdempotent_mul_eq_of_piW_eq_zero D v t
      have h0 := ptO_crd (D := D) _ hG e γ
      have h1 := hlat v _ (h0.symm ▸ hγ)
      have hat := (GlobalTheory.LatVac.latAtV_at_stable Vs Ws v).1 γ hγ
      have h2 := hfix _ (hvac.2 a ha _ h1 (isHalf_crd _ e γ a fun i j =>
        haz _ (fun u hu => congrFun (congrFun (hat u hu) i) j) (congrFun (congrFun ht i) j)))
      exact h0 ▸ h2)
  exact ⟨g, by rw [← hg]⟩
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.FiniteDimensionalNablaTAndContinuousWtOp
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

private theorem fd_dw (n : ℕ) (ν : Fin n → ℕ) : FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) := by
  obtain ⟨b, ⟨-, hb, -⟩, -⟩ := Formalism.GradedWeylDivisibility.sSBasis ℂ n n ν
  have : Finite (Formalism.GradedWeylDivisibility.ssIdx n n ν) := (Formalism.GradedWeylDivisibility.sSIdxFinite n n _).to_subtype
  rw [← hb]
  exact FiniteDimensional.span_of_finite ℂ (Set.finite_range b)

private theorem cont_rowAct (n : ℕ) (f : MvPolynomial (Fin n × Fin n) ℂ) :
    ∀ ℓ : MvPolynomial (Fin n × Fin n) ℂ →ₗ[ℂ] ℂ,
      Continuous fun g : Matrix (Fin n) (Fin n) ℂ => ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g f) := by
  induction f using MvPolynomial.induction_on with
  | C a =>
    intro ℓ
    simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.algHom_C]
    exact continuous_const
  | add p q hp hq =>
    intro ℓ
    simp only [map_add (f := _)]
    exact (hp ℓ).add (hq ℓ)
  | mul_X p v hp =>
    intro ℓ
    have e : ∀ g : Matrix (Fin n) (Fin n) ℂ, ℓ (Formalism.GradedWeylDivisibility.rowAct ℂ g (p * MvPolynomial.X v)) =
        ∑ b : Fin n, g v.1 b * (ℓ ∘ₗ LinearMap.mulRight ℂ (MvPolynomial.X (b, v.2))) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) := by
      intro g
      have h1 : Formalism.GradedWeylDivisibility.rowAct ℂ g (MvPolynomial.X v : MvPolynomial (Fin n × Fin n) ℂ) =
          ∑ b : Fin n, MvPolynomial.C (g v.1 b) * MvPolynomial.X (b, v.2) := by
        simp only [Formalism.GradedWeylDivisibility.rowAct, MvPolynomial.aeval_X]
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_mul, h1, Finset.mul_sum, map_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [mul_left_comm, ← MvPolynomial.smul_eq_C_mul, map_smul, smul_eq_mul]
      rfl
    simp only [e]
    refine continuous_finsetSum _ fun b _ => ?_
    exact (continuous_id.matrix_elem v.1 b).mul (hp _)

private theorem cont_rep (n : ℕ) (ν : Fin n → ℕ) (ℓ : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν →ₗ[ℂ] ℂ)
    (u : Formalism.GradedWeylDivisibility.dualWeyl ℂ n n ν) :
    Continuous fun g : GL (Fin n) ℂ => ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) := by
  obtain ⟨L, hL⟩ := LinearMap.exists_extend ℓ
  have e : ∀ g : GL (Fin n) ℂ, ℓ (Formalism.UG.dualWeylRep ℂ n n ν g u) =
      L (Formalism.GradedWeylDivisibility.rowAct ℂ ((g⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) (u : MvPolynomial (Fin n × Fin n) ℂ)) := by
    intro g
    rw [← hL, LinearMap.comp_apply, Submodule.subtype_apply, Formalism.UG.dualWeylRep_apply]
    rfl
  simp only [e]
  exact (cont_rowAct n _ L).comp Units.continuous_coe_inv

private theorem cont_multi {X ι : Type} [TopologicalSpace X] [Fintype ι] [DecidableEq ι] {V : ι → Type}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] [∀ i, FiniteDimensional ℂ (V i)]
    (m : (∀ i, V i) →ₘₗ[ℂ] ℂ) (F : ∀ i, X → V i) (hF : ∀ i (ℓ : V i →ₗ[ℂ] ℂ), Continuous fun x => ℓ (F i x)) :
    Continuous fun x => m fun i => F i x := by
  let b := fun i => Module.finBasis ℂ (V i)
  have e : ∀ x, (m fun i => F i x) = ∑ r : ∀ i, Fin (Module.finrank ℂ (V i)),
      (∏ i, (b i).coord (r i) (F i x)) • m fun i => b i (r i) := by
    intro x
    have h1 : (fun i => F i x) = fun i => ∑ j, (b i).coord j (F i x) • b i j := by
      funext i
      simp only [Module.Basis.coord_apply, Module.Basis.sum_repr]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [h1, MultilinearMap.map_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [MultilinearMap.map_smul_univ, RingHom.id_apply]
  simp only [e]
  refine continuous_finsetSum _ fun r _ => ?_
  exact (continuous_finsetProd _ fun i _ => hF i _).smul continuous_const

theorem UpperTheory.finiteDimensional_nablaT_and_continuous_wtOp :
    ∀ (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι] (mu : ι → ℕ → ℕ) (sh : ι → ℤ),
        FiniteDimensional ℂ (NablaT ℂ n mu) ∧ ∀ (ℓ : NablaT ℂ n mu →ₗ[ℂ] ℂ) (u : NablaT ℂ n mu),
          Continuous fun g : ι → GL (Fin n) ℂ => ℓ (wtOp ℂ n mu sh g u) := by
  intro n ι _ _ mu sh
  haveI : ∀ τ, FiniteDimensional ℂ (Formalism.GradedWeylDivisibility.dualWeyl ℂ n n (Formalism.CohomologicalDescent.LD.res n (mu τ))) := fun τ => fd_dw n _
  refine ⟨Module.Finite.of_basis (Basis.piTensorProduct fun τ => Module.finBasis ℂ _), fun ℓ u => ?_⟩
  have h1 : Continuous fun g : ι → GL (Fin n) ℂ => ℓ (GlobalTheory.ExpFrame.grp ℂ n mu g u) := by
    induction u using PiTensorProduct.induction_on with
    | smul_tprod c x =>
      simp only [map_smul, GlobalTheory.SemilinTransport.grp_tprod]
      refine Continuous.const_smul ?_ c
      exact cont_multi (ℓ.compMultilinearMap (PiTensorProduct.tprod ℂ))
        (fun τ (g : ι → GL (Fin n) ℂ) => Formalism.UG.dualWeylRep ℂ n n _ (g τ) (x τ))
        (fun τ l => (cont_rep n _ l (x τ)).comp (continuous_apply τ))
    | add a b ha hb =>
      simp only [map_add (f := _)]
      exact ha.add hb
  simp only [wtOp_apply, map_smul]
  have h2 : Continuous fun g : ι → GL (Fin n) ℂ =>
      (∏ τ, Matrix.GeneralLinearGroup.det (g τ) ^ (-sh τ) : ℂˣ) := by
    refine continuous_finsetProd _ fun τ _ => ?_
    refine Continuous.zpow ?_ _
    exact Matrix.GeneralLinearGroup.continuous_det.comp (continuous_apply τ)
  exact (Units.continuous_val.comp h2).smul h1
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.GoodPlaceOfTwistPlaceDividing
section
open NumberField IsDedekindDomain TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.L2.Pj GlobalTheory.BigTop GlobalTheory.BigOn
open Formalism.CohomologicalDescent.LogSmallConstantBounds (Par)
open Formalism.CohomologicalDescent.ShortWeightBounds (Wts)
open Formalism.CohomologicalDescent.DepthNonnegative (NablaT)
open GlobalTheory.ExpFrame GlobalTheory.ExpTie GlobalTheory.UnitaryBC GlobalTheory.CuspRep GlobalTheory.SmGL GlobalTheory.FrameAut
attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem UpperTheory.good_place_of_twist_place_dividing :
    ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
        {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} (p : PtAt ex Csz) (j : Fin D.R.m) (P : Par) (W : Wts D.what₂.Tau), Dict L j P W →
        ∀ w ∈ p.R.twPl, W.WRange P (Formalism.EigenvalueLevelCeiling.plc w) → ∀ v : HeightOneSpectrum (𝓞 D.host.E),
          ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) ∈ v.asIdeal → GlobalTheory.Hk3.Good p.R.toRealDat (p.R.mu w) v := by
  intro D L hT Gi Gl Kc Y cX ex Csz p j P W hD w hw hW v hv
  have hL := p.charW.base.lev
  have hl := Formalism.EigenvalueLevelCeiling.plc_prime w
  have key : ∀ q : ℕ, q.Prime → q ≠ Formalism.EigenvalueLevelCeiling.plc w → ((q : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
    intro q hq hne hqv
    have hc : IsCoprime ((q : ℕ) : 𝓞 D.host.E) ((Formalism.EigenvalueLevelCeiling.plc w : ℕ) : 𝓞 D.host.E) :=
      Nat.Coprime.cast ((Nat.coprime_primes hq hl).2 hne)
    obtain ⟨a, b, hab⟩ := hc
    exact v.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
      (hab ▸ v.asIdeal.add_mem (v.asIdeal.mul_mem_left a hqv) (v.asIdeal.mul_mem_left b hv)))
  have hsp : Formalism.EigenvalueLevelCeiling.plc w ∉ Formalism.MainNotions.JumpSetsAlt.excSet D := hD.special ▸ hW.2.2.2
  have hunr : (p.R.xiH (p.R.mu w)).UnrAt v := by
    obtain ⟨ψ, Q, hψ, e⟩ := p.charW.tup.mu_on w hw
    have e' : p.R.xiH (p.R.mu w) = p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w) * ψ := e
    have hd : (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).UnrAt v := by
      unfold Formalism.L2.Host.CharFrame.delAt
      split_ifs
      · refine p.R.C.isDel'.unr v (key _ D.host.pde'_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
      · refine p.R.C.isDel.unr v (key _ D.host.pde_prime fun h => hsp ?_)
        rw [← h]
        simp [Formalism.MainNotions.JumpSetsAlt.excSet]
    intro x hx
    have a1 := hd x hx
    have a2 := hψ.atl v hv x
    rw [e']
    change (p.R.C.delAt (Formalism.EigenvalueLevelCeiling.plc w)).loc v x * ψ.loc v x = 1
    rw [a1, a2, mul_one]
  intro PP hPP
  rcases hPP with hPP | hPP
  · obtain ⟨k, hk⟩ := (hL.Pg PP).1 hPP
    have hg : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have h1 := p.R.C.P.pb_over k
      have hk' : PP.under (𝓞 D.host.K) = p.R.C.P.pb k := hk
      rw [← hk'] at h1
      have h2 : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ PP.asIdeal := h1
      rwa [map_natCast] at h2
    have hn : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal := by
      refine key _ (D.host.g_prime k) fun h => ?_
      have h1 := hD.big k
      have h2 := hW.2.1
      rw [h] at h1
      exact absurd h1 (not_lt.2 h2)
    refine ⟨fun e => hn (e ▸ hg), fun hc => hn ?_⟩
    obtain ⟨c', h1, h2⟩ := hc _ hg
    have : c' = ((D.host.g k : ℕ) : 𝓞 D.host.E) := by
      apply RingOfIntegers.ext
      have e1 : (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) = ((D.host.g k : ℕ) : D.host.E) := map_natCast (algebraMap (𝓞 D.host.E) D.host.E) _
      have h3 : (c' : D.host.E) = star (((D.host.g k : ℕ) : 𝓞 D.host.E) : D.host.E) := h2
      rw [e1, star_natCast, ← e1] at h3
      exact h3
    exact this ▸ h1
  · exact ⟨fun e => (hL.Q_ram (p.R.mu w) v).2 (Or.inl (e ▸ hPP)) hunr,
      fun hc => (hL.Q_ram (p.R.mu w) v).2 (Or.inr ⟨PP, hPP, hc⟩) hunr⟩
end

-- bundled from Development.AutomorphicArithmetic.DivisorFrames.IsAutFormUOfVectorValuedInvariant
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.BasicNotions GlobalTheory.DefU GlobalTheory.FrameAut Formalism.CohomologicalDescent.DepthNonnegative

theorem UpperTheory.isAutFormU_of_vectorValued_invariant :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (M : Type) [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] (R : UA E n →* Module.End ℂ M),
        (∀ k ∈ finU (E := E) (n := n), R k = 1) → (∀ (ℓ : M →ₗ[ℂ] ℂ) (u : M), Continuous fun g => ℓ (R g u)) →
        ∀ F1 : UA E n → M, (∀ γ ∈ ratU E n, ∀ g, F1 (γ * g) = R γ (F1 g)) → (∀ x ∈ infU E n, ∀ g, F1 (g * x) = F1 g) →
        (∀ᶠ y in nhds (1 : UA E n), ∀ g, F1 (g * y) = F1 g) → ∀ ℓ : M →ₗ[ℂ] ℂ, IsAutFormU fun g => ℓ (R g⁻¹ (F1 g)) := by
  intro E _ _ _ n M _ _ _ R hfin hcont F1 hrat hinf hev ℓ
  have hRU : ∀ (x : UA E n) (φ : UA E n → ℂ) (g : UA E n), RU E n x φ g = φ (g * x) := fun _ _ _ => rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [continuous_iff_continuousAt]
    intro g₀
    have h1 : Continuous fun g : UA E n => ℓ (R g⁻¹ (F1 g₀)) := (hcont ℓ (F1 g₀)).comp continuous_inv
    refine h1.continuousAt.congr ?_
    have ht : Filter.Tendsto (fun g : UA E n => g₀⁻¹ * g) (nhds g₀) (nhds 1) := by
      have : Continuous fun g : UA E n => g₀⁻¹ * g := continuous_const.mul continuous_id
      have h2 := this.tendsto g₀
      rwa [inv_mul_cancel] at h2
    filter_upwards [ht.eventually hev] with g hg
    have := hg g₀
    rw [mul_inv_cancel_left] at this
    rw [this]
  · intro γ hγ g
    rw [hrat γ hγ g, ← Module.End.mul_apply, ← map_mul, mul_inv_rev, inv_mul_cancel_right]
  · set φ : UA E n → ℂ := fun g => ℓ (R g⁻¹ (F1 g)) with hφ
    let S : Subgroup (finU (E := E) (n := n)) :=
      { carrier := {k : finU (E := E) (n := n) | RU E n k φ = φ}
        one_mem' := by simp
        mul_mem' := by
          intro a b ha hb
          simp only [Set.mem_setOf_eq] at ha hb ⊢
          rw [Subgroup.coe_mul, map_mul, Module.End.mul_apply, hb, ha]
        inv_mem' := by
          intro a ha
          simp only [Set.mem_setOf_eq] at ha ⊢
          conv_lhs => rw [← ha]
          rw [← Module.End.mul_apply, ← map_mul]
          simp }
    refine S.isOpen_of_mem_nhds (g := 1) ?_
    have ht : Filter.Tendsto (fun k : finU (E := E) (n := n) => (k : UA E n)) (nhds 1) (nhds 1) :=
      continuous_subtype_val.tendsto (1 : finU (E := E) (n := n))
    filter_upwards [ht.eventually hev] with k hk
    show RU E n k φ = φ
    funext g
    rw [hRU]
    simp only [hφ]
    rw [hk g, mul_inv_rev, map_mul, hfin _ ((finU (E := E) (n := n)).inv_mem k.2), one_mul]
  · let L : (M →ₗ[ℂ] ℂ) →ₗ[ℂ] (UA E n → ℂ) :=
      { toFun := fun ℓ' g => ℓ' (R g⁻¹ (F1 g))
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    refine Submodule.finiteDimensional_of_le (S₂ := LinearMap.range L) ?_
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    refine ⟨ℓ ∘ₗ R (k : UA E n)⁻¹, ?_⟩
    funext g
    show ℓ (R (k : UA E n)⁻¹ (R g⁻¹ (F1 g))) = RU E n k _ g
    rw [hRU, hinf _ k.2 g, mul_inv_rev, map_mul, Module.End.mul_apply]
end

