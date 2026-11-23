module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CuspidalFiniteness.TypePoly
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.WtMatFix
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsAdaptedOfSurjective
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0041
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0043
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0039
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.AlgModBotCompactCasimirOfTypes
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private noncomputable def slc {K : Type} [Field K] [NumberField K] {n : ℕ} (g : AdelicGLn.AdelicGL K n) :
    archSmooth K n →ₗ[ℂ] (archCompact K n → ℂ) where
  toFun φ k := φ.1 (g * infEmb K n k.1)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem slc_op {K : Type} [Field K] [NumberField K] {n : ℕ} (X : (isExpLieAlgebra K n).lieSubalgebra)
    (hX : ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X) ∈ archCompact K n) :
    (∃ D : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      D (slc g φ) = slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ)) ∧
    ∀ (V : Submodule ℂ (archCompact K n → ℂ)), FiniteDimensional ℂ V → (∀ f ∈ V, ∀ k', (fun k => f (k * k')) ∈ V) →
      ∀ g φ, slc g φ ∈ V → slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) ∈ V := by
  let γ : ℝ → archCompact K n := fun t =>
    ⟨(isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X), hX t⟩
  have F : ∀ (g : AdelicGLn.AdelicGL K n) (φ : archSmooth K n) (k : archCompact K n),
      HasDerivAt (fun t => slc g φ (k * γ t)) (slc g (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ) k) 0 := by
    intro g φ k
    have d := (isExpLieAlgebra K n).hasDerivAt_rightDeriv
      ((show IsArchSmooth φ.1 from φ.2) (g * infEmb K n k.1)) ((isExpLieAlgebra K n).ofLie X) 1
    show HasDerivAt _ ((uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 (g * infEmb K n k.1)) 0
    rw [uAction_ι_apply]
    have e : (fun t => slc g φ (k * γ t)) = fun t => archSlice φ.1 (g * infEmb K n k.1)
        (1 * (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie X)) := by
      funext t
      simp only [slc, LinearMap.coe_mk, AddHom.coe_mk, archSlice_apply, one_mul, Subgroup.coe_mul, map_mul,
        mul_assoc]
      rfl
    rw [e]
    exact d
  let P : Submodule ℂ (archCompact K n → ℂ) :=
    { carrier := {f | ∀ k, DifferentiableAt ℝ (fun t => f (k * γ t)) 0}
      add_mem' := fun ha hb k => (ha k).add (hb k)
      zero_mem' := fun _ => differentiableAt_const _
      smul_mem' := fun c _ hf k => (hf k).const_smul c }
  let D₀ : P →ₗ[ℂ] (archCompact K n → ℂ) :=
    { toFun := fun f k => deriv (fun t => f.1 (k * γ t)) 0
      map_add' := fun f h => by
        funext k
        show deriv (fun t => f.1 (k * γ t) + h.1 (k * γ t)) 0 = _
        exact deriv_add (f.2 k) (h.2 k)
      map_smul' := fun c f => by
        funext k
        show deriv (fun t => c • f.1 (k * γ t)) 0 = _
        exact deriv_const_smul c (f.2 k) }
  obtain ⟨D, hD⟩ := LinearMap.exists_extend D₀
  refine ⟨⟨D, fun g φ => ?_⟩, fun V hV hVs g φ hφ => ?_⟩
  · have hm : slc g φ ∈ P := fun k => (F g φ k).differentiableAt
    have h1 := congrArg (fun L => L ⟨slc g φ, hm⟩) hD
    simp only [LinearMap.comp_apply, Submodule.subtype_apply] at h1
    rw [h1]
    funext k
    exact (F g φ k).deriv
  · haveI := hV
    exact mem_of_hasDerivAt V (c := fun t k => slc g φ (k * γ t)) (fun t => hVs _ hφ (γ t)) (fun k => F g φ k)

theorem UpperTheory.algMod_bot_compact_casimir_of_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Types S → ∀ (ι : Type) [Fintype ι] (X : ι → (isExpLieAlgebra K n).lieSubalgebra) (c : ι → ℝ), (∀ i, c i = 0 ∨ ∀ t : ℝ, (isExpLieAlgebra K n).expG (t • (isExpLieAlgebra K n).ofLie (X i)) ∈ archCompact K n) → AlgMod S ⊥ (uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i)))) := by
  intro K _ _ n S hS ι _ X c hc
  obtain ⟨V, hV, hVs, hSV⟩ := hS
  have hi : ∀ i, ∃ Di : Module.End ℂ (archCompact K n → ℂ), ∀ g φ,
      c i • Di (Di (slc g φ)) = slc g (c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ)) := by
    intro i
    rcases hc i with h0 | hX
    · exact ⟨0, fun g φ => by simp [h0]⟩
    · obtain ⟨D, hD⟩ := (slc_op (X i) hX).1
      exact ⟨D, fun g φ => by rw [hD, hD, LinearMap.map_smul_of_tower]⟩
  choose Di hDi using hi
  have e1 : ∀ φ : archSmooth K n, uAction (∑ i, c i • (UniversalEnvelopingAlgebra.ι ℝ (X i) *
      UniversalEnvelopingAlgebra.ι ℝ (X i))) φ = ∑ i, c i • uAction (UniversalEnvelopingAlgebra.ι ℝ (X i))
        (uAction (UniversalEnvelopingAlgebra.ι ℝ (X i)) φ) := by
    intro φ
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [map_sum, map_smul, map_mul, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
  have hinter : ∀ g φ, (∑ i, c i • (Di i * Di i)) (slc g φ) = slc g (uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ) := by
    intro g φ
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply]
    exact Finset.sum_congr rfl fun i _ => hDi i g φ
  have hstab : ∀ φ ∈ (⨅ g, V.comap (slc g)), uAction (∑ i, c i •
      (UniversalEnvelopingAlgebra.ι ℝ (X i) * UniversalEnvelopingAlgebra.ι ℝ (X i))) φ ∈ (⨅ g, V.comap (slc g)) := by
    intro φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ ⊢
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e1, map_sum]
    refine V.sum_mem fun i _ => ?_
    rw [LinearMap.map_smul_of_tower]
    rcases hc i with h0 | hX
    · rw [h0, zero_smul]
      exact V.zero_mem
    · exact V.smul_of_tower_mem _ ((slc_op (X i) hX).2 V hV hVs g _ ((slc_op (X i) hX).2 V hV hVs g φ (hφ g)))
  have hinV : ∀ g, ∀ φ ∈ (⨅ g, V.comap (slc g)), slc g φ ∈ V := by
    intro g φ hφ
    simp only [Submodule.mem_iInf, Submodule.mem_comap] at hφ
    exact hφ g
  obtain ⟨q, hq, -, hq0⟩ := UpperTheory.V.Af.CuspFin.polySlices (archSmooth K n) (archCompact K n → ℂ)
    (AdelicGLn.AdelicGL K n) _ _ (fun g => slc g) hinter V hV _ hstab hinV
  refine ⟨q, hq, fun φ hφ => ?_⟩
  rw [Submodule.mem_bot]
  have hN : φ ∈ (⨅ g, V.comap (slc g)) := by
    simp only [Submodule.mem_iInf, Submodule.mem_comap]
    exact fun g => hSV φ hφ g
  apply Subtype.ext
  funext g
  have h1 := congrFun (hq0 g φ hN) 1
  simpa [slc] using h1
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CrystallineVectorBasisExpansion
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

section Coord

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {V : Type} [AddCommGroup V] [Module Qp V]
    (ρ : Representation Qp G V) {d : ℕ} (e : Basis (Fin d) Qp V)

private theorem coord_sum (c : Fin d → B) (i : Fin d) :
    (TensorProduct.lid Qp B) (LinearMap.rTensor B (e.coord i) (∑ j, e j ⊗ₜ[Qp] c j)) = c i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, LinearMap.rTensor_tmul, TensorProduct.lid_tmul, Basis.coord_apply, Basis.repr_self]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Finsupp.single_apply, hj]
  · simp

private theorem exists_coord (x : V ⊗[Qp] B) : ∃ c : Fin d → B, x = ∑ j, e j ⊗ₜ[Qp] c j := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, by simp⟩
  | tmul v b =>
    refine ⟨fun j => e.repr v j • b, ?_⟩
    conv_lhs => rw [← e.sum_repr v]
    rw [sum_tmul]
    exact Finset.sum_congr rfl fun j _ => smul_tmul _ _ _
  | add x y hx hy =>
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    exact ⟨a + b, by simp [tmul_add, Finset.sum_add_distrib]⟩

private theorem act_sum (c : Fin d → B) (g : G) :
    actVB PD ρ g (∑ j, e j ⊗ₜ[Qp] c j) = ∑ i, e i ⊗ₜ[Qp]
      ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B)).mulVec (fun j => PD.actB g (c j)) i := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum, Matrix.mulVec, dotProduct, tmul_sum, Matrix.map_apply, LinearMap.toMatrix_apply]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  change ρ g (e j) ⊗ₜ[Qp] PD.actB g (c j) = _
  conv_lhs => rw [← e.sum_repr (ρ g (e j))]
  rw [sum_tmul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [smul_tmul, Algebra.smul_def]

private theorem core (M M' : Matrix (Fin d) (Fin d) B) (hM : M * M' = 1)
    (hg : ∀ g, (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B) * M.map (PD.actB g) = M)
    (x : V ⊗[Qp] B) (hx : x ∈ Dcris PD ρ) :
    ∃ c : Fin d → K₀, x = ∑ i, e i ⊗ₜ[Qp] (M.mulVec (fun j => algebraMap K₀ B (c j)) i) := by
  obtain ⟨y, rfl⟩ := exists_coord e x
  simp only [Dcris, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply,
    sub_eq_zero] at hx
  have hM' : M' * M = 1 := mul_eq_one_comm.1 hM
  have hy : ∀ g, ((LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B)).mulVec (fun j => PD.actB g (y j)) = y := by
    intro g
    funext i
    have h := hx g
    rw [act_sum] at h
    rw [← coord_sum e y i, ← h, coord_sum]
  have h2 : ∀ g, M' * (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B) = M'.map (PD.actB g) := by
    intro g
    have h1 : M.map (PD.actB g) * M'.map (PD.actB g) = 1 := by
      rw [← Matrix.map_mul, hM, Matrix.map_one _ (map_zero _) (map_one _)]
    set R := (LinearMap.toMatrix e e (ρ g)).map (algebraMap Qp B) with hR
    have : R * (M.map (PD.actB g) * M'.map (PD.actB g)) = M * M'.map (PD.actB g) := by
      rw [← Matrix.mul_assoc, hg g]
    rw [h1, Matrix.mul_one] at this
    rw [this, ← Matrix.mul_assoc, hM', Matrix.one_mul]
  choose c hc using fun i => PD.invB (M'.mulVec y i) fun g => by
    conv_rhs => rw [← hy g, Matrix.mulVec_mulVec, h2 g]
    simp [Matrix.mulVec, dotProduct]
  refine ⟨c, ?_⟩
  have h3 : (fun j => algebraMap K₀ B (c j)) = M'.mulVec y := funext hc
  rw [h3, Matrix.mulVec_mulVec, hM, Matrix.one_mulVec]

end Coord

theorem UpperTheory.crystalline_vector_basis_expansion :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) {d : ℕ} (e : Basis (Fin d) ℚ_[l] V) (M M' : Matrix (Fin d) (Fin d) (Bcr l)), M * M' = 1 → (∀ g : ↥(GK K), (LinearMap.toMatrix e e (ρ g)).map (algebraMap ℚ_[l] (Bcr l)) * M.map ((PP l).actQ (g : GQ l)) = M) → ∀ x ∈ Dcris ((PP l).PD K) ρ, ∃ c : Fin d → ↥(K0 K), x = ∑ i, e i ⊗ₜ[ℚ_[l]] (M.mulVec (fun j => algebraMap ↥(K0 K) (Bcr l) (c j)) i) := by
  intro l _ K V _ _ _ ρ d e M M' hM hg x hx
  refine core ((PP l).PD K) ρ e M M' hM (fun g => ?_) x hx
  have h5 : M.map (((PP l).PD K).actB g) = M.map ((PP l).actQ (g : GQ l)) := by
    ext i j
    exact (PP l).PD_actB K g _
  rw [h5, hg]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsCrystallineUnitFrobeniusEigen
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

theorem UpperTheory.exists_crystalline_unit_frobenius_eigen :
    ∀ (l : ℕ) [Fact l.Prime] (a : ℤ), ∃ u : (Bcr l)ˣ, (PP l).ιB (u : Bcr l) ∈ ((PP l).PD (botExt l)).Fil a ∧ (PP l).φB (u : Bcr l) = algebraMap ℚ_[l] (Bcr l) ((l : ℚ_[l]) ^ a) * (u : Bcr l) := by
  intro l _ a
  obtain ⟨T⟩ := tiedP l
  obtain ⟨t, ht⟩ := ((PP l).PD (botExt l)).t_unit
  have hl : (l : ℚ_[l]) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  refine ⟨t ^ a, ?_, ?_⟩
  · have h := GlobalTheory.DRFil.tdR_zpow_mem T (botExt l) a
    have e : GlobalTheory.IndefiniteRowSideFullHecke.DualExactSequence.tdR (PP l) (botExt l) =
        Units.map ((PP l).ιB : Bcr l →* (PP l).R.BdR) t := by
      ext
      change ((PP l).PD (botExt l)).ι ((PP l).PD (botExt l)).t = (PP l).ιB (t : Bcr l)
      rw [(PP l).PD_ι, ht]
    rw [e, ← map_zpow] at h
    exact h
  · have h1 : (PP l).φB (t : Bcr l) = algebraMap ℚ_[l] (Bcr l) (l : ℚ_[l]) * (t : Bcr l) := by
      have := ((PP l).PD (botExt l)).t_φ
      rw [(PP l).PD_φ, (PP l).PD_p, Algebra.smul_def, ← ht] at this
      exact this
    have e : Units.map ((PP l).φB : Bcr l →* Bcr l) t =
        Units.map (algebraMap ℚ_[l] (Bcr l) : ℚ_[l] →* Bcr l) (Units.mk0 _ hl) * t := Units.ext h1
    have e2 := congrArg (fun x : (Bcr l)ˣ => ((x ^ a : (Bcr l)ˣ) : Bcr l)) e
    simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map, Units.val_zpow_eq_zpow_val, Units.val_mk0] at e2
    exact e2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.FrobeniusIterateMatrixForm
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Polynomial

theorem UpperTheory.frobenius_iterate_matrix_form :
    ∀ {l : ℕ} [Fact l.Prime] (K : FinExt l) {d : ℕ} (M : Matrix (Fin d) (Fin d) (Bcr l)) (A : Matrix (Fin d) (Fin d) ↥(K0 K)), IsUnit A.det → M.map (PP l).φB = M * A.map (algebraMap ↥(K0 K) (Bcr l)) → ∀ k : ℕ, ∃ F : Matrix (Fin d) (Fin d) ↥(K0 K), IsUnit F.det ∧ M.map (((PP l).φB)^[k]) = M * F.map (algebraMap ↥(K0 K) (Bcr l)) := by
  intro l _ K d M A hA h k
  have hphi : ∀ c : ↥(K0 K), (PP l).φB (algebraMap ↥(K0 K) (Bcr l) c) =
      algebraMap ↥(K0 K) (Bcr l) (((PP l).PD K).σ c) := fun c => by
    rw [← (PP l).PD_φ K, ((PP l).PD K).φ_K₀]
  induction k with
  | zero => exact ⟨1, by simp, by simp⟩
  | succ k ih =>
    obtain ⟨F, hF, e⟩ := ih
    refine ⟨A * F.map ((PP l).PD K).σ, ?_, ?_⟩
    · rw [Matrix.det_mul]
      refine hA.mul ?_
      have := hF.map (((PP l).PD K).σ : ↥(K0 K) →+* ↥(K0 K))
      rw [RingHom.map_det] at this
      exact this
    · rw [Function.iterate_succ', ← Matrix.map_map, e, Matrix.map_mul, h, Matrix.map_mul, Matrix.mul_assoc]
      congr 2
      ext i j
      exact hphi _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneFunctorExactness
section
open Module

private theorem finrank_add_of_exact {k A B C : Type} [Field k] [AddCommGroup A] [Module k A] [AddCommGroup B]
    [Module k B] [AddCommGroup C] [Module k C] [FiniteDimensional k A] [FiniteDimensional k B] (f : A →ₗ[k] B)
    (p : B →ₗ[k] C) (hp : Function.Surjective p) (hex : Function.Exact f p) :
    finrank k (LinearMap.ker f) + finrank k B = finrank k A + finrank k C := by
  have h1 := LinearMap.finrank_range_add_finrank_ker f
  have h2 := LinearMap.finrank_range_add_finrank_ker p
  rw [LinearMap.range_eq_top.mpr hp, finrank_top, LinearMap.exact_iff.mp hex] at h2
  omega

open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.Pst.DpstMap in
theorem UpperTheory.weil_deligne_functor_exactness :
    UpperTheory.V.Af.Wd.WdExact := by
  intro l _ ι K L V' V V'' _ _ _ _ _ _ _ _ _ _ _ _ _ ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨hV', hV'', hds⟩ := UpperTheory.dpst_right_exact l K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hps hex hV
  obtain ⟨-, hde⟩ := UpperTheory.weilDeligne_dpst_leftExact l (UpperTheory.V.Loc.PP l) K L V' V V'' ρ' ρ ρ'' f p hf hp hfi hex
  haveI : FiniteDimensional ↥L.1 V' := FiniteDimensional.of_injective f hfi
  haveI : FiniteDimensional ↥L.1 V'' := Module.Finite.of_surjective p hps
  have key : Function.Exact (wdLin (UpperTheory.V.Loc.PP l) ι hf) (wdLin (UpperTheory.V.Loc.PP l) ι hp) ∧
      Function.Surjective (wdLin (UpperTheory.V.Loc.PP l) ι hp) :=
    letI := algC ι L
    UpperTheory.weilDeligne_functor_exact _ _ _ _ _ ℂ (mulD (UpperTheory.V.Loc.PP l) ρ') (mulD (UpperTheory.V.Loc.PP l) ρ) (mulD (UpperTheory.V.Loc.PP l) ρ'') (urC ι)
      (dmap (UpperTheory.V.Loc.PP l) hf) (dmap (UpperTheory.V.Loc.PP l) hp) _ _ hde hds
  refine ⟨hV', hV'', ?_, key.2, key.1⟩
  haveI := hV.finite
  haveI := hV'.finite
  have h1 := finrank_add_of_exact _ _ key.2 key.1
  have h2 := finrank_add_of_exact f p hps hex
  rw [LetterDim.finrank_wdSpace l _ ι K L V ρ hV, LetterDim.finrank_wdSpace l _ ι K L V' ρ' hV',
    LetterDim.finrank_wdSpace l _ ι K L V'' ρ'' hV''] at h1
  rw [LinearMap.ker_eq_bot.mpr hfi, finrank_bot] at h2
  rw [← LinearMap.ker_eq_bot, ← Submodule.finrank_eq_zero]
  omega
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.WeilDeligneUnramifiedPeriod
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Module TensorProduct GlobalTheory.Pst Polynomial

private theorem key {Q V B B' : Type} [Field Q] [AddCommGroup V] [Module Q V] [CommRing B] [Algebra Q B]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (T : V →ₗ[Q] V) (c : B →ₗ[Q] B')
    (w w' : Fin n → B) (h : ∀ i, ∑ j, algebraMap Q B (e.repr (T (e j)) i) * w' j = w i) :
    ∑ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (w i) := by
  have h1 : ∀ j, T (e j) ⊗ₜ[Q] c (w' j) = ∑ i, e i ⊗ₜ[Q] c (algebraMap Q B (e.repr (T (e j)) i) * w' j) := by
    intro j
    conv_lhs => rw [← e.sum_repr (T (e j))]
    rw [sum_tmul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_tmul, ← Algebra.smul_def, map_smul]
  simp only [h1]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← tmul_sum, ← map_sum, h]

private theorem eq_zero {Q V B' : Type} [Field Q] [AddCommGroup V] [Module Q V]
    [AddCommGroup B'] [Module Q B'] {n : ℕ} (e : Basis (Fin n) Q V) (w : Fin n → B')
    (h : ∑ i, e i ⊗ₜ[Q] w i = 0) (k : Fin n) : w k = 0 := by
  have := congrArg (fun x => TensorProduct.lid Q B' (LinearMap.rTensor B' (e.coord k) x)) h
  set_option synthInstance.maxHeartbeats 100000 in
    simpa [map_sum, Finsupp.single_apply, ite_smul] using this

private theorem phiV_pow {l : ℕ} [Fact l.Prime] (P : LocPrime l)
    (LL : Type) [Field LL] [Algebra ℚ_[l] LL] (k : ℕ) (v : LL) (b : P.R.B) :
    (phiV P LL LL ^ k) (v ⊗ₜ C b) = v ⊗ₜ C ((P.φB ^ k) b) := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_succ', Module.End.mul_apply, ih, phiV_tmul, phiSt_C, AlgHom.mul_apply]

theorem UpperTheory.weilDeligne_unramified_period :
    UpperTheory.V.Af.Wd.UnrPer := by
  intro l _ K L η hη hI
  haveI := GlobalTheory.UnramifiedCrys.compactSpace_GK K
  haveI : FiniteDimensional ℚ_[l] ↥L.1 := L.2
  haveI : IsModuleTopology ℚ_[l] ↥L.1 := isModuleTopologyOfFiniteDimensional
  have hη' : Continuous fun g => (η g : ↥L.1) := continuous_induced_rng.2 hη
  obtain ⟨n, e, M, hMc, hM⟩ := UpperTheory.galois_representation_integral_lattice l ↥(GK K) ↥L.1 (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η))
    (fun x => hη'.mul continuous_const)
  obtain ⟨W, hW, hWg, hWφ⟩ := UpperTheory.crystalline_frobenius_algebraic_elements l K n M hMc (fun g hg => by
    rw [← map_one M]
    ext i j
    rw [hM, hM, map_one]
    congr 2
    change (η g : ↥L.1) * e j = e j
    rw [hI g hg, Units.val_one, one_mul])
  haveI := nontrivial_B (V.Loc.PP l)
  haveI : Nonempty (Fin n) := e.index_nonempty
  let j₀ : Fin n := Classical.arbitrary _
  let c : V.Loc.Bcr l →ₗ[ℚ_[l]] Bst (V.Loc.PP l) := (CAlgHom : V.Loc.Bcr l →ₐ[ℚ_[l]] Bst (V.Loc.PP l)).toLinearMap
  have hk : ∀ (g : ↥(GK K)) (f : V.Loc.Bcr l → V.Loc.Bcr l),
      (M g).map (fun z => algebraMap ℚ_[l] (V.Loc.Bcr l) (z : ℚ_[l])) * W.map f = W →
      ∑ j, ((η g : ↥L.1) * e j) ⊗ₜ[ℚ_[l]] (C (f (W j j₀)) : Bst (V.Loc.PP l)) = ∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀) := by
    intro g f h
    refine key e (V.Loc.resCoef ℚ_[l] (V.Loc.chRep η) g) c (fun i => W i j₀) (fun i => f (W i j₀)) fun i => ?_
    have := congrFun (congrFun h i) j₀
    simpa only [Matrix.mul_apply, Matrix.map_apply, hM] using this
  refine ⟨∑ i, e i ⊗ₜ[ℚ_[l]] C (W i j₀), fun h0 => ?_, fun g => ?_, fun g k hg => ?_⟩
  · refine hW.ne_zero (Matrix.det_eq_zero_of_column_eq_zero j₀ fun i => ?_)
    exact C_eq_zero.1 (eq_zero e (fun i => (C (W i j₀) : Bst (V.Loc.PP l))) h0 i)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum]
      simp only [stRep_tmul, actSt_C]
      exact hk g _ (hWg g)
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.smul_sum]
      simp only [phiV_pow, smul_tmul']
      exact hk g _ (hWφ g k hg)
end

