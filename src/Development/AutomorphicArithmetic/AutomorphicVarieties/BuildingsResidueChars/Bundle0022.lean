module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FormsFiniteness.OrderedCechToCatCochainsOneApplyValueAtSubset
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0019
public import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SupercuspidalSupportUniqueGL
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwahoriProjSurjective
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsEquivDetCharacterOfIrreducibleRankLeOne
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0150
public import GroundTheory.AutomorphicForms.AutomorphicFormSpaces.GKStable
public import GroundTheory.AutomorphicForms.GKModules.KernelCalculus

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchExpSingleUnipotentEmbedding
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

open GroundTheory.Automorphic.CuspidalSpectrum in
private theorem archExp_single (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s)
    (x : mixedSpace K) :
    ∃ P : UPos (r + s) r → AdeleRing (𝓞 K) K,
      archExp (K := K) (n := r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) = unipGL P := by
  classical
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace K
  let P : UPos (r + s) r → AdeleRing (𝓞 K) K := fun p =>
    if p.1 = (Fin.castAdd s i, Fin.natAdd r j) then ((e.symm x, 0) : AdeleRing (𝓞 K) K) else 0
  refine ⟨P, ?_⟩
  have h0 : ∀ p, (P p).2 = 0 := by
    intro p
    by_cases hp : p.1 = (Fin.castAdd s i, Fin.natAdd r j)
    · simp [P, hp]
    · simp only [P, hp, if_false]
      rfl
  have hc := conj_unipGL_eq_archExp (1 : AdelicGLn.AdelicGL K (r + s)) P h0
  simp only [inv_one, one_mul, mul_one] at hc
  rw [hc]
  congr 1
  refine Matrix.ext fun a b => ?_
  simp [conjArch, archMat, archMatrixEquiv, Matrix.single_apply]
  show _ = e ((blockEntry P a b).1)
  rw [blockEntry_apply]
  by_cases hab : Fin.castAdd s i = a ∧ Fin.natAdd r j = b
  · obtain ⟨rfl, rfl⟩ := hab
    have hh : ((Fin.castAdd s i : Fin (r + s)) : ℕ) < r ∧ r ≤ ((Fin.natAdd r j : Fin (r + s)) : ℕ) :=
      ⟨by simp, by simp⟩
    rw [dite_eq_left hh, if_pos ⟨rfl, rfl⟩]
    simp only [P, if_pos rfl, Prod.fst]
    exact (e.apply_symm_apply x).symm
  · rw [if_neg hab]
    split_ifs with hh
    · have hne : ¬ ((a, b) : Fin (r + s) × Fin (r + s)) = (Fin.castAdd s i, Fin.natAdd r j) := by
        intro heq
        apply hab
        simp only [Prod.mk.injEq] at heq
        exact ⟨heq.1.symm, heq.2.symm⟩
      simp only [P, hne, if_false]
      exact (map_zero e).symm
    · exact (map_zero e).symm

open GroundTheory.Automorphic.CuspidalSpectrum in
theorem UpperTheory.archExp_single_unipotent_embedding :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (i : Fin r) (j : Fin s) (x : mixedSpace K), ∀ ψ ∈ NInv K (r + s) r, lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ ∈ Van K r s := by
  intro K _ _ r s i j x ψ hψ
  classical
  have hψ' : ∀ (X : UPos (r + s) r → AdeleRing (𝓞 K) K) (g : AdelicGLn.AdelicGL K (r + s)),
      ψ.1 (unipGL X * g) = ψ.1 g := hψ
  show ∀ (m₁ : GL (Fin r) (AdeleRing (𝓞 K) K)) (m₂ : GL (Fin s) (AdeleRing (𝓞 K) K)),
    (lam K (r + s) (Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x) ψ).1 (blk m₁ m₂) = 0
  intro m₁ m₂
  let Y : ArchMatrix K (r + s) := Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) x
  let g : AdelicGLn.AdelicGL K (r + s) := blk m₁ m₂
  have hd := CuspidalSpectrum.hasDerivAt_archExp ψ g Y 0
  simp only [zero_smul, CuspidalSpectrum.archExp_zero, mul_one] at hd
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear (AdeleRing (𝓞 K) K) r s m₁ m₂
  have hmap : Matrix.GeneralLinearGroup.map (RingHom.id (AdeleRing (𝓞 K) K)) (blk m₁ m₂) = blk m₁ m₂ := by
    ext
    rfl
  have hconst : (fun t : ℝ => ψ.1 (g * CuspidalSpectrum.archExp (t • Y))) = fun _ => ψ.1 g := by
    funext t
    have hsY : t • Y = Matrix.single (Fin.castAdd s i) (Fin.natAdd r j) (t • x) :=
      Matrix.smul_single _ _ _ _
    obtain ⟨P, hP⟩ := archExp_single K r s i j (t • x)
    rw [hsY, hP]
    have h1 := hc (AdeleRing (𝓞 K) K) (RingHom.id _) P
    rw [hmap] at h1
    show ψ.1 (blk m₁ m₂ * unipGL P) = ψ.1 (blk m₁ m₂)
    rw [h1, hψ']
  rw [hconst] at hd
  have h2 := hd.unique (hasDerivAt_const (0 : ℝ) (ψ.1 g))
  exact h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ArchimedeanUnitaryLeISupEmbUAndCommute
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep GlobalTheory.UnitaryBC Formalism.BasicNotions
open scoped TensorProduct

section
open GlobalTheory.DefU Matrix
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

private theorem infinite_unitary_generated_by_embeddings (s : Finset (InfinitePlace E)) :
    ∀ g ∈ infU E n, (∀ w, w ∉ s → evGL w (cInf g) = 1) → g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro g hg h
    have h2 : GeneralLinearGroup.map (pFin E) g.1 = 1 := hg
    have h1 : cInf g = 1 := gl_ext_evGL fun w => by
      rw [h w (Finset.notMem_empty w), map_one]
    have : g = 1 := by
      refine Subtype.ext (ga_ext ?_ ?_)
      · change cInf g = cInf 1
        rw [h1, map_one]
      · rw [h2]
        exact (map_one _).symm
    rw [this]
    exact one_mem _
  | insert v s hv ih =>
    intro g hg h
    have hr : (embRet v.embedding g : UA E n) ∈ embU n v.embedding := (embRet v.embedding g).2
    have hr' : (embRet v.embedding g : UA E n) ∈ ⨆ τ : E →+* ℂ, embU n τ :=
      (le_iSup (fun τ : E →+* ℂ => embU n τ) v.embedding) hr
    have hk : (embRet v.embedding g : UA E n)⁻¹ * g ∈ ⨆ τ : E →+* ℂ, embU n τ := by
      refine ih _ (mul_mem (inv_mem (embU_le_infU _ hr)) hg) fun w hw => ?_
      rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, InfinitePlace.mk_embedding]
      by_cases e : w = v
      · subst e
        rw [evGL_cutGL_self, inv_mul_cancel]
      · rw [evGL_cutGL_of_ne e, h w (by simp [e, hw]), inv_one, one_mul]
    simpa using mul_mem hr' hk

end

open GlobalTheory.DefU Matrix in
theorem UpperTheory.archimedeanUnitary_le_iSup_embU_and_commute :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), infU E n ≤ (⨆ τ : E →+* ℂ, embU n τ) ∧ ∀ τ τ' : E →+* ℂ, InfinitePlace.mk τ ≠ InfinitePlace.mk τ' → ∀ a ∈ embU (E := E) n τ, ∀ b ∈ embU n τ', a * b = b * a := by
  intro E _ _ _ n
  refine ⟨fun g hg => infinite_unitary_generated_by_embeddings Finset.univ g hg fun w hw => (hw (Finset.mem_univ w)).elim, ?_⟩
  intro τ τ' hne a ha b hb
  have h2 : GeneralLinearGroup.map (pFin E) b.1 = 1 := hb.1
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * b) = cInf (b * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ'
    · rw [evGL_cInf_of_mem ha (h ▸ hne.symm), one_mul, mul_one]
    · rw [evGL_cInf_of_mem hb h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CapOpCommuteRightTranslation
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem semiconj_gen {R : Type} [CommRing R] [Algebra ℝ R] {ι : Type} [Fintype ι] {n : ℕ}
    {A : Type} [Ring A] [Algebra ℂ A] [Algebra ℝ A] [IsScalarTower ℝ ℂ A] (D : Idem R ι)
    (l : Matrix (Fin n) (Fin n) R →ₗ[ℝ] A) (T : A) (P Q : Matrix (Fin n) (Fin n) R)
    (h : ∀ X, T * l X = l (P * X * Q) * T) (τ : ι) (i j : Fin n) :
    T * gen D l τ i j = (∑ k, ∑ m, (D.ch τ (P k i) * D.ch τ (Q j m)) • gen D l τ k m) * T := by
  have ent : ∀ (k m : Fin n) (r : R), (P * Matrix.single i j r * Q) k m = P k i * Q j m * r := by
    intro k m r
    simp [Matrix.mul_apply, Matrix.single_apply, ite_and, Finset.sum_ite_eq, Finset.sum_ite_eq', ite_mul]
    ring
  have key : ∀ x : ℂ ⊗[ℝ] R, T * unitMap l i j x =
      (∑ k, ∑ m, unitMap l k m ((1 ⊗ₜ[ℝ] (P k i * Q j m)) * x)) * T := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c r =>
      rw [unitMap_tmul, mul_smul_comm, h, Matrix.matrix_eq_sum_single (P * Matrix.single i j r * Q)]
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.sum_mul, Finset.smul_sum, Algebra.TensorProduct.tmul_mul_tmul, one_mul,
        unitMap_tmul, ent, smul_mul_assoc]
    | add x y hx hy =>
      simp only [map_add (f := _), mul_add, hx, hy, Finset.sum_add_distrib, add_mul]
  show T * unitMap l i j (D.e τ) = _
  rw [key]
  congr 1
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun m _ => ?_
  rw [D.mul_e, map_smul, map_mul]
  rfl

private theorem rtInf_lam {K : Type} [Field K] [NumberField K] {n : ℕ} (a : archGroup K n)
    (y : GL (Fin n) (mixedSpace K)) (hy : y = a.1) (X : Matrix (Fin n) (Fin n) (mixedSpace K)) :
    rtInf a * lam K n X = lam K n (y.val * X * (y⁻¹).val) * rtInf a := by
  subst hy
  apply LinearMap.ext
  intro φ
  simp only [Module.End.mul_apply, lam_apply]
  rw [uAction_rtInf, IsExpLieAlgebra.AdU_ι]
  congr 4
  apply Subtype.ext
  simp [IsExpLieAlgebra.AdLie, IsExpLieAlgebra.Ad, toLie, IsExpLieAlgebra.toLie, IsExpLieAlgebra.ofLie,
    mul_assoc]
  show (show ArchMatrix K n from X) = ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)) *
    ((((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n) * ((show ArchMatrix K n from X) *
      ((↑(↑a : (ArchMatrix K n)ˣ)⁻¹ : ArchMatrix K n)))) * ((↑a : (ArchMatrix K n)ˣ) : ArchMatrix K n))
  simp only [mul_assoc, Units.inv_mul_cancel_left]
  exact (Units.inv_mul_cancel_right (show ArchMatrix K n from X) (a : (ArchMatrix K n)ˣ)).symm

theorem UpperTheory.capOp_commute_rightTranslation :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (ι : Type) [Fintype ι] (D : Idem (mixedSpace K) ι) (τ : ι) (u : ℂ) (a : archGroup K n), Commute (capOp D n τ u) (rtInf a) := by
  intro K _ _ n ι _ D τ u a
  let y : GL (Fin n) (mixedSpace K) := a.1
  let P : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix y.val
  let Q : Matrix (Fin n) (Fin n) ℂ := (D.ch τ).mapMatrix (y⁻¹).val
  have hQP : Q * P = 1 := by
    simp only [Q, P]
    rw [← map_mul, Units.inv_mul, map_one]
  have hsemi := semiconj_gen D (lam K n) (rtInf a) y.val (y⁻¹).val
    (fun X => rtInf_lam a y rfl X) τ
  have hq := GlobalTheory.CapAdInv.qdet_semiconj (gen D (lam K n) τ) _ (rtInf a) hsemi u
  have hGl := (UpperTheory.gen_glRelations_and_commute_of_isLie (mixedSpace K) ι n _ D (lam K n) (isLie_lam K n)).1 τ
  have had := GlobalTheory.CapAdInv.qdet_ad (gen D (lam K n) τ) hGl P Q hQP u
  show Formalism.REAL.qdet (gen D (lam K n) τ) u * rtInf a = rtInf a * Formalism.REAL.qdet (gen D (lam K n) τ) u
  rw [hq]
  congr 1
  exact had.symm
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.CongruenceSubgroupEqDiagonalUnipotentLowerIwahor
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL ValuativeRel

private theorem inv_int {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {n : Type} [Fintype n] [DecidableEq n] [LinearOrder n] {c : GL n k}
    (hc : c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k n) (i j : n) : valuation k ((c⁻¹).val i j) ≤ 1 := by
  let M : Matrix n n 𝒪[k] := Matrix.of fun i j => ⟨c.val i j, hc.1 i j⟩
  have hdet : c.val.det = 1 := by
    rw [Matrix.det_of_lowerTriangular c.val fun i j hij => hc.2.1 i j hij]
    simp [hc.2.2]
  have hM : (algebraMap 𝒪[k] k).mapMatrix M = c.val := by ext i j; rfl
  have e : (c⁻¹).val = (algebraMap 𝒪[k] k).mapMatrix M.adjugate := by
    rw [RingHom.map_adjugate, hM, Matrix.coe_units_inv, Matrix.inv_def, hdet]
    simp
  rw [e]
  exact (M.adjugate i j).2

theorem UpperTheory.congruence_subgroup_eq_diagonal_unipotent_lower_iwahori :
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (N : ℕ) (γ : (ValueGroupWithZero k)ˣ) (hγ : γ ≤ 1),
    ∀ g ∈ GlobalTheory.CentralExponent.cong (Fin N) γ hγ, ∃ d : Fin N → kˣ, (∀ i, valuation k ((d i : k) - 1) < γ) ∧
      ∃ x ∈ unipB k (Fin N), ∃ c ∈ GlobalTheory.SmGL.IwahoriOnto.lowerInt k (Fin N), g = diagT k (Fin N) d * x * c := by
  intro k _ _ _ _ N γ hγ g hg
  have hg' : ∀ i j, valuation k ((g.val - 1) i j) < γ := hg
  have h1 : g ∈ KOne k (Fin N) := GlobalTheory.StepData.mem_KOne.2 fun i j => (hg' i j).trans_le hγ
  have hI : g ∈ iwahori k (Fin N) := by
    refine mem_iwahori.2 ⟨GlobalTheory.StepData.KOne_le_KO h1, fun i j hij => ?_⟩
    have := (hg' i j).trans_le (show ((γ : ValueGroupWithZero k)) ≤ 1 from hγ)
    rwa [Matrix.sub_apply, Matrix.one_apply_ne hij.ne', sub_zero] at this
  obtain ⟨d, -, x, hx, c, hc, e⟩ := GlobalTheory.SmGL.IwahoriOnto.iwahori_factor k (Fin N) g hI
  refine ⟨d, fun i => ?_, x, hx, c, hc, e⟩
  have hcl : c ∈ unipBLower k (Fin N) :=
    (mem_unipB (n := (Fin N)ᵒᵈ) k).2 ⟨fun i j hij => hc.2.1 i j hij, hc.2.2⟩
  have hci : (c⁻¹).val i i = 1 := ((mem_unipB (n := (Fin N)ᵒᵈ) k).1 (inv_mem hcl)).2 i
  have h2 : (g * c⁻¹).val i i = d i := by
    rw [e, mul_inv_cancel_right, Units.val_mul, val_diagT, Matrix.diagonal_mul, ((mem_unipB k).1 hx).2 i, mul_one]
  have h3 : ((g.val - 1) * (c⁻¹).val) i i = (d i : k) - 1 := by
    rw [sub_mul, one_mul, Matrix.sub_apply, hci, ← Units.val_mul, h2]
  rw [← h3, Matrix.mul_apply]
  refine Valuation.map_sum_lt _ γ.ne_zero fun s _ => ?_
  rw [map_mul]
  exact (mul_le_of_le_one_right' (inv_int hc s i)).trans_lt (hg' i s)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermArchSmooth
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.constantTerm_archSmooth :
    ∀ (K : Type) [Field K] [NumberField K] (n r : ℕ) (φ : archSmooth K n), IsAutomorphicForm φ.1 → ∃ hs : IsArchSmooth (constantTerm r φ.1), ∀ X : (isExpLieAlgebra K n).lieSubalgebra, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) ⟨constantTerm r φ.1, hs⟩).1 = constantTerm r (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 := by
  intro K _ _ n r φ hφ
  let μ : Measure (archGroup K n) := Measure.haar
  obtain ⟨d, b, ε, B, h1, h2, h3, h4, h5⟩ := exists_archCartanData K n
  obtain ⟨P, hPm, hPd, hP⟩ :=
    hφ.isSmoothKZ.exists_aeval_laplacian_sliceL_eq_zero b ε B h1 h2 h3 h4 h5
  obtain ⟨κ, hκs, hκc, -, hκ⟩ :=
    (isExpLieAlgebra K n).exists_kernel_eq_conv_of_aeval_laplacian μ b P hPm hPd
      (U := Set.univ) Filter.univ_mem
  have hκcont : Continuous κ :=
    IsExpLieAlgebra.IsTestFunction.continuous (isExpLieAlgebra K n) ⟨hκs, hκc⟩
  have rep : ∀ g y, archSlice φ.1 g y = ∫ z, archSlice φ.1 g (y * z) * κ z ∂μ :=
    fun g y => hκ _ (hP g) y
  have repφ : ∀ g, φ.1 g = ∫ z, φ.1 (g * infEmb K n z) * κ z ∂μ := by
    intro g
    have := rep g 1
    simpa [archSlice_apply] using this
  have hc : Continuous φ.1 := hφ.continuous
  have hct := UpperTheory.constantTerm_convolution_arch K n r μ φ.1 φ.1 κ hc hκcont hκc repφ
  have hctc := UpperTheory.continuous_constantTerm K n r φ.1 hc
  have hsliceC : ∀ g, Continuous (archSlice (constantTerm r φ.1) g) := by
    intro g
    show Continuous fun x => constantTerm r φ.1 (g * infEmb K n x)
    exact hctc.comp (continuous_const.mul continuous_infEmb)
  have repct : ∀ g y, archSlice (constantTerm r φ.1) g y
      = ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := by
    intro g y
    simp only [archSlice_apply]
    rw [hct (g * infEmb K n y)]
    simp [mul_assoc, map_mul]
  have hs : IsArchSmooth (constantTerm r φ.1) := by
    intro g
    have hfun : archSlice (constantTerm r φ.1) g
        = fun y => ∫ z, archSlice (constantTerm r φ.1) g (y * z) * κ z ∂μ := funext (repct g)
    rw [hfun]
    exact (isExpLieAlgebra K n).isSmoothFun_integral_mul μ (hsliceC g) ⟨hκs, hκc⟩
  refine ⟨hs, fun X => ?_⟩
  funext g
  have hD := (isExpLieAlgebra K n).continuous_convDeriv hκs ((isExpLieAlgebra K n).ofLie X)
  have hDc := (isExpLieAlgebra K n).hasCompactSupport_convDeriv hκc ((isExpLieAlgebra K n).ofLie X)
  have repU : ∀ h, (uAction (UniversalEnvelopingAlgebra.ι ℝ X) φ).1 h
      = ∫ y, φ.1 (h * infEmb K n y)
          * (isExpLieAlgebra K n).convDeriv ((isExpLieAlgebra K n).ofLie X) κ y ∂μ := by
    intro h
    rw [uAction_ι_apply,
      IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (φ.2 h) (rep h)]
    simp [archSlice_apply]
  rw [uAction_ι_apply,
    IsExpLieAlgebra.rightDeriv_eq_integral_convDeriv hκs hκc (hs g) (repct g),
    UpperTheory.constantTerm_convolution_arch K n r μ φ.1 _ _ hc hD hDc repU g]
  simp [archSlice_apply]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ConstantTermLeviRationalLeftInvariant
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

private theorem blk_mul_blk_inv {r s : ℕ} {R : Type} [CommRing R] (m₁ : GL (Fin r) R) (m₂ : GL (Fin s) R) :
    blk m₁ m₂ * blk m₁⁻¹ m₂⁻¹ = 1 := by
  simp only [blk]
  rw [emb_comm m₁⁻¹ m₂⁻¹, map_inv, map_inv]
  group

theorem UpperTheory.constantTerm_levi_rational_left_invariant :
    ∀ (K : Type) [Field K] [NumberField K] (r s : ℕ) (φ : AdelicGLn.AdelicGL K (r + s) → ℂ),
      IsLeftInvariant φ → ∀ (γ₁ : GL (Fin r) K) (γ₂ : GL (Fin s) K) g,
        constantTerm (r := r) φ (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g) =
          constantTerm (r := r) φ g := by
  intro K _ _ r s φ hφ γ₁ γ₂ g
  have hdiag : ∀ γ : GL (Fin (r + s)) K, AdelicGLn.diagonal K (r + s) γ =
      GeneralLinearGroup.map (algebraMap K (AdeleRing (𝓞 K) K)) γ := fun _ => rfl
  obtain ⟨c, hc⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁ γ₂
  obtain ⟨c', hc'⟩ := UpperTheory.blockDiag_conj_unipotent_linear K r s γ₁⁻¹ γ₂⁻¹
  have hDD : AdelicGLn.diagonal K (r + s) (blk γ₁⁻¹ γ₂⁻¹) = (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    rw [← map_inv]
    congr 1
    exact eq_inv_of_mul_eq_one_right (blk_mul_blk_inv γ₁ γ₂)
  have hu : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * Y q) =
        (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ * unipGL Y * AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) := by
    intro Y
    have h := hc' (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag, hDD] at h
    rw [h]
    group
  have hv : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * Y q) =
        AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * unipGL Y * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂))⁻¹ := by
    intro Y
    have h := hc (AdeleRing (𝓞 K) K) (algebraMap K (AdeleRing (𝓞 K) K)) Y
    rw [← hdiag] at h
    rw [h]
    group
  have hmem : ∀ (d : UPos (r + s) r → UPos (r + s) r → K) (X : UPos (r + s) r → AdeleRing (𝓞 K) K),
      X ∈ unipLattice K (r + s) r →
        (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) ∈ unipLattice K (r + s) r := by
    intro d X hX
    obtain ⟨y, rfl⟩ := AddMonoidHom.mem_range.mp hX
    refine AddMonoidHom.mem_range.mpr ⟨fun p => ∑ q, d p q * y q, ?_⟩
    funext p
    set_option synthInstance.maxHeartbeats 100000 in
      simp [AddMonoidHom.compLeft_apply, map_sum, map_mul]
  have hcont : ∀ d : UPos (r + s) r → UPos (r + s) r → K,
      Continuous (fun (X : UPos (r + s) r → AdeleRing (𝓞 K) K) p =>
        ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (d p q) * X q) := by
    intro d
    refine continuous_pi fun p => ?_
    exact continuous_finsetSum _ fun q _ => continuous_const.mul (continuous_apply q)
  have hinv1 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c' q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hv, hu]
    group
  have hinv2 : ∀ Y : UPos (r + s) r → AdeleRing (𝓞 K) K,
      (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) *
        (∑ q', algebraMap K (AdeleRing (𝓞 K) K) (c q q') * Y q')) = Y := by
    intro Y
    apply unipGL_injective
    rw [hu, hv]
    group
  let α : (UPos (r + s) r → AdeleRing (𝓞 K) K) ≃ₜ+ (UPos (r + s) r → AdeleRing (𝓞 K) K) :=
    { toFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q
      invFun := fun X p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c p q) * X q
      left_inv := fun X => hinv1 X
      right_inv := fun X => hinv2 X
      map_add' := by
        intro X Y
        funext p
        simp [mul_add, Finset.sum_add_distrib]
      continuous_toFun := hcont c'
      continuous_invFun := hcont c }
  have hα : ∀ X, α X ∈ unipLattice K (r + s) r ↔ X ∈ unipLattice K (r + s) r := by
    intro X
    constructor
    · intro h
      have h2 := hmem c (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) h
      rwa [hinv1] at h2
    · exact hmem c' X
  have hper : ∀ ξ ∈ unipLattice K (r + s) r, ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL (ξ + X) * g) = φ (unipGL X * g) :=
    fun ξ hξ X => hφ.unipGL_vadd g ⟨ξ, hξ⟩ X
  have hstep : ∀ X : UPos (r + s) r → AdeleRing (𝓞 K) K,
      φ (unipGL X * (AdelicGLn.diagonal K (r + s) (blk γ₁ γ₂) * g)) = φ (unipGL (α X) * g) := by
    intro X
    rw [← hφ (blk γ₁⁻¹ γ₂⁻¹), hDD]
    change _ = φ (unipGL (fun p => ∑ q, algebraMap K (AdeleRing (𝓞 K) K) (c' p q) * X q) * g)
    rw [hu]
    group
  unfold constantTerm
  simp_rw [hstep]
  exact UpperTheory.integral_unipFundamentalDomain_comp_lattice_preserving K (r + s) r α hα (fun X => φ (unipGL X * g)) hper
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsFiniteDimensionalCompactTranslatesOfLevelT
section
open NumberField NumberField.mixedEmbedding Matrix MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm UpperTheory.V.Af.Fin
open scoped TensorProduct
attribute [local instance 100] LieRing.ofAssociativeRing

theorem UpperTheory.exists_finiteDimensional_compact_translates_of_level_types :
    ∀ (K : Type) [Field K] [NumberField K] (n : ℕ) (S : Submodule ℂ (archSmooth K n)), Level S → Types S → ∃ V : Submodule ℂ (Reduction.maxCompact (K := K) (n := n) → ℂ), FiniteDimensional ℂ V ∧ ∀ φ ∈ S, ∀ g, (fun k : Reduction.maxCompact (K := K) (n := n) => φ.1 (g * k.1)) ∈ V := by
  intro K _ _ n S hLev hTyp
  obtain ⟨L, hL, hinv⟩ := hLev
  obtain ⟨V₀, hV₀, -, hφV⟩ := hTyp
  obtain ⟨L', -, hL'L, -, t, ht⟩ := UpperTheory.exists_open_level_normalized_by_integralFiniteGL K n L hL
  have hk : ∀ k : Reduction.maxCompact (K := K) (n := n), ∃ c ∈ t, c⁻¹ * finPart k.1 ∈ L' :=
    fun k => ht _ (finPart_mem_integralFiniteGL k.2)
  let Ψ : (↥t → ↥V₀) →ₗ[ℂ] (Reduction.maxCompact (K := K) (n := n) → ℂ) :=
    { toFun := fun h k =>
        (h ⟨Classical.choose (hk k), (Classical.choose_spec (hk k)).1⟩ : archCompact K n → ℂ)
          ⟨archPart k.1, archPart_mem_archCompact k.2⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  refine ⟨LinearMap.range Ψ, inferInstance, ?_⟩
  intro φ hφ g
  refine ⟨fun c => ⟨fun k' => φ.1 (g * finEmb K n c.1 * infEmb K n k'.1), hφV φ hφ _⟩, ?_⟩
  funext k
  show φ.1 (g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1)) = φ.1 (g * k.1)
  have hu : (Classical.choose (hk k))⁻¹ * finPart k.1 ∈ L := hL'L (Classical.choose_spec (hk k)).2
  have e : g * k.1 = g * finEmb K n (Classical.choose (hk k)) * infEmb K n (archPart k.1) *
      finEmb K n ((Classical.choose (hk k))⁻¹ * finPart k.1) := by
    conv_lhs => rw [← infEmb_archPart_mul_finEmb_finPart k.1]
    rw [map_mul, map_inv, mul_assoc g (finEmb K n _), ← infEmb_mul_finEmb_comm]
    simp only [mul_assoc, mul_inv_cancel_left]
  rw [e, hinv φ hφ _ hu]
end

