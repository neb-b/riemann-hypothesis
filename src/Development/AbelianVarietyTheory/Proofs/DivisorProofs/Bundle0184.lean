module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0139
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0099
public import ReciprocityTheory.CommutativeAlgebra.CohenMacaulay.Bundle0001
public import ReciprocityTheory.L2DbarEstimates.LeviForms.EventuallyDifferentiableAtOfContDiffAt
public import Development.AbelianVarietyTheory.Definitions.Divisors.TCoefMInMMul
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0157
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0129
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0169
public import Formalism.LatticeTheta.Statement

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterAugmentationSubspaceTopEqKerSmulStatement
section
open scoped TensorProduct
universe u
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.characterAugmentationSubspace_top_eq_ker_smul :
    ∀ (k : Type) [Field k] (C : Type) [CommRing C] (H : Type u) [AddCommGroup H]
      [Module k H] (σ : C →+* Module.End k H) (χ : C →+* k),
      letI : Module (k ⊗[ℤ] C) H := Module.compHom H
        (Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
          (fun _ _ => Algebra.commutes _ _)).toRingHom;
      ∀ x : H, x ∈ GlobalTheory.HTRho.mSub σ χ ⊤ ↔
        x ∈ (RingHom.ker (Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
          (fun _ _ => Commute.all _ _) : k ⊗[ℤ] C →ₐ[k] k) • ⊤ : Submodule (k ⊗[ℤ] C) H) := by
  intro k _ C _ H _ _ σ χ
  let L := Algebra.TensorProduct.lift (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
    (fun _ _ => Algebra.commutes _ _)
  let φ := Algebra.TensorProduct.lift (Algebra.ofId k k) χ.toIntAlgHom
    (fun _ _ => Commute.all _ _)
  let : Module (k ⊗[ℤ] C) H := Module.compHom H L.toRingHom
  let X := GlobalTheory.HTRho.mSub σ χ ⊤
  let Y : Submodule (k ⊗[ℤ] C) H := RingHom.ker φ • ⊤
  change ∀ x : H, x ∈ X ↔ x ∈ Y
  have hsmul (a : k ⊗[ℤ] C) (y : H) : a • y = L a y := rfl
  have hL (l : k) (c : C) (y : H) : L (l ⊗ₜ c) y = l • σ c y := by
    exact congrArg (fun f : Module.End k H => f y)
      (Algebra.TensorProduct.lift_tmul (Algebra.ofId k (Module.End k H)) σ.toIntAlgHom
        (fun _ _ => Algebra.commutes _ _) l c)
  have hφ (l : k) (c : C) : φ (l ⊗ₜ c) = l * χ c := by
    simp [φ]
  have hSub (a : k ⊗[ℤ] C) (y : H) : L a y - φ a • y ∈ X := by
    induction a using TensorProduct.inductionOn with
    | tmul l c =>
      rw [hL, hφ, mul_smul, ← smul_sub]
      exact Submodule.smul_mem X l (Submodule.subset_span ⟨c, y, trivial, by simp⟩)
    | add a b ha hb =>
      rw [map_add L, map_add φ, LinearMap.add_apply, add_smul, add_sub_add_comm]
      exact add_mem ha hb
  intro x
  constructor
  · intro hx
    induction hx using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, y, -, rfl⟩ := hz
      let a : k ⊗[ℤ] C := 1 ⊗ₜ c - χ c ⊗ₜ (1 : C)
      have ha : a ∈ RingHom.ker φ := by
        change φ a = 0
        simp [a, hφ]
      have hy : a • y ∈ Y := Submodule.smul_mem_smul ha (Submodule.mem_top (x := y))
      have hay : a • y = σ (algebraMap C C c) y - χ c • y := by
        rw [hsmul]
        simp [a, hL]
      exact hay ▸ hy
    | zero => exact Y.zero_mem
    | add a b _ _ ha hb => exact Y.add_mem ha hb
    | smul l z _ hz =>
      have hl : (l ⊗ₜ (1 : C) : k ⊗[ℤ] C) • z = l • z := by
        rw [hsmul, hL, map_one, one_apply_eq_self]
      exact hl ▸ Y.smul_mem _ hz
  · intro hx
    refine Submodule.smul_induction_on (show x ∈ RingHom.ker φ • ⊤ from hx) ?_ ?_
    · intro a ha y _
      rw [hsmul]
      simpa only [RingHom.mem_ker.mp ha, zero_smul, sub_zero] using hSub a y
    · intro a b ha hb
      exact X.add_mem ha hb
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClosureGenericFibreClopenSplit
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

theorem GlobalTheory.closure_generic_fibre_clopen_split : ∀ (R A : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] [CommRing A] [Algebra R A], Algebra.Smooth R A → ∀ C C' : Set (PrimeSpectrum A), C ∪ C' = {r | r.asIdeal.comap (algebraMap R A) = ⊥} → Disjoint C (closure C') → Disjoint (closure C) C' → Disjoint (closure C) (closure C') ∧ closure C ∪ closure C' = Set.univ := by
  intro R A _ _ _ _ _ hsm C C' hU hd1 hd2
  let K := FractionRing R
  let f : A →+* A ⊗[R] K := (Algebra.TensorProduct.includeLeft : A →ₐ[R] A ⊗[R] K).toRingHom
  let φ := PrimeSpectrum.comap f
  have hφc : Continuous φ := PrimeSpectrum.continuous_comap f

  have hF : {r : PrimeSpectrum A | r.asIdeal.comap (algebraMap R A) = ⊥} = Set.range φ := by
    have h1 := _root_.GlobalTheory.range_comap_includeRight_field R A K
    have hker : RingHom.ker (algebraMap R K) = ⊥ :=
      (RingHom.injective_iff_ker_eq_bot _).1 (IsFractionRing.injective R K)
    rw [hker] at h1
    rw [← h1]
    let e := (Algebra.TensorProduct.comm R A K).toRingEquiv
    have hg : (Algebra.TensorProduct.includeRight : A →ₐ[R] K ⊗[R] A).toRingHom = e.toRingHom.comp f := by
      ext a
      simp [f, e]
    rw [hg, PrimeSpectrum.comap_comp, Set.range_comp]
    have hsurj : Set.range (PrimeSpectrum.comap e.toRingHom) = Set.univ := by
      refine Set.eq_univ_of_forall fun y => ⟨PrimeSpectrum.comap e.symm.toRingHom y, ?_⟩
      rw [← PrimeSpectrum.comap_comp_apply, RingEquiv.symm_toRingHom_comp_toRingHom]
      rfl
    rw [hsurj, Set.image_univ]

  have hinj : Function.Injective f := by
    have hl := Module.Flat.lTensor_preserves_injective_linearMap (M := A) (Algebra.linearMap R K)
      (IsFractionRing.injective R K)
    intro x y hxy
    have : (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm x) =
        (LinearMap.lTensor A (Algebra.linearMap R K)) ((TensorProduct.rid R A).symm y) := by
      simpa [f] using hxy
    exact (TensorProduct.rid R A).symm.injective (hl this)
  have hdense : DenseRange φ :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).2
      (by rw [(RingHom.injective_iff_ker_eq_bot f).1 hinj]; exact bot_le)
  have hCC' : Disjoint C C' := hd1.mono_right subset_closure
  have hunion : φ ⁻¹' C ∪ φ ⁻¹' C' = Set.univ := by
    rw [← Set.preimage_union, hU, hF, Set.preimage_range]
  have hcompl : IsCompl (φ ⁻¹' C) (φ ⁻¹' C') :=
    ⟨hCC'.preimage φ, codisjoint_iff.2 hunion⟩
  have hS1 : φ ⁻¹' closure C = φ ⁻¹' C := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact h
    · exact absurd h (Set.disjoint_left.1 hd2 hx)
  have hclosed : IsClosed (φ ⁻¹' C) := hS1 ▸ isClosed_closure.preimage hφc
  have hS2 : φ ⁻¹' closure C' = φ ⁻¹' C' := by
    refine Set.Subset.antisymm (fun x hx => ?_) (Set.preimage_mono subset_closure)
    have hx' : x ∈ φ ⁻¹' C ∪ φ ⁻¹' C' := hunion ▸ Set.mem_univ x
    rcases hx' with h | h
    · exact absurd hx (Set.disjoint_left.1 hd1 h)
    · exact h
  have hclosed' : IsClosed (φ ⁻¹' C') := hS2 ▸ isClosed_closure.preimage hφc
  have hopen : IsOpen (φ ⁻¹' C) := by
    rw [← isClosed_compl_iff, hcompl.compl_eq]; exact hclosed'
  obtain ⟨ε, hε, hεS⟩ := PrimeSpectrum.isClopen_iff.1 ⟨hclosed, hopen⟩
  obtain ⟨a, ha, haε⟩ := _root_.GlobalTheory.exists_isIdempotentElem_tmul_one_eq_of_smooth R A hsm ε hε
  have hfa : f a = ε := by simp [f, haε]
  have hpre : φ ⁻¹' (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) = φ ⁻¹' C := by
    rw [hεS, ← hfa]
    ext x
    simp [φ, PrimeSpectrum.mem_basicOpen]
  have hCa : C ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inl hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ φ ⁻¹' C := hx
    rw [← hpre] at hy
    exact hy
  have hC'a : C' ⊆ (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A))ᶜ := by
    intro x hx
    have hxF : x ∈ Set.range φ := hF ▸ hU ▸ Or.inr hx
    obtain ⟨y, rfl⟩ := hxF
    have hy : y ∈ (φ ⁻¹' C)ᶜ := hcompl.compl_eq ▸ hx
    rw [← hpre] at hy
    exact hy
  have hclo : IsClopen (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)) :=
    PrimeSpectrum.isClopen_iff.2 ⟨a, ha, rfl⟩
  refine ⟨?_, ?_⟩
  · exact (disjoint_compl_right (a := (PrimeSpectrum.basicOpen a : Set (PrimeSpectrum A)))).mono
      (closure_minimal hCa hclo.isClosed) (closure_minimal hC'a hclo.isOpen.isClosed_compl)
  · rw [← closure_union, hU, hF]
    exact hdense.closure_range
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CokernelTorsionOfFiniteLengthModElement
section
open IsLocalRing

namespace GlobalTheory

theorem exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot
    (R : Type) [CommRing R] [IsLocalRing R] (f : R)
    (hdim : 1 ≤ ringKrullDim (R ⧸ Ideal.span {f})) :
    ∃ P : Ideal R, P.IsPrime ∧ f ∈ P ∧ P ≠ maximalIdeal R := by
  by_contra! hne
  have h0 : Ring.KrullDimLE 0 (R ⧸ Ideal.span {f}) := by
    refine Ring.krullDimLE_zero_iff.mpr fun Q hQ => ?_
    have hc : Q.comap (Ideal.Quotient.mk (Ideal.span {f})) = maximalIdeal R := by
      refine hne _ (Ideal.comap_isPrime _ _) ?_
      rw [Ideal.mem_comap, Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self f)]
      exact Q.zero_mem
    have hmax := (maximalIdeal.isMaximal R).map_of_surjective_of_ker_le
      (f := Ideal.Quotient.mk (Ideal.span {f})) Ideal.Quotient.mk_surjective
      (by rw [← hc]; exact Ideal.comap_mono bot_le)
    rwa [← hc, Ideal.map_comap_of_surjective _ Ideal.Quotient.mk_surjective] at hmax
  have := (Ring.krullDimLE_iff (n := 0)).mp h0
  have h10 := hdim.trans this
  norm_num at h10

theorem cokernel_torsion_of_finiteLength_mod : ∀ (R : Type) [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (f : R), 1 ≤ ringKrullDim (R ⧸ Ideal.span {f}) → ∀ (A B : Type) [CommRing A] [Algebra R A] [CommRing B] [Algebra R B] [Module.Finite R B] (ψ : A →ₐ[R] B), (∃ k : ℕ, ∀ x ∈ maximalIdeal R ^ k, ∀ b : B, ∃ a : A, ∃ c : B, x • b = ψ a + f • c) → ∃ s : R, s ≠ 0 ∧ ∀ b : B, s • b ∈ ψ.range := by
  intro R _ _ _ f hdim A B _ _ _ _ _ ψ ⟨k, hk⟩
  obtain ⟨P, hP, hfP, hPm⟩ := exists_prime_ne_maximalIdeal_of_one_le_ringKrullDim_quot R f hdim

  obtain ⟨x, hxk, hxP⟩ : ∃ x ∈ maximalIdeal R ^ k, x ∉ P := by
    by_contra! h
    have hle : maximalIdeal R ≤ P := hP.le_of_pow_le h
    exact hPm (le_antisymm (le_maximalIdeal hP.ne_top) hle)
  set N : Submodule R B := LinearMap.range ψ.toLinearMap
  set I : Ideal R := Ideal.span {f}
  let φ : Module.End R (B ⧸ N) := algebraMap R (Module.End R (B ⧸ N)) x
  have hφ : LinearMap.range φ ≤ I • ⊤ := by
    rintro _ ⟨c, rfl⟩
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective N c
    obtain ⟨a, c', hac⟩ := hk x hxk b
    have : φ (Submodule.Quotient.mk b) = f • Submodule.Quotient.mk c' := by
      simp only [φ, Module.algebraMap_end_apply, ← Submodule.Quotient.mk_smul, hac]
      have ha0 : Submodule.Quotient.mk (p := N) (ψ a) = 0 := (Submodule.Quotient.mk_eq_zero N).mpr ⟨a, rfl⟩
      rw [Submodule.Quotient.mk_add, ha0, zero_add]
    rw [this]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self f) Submodule.mem_top
  obtain ⟨p, hmon, -, hcoeff, hzero⟩ :=
    LinearMap.exists_monic_and_natDegree_eq_and_coeff_mem_pow_and_aeval_eq_zero R φ I hφ
  refine ⟨p.eval x, ?_, ?_⟩
  · intro h0
    apply hxP
    apply hP.mem_of_pow_mem p.natDegree
    have hs : p.eval x ∈ P := h0 ▸ P.zero_mem
    rw [Polynomial.eval_eq_sum_range, Finset.sum_range_succ, hmon.coeff_natDegree, one_mul] at hs
    refine (P.add_mem_iff_right ?_).mp hs
    refine P.sum_mem fun i hi => P.mul_mem_right _ ?_
    have hi' : 0 < p.natDegree - i := Nat.sub_pos_of_lt (Finset.mem_range.mp hi)
    have hIP : I ≤ P := (Ideal.span_singleton_le_iff_mem P).mpr hfP
    exact hIP (Ideal.pow_le_self hi'.ne' (hcoeff i))
  · intro b
    have h1 : (Polynomial.aeval φ p) (Submodule.Quotient.mk b) = 0 := by rw [hzero]; rfl
    rw [show φ = algebraMap R _ x from rfl, Polynomial.aeval_algebraMap_apply,
      Module.algebraMap_end_apply, Polynomial.aeval_def] at h1
    change Polynomial.eval x p • Submodule.Quotient.mk (p := N) b = 0 at h1
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at h1
    obtain ⟨a, ha⟩ := h1
    exact ⟨a, ha⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexHessianLogOneAddNormSq
section
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.FubiniStudyHessian

open ReciprocityTheory.L2DbarEstimates
open scoped ComplexConjugate

variable {n : ℕ}

theorem differentiableAt_coord (i : Fin n) (x : V n) : DifferentiableAt ℂ (fun w : V n => w i) x :=
  (EuclideanSpace.proj (𝕜 := ℂ) i).differentiableAt

theorem wd_coord (j i : Fin n) (x : V n) : wd n j (fun w : V n => w i) x = if j = i then 1 else 0 := by
  rw [wd_of_differentiableAt (differentiableAt_coord i x)]
  have h : fderiv ℂ (fun w : V n => w i) x = EuclideanSpace.proj (𝕜 := ℂ) i :=
    (EuclideanSpace.proj (𝕜 := ℂ) i).fderiv
  rw [h]
  by_cases hji : j = i
  · subst hji; simp [bas]
  · simp [bas, hji, Ne.symm hji]

theorem normSq_eq_sum : (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) = fun w => ∑ i, w i * conj (w i) := by
  funext w
  rw [EuclideanSpace.norm_sq_eq]
  simp [Complex.mul_conj, Complex.normSq_eq_norm_sq]

theorem differentiableAt_normSq (x : V n) : DifferentiableAt ℝ (fun w : V n => ‖w‖ ^ 2) x :=
  ((contDiff_norm_sq ℂ (n := 1)).differentiable one_ne_zero) x

theorem wd_normSq (j : Fin n) (x : V n) :
    wd n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = conj (x j) := by
  have hd : ∀ i, DifferentiableAt ℝ (fun w : V n => w i) x := fun i =>
    (differentiableAt_coord i x).restrictScalars ℝ
  rw [normSq_eq_sum, wd_sum Finset.univ (f := fun i (w : V n) => w i * conj (w i))
    (fun i _ => (hd i).mul (differentiableAt_conj (hd i)))]
  have h : ∀ i, wd n j (fun w : V n => w i * conj (w i)) x = if j = i then conj (x i) else 0 := fun i => by
    rw [wd_mul (hd i) (differentiableAt_conj (hd i)), wd_conj (hd i),
      wdb_of_differentiableAt (differentiableAt_coord i x), wd_coord]
    simp
  simp [h]

theorem wdb_normSq (j : Fin n) (x : V n) :
    wdb n j (fun w : V n => ((‖w‖ ^ 2 : ℝ) : ℂ)) x = x j := by
  rw [wdb_ofReal (differentiableAt_normSq x), wd_normSq, Complex.conj_conj]

theorem wdb_log (l : Fin n) :
    wdb n l (fun w : V n => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) =
      fun w => (((1 + ‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * w l := by
  funext x
  have hpos : (1 + ‖x‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => Real.log (1 + t)) (1 / (1 + ‖x‖ ^ 2)) (‖x‖ ^ 2) :=
    ((hasDerivAt_id' (‖x‖ ^ 2)).const_add 1).log hpos
  rw [wdb_ofReal_comp (k := fun t : ℝ => Real.log (1 + t)) (v := fun w : V n => ‖w‖ ^ 2)
    hk.differentiableAt (differentiableAt_normSq x), hk.deriv, wdb_normSq, one_div]

theorem cHess_log_one_add_normSq : ∀ (n : ℕ) (v : ReciprocityTheory.L2DbarEstimates.V n), ReciprocityTheory.L2DbarEstimates.cHess n (fun w => (Real.log (1 + ‖w‖ ^ 2) : ℂ)) v = Matrix.of (fun j l => (if j = l then 1 else 0) / (1 + (‖v‖ : ℂ) ^ 2) - (starRingEnd ℂ (v j) * v l) / (1 + (‖v‖ : ℂ) ^ 2) ^ 2) := by
  intro n v
  ext j l
  have hpos : (1 + ‖v‖ ^ 2 : ℝ) ≠ 0 := by positivity
  have hk : HasDerivAt (fun t : ℝ => (1 + t)⁻¹) (-1 / (1 + ‖v‖ ^ 2) ^ 2) (‖v‖ ^ 2) :=
    ((hasDerivAt_id' (‖v‖ ^ 2)).const_add 1).inv hpos
  have hd : DifferentiableAt ℝ (fun w : V n => (1 + ‖w‖ ^ 2)⁻¹) v :=
    ((differentiableAt_normSq v).const_add 1).inv hpos
  simp only [cHess, Matrix.of_apply]
  rw [wdb_log, wd_mul (differentiableAt_ofReal hd) ((differentiableAt_coord l v).restrictScalars ℝ),
    wd_ofReal_comp (k := fun t : ℝ => (1 + t)⁻¹) (v := fun w : V n => ‖w‖ ^ 2)
      hk.differentiableAt (differentiableAt_normSq v), hk.deriv, wd_normSq, wd_coord]
  push_cast
  ring

end GlobalTheory.FubiniStudyHessian
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffIter
section
open MvPolynomial GlobalTheory.PsCo.Pc1 GlobalTheory.PsCo.Pc1.A
open scoped ContDiff

namespace GlobalTheory.PsCo.Pc1.Homot

noncomputable def scF (G : ℝ → ℝ) (j : ℕ) (s y : ℝ) : ℝ := s ^ j * iteratedDeriv (j + 1) G (s * y)

lemma contDiff_iter {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (k : ℕ) : ContDiff ℝ ∞ (iteratedDeriv k G) := by
  rw [iteratedDeriv_eq_iterate]
  exact hG.iterate_deriv k

lemma scF_contDiff {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) : ContDiff ℝ ∞ (Function.uncurry (scF G j)) := by
  have h := contDiff_iter hG (j + 1)
  exact (contDiff_fst.pow j).mul (h.comp (contDiff_fst.mul contDiff_snd))

lemma deriv_scF {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) : deriv (scF G j s) y = scF G (j + 1) s y := by
  have h := (contDiff_iter hG (j + 1)).differentiable (by simp)
  have h1 : HasDerivAt (fun y => s * y) s y := by simpa using (hasDerivAt_id y).const_mul s
  have h2 := ((h (s * y)).hasDerivAt.comp y h1).const_mul (s ^ j)
  have h3 : deriv (scF G j s) y = _ := h2.deriv
  rw [h3, scF, iteratedDeriv_succ (n := j + 1)]
  ring

lemma iter_scale {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (s y : ℝ) :
    iteratedDeriv (j + 1) (fun y => G (s * y)) y = s * scF G j s y := by
  rw [iteratedDeriv_comp_const_mul (hG.of_le (by exact_mod_cast le_top)) s, scF]
  ring

lemma iter_zero {G : ℝ → ℝ} (h0 : ∀ x, 1 ≤ x → G x = 0) (k : ℕ) {x : ℝ} (hx : 1 < x) : iteratedDeriv k G x = 0 := by
  have : G =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    filter_upwards [Ioi_mem_nhds hx] with y hy using h0 y (le_of_lt hy)
  rw [this.iteratedDeriv_eq k]
  simp

lemma scF_cont {G : ℝ → ℝ} (hG : ContDiff ℝ ∞ G) (j : ℕ) (y : ℝ) : Continuous fun s => scF G j s y :=
  (scF_contDiff hG j).continuous.comp (continuous_id.prodMk continuous_const)

theorem stHomot : GlobalTheory.PsCo.Pc1.StHomot := by
  intro n ε G p q hP hK t ht
  obtain ⟨hG, h0, -, -⟩ := hP
  have hI : ∀ j, IsCutFn (fun y => ∫ s in (1:ℝ)..t, scF G j s y) ∧
      ∀ y, deriv (fun y => ∫ s in (1:ℝ)..t, scF G j s y) y = ∫ s in (1:ℝ)..t, deriv (scF G j s) y := by
    intro j
    refine _root_.GlobalTheory.PsCo.Pc1.isCutFn_intervalIntegral_and_deriv (scF G j) 1 t (scF_contDiff hG j) ⟨2, ?_⟩
    intro s hs y hy
    rw [Set.uIcc_of_le ht] at hs
    have : 1 < s * y := by nlinarith [hs.1]
    simp [scF, iter_zero h0 _ this]
  have key : famF ε G p 1 - famF ε G p t = -∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) := by
    funext g
    set D : ℝ → ℂ := fun s => ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
      ((scF G (j + 1) s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (rP ε) * q x j) +
        (scF G j s (rM ε g) : ℂ) * ev g (dZ ε (Matrix.single x.1.2 x.1.1 1) (q x j))) with hD
    have hc : ∀ j, Continuous fun s => (scF G j s (rM ε g) : ℂ) := fun j =>
      Complex.continuous_ofReal.comp (scF_cont hG j _)
    have hder : ∀ s ∈ Set.uIcc (1:ℝ) t, HasDerivAt (fun s : ℝ => famF ε G p s g) (D s) s := by
      intro s hs
      rw [Set.uIcc_of_le ht] at hs
      have hs0 : 0 < s := by linarith [hs.1]
      have h := _root_.GlobalTheory.PsCo.HomotDeriv.famF_hasDerivAt ε G p q hG hK s hs0 g
      convert h using 1
      rw [hD, Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      have hsc : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
      simp only [adBas, bas]
      rw [← iteratedDeriv_succ, iter_scale hG, iter_scale hG]
      push_cast
      field_simp
    have hDc : Continuous D := by
      rw [hD]
      refine continuous_finsetSum _ fun x _ => continuous_finsetSum _ fun j _ => ?_
      exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt hder (hDc.intervalIntegrable _ _)
    have hint : ∫ s in (1:ℝ)..t, D s = ∑ x : Mode ε, ∑ j ∈ Finset.range (nMode ε + 1),
        adBas ε (Matrix.single x.1.2 x.1.1 1) (fun y => ∫ s in (1:ℝ)..t, scF G j s y) (q x j) g := by
      rw [hD, intervalIntegral.integral_finsetSum]
      · refine Finset.sum_congr rfl fun x _ => ?_
        rw [intervalIntegral.integral_finsetSum]
        · refine Finset.sum_congr rfl fun j _ => ?_
          rw [intervalIntegral.integral_add (((hc _).mul_const _).intervalIntegrable _ _)
            (((hc _).mul_const _).intervalIntegrable _ _),
            intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const,
            intervalIntegral.integral_ofReal, intervalIntegral.integral_ofReal]
          simp only [adBas, bas, (hI j).2, deriv_scF hG]
        · intro j _
          exact (((hc _).mul continuous_const).add ((hc _).mul continuous_const)).intervalIntegrable _ _
      · intro x _
        refine (continuous_finsetSum _ fun j _ => ?_).intervalIntegrable _ _
        exact ((hc _).mul continuous_const).add ((hc _).mul continuous_const)
    simp only [Pi.sub_apply, Pi.neg_apply, Finset.sum_apply]
    rw [← hint, hftc]
    ring
  rw [key]
  exact neg_mem (Submodule.sum_mem _ fun x _ => Submodule.sum_mem _ fun j _ => _root_.GlobalTheory.PsCo.Pc1.adBas_mem_adSpanM ε _ _ _ (hI j).1)

end GlobalTheory.PsCo.Pc1.Homot
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyFractionalIdealRealLatticeImage
section
open NumberField nonZeroDivisors MeasureTheory GlobalTheory.LipschitzTR GlobalTheory.IndefiniteRowSideFullHecke.TraceDualDifferent
open scoped FourierTransform RealInnerProductSpace

namespace GlobalTheory.LipschitzTR

noncomputable def toMixedTR (F : Type) [Field F] [NumberField F] (x : RSp F) :
    mixedEmbedding.mixedSpace F :=
  (fun w => x (InfinitePlace.embedding_of_isReal w.prop), fun _ => 0)

theorem continuous_toMixedTR (F : Type) [Field F] [NumberField F] :
    Continuous (toMixedTR F) := by
  refine Continuous.prodMk (continuous_pi fun w => ?_) continuous_const
  exact (PiLp.continuous_apply 2 _ _)

theorem toMixedTR_remb (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : F) :
    toMixedTR F (remb F a) = mixedEmbedding F a := by
  refine Prod.ext (funext fun w => ?_) (funext fun w => ?_)
  · simp [toMixedTR, mixedEmbedding.mixedEmbedding_apply_isReal]
  · exact absurd (IsTotallyReal.isReal w.1) (InfinitePlace.not_isReal_iff_isComplex.mpr w.2)

theorem discrete_latOf : ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F]
    (N : FractionalIdeal (𝓞 F)⁰ F), DiscreteTopology (latOf N) := by
  intro F _ _ _ N
  by_cases hN : N = 0
  · have : Subsingleton (latOf N) := by
      constructor
      rintro ⟨x, hx⟩ ⟨y, hy⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      subst hN
      rw [FractionalIdeal.mem_zero_iff] at ha hb
      subst ha; subst hb; rfl
    infer_instance
  · let I : (FractionalIdeal (𝓞 F)⁰ F)ˣ := Units.mk0 N hN
    have hmem : ∀ x : latOf N, toMixedTR F x ∈ mixedEmbedding.idealLattice F I := by
      rintro ⟨x, hx⟩
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      rw [mixedEmbedding.mem_idealLattice]
      exact ⟨a, ha, (toMixedTR_remb F a).symm⟩
    let h : latOf N → mixedEmbedding.idealLattice F I := fun x => ⟨toMixedTR F x, hmem x⟩
    refine DiscreteTopology.of_continuous_injective (f := h) ?_ ?_
    · exact Continuous.subtype_mk ((continuous_toMixedTR F).comp continuous_subtype_val) _
    · rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
      obtain ⟨a, ha, rfl⟩ := (mem_latOf N x).1 hx
      obtain ⟨b, hb, rfl⟩ := (mem_latOf N y).1 hy
      have : toMixedTR F (remb F a) = toMixedTR F (remb F b) := congrArg Subtype.val hxy
      rw [toMixedTR_remb, toMixedTR_remb] at this
      have hab := NumberField.mixedEmbedding_injective F this
      subst hab; rfl

end GlobalTheory.LipschitzTR
end

