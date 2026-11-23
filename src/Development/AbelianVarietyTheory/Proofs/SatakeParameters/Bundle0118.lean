module

public import Mathlib
public import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
public import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
public import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
public import Formalism.LocalToGlobal.Columns.HeckeSp
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0090
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InvolutionSphericalHeckeAnti
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.LocalToGlobal.Divisibility.ProjLemmas
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ContinuousInfiniteAdeleMap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ElementaryDivisorsInvHeckeElementSplitPlace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Mult
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitDivisors

section Algebra

variable {R : Type} [CommRing R] {n : ℕ} {ε : R} {A B C : Matrix (Fin n) (Fin n) R}

theorem conj_diag_inv (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R))
    (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R) (hd : ∀ i, d i * d' i = 1) :
    ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C)) = ε • (1 : Matrix (Fin n) (Fin n) R) := by
  have h3 : Matrix.diagonal d * Matrix.diagonal d' = 1 := by
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    exact congrArg _ (funext hd)
  calc ε • ((B * Matrix.diagonal d * C) * (B * Matrix.diagonal d' * C))
      = B * Matrix.diagonal d * (ε • (C * B)) * Matrix.diagonal d' * C := by
        simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]
    _ = ε • (B * (Matrix.diagonal d * Matrix.diagonal d') * C) := by
        rw [h2]; simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc, Matrix.one_mul]
    _ = _ := by rw [h3, Matrix.mul_one, h1]

theorem conj_diag_mulVec (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * A.mulVec y a) = fun a => ε * B.mulVec (fun i => d i * z i) a := by
  have h' : ε • y = ε • B.mulVec z := h
  have h3 : (fun i => d i * z i) = (Matrix.diagonal d).mulVec z := funext fun i => (Matrix.mulVec_diagonal d z i).symm
  show ε • A.mulVec y = ε • B.mulVec (fun i => d i * z i)
  rw [← Matrix.smul_mulVec, hA, Matrix.smul_mulVec, ← Matrix.mulVec_smul, h', Matrix.mulVec_smul, h3,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.smul_mulVec, ← Matrix.smul_mulVec, Matrix.mul_assoc _ C,
    ← Matrix.mul_smul, h2, Matrix.mul_smul, Matrix.mul_one]

theorem conj_diag_scale (hε : ε * ε = ε) (h2 : ε • (C * B) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d d' : Fin n → R)
    (x : R) (hd : ∀ i, d i * d' i = x) (hA : ε • A = ε • (B * Matrix.diagonal d * C)) {y z : Fin n → R}
    (h : (fun a => ε * y a) = fun a => ε * B.mulVec z a) :
    (fun a => ε * (x * y a)) = fun a => ε * A.mulVec (fun a => ε * B.mulVec (fun i => d' i * z i) a) a := by
  rw [conj_diag_mulVec h2 d hA (z := fun i => d' i * z i) (funext fun a => by rw [← mul_assoc, hε])]
  have h1 : (fun i => d i * (d' i * z i)) = x • z := funext fun i => by
    rw [← mul_assoc, hd, Pi.smul_apply, smul_eq_mul]
  rw [h1, Matrix.mulVec_smul]
  funext a
  rw [Pi.smul_apply, smul_eq_mul, mul_left_comm, congrFun h a, mul_left_comm]

theorem det_congr (hε : ε * ε = ε) (h : ε • A = ε • B) : ε * A.det = ε * B.det := by
  have h1 : ε * ε ^ Fintype.card (Fin n) = ε := by
    rw [← pow_succ']; exact IsIdempotentElem.pow_succ_eq _ hε
  have h2 := congrArg (fun M => ε * Matrix.det M) h
  simpa only [Matrix.det_smul, ← mul_assoc, h1] using h2

theorem conj_diag_det (hε : ε * ε = ε) (h1 : ε • (B * C) = ε • (1 : Matrix (Fin n) (Fin n) R)) (d : Fin n → R)
    (hA : ε • A = ε • (B * Matrix.diagonal d * C)) : ε * A.det = ε * ∏ i, d i := by
  have h2 := det_congr hε h1
  rw [Matrix.det_mul, Matrix.det_one] at h2
  rw [det_congr hε hA, Matrix.det_mul, Matrix.det_mul, Matrix.det_diagonal]
  linear_combination (∏ i, d i) * h2

end Algebra

theorem getD_label (n k i : ℕ) :
    (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0).getD i 0 = if i < k then 1 else 0 := by
  split_ifs with h
  · rw [List.getD_append _ _ _ _ (by simpa using h)]
    simp [List.getD_eq_getElem?_getD, h]
  · rw [List.getD_append_right _ _ _ _ (by simpa using h)]
    simp only [List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split_ifs <;> rfl

theorem dualLab_label (n k : ℕ) : dualLab (List.replicate k (1 : ℤ) ++ List.replicate (n - k) 0) = splitLab n k := by
  simp [dualLab, splitLab]

theorem prod_label {R : Type} [CommRing R] (x : R) {n k : ℕ} (h : k ≤ n) :
    (∏ i : Fin n, if i.1 < k then x else 1) = x ^ k := by
  rw [Finset.prod_ite, Finset.prod_const_one, mul_one, Finset.prod_const, Fin.card_filter_val_lt, min_eq_right h]

theorem int_mul_mem (D : D7) (u : 𝓞 D.host.E) {y : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E} (hy : y ∈ intAE D) :
    finPart D (incA D (u : D.host.E)) * y ∈ intAE D := by
  refine AddSubgroup.closure_induction (p := fun y _ => finPart D (incA D (u : D.host.E)) * y ∈ intAE D) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨b, hb, v, rfl⟩
    refine AddSubgroup.subset_closure ⟨b, hb, u * v, ?_⟩
    show ((1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) ⊗ₜ[D.host.F] (u : D.host.E)) * _ = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]; rfl
  · rw [mul_zero]; exact zero_mem _
  · intro x y _ _ h1 h2; rw [mul_add]; exact add_mem h1 h2
  · intro x _ h; rw [mul_neg]; exact neg_mem h

theorem one_mem_int (D : D7) : (1 : Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) ∈ intAE D :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, 1, rfl⟩


set_option maxHeartbeats 1000000 in
theorem exists_model {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D)
    (ϖ : 𝓞 D.host.E) (k : ℕ) (he : IsIdemAt e P) (h0 : (ϖ : D.host.E) ≠ 0) (hk : k ≤ V.rank) :
    ∃ α : GA D V, IsHeckeElt V e (ϖ : D.host.E) k α ∧
      DivAt V e (ϖ : D.host.E) (List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0) α := by
  obtain ⟨B, hB1, hB2⟩ := _root_.GlobalTheory.LatLocBasis.exists_loc_basis V P e he
  have hε : finPart D e * finPart D e = finPart D e := by rw [← RingHom.map_mul, he.1.1]
  obtain ⟨C, hC1, hC2⟩ := (_root_.GlobalTheory.LatIntFacts.int_facts V).2.2 (finPart D e) B hε fun y hy => (hB2 y hy).imp fun _ h => h.2
  obtain ⟨d, hd⟩ : ∃ d : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
    ∀ i, d i = if i.1 < k then finPart D (incA D (ϖ : D.host.E)) else 1 := ⟨_, fun _ => rfl⟩
  have hdc : ∀ i : Fin V.rank, finPart D (incA D ((ϖ : D.host.E) ^
      ((List.replicate k (1 : ℤ) ++ List.replicate (V.rank - k) 0).getD i.1 0))) = d i := fun i => by
    rw [getD_label, hd]
    split_ifs
    · rw [zpow_one]
    · rw [zpow_zero, RingHom.map_one, RingHom.map_one]
  obtain ⟨α, hs, hα⟩ := _root_.GlobalTheory.SplitLift.split_lift V e he.1 (B * Matrix.diagonal d * C) _
    (conj_diag_inv hC1 hC2 d (fun i => if i.1 < k then finPart D (incA D (ϖ : D.host.E)⁻¹) else 1) fun i => by
      rw [hd]
      split_ifs
      · rw [← RingHom.map_mul, ← RingHom.map_mul, mul_inv_cancel₀ h0, RingHom.map_one, RingHom.map_one]
      · exact mul_one _)
  have idem : ∀ y : Fin V.rank → Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E,
      (fun a => finPart D e * (finPart D e * y a)) = fun a => finPart D e * y a := fun y =>
    funext fun a => by rw [← mul_assoc, hε]
  refine ⟨α, ⟨((_root_.GlobalTheory.IdemSupport.supported_group_and_prime_idempotents V).2.2.1 P e (e + cA D e) (Or.inl ⟨he, rfl⟩)).2.2.1 α hs, hs, fun y hy => ?_,
    fun y hy => ?_, 1, 1, ?_, ?_, ?_, ?_⟩, ?_, B, hB1, hB2, fun y hy => ?_, fun z hz => ?_⟩
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    rw [conj_diag_mulVec hC2 d hα h]
    refine hB1 _ fun i => ?_
    rw [hd]
    split_ifs
    · exact int_mul_mem D ϖ (hz i)
    · rw [one_mul]; exact hz i
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨_, hB1 (fun i => (if i.1 < k then 1 else finPart D (incA D (ϖ : D.host.E))) * z i) fun i => ?_, ?_⟩
    · beta_reduce
      split_ifs
      · rw [one_mul]; exact hz i
      · exact int_mul_mem D ϖ (hz i)
    · refine conj_diag_scale hε hC2 d _ _ (fun i => ?_) hα h
      rw [hd]
      split_ifs
      · exact mul_one _
      · exact one_mul _
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [RingHom.map_one]; exact one_mem_int D
  · rw [mul_one, mul_one]
  · refine GlobalTheory.SplitScalar.adele_ext ?_ ?_
    · simp only [RingHom.map_mul, GlobalTheory.SplitScalar.infPart_splitIdem he.1, zero_mul]
    · have h1 := conj_diag_det hε hC1 d hα
      rw [funext hd, prod_label _ hk] at h1
      rw [mul_one, (finPart D).map_mul, (finPart D).map_mul, (finPart D).map_pow, (finPart D).map_det]
      exact h1
  · rw [List.length_append, List.length_replicate, List.length_replicate]; omega
  · obtain ⟨z, hz, h⟩ := hB2 y hy
    refine ⟨z, hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα h
  · refine ⟨_, hB1 z hz, ?_⟩
    simp only [hdc]
    exact conj_diag_mulVec hC2 d hα (idem _)

theorem divAt_inv_of_isHeckeElt : ∀ {D : D7} (V : HSp D) (P : HeightOneSpectrum (𝓞 D.host.E)) (e : Formalism.L2.Theta.AE D) (ϖ : 𝓞 D.host.E) (k : ℕ) (α : GA D V), IsIdemAt e P → ϖ ∈ P.asIdeal → ϖ ∉ P.asIdeal ^ 2 → k ≤ V.rank → IsHeckeElt V e (ϖ : D.host.E) k α → DivAt V e (ϖ : D.host.E) (splitLab V.rank k) α⁻¹ := by
  intro D V P e ϖ k α he h1 h2 hk hα
  have h0 : (ϖ : D.host.E) ≠ 0 := fun h => h2 (by
    rw [show ϖ = 0 from Subtype.ext h]; exact zero_mem _)
  obtain ⟨α₀, hH, hD⟩ := exists_model V P e ϖ k he h0 hk
  obtain ⟨a, ha, b, hb, rfl⟩ := (((_root_.GlobalTheory.SplitPlace.split_local V P e he).2.2 ϖ h1 h2).2 k α₀ hH).2 ϖ α h1 h2 hα
  rw [← dualLab_label]
  exact (_root_.GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 ((_root_.GlobalTheory.DivDual.divAt_inv_and_mul V e _ _ _ he.1.1 h0 hD).2 a ha.1 b hb.1)).1

end GlobalTheory.SplitDivisors
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLevelVectorGoodTypeStableSubspace
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Hk3.Meet

theorem sum_char_conj_mul {K G : Type} [Field K] [CharZero K] [Group G] [Fintype G] {χ : G → K}
    (h : IsAbsIrrChar χ) (y s : G) :
    (∑ g : G, χ (g * y * g⁻¹ * s)) * χ 1 = (Fintype.card G : K) * χ y * χ s := by
  classical
  have hconj := h.conj
  obtain ⟨n, ρ, hi, hρ⟩ := h
  let j := algebraMap K (AlgebraicClosure K)
  have hj : Function.Injective j := j.injective
  set T : Module.End (AlgebraicClosure K) (Fin n → AlgebraicClosure K) := ∑ g : G, ρ (g * y * g⁻¹) with hTdef
  have hT : ∀ a v, T (ρ a v) = ρ a (T v) := by
    intro a v
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hTdef, LinearMap.sum_apply, map_sum]
    rw [← Equiv.sum_comp (Equiv.mulLeft a)]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  obtain ⟨c, hc⟩ := schur_scalar ρ T hT
  have h1 : ∀ u : G, ∑ g : G, ρ.character (g * y * g⁻¹ * u) = c * ρ.character u := by
    intro u
    have : LinearMap.trace _ _ (T * ρ u) = c * ρ.character u := by
      rw [hc]; simp [Representation.character, Module.End.mul_eq_comp]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← this, hTdef, Finset.sum_mul, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [Representation.character, map_mul]
  have h2 : j ((Fintype.card G : K) * χ y) = c * j (χ 1) := by
    have := h1 1
    simp only [mul_one, hρ, hconj] at this
    rw [← this]
    simp [j]
  have h3 : j (∑ g : G, χ (g * y * g⁻¹ * s)) = c * j (χ s) := by
    have := h1 s
    simp only [hρ] at this
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, this]
  apply hj
  rw [map_mul, h3, map_mul _ _ (χ s), h2]
  ring

section Op

variable {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
  (σ : K →+* ℂ) (ρ : Representation ℂ G W)

theorem class_sum_apply {χ : G → K} (h : IsAbsIrrChar χ) (h1 : χ 1 ≠ 0) (y : G) (u : W) :
    ∑ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      σ ((Fintype.card G : K) * χ y / χ 1) • ∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u := by
  classical
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have e1 : ∀ g : G, ρ (g * y * g⁻¹) (∑ r : G, σ ((chiIdem χ).coeff r) • ρ r u) =
      ∑ s : G, σ ((chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s)) • ρ s u := by
    intro g
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, ← Equiv.sum_comp (Equiv.mulLeft (g * y * g⁻¹)⁻¹)]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [map_smul, ← Module.End.mul_apply, ← map_mul]
    simp [mul_assoc]
  simp only [e1]
  rw [Finset.sum_comm, Finset.smul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← Finset.sum_smul, ← map_sum, smul_smul, ← map_mul]
  congr 2
  have e2 : ∀ g : G, (chiIdem χ).coeff ((g * y * g⁻¹)⁻¹ * s) =
      χ 1 / (Fintype.card G : K) * χ (g * y * g⁻¹ * s⁻¹) := by
    intro g
    rw [coeff_chiIdem]
    congr 1
    have := h.conj s (s⁻¹ * (g * y * g⁻¹))
    rw [_root_.mul_inv_rev, inv_inv, ← this]
    congr 1
    group
  simp only [e2]
  rw [← Finset.mul_sum, coeff_chiIdem]
  have := sum_char_conj_mul h y s⁻¹
  field_simp
  linear_combination this

end Op

def lvlCoef {K G : Type} [Field K] [Group G] (P : Subgroup G) (ψ : P →* Kˣ) (h : P) : K :=
  (Nat.card P : K)⁻¹ * ((ψ h⁻¹ : Kˣ) : K)


open Classical in
theorem coeff_chiIdem_mul_lvlIdem {K G : Type} [Field K] [Group G] [Fintype G] (χ : G → K) (P : Subgroup G)
    (ψ : P →* Kˣ) (t : G) :
    (chiIdem χ * lvlIdem P ψ).coeff t =
      χ 1 / (Fintype.card G : K) * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) := by
  classical
  unfold lvlIdem
  rw [Finset.mul_sum, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [MonoidAlgebra.coeff_mul_single_apply, coeff_chiIdem]
  simp only [lvlCoef, _root_.mul_inv_rev, inv_inv]
  ring

end GlobalTheory.Hk3.Meet

namespace GlobalTheory.Hk3


open GlobalTheory.Hk3.Meet in
theorem exists_level_vector : ∀ {K G W : Type} [Field K] [CharZero K] [Group G] [Fintype G] [AddCommGroup W] [Module ℂ W]
    [FiniteDimensional ℂ W] (σ : K →+* ℂ) (X : Finset (G → K)) (P : Subgroup G) (ψ : P →* Kˣ) (ρ : Representation ℂ G W)
    (U : Submodule ℂ W), (∀ χ ∈ X, IsAbsIrrChar χ) → (∀ χ ∈ X, chiIdem χ * lvlIdem P ψ ≠ 0) → (∀ g, U.map (ρ g) ≤ U) →
    U ≠ ⊥ → (∀ u ∈ U, ∑ g, σ ((idemOf X).coeff g) • ρ g u = u) →
    ∃ u ∈ U, u ≠ 0 ∧ ∀ p : P, ρ p u = σ (ψ p : K) • u := by
  intro K G W _ _ _ _ _ _ _ σ X P ψ ρ U hX hne hst hbot hid
  classical
  have hmem : ∀ g, ∀ u ∈ U, ρ g u ∈ U := fun g u hu => hst g (Submodule.mem_map_of_mem hu)

  obtain ⟨u₀, hu₀, hu₀ne⟩ := (Submodule.ne_bot_iff U).1 hbot
  have hsplit : ∑ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ = u₀ := by
    refine Eq.trans ?_ (hid u₀ hu₀)
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    have e : (idemOf X).coeff g = ∑ φ ∈ X, (chiIdem φ).coeff g := by
      unfold idemOf
      simp
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, e]
  obtain ⟨χ, hχ, hw⟩ : ∃ χ ∈ X, ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hu₀ne (by rw [← hsplit]; exact Finset.sum_eq_zero hcon)
  set w₀ := ∑ g, σ ((chiIdem χ).coeff g) • ρ g u₀ with hw₀
  have hw₀U : w₀ ∈ U := Submodule.sum_mem _ fun g _ => Submodule.smul_mem _ _ (hmem g _ hu₀)

  obtain ⟨t, ht⟩ : ∃ t, (chiIdem χ * lvlIdem P ψ).coeff t ≠ 0 := by
    by_contra hcon
    push_neg at hcon
    exact hne χ hχ (by
      apply MonoidAlgebra.ext
      ext t
      simpa using hcon t)
  rw [coeff_chiIdem_mul_lvlIdem] at ht
  have h1 : χ 1 ≠ 0 := fun e => ht (by simp [e])
  have hc : ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹) ≠ 0 := right_ne_zero_of_mul ht
  have hN : ((Fintype.card G : ℕ) : K) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero

  set L : W → W := fun w => ∑ h : P, σ (lvlCoef P ψ h) • ρ (h : G) w with hL
  have hLU : ∀ w ∈ U, L w ∈ U := fun w hw => Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (hmem _ _ hw)
  have hLe : ∀ (p : P) w, ρ p (L w) = σ (ψ p : K) • L w := by
    intro p w
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hL, map_sum, map_smul, Finset.smul_sum]
    refine (Equiv.sum_comp (Equiv.mulLeft p⁻¹) _).symm.trans (Finset.sum_congr rfl fun h _ => ?_)
    simp only [Equiv.coe_mulLeft]
    have e1 : lvlCoef P ψ (p⁻¹ * h) = (ψ p : K) * lvlCoef P ψ h := by
      simp only [lvlCoef, _root_.mul_inv_rev, inv_inv, map_mul, Units.val_mul]
      ring
    have e2 : ρ (p : G) (ρ ((p⁻¹ * h : P) : G) w) = ρ (h : G) w := by
      rw [← Module.End.mul_apply, ← map_mul]
      simp
    rw [e1, e2, map_mul, mul_smul]
  by_contra hno
  push_neg at hno
  have hL0 : ∀ w ∈ U, L w = 0 := by
    intro w hw
    by_contra hLw
    obtain ⟨p, hp⟩ := hno _ (hLU w hw) hLw
    exact hp (hLe p w)
  have hz : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) = 0 :=
    Finset.sum_eq_zero fun g _ => by rw [hL0 _ (hmem _ _ hw₀U), map_zero]
  have hz2 : ∑ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
      σ ((Fintype.card G : K) / χ 1 * ∑ h : P, lvlCoef P ψ h * χ ((h : G) * t⁻¹)) • w₀ := by
    have e : ∀ g : G, ρ g (L (ρ (t⁻¹ * g⁻¹) w₀)) =
        ∑ h : P, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ := by
      intro g
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [hL, map_sum, map_smul]
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [← Module.End.mul_apply (ρ (h : G)), ← map_mul, ← Module.End.mul_apply (ρ g), ← map_mul]
      simp [mul_assoc]
    simp only [e]
    rw [Finset.sum_comm]
    have e2 : ∀ h : P, ∑ g : G, σ (lvlCoef P ψ h) • ρ (g * ((h : G) * t⁻¹) * g⁻¹) w₀ =
        σ (lvlCoef P ψ h * ((Fintype.card G : K) * χ ((h : G) * t⁻¹) / χ 1)) • w₀ := by
      intro h
      rw [← Finset.smul_sum, map_mul, mul_smul]
      congr 1
      exact class_sum_apply σ ρ (hX χ hχ) h1 _ u₀
    simp only [e2]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_smul, ← map_sum, Finset.mul_sum]
    congr 2
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  rw [hz2] at hz
  rcases smul_eq_zero.1 hz with h0 | h0
  · exact (mul_ne_zero (div_ne_zero hN h1) hc) ((map_eq_zero σ).1 h0)
  · exact hw h0

end GlobalTheory.Hk3
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeisenbergOperatorFixThetaDatumAwaySplitPlaces
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

variable {D : D7}

theorem symplO_half_off (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x) (hu : ∀ i j, cA D a * u i j = 0) :
    symplO S T x u = 0 := by
  have h0 : cA D a • u = 0 := Matrix.ext fun i j => by
    show cA D a * u i j = 0
    exact hu i j
  rw [← (GlobalTheory.SplitScalar.isHalf_iff _ _).1 hx, GlobalTheory.SplitScalar.symplO_smul, h0, GlobalTheory.SplitScalar.symplO_zero_right]

theorem heisO_comm_off (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {a : AE D} {x u : WO S T} (hx : IsHalf a x)
    (hu : ∀ i j, cA D a * u i j = 0) (g : WO S T → ℂ) :
    heisO ψ S T u (heisO ψ S T x g) = heisO ψ S T x (heisO ψ S T u g) := by
  rw [GlobalTheory.SplitScalar.heisO_comm, GlobalTheory.SplitScalar.symplO_skew, symplO_half_off S T hx hu, neg_zero,
    AddChar.map_zero_eq_one, one_smul]

theorem heisO_fix_thetaAt_off : ∀ {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (e : AE D) (Λ : AddSubgroup (WO S T))
    (c : ℂ) (f₀ Φ f : WO S T → ℂ), IsThetaAt ψ (symplO S T) (heisO ψ S T) e Λ c f₀ Φ f → ∀ u : WO S T,
    (∀ i j, e * u i j = 0 ∧ cA D e * u i j = 0) → heisO ψ S T u f₀ = f₀ → heisO ψ S T u f = f := by
  intro D ψ S T e Λ c f₀ Φ f h u hu hf₀
  obtain ⟨⟨Tm, hTm⟩, hall⟩ := h
  have hm : IsPlaceModel ψ (symplO S T) (heisO ψ S T) e Λ c f₀ ((GlobalTheory.SplitScalar.heisL ψ S T u).comp Tm) :=
    { trans := fun Φ' hΦ' x hx => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.trans Φ' hΦ' x hx, heisO_comm_off ψ S T hx (fun i j => (hu i j).2)]
      modul := fun Φ' hΦ' y hy => by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.modul Φ' hΦ' y hy,
          heisO_comm_off ψ S T hy (fun i j => by rw [GlobalTheory.DualPairCheck.cA_cA]; exact (hu i j).1)]
      vac := by
        simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply]
        rw [hTm.vac, hf₀] }
  have h1 := hall _ hm
  have h2 := hall _ hTm
  simp only [LinearMap.comp_apply, GlobalTheory.SplitScalar.heisL_apply] at h1
  rw [h2] at h1 ⊢
  exact h1.symm

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IdeleMapOfAlgebraMaximalRealSubfieldInjective
section
open NumberField HeckeCharacterZeroLocus.ThmBIn GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele GlobalTheory.UnitaryHeckeBaseChange

namespace GlobalTheory.IdeleMapInjective

theorem adeleMap_injective {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} (h : IsCMExt F E σ) : Function.Injective (adeleMap F E) := by
  intro a b hab
  rw [← toAdele_algebraMap, ← toAdele_algebraMap] at hab
  exact Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := AF F) (B := E)
    (algebraMap F E).injective ((bijective_toAdele h).1 hab)

theorem ideleMap_injective (E : Type) [Field E] [NumberField E] [IsCMField E] :
    Function.Injective (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E) := by
  have h : IsCMExt (maximalRealSubfield E) E (IsCMField.complexConj E).toAlgHom :=
    ⟨inferInstance, inferInstance, Algebra.IsQuadraticExtension.finrank_eq_two _ _,
      fun τ x => IsCMField.complexEmbedding_complexConj E τ x⟩
  intro a b hab
  exact Units.ext (adeleMap_injective h (congrArg Units.val hab))

end GlobalTheory.IdeleMapInjective
end

