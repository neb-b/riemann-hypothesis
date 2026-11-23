module

public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0004
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0143

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DecompA
section
noncomputable section

open Matrix
open scoped ComplexOrder

namespace PositivityTheory.Rg.Sw.Glob.DecH

variable {n : ℕ}

theorem jj_mul_jj : JJ n * JJ n = -1 := by
  unfold JJ
  rw [fromBlocks_multiply]
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add, neg_zero]
  rw [← fromBlocks_one, fromBlocks_neg]
  simp

theorem inG_dual {g : M2 n} (h : InG g) : g * JJ n * gᴴ = JJ n := by
  have h' : gᴴ * (JJ n * g) = JJ n := by
    rw [← Matrix.mul_assoc]
    exact h
  have hK : (-(JJ n * gᴴ * JJ n)) * g = 1 := by
    simp only [Matrix.neg_mul, Matrix.mul_assoc, h', jj_mul_jj, neg_neg]
  have hK' : g * (-(JJ n * gᴴ * JJ n)) = 1 := mul_eq_one_comm.mp hK
  calc g * JJ n * gᴴ = g * JJ n * gᴴ * (-(JJ n * JJ n)) := by
        rw [jj_mul_jj, neg_neg, Matrix.mul_one]
    _ = (g * -(JJ n * gᴴ * JJ n)) * JJ n := by
        simp only [Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_assoc]
    _ = JJ n := by rw [hK', Matrix.one_mul]

theorem inG_blocks {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    Aᴴ * C = Cᴴ * A ∧ Aᴴ * D - Cᴴ * B = 1 ∧ Bᴴ * D = Dᴴ * B := by
  unfold InG JJ at h
  rw [fromBlocks_conjTranspose, fromBlocks_multiply, fromBlocks_multiply, fromBlocks_inj] at h
  obtain ⟨h1, h2, -, h4⟩ := h
  simp only [Matrix.mul_zero, Matrix.zero_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_neg,
    Matrix.neg_mul, add_zero, zero_add] at h1 h2 h4
  refine ⟨?_, ?_, ?_⟩
  · rw [← sub_eq_zero, ← h1]
    abel
  · rw [← h2]
    abel
  · rw [← sub_eq_zero, ← h4]
    abel

theorem inG_blocks_dual {A B C D : Matrix (Fin n) (Fin n) ℂ} (h : InG (fromBlocks A B C D)) :
    A * Bᴴ = B * Aᴴ ∧ A * Dᴴ - B * Cᴴ = 1 ∧ C * Bᴴ - D * Aᴴ = -1 ∧ C * Dᴴ = D * Cᴴ := by
  have h' : InG (fromBlocks Aᴴ Cᴴ Bᴴ Dᴴ) := by
    have hd := inG_dual h
    unfold InG
    rw [← fromBlocks_conjTranspose, conjTranspose_conjTranspose]
    exact hd
  obtain ⟨h1, h2, h3⟩ := inG_blocks h'
  simp only [conjTranspose_conjTranspose] at h1 h2 h3
  refine ⟨h1, h2, ?_, h3⟩
  have h4 := congrArg conjTranspose h2
  simp only [conjTranspose_sub, conjTranspose_mul, conjTranspose_conjTranspose,
    conjTranspose_one] at h4
  rw [← neg_sub, h4]

end PositivityTheory.Rg.Sw.Glob.DecH
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.DenseB
section
noncomputable section

open Matrix Topology

namespace PositivityTheory.Rg.Sw.Glob.DenseP

variable {n : ℕ}

theorem inG_nUh {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : InG (nU b) := by
  simp only [InG, nU, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, hb]
  simp

theorem inG_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) : InG (fromBlocks A 0 0 (A⁻¹)ᴴ) := by
  have h1 : Aᴴ * (A⁻¹)ᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.nonsing_inv_mul _ hA, Matrix.conjTranspose_one]
  have h2 : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ hA
  simp only [InG, JJ, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply, Matrix.conjTranspose_conjTranspose,
    Matrix.conjTranspose_zero]
  simp [h1, h2]

def hpart (A : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ := (1 / 2 : ℂ) • (A + Aᴴ)

theorem hpart_herm (A : Matrix (Fin n) (Fin n) ℂ) : (hpart A)ᴴ = hpart A := by
  simp only [hpart, Matrix.conjTranspose_smul, Matrix.conjTranspose_add, Matrix.conjTranspose_conjTranspose]
  rw [add_comm]
  congr 1
  simp

theorem hpart_of_herm {b : Matrix (Fin n) (Fin n) ℂ} (hb : bᴴ = b) : hpart b = b := by
  rw [hpart, hb, ← two_smul ℂ b, smul_smul]; norm_num

def nuE (A : Matrix (Fin n) (Fin n) ℂ) : GR n := mkGR (nU (hpart A)) (inG_nUh (hpart_herm A))

theorem continuous_hpart : Continuous (hpart (n := n)) := by
  have h : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A + Aᴴ :=
    (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).add (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)).matrix_conjTranspose
  exact h.const_smul (1 / 2 : ℂ)

theorem nU_mul_neg (b : Matrix (Fin n) (Fin n) ℂ) : nU b * nU (-b) = 1 := by
  simp [nU, Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one]

theorem continuous_nU : Continuous (nU (n := n)) :=
  Continuous.matrix_fromBlocks continuous_const continuous_id continuous_const continuous_const

theorem continuous_nuE : Continuous (nuE (n := n)) := by
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · show Continuous fun A => nU (hpart A)
    exact continuous_nU.comp continuous_hpart
  · show Continuous fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹
    have e : (fun A : Matrix (Fin n) (Fin n) ℂ => (nU (hpart A))⁻¹) = fun A => nU (-hpart A) := by
      funext A
      exact Matrix.inv_eq_right_inv (nU_mul_neg _)
    rw [e]
    exact continuous_nU.comp continuous_hpart.neg


open Classical in
def mlE (A : Matrix (Fin n) (Fin n) ℂ) : GR n :=
  if h : IsUnit A.det then mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) else 1

theorem mlE_of {A : Matrix (Fin n) (Fin n) ℂ} (h : IsUnit A.det) :
    mlE A = mkGR (fromBlocks A 0 0 (A⁻¹)ᴴ) (inG_mL h) := by
  unfold mlE; exact dif_pos h

theorem isOpen_unitDet : IsOpen {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} := by
  have : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} = (fun A : Matrix (Fin n) (Fin n) ℂ => A.det) ⁻¹' {z | z ≠ 0} :=
    Set.ext fun A => isUnit_iff_ne_zero
  rw [this]
  exact isOpen_ne.preimage (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ)))

theorem continuousOn_inv_mat : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) {A | IsUnit A.det} := by
  have e : (fun A : Matrix (Fin n) (Fin n) ℂ => A⁻¹) = fun A => (A.det)⁻¹ • A.adjugate := by
    funext A; rw [Matrix.inv_def, Ring.inverse_eq_inv']
  rw [e]
  have h1 : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ => (A.det)⁻¹) {A | IsUnit A.det} :=
    ContinuousOn.inv₀ (Continuous.matrix_det (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))).continuousOn
      fun A hA => isUnit_iff_ne_zero.1 hA
  have h2 : Continuous fun A : Matrix (Fin n) (Fin n) ℂ => A.adjugate :=
    Continuous.matrix_adjugate (continuous_id (X := Matrix (Fin n) (Fin n) ℂ))
  exact h1.smul h2.continuousOn

theorem inv_mL {A : Matrix (Fin n) (Fin n) ℂ} (hA : IsUnit A.det) :
    (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹ = fromBlocks A⁻¹ 0 0 Aᴴ := by
  refine Matrix.inv_eq_right_inv ?_
  have h1 : (A⁻¹)ᴴ * Aᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hA, Matrix.conjTranspose_one]
  rw [Matrix.fromBlocks_multiply]
  simp [Matrix.mul_nonsing_inv _ hA, h1, ← Matrix.fromBlocks_one]

theorem continuousOn_mlE : ContinuousOn (mlE (n := n)) {A | IsUnit A.det} := by
  have hind : Topology.IsInducing (fun g : GR n => Units.embedProduct _ (g : GL (Fin n ⊕ Fin n) ℂ)) :=
    Units.isEmbedding_embedProduct.isInducing.comp Topology.IsInducing.subtypeVal
  rw [hind.continuousOn_iff]
  have hi := continuousOn_inv_mat (n := n)
  have hc : ContinuousOn (fun A : Matrix (Fin n) (Fin n) ℂ =>
      (fromBlocks A 0 0 (A⁻¹)ᴴ, MulOpposite.op (fromBlocks A⁻¹ 0 0 Aᴴ))) {A | IsUnit A.det} := by
    rw [continuousOn_iff_continuous_restrict]
    have hi' : Continuous fun A : {A : Matrix (Fin n) (Fin n) ℂ | IsUnit A.det} => A.1⁻¹ := hi.restrict
    refine Continuous.prodMk ?_ ?_
    · exact Continuous.matrix_fromBlocks continuous_subtype_val continuous_const continuous_const
        hi'.matrix_conjTranspose
    · exact MulOpposite.continuous_op.comp (Continuous.matrix_fromBlocks hi' continuous_const continuous_const
        continuous_subtype_val.matrix_conjTranspose)
  refine ContinuousOn.congr hc fun A hA => ?_
  simp only [Function.comp_apply, mlE_of hA]
  show ((fromBlocks A 0 0 (A⁻¹)ᴴ), MulOpposite.op (fromBlocks A 0 0 (A⁻¹)ᴴ)⁻¹) = _
  rw [inv_mL hA]

theorem nuE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ) :
    nuE A ∈ closure (Set.range fun e : Matrix (Fin n) (Fin n) K => nuE (e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have h1 : nuE A ∈ nuE '' closure (Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ) := by
    rw [hd.closure_range]; exact ⟨A, trivial, rfl⟩
  have h2 := image_closure_subset_closure_image continuous_nuE h1
  rwa [← Set.range_comp] at h2

theorem mlE_mem_closure {K : Type} [Field K] (τ : K →+* ℂ) (hτ : DenseRange τ) (A : Matrix (Fin n) (Fin n) ℂ)
    (hA : IsUnit A.det) :
    mlE A ∈ closure (mlE '' ({A | IsUnit A.det} ∩ Set.range fun e : Matrix (Fin n) (Fin n) K => e.map τ)) := by
  have hd : DenseRange (fun e : Matrix (Fin n) (Fin n) K => e.map τ) :=
    DenseRange.piMap fun _ => DenseRange.piMap fun _ => hτ
  have hc : ContinuousAt (mlE (n := n)) A := (continuousOn_mlE (n := n)).continuousAt (isOpen_unitDet.mem_nhds hA)
  rw [mem_closure_iff_nhds]
  intro t ht
  have h1 : mlE ⁻¹' t ∩ {A | IsUnit A.det} ∈ 𝓝 A := Filter.inter_mem (hc ht) (isOpen_unitDet.mem_nhds hA)
  obtain ⟨U, hU, hUo, hAU⟩ := mem_nhds_iff.1 h1
  obtain ⟨e, he⟩ := hd.exists_mem_open hUo ⟨A, hAU⟩
  exact ⟨mlE (e.map τ), (hU he).1, e.map τ, ⟨(hU he).2, e, rfl⟩, rfl⟩

end PositivityTheory.Rg.Sw.Glob.DenseP
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.EvXTemperate
section
noncomputable section

open MvPolynomial

namespace PositivityTheory.Rg.Sw.Glob

theorem evX_temperate {m n : ℕ} (P : PX m n) :
    Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX P u) := by
  have hcoord : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => u a i) := by
    intro a i
    exact ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ))).hasTemperateGrowth
  have hconj : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => star (u a i)) := by
    intro a i
    have h := (Complex.conjCLE.toContinuousLinearMap.comp
      ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
        (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
    convert h using 1
    funext u
    simp [Complex.conjCLE_apply]
  refine MvPolynomial.induction_on
    (motive := fun Q : PX m n =>
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => evX Q u)) P ?_ ?_ ?_
  · intro a
    convert Function.HasTemperateGrowth.const (E := Fin m → Fin n → ℂ) a using 1
    funext u
    simp [evX]
  · intro p q hp hq
    convert hp.add hq using 1
    funext u
    simp [evX]
  · intro p k hp
    obtain ⟨a, i, b⟩ := k
    cases b
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, false)) u) =
          (fun u => evX p u) * (fun u => u a i) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hcoord a i)
    · have e : (fun u : Fin m → Fin n → ℂ => evX (p * X (a, i, true)) u) =
          (fun u => evX p u) * (fun u => star (u a i)) := by
        funext u
        simp [evX]
      rw [e]
      exact hp.mul (hconj a i)

private theorem hasTemperateGrowth_const_mul_sum_norm_sq {m n : ℕ} (c : ℝ) :
    Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
  have hre : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).re) := fun a i =>
    (Complex.reCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have him : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => (u a i).im) := fun a i =>
    (Complex.imCLM.comp ((ContinuousLinearMap.proj i : (Fin n → ℂ) →L[ℝ] ℂ).comp
      (ContinuousLinearMap.proj a : (Fin m → Fin n → ℂ) →L[ℝ] (Fin n → ℂ)))).hasTemperateGrowth
  have hsq : ∀ (a : Fin m) (i : Fin n),
      Function.HasTemperateGrowth (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) := by
    intro a i
    have e : (fun u : Fin m → Fin n → ℂ => ‖u a i‖ ^ 2) =
        fun u : Fin m → Fin n → ℂ => (u a i).re * (u a i).re + (u a i).im * (u a i).im := by
      funext u
      rw [Complex.sq_norm, Complex.normSq_apply]
    rw [e]
    exact ((hre a i).mul (hre a i)).add ((him a i).mul (him a i))
  have hin : ∀ a : Fin m, Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ i : Fin n, ‖u a i‖ ^ 2) := fun a =>
    Function.HasTemperateGrowth.sum fun i _ => hsq a i
  have hsum : Function.HasTemperateGrowth
      (fun u : Fin m → Fin n → ℂ => ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) :=
    Function.HasTemperateGrowth.sum fun a _ => hin a
  exact (Function.HasTemperateGrowth.const c).mul hsum

private theorem norm_iteratedFDeriv_cexp_neg_eq_exp_neg (i : ℕ) (t : ℝ) :
    ‖iteratedFDeriv ℝ i (fun s : ℝ => Complex.exp (-(s : ℂ))) t‖ = Real.exp (-t) := by
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hit : iteratedDeriv i (fun s : ℝ => Complex.exp (-(s : ℂ))) =
      fun s : ℝ => (-1 : ℂ) ^ i * Complex.exp (-(s : ℂ)) := by
    induction i with
    | zero =>
      funext s
      simp
    | succ i ih =>
      rw [iteratedDeriv_succ, ih]
      funext s
      have h0 : HasDerivAt (fun s : ℝ => (s : ℂ)) 1 s := by
        simpa using (hasDerivAt_id s).ofReal_comp
      have hd : HasDerivAt (fun s : ℝ => -(s : ℂ)) (-1) s := h0.neg
      have he := (hd.cexp).const_mul ((-1 : ℂ) ^ i)
      rw [he.deriv]
      ring
  rw [hit]
  simp [Complex.norm_exp]

private theorem exists_bound_one_add_pow_mul_exp_neg_sq (c : ℝ) (hc : 0 < c) (j : ℕ) :
    ∃ M : ℝ, ∀ r : ℝ, 0 ≤ r → (1 + r) ^ j * Real.exp (-(c * r ^ 2)) ≤ M := by
  refine ⟨2 ^ j * (1 + j.factorial / c ^ j), fun r hr => ?_⟩
  have hy : 0 ≤ c * r ^ 2 := by positivity
  have hexp := Real.pow_div_factorial_le_exp (c * r ^ 2) hy j
  have hE : 0 < Real.exp (c * r ^ 2) := Real.exp_pos _
  have hcj : 0 < c ^ j := pow_pos hc j
  have h2j : (0 : ℝ) < 2 ^ j := pow_pos two_pos j
  have hr2j : 0 ≤ (r ^ 2) ^ j := by positivity
  have h1 : (1 + r) ^ j ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by
    rcases le_total r 1 with h | h
    · calc (1 + r) ^ j ≤ 2 ^ j := pow_le_pow_left₀ (by linarith) (by linarith) j
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
    · calc (1 + r) ^ j ≤ (2 * r ^ 2) ^ j := pow_le_pow_left₀ (by linarith) (by nlinarith) j
        _ = 2 ^ j * (r ^ 2) ^ j := mul_pow _ _ _
        _ ≤ 2 ^ j * (1 + (r ^ 2) ^ j) := by nlinarith
  have h2 : (r ^ 2) ^ j * Real.exp (-(c * r ^ 2)) ≤ j.factorial / c ^ j := by
    rw [mul_pow, div_le_iff₀ (by positivity)] at hexp
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_div_iff₀ hE hcj]
    nlinarith
  have h3 : Real.exp (-(c * r ^ 2)) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    linarith
  calc (1 + r) ^ j * Real.exp (-(c * r ^ 2))
      ≤ 2 ^ j * (1 + (r ^ 2) ^ j) * Real.exp (-(c * r ^ 2)) := by gcongr
    _ = 2 ^ j * (Real.exp (-(c * r ^ 2)) + (r ^ 2) ^ j * Real.exp (-(c * r ^ 2))) := by ring
    _ ≤ 2 ^ j * (1 + j.factorial / c ^ j) :=
        mul_le_mul_of_nonneg_left (add_le_add h3 h2) h2j.le

theorem gs_sch {m n : ℕ} (c : ℝ) (hc : 0 < c) :
    ∃ S : SchwartzMap (Fin m → Fin n → ℂ) ℂ, ∀ u, S u = gs c u := by
  have hqT := hasTemperateGrowth_const_mul_sum_norm_sq (m := m) (n := n) c
  have hhC : ContDiff ℝ (⊤ : ℕ∞) (fun s : ℝ => Complex.exp (-(s : ℂ))) :=
    Complex.contDiff_exp.comp (Complex.ofRealCLM.contDiff.neg)
  have hgs : (gs c : (Fin m → Fin n → ℂ) → ℂ) =
      (fun s : ℝ => Complex.exp (-(s : ℂ))) ∘
        (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
    funext u
    simp [gs]
  have hlow : ∀ u : Fin m → Fin n → ℂ, ‖u‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by
    intro u
    have hS0 : 0 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 := by positivity
    have hb : ‖u‖ ≤ Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) := by
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun a => ?_
      refine (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun i => ?_
      have h1 : ‖u a i‖ ^ 2 ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
        calc ‖u a i‖ ^ 2 ≤ ∑ i' : Fin n, ‖u a i'‖ ^ 2 :=
              Finset.single_le_sum (f := fun i' => ‖u a i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ i)
          _ ≤ ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2 :=
              Finset.single_le_sum (f := fun a' => ∑ i' : Fin n, ‖u a' i'‖ ^ 2)
                (fun _ _ => by positivity) (Finset.mem_univ a)
      have h2 := Real.abs_le_sqrt h1
      rwa [abs_of_nonneg (norm_nonneg _)] at h2
    calc ‖u‖ ^ 2 ≤ (Real.sqrt (∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hb 2
      _ = _ := Real.sq_sqrt hS0
  refine ⟨⟨gs c, ?_, ?_⟩, fun u => rfl⟩
  · rw [hgs]
    exact hhC.comp hqT.1
  · intro k N
    obtain ⟨K, C, hC0, hC⟩ := hqT.norm_iteratedFDeriv_le_uniform N
    obtain ⟨M, hM⟩ := exists_bound_one_add_pow_mul_exp_neg_sq c hc (k + K * N)
    refine ⟨N.factorial * (C + 1) ^ N * M, fun u => ?_⟩
    have hu0 := norm_nonneg u
    have hD1 : 1 ≤ (C + 1) * (1 + ‖u‖) ^ K :=
      one_le_mul_of_one_le_of_one_le (by linarith) (one_le_pow₀ (by linarith))
    have hD : ∀ i : ℕ, 1 ≤ i → i ≤ N →
        ‖iteratedFDeriv ℝ i
          (fun u : Fin m → Fin n → ℂ => c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2) u‖ ≤
          ((C + 1) * (1 + ‖u‖) ^ K) ^ i := by
      intro i hi1 hiN
      calc _ ≤ C * (1 + ‖u‖) ^ K := hC i hiN u
        _ ≤ (C + 1) * (1 + ‖u‖) ^ K := by gcongr; linarith
        _ ≤ _ := le_self_pow₀ hD1 (by omega)
    have key := norm_iteratedFDeriv_comp_le (𝕜 := ℝ) (n := N) hhC hqT.1
      (by exact_mod_cast le_top) u
      (C := Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)))
      (fun i _ => (norm_iteratedFDeriv_cexp_neg_eq_exp_neg i _).le) hD
    have hexp_le : Real.exp (-(c * ∑ a : Fin m, ∑ i : Fin n, ‖u a i‖ ^ 2)) ≤
        Real.exp (-(c * ‖u‖ ^ 2)) := by
      apply Real.exp_le_exp.2
      have := mul_le_mul_of_nonneg_left (hlow u) hc.le
      linarith
    have hpow : ‖u‖ ^ k ≤ (1 + ‖u‖) ^ k := pow_le_pow_left₀ hu0 (by linarith) k
    rw [hgs]
    calc ‖u‖ ^ k * ‖iteratedFDeriv ℝ N _ u‖
        ≤ (1 + ‖u‖) ^ k * (N.factorial * Real.exp (-(c * ‖u‖ ^ 2)) *
            ((C + 1) * (1 + ‖u‖) ^ K) ^ N) := by
          refine mul_le_mul hpow (key.trans ?_) (norm_nonneg _) (by positivity)
          gcongr
      _ = N.factorial * (C + 1) ^ N *
            ((1 + ‖u‖) ^ (k + K * N) * Real.exp (-(c * ‖u‖ ^ 2))) := by
          rw [mul_pow, ← pow_mul, pow_add]
          ring
      _ ≤ N.factorial * (C + 1) ^ N * M := by
          gcongr
          exact hM _ hu0

theorem schFP : SchFP := by
  intro m n c hc P
  obtain ⟨S, hS⟩ := gs_sch (m := m) (n := n) c hc
  refine ⟨SchwartzMap.smulLeftCLM ℂ (fun u => evX P u) S, ?_⟩
  rw [SchwartzMap.smulLeftCLM_apply (evX_temperate P)]
  funext u
  simp [fP, hS, smul_eq_mul]

end PositivityTheory.Rg.Sw.Glob
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.GlobalGaussLaws.GaussLaw
section
noncomputable section

open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct ComplexOrder
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace PositivityTheory.Rg.Sw.Glob

variable {D : D7} {n : ℕ}

def IsAwayFn {m : ℕ} (θ : InfFam D) (τ : D.what₂.Tau) (Ψ : Mx D m n → ℂ) : Prop :=
  ∀ x x' : Mx D m n, (∀ τ', τ' ≠ τ → compAt θ τ' x = compAt θ τ' x') → x.map (finPart D) = x'.map (finPart D) → Ψ x = Ψ x'

def IsTrivAt (θ : InfFam D) (τ : D.what₂.Tau) (x : G D n) : Prop := compAt θ τ (mat x) = 1

def IsLocFact {θ : InfFam D} {V : HSp D} (ω : G D n →* Module.End ℂ (schwartzA θ V.rank n)) (τ : D.what₂.Tau)
    (fr : Matrix (Fin V.rank) (Fin V.rank) ℂ) (ι : GR n →* G D n)
    (L : GR n → ((Fin V.rank → Fin n → ℂ) → ℂ) → ((Fin V.rank → Fin n → ℂ) → ℂ)) : Prop :=
  (∀ y f, IsSch f → IsSch (L y f)) ∧ ∀ (y : GR n) Ψ (hΨ : AwayCls θ τ fr Ψ) f (hf : IsSch f),
    (ω (ι y) ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr (L y f) Ψ

def epsT {m : ℕ} (t : ℝ) (ε : Fin m → Bool) : Fin m → Bool := fun a => if 0 < t then ε a else !ε a

def gramB {m : ℕ} (ε : Fin m → Bool) (b : Bool) (y : Fin m → Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => evX (Qb ε b i j) y

def gZf {m : ℕ} (ε : Fin m → Bool) (t c : ℝ) (Z : Matrix (Fin n) (Fin n) ℂ) (y : Fin m → Fin n → ℂ) : ℂ :=
  Complex.exp (Complex.I * c * (Z * gramB (epsT t ε) true y).trace - Complex.I * c * (Zᴴ * gramB (epsT t ε) false y).trace)

def IsSiegel (Z : Matrix (Fin n) (Fin n) ℂ) : Prop := ((-(Complex.I / 2)) • (Z - Zᴴ)).PosDef

def actZ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ((mR y).toBlocks₁₁ * Z + (mR y).toBlocks₁₂) * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂)⁻¹

def jF (e : ℤ) (p q : ℕ) (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ) : ℂ :=
  (mR y).det ^ e * ((mR y).toBlocks₂₁ * Z + (mR y).toBlocks₂₂).det ^ (-(p : ℤ)) *
    ((mR y).toBlocks₂₁ * Zᴴ + (mR y).toBlocks₂₂).det ^ (-(q : ℤ))

def GZSch : Prop :=
  ∀ (m n : ℕ) (ε : Fin m → Bool) (t c : ℝ), 0 < c → |t| = c → ∀ Z : Matrix (Fin n) (Fin n) ℂ, IsSiegel Z → IsSch (gZf ε t c Z)

def AwayAct : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ x : G D n, IsTrivAt θ τ x →
    ∃ A : (Mx D V.rank n → ℂ) → (Mx D V.rank n → ℂ), ∀ Ψ (hΨ : AwayCls θ τ fr Ψ), AwayCls θ τ fr (A Ψ) ∧
      ∀ f (hf : IsSch f), (ω x ⟨tens θ τ fr f Ψ, hΨ.2 f hf⟩).1 = tens θ τ fr f (A Ψ)

def DecompAway : Prop :=
  ∀ (D : D7) (n : ℕ) (θ : InfFam D) (τ : D.what₂.Tau) (ι : GR n →* G D n), IsInfFam θ → IsPlaceEmb θ τ ι → ∀ g : G D n,
    ∃ (x : G D n) (y : GR n), IsTrivAt θ τ x ∧ g = x * ι y ∧ ∀ y' : GR n, x * ι y' = ι y' * x

def LocFact : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∃ L, IsLocFact ω τ fr ι L

def GaussLaw : Prop :=
  ∀ D n V ψ χ θ μ ω H l s ν τ ε fr ι, Cx D n V ψ χ θ μ ω H l s ν τ ε fr ι → ∀ L, IsLocFact ω τ fr ι L →
    ∃ e : ℤ, ∀ (y : GR n) (Z : Matrix (Fin n) (Fin n) ℂ), IsSiegel Z →
      L y (gZf ε (tLoc l τ) (cLoc l τ) Z) = fun u => jF e (cnt (epsT (tLoc l τ) ε) true) (cnt (epsT (tLoc l τ) ε) false) y Z *
        gZf ε (tLoc l τ) (cLoc l τ) (actZ y Z) u

end PositivityTheory.Rg.Sw.Glob
end
end

