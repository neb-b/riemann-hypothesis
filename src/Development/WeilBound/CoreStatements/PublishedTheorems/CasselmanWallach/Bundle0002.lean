module

public import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirRealOfCentral
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirRealScalar

variable {n : ℕ}

theorem casimir_eq_trace {V : Type} [AddCommGroup V] [Module ℂ V] (E : Fin n → Fin n → Module.End ℂ V) :
    casimir E = (Mm E ^ 2).trace := by
  unfold casimir Mm
  rw [sq, Matrix.trace]
  simp [Matrix.diag, Matrix.mul_apply]

theorem term_im {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E) (a b : Fin n) (v : V) :
    (inner ℂ v (E a b (E b a v))).im = 0 := by
  rw [← inner_conj_symm, hu a b, Complex.conj_im, neg_eq_zero]
  have h1 : (adjSign ε a b).im = 0 := by
    unfold adjSign
    split_ifs <;> simp
  have h2 : (inner ℂ (E b a v) (E b a v)).im = 0 := inner_self_im (𝕜 := ℂ) _
  rw [Complex.mul_im, h1, h2]
  ring

theorem cas_im {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] (ε : Fin n → Bool)
    (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E) (v : V) :
    (inner ℂ v (casimir E v)).im = 0 := by
  unfold casimir
  simp only [LinearMap.sum_apply, Module.End.mul_apply, inner_sum, Complex.im_sum]
  exact Finset.sum_eq_zero fun a _ => Finset.sum_eq_zero fun b _ => term_im ε E hu a b v

end CasimirRealScalar

theorem casimir_real_of_central : A2 → A3 → CasimirIsRealScalar := by
  intro h2 h3
  unfold CasimirIsRealScalar ForMod
  intro n ε V _ _ E h
  have hc : ∀ a b, E a b * casimir E = casimir E * E a b := by
    intro a b
    rw [CasimirRealScalar.casimir_eq_trace]
    exact h2 n ε V E h 2 a b
  obtain ⟨c, hc'⟩ := h3 n ε V E h (casimir E) hc
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have him := CasimirRealScalar.cas_im ε E h.uni v
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have hcim : c.im = 0 := by
    rw [hc', inner_smul_right, inner_self_eq_norm_sq_to_K, Complex.mul_im] at him
    have hre : ((‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_re]
    have him2 : ((‖v‖ : ℂ) ^ 2).im = 0 := by
      rw [← Complex.ofReal_pow, Complex.ofReal_im]
    erw [hre, him2, mul_zero, zero_add] at him
    rcases mul_eq_zero.mp him with h0 | h0
    · exact h0
    · exact absurd (pow_eq_zero_iff two_ne_zero |>.mp h0) hn
  refine ⟨c.re, fun w => ?_⟩
  rw [hc' w]
  congr 1
  apply Complex.ext <;> simp [hcim]

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CasimirRealScalar
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace CasimirEigenvector

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

lemma comm_casimirK (T : Module.End ℂ V) (hT : ∀ a b, E a b * T = T * E a b) :
    casimirK ε E * T = T * casimirK ε E := by
  unfold casimirK
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [mul_assoc, hT b a, ← mul_assoc, hT a b, mul_assoc]

lemma exists_eig_ne (h : Mod ε E) [Nontrivial V] : ∃ μ : ℝ, ∃ v : V, v ≠ 0 ∧ Eig ε E μ v := by
  by_contra hc
  push_neg at hc
  have hb : Submodule.span ℂ {v | ∃ μ : ℝ, Eig ε E μ v} = ⊥ := by
    rw [Submodule.span_eq_bot]
    rintro v ⟨μ, hv⟩
    by_contra hne
    exact hc μ v hne hv
  rw [h.span] at hb
  exact top_ne_bot hb

end CasimirEigenvector

theorem casimir_eigen_exists : A3 := by
  intro n ε V _ _ E h T hT
  rcases subsingleton_or_nontrivial V with hV | hV
  · exact ⟨0, fun v => Subsingleton.elim _ _⟩
  obtain ⟨μ, v, hv0, hv⟩ := CasimirEigenvector.exists_eig_ne h
  set W := Module.End.eigenspace (casimirK ε E) (μ : ℂ) with hWdef
  have hWle : W ≤ Submodule.span ℂ {v | ∃ ν : ℝ, ν ≤ μ ∧ Eig ε E ν v} := by
    intro x hx
    apply Submodule.subset_span
    exact ⟨μ, le_rfl, Module.End.mem_eigenspace_iff.mp hx⟩
  have := h.fin μ
  have : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le hWle
  have hvW : v ∈ W := Module.End.mem_eigenspace_iff.mpr hv
  have : Nontrivial W := ⟨⟨⟨v, hvW⟩, 0, fun he => hv0 (congrArg Subtype.val he)⟩⟩
  have hTW : ∀ x ∈ W, T x ∈ W := by
    intro x hx
    rw [Module.End.mem_eigenspace_iff] at hx ⊢
    have hc := congrArg (fun f : Module.End ℂ V => f x) (CasimirEigenvector.comm_casimirK (ε := ε) T hT)
    simp only [Module.End.mul_apply] at hc
    rw [hc, hx, map_smul]
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (T.restrict hTW)
  obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
  refine ⟨c, ?_⟩
  have hN : LinearMap.ker (T - c • 1) = ⊥ ∨ LinearMap.ker (T - c • 1) = ⊤ := by
    apply h.irr
    intro a b x hx
    rw [LinearMap.mem_ker] at hx ⊢
    have he := congrArg (fun f : Module.End ℂ V => f x) (hT a b)
    simp only [Module.End.mul_apply] at he
    simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at hx ⊢
    rw [← he, ← LinearMap.map_smul, ← map_sub, hx, map_zero]
  have hw1 : T (w : V) = c • (w : V) := by
    have := Module.End.mem_eigenspace_iff.mp hw.1
    exact congrArg Subtype.val this
  have hw0 : (w : V) ≠ 0 := fun h0 => hw.2 (Subtype.ext h0)
  rcases hN with hN | hN
  · exfalso
    apply hw0
    have : (w : V) ∈ LinearMap.ker (T - c • 1) := by
      rw [LinearMap.mem_ker]
      simp [hw1]
    rw [hN] at this
    exact (Submodule.mem_bot ℂ).mp this
  · intro x
    have : x ∈ LinearMap.ker (T - c • 1) := by rw [hN]; trivial
    rw [LinearMap.mem_ker] at this
    simpa [sub_eq_zero] using this

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.ColumnMomentsOfSymmetric
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace MatrixActionSingle

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def act (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) : Module.End ℂ (PiLp 2 fun _ : Fin n => V) where
  toFun u := WithLp.toLp 2 (fun a => ∑ b, A a b (u b))
  map_add' u w := by ext a; simp [Finset.sum_add_distrib]
  map_smul' c u := by ext a; simp [Finset.smul_sum]

lemma act_apply (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (u : PiLp 2 fun _ : Fin n => V) (a : Fin n) :
    act A u a = ∑ b, A a b (u b) := rfl

lemma act_mul (A B : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (u : PiLp 2 fun _ : Fin n => V) :
    act (A * B) u = act A (act B u) := by
  ext a
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [act_apply, Matrix.mul_apply, LinearMap.sum_apply, Module.End.mul_apply, map_sum]
  exact Finset.sum_comm

lemma act_pow (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (m : ℕ) (u : PiLp 2 fun _ : Fin n => V) :
    act (A ^ m) u = (act A ^ m) u := by
  induction m generalizing u with
  | zero =>
    ext a
    simp [act_apply, Matrix.one_apply]
    rw [Finset.sum_eq_single a (fun b _ hb => by simp [Ne.symm hb]) (by simp)]
    simp
  | succ m ih => rw [pow_succ, act_mul, ih, pow_succ, Module.End.mul_apply]

lemma adjSign_symm (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b = adjSign ε b a := by
  simp [adjSign, eq_comm]

lemma adj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Mm E) u) w = inner ℂ u (act (Md ε E) w) := by
  simp only [PiLp.inner_apply, act_apply, Mm, Md, Matrix.of_apply, sum_inner, inner_sum,
    LinearMap.smul_apply, inner_smul_right]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun a _ => ?_
  rw [adjSign_symm]
  exact hu a b _ _

lemma adj' (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (u w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (act (Md ε E) u) w = inner ℂ u (act (Mm E) w) := by
  rw [← inner_conj_symm, ← adj ε E hu, inner_conj_symm]

lemma act_single (A : Matrix (Fin n) (Fin n) (Module.End ℂ V)) (e a : Fin n) (v : V) :
    act A (PiLp.single 2 e v) a = A a e v := by
  rw [act_apply, Finset.sum_eq_single e]
  · simp [PiLp.single_apply]
  · intro b _ hb
    simp [PiLp.single_apply, hb]
  · intro h
    exact absurd (Finset.mem_univ e) h

lemma inner_single (e : Fin n) (v : V) (w : PiLp 2 fun _ : Fin n => V) :
    inner ℂ (PiLp.single 2 e v) w = inner ℂ v (w e) := by
  rw [PiLp.inner_apply, Finset.sum_eq_single e (fun b _ hb => by simp [hb]) (by simp)]
  simp

end MatrixActionSingle

open MatrixActionSingle in
theorem column_moments_of_symmetric : A7 → ColumnOperatorMoments := by
  intro h7
  unfold ColumnOperatorMoments ForMod
  intro n ε V _ _ E hM v hv e j
  have hu := hM.uni
  have hsa : ∀ y z : PiLp 2 (fun _ : Fin n => V),
      inner ℂ (act (Md ε E * Mm E) y) z = inner ℂ y (act (Md ε E * Mm E) z) := by
    intro y z
    rw [act_mul, act_mul, adj' ε E hu, adj ε E hu]
  have hxn : ‖(PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ = 1 := by
    rw [PiLp.norm_single, hv]
  have hn : ‖act (Mm E) (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))‖ ^ 2
      = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [PiLp.norm_sq_eq_of_L2]
    refine Finset.sum_congr rfl fun a _ => ?_
    have := act_single (Mm E) e a v
    simp only [Mm, Matrix.of_apply] at this
    rw [← this]
    rfl
  have hq : inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v)) = ((∑ a, ‖E a e v‖ ^ 2 : ℝ) : ℂ) := by
    rw [act_mul, ← adj ε E hu, inner_self_eq_norm_sq_to_K, ← hn]
    norm_cast
  have hre : (inner ℂ (PiLp.single 2 e v : PiLp 2 (fun _ : Fin n => V))
      (act (Md ε E * Mm E) (PiLp.single 2 e v))).re = ∑ a, ‖E a e v‖ ^ 2 := by
    rw [hq, Complex.ofReal_re]
  have key := h7 (PiLp 2 (fun _ : Fin n => V)) (act (Md ε E * Mm E)) hsa
    (PiLp.single 2 e v) hxn (by rw [hre]; positivity) j
  rw [hre, ← act_pow, inner_single, act_single] at key
  exact key

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.CompactGroupFacts
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS Filter Topology Set

namespace PositivityTheory.CW

theorem second_derivative_holds : B3 := by
  intro ψ ψ' d hmax hψ hd
  by_contra hneg
  have hdpos : 0 < d := lt_of_not_ge hneg
  have h0 : ψ' 0 = 0 := hmax.hasDerivAt_eq_zero (hψ 0)
  have hslope := hd.tendsto_slope_zero_right
  have e1 : ∀ᶠ t in 𝓝[>] (0 : ℝ), ψ t ≤ ψ 0 := nhdsWithin_le_nhds hmax
  have e2 : ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 < t⁻¹ • (ψ' (0 + t) - ψ' 0) := hslope (lt_mem_nhds hdpos)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp (e1.and e2)
  have hu0 : (0 : ℝ) < u := hu
  have hb : u / 2 ∈ Set.Ioo (0 : ℝ) u := ⟨by linarith, by linarith⟩
  obtain ⟨c, hc, hcslope⟩ := exists_hasDerivAt_eq_slope ψ ψ' (half_pos hu0)
    (fun t _ => (hψ t).continuousAt.continuousWithinAt) (fun t _ => hψ t)
  have hcu : c ∈ Set.Ioo (0 : ℝ) u := ⟨hc.1, hc.2.trans (by linarith)⟩
  obtain ⟨-, hc'⟩ := hsub hcu
  obtain ⟨hbmax, -⟩ := hsub hb
  simp only [zero_add, h0, sub_zero, smul_eq_mul] at hc'
  have hψc : 0 < ψ' c := (pos_iff_pos_of_mul_pos hc').mp (inv_pos.mpr hc.1)
  rw [hcslope, sub_zero] at hψc
  have hdiff : 0 < ψ (u / 2) - ψ 0 := by
    have := mul_pos hψc (half_pos hu0)
    rwa [div_mul_cancel₀ _ (half_pos hu0).ne'] at this
  linarith

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenWeightedSumBound
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace SumSquaresShift

theorem shift {n : ℕ} {ε : Fin n → Bool} (hB3g : UnitaryGroupFacts) (F0 : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (X : Matrix (Fin n) (Fin n) ℂ) (hX : inP ε X) (D : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (h : ∀ g ∈ UJset ε, HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D g) 0)
    (g : Matrix (Fin n) (Fin n) ℂ) (hg : g ∈ UJset ε) (t : ℝ) :
    HasDerivAt (fun t : ℝ => F0 (g * NormedSpace.exp (t • X))) (D (g * NormedSpace.exp (t • X))) t := by
  obtain ⟨-, -, hmem, hadd, -⟩ := hB3g n ε
  have hg' := hmem g hg X hX t
  have h1 := h _ hg'
  have h0 : HasDerivAt (fun s : ℝ => F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp (s • X)))
      (D (g * NormedSpace.exp (t • X))) (t - t) := by
    rw [sub_self]; exact h1
  have h4 := h0.comp_sub_const t t
  refine h4.congr_of_eventuallyEq (Filter.Eventually.of_forall fun u => ?_)
  have hu : t + (u - t) = u := by ring
  show F0 (g * NormedSpace.exp (u • X)) = F0 (g * NormedSpace.exp (t • X) * NormedSpace.exp ((u - t) • X))
  rw [mul_assoc, ← hadd X t (u - t), hu]

end SumSquaresShift

open SumSquaresShift in
theorem second_derivatives_of_growth : B1 → UnitaryGroupFacts → SumSquaresSecondDerivative := by
  intro hB1 hB3g n ε V _ _ E hMod ι b μ hEig κ hκ F hF S a g hg
  obtain ⟨hXp, hcas, hnorm⟩ := hB1 n ε V E hMod
  have hd : ∀ p ∈ nc ε, ∀ (v : V) (t : ℝ),
      HasDerivAt (fun s : ℝ => F v (g * NormedSpace.exp (s • Xp p.1 p.2)))
        (F (actM E (Xp p.1 p.2) v) (g * NormedSpace.exp (t • Xp p.1 p.2))) t := by
    intro p hp v t
    exact shift hB3g (F v) (Xp p.1 p.2) (hXp p hp) (fun k => F (actM E (Xp p.1 p.2) v) k)
      (fun k hk => hF _ (hXp p hp) v k hk) g hg t
  have hexp0 : ∀ X : Matrix (Fin n) (Fin n) ℂ, g * NormedSpace.exp ((0:ℝ) • X) = g := by
    intro X
    simp [NormedSpace.exp_zero]
  refine ⟨fun p => ∑ i ∈ S, a i * (2 * (inner ℝ (F (b i) g)
      (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g) + ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2)), ?_, ?_⟩
  · intro p hp
    refine ⟨fun t => ∑ i ∈ S, a i * (2 * inner ℝ (F (b i) (g * NormedSpace.exp (t • Xp p.1 p.2)))
      (F (actM E (Xp p.1 p.2) (b i)) (g * NormedSpace.exp (t • Xp p.1 p.2)))), ?_, ?_⟩
    · intro t
      beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      exact ((hd p hp (b i) t).norm_sq).const_mul (a i)
    · beta_reduce
      apply HasDerivAt.fun_sum
      intro i _
      have h1 := hd p hp (b i) 0
      have h2 := hd p hp (actM E (Xp p.1 p.2) (b i)) 0
      have h3 := ((HasDerivAt.inner ℝ h1 h2).const_mul 2).const_mul (a i)
      rw [hexp0] at h3
      refine h3.congr_deriv ?_
      rw [real_inner_self_eq_norm_sq]
  · dsimp only
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    have hN : ∑ p ∈ nc ε, ‖F (actM E (Xp p.1 p.2) (b i)) g‖ ^ 2
        = ∑ p ∈ nc ε, ‖F (E p.1 p.2 (b i)) g‖ ^ 2 :=
      hnorm ((LinearMap.proj g).comp F) (b i)
    have hs : ∑ p ∈ nc ε, F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g
        = ((κ - μ i : ℝ) : ℂ) * F (b i) g := by
      have h0 := congrArg (fun v => F v g) (hcas κ hκ (b i))
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [map_sum, Finset.sum_apply] at h0
      rw [h0, (hEig.eig i : casimirK ε E (b i) = _)]
      simp only [map_sub, map_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      push_cast
      ring
    have hI : ∑ p ∈ nc ε, inner ℝ (F (b i) g) (F (actM E (Xp p.1 p.2) (actM E (Xp p.1 p.2) (b i))) g)
        = (κ - μ i) * ‖F (b i) g‖ ^ 2 := by
      rw [← inner_sum, hs, ← Complex.real_smul, real_inner_smul_right, real_inner_self_eq_norm_sq]
    rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_add_distrib, hI, hN]
    ring

end PositivityTheory.CW

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.EigenbasisOfBasic
section
noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace EigenspaceDecomposition

variable {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
  {E : Fin n → Fin n → Module.End ℂ V}

abbrev Es (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (μ : ℝ) : Submodule ℂ V :=
  Module.End.eigenspace (casimirK ε E) (μ : ℂ)

theorem mem_Es {μ : ℝ} {v : V} : v ∈ Es ε E μ ↔ Eig ε E μ v :=
  Module.End.mem_eigenspace_iff

theorem fd (h : Mod ε E) (μ : ℝ) : FiniteDimensional ℂ (Es ε E μ) := by
  haveI := h.fin μ
  refine Submodule.finiteDimensional_of_le (S₂ := Submodule.span ℂ {v : V | ∃ μ' ≤ μ, Eig ε E μ' v}) ?_
  intro v hv
  exact Submodule.subset_span ⟨μ, le_rfl, mem_Es.mp hv⟩

end EigenspaceDecomposition

open EigenspaceDecomposition in
theorem eigenbasis_of_basic : A0 → EigenbasisExists := by
  intro hA n ε V _ _ E h
  obtain ⟨hsym, hnn, -, -⟩ := hA n ε V E h
  haveI : ∀ μ : ℝ, FiniteDimensional ℂ (Es ε E μ) := fun μ => fd h μ
  let f : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) → V :=
    fun i => ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2 : V)
  have hOF : OrthogonalFamily ℂ (fun μ : ℝ => Es ε E μ) (fun μ => (Es ε E μ).subtypeₗᵢ) :=
    (LinearMap.IsSymmetric.orthogonalFamily_eigenspaces (T := casimirK ε E) hsym).comp
      (f := fun μ : ℝ => (μ : ℂ)) Complex.ofReal_injective
  have hon : Orthonormal ℂ f :=
    hOF.orthonormal_sigma_orthonormal (fun μ => (stdOrthonormalBasis ℂ (Es ε E μ)).orthonormal)
  have hli : LinearIndependent ℂ f := hon.linearIndependent
  have hEs : ∀ μ : ℝ, ∀ v ∈ Es ε E μ, v ∈ Submodule.span ℂ (Set.range f) := by
    intro μ v hv
    have key := (stdOrthonormalBasis ℂ (Es ε E μ)).sum_repr ⟨v, hv⟩
    have hv' : v = ∑ i, ((stdOrthonormalBasis ℂ (Es ε E μ)).repr ⟨v, hv⟩ i) •
        ((stdOrthonormalBasis ℂ (Es ε E μ)) i : V) := by
      have := congrArg Subtype.val key
      rw [Submodule.coe_sum] at this
      simpa using this.symm
    rw [hv']
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨μ, i⟩, rfl⟩)
  have hsp : ⊤ ≤ Submodule.span ℂ (Set.range f) := by
    rw [← h.span, Submodule.span_le]
    rintro v ⟨μ, hμ⟩
    exact hEs μ v (mem_Es.mpr hμ)
  have heig : ∀ i, Eig ε E i.1 (f i) := fun i =>
    mem_Es.mp ((stdOrthonormalBasis ℂ (Es ε E i.1)) i.2).2
  refine ⟨_, Module.Basis.mk hli hsp, fun i => i.1, ?_⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · simpa using hon
  · intro i
    simpa using heig i
  · intro i
    refine hnn i.1 (f i) (heig i) ?_
    intro h0
    have := hon.1 i
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  · intro R
    haveI := h.fin R
    let W := Submodule.span ℂ {v : V | ∃ μ ≤ R, Eig ε E μ v}
    let g : {i : (Σ μ : ℝ, Fin (Module.finrank ℂ (Es ε E μ))) | i.1 ≤ R} → W :=
      fun i => ⟨f i.1, Submodule.subset_span ⟨i.1.1, i.2, heig i.1⟩⟩
    have hg : LinearIndependent ℂ g :=
      LinearIndependent.of_comp W.subtype (hli.comp _ Subtype.val_injective)
    haveI := hg.finite
    exact Set.toFinite _

end PositivityTheory.CW

end
end

