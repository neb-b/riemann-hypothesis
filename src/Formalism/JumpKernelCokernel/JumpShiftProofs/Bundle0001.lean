module

public import Formalism.JumpKernelCokernel.Statement
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle0002
public import Formalism.TruncatedSeriesCounting.TruncatedSeriesProofs.Bundle0001

@[expose] public section

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.ColThmC
section
noncomputable section

namespace Formalism.KernelCokernelLengths

theorem column_theorem_C : ColThmC := by
  intro O _ _ _ M _ _ _ _ ℓ P k F gen n r m e e' S cD hn hrk hgen hk hF0 hF hsub hG hN hE
  have h := Formalism.TruncatedSeriesCounting.RamifiedCoefficientChains.column_assembly_bound O M ℓ P k F gen m e e' (r * S + 2 * m * cD) hF0 hF hsub hG hN hE
  refine h.trans ?_
  have hAB : Module.finrank O M * e + gen.card * m * e' + (k - gen.card) * (r * S + 2 * m * cD) ≤
      (n + 1) * r * e + 4 * n * m * e' + (3 * n / 2) * (r * S + 2 * m * cD) := by
    gcongr
  gcongr

end Formalism.KernelCokernelLengths
end
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.ColumnDegreeBound
section
namespace Formalism.KernelCokernelLengths

theorem column_degree_bound : CDge := by
  intro ℓ hℓ bi S η h hh
  have h2 : bi + S + η ≤ h + η := by omega
  gcongr
  all_goals first
    | exact_mod_cast h2
    | (rw [sub_nonneg]; exact_mod_cast (by omega : 1 ≤ ℓ))
    | (rw [sub_pos]; exact_mod_cast (by omega : 1 < ℓ))

end Formalism.KernelCokernelLengths
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.DetLen
section
namespace Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module

theorem ord_prod {O : Type} [CommRing O] [IsDomain O] {ι : Type} (s : Finset ι) (a : ι → O)
    (ha : ∀ i, a i ≠ 0) :
    Ring.ord O (∏ i ∈ s, a i) = ∑ i ∈ s, Ring.ord O (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi,
      Ring.ord_mul' O (mem_nonZeroDivisors_of_ne_zero (ha i)), ih]

end Formalism.KernelCokernelLengths.DeterminantLengthLemmas

open Module in
theorem Formalism.KernelCokernelLengths.determinant_length_formula : Formalism.KernelCokernelLengths.DetLen := by
  intro O _ _ _ M _ _ _ _ d hdet
  classical
  have hinj : Function.Injective d := by
    rw [← LinearMap.ker_eq_bot]
    by_contra hk
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hk)
  let e : M ≃ₗ[O] LinearMap.range d := LinearEquiv.ofInjective d hinj
  have h : finrank O (LinearMap.range d) = finrank O M := e.finrank_eq.symm
  let b := Free.chooseBasis O M
  let a := Submodule.smithNormalFormCoeffs b h
  let b' := Submodule.smithNormalFormTopBasis b h
  let ab := Submodule.smithNormalFormBotBasis b h
  have hab : ∀ i, (ab i : M) = a i • b' i := Submodule.smithNormalFormBotBasis_def b h
  have ha : ∀ i, a i ≠ 0 := Submodule.smithNormalFormCoeffs_ne_zero b h

  have hL : Module.length O (M ⧸ LinearMap.range d) = ∑ i, Ring.ord O (a i) := by
    rw [((LinearMap.range d).quotientEquivPiSpan b h).length_eq,
      Module.length_pi_of_fintype]
    rfl

  let u : M ≃ₗ[O] LinearMap.range d := b'.equiv ab (Equiv.refl _)
  let D : M →ₗ[O] M := (LinearMap.range d).subtype ∘ₗ u.toLinearMap
  have hD : LinearMap.det D = ∏ i, a i := by
    rw [← LinearMap.det_toMatrix b']
    have : LinearMap.toMatrix b' b' D = Matrix.diagonal a := by
      ext i j
      rw [LinearMap.toMatrix_apply]
      simp only [D, u, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
        Basis.equiv_apply, Equiv.refl_apply, Submodule.coe_subtype, hab, map_smul,
        Basis.repr_self, Finsupp.smul_apply, smul_eq_mul, Matrix.diagonal_apply,
        Finsupp.single_apply]
      by_cases hij : j = i
      · subst hij; simp
      · simp [hij, Ne.symm hij]
    rw [this, Matrix.det_diagonal]
  have hd : d = D ∘ₗ (e.trans u.symm).toLinearMap := by
    ext x
    simp [D, e]
  have hdet' : LinearMap.det d = (∏ i, a i) * LinearMap.det (e.trans u.symm).toLinearMap := by
    rw [congrArg LinearMap.det hd, LinearMap.det_comp, hD]
  rw [hL]
  change _ = Ring.ord O (LinearMap.det d)
  rw [hdet', Ring.ord_mul_of_isUnit_right (LinearEquiv.isUnit_det' _),
    Formalism.KernelCokernelLengths.DeterminantLengthLemmas.ord_prod _ _ ha]
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.FiltrationExponentHolds
section
theorem Formalism.KernelCokernelLengths.filtration_exponent_holds : Formalism.KernelCokernelLengths.FExp := by
  intro R _ u π₀ q ℓ hℓ Mi h hMi
  set m := h / (ℓ - 1) with hm
  have hpos : 0 < ℓ - 1 := by omega
  have hk : Mi + 1 ≤ (ℓ - 1) * (m + 1) := by
    have := Nat.lt_mul_div_succ h hpos
    exact Nat.succ_le_of_lt (lt_of_le_of_lt hMi this)
  obtain ⟨d, hd⟩ : ∃ d, (ℓ - 1) * (m + 1) = Mi + 1 + d := ⟨_, (Nat.add_sub_cancel' hk).symm⟩
  rw [Ideal.mem_span_singleton]
  refine ⟨u ^ (m + 1) * q ^ d, ?_⟩
  rw [mul_pow, mul_pow, ← pow_mul, hd, pow_add]
  ring
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.HCoefLim
section
noncomputable section

namespace Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

def P (s : ℝ) : ℝ := 25 + 57 * s + 40 * s ^ 2 + 8 * s ^ 3

lemma hCoef_eq (x : ℝ) (hx : 1 < x) : Formalism.KernelCokernelLengths.hCoef x = P (1 / (x - 1)) := by
  have h1 : x - 1 ≠ 0 := by linarith
  have h0 : x ≠ 0 := by linarith
  unfold Formalism.KernelCokernelLengths.hCoef P
  field_simp
  ring

lemma P_mono {s t : ℝ} (ht : 0 ≤ t) (hts : t ≤ s) : P t ≤ P s := by
  unfold P
  have hs : 0 ≤ s := le_trans ht hts
  nlinarith [mul_le_mul hts hts ht hs, pow_le_pow_left₀ ht hts 3, pow_le_pow_left₀ ht hts 2]

lemma P_ge {s : ℝ} (hs : 0 ≤ s) : 25 ≤ P s := by
  unfold P
  nlinarith [pow_nonneg hs 2, pow_nonneg hs 3]

end Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas

open Formalism.KernelCokernelLengths.CoefficientHeightLimitLemmas in
theorem Formalism.KernelCokernelLengths.coefficient_height_limit : Formalism.KernelCokernelLengths.HCoefLim := by
  refine ⟨?_, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    rw [hCoef_eq x (by linarith), hCoef_eq y (by linarith)]
    apply P_mono
    · have : 0 < y - 1 := by linarith
      positivity
    · exact one_div_le_one_div_of_le (by linarith) (by linarith)
  · intro x hx
    rw [hCoef_eq x (by linarith)]
    apply P_ge
    have : 0 < x - 1 := by linarith
    positivity
  · have hs : Filter.Tendsto (fun x : ℝ => 1 / (x - 1)) Filter.atTop (nhds 0) := by
      have h := tendsto_inv_atTop_zero.comp
        (Filter.tendsto_atTop_add_const_right Filter.atTop (-1 : ℝ) Filter.tendsto_id)
      refine h.congr ?_
      intro x
      simp [sub_eq_add_neg]
    have hP : Continuous P := by unfold P; fun_prop
    have h25 : P 0 = 25 := by unfold P; norm_num
    have hlim : Filter.Tendsto (fun x : ℝ => P (1 / (x - 1))) Filter.atTop (nhds 25) := by
      rw [← h25]; exact (hP.tendsto 0).comp hs
    refine hlim.congr' ?_
    filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
    exact (hCoef_eq x hx).symm
end
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.IdealPowerSumMem
section
namespace Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem add_pow_mem_span_pow_pow (R : Type) [CommRing R] (π₀ ℓ : R) (A r : ℕ) :
    (π₀ + ℓ) ^ (A + r - 1) ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := by
  have hπ : π₀ ^ A ∈ Ideal.span {π₀ ^ A, ℓ ^ r} := Ideal.subset_span (Set.mem_insert _ _)
  have hℓ : ℓ ^ r ∈ Ideal.span {π₀ ^ A, ℓ ^ r} :=
    Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  rw [add_pow]
  refine Ideal.sum_mem _ fun i hi => ?_
  have hi' : i ≤ A + r - 1 := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
  by_cases hA : A ≤ i
  · have e : π₀ ^ i = π₀ ^ A * π₀ ^ (i - A) := by rw [← pow_add, Nat.add_sub_cancel' hA]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ (Ideal.mul_mem_right _ _ hπ))
  · have hr : r ≤ A + r - 1 - i := by omega
    have e : ℓ ^ (A + r - 1 - i) = ℓ ^ r * ℓ ^ (A + r - 1 - i - r) := by
      rw [← pow_add, Nat.add_sub_cancel' hr]
    rw [e]
    exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ hℓ))

end Formalism.KernelCokernelLengths.IdealPowerSumLemmas

theorem Formalism.KernelCokernelLengths.ideal_power_sum_mem : Formalism.KernelCokernelLengths.QPow := by
  intro R _ π₀ ℓ A r
  exact Formalism.KernelCokernelLengths.IdealPowerSumLemmas.add_pow_mem_span_pow_pow R π₀ ℓ A r
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.InvConst
section
namespace Formalism.KernelCokernelLengths

theorem fil_eq_of_noJump {K D : Type} [Field K] [AddCommGroup D] [Module K D]
    (Fil : ℤ → Submodule K D) (b η : ℕ)
    (hj : ∀ j : ℤ, -(b : ℤ) < j → j < -(η : ℤ) → Fil j = Fil (j + 1)) :
    ∀ k : ℕ, ∀ j : ℤ, -(b : ℤ) < j → j + k = -(η : ℤ) → Fil j = Fil (-(η : ℤ)) := by
  intro k
  induction k with
  | zero =>
    intro j _ hjk
    simp only [Nat.cast_zero, add_zero] at hjk
    rw [hjk]
  | succ k ih =>
    intro j hjb hjk
    have hlt : j < -(η : ℤ) := by push_cast at hjk; omega
    rw [hj j hjb hlt]
    exact ih (j + 1) (by omega) (by push_cast at hjk ⊢; omega)

theorem exists_fixed_add_of_sub_mem : InvConst := by
  intro K _ D _ _ Fil hA χ hχ b η w hj hw
  have h1 : ∀ i : ℤ, i ≠ 0 → w i ∈ Fil (-i) := by
    intro i hi
    have hne : χ ^ i - 1 ≠ 0 := sub_ne_zero.mpr (hχ i hi)
    have h2 := (Fil (-i)).smul_mem (χ ^ i - 1)⁻¹ (hw i)
    rwa [smul_smul, inv_mul_cancel₀ hne, one_smul] at h2
  refine ⟨h1, fun i hi hib => ?_⟩
  by_cases hη : (η : ℤ) ≤ i
  · obtain ⟨k, hk⟩ : ∃ k : ℕ, -i + k = -(η : ℤ) := ⟨(i - η).toNat, by omega⟩
    rw [← fil_eq_of_noJump Fil b η hj k (-i) (by omega) hk]
    exact h1 i hi
  · exact hA (by omega : -(η : ℤ) ≤ -i) (h1 i hi)

end Formalism.KernelCokernelLengths
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.JumpShift
section
namespace Formalism.KernelCokernelLengths

theorem jump_shift_holds : JumpShift := by
  intro s S η t a ht
  refine ⟨fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ⟨by omega, by omega⟩, fun h1 h2 => ?_, fun h1 h2 h3 => ?_⟩
  · rw [abs_le]; constructor <;> omega
  · rw [abs_le]; constructor <;> omega

end Formalism.KernelCokernelLengths
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.KerCoker
section
namespace Formalism.KernelCokernelLengths.KernelCokernelLemmas

theorem main (O : Type) [CommRing O] (M : Type) [AddCommGroup M] [Module O M]
    (hM : Module.length O M ≠ ⊤) (f : Module.End O M) (N : Submodule O M) (hN : N.map f ≤ N) :
    Module.length O (↥N ⧸ (N.map f).comap N.subtype) ≤ Module.length O (LinearMap.ker f) := by
  have hNf : ∀ x ∈ N, f x ∈ N := fun x hx => hN (Submodule.mem_map_of_mem hx)
  let g : N →ₗ[O] ↥((N.map f).comap N.subtype) :=
    LinearMap.codRestrict ((N.map f).comap N.subtype) (f.restrict hNf)
      (fun x => Submodule.mem_comap.2 (Submodule.mem_map_of_mem x.2))
  have hgs : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨x, hx, hxy⟩ := Submodule.mem_comap.1 hy
    exact ⟨⟨x, hx⟩, Subtype.ext (Subtype.ext hxy)⟩
  have hNfin : Module.length O N ≠ ⊤ :=
    ne_top_of_le_ne_top hM (Module.length_le_of_injective N.subtype N.injective_subtype)
  have hQfin : Module.length O ((N.map f).comap N.subtype) ≠ ⊤ :=
    ne_top_of_le_ne_top hNfin (Module.length_le_of_injective _ (Submodule.injective_subtype _))
  have e1 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype ((N.map f).comap N.subtype))
    (Submodule.mkQ_surjective _) (LinearMap.exact_subtype_mkQ ((N.map f).comap N.subtype))
  have e2 := Module.length_eq_add_of_exact _ _ (Submodule.injective_subtype (LinearMap.ker g)) hgs
    (LinearMap.exact_subtype_ker_map g)
  have e3 : Module.length O (↥N ⧸ (N.map f).comap N.subtype) = Module.length O (LinearMap.ker g) := by
    rw [e1, add_comm] at e2
    exact WithTop.add_right_cancel hQfin e2
  rw [e3]
  refine Module.length_le_of_injective
    (LinearMap.codRestrict (LinearMap.ker f) (N.subtype.comp (LinearMap.ker g).subtype) ?_) ?_
  · intro x
    exact LinearMap.mem_ker.2
      (congrArg (fun z : ↥((N.map f).comap N.subtype) => ((z : N) : M)) (LinearMap.mem_ker.1 x.2))
  · intro x y hxy
    have h := congrArg Subtype.val hxy
    apply Subtype.ext
    apply Subtype.ext
    exact h

end Formalism.KernelCokernelLengths.KernelCokernelLemmas

theorem Formalism.KernelCokernelLengths.kernel_cokernel_lengths : Formalism.KernelCokernelLengths.KerCoker := by
  intro O _ M _ _ hM f N hN
  exact Formalism.KernelCokernelLengths.KernelCokernelLemmas.main O M hM f N hN
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.LenSplit
section
namespace Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem main (O : Type) [CommRing O] (R : Type) [AddCommGroup R] [Module O R]
    (π : Module.End O R) (R' R'' : Submodule O R) (h : R' ≤ R'') :
    Module.length O (R ⧸ (R' ⊔ LinearMap.range π)) ≤
      Module.length O (R ⧸ (R'' ⊔ LinearMap.range π)) +
        Module.length O (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) := by
  set A := R' ⊔ LinearMap.range π with hA
  set B := R'' ⊔ LinearMap.range π with hB
  have hAB : A ≤ B := sup_le_sup_right h _
  let f : (B ⧸ A.comap B.subtype) →ₗ[O] (R ⧸ A) := Submodule.mapQ (A.comap B.subtype) A B.subtype le_rfl
  let g : (R ⧸ A) →ₗ[O] (R ⧸ B) := Submodule.mapQ A B LinearMap.id (by simpa using hAB)
  have hf : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    intro x hx
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    rw [LinearMap.mem_ker] at hx
    simp only [f, Submodule.mapQ_apply, Submodule.subtype_apply, Submodule.Quotient.mk_eq_zero] at hx
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, Submodule.mem_comap]
    exact hx
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    exact ⟨Submodule.Quotient.mk r, rfl⟩
  have hex : Function.Exact f g := by
    intro y
    obtain ⟨r, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    constructor
    · intro hy
      simp only [g, Submodule.mapQ_apply, LinearMap.id_apply, Submodule.Quotient.mk_eq_zero] at hy
      exact ⟨Submodule.Quotient.mk ⟨r, hy⟩, rfl⟩
    · rintro ⟨x, hx⟩
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      rw [← hx]
      simp only [f, g, Submodule.mapQ_apply, Submodule.subtype_apply, LinearMap.id_apply,
        Submodule.Quotient.mk_eq_zero]
      exact b.2
  have hlen := Module.length_eq_add_of_exact f g hf hg hex
  have hRB : R'' ≤ B := le_sup_left
  let k : (↥R'' ⧸ (R' ⊔ R''.map π).comap R''.subtype) →ₗ[O] (B ⧸ A.comap B.subtype) :=
    Submodule.mapQ _ _ (Submodule.inclusion hRB) (by
      intro x hx
      simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_inclusion] at hx ⊢
      exact sup_le_sup_left (LinearMap.map_le_range) R' hx)
  have hk : Function.Surjective k := by
    intro y
    obtain ⟨⟨b, hb⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    obtain ⟨r, hr, p, hp, rfl⟩ := Submodule.mem_sup.mp hb
    refine ⟨Submodule.Quotient.mk ⟨r, hr⟩, ?_⟩
    simp only [k, Submodule.mapQ_apply]
    rw [Submodule.Quotient.eq]
    simp only [Submodule.mem_comap, Submodule.subtype_apply, Submodule.coe_sub, Submodule.coe_inclusion]
    have : r - (r + p) = -p := by abel
    rw [this]
    exact A.neg_mem (Submodule.mem_sup_right hp)
  have hle := Module.length_le_of_surjective k hk
  rw [hlen, add_comm]
  gcongr

end Formalism.KernelCokernelLengths.LengthSplittingLemmas

theorem Formalism.KernelCokernelLengths.length_splits_additively : Formalism.KernelCokernelLengths.LenSplit := by
  intro O _ R _ _ π R' R'' h
  exact Formalism.KernelCokernelLengths.LengthSplittingLemmas.main O R π R' R'' h
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.PdFacts
section
noncomputable section

namespace Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial

variable {O : Type} [CommRing O] {V : Type} [AddCommGroup V] [Module O V]

theorem decomp (d : Module.End O V) (P : O[X]) (v : V) :
    aeval d P v = P.eval 0 • v + aeval d P.divX (d v) := by
  conv_lhs => rw [← Polynomial.divX_mul_X_add P]
  rw [map_add (f := _), map_mul, aeval_X, aeval_C, LinearMap.add_apply, Module.End.mul_apply,
    Module.algebraMap_end_apply, ← Polynomial.coeff_zero_eq_eval_zero, add_comm]

theorem aeval_mem (d : Module.End O V) (M : Submodule O V) (hM : M.map d ≤ M) :
    ∀ (Q : O[X]) (v : V), v ∈ M → aeval d Q v ∈ M := by
  have hd : ∀ v ∈ M, d v ∈ M := fun v hv => hM (Submodule.mem_map_of_mem hv)
  have hpow : ∀ (n : ℕ) (v : V), v ∈ M → (d ^ n) v ∈ M := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih =>
      intro v hv
      rw [pow_succ, Module.End.mul_apply]
      exact ih _ (hd v hv)
  intro Q
  induction Q using Polynomial.induction_on' with
  | add p q hp hq =>
    intro v hv
    rw [map_add (f := _), LinearMap.add_apply]
    exact M.add_mem (hp v hv) (hq v hv)
  | monomial n a =>
    intro v hv
    rw [aeval_monomial, Module.End.mul_apply, Module.algebraMap_end_apply]
    exact M.smul_mem a (hpow n v hv)

end Formalism.KernelCokernelLengths.PolynomialDegreeLemmas

open Polynomial Formalism.KernelCokernelLengths.PolynomialDegreeLemmas in
theorem Formalism.KernelCokernelLengths.polynomial_degree_facts : Formalism.KernelCokernelLengths.PdFacts := by
  intro O _ V _ _ d P M hM
  refine ⟨fun h0 => ?_, fun h0 u hu => ?_⟩
  · have ha : ∀ v : V, d (aeval d P v) = 0 := by
      intro v
      have h1 := congrArg (fun f : Module.End O V => f v) h0
      simpa [map_mul, aeval_X] using h1
    refine ⟨ha, fun v hv => ?_, fun w hw u hu => ?_⟩
    · rw [decomp d P v, hv, map_zero, add_zero]
    · have h1 := decomp d P u
      have h2 : P.eval 0 • w = d (-(aeval d P.divX w)) := by
        have h3 : P.eval 0 • u = aeval d P u - aeval d P.divX (d u) := eq_sub_of_add_eq h1.symm
        rw [← hu, ← map_smul, h3, map_sub, ha, zero_sub, map_neg]
      rw [h2]
      exact Submodule.mem_map_of_mem (M.neg_mem (aeval_mem d M hM _ w hw))
  · have h1 := decomp d P u
    rw [h0, LinearMap.zero_apply] at h1
    have h3 : P.eval 0 • u = -(aeval d P.divX (d u)) := eq_neg_of_add_eq_zero_left h1.symm
    rw [h3]
    exact M.neg_mem (aeval_mem d M hM _ _ hu)
end
end

-- bundled from Formalism.JumpKernelCokernel.JumpShiftProofs.RelZero
section
namespace Formalism.KernelCokernelLengths

theorem relation_vanishes : RelZero := by
  intro R _ u π₀ q ℓ h η y hℓ hη hy
  apply Formalism.TruncatedSeriesCounting.R9.pow_mem_span_pow_mul R u π₀ q ℓ (h / (ℓ - 1) + 1) η y hy
  have hpos : 0 < ℓ - 1 := by omega
  have h1 : h < (ℓ - 1) * (h / (ℓ - 1) + 1) := Nat.lt_mul_div_succ h hpos
  have h2 : (ℓ - 1) * (h / (ℓ - 1) + 1) ≤ (ℓ - 1) * y := Nat.mul_le_mul_left _ hy
  omega

end Formalism.KernelCokernelLengths
end

