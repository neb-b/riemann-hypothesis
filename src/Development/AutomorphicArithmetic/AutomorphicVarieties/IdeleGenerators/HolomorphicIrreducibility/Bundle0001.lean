module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.ConstSmall
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SimultaneousEigenvectors.SimEig
public import Mathlib

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.CuspOf
section
open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af
open scoped MatrixGroups ModularForm

theorem UpperTheory.V.Sd.cuspOf :
    UpperTheory.V.Sd.CuspOf := by
  intro N k _ χ f hχ hv h0
  have hT : (1:ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    rw [Subgroup.mem_strictPeriods_iff]
    refine ⟨ModularGroup.T, ?_, ?_⟩
    · rw [SetLike.mem_coe, Gamma1_mem]
      simp [ModularGroup.T]
    · ext i j
      rw [Matrix.SpecialLinearGroup.mapGL_coe_matrix, Matrix.SpecialLinearGroup.map_apply_coe]
      fin_cases i <;> fin_cases j <;> simp [ModularGroup.T]
  have hinf : IsZeroAtImInfty f := by
    apply ModularForm.isZeroAtImInfty_of_valueAtInfty_eq_zero f
    rw [← qExpansion_coeff_zero one_pos (ModularFormClass.analyticAt_cuspFunction_zero f one_pos hT)
      (SlashInvariantFormClass.periodic_comp_ofComplex f hT)]
    exact h0
  refine ⟨⟨f.toSlashInvariantForm, f.holo', fun {c} hc => ?_⟩, rfl⟩
  have hc' : IsCusp c 𝒮ℒ := by
    rwa [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hc
  rw [OnePoint.isZeroAt_iff_forall_SL2Z hc']
  intro γ _
  by_cases hd : (N:ℤ) ∣ γ 1 0
  · have hγ : γ ∈ Gamma0 N := Gamma0_mem.mpr ((ZMod.intCast_zmod_eq_zero_iff_dvd _ N).mpr hd)
    change IsZeroAtImInfty (⇑f ∣[(k:ℤ)] γ)
    rw [hχ γ hγ]
    exact hinf.smul _
  · exact hv γ hd
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.DelSerre
section
open Module

section
variable {K M : Type} [Field K] [IsAlgClosed K] [AddCommGroup M] [Module K M] [FiniteDimensional K M]

omit [IsAlgClosed K] in
private theorem finrank_map_lt (U : Submodule K M) (S : Module.End K M) (v : M) (hv : v ∈ U) (hv0 : v ≠ 0)
    (hS : S v = 0) : finrank K (U.map S) < finrank K U := by
  have h1 := LinearMap.finrank_range_add_finrank_ker (S.domRestrict U)
  rw [LinearMap.range_domRestrict] at h1
  have h2 : LinearMap.ker (S.domRestrict U) ≠ ⊥ := (Submodule.ne_bot_iff _).mpr
    ⟨⟨v, hv⟩, by simpa using hS, fun h => hv0 (congrArg Subtype.val h)⟩
  have h3 : finrank K (LinearMap.ker (S.domRestrict U)) ≠ 0 := fun h => h2 (Submodule.finrank_eq_zero.mp h)
  omega

end

section
variable {K : Type} [NormedField K] [IsUltrametricDist K]

private theorem sub_le_one' {x y : K} (hx : ‖x‖ ≤ 1) (hy : ‖y‖ ≤ 1) : ‖x - y‖ ≤ 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by simpa using hy))

private theorem sub_lt_one' {x y : K} (hx : ‖x‖ < 1) (hy : ‖y‖ < 1) : ‖x - y‖ < 1 := by
  rw [sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt hx (by simpa using hy))

private def bdd {I : Type} (V : Submodule K (I → K)) : Submodule K V where
  carrier := {v | ∃ c : K, c ≠ 0 ∧ ∀ n, ‖(c • v).1 n‖ ≤ 1}
  zero_mem' := ⟨1, one_ne_zero, fun n => by simp⟩
  add_mem' := by
    have key : ∀ (c e x : K), e ≠ 0 → ‖c‖ ≤ ‖e‖ → ‖e * x‖ ≤ 1 → ‖c * x‖ ≤ 1 := by
      intro c e x _ hce hx
      rw [norm_mul] at hx ⊢
      exact (mul_le_mul_of_nonneg_right hce (norm_nonneg _)).trans hx
    rintro v w ⟨c, hc, hv⟩ ⟨e, he, hw⟩
    rcases le_total ‖c‖ ‖e‖ with h | h
    · refine ⟨c, hc, fun n => ?_⟩
      have : (c • (v + w)).1 n = c * v.1 n + c * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hv n) (key c e _ he h (hw n)))
    · refine ⟨e, he, fun n => ?_⟩
      have : (e • (v + w)).1 n = e * v.1 n + e * w.1 n := by simp [mul_add]
      rw [this]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (key e c _ hc h (hv n)) (hw n))
  smul_mem' := by
    rintro s v ⟨c, hc, hv⟩
    by_cases hs : s = 0
    · exact ⟨1, one_ne_zero, fun n => by simp [hs]⟩
    · refine ⟨c / s, div_ne_zero hc hs, fun n => ?_⟩
      rw [smul_smul, div_mul_cancel₀ c hs]
      exact hv n

omit [IsUltrametricDist K] in
private theorem eig_le_one {I : Type} {V : Submodule K (I → K)} (T : Module.End K V)
    (hT : ∀ v : V, (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T v).1 n‖ ≤ 1) (v : V) (hv0 : v ≠ 0) (hv : ∀ n, ‖v.1 n‖ ≤ 1)
    (c : K) (hc : T v = c • v) : ‖c‖ ≤ 1 := by
  by_contra h
  push Not at h
  have hk : ∀ k : ℕ, ∀ n, ‖(c ^ k • v).1 n‖ ≤ 1 := by
    intro k
    induction k with
    | zero => simpa using hv
    | succ k ih =>
      have := hT _ ih
      rwa [map_smul, hc, smul_smul, ← pow_succ] at this
  obtain ⟨n, hn⟩ : ∃ n, v.1 n ≠ 0 := by
    by_contra h'
    push Not at h'
    exact hv0 (Subtype.ext (funext h'))
  have hpos : 0 < ‖v.1 n‖ := norm_pos_iff.mpr hn
  obtain ⟨k, hk'⟩ := pow_unbounded_of_one_lt (‖v.1 n‖⁻¹) h
  have h1 := hk k n
  have h2 : (c ^ k • v).1 n = c ^ k * v.1 n := by simp
  rw [h2, norm_mul, norm_pow] at h1
  have h3 := mul_lt_mul_of_pos_right hk' hpos
  rw [inv_mul_cancel₀ hpos.ne'] at h3
  linarith

private theorem main [IsAlgClosed K] {I J : Type} (V : Submodule K (I → K)) [FiniteDimensional K V]
    (T : J → Module.End K V) (hc : ∀ i j, T i * T j = T j * T i)
    (h1 : ∀ j (v : V), (∀ n, ‖v.1 n‖ ≤ 1) → ∀ n, ‖(T j v).1 n‖ ≤ 1)
    (h2 : ∀ j (v : V), (∀ n, ‖v.1 n‖ < 1) → ∀ n, ‖(T j v).1 n‖ < 1) (a : J → K) (ha : ∀ j, ‖a j‖ ≤ 1) :
    ∀ (d : ℕ) (U : Submodule K V), finrank K U = d → U ≤ bdd V → (∀ j, ∀ x ∈ U, T j x ∈ U) →
      ∀ f ∈ U, (∀ n, ‖f.1 n‖ ≤ 1) → (∃ n, ‖f.1 n‖ = 1) → (∀ j n, ‖(T j f).1 n - a j * f.1 n‖ < 1) →
      ∃ (h : V) (b : J → K), h ≠ 0 ∧ (∀ n, ‖h.1 n‖ ≤ 1) ∧ (∀ j, T j h = b j • h) ∧ ∀ j, ‖b j - a j‖ < 1 := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro U hd hb hT f hfU hf hf1 hfa
    by_cases h : ∀ j (c : K), ∀ v ∈ U, v ≠ 0 → T j v = c • v → ‖c - a j‖ < 1
    · have hU : U ≠ ⊥ := by
        refine (Submodule.ne_bot_iff U).mpr ⟨f, hfU, ?_⟩
        rintro rfl
        obtain ⟨n, hn⟩ := hf1
        simp at hn
      obtain ⟨v, hv, hv0, hve⟩ := UpperTheory.V.LinAlg.simEig T hc _ U rfl hU hT
      choose b hbv using hve
      obtain ⟨c, hc0, hcv⟩ := hb hv
      refine ⟨c • v, b, smul_ne_zero hc0 hv0, hcv, fun j => ?_, fun j => h j (b j) v hv hv0 (hbv j)⟩
      rw [map_smul, hbv j, smul_comm]
    · push Not at h
      obtain ⟨j, c, v, hv, hv0, hcv, hca⟩ := h
      have hc1 : ‖c‖ ≤ 1 := by
        obtain ⟨e, he0, hev⟩ := hb hv
        refine eig_le_one (T j) (h1 j) (e • v) (smul_ne_zero he0 hv0) hev c ?_
        rw [map_smul, hcv, smul_comm]
      have hca1 : ‖c - a j‖ = 1 := le_antisymm (sub_le_one' hc1 (ha j)) hca
      let S : Module.End K V := T j - c • 1
      have hS : ∀ x, S x = T j x - c • x := fun x => by simp [S]
      have hcomm : ∀ i x, T i (S x) = S (T i x) := by
        intro i x
        have h3 : T j (T i x) = T i (T j x) := by
          have := congrArg (fun S : Module.End K V => S x) (hc j i)
          simpa using this
        rw [hS, hS, map_sub, map_smul, h3]
      have hle : U.map S ≤ U := by
        rintro _ ⟨x, hx, rfl⟩
        rw [hS]
        exact U.sub_mem (hT j x hx) (U.smul_mem c hx)
      have hSn : ∀ (x : V) n, (S x).1 n = (T j x).1 n - c * x.1 n := fun x n => by rw [hS]; simp
      refine ih _ (hd ▸ finrank_map_lt U S v hv hv0 (by rw [hS, hcv, sub_self])) (U.map S) rfl (hle.trans hb) ?_
        (S f) ⟨f, hfU, rfl⟩ ?_ ?_ ?_
      · rintro i _ ⟨x, hx, rfl⟩
        exact ⟨T i x, hT i x hx, (hcomm i x).symm⟩
      · intro n
        rw [hSn]
        refine sub_le_one' (h1 j f hf n) ?_
        rw [norm_mul]
        exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
      · obtain ⟨n, hn⟩ := hf1
        refine ⟨n, le_antisymm ?_ ?_⟩
        · rw [hSn]
          refine sub_le_one' (h1 j f hf n) ?_
          rw [norm_mul]
          exact mul_le_one₀ hc1 (norm_nonneg _) (hf n)
        · by_contra hlt
          push Not at hlt
          have h4 := sub_lt_one' (hfa j n) hlt
          have h5 : (T j f).1 n - a j * f.1 n - (S f).1 n = (c - a j) * f.1 n := by rw [hSn]; ring
          rw [h5, norm_mul, hca1, hn] at h4
          simp at h4
      · intro i n
        have hg : ∀ n, ‖(T i f - a i • f).1 n‖ < 1 := fun n => by simpa using hfa i n
        have h6 : (T i (S f)).1 n - a i * (S f).1 n = (S (T i f - a i • f)).1 n := by
          rw [map_sub, map_smul, hcomm]; simp
        rw [h6, hSn]
        refine sub_lt_one' (h2 j _ hg n) ?_
        rw [norm_mul]
        exact mul_lt_one_of_nonneg_of_lt_one_right hc1 (norm_nonneg _) (hg n)

end

theorem UpperTheory.V.Sd.delSerre :
    UpperTheory.V.Sd.DelSerre := by
  intro l _ I J V hV T hc h1 h2 f a hf hf1 ha hfa
  refine main V T hc h1 h2 a ha _ (bdd V) rfl le_rfl ?_ f ⟨1, one_ne_zero, by simpa using hf⟩ hf hf1 hfa
  rintro j x ⟨c, hc0, hx⟩
  refine ⟨c, hc0, ?_⟩
  rw [← map_smul]
  exact h1 j _ hx
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EPrim
section
theorem UpperTheory.V.Sd.ePrim :
    UpperTheory.V.Sd.EPrim := by
  intro l M w φ θ χ D
  have hM := D.one_lt
  have hw := D.prime
  haveI : NeZero M := ⟨by omega⟩
  haveI : NeZero w := ⟨hw.ne_zero⟩
  haveI : NeZero (M * w) := ⟨mul_ne_zero (NeZero.ne M) (NeZero.ne w)⟩
  set A := DirichletCharacter.changeLevel (dvd_mul_right M w) φ with hA
  set B := DirichletCharacter.changeLevel (dvd_mul_left w M) θ with hB
  have hχ : χ = A * B := by
    ext u
    have h1 := D.mul (u : ZMod (M * w)).val
    rw [MulChar.mul_apply, hA, hB, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd, ← ZMod.natCast_val, ← ZMod.natCast_val,
      ← h1, ZMod.natCast_zmod_val]
  have hAc : A.conductor = M := by
    rw [hA, DirichletCharacter.conductor_changeLevel]
    exact D.prim
  have hBc : B.conductor = w := by
    rw [hB, DirichletCharacter.conductor_changeLevel]
    rcases (Nat.dvd_prime hw).mp θ.conductor_dvd_level with h | h
    · exact absurd (DirichletCharacter.eq_one_iff_conductor_eq_one.mpr h) D.θne
    · exact h
  have hcop : M.Coprime w := ((Nat.Prime.coprime_iff_not_dvd hw).mpr D.wM).symm
  have h1 : M ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor χ B⁻¹
    rw [DirichletCharacter.conductor_inv, hBc] at h
    have e : χ * B⁻¹ = A := by rw [hχ, mul_inv_cancel_right]
    rw [e, hAc] at h
    exact hcop.dvd_of_dvd_mul_right (h.trans (Nat.lcm_dvd_mul _ _))
  have h2 : w ∣ χ.conductor := by
    have h := DirichletCharacter.conductor_mul_dvd_lcm_conductor A⁻¹ χ
    rw [DirichletCharacter.conductor_inv, hAc] at h
    have e : A⁻¹ * χ = B := by rw [hχ, inv_mul_cancel_left]
    rw [e, hBc] at h
    exact hcop.symm.dvd_of_dvd_mul_left (h.trans (Nat.lcm_dvd_mul _ _))
  exact Nat.dvd_antisymm χ.conductor_dvd_level (hcop.mul_dvd_of_dvd_of_dvd h1 h2)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.EisSlash
section
noncomputable section

open CongruenceSubgroup UpperHalfPlane
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Sd

private def slashEquiv (N : ℕ) (x : ZMod N) (a b c d : ℤ) (hdet : a * d - b * c = 1) (hc : (c : ZMod N) = 0) :
    {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x} ≃
      {v : ℤ × ℤ // (v.1 : ZMod N) = 0 ∧ (v.2 : ZMod N) = x * (d : ZMod N)} where
  toFun v := ⟨(v.1.1 * a + v.1.2 * c, v.1.1 * b + v.1.2 * d), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    constructor <;> simp [h1, h2, hc]⟩
  invFun v := ⟨(v.1.1 * d - v.1.2 * c, -(v.1.1 * b) + v.1.2 * a), by
    obtain ⟨⟨m, n⟩, h1, h2⟩ := v
    simp only at h1 h2
    have h : (a : ZMod N) * d = 1 := by
      have := congrArg (Int.cast : ℤ → ZMod N) hdet
      push_cast at this
      simpa [hc] using this
    constructor
    · simp [h1, hc]
    · push_cast
      rw [h1, h2]
      linear_combination x * h⟩
  left_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * a + n * c) * d - (m * b + n * d) * c = m
      linear_combination m * hdet
    · show -((m * a + n * c) * b) + (m * b + n * d) * a = n
      linear_combination n * hdet
  right_inv v := by
    obtain ⟨⟨m, n⟩, h⟩ := v
    apply Subtype.ext
    apply Prod.ext
    · show (m * d - n * c) * a + (-(m * b) + n * a) * c = m
      linear_combination m * hdet
    · show (m * d - n * c) * b + (-(m * b) + n * a) * d = n
      linear_combination n * hdet

theorem eisSlash : EisSlash := by
  intro N k _ _ a γ hγ
  have hdet : γ 0 0 * γ 1 1 - γ 0 1 * γ 1 0 = 1 := by
    have := γ.2
    rw [Matrix.det_fin_two] at this
    exact this
  have hc : ((γ 1 0 : ℤ) : ZMod N) = 0 := Gamma0_mem.mp hγ
  ext z
  rw [ModularForm.SL_slash_apply]
  have hden : denom (Matrix.SpecialLinearGroup.toGL ((Matrix.SpecialLinearGroup.map (Int.castRingHom ℝ)) γ)) (z : ℂ) = (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) := by
    simp [denom]
  have hsm : ((γ • z : ℍ) : ℂ) = ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) := by
    rw [UpperHalfPlane.coe_specialLinearGroup_apply]
    simp
  have hne : (γ 1 0 : ℂ) * z + (γ 1 1 : ℂ) ≠ 0 := by
    rw [← hden]
    exact denom_ne_zero _ z
  have key : ((γ 0 0 : ℂ) * z + (γ 0 1 : ℂ)) / ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) * ((γ 1 0 : ℂ) * z + (γ 1 1 : ℂ)) = (γ 0 0 : ℂ) * z + (γ 0 1 : ℂ) := div_mul_cancel₀ _ hne
  rw [hden]
  unfold eisFun
  rw [hsm, mul_assoc, ← tsum_mul_right]
  rw [← (slashEquiv N a (γ 0 0) (γ 0 1) (γ 1 0) (γ 1 1) hdet hc).tsum_eq]
  congr 1
  congr 1
  funext v
  rw [← mul_zpow]
  congr 1
  simp only [slashEquiv, Equiv.coe_fn_mk]
  push_cast
  linear_combination ((v : ℤ × ℤ).1 : ℂ) * key

end UpperTheory.V.Sd
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.FinDim
section
open CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af Filter Asymptotics Function
open scoped MatrixGroups ModularForm Topology

private theorem fd_bigO {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ) (h : ∀ n < m, (qExpansion 1 f).coeff n = 0) :
    (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m := by
  have hF := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have hle : ((m : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    rw [natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF]
    intro i hi
    have hc := h i hi
    rw [qExpansion_coeff] at hc
    simpa [Nat.factorial_ne_zero] using hc
  obtain ⟨g, hg, hev⟩ := (natCast_le_analyticOrderAt hF).mp hle
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hev' : ∀ᶠ τ : ℍ in atImInfty,
      Periodic.qParam 1 τ ^ m * g (Periodic.qParam 1 τ) = f τ := by
    filter_upwards [hq.eventually hev] with τ hτ
    rw [← SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero, hτ, sub_zero, smul_eq_mul]
  have hb : (fun τ : ℍ => g (Periodic.qParam 1 τ)) =O[atImInfty] (fun _ => (1 : ℂ)) :=
    (hg.continuousAt.tendsto.comp hq).isBigO_one ℂ
  have key := (isBigO_refl (fun τ : ℍ => Periodic.qParam 1 τ ^ m) atImInfty).mul hb
  simp only [mul_one] at key
  exact key.congr' hev' (Eventually.of_forall fun _ => rfl)

private theorem fd_order {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (f : F) (m : ℕ)
    (h : (f : ℍ → ℂ) =O[atImInfty] fun τ : ℍ => Periodic.qParam 1 τ ^ m) :
    ∀ n < m, (qExpansion 1 f).coeff n = 0 := by
  have hF := ModularFormClass.analyticAt_cuspFunction_zero f one_pos hΓ
  have hq := qParam_tendsto_atImInfty (h := 1) one_pos
  have hle : ((m : ℕ) : ℕ∞) ≤ analyticOrderAt (cuspFunction 1 f) 0 := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
    rw [← hn, Nat.cast_lt] at hlt
    obtain ⟨g, hg, hg0, hev⟩ := hF.analyticOrderAt_eq_natCast.mp hn.symm
    obtain ⟨C, hC⟩ := h.bound
    have key : ∀ᶠ τ : ℍ in atImInfty,
        ‖g (Periodic.qParam 1 τ)‖ ≤ C * ‖Periodic.qParam 1 τ‖ ^ (m - n) := by
      filter_upwards [hC, hq.eventually hev] with τ h1 h2
      rw [← SlashInvariantFormClass.eq_cuspFunction f τ hΓ one_ne_zero, h2, sub_zero,
        smul_eq_mul, norm_mul, norm_pow, norm_pow] at h1
      have hpos : 0 < ‖Periodic.qParam 1 (τ : ℂ)‖ ^ n :=
        pow_pos (norm_pos_iff.mpr (Periodic.qParam_ne_zero _)) n
      have hsplit : ‖Periodic.qParam 1 (τ : ℂ)‖ ^ m =
          ‖Periodic.qParam 1 (τ : ℂ)‖ ^ n * ‖Periodic.qParam 1 (τ : ℂ)‖ ^ (m - n) := by
        rw [← pow_add, Nat.add_sub_cancel' hlt.le]
      rw [hsplit, mul_left_comm] at h1
      exact le_of_mul_le_mul_left h1 hpos
    have t1 : Tendsto (fun τ : ℍ => ‖g (Periodic.qParam 1 τ)‖) atImInfty (𝓝 ‖g 0‖) :=
      (hg.continuousAt.tendsto.comp hq).norm
    have t2 : Tendsto (fun τ : ℍ => C * ‖Periodic.qParam 1 τ‖ ^ (m - n)) atImInfty
        (𝓝 (C * ‖(0 : ℂ)‖ ^ (m - n))) :=
      (hq.norm.pow (m - n)).const_mul C
    have hlim := le_of_tendsto_of_tendsto t1 t2 key
    rw [norm_zero, zero_pow (by omega), mul_zero] at hlim
    exact hg0 (norm_le_zero_iff.mp hlim)
  intro n hn
  have hz := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero hF).mp hle n hn
  simp [qExpansion_coeff, hz]

private theorem fd_norm {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {k : ℤ} [ModularFormClass F Γ k]
    [Γ.IsArithmetic] (f : F) : (ModularForm.norm 𝒮ℒ f : ℍ → ℂ) =O[atImInfty] (f : ℍ → ℂ) := by
  letI := Fintype.ofFinite ((𝒮ℒ) ⧸ Γ.subgroupOf 𝒮ℒ)
  classical
  have hb : ∀ q : (𝒮ℒ) ⧸ Γ.subgroupOf 𝒮ℒ,
      SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q =O[atImInfty] (fun _ => (1 : ℂ)) := by
    intro q
    induction q using Quotient.inductionOn with
    | h r =>
      obtain ⟨_, γ, rfl⟩ := r
      rw [SlashInvariantForm.quotientFunc_mk]
      have hbd := ModularFormClass.bdd_at_infty_slash f γ⁻¹
      rw [ModularForm.SL_slash] at hbd
      have e : (Matrix.SpecialLinearGroup.mapGL ℝ γ)⁻¹ = Matrix.SpecialLinearGroup.mapGL ℝ γ⁻¹ :=
        (map_inv _ _).symm
      refine IsBigO.trans ?_ (isBigO_const_const (1 : ℝ) (one_ne_zero (α := ℂ)) atImInfty)
      simp only [Subgroup.coe_mk, e]
      exact hbd
  have hP : (fun τ => ∏ q ∈ Finset.univ.erase ⟦(1 : 𝒮ℒ)⟧,
      SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q τ) =O[atImInfty] (fun _ => (1 : ℂ)) := by
    simpa using IsBigO.finsetProd (s := Finset.univ.erase ⟦(1 : 𝒮ℒ)⟧) (fun q _ => hb q)
  refine IsBigO.congr ((isBigO_refl (⇑f) atImInfty).mul hP) (fun τ => ?_) (fun τ => mul_one _)
  rw [ModularForm.coe_norm, Finset.prod_apply,
    ← Finset.mul_prod_erase Finset.univ (fun q => SlashInvariantForm.quotientFunc (𝒢 := Γ) (k := k) f q τ)
      (Finset.mem_univ ⟦(1 : 𝒮ℒ)⟧)]
  simp [SlashInvariantForm.quotientFunc_mk]
  left
  convert rfl

private theorem fd_sturm {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic] (hΓ : (1 : ℝ) ∈ Γ.strictPeriods) (k : ℤ) :
    ∃ m : ℕ, ∀ f : CuspForm Γ k, (∀ n < m, (qExpansion 1 f).coeff n = 0) → f = 0 := by
  refine ⟨(k * Nat.card (𝒮ℒ ⧸ (Γ.subgroupOf 𝒮ℒ))).toNat / 12 + 1, fun f hf => ?_⟩
  have h1 := fd_order one_mem_strictPeriods_SL (ModularForm.norm 𝒮ℒ f) _ ((fd_norm f).trans (fd_bigO hΓ f _ hf))
  have h2 : ModularForm.norm 𝒮ℒ f = 0 := by
    apply ModularForm.sturm_bound_levelOne
    refine lt_of_lt_of_le ?_ (PowerSeries.nat_le_order _ _ h1)
    exact_mod_cast Nat.lt_succ_self _
  rw [ModularForm.norm_eq_zero_iff] at h2
  ext τ
  simpa using congr_fun h2 τ

theorem UpperTheory.V.Sd.finDim :
    UpperTheory.V.Sd.FinDim := by
  intro N k _
  have hΓ : (1 : ℝ) ∈ (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)).strictPeriods := by
    simp
  obtain ⟨m, hm⟩ := fd_sturm hΓ (k : ℤ)
  refine ⟨?_, fun f hf => hm f fun n _ => ?_⟩
  · let L : CuspForm (Subgroup.map (Matrix.SpecialLinearGroup.mapGL ℝ) (Gamma1 N)) (k : ℤ) →ₗ[ℂ]
        (Fin m → ℂ) :=
      { toFun := fun f i => (qExpansion 1 f).coeff i
        map_add' := fun f g => by
          ext i
          simp only [CuspForm.coe_add, ModularForm.qExpansion_add one_pos hΓ f g, map_add (f := _),
            Pi.add_apply]
        map_smul' := fun c f => by
          ext i
          simp only [CuspForm.coe_smul, ModularForm.qExpansion_smul one_pos hΓ c f,
            PowerSeries.coeff_smul, smul_eq_mul, Pi.smul_apply, RingHom.id_apply] }
    refine Module.Finite.of_injective L fun f g hfg => ?_
    have hfg0 : f - g = 0 := hm (f - g) fun n hn => by
      have hc := congrFun hfg ⟨n, hn⟩
      simp only [L, LinearMap.coe_mk, AddHom.coe_mk] at hc
      rw [CuspForm.coe_sub, ModularForm.qExpansion_sub one_pos hΓ f g, map_sub, hc, sub_self]
    exact sub_eq_zero.mp hfg0
  · rcases Nat.eq_zero_or_pos n with rfl | hn
    · exact CuspFormClass.qExpansion_coeff_zero f one_pos hΓ
    · exact hf n hn
end

