module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RTwist
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0022

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LevelVec
section
open NumberField Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Sd UpperTheory.V.Af UpperTheory.V.Af.Nf Filter Topology

namespace UpperTheory.V.Br

private theorem lv_zero {x : Af ℚ} (h : ∀ n : ℕ, ∃ y ∈ Ohat ℚ, x = (n.factorial : ℕ) * y) : x = 0 := by
  by_contra hx
  have hc : IsCompact (Ohat ℚ : Set (Af ℚ)) := by
    convert GroundTheory.Global.isCompact_integralFiniteAdeles ℚ using 1
    exact Set.ext fun _ => mem_Ohat
  have key : ∀ᶠ d in 𝓝 (0 : Af ℚ), ∀ z ∈ (Ohat ℚ : Set (Af ℚ)), x ≠ d * z :=
    hc.eventually_forall_of_forall_eventually fun z _ =>
      (isOpen_ne_fun continuous_const (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using hx)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists
  obtain ⟨y, hy, e⟩ := h n
  exact hn y hy e

private theorem lv_KLev {U : Set (GL (Fin 2) (Af ℚ))} (hU : IsOpen U) (h1 : 1 ∈ U) :
    ∃ M : ℕ, 1 ≤ M ∧ ∀ g ∈ KLev ℚ 2 M, g ∈ U := by
  by_contra h
  push Not at h
  have hcl : ∀ n : ℕ, IsClosed ((KLev ℚ 2 n.factorial : Set (GL (Fin 2) (Af ℚ))) ∩ Uᶜ) := fun n =>
    (Subgroup.isClosed_of_isOpen _ (isOpen_KLev n.factorial_pos)).inter hU.isClosed_compl
  obtain ⟨g, hg⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
    (fun n : ℕ => (KLev ℚ 2 n.factorial : Set (GL (Fin 2) (Af ℚ))) ∩ Uᶜ)
    (fun n => Set.inter_subset_inter_left _ (KLev_le_of_dvd (Nat.factorial_dvd_factorial n.le_succ)))
    (fun n => h _ n.factorial_pos) ((isCompact_KLev (Nat.factorial_pos 0)).inter_right hU.isClosed_compl) hcl
  rw [Set.mem_iInter] at hg
  refine (hg 0).2 ?_
  rwa [show g = 1 from Units.ext (Matrix.ext fun a b => sub_eq_zero.1 (lv_zero fun n => (mem_KLev.1 (hg n).1).2.2 a b))]

private theorem lv_eig {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (ρ : G →* Module.End ℂ V) {N : ℕ} [NeZero N]
    (δ : G →* ZMod N) (W : Submodule ℂ V) (hW : ∀ g, ∀ w ∈ W, ρ g w ∈ W) {v : V} (hv : v ∈ W) (h0 : v ≠ 0)
    (hk : ∀ g, δ g = 1 → ρ g v = v) :
    ∃ (χ : DirichletCharacter ℂ N), ∃ w ∈ W, w ≠ 0 ∧ ∀ g, χ (δ g) • ρ g w = w := by
  classical
  let f : ZMod N → V := fun a => if h : ∃ g, δ g = a then ρ h.choose v else 0
  have hf : ∀ g, f (δ g) = ρ g v := fun g => by
    have h : ∃ g', δ g' = δ g := ⟨g, rfl⟩
    have := hk (g⁻¹ * h.choose) (by rw [map_mul, h.choose_spec, ← map_mul, inv_mul_cancel, map_one])
    simp only [f, dif_pos h]
    conv_rhs => rw [← this]
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
  have hm : ∀ g a, ρ g (f a) = f (δ g * a) := fun g a => by
    by_cases h : ∃ g, δ g = a
    · obtain ⟨g', rfl⟩ := h
      rw [← map_mul, hf, hf, map_mul, Module.End.mul_apply]
    · have h' : ¬ ∃ g', δ g' = δ g * a := fun ⟨g', e⟩ => h ⟨g⁻¹ * g', by
        rw [map_mul, e, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul]⟩
      simp only [f, dif_neg h, dif_neg h', map_zero]
  have hfW : ∀ a, f a ∈ W := fun a => by
    simp only [f]; split_ifs
    · exact hW _ _ hv
    · exact W.zero_mem
  have hs : ∑ χ : DirichletCharacter ℂ N, ∑ a, χ a • f a ≠ 0 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, DirichletCharacter.sum_characters_eq, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, if_true]
    rw [← map_one δ, hf, map_one]
    exact smul_ne_zero (Nat.cast_ne_zero.2 (Nat.totient_pos.2 (NeZero.pos N)).ne') h0
  obtain ⟨χ, -, hχ⟩ := Finset.exists_ne_zero_of_sum_ne_zero hs
  refine ⟨χ, _, W.sum_mem fun a _ => W.smul_mem _ (hfW a), hχ, fun g => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, Finset.smul_sum]
  refine Fintype.sum_equiv (δ.toHomUnits g).mulLeft _ _ fun a => ?_
  rw [map_smul, hm, smul_smul, ← map_mul]
  rfl

private theorem lv_red {M : ℕ} (hM : 1 ≤ M) : ∃ r : ↥(Ohat ℚ) →* ZMod M,
    ∀ (x : ↥(Ohat ℚ)) (d : ℤ), r x = d ↔ ∃ y ∈ Ohat ℚ, (x : Af ℚ) - d = M * y := by
  have hM' : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hi : algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * M = 1 := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ)), ← map_mul, inv_mul_cancel₀ hM', map_one]
  have uq : ∀ {x : Af ℚ} {d e : ℤ}, (∃ y ∈ Ohat ℚ, x - d = M * y) → (∃ y ∈ Ohat ℚ, x - e = M * y) → (d : ZMod M) = e := by
    rintro x d e ⟨y, hy, hd⟩ ⟨z, hz, he⟩
    have h1 : algebraMap ℚ (Af ℚ) ((M : ℚ)⁻¹ * ((e : ℚ) - d)) = y - z := by
      rw [map_mul, map_sub, map_intCast, map_intCast]
      linear_combination algebraMap ℚ (Af ℚ) (M : ℚ)⁻¹ * (hd - he) + (y - z) * hi
    obtain ⟨n, hn⟩ := ratAd.2.2 _ (h1 ▸ sub_mem hy hz)
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub]
    refine ⟨n, ?_⟩
    rw [inv_mul_eq_iff_eq_mul₀ hM'] at hn
    exact_mod_cast hn
  choose f hf using fun x : ↥(Ohat ℚ) => ratAd.2.1 M hM x x.2
  refine ⟨⟨⟨fun x => f x, ?_⟩, fun a b => ?_⟩, fun x d => ⟨fun h => ?_, uq (hf x)⟩⟩
  · simpa using uq (e := 1) (hf 1) ⟨0, zero_mem _, by simp⟩
  · obtain ⟨y, hy, h1⟩ := hf a
    obtain ⟨z, hz, h2⟩ := hf b
    have := uq (e := f a * f b) (hf (a * b)) ⟨a * z + f b * y,
      add_mem (mul_mem a.2 hz) (mul_mem (intCast_mem _ _) hy), by
        rw [Subring.coe_mul, Int.cast_mul]
        linear_combination (a : Af ℚ) * h2 + (f b : Af ℚ) * h1⟩
    simpa using this
  · obtain ⟨n, hn⟩ := (ZMod.intCast_eq_intCast_iff_dvd_sub _ _ _).1 h
    obtain ⟨y, hy, h1⟩ := hf x
    have hn' : (d : Af ℚ) - f x = M * n := by exact_mod_cast congrArg (Int.cast : ℤ → Af ℚ) hn
    exact ⟨y - n, sub_mem hy (intCast_mem _ _), by linear_combination h1 - hn'⟩

private theorem lv_det {N : ℕ} {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G N) :
    ((Matrix.GeneralLinearGroup.det g : (Af ℚ)ˣ) : Af ℚ) ∈ Ohat ℚ := by
  have h := ((memK N g).1 hg).1
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  exact sub_mem (mul_mem (h 0 0) (h 1 1)) (mul_mem (h 0 1) (h 1 0))

private theorem lv_conj {R : Type} [CommRing R] (m : Rˣ) (g : GL (Fin 2) R) :
    (aff m 0 * g * (aff m 0)⁻¹).val = !![g 0 0, m * g 0 1; g 1 0 * (m⁻¹ : Rˣ), g 1 1] := by
  change (aff m 0).val * g.val * (aff m 0).inv = _
  ext i j
  fin_cases i <;> fin_cases j <;> simp [aff, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_succ]
  rw [mul_right_comm, Units.mul_inv, one_mul]

private theorem lv_int {M : ℕ} {m : (Af ℚ)ˣ} (hm : (m : Af ℚ) = M) {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G (M * M)) (a b : Fin 2) :
    (aff m 0 * g * (aff m 0)⁻¹ : GL (Fin 2) (Af ℚ)) a b ∈ Ohat ℚ := by
  obtain ⟨h, -, ⟨y, hy, e⟩, -⟩ := (memK _ g).1 hg
  revert a b
  rw [lv_conj]
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨h 0 0, mul_mem (hm ▸ natCast_mem _ M) (h 0 1)⟩,
    Fin.forall_fin_two.2 ⟨?_, h 1 1⟩⟩
  change g 1 0 * (m⁻¹ : (Af ℚ)ˣ) ∈ _
  rw [e, Nat.cast_mul, ← hm, mul_assoc, mul_assoc, mul_comm, mul_assoc, mul_assoc, Units.inv_mul, mul_one]
  exact mul_mem (hm ▸ natCast_mem _ M) hy

private theorem lv_mem {M : ℕ} {m : (Af ℚ)ˣ} (hm : (m : Af ℚ) = M) {g : GL (Fin 2) (Af ℚ)} (hg : g ∈ K1G (M * M))
    (hd : ∃ y ∈ Ohat ℚ, ((Matrix.GeneralLinearGroup.det g : (Af ℚ)ˣ) : Af ℚ) - (1 : ℤ) = (M * M : ℕ) * y) :
    aff m 0 * g * (aff m 0)⁻¹ ∈ KLev ℚ 2 M := by
  refine mem_KLev.2 ⟨lv_int hm hg, fun a b => ?_, ?_⟩
  · have := lv_int hm (inv_mem hg) a b
    rwa [show aff m 0 * g⁻¹ * (aff m 0)⁻¹ = (aff m 0 * g * (aff m 0)⁻¹)⁻¹ by group] at this
  obtain ⟨h, -, ⟨w, hw, e1⟩, z, hz, e2⟩ := (memK _ g).1 hg
  obtain ⟨y, hy, e3⟩ := hd
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two, Int.cast_one] at e3
  rw [Nat.cast_mul] at e1 e2 e3
  have hM := natCast_mem (Ohat ℚ) M
  rw [lv_conj]
  refine Fin.forall_fin_two.2 ⟨Fin.forall_fin_two.2 ⟨⟨M * (y - g 0 0 * z + g 0 1 * w),
    mul_mem hM (add_mem (sub_mem hy (mul_mem (h 0 0) hz)) (mul_mem (h 0 1) hw)), ?_⟩, ⟨_, h 0 1, ?_⟩⟩,
    Fin.forall_fin_two.2 ⟨⟨w, hw, ?_⟩, ⟨M * z, mul_mem hM hz, ?_⟩⟩⟩
  · change g 0 0 - 1 = _
    linear_combination e3 - g 0 0 * e2 + g 0 1 * e1
  · change m * g 0 1 - 0 = _
    rw [hm, sub_zero]
  · change g 1 0 * (m⁻¹ : (Af ℚ)ˣ) - 0 = _
    rw [e1, ← hm]
    linear_combination (m : Af ℚ) * w * m.mul_inv
  · change g 1 1 - 1 = _
    rw [e2, mul_assoc]

private noncomputable def lowSub (k : ℕ) : Submodule ℂ (TR.Sm ℚ 2) where
  carrier := {φ | IsLow k φ}
  zero_mem' := ⟨fun _ => by simp, fun _ => by simp, fun _ => by simp⟩
  add_mem' {a b} ha hb :=
    ⟨fun v => by simp only [map_add (f := _)]; linear_combination (norm := module) ha.wt v + hb.wt v,
      fun v => by simp only [map_add (f := _)]; linear_combination (norm := module) ha.low v + hb.low v,
      fun v => by simp only [map_add (f := _)]; linear_combination (norm := module) ha.one v + hb.one v⟩
  smul_mem' c a ha :=
    ⟨fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.wt v,
      fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.low v,
      fun v => by simp only [map_smul]; linear_combination (norm := module) c • ha.one v⟩

private theorem lv_map {k : ℕ} (T : TR.Sm ℚ 2 →ₗ[ℂ] TR.Sm ℚ 2) (hT : ∀ v i j φ, TR.Eop v i j (T φ) = T (TR.Eop v i j φ))
    {φ : TR.Sm ℚ 2} (h : IsLow k φ) : IsLow k (T φ) :=
  ⟨fun v => by rw [hT, hT, ← map_sub, h.wt, map_smul],
    fun v => by rw [hT, hT, hT, hT, ← map_sub, h.low, map_smul, map_add (f := _)],
    fun v => by rw [hT, hT, ← map_add (f := _), h.one, map_zero]⟩

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.levelVec :
    UpperTheory.V.Br.LevelVec := by
  rintro k π ⟨φ, hφ, h0, hl⟩
  obtain ⟨M, hM, hK⟩ := lv_KLev (π.cusp φ hφ).1.level (by simp)
  have hN : 1 ≤ M * M := Nat.mul_pos hM hM
  haveI : NeZero (M * M) := ⟨by omega⟩
  obtain ⟨m, hm⟩ : IsUnit (M : Af ℚ) := by
    rw [← map_natCast (algebraMap ℚ (Af ℚ))]
    exact (IsUnit.mk0 _ (Nat.cast_ne_zero.2 (by omega))).map _
  obtain ⟨r, hr⟩ := lv_red hN
  let j : ↥(K1G (M * M)) →* ↥(Ohat ℚ) :=
    { toFun := fun g => ⟨_, lv_det g.2⟩
      map_one' := Subtype.ext (congrArg Units.val (map_one Matrix.GeneralLinearGroup.det))
      map_mul' := fun a b => Subtype.ext (congrArg Units.val (map_mul Matrix.GeneralLinearGroup.det a.1 b.1)) }
  have hW : ∀ g, ∀ w ∈ π.V ⊓ lowSub k, TR.finRep ℚ 2 g w ∈ π.V ⊓ lowSub k := fun g w hw =>
    ⟨π.stable (.fin g) w hw.1, lv_map _ (fun v a b ψ => LinearMap.congr_fun (TR.lie_rt_fin _ g) ψ) hw.2⟩
  obtain ⟨χ, w, hw, hw0, hχ⟩ := lv_eig ((TR.finRep ℚ 2).comp (K1G (M * M)).subtype) (r.comp j) (π.V ⊓ lowSub k)
    (fun g => hW g.1) (hW (aff m 0)⁻¹ φ ⟨hφ, hl⟩)
    (fun h => h0 (by
      have := congrArg (TR.finRep ℚ 2 (aff m 0)) h
      rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, map_zero] at this))
    (fun g hg => by
      have h1 : TR.finRep ℚ 2 _ φ = φ := hK _ (lv_mem hm g.2 ((hr (j g) 1).1 (by rw [Int.cast_one]; exact hg)))
      change TR.finRep ℚ 2 g.1 (TR.finRep ℚ 2 _ φ) = _
      conv_rhs => rw [← h1]
      rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, ← mul_assoc, inv_mul_cancel_left])
  obtain ⟨ν, hν⟩ := dirChar (M * M) hN χ⁻¹
  have he : ∀ v, TR.expo ν v = 0 := fun v => TR.expo_eq_of_exp ν v 0 fun t => by
    rw [zero_mul, Complex.exp_zero]
    exact congrArg Units.val (hν.pos _ fun _ => Real.exp_pos _)
  refine ⟨M * M, χ⁻¹, ν, hN, hν, TR.mulChi 2 ν w, ⟨w, hw.1, rfl⟩, (TR.mulChi 2 ν).map_ne_zero_iff.2 hw0,
    lv_map (TR.mulChi 2 ν).toLinearMap (fun v a b ψ => ?_) hw.2, fun u hu => ?_⟩
  · refine (TR.Eop_mulChi ν v a b ψ).trans ?_
    rw [he, ite_self, zero_smul, add_zero]
    rfl
  · refine (TR.rt_mulChi ν (finGL ℚ 2 u) w).trans (congrArg _ ?_)
    obtain ⟨d, hd⟩ := ratAd.2.1 _ hN _ (lv_det hu)
    have h1 := hν.unit (Matrix.GeneralLinearGroup.det u) ⟨lv_det hu, by rw [← map_inv]; exact lv_det (inv_mem hu)⟩ d hd
    have h2 : chiDet 2 ν (finGL ℚ 2 u) = ν.1 (finId ℚ (Matrix.GeneralLinearGroup.det u)) := congrArg ν.1 (TR.det_finGL u)
    rw [MulChar.inv_apply_eq_inv', ← div_eq_mul_inv] at h1
    rw [h2, eq_of_div_eq_one h1, ← (hr (j ⟨u, hu⟩) d).2 hd]
    exact hχ ⟨u, hu⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.LieX0EqRaisingLowering
section
open NumberField GlobalTheory.CuspRep Matrix UpperTheory.V

namespace UpperTheory.V.Br.WeightVectorLie

variable {F : Type} [Field F] [NumberField F]

private noncomputable def rot (t : ℝ) : TR.Kinf F 2 :=
  ⟨!![fun _ => Real.cos t, fun _ => Real.sin t; fun _ => -Real.sin t, fun _ => Real.cos t], by
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j v
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_succ, Matrix.star_apply] <;>
      nlinarith [Real.sin_sq_add_cos_sq t]⟩

omit [NumberField F] in
private theorem rot_zero : rot 0 = (1 : TR.Kinf F 2) := by
  ext i j v
  fin_cases i <;> fin_cases j <;> simp [rot]

private noncomputable def X0 : TR.Lie F 2 := TR.toL !![0, 1; -1, 0]

private theorem lie_X0_eq_raising_lowering [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (v : InfinitePlace F) (φ : TR.Sm F 2) :
    TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = TR.lie F 2 X0 φ := by
  unfold TR.Eop
  rw [← LinearMap.sub_apply, ← map_sub]
  congr 2
  ext i j u
  obtain rfl : u = v := Subsingleton.elim _ _
  fin_cases i <;> fin_cases j <;> simp [X0]

private theorem rot_deriv : HasDerivAt (fun t : ℝ => TR.toL (Unitary.toUnits (rot (F := F) t)).val) X0 0 := by
  refine hasDerivAt_pi.2 fun i => hasDerivAt_pi.2 fun j => hasDerivAt_pi.2 fun v => ?_
  fin_cases i <;> fin_cases j
  · simpa [X0, rot] using Real.hasDerivAt_cos 0
  · simpa [X0, rot] using Real.hasDerivAt_sin 0
  · simpa [X0, rot] using (Real.hasDerivAt_sin 0).fun_neg
  · simpa [X0, rot] using Real.hasDerivAt_cos 0

private theorem lie_mem [IsTotallyReal F] (U : Submodule ℂ (TR.Sm F 2)) [FiniteDimensional ℂ U]
    (hU : ∀ k, ∀ ψ ∈ U, TR.cptRep F 2 k ψ ∈ U) (ψ : TR.Sm F 2) (hψ : ψ ∈ U) : TR.lie F 2 X0 ψ ∈ U := by
  let U' : Submodule ℂ (GA F 2 → ℂ) := U.map (TR.Sm F 2).subtype
  have hcl : IsClosed (U' : Set (GA F 2 → ℂ)) := U'.closed_of_finiteDimensional
  have key : ∀ g, HasDerivAt (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) ((TR.lie F 2 X0 ψ).1 g) 0 := fun g =>
    TR.hasDerivAt_curve ψ g (fun t => Unitary.toUnits (rot t)) X0 (by rw [rot_zero, map_one]) rot_deriv
  have hm : (TR.lie F 2 X0 ψ).1 ∈ U' := by
    refine hcl.mem_of_tendsto (b := nhdsWithin (0 : ℝ) {0}ᶜ)
      (f := fun t g => slope (fun t => (TR.cptRep F 2 (rot t) ψ).1 g) 0 t)
      (tendsto_pi_nhds.2 fun g => hasDerivAt_iff_tendsto_slope.1 (key g)) (Filter.Eventually.of_forall fun t => ?_)
    exact U'.smul_of_tower_mem ((t - 0)⁻¹ : ℝ)
      (U'.sub_mem (Submodule.mem_map_of_mem (hU (rot t) ψ hψ)) (Submodule.mem_map_of_mem (hU (rot 0) ψ hψ)))
  obtain ⟨χ, hχ, e⟩ := hm
  rwa [← Subtype.ext e]

private theorem eig_abs {G M : Type} [Group G] [AddCommGroup M] [Module ℂ M] (ρ : Representation ℂ G M) (D : Module.End ℂ M)
    (hD : ∀ U : Submodule ℂ M, FiniteDimensional ℂ U → (∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U) → ∀ ψ ∈ U, D ψ ∈ U)
    (V : Submodule ℂ M) (φ : M) (hφ0 : φ ≠ 0) (hV : ∀ k, ρ k φ ∈ V)
    (hf : FiniteDimensional ℂ (Submodule.span ℂ (Set.range fun k => ρ k φ))) :
    ∃ ψ ∈ V, ψ ≠ 0 ∧ ∃ z : ℂ, D ψ = z • ψ := by
  let U : Submodule ℂ M := Submodule.span ℂ (Set.range fun k => ρ k φ)
  have hUV : U ≤ V := Submodule.span_le.2 (by rintro _ ⟨k, rfl⟩; exact hV k)
  have hU : ∀ k, ∀ ψ ∈ U, ρ k ψ ∈ U := fun k ψ hψ => by
    have h : U ≤ U.comap (ρ k) := Submodule.span_le.2 (by
      rintro _ ⟨k', rfl⟩
      exact Submodule.subset_span ⟨k * k', by simp⟩)
    exact h hψ
  have hφU : φ ∈ U := Submodule.subset_span ⟨1, by simp⟩
  have : Nontrivial U := ⟨⟨⟨φ, hφU⟩, 0, fun h => hφ0 (congrArg Subtype.val h)⟩⟩
  obtain ⟨z, hz⟩ := Module.End.exists_eigenvalue (D.restrict (hD U hf hU))
  obtain ⟨ψ, hψ⟩ := hz.exists_hasEigenvector
  exact ⟨ψ.1, hUV ψ.2, fun h => hψ.2 (Subtype.ext h), z, congrArg Subtype.val hψ.apply_eq_smul⟩

private theorem act_cpt [IsTotallyReal F] (k : TR.Kinf F 2) : TR.act (.cpt k) = TR.cptRep F 2 k := by
  rw [TR.act]

private theorem eig [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (π : TR.CuspSub F 2) :
    ∃ φ ∈ π.V, φ ≠ 0 ∧ ∃ z : ℂ, ∀ v, TR.Eop v 0 1 φ - TR.Eop v 1 0 φ = z • φ := by
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot π.ne_bot
  obtain ⟨ψ, h1, h2, z, h3⟩ := eig_abs (TR.cptRep F 2) (TR.lie F 2 X0) (fun U _ hU => lie_mem U hU) π.V φ hφ0
    (fun k => by rw [← act_cpt]; exact π.stable _ φ hφ) (π.cusp φ hφ).1.kfin
  exact ⟨ψ, h1, h2, z, fun v => (lie_X0_eq_raising_lowering v ψ).trans h3⟩

private theorem int_of [IsTotallyReal F] [Subsingleton (InfinitePlace F)] (ψ : TR.Sm F 2) (h0 : ψ ≠ 0) (z : ℂ)
    (he : ∀ v, TR.Eop v 0 1 ψ - TR.Eop v 1 0 ψ = z • ψ) : ∃ n : ℤ, z = Complex.I * n := by
  have hr : IsRot (F := F) (fun _ => 2 * Real.pi) 1 := by
    ext i j v
    fin_cases i <;> fin_cases j <;> simp
  obtain ⟨g, hg⟩ : ∃ g, ψ.1 g ≠ 0 := by
    by_contra h
    push Not at h
    exact h0 (Subtype.ext (funext h))
  have h1 := rotEig F ψ z he _ _ hr g
  rw [map_one, mul_one] at h1
  have h2 : Complex.exp (z * (2 * Real.pi)) = 1 := by
    have h3 := mul_right_cancel₀ hg (h1.symm.trans (one_mul _).symm)
    have : Unique (InfinitePlace F) := uniqueOfSubsingleton (Classical.arbitrary _)
    simpa using h3
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.1 h2
  refine ⟨n, ?_⟩
  have hpi : (2 * Real.pi : ℂ) ≠ 0 := by simp [Real.pi_ne_zero]
  apply mul_right_cancel₀ hpi
  rw [hn]; ring

end UpperTheory.V.Br.WeightVectorLie

open UpperTheory.V.Br.WeightVectorLie in
theorem UpperTheory.V.Br.wtVec :
    UpperTheory.V.Br.WtVec := by
  intro π
  obtain ⟨φ, hφ, h0, z, he⟩ := eig π
  obtain ⟨n, rfl⟩ := int_of φ h0 z he
  exact ⟨φ, hφ, h0, n, he⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Sl2Low
section
namespace UpperTheory.V.Br

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {k : ℕ}

private theorem wt_low (hL : W * L - L * W = (-2 : ℂ) • L) {x : V} {n : ℤ} (hx : W x = (n : ℂ) • x) :
    W (L x) = ((n - 2 : ℤ) : ℂ) • L x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hL
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

private theorem cas (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W)) {x : V} {n : ℤ}
    (hx : W x = (n : ℂ) • x) :
    R (L x) = ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) • x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hC
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul,
    Module.End.one_apply] at h
  have e : R (L x) = (1 / 4 : ℂ) • (4 : ℂ) • R (L x) := by
    rw [smul_smul]; norm_num
  rw [e, h]
  push_cast
  module

private theorem bound (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    {x : V} (hx0 : x ≠ 0) {n : ℤ} (hx : W x = (n : ℂ) • x) : (k : ℤ) * (k - 2) ≤ n * (n - 2) := by
  by_contra hlt
  push_neg at hlt
  have hltR : (n : ℝ) * (n - 2) < (k : ℝ) * (k - 2) := by exact_mod_cast hlt
  set c : ℝ := ((k : ℝ) * (k - 2) - n * (n - 2)) / 4 with hc
  have hcpos : 0 < c := div_pos (by linarith) (by norm_num)
  have hcC : ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) = (c : ℂ) := by
    rw [hc]; push_cast; ring
  have hwl := wt_low hL hx
  have h1 : H x (L x) = 0 := by
    have e := hW x (L x)
    rw [hx, hwl] at e
    simp [map_smulₛₗ] at e
    rcases e with e | e
    · have h2 : (2 : ℂ) = 0 := by linear_combination e
      norm_num at h2
    · exact e
  have h2 : H (L x) x = 0 := by
    have e := hW (L x) x
    rw [hwl, hx] at e
    simp [map_smulₛₗ] at e
    exact e
  have h3 : H (L x) (L x) = -(c : ℂ) * H x x := by
    have e := hH x (L x)
    rw [cas hC hx, hcC] at e
    simp only [map_smul, smul_eq_mul] at e
    rw [e]; ring
  set s : ℂ := ((Real.sqrt c : ℝ) : ℂ) with hsdef
  have hs : (starRingEnd ℂ) s = s := Complex.conj_ofReal _
  have hss : s * s = (c : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hcpos.le]
  have hy : H (s • x + L x) (s • x + L x) = 0 := by
    simp only [map_add (f := _), LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hs,
      h1, h2, h3, RingHom.id_apply]
    ring_nf
    linear_combination (H x x) * hss
  have hy0 := h0 _ hy
  have hLx : L x = -(s • x) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy0)
  have e1 : W (L x) = -(s • ((n : ℂ) • x)) := by rw [hLx, map_neg, map_smul, hx]
  rw [hwl, hLx] at e1
  have key : ((2 : ℂ) * s) • x = 0 := by
    have e2 : ((2 : ℂ) * s) • x = (((n - 2 : ℤ) : ℂ) • -(s • x)) - (-(s • ((n : ℂ) • x))) := by
      push_cast; module
    rw [e2, e1, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    have hc0 : (c : ℂ) = 0 := by rw [← hss, hs0, mul_zero]
    have : c = 0 := by exact_mod_cast hc0
    linarith
  · exact hx0 h

private theorem descend (hk : 3 ≤ k) (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    (j : ℕ) : ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x → ∃ x, x ≠ 0 ∧ W x = (k : ℂ) • x ∧ L x = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx0 hx
  have hb := bound hL hC h0 hW hH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hj2 : 2 ≤ j := by
    by_contra h
    push_neg at h
    interval_cases j <;> (push_cast at hb; nlinarith)
  by_cases hL0 : L x = 0
  · refine ⟨x, hx0, ?_, hL0⟩
    have hc := cas hC hx
    rw [hL0, map_zero] at hc
    have hq : ((((k : ℤ) * (k - 2) - ((j : ℤ) : ℤ) * ((j : ℤ) - 2) : ℤ)) : ℂ) / 4 = 0 := by
      rcases smul_eq_zero.mp hc.symm with h | h
      · exact h
      · exact absurd h hx0
    have hq' : (k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0 := by
      have h4 : (((k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ) = 0 := by
        linear_combination 4 * hq
      exact_mod_cast h4
    have hf : ((k : ℤ) - j) * ((k : ℤ) + j - 2) = 0 := by linear_combination hq'
    have hjk : j = k := by
      rcases mul_eq_zero.mp hf with h | h
      · omega
      · omega
    rw [hx, hjk]
    simp
  · have hwl := wt_low hL hx
    refine ih (j - 2) (by omega) (L x) hL0 ?_
    rw [hwl, show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega]

end

theorem sl2Low : UpperTheory.V.Br.Sl2Low := by
  intro V _ _ W R L H k hk hR hL hC hC' h0 hW hRH hLH hex
  obtain ⟨x, hx0, n, hx⟩ := hex
  have hb := bound hL hC h0 hW hLH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hf : (n - k) * (n + k - 2) = n * (n - 2) - k * (k - 2) := by ring
  rcases le_or_gt (k : ℤ) n with hn | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j := ⟨n.toNat, by omega⟩
    obtain ⟨y, hy0, hy1, hy2⟩ := descend hk hL hC h0 hW hLH j x hx0 hx
    exact ⟨y, hy0, Or.inl ⟨hy1, hy2⟩⟩
  · have hn2 : n + k - 2 ≤ 0 := by nlinarith
    obtain ⟨j, hj⟩ : ∃ j : ℕ, -n = j := ⟨(-n).toNat, by omega⟩
    have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [show (-W) * R - R * (-W) = -(W * R - R * W) by noncomm_ring, hR]
      module
    have hC2 : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - ((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hC']
      congr 1
      rw [neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]
    have hx' : (-W) x = ((j : ℤ) : ℂ) • x := by
      rw [LinearMap.neg_apply, hx, ← neg_smul, ← hj]
      push_cast
      rfl
    obtain ⟨y, hy0, hy1, hy2⟩ :=
      descend (W := -W) (R := L) (L := R) (H := H) hk hL' hC2 h0 hW' hRH j x hx0 hx'
    refine ⟨y, hy0, Or.inr ⟨?_, hy2⟩⟩
    rw [neg_smul, ← hy1, LinearMap.neg_apply, neg_neg]

end UpperTheory.V.Br
end

