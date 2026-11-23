module

public import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.PhiIndep
public import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.BernsteinTheoremA.LeviTransposeDistributions.BoundOneTwo

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetPfTrGL
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.SplitWeil

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) : GL (Fin (n + 1)) k :=
  ⟨(h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ, ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ,
    by rw [← transpose_mul, Units.inv_mul, transpose_one],
    by rw [← transpose_mul, Units.mul_inv, transpose_one]⟩

omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem det_pfTrGL {n : ℕ} (h : GL (Fin (n + 1)) k) :
    GeneralLinearGroup.det (pfTrGL h) = GeneralLinearGroup.det h := by
  apply Units.ext
  simp [pfTrGL, GeneralLinearGroup.val_det_apply, det_transpose]


omit [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
theorem transpose_mulVec_dotProduct_inv_mulVec {n : ℕ} (h : GL (Fin (n + 1)) k) (x z : Vc k n) :
    ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ x) ⬝ᵥ
        (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z) = x ⬝ᵥ z := by
  rw [mulVec_transpose, dotProduct_mulVec, vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    vecMul_one]

variable (k) in
theorem pfAct : PfAct k := by
  intro mk bs ν hν ψ c hc n F hF h
  funext z
  have key := integral_comp_mulVec_eq_smul ν (pfTrGL h)
    (fun u => F (cj h⁻¹ z.1, u) * ((ψ (u ⬝ᵥ (((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) *ᵥ z.2)) : Circle) : ℂ))
  have hv : ((pfTrGL h : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ := rfl
  simp only [hv, transpose_mulVec_dotProduct_inv_mulVec, det_pfTrGL] at key
  simp only [GlobalTheory.SplitDict.pf]
  rw [key, Complex.real_smul, Complex.ofReal_inv]

end PositivityTheory.RgUd.AB.Pf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.DetUpdateRowOneLast
section
noncomputable section

open Matrix MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir GroundTheory.Automorphic.Whittaker

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem det_updateRow_one_last {n : ℕ} (v : Fin (n + 1) → k) :
    (updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) v).det = v (Fin.last n) := by
  rw [Matrix.det_of_lowerTriangular]
  · rw [Fin.prod_univ_castSucc]
    simp [Matrix.updateRow_apply, Fin.castSucc_ne_last]
  · intro i j hij
    have hij' : i < j := hij
    have hi : i ≠ Fin.last n := ne_of_lt (lt_of_lt_of_le hij' (Fin.le_last j))
    rw [Matrix.updateRow_ne hi, Matrix.one_apply_ne (ne_of_lt hij')]

theorem exists_last_row {n : ℕ} (w : Fin (n + 1) → k) (hw : w ≠ 0) :
    ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j := by
  obtain ⟨m, hm⟩ := Function.ne_iff.mp hw
  have hm' : w m ≠ 0 := by simpa using hm
  have hM : ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)
      (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))).det ≠ 0 := by
    rw [Matrix.det_permute', det_updateRow_one_last, Equiv.swap_apply_right]
    refine mul_ne_zero ?_ hm'
    rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.swap m (Fin.last n))) with h | h <;> simp [h]
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hM, fun j => ?_⟩
  show ((updateRow (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n)
      (fun j => w (Equiv.swap m (Fin.last n) j))).submatrix id (Equiv.swap m (Fin.last n))) (Fin.last n) j = w j
  simp [Matrix.submatrix_apply, Matrix.updateRow_self, Equiv.swap_apply_self]

theorem secSpec : SecSpec k := by
  intro n w hw j
  have h := exists_last_row w hw
  unfold sec
  rw [dite_eq_left h]
  exact h.choose_spec j

theorem cj_mul {n : ℕ} (a b : GL (Fin (n + 1)) k) (x : Mx k n) : cj (a * b) x = cj a (cj b x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem cj_one {n : ℕ} (x : Mx k n) : cj (1 : GL (Fin (n + 1)) k) x = x := by
  simp [cj]

def cjHomeo {n : ℕ} (g : GL (Fin (n + 1)) k) : Mx k n ≃ₜ Mx k n where
  toFun := cj g
  invFun := cj g⁻¹
  left_inv x := by rw [← cj_mul, inv_mul_cancel, cj_one]
  right_inv x := by rw [← cj_mul, mul_inv_cancel, cj_one]
  continuous_toFun := by unfold cj; fun_prop
  continuous_invFun := by unfold cj; fun_prop

theorem slice_cj_mem {n : ℕ} {F : Mx k n × Vc k n → ℂ} (hF : F ∈ SB (Mx k n × Vc k n)) (g : GL (Fin (n + 1)) k)
    (w : Vc k n) : (fun x => F (cj g x, w)) ∈ SB (Mx k n) := by
  change IsLocallyConstant F ∧ HasCompactSupport F at hF
  have hι : Topology.IsClosedEmbedding (fun y : Mx k n => (y, w)) := by
    refine ⟨isEmbedding_prodMkLeft w, ?_⟩
    have hr : Set.range (fun y : Mx k n => (y, w)) = Set.univ ×ˢ {w} := by
      ext ⟨a, b⟩
      simp [eq_comm]
    rw [hr]
    exact isClosed_univ.prod isClosed_singleton
  have hemb := hι.comp (cjHomeo g).isClosedEmbedding
  exact ⟨hF.1.comp_continuous hemb.continuous, hF.2.comp_isClosedEmbedding hemb⟩

theorem phiIndep : PhiIndep k := by
  intro n Λ hΛ F hF w hw s hs
  unfold phi
  rw [if_neg hw]
  have hrow : ∀ (g : GL (Fin (n + 1)) k) (j : Fin (n + 1)),
      (eLast k n ᵥ* (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k)) j = (g : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j := by
    intro g j
    simp [eLast, Matrix.vecMul, dotProduct, Pi.single_apply]
  have ht : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) (Fin.last n) j = w j :=
    secSpec n w hw
  have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)
      = eLast k n ᵥ* (s : Matrix (Fin (n + 1)) (Fin (n + 1)) k) := by
    funext j
    rw [hrow, hrow, ht, hs]
  have hp : sec w * s⁻¹ ∈ Mir k n := by
    change eLast k n ᵥ* ((sec w * s⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k) = eLast k n
    rw [Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, Units.mul_inv, Matrix.vecMul_one]
  have hf : (fun x => F (cj (sec w)⁻¹ x, w)) ∈ SB (Mx k n) := slice_cj_mem hF (sec w)⁻¹ w
  rw [← hΛ _ hp _ hf]
  congr 1
  funext x
  dsimp only [Function.comp_apply]
  rw [← cj_mul, inv_mul_cancel_left]

theorem phiLin : PhiLin k := by
  intro n Λ F _ G _ a b
  funext w
  unfold phi
  simp only [Pi.add_apply, Pi.smul_apply]
  split_ifs
  · simp
  · rw [← map_smul, ← map_smul, ← map_add (f := _)]
    congr 1

theorem phiEquiv : PhiEquiv k := by
  intro n Λ hΛ F hF h w
  by_cases hw : w = 0
  · subst hw
    simp [phi, Matrix.mulVec_zero]
  · have hw' : (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w ≠ 0 := by
      intro h0
      apply hw
      have e : ((h⁻¹ : GL (Fin (n + 1)) k) : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ
          ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w) = w := by
        rw [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, Units.mul_inv, Matrix.transpose_one, Matrix.one_mulVec]
      rw [← e, h0, Matrix.mulVec_zero]
    rw [phiIndep n Λ hΛ F hF _ hw' (sec w * h) ?_]
    · unfold phi
      rw [if_neg hw]
      congr 1
      funext x
      dsimp only
      rw [← cj_mul, _root_.mul_inv_rev]
    · intro j
      rw [Units.val_mul, Matrix.mul_apply]
      simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply]
      exact Finset.sum_congr rfl fun x _ => by rw [secSpec n w hw x, mul_comm]

theorem ltEquiv (hE : PhiEquiv k) : LtEquiv k := by
  intro _ _ ν _ n Λ hΛ F hF h
  unfold lt
  have e : ∀ w, phi Λ (fun q : Mx k n × Vc k n => F (cj h⁻¹ q.1, (h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ q.2)) w
      = phi Λ F ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ *ᵥ w) := fun w => hE n Λ hΛ F hF h w
  simp only [e]
  have hd : ((h : Matrix (Fin (n + 1)) (Fin (n + 1)) k)ᵀ).det ≠ 0 := by
    rw [Matrix.det_transpose]
    exact ((Matrix.isUnit_iff_isUnit_det _).mp h.isUnit).ne_zero
  have key := integral_comp_mulVec_eq_smul ν (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd) (fun v => phi Λ F v)
  have hdet : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hd)
      = Matrix.GeneralLinearGroup.det h := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
    exact Matrix.det_transpose _
  rw [hdet] at key
  exact key.trans (by simp [Complex.real_smul])

end PositivityTheory.RgUd.AB.Pf
end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TraceDistributionsGL.EventuallyConjGL
section
noncomputable section

open Matrix Topology Filter GlobalTheory.SplitWeil GlobalTheory.SplitWeil.FourierPi GlobalTheory.BZMir

namespace PositivityTheory.RgUd.AB.Pf

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}

namespace Near

theorem cj_mul (g h : GL (Fin (n + 1)) k) (x : Mx k n) : cj (g * h) x = cj g (cj h x) := by
  simp only [cj, _root_.mul_inv_rev, Units.val_mul, Matrix.mul_assoc]

theorem inv_cj (g : GL (Fin (n + 1)) k) (x : Mx k n) :
    ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * cj g x * (g : Mx k n) = x := by
  simp only [cj, ← Matrix.mul_assoc]
  rw [Matrix.mul_assoc _ _ (g : Mx k n)]
  simp [← Units.val_mul, Matrix.mul_assoc]

theorem eventually_conj {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ AB : Mx k n × Mx k n in 𝓝 (1, 1), ∀ y ∈ tsupport f, f (AB.1 * y * AB.2) = f y := by
  obtain ⟨hlc, hcs⟩ := hf
  apply hcs.eventually_forall_of_forall_eventually
  intro y _
  have hc : Continuous fun z : (Mx k n × Mx k n) × Mx k n => z.1.1 * z.2 * z.1.2 :=
    ((continuous_fst.fst).matrix_mul continuous_snd).matrix_mul continuous_fst.snd
  have h1 := (hlc.comp_continuous hc).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  have h2 := (hlc.comp_continuous continuous_snd).eventually_eq (((1 : Mx k n), (1 : Mx k n)), y)
  filter_upwards [h1, h2] with z hz1 hz2
  simp only [Function.comp_apply] at hz1 hz2
  rw [hz1, hz2]
  simp

def rE (w : Vc k n) : Mx k n := vecMulVec (eN k n) (w - eN k n)

theorem rE_mul (w : Vc k n) : rE w * rE w = (w (Fin.last n) - 1) • rE w := by
  unfold rE
  rw [Matrix.vecMulVec_mul_vecMulVec]
  have hd : (w - eN k n) ⬝ᵥ eN k n = w (Fin.last n) - 1 := by
    simp [eN, dotProduct_single]
  rw [hd]
  ext i j
  simp only [vecMulVec_apply, Pi.smul_apply, smul_eq_mul, Matrix.smul_apply]
  ring

def sw (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : GL (Fin (n + 1)) k :=
  ⟨1 + rE w, 1 - (w (Fin.last n))⁻¹ • rE w, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [add_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, Matrix.mul_smul, rE_mul,
      smul_smul, hc, sub_smul, one_smul]
    abel, by
    have hc : (w (Fin.last n))⁻¹ * (w (Fin.last n) - 1) = 1 - (w (Fin.last n))⁻¹ := by
      rw [mul_sub, inv_mul_cancel₀ hw, mul_one]
    rw [sub_mul, Matrix.one_mul, Matrix.smul_mul, Matrix.mul_add, Matrix.mul_one, rE_mul, smul_add, smul_smul, hc,
      sub_smul, one_smul]
    abel⟩

theorem sw_val (w : Vc k n) (hw : w (Fin.last n) ≠ 0) : ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) = 1 + rE w := rfl

theorem sw_last (w : Vc k n) (hw : w (Fin.last n) ≠ 0) (j : Fin (n + 1)) :
    ((sw w hw : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
  rw [sw_val]
  by_cases h : j = Fin.last n
  · subst h
    simp [rE, eN, vecMulVec]
  · have h' : Fin.last n ≠ j := fun e => h e.symm
    simp [rE, eN, vecMulVec, Matrix.one_apply, h, h']

end Near

private theorem conj_of_pair_lemma {f : Mx k n → ℂ} (g : GL (Fin (n + 1)) k)
    (h1 : ∀ y ∈ tsupport f, f ((g : Mx k n) * y * ((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n)) = f y)
    (h2 : ∀ y ∈ tsupport f, f (((g⁻¹ : GL (Fin (n + 1)) k) : Mx k n) * y * (g : Mx k n)) = f y) :
    ∀ x, f (cj g x) = f x := by
  intro x
  by_cases hx : x ∈ tsupport f
  · exact h1 x hx
  · have hx0 : f x = 0 := image_eq_zero_of_notMem_tsupport hx
    rw [hx0]
    by_contra hne
    have hy : cj g x ∈ tsupport f := subset_tsupport f hne
    have := h2 _ hy
    rw [Near.inv_cj] at this
    exact hne (this.symm.trans hx0)

private theorem near_lemma_2 {f : Mx k n → ℂ} (hf : f ∈ SB (Mx k n)) :
    ∀ᶠ w : Vc k n in 𝓝 (eN k n), ∀ hw : w (Fin.last n) ≠ 0,
      ∀ x, f (cj (Near.sw w hw)⁻¹ x) = f x := by
  have hr : Continuous (fun w : Vc k n => Near.rE w) := by
    refine continuous_matrix fun i j => ?_
    simp only [Near.rE, vecMulVec_apply]
    exact continuous_const.mul (((continuous_apply j).sub continuous_const))
  have h0 : Near.rE (eN k n) = 0 := by simp [Near.rE]
  have hi : Tendsto (fun w : Vc k n => (w (Fin.last n))⁻¹) (𝓝 (eN k n))
      (𝓝 ((eN k n (Fin.last n))⁻¹)) :=
    ((continuous_apply (Fin.last n)).tendsto _).inv₀ (by simp [eN])
  have hA : Tendsto (fun w : Vc k n => (1 : Mx k n) - (w (Fin.last n))⁻¹ • Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).sub (hi.smul (hr.tendsto (eN k n)))
    simpa [h0] using this
  have hB : Tendsto (fun w : Vc k n => (1 : Mx k n) + Near.rE w) (𝓝 (eN k n)) (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : Mx k n))).add (hr.tendsto (eN k n))
    simpa [h0] using this
  have hS := Near.eventually_conj hf
  filter_upwards [(hA.prodMk_nhds hB).eventually hS, (hB.prodMk_nhds hA).eventually hS] with w h1 h2 hw
  have eA : (((Near.sw w hw)⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 - (w (Fin.last n))⁻¹ • Near.rE w := rfl
  have eB : (((Near.sw w hw)⁻¹⁻¹ : GL (Fin (n + 1)) k) : Mx k n) = 1 + Near.rE w := by
    rw [inv_inv]; exact Near.sw_val w hw
  apply conj_of_pair_lemma
  · intro y hy
    rw [eA, eB]
    exact h1 y hy
  · intro y hy
    rw [eA, eB]
    exact h2 y hy

open Near in
theorem phiNear : PhiNear k := by
  intro n Λ hΛ f₀ hf₀
  have hne : ∀ᶠ w : Vc k n in 𝓝 (eN k n), w (Fin.last n) ≠ 0 :=
    ((continuous_apply (Fin.last n)).tendsto (eN k n)).eventually_ne (by simp [eN])
  have hev := hne.and (near_lemma_2 hf₀)
  have ht : Tendsto (fun v : Vc k n => eN k n + v) (𝓝 0) (𝓝 (eN k n)) := by
    have hc : Continuous (fun v : Vc k n => eN k n + v) := by fun_prop
    simpa using hc.tendsto (0 : Vc k n)
  have hU := ht.eventually hev
  obtain ⟨t, htU⟩ := exists_box_subset hU
  refine ⟨t, fun s hst => ?_⟩
  funext w
  by_cases hw : w - eN k n ∈ box (Fin (n + 1)) s
  · have hP := htU (hst hw)
    simp only [Set.mem_setOf_eq, add_sub_cancel] at hP
    obtain ⟨hl, hc⟩ := hP
    have hw0 : w ≠ 0 := by
      intro h
      apply hl
      simp [h]
    have hmem : w ∈ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_mem hmem]
    simp only [phi, if_neg hw0, Set.indicator_of_mem hmem, Pi.one_apply, mul_one]
    have hex : ∃ s : GL (Fin (n + 1)) k, ∀ j, (s : Mx k n) (Fin.last n) j = w j :=
      ⟨sw w hl, sw_last w hl⟩
    have hsec : ∀ j, ((sec w : GL (Fin (n + 1)) k) : Mx k n) (Fin.last n) j = w j := by
      simp only [sec, dif_pos hex]
      exact hex.choose_spec
    have hrow : ∀ M : Mx k n, eLast k n ᵥ* M = M (Fin.last n) := by
      intro M
      ext j
      simp [eLast, vecMul, dotProduct, Pi.single_apply]
    set p := sec w * (sw w hl)⁻¹ with hpdef
    have hp : p ∈ Mir k n := by
      show eLast k n ᵥ* ((p : GL (Fin (n + 1)) k) : Mx k n) = eLast k n
      have e1 : eLast k n ᵥ* ((sec w : GL (Fin (n + 1)) k) : Mx k n)
          = eLast k n ᵥ* ((sw w hl : GL (Fin (n + 1)) k) : Mx k n) := by
        rw [hrow, hrow]
        funext j
        rw [hsec j, sw_last w hl j]
      rw [hpdef, Units.val_mul, ← Matrix.vecMul_vecMul, e1, Matrix.vecMul_vecMul, ← Units.val_mul,
        mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
    have hsecp : sec w = p * sw w hl := by simp [hpdef]
    have hfun : (fun x : Mx k n => f₀ (cj (sec w)⁻¹ x)) = f₀ ∘ cj p⁻¹ := by
      funext x
      rw [hsecp, _root_.mul_inv_rev, cj_mul, Function.comp_apply]
      exact hc hl _
    rw [hfun]
    exact hΛ p⁻¹ (inv_mem hp) f₀ hf₀
  · have hmem : w ∉ {w : Vc k n | w - eN k n ∈ box (Fin (n + 1)) s} := hw
    rw [Set.indicator_of_notMem hmem]
    simp only [phi, Set.indicator_of_notMem hmem, mul_zero]
    split_ifs
    · rfl
    · exact map_zero Λ

end PositivityTheory.RgUd.AB.Pf
end
end

