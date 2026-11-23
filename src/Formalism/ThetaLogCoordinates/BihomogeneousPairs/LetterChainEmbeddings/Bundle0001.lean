module

public import Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.PairStep

@[expose] public section

-- bundled from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeEqualHolds
section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality

section tieop
variable {p : ℕ} [Fact p.Prime]

theorem int_Fpow {τ : Type} {r : ℕ} (L m : ℕ) (hmL : Nat.log p m ≤ L) (w e : Fin r → τ)
    {y : MvPolynomial τ ℚ_[p]} (hy : y ∈ IntPol p τ) :
    (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) • (tieF w e ^ m) y) ∈ IntPol p τ := by
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Fact.out : p.Prime).one_lt.le
  set Mc : ℝ := (p : ℝ) ^ L with hMc
  have hM1 : 1 ≤ Mc := one_le_pow₀ hp1
  have hM : ∀ j ≤ m, ∀ k ≤ j, ‖(((j.choose k : ℕ) : ℚ_[p]))⁻¹‖ ≤ Mc := fun j hj k hk =>
    (norm_choose_inv_le j k hk).trans (pow_le_pow_right₀ hp1 ((Nat.log_mono_right hj).trans hmL))
  let Dc : Fin r → (MvPolynomial τ ℚ_[p] →ₗ[ℚ_[p]] MvPolynomial τ ℚ_[p]) := fun c =>
    (pderiv (w c) : Derivation ℚ_[p] (MvPolynomial τ ℚ_[p]) (MvPolynomial τ ℚ_[p])).toLinearMap ∘ₗ
      (pderiv (e c)).toLinearMap
  have hcomm : ∀ a b, Commute (Dc a) (Dc b) := by
    intro a b
    simp only [Dc, ← Module.End.mul_eq_comp]
    refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
      exact commute_pderiv _ _
  have hF := contr_Fsum Dc hcomm (fun a k => contr_D _ _ k) hM1 m hM Finset.univ
  rw [Finset.card_univ, Fintype.card_fin] at hF
  have hFeq : tieF (k := ℚ_[p]) w e = ∑ c ∈ Finset.univ, Dc c := rfl
  have hb : Bnd (p := p) 1 y := (intPol_iff_bnd y).mp hy
  have h1 := hF m le_rfl 1 zero_le_one y hb
  rw [← hFeq] at h1
  rw [intPol_iff_bnd, ← smul_smul]
  have h2 := bnd_smul ((p : ℚ_[p]) ^ (r * L)) h1
  intro μ
  refine (h2 μ).trans (le_of_eq ?_)
  rw [Padic.norm_p_pow, hMc, one_mul, ← pow_mul, zpow_neg, zpow_natCast, mul_comm L r]
  exact inv_mul_cancel₀ (pow_ne_zero _ (by positivity))

variable {N r : ℕ} [NeZero r] {D : BlockData N}

theorem xi_free {b : ℕ} {g : MvPolynomial (BVar N r D.T.t) ℚ_[p]} (hg : g ∈ XiPolZ p N r D.T.t b)
    {v : BVar N r D.T.t} (hv : ∀ c, v ≠ xiVar N r D.T.t c) : pderiv v g = 0 :=
  ProjS.pderiv_of_free v g (fun m hm => (xi_supp hg hm).1 v hv)

theorem tieF_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) :
    tieF (wv D i) (ev D i) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) y) * g := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [tieF_apply', tieF_apply', map_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [pderiv_mul, he c, mul_zero, add_zero, ev_chain hB, pderiv_rename chainEmb_inj, pderiv_mul, hw c,
    mul_zero, add_zero, wv_chain hB, pderiv_rename chainEmb_inj]

theorem tieF_pow_gen (hB : D.BlockOK) (i : Fin D.T.t) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (g : MvPolynomial (BVar N r D.T.t) ℚ_[p]) (hw : ∀ c, pderiv (wv D i c) g = 0)
    (he : ∀ c, pderiv (ev D i c) g = 0) (m : ℕ) :
    (tieF (wv D i) (ev D i) ^ m) (rename (chainEmb N r D.T.t) y * g) =
      rename (chainEmb N r D.T.t)
        ((tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y) * g := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', Module.End.mul_apply, ih, tieF_gen hB i _ g hw he, ← Module.End.mul_apply, ← pow_succ']

omit [NeZero r] in
theorem update_single (j : Fin D.T.t → ℕ) (i : Fin D.T.t) (m : ℕ) :
    Function.update (j + Pi.single i m : Fin D.T.t → ℕ) i ((j + Pi.single i m : Fin D.T.t → ℕ) i + 1) =
      j + Pi.single i (m + 1) := by
  funext k
  by_cases hk : k = i
  · subst hk; simp; ring
  · simp [hk]

theorem Y_iter (hF : HypJoin p (r := r) D) (i : Fin D.T.t) :
    ∀ m (j : Fin D.T.t → ℕ) (jp : ℕ), ∀ y ∈ Y p (r := r) (D.lettersAt j jp) D.T.J D.T.thr,
      (tieF (fun c => (D.letterAt (D.T.pos i), c)) (fun c => (D.letterAt (D.T.pos i + 1), c)) ^ m) y ∈
        Y p (r := r) (D.lettersAt (j + Pi.single i m) jp) D.T.J D.T.thr := by
  intro m
  induction m with
  | zero =>
    intro j jp y hy
    have h0 : j + Pi.single i 0 = j := by simp
    rw [h0, pow_zero, Module.End.one_apply]
    exact hy
  | succ m ih =>
    intro j jp y hy
    have h := hF _ jp i _ (ih j jp y hy)
    rw [update_single] at h
    rw [pow_succ', Module.End.mul_apply]
    exact h

theorem lat_tie (hB : D.BlockOK) (hF : HypJoin p (r := r) D) (j : Fin D.T.t → ℕ) (jp : ℕ) (i : Fin D.T.t)
    (m L : ℕ) (hmL : Nat.log p m ≤ L) :
    ∀ x ∈ Lat p D (r := r) j jp, (((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹) •
      (tieF (wv D i) (ev D i) ^ m) x) ∈ Lat p D (r := r) (j + Pi.single i m) jp := by
  intro x hx
  have := span_map_mem ((((p : ℚ_[p]) ^ (r * L) * ((m.factorial : ℚ_[p]) ^ 2)⁻¹)) •
    (tieF (wv D i) (ev D i) ^ m)) _ (Lat p D (r := r) (j + Pi.single i m) jp) ?_ x hx
  · simpa using this
  rintro v ⟨y, hy, g, hg, rfl⟩
  rw [LinearMap.smul_apply, tieF_pow_gen hB i y g
    (fun c => xi_free hg (fun d => wv_ne_xi hB i c d)) (fun c => xi_free hg (fun d => ev_ne_xi hB i c d)),
    ← smul_mul_assoc, ← map_smul]
  refine Submodule.subset_span ⟨_, yz_mk (Submodule.smul_mem _ _ (Y_iter hF i m j jp y (yz_y hy)))
    (int_Fpow L m hmL _ _ (yz_int hy)), g, hg, rfl⟩

end tieop

theorem lattice_equal_holds : LatTie := by
  intro p _ N r _ D hB hF j jp i m L hmL x hx
  exact lat_tie hB hF j jp i m L hmL x hx

end Formalism.InvariantFactorPaths.KP.LL
end

-- bundled from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LatticeLinearHolds
section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

section abs
variable {p : ℕ} [Fact p.Prime] {σ : Type} {r : ℕ}

noncomputable def cmTiePL (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) :
    Module.End ℚ_[p] (MvPolynomial σ ℚ_[p]) :=
  ∑ l ∈ range (o + 1),
    (((-1 : ℚ_[p]) ^ l) / (((l.factorial : ℚ_[p]) ^ 2) * ((o + n + r + z - 1).choose l : ℚ_[p]))) •
      ((tieEh w e zv sv) ^ l * ((tieF w e) ^ l * LinearMap.mulLeft ℚ_[p] (X zv ^ z)))

theorem cm_tiePL_apply (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ) (x : MvPolynomial σ ℚ_[p]) :
    cmTiePL w e zv sv o n z x = tieP w e zv sv o n z x := by
  simp only [cmTiePL, tieP, LinearMap.sum_apply, LinearMap.smul_apply, Module.End.mul_apply,
    LinearMap.mulLeft_apply]

theorem cm_F_F {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) :
    Commute (tieF (k := ℚ_[p]) w' e') (tieF w e) := by
  unfold tieF
  refine Commute.sum_left _ _ _ (fun c _ => Commute.sum_right _ _ _ (fun d _ => ?_))
  simp only [← Module.End.mul_eq_comp]
  refine Commute.mul_left (Commute.mul_right ?_ ?_) (Commute.mul_right ?_ ?_) <;>
    exact PhiIntegrality.commute_pderiv _ _

theorem cm_F_mul {r' : ℕ} (w' e' : Fin r' → σ) (q : MvPolynomial σ ℚ_[p]) (hw : ∀ c, pderiv (w' c) q = 0)
    (he : ∀ c, pderiv (e' c) q = 0) : Commute (tieF w' e') (LinearMap.mulLeft ℚ_[p] q) :=
  LinearMap.ext fun f => by
    simp only [Module.End.mul_apply, LinearMap.mulLeft_apply]
    exact tieF_mul_free w' e' q f hw he

theorem cm_F_P {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (hw : ∀ c, zv ≠ w' c ∧ sv ≠ w' c ∧ (∀ d, w d ≠ w' c) ∧ ∀ d, e d ≠ w' c)
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) :
    Commute (tieF (k := ℚ_[p]) w' e') (cmTiePL w e zv sv o n z) := by
  unfold cmTiePL
  refine Commute.sum_right _ _ _ (fun l _ => Commute.smul_right ?_ _)
  refine Commute.mul_right (Commute.pow_right ?_ _) (Commute.mul_right (Commute.pow_right (cm_F_F _ _ _ _) _) ?_)
  · exact cm_F_mul w' e' (ehP w e zv sv)
      (fun c => free_ehP (hw c).1 (hw c).2.1 (hw c).2.2.1 (hw c).2.2.2)
      (fun c => free_ehP (he c).1 (he c).2.1 (he c).2.2.1 (he c).2.2.2)
  · exact cm_F_mul w' e' _ (fun c => free_pow (free_X (hw c).1) _) (fun c => free_pow (free_X (he c).1) _)

theorem cm_Fpow_P {r' : ℕ} (w' e' : Fin r' → σ) (w e : Fin r → σ) (zv sv : σ) (o n z : ℕ)
    (hw : ∀ c, zv ≠ w' c ∧ sv ≠ w' c ∧ (∀ d, w d ≠ w' c) ∧ ∀ d, e d ≠ w' c)
    (he : ∀ c, zv ≠ e' c ∧ sv ≠ e' c ∧ (∀ d, w d ≠ e' c) ∧ ∀ d, e d ≠ e' c) (m : ℕ)
    (x : MvPolynomial σ ℚ_[p]) :
    (tieF w' e' ^ m) (tieP w e zv sv o n z x) = tieP w e zv sv o n z ((tieF w' e' ^ m) x) := by
  have h := (cm_F_P (p := p) w' e' w e zv sv o n z hw he).pow_left m
  have h2 := LinearMap.congr_fun h.eq x
  simpa only [Module.End.mul_apply, cm_tiePL_apply] using h2

end abs

section block
variable {p : ℕ} [Fact p.Prime] {N r : ℕ} [NeZero r] {D : BlockData N}

noncomputable def cmPLL (p : ℕ) [Fact p.Prime] {N r : ℕ} (D : BlockData N) (L : List (Fin D.T.t))
    (j : Fin D.T.t → ℕ) (jp : ℕ) : Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  L.foldr (fun i acc => cmTiePL (wv D i) (ev D i) (zi D r i) (si D r i)
    ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
    (D.T.z i) * acc) 1

theorem cm_PLL_apply (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : cmPLL p D L j jp x = PL p D L j jp x := by
  induction L with
  | nil => rfl
  | cons i L ih =>
    have h1 : cmPLL (r := r) p D (i :: L) j jp = cmTiePL (wv D i) (ev D i) (zi D r i) (si D r i)
        ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i))) ((D.lettersAt j jp).deg (D.letterAt (D.T.pos i + 1)))
        (D.T.z i) * cmPLL p D L j jp := rfl
    rw [h1, Module.End.mul_apply, ih, cm_tiePL_apply]
    rfl

noncomputable def cmPplusL (p : ℕ) [Fact p.Prime] {N r : ℕ} (D : BlockData N) (jp : ℕ) :
    Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]) :=
  cmTiePL (wU D) (xiVar N r D.T.t) (zP D r) (sP D r) (D.LL.deg D.uPos - jp) (D.B - jp) D.zPlus

theorem cm_PplusL_apply (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    cmPplusL p D jp x = Pplus p D jp x := by
  unfold cmPplusL
  rw [cm_tiePL_apply]
  rfl

theorem cm_wv_wv (hB : D.BlockOK) {i k : Fin D.T.t} (h : i ≠ k) (c d : Fin r) : wv D i d ≠ wv D k c := by
  intro h'
  simp only [wv, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, finPos_pos_val hB] at this
  exact h (pos_inj hB this)

theorem cm_ev_ev (hB : D.BlockOK) {i k : Fin D.T.t} (h : i ≠ k) (c d : Fin r) : ev D i d ≠ ev D k c := by
  intro h'
  simp only [ev, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_succ_val hB, finPos_succ_val hB] at this
  exact h (pos_inj hB (by omega))

theorem cm_wv_ev (hB : D.BlockOK) (i k : Fin D.T.t) (c d : Fin r) : wv D i d ≠ ev D k c := by
  intro h'
  simp only [wv, ev, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, finPos_succ_val hB] at this
  exact pos_ne_succ hB i k this

theorem cm_wv_wU (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : wv D i d ≠ wU D c := by
  intro h'
  simp only [wv, wU, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_pos_val hB, Fin.val_castSucc] at this
  have := pos_lt_u hB i
  omega

theorem cm_ev_wU (hB : D.BlockOK) (i : Fin D.T.t) (c d : Fin r) : ev D i d ≠ wU D c := by
  intro h'
  simp only [ev, wU, Sum.inl.injEq, Prod.mk.injEq] at h'
  have := congrArg Fin.val h'.1
  rw [finPos_succ_val hB, Fin.val_castSucc] at this
  have := pos_lt_u hB i
  omega

theorem cm_Pt_tie (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp m : ℕ) {i k : Fin D.T.t} (h : i ≠ k)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (tieF (wv D k) (ev D k) ^ m) (Pt p D j jp i x) = Pt p D j jp i ((tieF (wv D k) (ev D k) ^ m) x) :=
  cm_Fpow_P (wv D k) (ev D k) (wv D i) (ev D i) (zi D r i) (si D r i) _ _ _
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_wv hB h c d, fun d => (cm_wv_ev hB k i d c).symm⟩)
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_ev hB i k c d, fun d => cm_ev_ev hB h c d⟩) m x

theorem cm_Pt_plus (hB : D.BlockOK) (j : Fin D.T.t → ℕ) (jp m : ℕ) (i : Fin D.T.t)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    (tieF (wU D) (xiVar N r D.T.t) ^ m) (Pt p D j jp i x) =
      Pt p D j jp i ((tieF (wU D) (xiVar N r D.T.t) ^ m) x) :=
  cm_Fpow_P (wU D) (xiVar N r D.T.t) (wv D i) (ev D i) (zi D r i) (si D r i) _ _ _
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => cm_wv_wU hB i c d, fun d => cm_ev_wU hB i c d⟩)
    (fun c => ⟨Sum.inr_ne_inl, Sum.inr_ne_inl, fun d => wv_ne_xi hB i d c, fun d => ev_ne_xi hB i d c⟩) m x

theorem cm_Pt_param (hB : D.BlockOK) (j j' : Fin D.T.t → ℕ) (jp jp' : ℕ) (i : Fin D.T.t) (h : j i = j' i)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : Pt p D j jp i x = Pt p D j' jp' i x := by
  unfold Pt
  rw [deg_lettersAt_pos hB j jp, deg_lettersAt_pos_succ hB j jp, deg_lettersAt_pos hB j' jp', deg_lettersAt_pos_succ hB j' jp', h]

theorem cm_PL_nil (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    PL p D [] j jp x = x := rfl

theorem cm_PL_cons (i : Fin D.T.t) (L : List (Fin D.T.t)) (j : Fin D.T.t → ℕ) (jp : ℕ)
    (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) : PL p D (i :: L) j jp x = Pt p D j jp i (PL p D L j jp x) := rfl

theorem cm_midGen_top (j : Fin D.T.t → ℕ) (jp : ℕ) (x : MvPolynomial (BVar N r D.T.t) ℚ_[p]) :
    midGen p D D.T.t j jp x = (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
      (∏ i, X (scalZ N r D.T.t (Fin.castSucc i)) ^ D.T.z i) * X (scalZ N r D.T.t (Fin.last D.T.t)) ^ D.zPlus *
      x := by
  unfold midGen
  rw [List.drop_eq_nil_of_le (by simp), Finset.filter_true_of_mem (fun i _ => i.2)]
  rfl

end block

theorem lattice_linear_holds : PLLin := by
  intro p _ N r _ D L j jp
  exact ⟨⟨cmPLL p D L j jp, cm_PLL_apply L j jp⟩, ⟨cmPplusL p D jp, cm_PplusL_apply jp⟩⟩

theorem comm_lattice_holds : CommPL := by
  intro p _ N r _ D hB L j jp m x
  induction L with
  | nil => exact ⟨fun _ _ => rfl, rfl⟩
  | cons i L ih =>
    refine ⟨fun k hk => ?_, ?_⟩
    · have hki : i ≠ k := fun h => hk (by simp [h])
      have hkL : k ∉ L := fun h => hk (by simp [h])
      show (tieF (wv D k) (ev D k) ^ m) (Pt p D j jp i (PL p D L j jp x)) =
        Pt p D j jp i (PL p D L j jp ((tieF (wv D k) (ev D k) ^ m) x))
      rw [cm_Pt_tie hB j jp m hki, ih.1 k hkL]
    · show (tieF (wU D) (xiVar N r D.T.t) ^ m) (Pt p D j jp i (PL p D L j jp x)) =
        Pt p D j jp i (PL p D L j jp ((tieF (wU D) (xiVar N r D.T.t) ^ m) x))
      rw [cm_Pt_plus hB j jp m i, ih.2]

theorem param_lattice_holds : ParamPL := by
  intro p _ N r _ D hB L j j' jp jp' x h
  induction L with
  | nil => rw [cm_PL_nil, cm_PL_nil]
  | cons i L ih =>
    rw [cm_PL_cons, cm_PL_cons, ih (fun a ha => h a (by simp [ha])), cm_Pt_param hB j j' jp jp' i (h i (by simp))]

theorem middle_top_holds : MidTop := by
  intro p _ N r _ D
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, jp, hok, x, hx, rfl⟩
    rw [SetLike.mem_coe, cm_midGen_top, ← LinearMap.mulLeft_apply (R := ℚ_[p])]
    refine span_map_mem _ _ _ ?_ x hx
    rintro _ ⟨y, hy, g, hg, rfl⟩
    refine Submodule.subset_span ?_
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hok, y, hy, g, hg, by rw [LinearMap.mulLeft_apply, mul_assoc _ (rename _ y) g]⟩
  · refine Submodule.span_le.mpr ?_
    intro v hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hv
    refine Submodule.subset_span ⟨j, jp, hok, rename (chainEmb N r D.T.t) y * g,
      Submodule.subset_span ⟨y, hy, g, hg, rfl⟩, ?_⟩
    rw [cm_midGen_top, mul_assoc _ (rename _ y) g]

theorem middle_p_eq_holds : MidPEq := by
  intro p _ N r _ D
  apply le_antisymm
  · refine Submodule.span_le.mpr ?_
    rintro v ⟨j, jp, hok, x, hx, rfl⟩
    have key : ∀ x' : MvPolynomial (BVar N r D.T.t) ℚ_[p],
        ((LinearMap.mulLeft ℚ_[p] ((∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp) *
          (cmPplusL p D jp * cmPLL p D (List.finRange D.T.t) j jp) :
            Module.End ℚ_[p] (MvPolynomial (BVar N r D.T.t) ℚ_[p]))) x' =
        (∏ i, D.Ehat p (r := r) i ^ j i) * D.Eplus p (r := r) ^ jp *
          Pplus p D jp (PL p D (List.finRange D.T.t) j jp x') := by
      intro x'
      rw [Module.End.mul_apply, Module.End.mul_apply, cm_PLL_apply, cm_PplusL_apply, LinearMap.mulLeft_apply]
    rw [SetLike.mem_coe, ← key]
    refine span_map_mem _ _ _ ?_ x hx
    rintro _ ⟨y, hy, g, hg, rfl⟩
    refine Submodule.subset_span ?_
    simp only [Set.mem_iUnion]
    exact ⟨j, jp, hok, y, hy, g, hg, by rw [key, Pall_eq]⟩
  · refine Submodule.span_le.mpr ?_
    intro v hv
    simp only [Set.mem_iUnion] at hv
    obtain ⟨j, jp, hok, y, hy, g, hg, rfl⟩ := hv
    exact Submodule.subset_span ⟨j, jp, hok, rename (chainEmb N r D.T.t) y * g,
      Submodule.subset_span ⟨y, hy, g, hg, rfl⟩, by rw [Pall_eq]⟩

end Formalism.InvariantFactorPaths.KP.LL
end

-- bundled from Formalism.ThetaLogCoordinates.BihomogeneousPairs.LetterChainEmbeddings.LevelLatticeOf
section
namespace Formalism.InvariantFactorPaths.KP.LL

open Formalism.GM

open MvPolynomial Finset Formalism.GM.M

lemma asm_num (p : ℕ) [Fact p.Prime] (a r : ℕ) (ha : 1 ≤ a) :
    r * Nat.log p (2 * a) + Nat.log p (6 * a + r) ≤ ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ := by
  have hp : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  have ha' : (1 : ℝ) ≤ a := by exact_mod_cast ha
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  have h1 : (Nat.log p (2 * a) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h2 : (Nat.log p (6 * a + r) : ℝ) ≤ Real.logb p (8 * a + r) := by
    refine (Real.natLog_le_logb _ _).trans ?_
    apply Real.logb_le_logb_of_le hp
    · push_cast; linarith
    · push_cast; linarith
  have h3 : ((r * Nat.log p (2 * a) + Nat.log p (6 * a + r) : ℕ) : ℝ) ≤ ((r : ℝ) + 1) * lgV2 p a r := by
    push_cast
    unfold lgV2
    have := mul_le_mul_of_nonneg_left h1 hr
    nlinarith
  exact_mod_cast h3.trans (Nat.le_ceil _)

lemma asm_chain (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (M : ℕ → Submodule ℤ_[p] V) (u t : ℕ)
    (h : ∀ k < t, (∀ v ∈ M (k + 1), (p : ℚ_[p]) ^ u • v ∈ M k) ∧ (∀ v ∈ M k, (p : ℚ_[p]) ^ u • v ∈ M (k + 1))) :
    ∀ k ≤ t, (∀ v ∈ M k, (p : ℚ_[p]) ^ (k * u) • v ∈ M 0) ∧ (∀ v ∈ M 0, (p : ℚ_[p]) ^ (k * u) • v ∈ M k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro hk
    obtain ⟨i1, i2⟩ := ih (by omega)
    obtain ⟨s1, s2⟩ := h k (by omega)
    constructor
    · intro v hv
      have := i1 _ (s1 v hv)
      rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
    · intro v hv
      have := s2 _ (i2 v hv)
      rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this

lemma asm_span (p : ℕ) [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℚ_[p] V] [Module ℤ_[p] V]
    (A B : Submodule ℤ_[p] V) (K : ℕ) (h : ∀ v ∈ A, (p : ℚ_[p]) ^ K • v ∈ B) :
    Submodule.span ℚ_[p] (A : Set V) ≤ Submodule.span ℚ_[p] (B : Set V) := by
  have hp : ((p : ℚ_[p]) ^ K) ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  rw [Submodule.span_le]
  intro x hx
  have h1 : (p : ℚ_[p]) ^ K • x ∈ Submodule.span ℚ_[p] (B : Set V) := Submodule.subset_span (h x hx)
  have h2 := Submodule.smul_mem _ (((p : ℚ_[p]) ^ K)⁻¹) h1
  rwa [smul_smul, inv_mul_cancel₀ hp, one_smul] at h2

theorem LevelLattice_of : MidTop → MidPEq → JoinCondition → PlusCondition → Formalism.GM.M.LevelLattice := by
  intro hTop hPEq hTie hPlus p _ N r _ D a hOK hr ha hdeg hB hz hzP hYT hYU
  have hnum := asm_num p a r ha
  generalize ⌈((r : ℝ) + 1) * lgV2 p a r⌉₊ = u at hnum ⊢
  have hT : HypJoin p (r := r) D := hYT
  have hU : HypU p (r := r) D := hYU
  obtain ⟨c1, c2⟩ := asm_chain p (fun k => Mid p (r := r) D k) u D.T.t
    (hTie p N r D a u hOK hr hdeg hz hT hnum) D.T.t le_rfl
  obtain ⟨q1, q2⟩ := hPlus p N r D a u hOK hr hdeg hB hzP hU hnum
  rw [← hTop p N r D, ← hPEq p N r D]
  have k1 : ∀ x ∈ Mid p (r := r) D D.T.t, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ MidP p (r := r) D := by
    intro x hx
    have := q1 _ (c1 x hx)
    rwa [smul_smul, ← pow_add, add_comm u, ← Nat.succ_mul] at this
  have k2 : ∀ x ∈ MidP p (r := r) D, (p : ℚ_[p]) ^ ((D.T.t + 1) * u) • x ∈ Mid p (r := r) D D.T.t := by
    intro x hx
    have := c2 _ (q2 x hx)
    rwa [smul_smul, ← pow_add, ← Nat.succ_mul] at this
  exact ⟨le_antisymm (asm_span p _ _ _ k1) (asm_span p _ _ _ k2), k1, k2⟩

end Formalism.InvariantFactorPaths.KP.LL
end

