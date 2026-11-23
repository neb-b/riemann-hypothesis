module

public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0007
public import Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.Bundle0006
public import Formalism.PolynomialDimension.MultinomialDepth.TieOps

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.ExponentMatrixFirstDepthEq
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

section TM

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def epsM (XM : flipOneThree.InstM) (i : Fin XM.T.t) : ℝ := XM.eps i

def RestTMHyp : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    (XMof C0 CE1 CE2 X dl a x.1 x.2).Hyp

def RestTMEps (CM : ℝ) : Prop :=
  ∀ dl ∈ clSet C0 CE1 CE2 X, ∀ a ∈ cbox C0 CE1 CE2 X dl, ∀ x ∈ idx C0 CE1 CE2 X dl a,
    ∀ i, epsM (XMof C0 CE1 CE2 X dl a x.1 x.2) i ≤ (30 + CM) / X.L.Y

variable {C0 CE1 CE2 X}

theorem mem_levels {N : ℕ} (G : Formalism.GM.M.BlockData N) (x : (Fin G.T.t → ℕ) × ℕ) (h : x ∈ levels G) :
    G.LevelOK x.1 x.2 := by
  classical
  unfold levels at h
  exact (Finset.mem_filter.1 h).2

theorem chain_eta (aTop : Fin X.s → ℕ) (b : SegBlock X.s X.r) (i : Fin (X.S C0 CE1 CE2).t)
    (q : Fin (2 * X.s + 1)) (hq : (q : ℕ) = 2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) :
    (segChain X.p (X.S C0 CE1 CE2) aTop b).deg q = coarseC X.p (X.S C0 CE1 CE2) aTop b (uTop (X.S C0 CE1 CE2) i) := by
  have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := by
    have := i.2
    unfold SegData.t at this
    omega
  have h1 : (q : ℕ) ≠ 2 * X.s := by omega
  have h2 : ¬ (q : ℕ) % 2 = 0 := by omega
  have h3 : topOf q h1 = uTop (X.S C0 CE1 CE2) i := by
    unfold topOf uTop
    exact Fin.ext (by simp only; omega)
  have h4 : ¬ ((uTop (X.S C0 CE1 CE2) i : Fin X.s) : ℕ) < (X.S C0 CE1 CE2).sigma := by
    unfold uTop; simp
  unfold segChain
  simp only
  rw [dite_eq_right h1, if_neg h2, h3, if_neg h4]

theorem lvlRoom_of {dl : DCl X} {a0 : Fin X.s → ℕ} (ha0 : a0 ∈ cbox C0 CE1 CE2 X dl) {x : Σ _ : SegBlock X.s X.r, Lv C0 CE1 CE2 X}
    (hb : x.1.ry = dl.2) (hx : ∀ a ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a) :
    LvlRoom C0 CE1 CE2 X dl x.2 := by
  classical
  intro i v hv
  have ha' : Function.update a0 (uTop (X.S C0 CE1 CE2) i) v ∈ cbox C0 CE1 CE2 X dl := by
    have hbox := cbox_eq C0 CE1 CE2 X dl a0 ha0
    have ha0' := hbox ▸ ha0
    rw [hbox]
    rw [Fintype.mem_piFinset] at ha0' ⊢
    intro l
    by_cases hl : l = uTop (X.S C0 CE1 CE2) i
    · subst hl; rw [Function.update_self]; exact hv
    · rw [Function.update_of_ne hl]; exact ha0' l
  have h := hx _ ha'
  unfold idx at h
  rw [Finset.mem_sigma] at h
  have hl := h.2
  have hOK := ((mem_levels _ _ hl).1 i).2
  have hi : (X.S C0 CE1 CE2).sigma + (i : ℕ) < X.s := by
    have := i.2
    unfold SegData.t at this
    omega
  have e := chain_eta (C0 := C0) (CE1 := CE1) (CE2 := CE2) (X := X) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1 i
    ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
      by omega⟩ (by show min (2 * ((X.S C0 CE1 CE2).sigma + (i : ℕ)) + 1) (2 * X.s + 1 - 1) = _; omega)
  have e2 : (gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).LL.deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ = (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1).deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ := rfl
  have hOK' : x.2.1 i ≤ (segChain X.p (X.S C0 CE1 CE2) (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) x.1).deg
      ⟨min ((gB C0 CE1 CE2 X (Function.update a0 (uTop (X.S C0 CE1 CE2) i) v) 0 x.1).T.pos i + 1) (2 * X.s + 1 - 1),
        by omega⟩ := by
    rw [← e2]; exact hOK
  rw [e] at hOK'
  unfold coarseC at hOK'
  rw [Function.update_self, hb] at hOK'
  exact hOK'

theorem reindex {dl : DCl X} {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x) (f : (Fin (X.S C0 CE1 CE2).t → ℕ) → ℝ) :
    ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        f (fun i => cm C0 CE1 CE2 X dl x i (n i)) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), f n := by
  classical
  unfold Nl
  rw [Fintype.piFinset_image, Finset.sum_image]
  intro n hn n' hn' h
  funext i
  exact cm_inj hr i (Fintype.mem_piFinset.1 hn i) (Fintype.mem_piFinset.1 hn' i) (congrFun h i)

theorem prog_eq {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) {x : Lv C0 CE1 CE2 X}
    (hr : LvlRoom C0 CE1 CE2 X dl x) (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) :
    (XMof C0 CE1 CE2 X dl a b x).prog = Fintype.piFinset (Nl C0 CE1 CE2 X dl x) := by
  unfold flipOneThree.InstM.prog
  congr 1
  funext i
  exact (interval_eq _ ((hne i).image _) (Nl_conv hr i)).symm

theorem top_eq {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) {x : Lv C0 CE1 CE2 X}
    (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty) (i : Fin (X.S C0 CE1 CE2).t) :
    (XMof C0 CE1 CE2 X dl a b x).top i = cm C0 CE1 CE2 X dl x i (topA C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)) := by
  rw [cm_top x i (hne i)]
  have hmem : sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) ∈ Nl C0 CE1 CE2 X dl x i := by
    have := Nat.sInf_mem (s := ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ)) (by
      obtain ⟨v, hv⟩ := (hne i).image (cm C0 CE1 CE2 X dl x i)
      exact ⟨v, by exact_mod_cast hv⟩)
    exact_mod_cast this
  have hle := Finset.le_sup (f := id) hmem
  show sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) +
    1 * ((Nl C0 CE1 CE2 X dl x i).sup id - sInf ((Nl C0 CE1 CE2 X dl x i : Finset ℕ) : Set ℕ) + 1 - 1) = _
  simp only [id] at hle ⊢
  omega

theorem exponent_matrix_first_depth_eq (dl : DCl X) (a : Fin X.s → ℕ) (b : SegBlock X.s X.r) (x : Lv C0 CE1 CE2 X) :
    (XMof C0 CE1 CE2 X dl a b x).D1 = D1r C0 CE1 CE2 X 1 := by
  show ((X.S C0 CE1 CE2).t : ℝ) * (X.L.Y * kapS X + kapS X) + kapS X = _
  unfold D1r
  rw [one_mul]

theorem fibre_ineq (D : Formalism.BasicNotions.D7) (ε : ℝ) {dl : DCl X} (a : Fin X.s → ℕ) (b : SegBlock X.s X.r)
    (hb : b.ry = dl.2) {x : Lv C0 CE1 CE2 X} (hr : LvlRoom C0 CE1 CE2 X dl x)
    (hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty)
    (hM : ModelLatticeRank D (XMof C0 CE1 CE2 X dl a b x)) (hH : (XMof C0 CE1 CE2 X dl a b x).Hyp)
    (hε : ∀ i, epsM (XMof C0 CE1 CE2 X dl a b x) i ≤ ε) :
    ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ) ≤
      ε * ∑ i, ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl (ovr (uTop (X.S C0 CE1 CE2)) a n) i) 0 b)
          x.1 x.2 : ℝ) := by
  classical
  have h1 := hM hH
  rw [prog_eq a b hr hne, exponent_matrix_first_depth_eq] at h1
  have hc : (0 : ℝ) < ((Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).card : ℝ) := by
    have : (Fintype.piFinset (Nl C0 CE1 CE2 X dl x)).Nonempty := by
      rw [Fintype.piFinset_nonempty]
      intro i
      exact (hne i).image _
    exact_mod_cast this.card_pos

  have hL : ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (bY C0 CE1 CE2 X (ovr (uTop (X.S C0 CE1 CE2)) a n) b x ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ) := by
    rw [← reindex hr (fun n => (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ))]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [bY_ovr C0 CE1 CE2 X dl a n b hb x]

  have hR : ∀ i, ∑ n ∈ Fintype.piFinset (fun i => Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)),
        (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl (ovr (uTop (X.S C0 CE1 CE2)) a n) i) 0 b)
          x.1 x.2 : ℝ) =
      ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x),
        (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ) := by
    intro i
    rw [← reindex hr (fun n => (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ))]
    refine Finset.sum_congr rfl fun n _ => ?_
    unfold upd
    rw [ovr_update _ (uTop_inj C0 CE1 CE2 X), dimY_ovr C0 CE1 CE2 X dl a _ b hb x, top_eq a b hne i]
    congr 2
    funext i'
    by_cases hi : i' = i
    · subst hi; simp
    · rw [Function.update_of_ne hi, Function.update_of_ne hi]
  rw [hL]
  simp only [hR]
  have h2 : ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x), (BADf C0 CE1 CE2 X a b x ⌊D1r C0 CE1 CE2 X 1⌋ n : ℝ) ≤
      ∑ i, epsM (XMof C0 CE1 CE2 X dl a b x) i * ∑ n ∈ Fintype.piFinset (Nl C0 CE1 CE2 X dl x),
        (FRf C0 CE1 CE2 X a b x (Function.update n i ((XMof C0 CE1 CE2 X dl a b x).top i)) : ℝ) := by
    have h3 := (div_le_iff₀ hc).1 h1
    calc _ ≤ _ := h3
      _ = _ := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        have key : ∀ (e S c : ℝ), c ≠ 0 → e * (S / c * c) = e * S := fun e S c hc' => by
          rw [div_mul_cancel₀ _ hc']
        rw [mul_assoc]
        exact (key _ _ _ hc.ne').trans rfl
  refine h2.trans ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  exact mul_le_mul_of_nonneg_right (hε i) (Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _)

theorem restTM_of_rests (D : Formalism.BasicNotions.D7) (hM : ∀ XM : flipOneThree.InstM, ModelLatticeRank D XM)
    (hF : RestFree C0 CE1 CE2 X) (hH : RestTMHyp C0 CE1 CE2 X) (hE : RestTMEps C0 CE1 CE2 X 1) :
    RestTM C0 CE1 CE2 X 1 := by
  classical
  intro dl hdl a0 ha0 x hx
  have hxa : ∀ a ∈ cbox C0 CE1 CE2 X dl, x ∈ idx C0 CE1 CE2 X dl a := fun a ha => by
    rw [← hF dl hdl a0 ha0 a ha]; exact hx
  have hb : x.1.ry = dl.2 := by
    have := hx
    unfold idx at this
    rw [Finset.mem_sigma, Finset.mem_filter] at this
    exact (congrArg Prod.snd this.1.2 : _)
  have hr := lvlRoom_of ha0 hb hxa
  have hbox := cbox_eq C0 CE1 CE2 X dl a0 ha0
  have hne : ∀ i, (Wl C0 CE1 CE2 X dl (uTop (X.S C0 CE1 CE2) i)).Nonempty := fun i =>
    ⟨a0 (uTop (X.S C0 CE1 CE2) i), Fintype.mem_piFinset.1 (hbox ▸ ha0) _⟩
  rw [hbox]
  refine box_of_fibres (uTop (X.S C0 CE1 CE2)) (uTop_inj C0 CE1 CE2 X) (Wl C0 CE1 CE2 X dl)
    (fun a => (bY C0 CE1 CE2 X a x.1 x.2 ⌊D1r C0 CE1 CE2 X 1⌋ : ℝ))
    (fun i a => (dimY X.p (r := X.r) (gB C0 CE1 CE2 X (upd C0 CE1 CE2 X dl a i) 0 x.1) x.2.1 x.2.2 : ℝ))
    ((30 + 1) / X.L.Y) (hbox ▸ ⟨a0, ha0⟩) ?_
  intro a ha
  have ha' : a ∈ cbox C0 CE1 CE2 X dl := hbox ▸ ha
  exact fibre_ineq D _ a x.1 hb hr hne (hM _) (hH dl hdl a ha' x (hxa a ha'))
    (hE dl hdl a ha' x (hxa a ha'))

end TM

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.PhisBRenameMul
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial

section Free

variable {k σ : Type} [Field k] {r : ℕ}

theorem tieE_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) :
    Formalism.GM.tieE w e (F * m) = Formalism.GM.tieE w e F * m := by
  simp only [Formalism.GM.tieE, LinearMap.mulLeft_apply, mul_assoc]

theorem tieF_mul_free (w e : Fin r → σ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tieF w e (F * m) = Formalism.GM.tieF w e F * m := by
  have key : ∀ (v : σ) (G : MvPolynomial σ k), pderiv v m = 0 → pderiv v (G * m) = pderiv v G * m := by
    intro v G hv
    rw [Derivation.leibniz, hv, smul_zero, zero_add, smul_eq_mul, mul_comm]
  unfold Formalism.GM.tieF
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun c _ => ?_
  show pderiv (w c) (pderiv (e c) (F * m)) = pderiv (w c) (pderiv (e c) F) * m
  rw [key _ _ (he c), key _ _ (hw c)]

theorem tiePhi_mul_free (w e : Fin r → σ) (o n z : ℕ) (F m : MvPolynomial σ k) (hw : ∀ c, pderiv (w c) m = 0)
    (he : ∀ c, pderiv (e c) m = 0) : Formalism.GM.tiePhi w e o n z (F * m) = Formalism.GM.tiePhi w e o n z F * m := by
  have hE : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieE w e) ^ j) (G * m) = ((Formalism.GM.tieE w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) (G * m)) =
        Formalism.GM.tieE w e (((Formalism.GM.tieE w e) ^ j) G) * m
      rw [ih, tieE_mul_free]
  have hF : ∀ (j : ℕ) (G : MvPolynomial σ k),
      ((Formalism.GM.tieF w e) ^ j) (G * m) = ((Formalism.GM.tieF w e) ^ j) G * m := by
    intro j
    induction j with
    | zero => intro G; rfl
    | succ j ih =>
      intro G
      rw [pow_succ']
      show Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) (G * m)) =
        Formalism.GM.tieF w e (((Formalism.GM.tieF w e) ^ j) G) * m
      rw [ih, tieF_mul_free w e _ m hw he]
  unfold Formalism.GM.tiePhi
  rw [LinearMap.sum_apply, LinearMap.sum_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LinearMap.smul_apply, LinearMap.smul_apply, LinearMap.comp_apply, LinearMap.comp_apply, hF, hE,
    smul_mul_assoc]

theorem foldr_mul_free {ι : Type*} (l : List ι) (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (m : MvPolynomial σ k)
    (h : ∀ i ∈ l, ∀ F, f i (F * m) = f i F * m) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) (F * m) = (l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F * m := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

theorem foldr_rename {τ : Type} {ι : Type*} (l : List ι) (em : σ → τ)
    (f : ι → MvPolynomial σ k →ₗ[k] MvPolynomial σ k) (g : ι → MvPolynomial τ k →ₗ[k] MvPolynomial τ k)
    (h : ∀ i ∈ l, ∀ F, g i (rename em F) = rename em (f i F)) (F : MvPolynomial σ k) :
    (l.foldr (fun i acc => g i ∘ₗ acc) LinearMap.id) (rename em F) =
      rename em ((l.foldr (fun i acc => f i ∘ₗ acc) LinearMap.id) F) := by
  induction l with
  | nil => rfl
  | cons i l ih =>
    simp only [List.foldr_cons, LinearMap.comp_apply]
    rw [ih (fun j hj => h j (List.mem_cons_of_mem _ hj)), h i (by simp)]

end Free

section Level

variable (p : ℕ) [Fact p.Prime] {N r : ℕ} [NeZero r] (G : Formalism.GM.M.BlockData N)

theorem phisB_rename_mul (hB : G.BlockOK) (j : Fin G.T.t → ℕ) (jp : ℕ) (y : MvPolynomial (Fin N × Fin r) ℚ_[p])
    (m : MvPolynomial (Formalism.GM.M.BVar N r G.T.t) ℚ_[p])
    (hm : ∀ (a : Fin N) (c : Fin r), pderiv (Sum.inl (Fin.castSucc a, c)) m = 0) :
    phisB p (r := r) G j jp (rename (Formalism.GM.M.chainEmb N r G.T.t) y * m) =
      rename (Formalism.GM.M.chainEmb N r G.T.t) (G.T.phis p (r := r) (G.lettersAt j jp) y) * m := by
  obtain ⟨-, hpos, -, hN⟩ := hB
  have hlt : ∀ i : Fin G.T.t, G.T.pos i + 1 < N := fun i => by have := hpos i; omega
  have hfin0 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i) =
      Fin.castSucc (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hfin1 : ∀ i : Fin G.T.t, Formalism.GM.M.finPos N (G.T.pos i + 1) =
      Fin.castSucc (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.finPos, Fin.coe_castSucc]
    have := hlt i
    omega
  have hlet0 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i) = (⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hlet1 : ∀ i : Fin G.T.t, G.letterAt (G.T.pos i + 1) = (⟨G.T.pos i + 1, hlt i⟩ : Fin N) := by
    intro i
    apply Fin.ext
    simp only [Formalism.GM.M.BlockData.letterAt]
    have := hlt i
    omega
  have hinj : Function.Injective (Formalism.GM.M.chainEmb N r G.T.t) := by
    intro x y h
    simp only [Formalism.GM.M.chainEmb, Sum.inl.injEq, Prod.mk.injEq, Fin.castSucc_inj] at h
    exact Prod.ext h.1 h.2
  unfold phisB
  rw [foldr_mul_free]
  · congr 1
    unfold Formalism.GM.M.TieData.phis
    refine foldr_rename _ _ _ _ (fun i _ F => ?_) y
    simp only [Formalism.GM.M.TieData.phi, dif_pos (hlt i), Formalism.GM.M.tiePhiAt]
    rw [hfin0, hfin1, hlet0, hlet1]
    exact Formalism.CountingSumsFrames.TO.tiePhi_rename (Formalism.GM.M.chainEmb N r G.T.t) hinj
      (fun c : Fin r => ((⟨G.T.pos i, by have := hlt i; omega⟩ : Fin N), c))
      (fun c : Fin r => ((⟨G.T.pos i + 1, hlt i⟩ : Fin N), c)) _ _ _ F
  · intro i _ F
    exact tiePhi_mul_free _ _ _ _ _ F m (fun c => by rw [hfin0]; exact hm _ c)
      (fun c => by rw [hfin1]; exact hm _ c)

end Level

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.MonomialFactorials.RestDirOf
section
noncomputable section

namespace Formalism.MainNotions.G.SymmetricFormBlocks

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.MainNotions.G.CountingStatementReduction

variable (C0 CE1 CE2 : ℝ) (X : flipOneThree.Inst)

def RestDirQ : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      ∑ x ∈ lv C0 CE1 CE2 X aTop b, rL C0 CE1 CE2 X aTop b x ≤
        Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])))

def RestDimBC : Prop :=
  ∀ aTop ∈ Fintype.piFinset (fun _ : Fin X.s => X.winA), ∀ aPlus ∈ X.winA,
    ∀ b, Kept X.p X.r (X.S C0 CE1 CE2) aTop b →
      Module.finrank ℚ_[X.p] (Submodule.span ℚ_[X.p]
          (((gB C0 CE1 CE2 X aTop aPlus b).SSZ X.p (r := X.r) :
            Submodule ℤ_[X.p] (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p])) :
              Set (MvPolynomial (Formalism.GM.M.BVar (2 * X.s + 1) X.r (gB C0 CE1 CE2 X aTop aPlus b).T.t) ℚ_[X.p]))) ≤
        bRank C0 CE1 CE2 X aTop aPlus b

variable {C0 CE1 CE2 X}

theorem restDir_of (hQ : RestDirQ C0 CE1 CE2 X) (hB : RestDimBC C0 CE1 CE2 X) : RestDir C0 CE1 CE2 X :=
  fun aTop hT aPlus hP b hk => (hQ aTop hT aPlus hP b hk).trans (hB aTop hT aPlus hP b hk)

end Formalism.MainNotions.G.SymmetricFormBlocks

end
end

