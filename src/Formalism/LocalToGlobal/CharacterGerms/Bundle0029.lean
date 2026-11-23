module

public import Formalism.LocalToGlobal.CharacterGerms.Bundle0026
public import Formalism.LocalToGlobal.CharacterGerms.CoeffSubstEqSum
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0016

@[expose] public section

-- bundled from Formalism.LocalToGlobal.CharacterGerms.RowTiePLimTy
section
noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ RowTiePE0

namespace LimTy

variable {C : Type} [Field C] {V : VF C}

theorem tendsS_sum {σ ι : Type} (S : Finset ι) {f : ι → ℕ → MvPowerSeries σ C} {F : ι → MvPowerSeries σ C}
    (h : ∀ i ∈ S, TendsS V (f i) (F i)) : TendsS V (fun k => ∑ i ∈ S, f i k) (∑ i ∈ S, F i) := by
  intro μ
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [map_sum]
  exact Tends.sum S (fun i hi => h i hi μ)

theorem tendsS_smul {σ : Type} (c : C) {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => c • f k) (c • F) := by
  intro μ
  first
    | simp only [map_smul, smul_eq_mul]
    | simp only [MvPowerSeries.coeff_smul]
  exact (tends_const c).mul (h μ)

theorem tendsS_ite {σ : Type} (P : Prop) [Decidable P] {f : ℕ → MvPowerSeries σ C} {F : MvPowerSeries σ C}
    (h : TendsS V f F) : TendsS V (fun k => if P then f k else 0) (if P then F else 0) := by
  split_ifs
  · exact h
  · exact TendsS.const 0

theorem coeff_tyS_mv (l : ℕ) (b : ℕ → C) (μ : Unit →₀ ℕ) :
    MvPowerSeries.coeff μ (tyS l b) = ∑ s ∈ Finset.range (μ () + 1), if l ^ s = μ () then b s else 0 := rfl

theorem tendsS_tyS (l : ℕ) {a : ℕ → ℕ → C} {a' : ℕ → C} (h : ∀ s, Tends V (fun k => a k s) (a' s)) :
    TendsS V (fun k => tyS l (a k)) (tyS l a') := by
  intro μ
  simp only [coeff_tyS_mv]
  refine Tends.sum _ (fun s _ => ?_)
  split_ifs
  · exact h s
  · exact tends_const 0

theorem tendsP {f : ℕ → PowerSeries C} {F : PowerSeries C} (h : TendsS V f F) (n : ℕ) :
    Tends V (fun k => PowerSeries.coeff n (f k)) (PowerSeries.coeff n F) :=
  h (Finsupp.single () n)

private theorem eq_zero_of_tends_const_zero {y : C} (h : Tends V (fun _ => (0 : C)) y) : y = 0 := by
  by_contra hy
  have hne : V.v y ≠ ⊤ := fun ht => hy ((AddValuation.top_iff V.v).mp ht)
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hne
  obtain ⟨n0, hn0⟩ := h (r + 1)
  have h1 : ((r + 1 : ℝ) : WithTop ℝ) ≤ V.v (y - 0) := hn0 n0 le_rfl
  rw [sub_zero, ← hr] at h1
  have h2 := WithTop.coe_le_coe.mp h1
  linarith

private theorem ge_zero_of_tends_of_forall_ge_zero {s : ℕ → C} {y : C} (h : Tends V s y) (hs : ∀ k, V.Ge 0 (s k)) :
    V.Ge 0 y := by
  obtain ⟨n0, hn0⟩ := h 0
  have h1 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (y - s n0) := hn0 n0 le_rfl
  have h2 : ((0 : ℝ) : WithTop ℝ) ≤ V.v (s n0) := hs n0
  have e : y = (y - s n0) + s n0 := by ring
  show ((0 : ℝ) : WithTop ℝ) ≤ V.v y
  rw [e]
  exact le_trans (le_min h1 h2) (V.v.map_add _ _)

theorem isCv_lim {σ : Type} {γ : ℕ → σ → PowerSeries C} {Γ : σ → PowerSeries C}
    (h : ∀ i, TendsS V (fun k => γ k i) (Γ i)) (hc : ∀ k, IsCv V (γ k)) : IsCv V Γ := by
  intro i
  have hcoef : ∀ n, Tends V (fun k => PowerSeries.coeff n (γ k i)) (PowerSeries.coeff n (Γ i)) :=
    fun n => tendsP (h i) n
  refine ⟨?_, fun n => ge_zero_of_tends_of_forall_ge_zero (hcoef n) (fun k => (hc k i).2 n)⟩
  have e : ∀ k, PowerSeries.coeff 0 (γ k i) = 0 := fun k => by
    rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
    exact (hc k i).1
  have h0 := hcoef 0
  simp only [e] at h0
  rw [← PowerSeries.coeff_zero_eq_constantCoeff_apply]
  exact eq_zero_of_tends_const_zero h0

theorem constantCoeff_lin {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type}
    (X : RawChart C d I κ) (l : ℕ) (hl : 2 ≤ l) (g : Fin 2) (b : I g → ℕ → C) (i : κ) :
    MvPowerSeries.constantCoeff (∑ c : I g, X.u g c i • tyS l (b c)) = 0 := by
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum]
  refine Finset.sum_eq_zero fun c _ => ?_
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  first
    | rw [map_smul, coeff_tyS_mv]
    | rw [MvPowerSeries.coeff_smul, coeff_tyS_mv]
  simp

private theorem hasSubst_of_constantCoeff_eq_zero' {σ τ : Type} [Finite σ] {a : σ → MvPowerSeries τ C}
    (ha : ∀ s, MvPowerSeries.constantCoeff (a s) = 0) : MvPowerSeries.HasSubst a := by
  first
    | exact MvPowerSeries.hasSubst_of_constantCoeff_zero ha
    | exact MvPowerSeries.HasSubst.of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)
    | exact MvPowerSeries.hasSubst_of_constantCoeff_nilpotent (fun s => by rw [ha s]; exact IsNilpotent.zero)

theorem lim_mem {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ] (X : RawChart C d I κ)
    (hl : 2 ≤ V.l)
    (hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0) (hex0 : ∀ i, MvPowerSeries.constantCoeff (X.ex i) = 0)
    (hlgex : ∀ i, MvPowerSeries.subst X.ex (X.lg i) = MvPowerSeries.X i)
    (hexlg : ∀ i, MvPowerSeries.subst X.lg (X.ex i) = MvPowerSeries.X i)
    (g : Fin 2) (x : ℕ → ℕ → I g ⊕ JJ I g → C) (x' : ℕ → I g ⊕ JJ I g → C)
    (hx : ∀ k, x k ∈ X.TySet V g) (hlim : VLim V x x') : x' ∈ X.TySet V g := by
  classical
  unfold RawChart.TySet at hx ⊢
  simp only [Set.mem_setOf_eq] at hx ⊢
  choose γk lamk hγk hlamk hA hB using hx
  obtain ⟨T, hTdef⟩ : ∃ T : ℕ → κ → PowerSeries C,
      T = fun k i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x k s (Sum.inl c)) := ⟨_, rfl⟩
  obtain ⟨T', hT'def⟩ : ∃ T' : κ → PowerSeries C,
      T' = fun i => ∑ c : I g, X.u g c i • tyS V.l (fun s => x' s (Sum.inl c)) := ⟨_, rfl⟩
  have hT0 : ∀ k i, MvPowerSeries.constantCoeff (T k i) = 0 := by
    intro k i
    rw [hTdef]
    exact constantCoeff_lin X V.l hl g (fun c s => x k s (Sum.inl c)) i
  have hT'0 : ∀ i, MvPowerSeries.constantCoeff (T' i) = 0 := by
    intro i
    rw [hT'def]
    exact constantCoeff_lin X V.l hl g (fun c s => x' s (Sum.inl c)) i
  have hTlim : ∀ i, TendsS V (fun k => T k i) (T' i) := by
    intro i
    simp only [hTdef, hT'def]
    exact tendsS_sum Finset.univ (fun c _ => tendsS_smul (X.u g c i)
      (tendsS_tyS (a := fun k s => x k s (Sum.inl c)) (a' := fun s => x' s (Sum.inl c)) V.l
        (fun s w => hlim w s (Sum.inl c))))
  have hHSlg : MvPowerSeries.HasSubst X.lg := hasSubst_of_constantCoeff_eq_zero' hlg0
  have hHSex : MvPowerSeries.HasSubst X.ex := hasSubst_of_constantCoeff_eq_zero' hex0
  have hHS : ∀ k, MvPowerSeries.HasSubst (γk k) := fun k =>
    hasSubst_of_constantCoeff_eq_zero' (fun i => (hγk k i).1)
  have hHST' : MvPowerSeries.HasSubst T' := hasSubst_of_constantCoeff_eq_zero' hT'0
  have hγeq : ∀ k i, γk k i = MvPowerSeries.subst (T k) (X.ex i) := by
    intro k i
    have e1 : T k = fun j => MvPowerSeries.subst (γk k) (X.lg j) := by
      funext j
      rw [hTdef]
      exact (hA k j).symm
    rw [e1, ← MvPowerSeries.subst_comp_subst_apply hHSlg (hHS k), hexlg, MvPowerSeries.subst_X (hHS k)]
  obtain ⟨γ', hγ'def⟩ : ∃ γ' : κ → PowerSeries C, γ' = fun i => MvPowerSeries.subst T' (X.ex i) :=
    ⟨_, rfl⟩
  have hγlim : ∀ i, TendsS V (fun k => γk k i) (γ' i) := by
    intro i
    simp only [hγeq, hγ'def]
    exact TendsS.subst (fun k j => hT0 k j) hT'0 hTlim (TendsS.const _)
  have hγ' : IsCv V γ' := isCv_lim hγlim hγk
  have hγ'0 : ∀ i, MvPowerSeries.constantCoeff (γ' i) = 0 := fun i => (hγ' i).1
  have hrel : ∀ i, alongCv γ' (X.lg i) = T' i := by
    intro i
    unfold alongCv
    rw [hγ'def, ← MvPowerSeries.subst_comp_subst_apply hHSex hHST', hlgex, MvPowerSeries.subst_X hHST']
  obtain ⟨lam', hlam'def⟩ : ∃ lam' : JJ I g → PowerSeries C, lam' = fun q =>
      tyS V.l (fun s => x' s (Sum.inr q)) + alongCv γ' (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x' s (Sum.inl c)) else 0) := ⟨_, rfl⟩
  have hlamlim : ∀ q, TendsS V (fun k => lamk k q) (lam' q) := by
    intro q
    have e : ∀ k, lamk k q = tyS V.l (fun s => x k s (Sum.inr q)) + alongCv (γk k) (X.sg (X.u (1 - g) q)) -
        ∑ c : I g, (if X.ty g c = X.ty (1 - g) q then
          X.sg1 (X.u g c) (X.u (1 - g) q) • tyS V.l (fun s => x k s (Sum.inl c)) else 0) := by
      intro k
      rw [hB k q]
      ring
    simp only [e, hlam'def]
    refine TendsS.sub (TendsS.add ?_ ?_) ?_
    · exact tendsS_tyS (a := fun k s => x k s (Sum.inr q)) (a' := fun s => x' s (Sum.inr q)) V.l
        (fun s w => hlim w s (Sum.inr q))
    · unfold alongCv
      exact TendsS.subst (fun k j => (hγk k j).1) hγ'0 hγlim (TendsS.const _)
    · refine tendsS_sum _ (fun c _ => ?_)
      split_ifs
      · exact tendsS_smul _ (tendsS_tyS (a := fun k s => x k s (Sum.inl c))
          (a' := fun s => x' s (Sum.inl c)) V.l (fun s w => hlim w s (Sum.inl c)))
      · exact TendsS.const 0
  refine ⟨γ', lam', hγ', isCv_lim hlamlim hlamk, fun i => ?_, fun q => ?_⟩
  · rw [hrel i, hT'def]
  · simp only [hlam'def]
    ring

end LimTy

end Formalism.L2.FormalSeriesBounds
end
end

-- bundled from Formalism.LocalToGlobal.CharacterGerms.UncurryLinearCombination
section
set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {C : Type} [Field C] [CharZero C] {V : VF C} {O : Type} [CommRing O] [StarRing O] {dd : ℕ}

theorem FBChart.uncurry_log_constantCoeff_chart (Y : FBChart C V O dd) (i : Fin dd) : MvPowerSeries.constantCoeff (un1 (Y.lg i)) = 0 := by
  rw [constantCoeff_uncurry, Y.lg_const]

theorem FBChart.uncurry_exp_log_eq_X (Y : FBChart C V O dd) (i : Fin dd) :
    MvPowerSeries.subst (fun j => un1 (Y.lg j)) (un1 (Y.ex i)) = (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  rw [uncurry_comp Y.lg_const, Y.ex_lg]
  exact uncurry_X i

theorem FBChart.uncurry_linear_combination (Y : FBChart C V O dd) (i : Fin dd) (μ : Fin dd →₀ ℕ) (hμ : μ.degree ≤ 1) :
    MvPowerSeries.coeff μ (un1 (Y.lg i)) =
      MvPowerSeries.coeff μ (MvPowerSeries.X i : MvPowerSeries (Fin dd) C) := by
  show MvPowerSeries.coeff (μ.mapDomain fun x : Fin dd => ((0 : Fin 1), x)) (Y.lg i) = _
  rw [Y.lg_lin i _ (by rw [Finsupp.degree_mapDomain]; exact hμ), ← uncurry_X i]
  rfl

theorem FBChart.ex_lg_at' (Y : FBChart C V O dd) {τ : Type} (A : Fin dd → MvPowerSeries τ C)
    (hA : ∀ j, MvPowerSeries.constantCoeff (A j) = 0) (i : Fin dd) :
    MvPowerSeries.subst (fun j => MvPowerSeries.subst A (un1 (Y.lg j))) (un1 (Y.ex i)) = A i := by
  have hA' := MvPowerSeries.hasSubst_of_constantCoeff_zero hA
  have hL : MvPowerSeries.HasSubst (fun j => un1 (Y.lg j)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun j => Y.uncurry_log_constantCoeff_chart j
  rw [← MvPowerSeries.subst_comp_subst_apply hL hA', Y.uncurry_exp_log_eq_X, MvPowerSeries.subst_X hA']

theorem hom_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} {U : Fin dd → C} (hγ : IsCv V γ)
    (hlg : Y.LgLin γ U) (i : Fin dd) (μ : Fin 2 →₀ ℕ) (hμ0 : μ 0 < V.l) (hμ1 : μ 1 < V.l) :
    MvPowerSeries.coeff μ
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F i) -
        cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ i)) = 0 := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hX : ∀ k : Fin 2, MvPowerSeries.constantCoeff (MvPowerSeries.X k : MvPowerSeries (Fin 2) C) = 0 :=
    fun k => MvPowerSeries.constantCoeff_X k
  have hS : MvPowerSeries.constantCoeff (MvPowerSeries.X 0 + MvPowerSeries.X 1 : MvPowerSeries (Fin 2) C) = 0 := by
    rw [map_add (f := _), hX 0, hX 1, add_zero]
  have hP0 : ∀ (k : Fin 2) (j : Fin dd), MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X k) (γ j)) = 0 :=
    fun k j => const_cvAt (hX k) (hγ0 j)
  have hQ0 : ∀ j, MvPowerSeries.constantCoeff (cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j)) = 0 :=
    fun j => const_cvAt hS (hγ0 j)
  have hPP : MvPowerSeries.HasSubst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) :=
    MvPowerSeries.hasSubst_of_constantCoeff_zero fun q => hP0 q.1 q.2
  have hFP0 : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j)) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero hPP (fun q => hP0 q.1 q.2) (Y.B.G.const j)
  have hAt : ∀ (s : MvPowerSeries (Fin 2) C), MvPowerSeries.constantCoeff s = 0 → ∀ j,
      Agr (V.l ^ 2) (MvPowerSeries.subst (fun j' => cvAt s (γ j')) (un1 (Y.lg j))) (U j • s) := by
    intro s hs j
    rw [subst_cvAt hs hγ0, ← cvAt_smul_X hs]
    exact agr_subst_right (a := fun _ : Unit => s) (fun _ => hs) (hlg j)
  have hsum : ∀ j, Agr (V.l ^ 2)
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j)))
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) := by
    intro j
    refine ((hAt _ (hX 0) j).add (hAt _ (hX 1) j)).trans ?_
    rw [← smul_add]
    exact (hAt _ hS j).symm
  have e1 := Y.ex_lg_at' _ hFP0 i
  have e1' : (fun j => MvPowerSeries.subst
      (fun j' => MvPowerSeries.subst (fun q : Fin 2 × Fin dd => cvAt (MvPowerSeries.X q.1) (γ q.2)) (Y.B.G.F j'))
      (un1 (Y.lg j))) = fun j =>
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j)) := by
    funext j
    exact lg_addOf Y (fun k j' => cvAt (MvPowerSeries.X k) (γ j')) hP0 j
  rw [e1'] at e1
  have e2 := Y.ex_lg_at' _ hQ0 i
  have hc : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0) (γ j')) (un1 (Y.lg j)) +
        MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) = 0 := by
    intro j
    rw [map_add (f := _), MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 0 j') (fun j' => hP0 0 j') (Y.uncurry_log_constantCoeff_chart j),
      MvPowerSeries.constantCoeff_subst_eq_zero
        (MvPowerSeries.hasSubst_of_constantCoeff_zero fun j' => hP0 1 j') (fun j' => hP0 1 j') (Y.uncurry_log_constantCoeff_chart j),
      add_zero]
  have hc' : ∀ j, MvPowerSeries.constantCoeff
      (MvPowerSeries.subst (fun j' => cvAt (MvPowerSeries.X 0 + MvPowerSeries.X 1) (γ j')) (un1 (Y.lg j))) = 0 :=
    fun j => MvPowerSeries.constantCoeff_subst_eq_zero
      (MvPowerSeries.hasSubst_of_constantCoeff_zero hQ0) hQ0 (Y.uncurry_log_constantCoeff_chart j)
  have hag := agr_subst_left hc hc' hsum (un1 (Y.ex i))
  rw [e1, e2] at hag
  have hdeg : μ.degree < V.l ^ 2 := by
    rw [Finsupp.degree_eq_sum, Fin.sum_univ_two]
    nlinarith
  rw [map_sub, sub_eq_zero]
  exact hag μ hdeg

theorem coeff1_of_lgLin (Y : FBChart C V O dd) {γ : Fin dd → PowerSeries C} {U : Fin dd → C} (hγ : IsCv V γ)
    (hlg : Y.LgLin γ U) (i : Fin dd) : PowerSeries.coeff 1 (γ i) = U i := by
  have hl := V.l_prime.two_le
  have hγ0 : ∀ j, PowerSeries.constantCoeff (γ j) = 0 := fun j => (hγ j).1
  have hlin : Agr 2 (un1 (Y.lg i)) (MvPowerSeries.X i) := fun e he => Y.uncurry_linear_combination i e (by omega)
  have h2 := agr_subst_right (a := γ) hγ0 hlin
  rw [MvPowerSeries.subst_X (MvPowerSeries.hasSubst_of_constantCoeff_zero hγ0)] at h2
  have h3 := (hlg i).mono (show 2 ≤ V.l ^ 2 by nlinarith)
  have h4 := (h2.symm.trans h3) (Finsupp.single () 1) (by rw [Finsupp.degree_single]; omega)
  change PowerSeries.coeff 1 (γ i) = PowerSeries.coeff 1 _ at h4
  rw [h4, map_smul, coeffX', if_pos rfl, smul_eq_mul, mul_one]

theorem agr_of_ty {I : Fin 2 → Type} [∀ g, Fintype (I g)] {g : Fin 2} {w : I g → C} {x : ℕ → I g ⊕ JJ I g → C}
    (h0 : x 0 = Sum.elim w 0) (h1 : ∀ c, x 1 (Sum.inl c) = 0) (cf : I g → C) :
    Agr (V.l ^ 2) (∑ c : I g, cf c • tyS V.l (fun s => x s (Sum.inl c)))
      ((∑ c, cf c * w c) • (MvPowerSeries.X () : PowerSeries C)) := by
  intro e he
  have hl := V.l_prime.two_le
  obtain ⟨n, rfl⟩ : ∃ n, e = Finsupp.single () n := ⟨e (), Finsupp.unique_single e⟩
  rw [Finsupp.degree_single] at he
  change PowerSeries.coeff n _ = PowerSeries.coeff n _
  set_option synthInstance.maxHeartbeats 100000 in
    rw [map_sum, map_smul, coeffX']
  simp only [map_smul, smul_eq_mul, tyS_good_coeff h0 h1 hl _ n he]
  by_cases hn1 : n = 1
  · simp [hn1]
  · simp [hn1]

end Formalism.L2.FormalSeriesBounds
end
end

