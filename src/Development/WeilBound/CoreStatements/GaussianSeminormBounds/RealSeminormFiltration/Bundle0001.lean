module

public import Mathlib

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasA
section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

theorem pos_of_eig {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (S : E →ₗ[ℂ] E) (hS : S.IsSymmetric) (h : ∀ t : ℝ, t ≤ 0 → ∀ x, S x = (t : ℂ) • x → x = 0) (x : E) :
    0 ≤ (⟪x, S x⟫_ℂ).re ∧ ((⟪x, S x⟫_ℂ).re = 0 → x = 0) := by
  let b := hS.eigenvectorBasis (n := Module.finrank ℂ E) rfl
  let ev := hS.eigenvalues (n := Module.finrank ℂ E) rfl
  have hb : ∀ i, S (b i) = (ev i : ℂ) • b i := fun i => hS.apply_eigenvectorBasis rfl i
  have hev : ∀ i, 0 < ev i := by
    intro i
    by_contra hc
    exact b.orthonormal.ne_zero i (h _ (not_lt.1 hc) _ (hb i))
  have key : (⟪x, S x⟫_ℂ).re = ∑ i, ev i * Complex.normSq ⟪b i, x⟫_ℂ := by
    rw [← b.sum_inner_mul_inner x (S x), Complex.re_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← hS (b i) x, hb, inner_smul_left, Complex.conj_ofReal, ← inner_conj_symm x (b i), mul_left_comm,
      ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul, Complex.ofReal_re]
  have hnn : ∀ i ∈ Finset.univ, 0 ≤ ev i * Complex.normSq ⟪b i, x⟫_ℂ :=
    fun i _ => mul_nonneg (hev i).le (Complex.normSq_nonneg _)
  rw [key]
  refine ⟨Finset.sum_nonneg hnn, fun h0 => ?_⟩
  rw [Finset.sum_eq_zero_iff_of_nonneg hnn] at h0
  have hz : ∀ i, ⟪b i, x⟫_ℂ = 0 := fun i =>
    Complex.normSq_eq_zero.1 ((mul_eq_zero.1 (h0 i (Finset.mem_univ i))).resolve_left (hev i).ne')
  rw [← b.sum_repr' x]
  simp [hz]

section Ops

variable {I : Type} [Fintype I] {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

def matOp (m : Matrix I I ℂ) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => ∑ j, m i j • Θ j)
  map_add' x y := by
    ext i
    simp [Finset.sum_add_distrib]
  map_smul' a x := by
    ext i
    simp [Finset.smul_sum, smul_comm a]

def valOp (A : Module.End ℂ V) : Module.End ℂ (PiLp 2 (fun _ : I => V)) where
  toFun Θ := WithLp.toLp 2 (fun i => A (Θ i))
  map_add' x y := by
    ext i
    simp
  map_smul' a x := by
    ext i
    simp

theorem matOp_apply (m : Matrix I I ℂ) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    matOp m Θ i = ∑ j, m i j • Θ j := rfl

theorem valOp_apply (A : Module.End ℂ V) (Θ : PiLp 2 (fun _ : I => V)) (i : I) :
    valOp A Θ i = A (Θ i) := rfl

theorem matOp_adj (m : Matrix I I ℂ) (x y : PiLp 2 (fun _ : I => V)) :
    ⟪matOp m x, y⟫_ℂ = ⟪x, matOp mᴴ y⟫_ℂ := by
  simp only [PiLp.inner_apply, matOp_apply, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
    conjTranspose_apply]
  rw [Finset.sum_comm]
  rfl

end Ops

theorem cas_one {K I : Type} [Fintype K] [Fintype I] [DecidableEq I] (σ : K → K) (hσ : Function.Involutive σ)
    {M : Type} [AddCommGroup M] [Module ℂ M] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M)
    (c : K → Matrix I I ℂ) (d c0 : ℝ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h3 : ∀ k, c (σ k) = (c k)ᴴ)
    (h4 : ∑ k, c k * c (σ k) = (d : ℂ) • (1 : Matrix I I ℂ))
    {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (ρ : K → Module.End ℂ V) (hadj : ∀ k u v, ⟪ρ k u, v⟫_ℂ = ⟪u, ρ (σ k) v⟫_ℂ)
    (hc0 : ∑ k, ρ k * ρ (σ k) = (c0 : ℂ) • (1 : Module.End ℂ V))
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v))
    (h5 : ∀ t : ℝ, t ≤ c0 + d → ∀ x ∈ Submodule.span ℂ {y | ∃ i v, y = X i (ι v)},
      (∑ k, e k * e (σ k)) x = (t : ℂ) • x → x = 0)
    (Φ : I → V) (hΦ : ∀ Θ : I → V, ∑ i, X i (ι (Θ i)) = 0 → ∑ i, ⟪Φ i, Θ i⟫_ℂ = 0) :
    0 ≤ (∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re ∧
      ((∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ).re = 0 → Φ = 0) := by
  let R : K → Module.End ℂ (PiLp 2 (fun _ : I => V)) := fun k => matOp (c k) + valOp (ρ k)
  have hRa : ∀ k Θ i, R k Θ i = ∑ j, c k i j • Θ j + ρ k (Θ i) := fun k Θ i => rfl
  have hRadj : ∀ k x y, ⟪R k x, y⟫_ℂ = ⟪x, R (σ k) y⟫_ℂ := by
    intro k x y
    simp only [R, LinearMap.add_apply, inner_add_left, inner_add_right]
    rw [matOp_adj, h3]
    congr 1
    simp only [PiLp.inner_apply, valOp_apply, hadj]
  let m1 : PiLp 2 (fun _ : I => V) →ₗ[ℂ] M :=
    { toFun := fun Θ => ∑ i, X i (ι (Θ i))
      map_add' := fun x y => by simp [Finset.sum_add_distrib]
      map_smul' := fun a x => by simp [Finset.smul_sum] }
  have hm1 : ∀ Θ, m1 Θ = ∑ i, X i (ι (Θ i)) := fun _ => rfl
  have hem : ∀ k Θ, e k (m1 Θ) = m1 (R k Θ) := by
    intro k Θ
    have h1' : ∀ i y, e k (X i y) = ∑ j, c k j i • X j y + X i (e k y) := by
      intro i y
      have := LinearMap.congr_fun (h1 k i) y
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at this
      rw [← this]; abel
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [hm1, hRa, map_sum, map_add (f := _), map_smul, h1', hι, Finset.sum_add_distrib]
    rw [Finset.sum_comm]
  let N := (LinearMap.ker m1)ᗮ
  have hRN : ∀ k, ∀ x ∈ N, R k x ∈ N := by
    intro k x hx
    rw [Submodule.mem_orthogonal'] at hx ⊢
    intro u hu
    rw [hRadj]
    apply hx
    rw [LinearMap.mem_ker] at hu ⊢
    rw [← hem, hu, map_zero]
  let S : Module.End ℂ (PiLp 2 (fun _ : I => V)) := ∑ k, R k * R (σ k) - ((c0 + d : ℝ) : ℂ) • 1
  have hSa : ∀ x, S x = ∑ k, R k (R (σ k) x) - ((c0 + d : ℝ) : ℂ) • x := by
    intro x
    simp only [S, LinearMap.sub_apply, LinearMap.sum_apply, Module.End.mul_apply, LinearMap.smul_apply,
      Module.End.one_apply]
  have hS : LinearMap.IsSymmetric S := by
    intro x y
    rw [hSa, hSa, inner_sub_left, inner_sub_right, sum_inner, inner_sum, inner_smul_left, inner_smul_right,
      Complex.conj_ofReal]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hRadj, hRadj, hσ]
  have hSN : ∀ x ∈ N, S x ∈ N := by
    intro x hx
    rw [hSa]
    exact N.sub_mem (N.sum_mem fun k _ => hRN _ _ (hRN _ _ hx)) (N.smul_mem _ hx)
  have hΦN : WithLp.toLp 2 Φ ∈ N := by
    rw [Submodule.mem_orthogonal']
    intro u hu
    rw [PiLp.inner_apply]
    exact hΦ (fun i => u i) hu
  have hpos := pos_of_eig (S.restrict hSN) (hS.restrict_invariant hSN) (by
    intro t ht x hx
    have hx' : S x.1 = (t : ℂ) • x.1 := congrArg Subtype.val hx
    have h0 : m1 x.1 = 0 := by
      refine h5 (t + (c0 + d)) (by linarith) _ ?_ ?_
      · rw [hm1]
        exact Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨i, _, rfl⟩
      · rw [hSa, sub_eq_iff_eq_add, ← add_smul] at hx'
        rw [LinearMap.sum_apply]
        simp only [Module.End.mul_apply, hem]
        set_option synthInstance.maxHeartbeats 100000 in
          rw [← map_sum, hx', map_smul]
        push_cast
        rfl
    have h2 : ⟪x.1, x.1⟫_ℂ = 0 := (Submodule.mem_orthogonal' _ _).1 x.2 _ h0
    exact Subtype.ext (inner_self_eq_zero.1 h2)) ⟨_, hΦN⟩
  have hval : ∀ i, S (WithLp.toLp 2 Φ) i = (2 : ℂ) • ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
    intro i
    have e1 : ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l = (d : ℂ) • Φ i := by
      have : ∀ l, ∑ k, ∑ j, c k i j * c (σ k) j l = (d : ℂ) * (if i = l then 1 else 0) := by
        intro l
        have := congrFun (congrFun h4 i) l
        simpa [Matrix.sum_apply, Matrix.mul_apply, Matrix.one_apply] using this
      calc ∑ k, ∑ j, c k i j • ∑ l, c (σ k) j l • Φ l
          = ∑ k, ∑ l, ∑ j, (c k i j * c (σ k) j l) • Φ l := by
            refine Finset.sum_congr rfl fun k _ => ?_
            rw [Finset.sum_comm]
            simp only [Finset.smul_sum, smul_smul]
        _ = ∑ l, (∑ k, ∑ j, c k i j * c (σ k) j l) • Φ l := by
            rw [Finset.sum_comm]
            simp only [Finset.sum_smul]
        _ = (d : ℂ) • Φ i := by simp [this]
    have e2 : ∑ k, ρ k (ρ (σ k) (Φ i)) = (c0 : ℂ) • Φ i := by
      have := LinearMap.congr_fun hc0 (Φ i)
      simpa [LinearMap.sum_apply] using this
    have e3 : ∑ k, ρ k (∑ l, c (σ k) i l • Φ l) = ∑ k, ∑ j, c k i j • ρ (σ k) (Φ j) := by
      rw [← Equiv.sum_comp hσ.toPerm]
      refine Finset.sum_congr rfl fun k _ => ?_
      set_option synthInstance.maxHeartbeats 100000 in
        simp only [Function.Involutive.coe_toPerm, hσ k, map_sum, map_smul]
    have e4 : S (WithLp.toLp 2 Φ) i = ∑ k, R k (R (σ k) (WithLp.toLp 2 Φ)) i - ((c0 + d : ℝ) : ℂ) • Φ i := by
      rw [hSa]
      simp
    rw [e4]
    simp only [hRa, smul_add, map_add (f := _), Finset.sum_add_distrib]
    rw [e1, e2, e3, two_smul]
    push_cast
    rw [add_smul]
    abel
  have hin : (⟪(⟨_, hΦN⟩ : N), S.restrict hSN ⟨_, hΦN⟩⟫_ℂ) =
      2 * ∑ k, ∑ i, ∑ j, ⟪Φ i, c k i j • ρ (σ k) (Φ j)⟫_ℂ := by
    change ⟪WithLp.toLp 2 Φ, S (WithLp.toLp 2 Φ)⟫_ℂ = _
    rw [PiLp.inner_apply, Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hval, inner_smul_right]
    simp only [inner_sum]
  rw [hin] at hpos
  have h2re : ∀ z : ℂ, (2 * z).re = 2 * z.re := fun z => by simp
  rw [h2re] at hpos
  refine ⟨by linarith [hpos.1], fun h0 => ?_⟩
  have := congrArg Subtype.val (hpos.2 (by rw [h0, mul_zero]))
  funext i
  exact congrArg (fun z : PiLp 2 (fun _ : I => V) => z i) this

end PositivityTheory.KReal

end
end

-- bundled from Development.WeilBound.CoreStatements.GaussianSeminormBounds.RealSeminormFiltration.CoreCasB
section
noncomputable section

open Matrix
open scoped InnerProductSpace

namespace PositivityTheory.KReal

variable {K I : Type} {M : Type} [AddCommGroup M] [Module ℂ M] {V : Type} [AddCommGroup V] [Module ℂ V]

def wordX (X : I → Module.End ℂ M) (l : List I) : Module.End ℂ M := (l.map X).prod

def filtX (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) : Submodule ℂ M :=
  Submodule.span ℂ {y | ∃ (l : List I) (v : V), l.length ≤ n ∧ y = wordX X l (ι v)}

theorem wordX_cons (X : I → Module.End ℂ M) (a : I) (l : List I) (y : M) :
    wordX X (a :: l) y = X a (wordX X l y) := by
  simp [wordX]

theorem filtX_zero (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) : filtX X ι 0 = LinearMap.range ι := by
  apply le_antisymm
  · rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    have : l = [] := List.length_eq_zero_iff.1 (Nat.le_zero.1 hl)
    subst this
    exact ⟨v, by simp [wordX]⟩
  · rintro _ ⟨v, rfl⟩
    exact Submodule.subset_span ⟨[], v, le_rfl, by simp [wordX]⟩

theorem filtX_mono (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) {m n : ℕ} (h : m ≤ n) :
    filtX X ι m ≤ filtX X ι n := by
  refine Submodule.span_mono ?_
  rintro _ ⟨l, v, hl, rfl⟩
  exact ⟨l, v, hl.trans h, rfl⟩

theorem filtX_X (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) (i : I) :
    ∀ x ∈ filtX X ι n, X i x ∈ filtX X ι (n + 1) := by
  have : filtX X ι n ≤ (filtX X ι (n + 1)).comap (X i) := by
    rw [filtX, Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact Submodule.subset_span ⟨i :: l, v, by simpa using hl, (wordX_cons X i l _).symm⟩
  exact fun x hx => this hx

theorem filtX_fd [Fintype I] [FiniteDimensional ℂ V] (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    FiniteDimensional ℂ (filtX X ι n) := by
  induction n with
  | zero => rw [filtX_zero]; infer_instance
  | succ n ih =>
    classical
    have hle : filtX X ι (n + 1) ≤ filtX X ι n ⊔ ⨆ i, (filtX X ι n).map (X i) := by
      rw [filtX, Submodule.span_le]
      rintro _ ⟨l, v, hl, rfl⟩
      cases l with
      | nil => exact Submodule.mem_sup_left (Submodule.subset_span ⟨[], v, Nat.zero_le _, rfl⟩)
      | cons a l =>
        refine Submodule.mem_sup_right (Submodule.mem_iSup_of_mem a ?_)
        exact ⟨wordX X l (ι v), Submodule.subset_span ⟨l, v, by simpa using hl, rfl⟩, (wordX_cons X a l _).symm⟩
    exact Submodule.finiteDimensional_of_le hle

theorem filtX_succ_le (X : I → Module.End ℂ M) (ι : V →ₗ[ℂ] M) (n : ℕ) :
    filtX X ι (n + 1) ≤ filtX X ι n ⊔
      Submodule.span ℂ {y | ∃ (w : Fin (n + 1) → I) (v : V), y = wordX X (List.ofFn w) (ι v)} := by
  conv_lhs => rw [filtX]
  rw [Submodule.span_le]
  rintro _ ⟨l, v, hl, rfl⟩
  by_cases h : l.length ≤ n
  · exact Submodule.mem_sup_left (Submodule.subset_span ⟨l, v, h, rfl⟩)
  · have h' : l.length = n + 1 := by omega
    refine Submodule.mem_sup_right (Submodule.subset_span ⟨fun i => l.get (i.cast h'.symm), v, ?_⟩)
    congr 2
    apply List.ext_getElem
    · simp [h']
    · intro m h1 h2
      rw [List.getElem_ofFn]
      simp

theorem filtX_e [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) (n : ℕ) (k : K) :
    ∀ x ∈ filtX X ι n, e k x ∈ filtX X ι n := by
  have key : ∀ (l : List I) (v : V), e k (wordX X l (ι v)) ∈ filtX X ι l.length := by
    intro l v
    induction l with
    | nil =>
      have : e k (wordX X [] (ι v)) = wordX X [] (ι (ρ k v)) := by simp [wordX, hι]
      rw [this]
      exact Submodule.subset_span ⟨[], _, le_rfl, rfl⟩
    | cons a l ih =>
      have h := LinearMap.congr_fun (h1 k a) (wordX X l (ι v))
      simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.sum_apply, LinearMap.smul_apply] at h
      rw [wordX_cons, sub_eq_iff_eq_add.1 h, List.length_cons]
      refine Submodule.add_mem _ (Submodule.sum_mem _ fun j _ => Submodule.smul_mem _ _ ?_)
        (filtX_X X ι _ a _ ih)
      exact filtX_X X ι _ j _ (Submodule.subset_span ⟨l, v, le_rfl, rfl⟩)
  have : filtX X ι n ≤ (filtX X ι n).comap (e k) := by
    conv_lhs => rw [filtX]
    rw [Submodule.span_le]
    rintro _ ⟨l, v, hl, rfl⟩
    exact filtX_mono X ι hl (key l v)
  exact fun x hx => this hx

theorem filtX_perm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j)
    (h2 : ∀ i j, X i * X j - X j * X i ∈ Submodule.span ℂ (Set.range e)) (ρ : K → Module.End ℂ V)
    (ι : V →ₗ[ℂ] M) (hι : ∀ k v, ι (ρ k v) = e k (ι v)) {l l' : List I} (h : l.Perm l') (n : ℕ)
    (hn : l.length ≤ n + 1) (v : V) : wordX X l (ι v) - wordX X l' (ι v) ∈ filtX X ι n := by
  induction h generalizing n with
  | nil => simp
  | @cons a l l' hp ih =>
    rw [wordX_cons, wordX_cons, ← map_sub]
    cases n with
    | zero =>
      have h0 : l = [] := List.length_eq_zero_iff.1 (by simpa using hn)
      subst h0
      have h0' : l' = [] := hp.nil_eq.symm
      subst h0'
      simp
    | succ n => exact filtX_X X ι n a _ (ih n (by simpa using hn))
  | swap a b l =>
    have hl : l.length ≤ n := by simp only [List.length_cons] at hn; omega
    have hm : wordX X l (ι v) ∈ filtX X ι n := Submodule.subset_span ⟨l, v, hl, rfl⟩
    have hall : ∀ E ∈ Submodule.span ℂ (Set.range e), E (wordX X l (ι v)) ∈ filtX X ι n := by
      intro E hE
      induction hE using Submodule.span_induction with
      | mem E hE =>
        obtain ⟨k, rfl⟩ := hE
        exact filtX_e e X c h1 ρ ι hι n k _ hm
      | zero => simp
      | add E F _ _ h1 h2 => exact Submodule.add_mem _ h1 h2
      | smul a E _ h1 => exact Submodule.smul_mem _ a h1
    simp only [wordX_cons]
    exact hall _ (h2 b a)
  | trans p1 p2 ih1 ih2 =>
    have := Submodule.add_mem _ (ih1 n hn) (ih2 n (p1.length_eq ▸ hn))
    rwa [sub_add_sub_cancel] at this

theorem wordX_comm [Fintype I] (e : K → Module.End ℂ M) (X : I → Module.End ℂ M) (c : K → Matrix I I ℂ)
    (h1 : ∀ k i, e k * X i - X i * e k = ∑ j, c k j i • X j) (k : K) (n : ℕ) (w : Fin n → I) :
    e k * wordX X (List.ofFn w) = wordX X (List.ofFn w) * e k +
      ∑ i, ∑ j, c k j (w i) • wordX X (List.ofFn (Function.update w i j)) := by
  induction n with
  | zero => simp [wordX]
  | succ n ih =>
    have hc : ∀ (a : I) (l : List I), wordX X (a :: l) = X a * wordX X l := fun a l => by simp [wordX]
    have u0 : ∀ j, List.ofFn (Function.update w 0 j) = j :: List.ofFn (fun i : Fin n => w i.succ) := by
      intro j
      rw [List.ofFn_succ]
      simp [Function.update_of_ne (Fin.succ_ne_zero _)]
    have us : ∀ (i : Fin n) j, List.ofFn (Function.update w i.succ j) =
        w 0 :: List.ofFn (Function.update (fun i : Fin n => w i.succ) i j) := by
      intro i j
      rw [List.ofFn_succ, Function.update_of_ne (Fin.succ_ne_zero i).symm]
      congr 2
      funext m
      by_cases hm : m = i
      · subst hm; simp
      · rw [Function.update_of_ne hm, Function.update_of_ne (fun h => hm (Fin.succ_injective _ h))]
    rw [Fin.sum_univ_succ]
    simp only [u0, us, hc]
    rw [List.ofFn_succ, hc, ← mul_assoc, sub_eq_iff_eq_add.1 (h1 k (w 0)), add_mul, mul_assoc,
      ih (fun i => w i.succ), mul_add, Finset.sum_mul, Finset.mul_sum]
    simp only [Finset.mul_sum, mul_smul_comm, smul_mul_assoc, mul_assoc]
    abel

end PositivityTheory.KReal

end
end

