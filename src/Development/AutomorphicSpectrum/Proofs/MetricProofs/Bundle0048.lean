module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0040
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0032
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartFirst
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo

section Gen

variable {e N : ℕ} {s : Set (Fin e → ℂ)}

theorem analytic_minorIJ (g : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun w => minorIJ (g w) I J) s := by
  by_cases e' : I.card = J.card
  · have hfun : (fun w => minorIJ (g w) I J) = fun w => ∑ σ : Equiv.Perm (Fin J.card),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i) := by
      funext w
      rw [minorIJ, dite_eq_left e', Matrix.det_apply']
      rfl
    rw [hfun]
    have H := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Equiv.Perm (Fin J.card)))
      (f := fun σ w => ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i))
      (fun σ _ => analyticOnNhd_const.mul (by
        have P := Finset.analyticOnNhd_prod (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Fin J.card))
          (f := fun i w => g w (I.orderEmbOfFin e' (σ i)) (J.orderEmbOfFin rfl i)) (fun i _ => hg _ _)
        convert P using 1
        funext w
        rw [Finset.prod_apply]))
    convert H using 1
    funext w
    rw [Finset.sum_apply]
  · have hfun : (fun w => minorIJ (g w) I J) = fun _ => 0 := by
      funext w
      rw [minorIJ, dite_eq_right e']
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_mul_entry (g g' : (Fin e → ℂ) → Matrix (Fin N) (Fin N) ℂ)
    (hg : ∀ a b, AnalyticOnNhd ℂ (fun w => g w a b) s)
    (hg' : ∀ a b, AnalyticOnNhd ℂ (fun w => g' w a b) s) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (g w * g' w) a b) s := by
  simp only [Matrix.mul_apply]
  have H := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) (Finset.univ : Finset (Fin N))
    (f := fun c w => g w a c * g' w c b) (fun c _ => (hg a c).mul (hg' c b))
  convert H using 1
  funext w
  rw [Finset.sum_apply]

theorem analytic_coord (i : Fin e) : AnalyticOnNhd ℂ (fun w : Fin e → ℂ => w i) s := by
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ) i).analyticOnNhd s

end Gen

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {n e : ℕ}

theorem analytic_lowMat (s : Set (Fin e → ℂ)) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' a b) s := by
  by_cases hc : b < a ∧ ((a : ℕ) < N - j ↔ (b : ℕ) < N - j)
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun w => w (ε (Sum.inr (Sum.inl ⟨(τ', a, b), hc⟩))) := by
      funext w
      simp only [lowMat]
      rw [dite_eq_left hc]
      rfl
    rw [hfun]
    exact analytic_coord _
  · have hfun : (fun w => lowMat (wL ε w) τ' a b) = fun _ => if a = b then (1 : ℂ) else 0 := by
      funext w
      simp only [lowMat]
      rw [dite_eq_right hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_wH (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => wH h ε τ' w a b) s := by
  exact analytic_mul_entry (s := s) (fun _ => h τ') (fun w => lowMat (wL ε w) τ') (fun _ _ => analyticOnNhd_const)
    (fun a b => analytic_lowMat s ε τ' a b) a b

theorem analytic_wH_snd (s : Set (Fin e → ℂ)) (h : Ψ → Matrix (Fin N) (Fin N) ℂ)
    (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ : Ψ) (ca cb : Fin N) (a b : Fin N) :
    AnalyticOnNhd ℂ (fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a b) s := by
  refine analytic_mul_entry (s := s) (fun w => wH h ε τ w) (fun w => 1 + Matrix.single cb ca (wT ε w))
    (fun a b => analytic_wH s h ε τ a b) (fun a' b' => ?_) a b
  beta_reduce
  by_cases hc : cb = a' ∧ ca = b'
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun w => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + w (ε (Sum.inr (Sum.inr ()))) := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_pos hc]
      rfl
    rw [hfun]
    exact analyticOnNhd_const.add (analytic_coord _)
  · have hfun : (fun w => (1 + Matrix.single cb ca (wT ε w)) a' b') =
        fun _ => (1 : Matrix (Fin N) (Fin N) ℂ) a' b' + 0 := by
      funext w
      rw [Matrix.add_apply, Matrix.single_apply, if_neg hc]
    rw [hfun]
    exact analyticOnNhd_const

theorem analytic_flagZ (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) {s : Set (Fin e → ℂ)}
    (zb : (Fin e → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (H : (Fin e → ℂ) → Ψ → Matrix (Fin N) (Fin N) ℂ)
    (hzb : ∀ q, AnalyticOnNhd ℂ (fun w => zb w q) s)
    (hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (zb w)) s)
    (hH : ∀ τ' a b, AnalyticOnNhd ℂ (fun w => H w τ' a b) s) (q : Σ k, ι k) :
    AnalyticOnNhd ℂ (fun w => flagZ M F (zb w) (H w) q) s := by
  by_cases e' : ∃ p, M.blk p = some q.1
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w =>
        ∑ I, valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2) := by
      funext w
      simp only [flagZ]
      rw [dite_eq_left e']
    rw [hfun]
    have S := Finset.analyticOnNhd_sum (𝕜 := ℂ) (s := s) Finset.univ
      (f := fun I w => valAt M.x (F.u q I) (zb w) * minorIJ (H w e'.choose.1) I (stepCols N j e'.choose.2))
      (fun I _ => (hval q I).mul (analytic_minorIJ (fun w => H w e'.choose.1) (fun a b => hH _ a b) I _))
    convert S using 1
    funext w
    rw [Finset.sum_apply]
  · have hfun : (fun w => flagZ M F (zb w) (H w) q) = fun w => zb w ⟨⟨q.1, fun p hp => e' ⟨p, hp⟩⟩, q.2⟩ := by
      funext w
      simp only [flagZ]
      rw [dite_eq_right e']
    rw [hfun]
    exact hzb _

theorem analytic_wB {Λ : Type} (ε : Fin n ⊕ Λ ⊕ Unit ≃ Fin e) (V : Set (Fin n → ℂ)) :
    AnalyticOnNhd ℂ (wB ε) (wD ε V) := by
  exact AnalyticOnNhd.pi (fun i => analytic_coord (s := wD ε V) (ε (Sum.inl i)))

end Flag

theorem wPhi_holo : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → ∀ p, AnalyticOnNhd ℂ (fun w => wPhi M F bl h ε k₀ τ ca cb w p) (wD ε V) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hctx p
  obtain ⟨-, -, -, -, -, -, -, ⟨-, -, hbl, hvl, -⟩, -, -, -⟩ := hctx
  have hB : AnalyticOnNhd ℂ (wB ε) (wD ε V) := analytic_wB ε V
  have hmaps : Set.MapsTo (wB ε) (wD ε V) V := fun w hw => hw
  have hzb : ∀ q, AnalyticOnNhd ℂ (fun w => bl (wB ε w) q) (wD ε V) := fun q => (hbl q).comp hB hmaps
  have hval : ∀ q I, AnalyticOnNhd ℂ (fun w => valAt M.x (F.u q I) (bl (wB ε w))) (wD ε V) :=
    fun q I => (hvl q I).comp hB hmaps
  obtain ⟨o, m⟩ := p
  cases o with
  | some k =>
    exact analytic_flagZ M F (fun w => bl (wB ε w)) (fun w τ' => wH h ε τ' w) hzb hval
      (fun τ' a' b' => analytic_wH _ h ε τ' a' b') ⟨k, m⟩
  | none =>
    refine analytic_flagZ M F (fun w => bl (wB ε w))
      (fun w => Function.update (fun τ' => wH h ε τ' w) τ (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))))
      hzb hval ?_ ⟨k₀, m⟩
    intro τ' a' b'
    by_cases hτ : τ' = τ
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') =
          fun w => (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) a' b' := by
        funext w
        rw [Function.update_apply, if_pos hτ]
      rw [hfun]
      exact analytic_wH_snd _ h ε τ ca cb a' b'
    · have hfun : (fun w => Function.update (fun τ'' => wH h ε τ'' w) τ
          (wH h ε τ w * (1 + Matrix.single cb ca (wT ε w))) τ' a' b') = fun w => wH h ε τ' w a' b' := by
        funext w
        rw [Function.update_apply, if_neg hτ]
      rw [hfun]
      exact analytic_wH _ h ε τ' a' b'

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Holo
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentChartSecond
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq GlobalTheory.CompanionTheory.Ar.PB.WMan

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact

open GlobalTheory.CompanionTheory.Ar.PB.MinorCalc

section Minor

variable {N : ℕ}

theorem minorIJ_mul_one_add_single (H : Matrix (Fin N) (Fin N) ℂ) (I C : Finset (Fin N)) {ca cb : Fin N} (hlt : ca < cb)
    (hiff : ca ∈ C ↔ cb ∈ C) (t : ℂ) :
    minorIJ (H * (1 + Matrix.single cb ca t)) I C = minorIJ H I C := by
  have hne : ∀ x, ¬ (x = cb ∧ x = ca) := fun x hx => hlt.ne (hx.2.symm.trans hx.1)
  have hent : ∀ x y, (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) x y =
      (if x = y then 1 else 0) + (if x = cb ∧ y = ca then t else 0) := by
    intro x y
    simp [Matrix.add_apply, Matrix.one_apply, Matrix.single_apply, eq_comm]
  rw [minorIJ_mul_of_support H _ I C]
  · have h1 : minorIJ (1 + Matrix.single cb ca t : Matrix (Fin N) (Fin N) ℂ) C C = 1 := by
      rw [minorIJ_eq_det _ C C _ rfl rfl, Matrix.det_of_lowerTriangular]
      · refine Finset.prod_eq_one fun x _ => ?_
        rw [Matrix.submatrix_apply, hent, if_pos rfl, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        exact hne _ ⟨e1, e2⟩
      · intro x y hxy
        have hxy' : x < y := hxy
        have hs := (C.orderEmbOfFin rfl).strictMono hxy'
        rw [Matrix.submatrix_apply, hent, if_neg hs.ne, if_neg, add_zero]
        rintro ⟨e1, e2⟩
        rw [e1, e2] at hs
        exact absurd hs (not_lt.mpr hlt.le)
    rw [h1, mul_one]
  · intro k c hc hk
    have hkc : k ≠ c := by
      rintro rfl
      exact hk hc
    rw [hent, if_neg hkc, if_neg, add_zero]
    rintro ⟨e1, e2⟩
    rw [e1] at hk
    rw [e2] at hc
    exact hk (hiff.mp hc)

theorem mem_stepCols_iff {j : ℕ} {a b ca cb i : Fin N} (hb : (b : ℕ) = a + 1) (h2 : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have h3 := i.2
  have h4 := b.2
  have h5 := ca.2
  have h6 := cb.2
  have hi' : (i : ℕ) ≠ a := fun e => hi (Fin.ext e)
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

end Minor

section Low

variable {Ψ : Type} {N j : ℕ}

theorem lowMat_isBlockDiag (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : IsBlockDiag j (lowMat c τ) := by
  intro x y hxy
  unfold lowMat
  rw [_root_.dite_eq_right (fun e => hxy e.2), if_neg]
  rintro rfl
  exact hxy Iff.rfl

theorem lowMat_det (c : LowIdx Ψ N j → ℂ) (τ : Ψ) : (lowMat c τ).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · refine Finset.prod_eq_one fun x _ => ?_
    unfold lowMat
    rw [_root_.dite_eq_right (fun e => lt_irrefl _ e.1), if_pos rfl]
  · intro x y hxy
    have hxy' : x < y := hxy
    unfold lowMat
    rw [_root_.dite_eq_right (fun e => lt_asymm hxy' e.1), if_neg hxy'.ne]

theorem analytic_wH {n e : ℕ} (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin e) (τ' : Ψ)
    (r s : Fin N) (S : Set (Fin e → ℂ)) : AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) S := by
  have hl : ∀ x, AnalyticOnNhd ℂ (fun w => lowMat (wL ε w) τ' x s) S := by
    intro x
    unfold lowMat
    by_cases hh : s < x ∧ ((x : ℕ) < N - j ↔ (s : ℕ) < N - j)
    · simp only [dif_pos hh, wL]
      exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin e => ℂ)
        (ε (Sum.inr (Sum.inl ⟨(τ', x, s), hh⟩)))).analyticOnNhd _
    · simp only [_root_.dite_eq_right hh]
      exact analyticOnNhd_const
  have : (fun w => wH h ε τ' w r s) = fun w => ∑ x, h τ' r x * lowMat (wL ε w) τ' x s := by
    funext w
    simp only [wH, Matrix.mul_apply]
  rw [this]
  exact Finset.analyticOnNhd_fun_sum _ fun x _ => analyticOnNhd_const.mul (hl x)

end Low

section Flag

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ}
  {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ} {M : FlagModel y Ψ N j} {F : FrameData ι Ψ N M.Ω M.blk}
  {zb : (Σ k, baseIdx ι M.blk k) → ℂ} {H : Ψ → Matrix (Fin N) (Fin N) ℂ}

theorem flagZ_base (k : NonPluckerBlocks M.blk) (m : ι k.1) : flagZ M F zb H ⟨k.1, m⟩ = zb ⟨k, m⟩ := by
  unfold flagZ
  rw [_root_.dite_eq_right (fun e => by obtain ⟨p, hp⟩ := e; exact k.2 p hp)]

theorem flagZ_step {p : Ψ × Fin N} {k : K} (hp : M.blk p = some k) (m : ι k) :
    flagZ M F zb H ⟨k, m⟩ = ∑ I, valAt M.x (F.u ⟨k, m⟩ I) zb * minorIJ (H p.1) I (stepCols N j p.2) := by
  have e : ∃ p, M.blk p = some k := ⟨p, hp⟩
  have hc : e.choose = p := M.blk_inj _ _ _ e.choose_spec hp
  unfold flagZ
  simp only [dif_pos e, hc]

variable {k₀ : K} {τ : Ψ} {ca cb : Fin N} {t : ℂ}

theorem fst_sqZ (k : K) (m : ι k) :
    fstPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := rfl

theorem snd_sqZ_ne {k : K} (hk : k ≠ k₀) (m : ι k) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k, m⟩ = flagZ M F zb H ⟨k, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k, m⟩) = _
  rw [v₁_ne (p := ⟨k, m⟩) hk]
  rfl

theorem snd_sqZ_self (m : ι k₀) :
    sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k₀, m⟩ =
      flagZ M F zb (Function.update H τ (H τ * (1 + Matrix.single cb ca t))) ⟨k₀, m⟩ := by
  show sqZ M F zb H k₀ τ ca cb t (v₁ k₀ ⟨k₀, m⟩) = _
  rw [v₁_self]
  rfl

theorem basePart_fst : basePart M.blk (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  exact flagZ_base k m

theorem basePart_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) :
    basePart M.blk (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t)) = zb := by
  funext q
  obtain ⟨k, m⟩ := q
  have hne : k.1 ≠ k₀ := fun e => k.2 (τ, a) (by rw [hk₀, e])
  show sndPt k₀ (sqZ M F zb H k₀ τ ca cb t) ⟨k.1, m⟩ = _
  rw [snd_sqZ_ne hne]
  exact flagZ_base k m

theorem exact_fst (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (p : Ψ × Fin N) :
    M.ExactAt F p (fstPt k₀ (sqZ M F zb H k₀ τ ca cb t)) (H p.1) := by
  refine ⟨fun k => by rw [basePart_fst]; exact hn k, fun k hk m => ?_⟩
  rw [fst_sqZ, flagZ_step hk, basePart_fst]

theorem exact_snd {a : Fin N} (hk₀ : M.blk (τ, a) = some k₀) (hlt : ca < cb)
    (hiff : ∀ i, i ≠ a → (ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i))
    (hn : ∀ k, zb ⟨k, F.c k⟩ = 1) (τ' : Ψ) (i : Fin N) :
    M.ExactAt F (τ', i) (sndPt k₀ (sqZ M F zb H k₀ τ ca cb t))
      (if τ' = τ then H τ * (1 + Matrix.single cb ca t) else H τ') := by
  refine ⟨fun k => by rw [basePart_snd hk₀]; exact hn k, fun k hk m => ?_⟩
  rw [basePart_snd hk₀]
  by_cases hkk : k = k₀
  · subst hkk
    have hp : (τ', i) = (τ, a) := M.blk_inj _ _ _ hk hk₀
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hp
    rw [snd_sqZ_self, flagZ_step hk₀, if_pos rfl, Function.update_self]
  · rw [snd_sqZ_ne hkk, flagZ_step hk]
    refine Finset.sum_congr rfl fun I _ => ?_
    by_cases hτ : τ' = τ
    · subst hτ
      have hia : i ≠ a := by
        rintro rfl
        exact hkk (Option.some_injective _ (hk.symm.trans hk₀))
      rw [if_pos rfl, minorIJ_mul_one_add_single _ _ _ hlt (hiff i hia)]
    · rw [if_neg hτ]

end Flag

theorem chart_exact : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (Rb : AnLogRes (mCoordIdeal M.x) ⊤ n) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N) (F : FrameData ι Ψ N M.Ω M.blk) (kb : Fin Rb.A.n) (V : Set (Fin n → ℂ)) (bl : (Fin n → ℂ) → (Σ k, baseIdx ι M.blk k) → ℂ) (r : ((Σ k, baseIdx ι M.blk k) → ℂ) → Rb.X) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (ε : Fin n ⊕ LowIdx Ψ N j ⊕ Unit ≃ Fin (d + 2)), IsWCtx M Rb τ a b k₀ ca cb d F kb V bl r h → (∀ τ' r s, AnalyticOnNhd ℂ (fun w => wH h ε τ' w r s) (wD ε V)) ∧ ∀ w ∈ wD ε V, (∀ τ', IsBlockDiag j (wH h ε τ' w) ∧ (wH h ε τ' w).det ≠ 0) ∧ baseOf M k₀ (wPhi M F bl h ε k₀ τ ca cb w) = bl (wB ε w) ∧ ∀ τ' i, ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (fstPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (wH h ε τ' w) ∧ ((fun {jExact : ℕ} (mExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FlagModel _ _ _ jExact) (fExact : _root_.GlobalTheory.CompanionTheory.Ar.PB.FrameData _ _ _ mExact.Ω mExact.blk) (pExact : _) (zExact : _ → ℂ) (hExact : _root_.Matrix _ _ ℂ) => (∀ kExact, _root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact ⟨kExact, fExact.c kExact⟩ = 1) ∧ ∀ kExact, mExact.blk pExact = some kExact → ∀ iExact, zExact ⟨kExact, iExact⟩ = _root_.Finset.sum _root_.Finset.univ (fun aExact => _root_.GroundTheory.Heights₂.Heights.LowerBoundFree.valAt mExact.x (fExact.u ⟨kExact, iExact⟩ aExact) (_root_.GlobalTheory.CompanionTheory.Ar.PB.basePart mExact.blk zExact) * _root_.GlobalTheory.CompanionTheory.Ar.PB.minorIJ hExact aExact (_root_.GlobalTheory.CompanionTheory.Ar.PB.stepCols _ jExact pExact.2))) M) F (τ', i) (sndPt k₀ (wPhi M F bl h ε k₀ τ ca cb w)) (if τ' = τ then wH h ε τ w * (1 + Matrix.single cb ca (wT ε w)) else wH h ε τ' w) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d Rb τ a b k₀ ca cb F kb V bl r h ε hW
  obtain ⟨hb, h2, hk₀, hca, hcb, -, -, hB, -, -, hh⟩ := hW
  have hlt : ca < cb := by
    rw [Fin.lt_def]
    omega
  refine ⟨fun τ' r s => analytic_wH h ε τ' r s _, fun w hw => ⟨fun τ' => ⟨?_, ?_⟩, ?_, fun τ' i => ⟨?_, ?_⟩⟩⟩
  · exact isBlockDiag_mul (hh τ').1 (lowMat_isBlockDiag _ _)
  · rw [wH, Matrix.det_mul, lowMat_det, mul_one]
    exact (hh τ').2
  · exact basePart_fst
  · exact exact_fst (H := fun τ' => wH h ε τ' w) ((hB.2.2.2.2 _ hw).2.1) (τ', i)
  · exact exact_snd (H := fun τ' => wH h ε τ' w) hk₀ hlt
      (fun i hi => mem_stepCols_iff hb h2 hca hcb hi) ((hB.2.2.2.2 _ hw).2.1) τ' i

end GlobalTheory.CompanionTheory.Ar.PB.WMan.Exact
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentPluckerOrbit
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC

theorem mul_one_add_single_apply {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (ca cb : Fin N) (t : ℂ) (r c : Fin N) :
    (h * (1 + Matrix.single cb ca t)) r c = h r c + if c = ca then t * h r cb else 0 := by
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply, Matrix.mul_apply]
  congr 1
  simp only [Matrix.single_apply]
  split_ifs with hc
  · subst hc
    simp [mul_comm]
  · simp [Ne.symm hc]

theorem minorIJ_mul_transvection {N : ℕ} (h : Matrix (Fin N) (Fin N) ℂ) (I J : Finset (Fin N)) {ca cb : Fin N}
    (hne : ca ≠ cb) (t : ℂ) (hJ : ca ∈ J ↔ cb ∈ J) :
    minorIJ (h * (1 + Matrix.single cb ca t)) I J = minorIJ h I J := by
  unfold minorIJ
  split_ifs with e
  · by_cases hca : ca ∈ J
    · have hcb := hJ.1 hca
      obtain ⟨p, hp⟩ : ca ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hca
      obtain ⟨q, hq⟩ : cb ∈ Set.range (J.orderEmbOfFin (rfl : J.card = J.card)) := by
        rw [Finset.range_orderEmbOfFin]; exact hcb
      have hpq : p ≠ q := fun h' => hne (by rw [← hp, ← hq, h'])
      refine (congrArg Matrix.det ?_).trans
        (Matrix.det_updateCol_add_smul_self (h.submatrix (I.orderEmbOfFin e) (J.orderEmbOfFin rfl)) hpq t)
      ext a b
      rw [Matrix.submatrix_apply, mul_one_add_single_apply]
      by_cases hb : b = p
      · rw [hb, Matrix.updateCol_self]
        simp [hp, hq]
      · have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' =>
          hb ((J.orderEmbOfFin rfl).injective (h'.trans hp.symm))
        rw [Matrix.updateCol_ne hb]
        simp [hbc]
    · congr 1
      ext a b
      have hbc : J.orderEmbOfFin rfl b ≠ ca := fun h' => hca (h' ▸ Finset.orderEmbOfFin_mem J rfl b)
      simp [mul_one_add_single_apply, hbc]
  · rfl

theorem mem_stepCols_iff {N j : ℕ} {a b i ca cb : Fin N} (hb : (b : ℕ) = a + 1) (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ))
    (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) (hi : i ≠ a) :
    ca ∈ stepCols N j i ↔ cb ∈ stepCols N j i := by
  have hi' : (i : ℕ) ≠ a := fun h => hi (Fin.ext h)
  have := a.isLt
  have := b.isLt
  have := i.isLt
  have := ca.isLt
  have := cb.isLt
  simp only [stepCols, Finset.mem_filter, Finset.mem_univ, true_and]
  unfold lastCol at hca
  split_ifs at hca ⊢ <;> omega

theorem fstPt_sndPt_wVec : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ) (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (t : ℂ), fstPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b h ∧ sndPt k₀ (FC.wVec M F b h τ a k₀ ca cb t) = FC.flagPt M F b (Function.update h τ (h τ * (1 + Matrix.single cb ca t))) := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M τ a b k₀ ca cb hb hab hblk hca hcb F bv h t
  have hne : ca ≠ cb := by
    intro e
    have := congrArg Fin.val e
    omega
  refine ⟨?_, ?_⟩
  · funext p
    obtain ⟨k, m⟩ := p
    rfl
  · funext p
    obtain ⟨k, m⟩ := p
    simp only [sndPt, Function.comp_apply]
    by_cases hk : k = k₀
    · subst hk
      rw [v₁_self]
      show (∑ I, valAt M.x (F.u ⟨k, m⟩ I) bv * minorIJ (h τ * (1 + Matrix.single cb ca t)) I (stepCols N j a)) = _
      rw [flagPt_step M F bv _ hblk m]
      simp [Function.update_self]
    · rw [v₁_ne (p := ⟨k, m⟩) hk]
      show FC.flagPt M F bv h ⟨k, m⟩ = _
      by_cases hbase : ∀ p, M.blk p ≠ some k
      · simp [FC.flagPt, hbase]
      · push Not at hbase
        obtain ⟨⟨τ', i⟩, hp⟩ := hbase
        rw [flagPt_step M F bv h hp m, flagPt_step M F bv _ hp m]
        refine Finset.sum_congr rfl fun I _ => ?_
        dsimp only
        congr 1
        by_cases hτ : τ' = τ
        · subst hτ
          have hia : i ≠ a := by
            rintro rfl
            exact hk (Option.some_injective _ (hp.symm.trans hblk))
          rw [Function.update_self, minorIJ_mul_transvection _ _ _ hne t (mem_stepCols_iff hb hab hca hcb hia)]
        · rw [Function.update_of_ne hτ]

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC
end
end

