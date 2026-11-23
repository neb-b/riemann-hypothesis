module

public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0003
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0004
public import Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.Bundle0002

@[expose] public section

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.InitialLevelFormula
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree


open Classical in
def RestOddTops : Prop :=
  ∀ (n' : ℕ) (TT : Finset (Fin n')), 2 ≤ numSeg TT → ∀ f : Fin n' → Fin n' → ℕ → ℝ,
    ∑ j : Fin (numSeg TT), ∑ i : Fin (segS TT j), f (segPos TT j i) (segStart TT j) ((segDists TT j).get i) =
      ∑ y ∈ TT.filter (fun y => ¬ IsTypeV y), f y (yPrev TT y) (dPrev TT y)

theorem tle_abs (Ct C N N1 p k Q L ar a' b' La La' ccl cS n' S S' : ℝ) (hCt : 0 < Ct) (hC : 4 * Ct + 4 ≤ C)
    (hN : 1 ≤ N) (hN1 : 1 ≤ N1) (hp : 0 < p) (hk : 1 ≤ k) (hQ : 1 ≤ Q) (hL : 0 ≤ L) (har : 0 ≤ ar)
    (ha0 : 0 ≤ a') (ha : a' ≤ 2 * ar) (hb : 0 < b') (hLa : 0 ≤ La) (hLa0 : 0 ≤ La') (hLa' : La' ≤ 2 * La)
    (hccl : 0 ≤ ccl) (hcS : 0 ≤ cS) (hn' : 0 ≤ n') (hS : S' ≤ S + N * ccl) :
    (S' + Ct * N * (a' / p ^ 2 + b' / p + La' * a' / (p * k) + La' * b' / k + k * Q +
        Q * (cS + 2 * N * ccl + 2 * n' * ccl))) + N * (La' * b' / k) + 1 + 2 * n' * ccl ≤
      S + C * N * N1 * (ar / p ^ 2 + b' / p + La * ar / (p * k) + La * b' / k) +
        C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl) + k * Q + k * L + ccl) + 2 * n' * ccl := by
  have hN0 : 0 ≤ N := by linarith
  have hk0 : 0 < k := by linarith
  have hQ0 : 0 ≤ Q := by linarith
  have hC0 : 0 ≤ C := by linarith
  have hCN1 : C ≤ C * N1 := by nlinarith
  have hp2 : 0 < p ^ 2 := by positivity
  have hA : a' / p ^ 2 ≤ 2 * (ar / p ^ 2) := by
    rw [← mul_div_assoc]
    exact div_le_div_of_nonneg_right ha hp2.le
  have hA0 : 0 ≤ ar / p ^ 2 := by positivity
  have hB0 : 0 ≤ b' / p := by positivity
  have hE : La' * a' / (p * k) ≤ 4 * (La * ar / (p * k)) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ (by positivity)
    have := mul_le_mul hLa' ha ha0 (by linarith : (0 : ℝ) ≤ 2 * La)
    linarith
  have hE0 : 0 ≤ La * ar / (p * k) := by positivity
  have hF : La' * b' / k ≤ 2 * (La * b' / k) := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right _ hk0.le
    nlinarith
  have hF0 : 0 ≤ La * b' / k := by positivity
  have hF'0 : 0 ≤ La' * b' / k := by positivity
  have t1 : Ct * N * (a' / p ^ 2) ≤ C * N * N1 * (ar / p ^ 2) := by
    have h1 := mul_le_mul_of_nonneg_left hA (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct ≤ C * N1) (mul_nonneg hN0 hA0)
    nlinarith
  have t2 : Ct * N * (b' / p) ≤ C * N * N1 * (b' / p) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : Ct ≤ C * N1) (mul_nonneg hN0 hB0)
    nlinarith
  have t3 : Ct * N * (La' * a' / (p * k)) ≤ C * N * N1 * (La * ar / (p * k)) := by
    have h1 := mul_le_mul_of_nonneg_left hE (mul_nonneg hCt.le hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 4 * Ct ≤ C * N1) (mul_nonneg hN0 hE0)
    nlinarith
  have t4 : Ct * N * (La' * b' / k) + N * (La' * b' / k) ≤ C * N * N1 * (La * b' / k) := by
    have h1 := mul_le_mul_of_nonneg_left hF (mul_nonneg (by linarith : (0 : ℝ) ≤ Ct + 1) hN0)
    have h2 := mul_le_mul_of_nonneg_right (by linarith : 2 * Ct + 2 ≤ C * N1) (mul_nonneg hN0 hF0)
    nlinarith
  have hNkQ : 1 ≤ N * k * Q := by
    have := one_le_mul_of_one_le_of_one_le hN hk
    exact one_le_mul_of_one_le_of_one_le this hQ
  have t5 : Ct * N * (k * Q) + 1 ≤ C * N * (k * Q) := by
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (4 : ℝ) ≤ C - Ct) (by linarith : (0 : ℝ) ≤ N * k * Q)
    nlinarith
  have hX0 : 0 ≤ cS + 2 * N * ccl + 2 * n' * ccl := by positivity
  have hXY : cS + 2 * N * ccl + 2 * n' * ccl ≤ cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl := by
    have : 0 ≤ C * N * k * L := by positivity
    have : 0 ≤ N * ccl := by positivity
    linarith
  have t6 : Ct * N * (Q * (cS + 2 * N * ccl + 2 * n' * ccl)) ≤
      C * N * (Q * (cS + C * N * k * L + 4 * N * ccl + 2 * n' * ccl)) := by
    apply mul_le_mul (mul_le_mul_of_nonneg_right (by linarith) hN0)
      (mul_le_mul_of_nonneg_left hXY hQ0) (mul_nonneg hQ0 hX0) (mul_nonneg hC0 hN0)
  have t7 : N * ccl ≤ C * N * (k * L + ccl) := by
    have : 0 ≤ C * N * (k * L) := by positivity
    have h2 := mul_le_mul_of_nonneg_right (by linarith : (1 : ℝ) ≤ C) (mul_nonneg hN0 hccl)
    linarith
  linarith [t1, t2, t3, t4, t5, t6, t7]

theorem initial_level_formula (K : Cst) (X : Dat) (A B : X.TT → ℕ) :
    X.t0 K A B = (∑ j : Fin (numSeg X.TT), ∑ i : Fin (segS X.TT j),
        min ((ex B (segPos X.TT j i) : ℕ) : ℝ)
          (((ex A (segStart X.TT j) : ℕ) : ℝ) / (X.p : ℝ) ^ ((segDists X.TT j).get i))) +
      K.Ct * X.N * ((X.a : ℝ) / (X.p : ℝ) ^ 2 + X.b' / X.p + LaI K.C₀ X.N₁ X.a * X.a / (X.p * X.k) +
        LaI K.C₀ X.N₁ X.a * X.b' / X.k + X.k * (X.p : ℝ) ^ X.G' +
        (X.p : ℝ) ^ X.G' * ((X.cStar : ℝ) + 2 * X.N * X.ccl + 2 * X.n' * X.ccl)) := by
  unfold Dat.t0 t0I t0G4 Dat.c4 Dat.N Dat.k
  push_cast
  ring

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.RingIndep
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

theorem lpRingIndep_of (h1 : RestRSIso) (h2 : RestHLTransport) : LPRingIndep := by
  unfold LPRingIndep
  intro p n' R₁ R₂ m r lam0 t D κ cStar hLP
  obtain ⟨I⟩ := h1 p n' R₁ R₂
  obtain ⟨Φ, Ψ, hΨ, hLat, hEdge, hHL, hHLe, hdim⟩ := h2 p n' R₁ R₂ I m lam0

  have hwK : ∀ z : ℤ, I.φK (algebraMap R₁.O R₁.Kf R₁.w ^ z) = algebraMap R₂.O R₂.Kf R₂.w ^ z := by
    intro z; rw [map_zpow₀, I.hOK, I.hw]
  have hpK : ∀ z : ℤ, I.φK ((p : R₁.Kf) ^ z) = (p : R₂.Kf) ^ z := by
    intro z; rw [map_zpow₀, map_natCast]

  let back : Edge R₂.W R₂.Qq (m + 1) → Edge R₁.W R₁.Qq (m + 1) := fun e => ⟨Φ.symm e.src, Φ.symm e.tgt⟩
  have hback : ∀ e, (⟨Φ (back e).src, Φ (back e).tgt⟩ : Edge R₂.W R₂.Qq (m + 1)) = e := by
    intro e; cases e; simp [back]
  have hbackEdge : ∀ e, IsEdge p n' r e → IsEdge p n' r (back e) := by
    intro e he; rw [hEdge r (back e), hback]; exact he
  have hHLe' : ∀ e x, x ∈ HLe p R₁.ι R₁.σ R₁.w lam0 (back e) ↔ Ψ x ∈ HLe p R₂.ι R₂.σ R₂.w lam0 e := by
    intro e x; have h := hHLe (back e) x; rwa [hback] at h
  unfold LPprime at hLP ⊢
  obtain ⟨hc, hall⟩ := hLP
  refine ⟨hc, fun L hL => ?_⟩
  have hL1 : IsLattice R₁.W (Φ.symm L) := by rw [hLat, Φ.apply_symm_apply]; exact hL
  have hAt := hall _ hL1
  unfold LPprimeAt at hAt ⊢
  obtain ⟨M, e, F, he, hF, hF', n, hn, hG⟩ := hAt
  refine ⟨M, fun i => ⟨Φ (e i).src, Φ (e i).tgt⟩, fun i => Ψ (F i), ?_, ?_, ?_, n, ?_, ?_⟩
  · intro i
    refine ⟨(hEdge r (e i)).1 (he i).1, ?_⟩
    show Φ (e i).tgt = L
    rw [(he i).2, Φ.apply_symm_apply]
  · intro i
    have hFi := hF i
    simp only [Nsrc, Re, Submodule.mem_inf, Submodule.mem_iInf] at hFi ⊢
    refine ⟨?_, ?_⟩
    · have h := sl_scale I.φK Ψ hΨ _ (hHL (e i).src) hFi.1
      rwa [hwK] at h
    · intro e' he'
      have hb : IsEdge p n' r (back e') ∧ (back e').src = (e i).src := by
        refine ⟨hbackEdge e' he'.1, ?_⟩
        show Φ.symm e'.src = (e i).src
        rw [he'.2]; exact Φ.symm_apply_apply _
      have h := sl_scale I.φK Ψ hΨ _ (hHLe' e') (hFi.2 (back e') hb)
      rwa [hwK] at h
  · intro i e' he' hsrc hne
    have hb : (back e').src = (e i).src := by
      show Φ.symm e'.src = (e i).src
      rw [hsrc]; exact Φ.symm_apply_apply _
    have hne' : back e' ≠ e i := by
      intro h; apply hne; rw [← hback e', h]
    have hx := hF' i (back e') (hbackEdge e' he') hb hne'
    simp only [Re] at hx ⊢
    have h := sl_scale2 I.φK Ψ hΨ _ _ (hHLe' e') hx
    rwa [hwK, hwK] at h
  · rw [← hdim]; exact hn
  ·
    have hN : ∀ G, G ∈ Ntgt p n' R₁.ι R₁.σ R₁.w r lam0 t (Φ.symm L) →
        dT I.φK Ψ hΨ G ∈ Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L := by
      intro G hG
      simp only [Ntgt, Re', Submodule.mem_inf, Submodule.mem_iInf] at hG ⊢
      refine ⟨?_, ?_⟩
      · have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHL (Φ.symm L)) hG.1
        rwa [hwK, Φ.apply_symm_apply] at h
      · intro e' he'
        have hb : IsEdge p n' r (back e') ∧ (back e').tgt = Φ.symm L := by
          refine ⟨hbackEdge e' he'.1, ?_⟩
          show Φ.symm e'.tgt = Φ.symm L
          rw [he'.2]
        have h := sl_scale_dual I.φO I.φK Ψ hΨ I.hOK _ (hHLe' e') (hG.2 (back e') hb)
        rwa [hwK] at h
    unfold GoodRankK at hG ⊢
    obtain ⟨u, Mt, hu⟩ := hG
    have hdTv : ∀ (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) v, dT I.φK Ψ hΨ G v = I.φK (G (Ψ.symm v)) :=
      fun _ _ => rfl
    let u₂ : (Fin n → R₂.O) →ₗ[R₂.O] Ntgt p n' R₂.ι R₂.σ R₂.w r lam0 t L :=
      { toFun := fun x => ⟨dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)), hN _ (u _).2⟩
        map_add' := by
          intro x y
          have hx : (fun j => I.φO.symm ((x + y) j)) =
              (fun j => I.φO.symm (x j)) + (fun j => I.φO.symm (y j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          simp only [hx, map_add (f := _), Submodule.coe_add, LinearMap.add_apply, hdTv]
        map_smul' := by
          intro c x
          have hx : (fun j => I.φO.symm ((c • x) j)) = I.φO.symm c • (fun j => I.φO.symm (x j)) := by
            funext j; simp
          apply Subtype.ext
          apply LinearMap.ext
          intro v
          show I.φK ((u fun j => I.φO.symm ((c • x) j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)) (Ψ.symm v)) =
            (c • (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)) : Module.Dual R₂.Kf (Vsp R₂.Kf lam0))) v
          rw [hx, map_smul, LinearMap.smul_apply, hdTv]
          simp only [SetLike.val_smul, Submodule.coe_smul_of_tower, LinearMap.smul_apply]
          rw [Algebra.smul_def, Algebra.smul_def, map_mul, I.hOK, RingEquiv.apply_symm_apply] }
    refine ⟨u₂, Mt.map I.φO, ?_⟩
    intro x j
    have hbe : ∀ i (G : Module.Dual R₁.Kf (Vsp R₁.Kf lam0)),
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ G) = I.φK (be p r lam0 (F i) G) := by
      intro i G
      simp only [be]
      rw [← hpK, ← hΨ, dT_apply]
    have hx := hu (fun j => I.φO.symm (x j)) j
    show ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
        be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j))) =
      algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j)
    calc ∑ i, algebraMap R₂.O R₂.Kf (I.φO (Mt j i)) *
          be p r lam0 (Ψ (F i)) (dT I.φK Ψ hΨ (u fun j => I.φO.symm (x j)))
        = ∑ i, I.φK (algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [hbe, map_mul, I.hOK]
      _ = I.φK (∑ i, algebraMap R₁.O R₁.Kf (Mt j i) *
            be p r lam0 (F i) (u fun j => I.φO.symm (x j) : Module.Dual R₁.Kf (Vsp R₁.Kf lam0))) :=
          (map_sum _ _ _).symm
      _ = I.φK (algebraMap R₁.O R₁.Kf ((p : R₁.O) ^ D * I.φO.symm (x j))) := by rw [hx]
      _ = algebraMap R₂.O R₂.Kf ((p : R₂.O) ^ D * x j) := by
          rw [I.hOK, map_mul, map_pow, map_natCast, RingEquiv.apply_symm_apply]

end Formalism.MainNotions.flipOneThree.Pf

end
end

-- bundled from Formalism.SharpRestriction.GrowthBounds.ColumnSpanDensity.TwoHundredLeRadius
section
noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree

def Cst.TM (K : Cst) : ℝ := max K.TLP (max (4 * K.CH + 1) (2 * K.Cm + 24))

theorem TM_pos (K : Cst) : 0 < K.TM :=
  lt_of_lt_of_le (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 108) (le_trans (le_max_left _ _) (le_max_left _ _)))
    (le_max_left _ _)

theorem two_hundred_le_radius {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) : (200 : ℝ) ≤ X.ar := by
  have := mul_le_mul B.hp25 B.hb8 (by norm_num) (by linarith [B.hp25])
  linarith [B.hpa]

theorem log_round {K : Cst} {CH : ℝ} {X : Dat} (B : Base K CH X) :
    Real.log X.ar ≤ Real.log X.a ∧ Real.log X.a ≤ Real.log X.ar + 1 / 200 := by
  have h200 := two_hundred_le_radius B
  have har : 0 < X.ar := by linarith
  have ha : (0 : ℝ) < X.a := by linarith [B.haa]
  refine ⟨Real.log_le_log har B.haa, ?_⟩
  have h1 : Real.log ((X.a : ℝ) / X.ar) = Real.log X.a - Real.log X.ar := Real.log_div ha.ne' har.ne'
  have h2 := Real.log_le_sub_one_of_pos (div_pos ha har)
  have h3 : (X.a : ℝ) / X.ar - 1 ≤ 1 / 200 := by
    have : (X.a : ℝ) / X.ar ≤ 1 + 1 / 200 := by
      rw [div_le_iff₀ har]
      linarith [B.haa1]
    linarith
  linarith

theorem La_round {K : Cst} (hK : K.Pos) {CH : ℝ} {X : Dat} (B : Base K CH X) :
    LaI K.C₀ X.N₁ X.ar ≤ LaI K.C₀ X.N₁ X.a ∧ LaI K.C₀ X.N₁ X.a ≤ 2 * LaI K.C₀ X.N₁ X.ar ∧
      LaI K.C₀ X.N₁ X.a * Real.log X.a ≤ 2 * (LaI K.C₀ X.N₁ X.ar * Real.log X.ar) := by
  obtain ⟨h1, h2⟩ := log_round B
  have hl := B.hlog1
  have hC0 : 0 < K.C₀ := hK.1
  have hcn : 0 ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 := by positivity
  unfold LaI
  refine ⟨mul_le_mul_of_nonneg_left h1 hcn, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left (by linarith : Real.log X.a ≤ 2 * Real.log X.ar) hcn
    linarith
  · have hsq : Real.log X.a * Real.log X.a ≤ 2 * (Real.log X.ar * Real.log X.ar) := by
      have a1 : Real.log X.a ≤ (1 + 1 / 200) * Real.log X.ar := by linarith
      have a0 : 0 ≤ Real.log X.a := by linarith
      have a2 := mul_le_mul a1 a1 a0 (by linarith)
      have a3 : 0 ≤ Real.log X.ar * Real.log X.ar := by positivity
      nlinarith
    have := mul_le_mul_of_nonneg_left hsq hcn
    calc K.C₀ * (X.N₁ : ℝ) ^ 2 * Real.log X.a * Real.log X.a
        = K.C₀ * (X.N₁ : ℝ) ^ 2 * (Real.log X.a * Real.log X.a) := by ring
      _ ≤ K.C₀ * (X.N₁ : ℝ) ^ 2 * (2 * (Real.log X.ar * Real.log X.ar)) := this
      _ = _ := by ring

theorem r12 (Yb N La La' b' k w : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 ≤ b') (hk : 0 < k) (h2 : La' ≤ 2 * La)
    (h : Yb * N * La * b' / k ≤ w) : Yb / 2 * N * La' * b' / k ≤ w := by
  have hc : 0 ≤ Yb * N * b' / k := by positivity
  have := mul_le_mul_of_nonneg_left (by linarith : La' / 2 ≤ La) hc
  calc Yb / 2 * N * La' * b' / k = Yb * N * b' / k * (La' / 2) := by ring
    _ ≤ Yb * N * b' / k * La := this
    _ = Yb * N * La * b' / k := by ring
    _ ≤ w := h

theorem r15 (Yb N La La' k : ℝ) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (h2 : La' ≤ 2 * La) (h : 2 * Yb * N * La < k) :
    2 * (Yb / 2) * N * La' < k := by
  have hc : 0 ≤ Yb * N := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc 2 * (Yb / 2) * N * La' = Yb * N * La' := by ring
    _ ≤ Yb * N * (2 * La) := this
    _ = 2 * Yb * N * La := by ring
    _ < k := h

theorem r16 (k Y Yb N La La' l l' ar a' b' : ℝ) (hk : 0 ≤ k) (hY : 0 ≤ Y) (hYb : 0 ≤ Yb) (hN : 0 ≤ N) (hb : 0 < b')
    (ha : ar ≤ a') (h2 : La' * l' ≤ 2 * (La * l)) (h : k * Y ^ 2 * Yb * N * La * l ≤ ar / b') :
    k * Y ^ 2 * (Yb / 2) * N * La' * l' ≤ a' / b' := by
  have hc : 0 ≤ k * Y ^ 2 * Yb * N / 2 := by positivity
  have := mul_le_mul_of_nonneg_left h2 hc
  calc k * Y ^ 2 * (Yb / 2) * N * La' * l' = k * Y ^ 2 * Yb * N / 2 * (La' * l') := by ring
    _ ≤ k * Y ^ 2 * Yb * N / 2 * (2 * (La * l)) := this
    _ = k * Y ^ 2 * Yb * N * La * l := by ring
    _ ≤ ar / b' := h
    _ ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le

theorem rde (CH CH1 N1 La La' k r : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 + 1 ≤ CH) (hN1 : 1 ≤ N1) (hLa : 1 ≤ La)
    (h2 : La' ≤ 2 * La) (hk : 0 < k) : CH1 * N1 * La' / k + r + 1 / k ≤ CH * N1 * La / k + r := by
  have h1 : CH1 * N1 * La' + 1 ≤ CH * N1 * La := by
    have a1 : CH1 * N1 * La' ≤ CH1 * N1 * (2 * La) := mul_le_mul_of_nonneg_left h2 (by positivity)
    have a2 : 1 ≤ N1 * La := one_le_mul_of_one_le_of_one_le hN1 hLa
    have a3 : (2 * CH1 + 1) * (N1 * La) ≤ CH * (N1 * La) := mul_le_mul_of_nonneg_right hCH (by linarith)
    nlinarith
  have := div_le_div_of_nonneg_right h1 hk.le
  have e : (CH1 * N1 * La' + 1) / k = CH1 * N1 * La' / k + 1 / k := add_div _ _ _
  linarith

theorem rband (ar a' b' de de' k x : ℝ) (hb : 0 < b') (hk : 0 < k) (hka : k ≤ ar) (ha : ar ≤ a') (ha1 : a' ≤ ar + 1)
    (hde0 : 0 ≤ de') (hde6 : de' < 1 / 6) (hde : de' + 1 / k ≤ de)
    (h : a' / b' * (1 - 2 * de') ≤ x ∧ x ≤ a' / b' * (1 + 2 * de')) :
    ar / b' * (1 - 2 * de) ≤ x ∧ x ≤ ar / b' * (1 + 2 * de) := by
  have har : 0 < ar := lt_of_lt_of_le hk hka
  have hk1 : 0 < 1 / k := by positivity
  have hab : ar / b' ≤ a' / b' := div_le_div_of_nonneg_right ha hb.le
  have hab0 : 0 ≤ ar / b' := by positivity
  constructor
  · refine le_trans ?_ h.1
    calc ar / b' * (1 - 2 * de) ≤ ar / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_left (by linarith) hab0
      _ ≤ a' / b' * (1 - 2 * de') := mul_le_mul_of_nonneg_right hab (by linarith)
  · refine le_trans h.2 ?_
    have h1 : a' * (1 + 2 * de') ≤ ar * (1 + 2 * de) := by
      have a1 : a' * (1 + 2 * de') ≤ (ar + 1) * (1 + 2 * de') := mul_le_mul_of_nonneg_right ha1 (by linarith)
      have a2 : ar * (1 + 2 * de' + 2 * (1 / k)) ≤ ar * (1 + 2 * de) := mul_le_mul_of_nonneg_left (by linarith) har.le
      have a3 : 1 ≤ ar * (1 / k) := by
        rw [mul_one_div, le_div_iff₀ hk]
        linarith
      nlinarith
    calc a' / b' * (1 + 2 * de') = a' * (1 + 2 * de') / b' := by ring
      _ ≤ ar * (1 + 2 * de) / b' := div_le_div_of_nonneg_right h1 hb.le
      _ = _ := by ring

theorem r19 (CH CH1 N La La' k : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 4 * CH1 ≤ CH) (hN : 0 ≤ N) (hLa0 : 0 ≤ La')
    (h2 : La' ≤ 2 * La) (h : CH * N * La ^ 2 ≤ k) : CH1 * N * La' ^ 2 ≤ k := by
  have a1 : La' ^ 2 ≤ (2 * La) ^ 2 := pow_le_pow_left₀ hLa0 h2 2
  have a2 : CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := mul_le_mul_of_nonneg_left a1 (by positivity)
  have a3 : 4 * CH1 * (N * La ^ 2) ≤ CH * (N * La ^ 2) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * N * La' ^ 2 ≤ CH1 * N * (2 * La) ^ 2 := a2
    _ = 4 * CH1 * (N * La ^ 2) := by ring
    _ ≤ CH * (N * La ^ 2) := a3
    _ = CH * N * La ^ 2 := by ring
    _ ≤ k := h

theorem r22 (CH CH1 G L L' Dp : ℝ) (hCH1 : 0 ≤ CH1) (hCH : 2 * CH1 ≤ CH) (hG : 0 ≤ G) (hL : 0 ≤ L) (h2 : L' ≤ 2 * L)
    (h : CH * G * L ≤ Dp) : CH1 * G * L' ≤ Dp := by
  have a1 : CH1 * G * L' ≤ CH1 * G * (2 * L) := mul_le_mul_of_nonneg_left h2 (by positivity)
  have a2 : 2 * CH1 * (G * L) ≤ CH * (G * L) := mul_le_mul_of_nonneg_right hCH (by positivity)
  calc CH1 * G * L' ≤ CH1 * G * (2 * L) := a1
    _ = 2 * CH1 * (G * L) := by ring
    _ ≤ CH * (G * L) := a2
    _ = CH * G * L := by ring
    _ ≤ Dp := h

theorem hyp_round {K : Cst} (hK : K.Pos) {CH : ℝ} (hCH : K.TM ≤ CH) {X : Dat} (h : X.Hyp K.C₀ CH) (B : Base K CH X) :
    HypI K.C₀ K.CH X.p X.n' X.m X.TT X.G' X.N₁ X.Y (X.Yb / 2) (X.a : ℝ) X.b' X.bl X.bu X.ccl X.Dp X.cStar := by
  obtain ⟨hY, hp, hev, hseg2, hgap, hN1, hm, hLa8, hb, hbl, hbu, hIb1, hIb2, hYb, hk2, hab, hde, hpab, hkLa, hband,
    hccl, hD, hcs, hsize⟩ := h
  obtain ⟨l1, l2, l3⟩ := La_round hK B
  obtain ⟨-, -, g3, g4⟩ := logs_of B
  have hCH1 : 0 < K.CH := hK.2.1
  have hCH4 : 4 * K.CH + 1 ≤ CH := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hCH
  have h108 : (108 : ℝ) ≤ CH :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)) hCH
  have hYb0 : 0 ≤ X.Yb := by linarith
  have hN0 : (0 : ℝ) ≤ (X.TT.card : ℝ) := by positivity
  have hk5 : (5 : ℝ) ≤ (X.m : ℝ) + 1 := B.hk5
  have hk0 : (0 : ℝ) < (X.m : ℝ) + 1 := by linarith
  have hLa1 : 1 ≤ LaI K.C₀ X.N₁ X.ar := B.hLa1
  have hLa'0 : 0 ≤ LaI K.C₀ X.N₁ X.a := by linarith
  have hN1r : (1 : ℝ) ≤ (X.N₁ : ℝ) := B.hN1
  have hY0 : 0 ≤ X.Y := by linarith
  have hdd : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu + 1 / ((X.m : ℝ) + 1) ≤
      deI CH K.C₀ X.m X.N₁ X.ar X.b' X.bl X.bu := by
    unfold deI
    exact rde CH K.CH X.N₁ _ _ _ _ hCH1.le (by linarith) hN1r hLa1 l2 hk0
  have hk1 : 0 < 1 / ((X.m : ℝ) + 1) := by positivity
  have hde0 : 0 ≤ deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu := by
    unfold deI
    have : 0 ≤ X.bu - X.bl := by linarith
    positivity
  have hde6 : deI K.CH K.C₀ X.m X.N₁ X.a X.b' X.bl X.bu < 1 / 6 := by linarith
  have hka : (X.m : ℝ) + 1 ≤ X.ar := by
    have h1 : (X.m : ℝ) + 1 ≤ X.p := B.hkp
    have h2 := le_mul_of_one_le_right (by linarith [B.hp25] : (0 : ℝ) ≤ X.p) (by linarith [B.hb8] : (1 : ℝ) ≤ X.b')
    linarith [B.hpa]
  refine ⟨hY, hp, hev, hseg2, hgap, hN1, hm, by linarith, hb, hbl, hbu, ?_, hIb2, by linarith, ?_, ?_, hde6, ?_, ?_,
    ?_, ?_, ?_, hcs, ?_⟩
  · exact r12 _ _ _ _ _ _ _ hYb0 hN0 hb.le hk0 l2 hIb1
  · exact r15 _ _ _ _ _ hYb0 hN0 l2 hk2
  · exact r16 _ _ _ _ _ _ _ _ _ _ _ hk0.le hY0 hYb0 hN0 hb B.haa l3 hab
  · exact lt_of_lt_of_le hpab (div_le_div_of_nonneg_right B.haa hb.le)
  · exact r19 CH _ _ _ _ _ hCH1.le (by linarith) hN0 hLa'0 l2 hkLa
  · intro d hd hc
    exact hband d hd (rband _ _ _ _ _ _ _ hb hk0 hka B.haa B.haa1.le hde0 hde6 hdd hc)
  · have : LaI K.C₀ X.N₁ X.ar * X.b' / ((X.m : ℝ) + 1) ≤ LaI K.C₀ X.N₁ X.a * X.b' / ((X.m : ℝ) + 1) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right l1 hb.le) hk0.le
    linarith
  · have hG : (0 : ℝ) ≤ (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) := by positivity
    have := r22 CH K.CH _ _ _ _ hCH1.le (by linarith) hG (by linarith [B.hL1]) g4
      (by calc CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.ar
            = CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.ar := by ring
          _ ≤ (X.Dp : ℝ) := hD)
    calc K.CH * (X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3) * Real.logb X.p X.a
        = K.CH * ((X.TT.card : ℝ) * X.Y ^ 2 * ((X.N₁ : ℝ) ^ 5 + ((X.m : ℝ) + 1) ^ 3)) * Real.logb X.p X.a := by ring
      _ ≤ (X.Dp : ℝ) := this
  · have hG : (0 : ℝ) ≤ ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
        ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by positivity
    have := mul_le_mul_of_nonneg_right (by linarith : K.CH ≤ CH) hG
    calc K.CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y
        = K.CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := by ring
      _ ≤ CH * (((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y) := this
      _ = CH * ((X.m : ℝ) + 1) ^ 3 * X.TT.card * ((X.p : ℝ) ^ X.G') ^ 4 *
          ((X.cStar : ℝ) + X.TT.card * X.ccl + X.n' * X.ccl) * X.Y := by ring
      _ ≤ X.b' := hsize

end Formalism.MainNotions.flipOneThree.Pf

end
end

