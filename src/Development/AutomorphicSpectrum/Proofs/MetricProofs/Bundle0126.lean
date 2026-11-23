module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0037
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagCoverArithmeticFifth
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0049
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0116
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0098
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0048
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0120
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0077
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0047
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.PotentialsBoundedRegSettingEqReference
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0006
public import Development.WeilBound.CoreStatements.PlurisubharmonicCones.ContDiffAtSmoothOnProj

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAdjacentTwistedResolutionSixth
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

theorem fst_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (fstPt k₀ z) (fstPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (some k), fun k => hc _, rfl⟩

theorem snd_orbit {k₀ : K} {z z' : (Σ o : Option K, ι (o.getD k₀)) → ℂ} (h : SameOrbit z z') :
    SameOrbit (sndPt k₀ z) (sndPt k₀ z') := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => if k = k₀ then c none else c (some k), fun k => by dsimp only; split_ifs <;> exact hc _, ?_⟩
  funext ⟨k, m⟩
  by_cases e : k = k₀
  · subst e
    simp [sndPt, v₁_self]
  · simp [sndPt, v₁_ne (p := ⟨k, m⟩) e, e]

theorem same_block {N j : ℕ} {a b ca cb : Fin N} (hj : j ≤ N) (hb : (b : ℕ) = a + 1)
    (hab : (b : ℕ) < j ∨ j ≤ (a : ℕ)) (hca : (ca : ℕ) = lastCol N j a) (hcb : (cb : ℕ) = ca + 1) :
    ((cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) := by
  have := b.2
  have := cb.2
  unfold lastCol at hca
  split_ifs at hca <;> omega

theorem blockDiag_transv {N j : ℕ} {ca cb : Fin N} (h : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (t : ℂ) :
    IsBlockDiag j (1 + Matrix.single cb ca t) := by
  intro r s hrs
  have hne : r ≠ s := fun e => hrs (by rw [e])
  rw [Matrix.add_apply, Matrix.one_apply_ne hne, zero_add, Matrix.single_apply]
  split_ifs with e
  · obtain ⟨rfl, rfl⟩ := e
    exact absurd h hrs
  · rfl

theorem lowerUni_transv {N : ℕ} {ca cb : Fin N} (h : ca < cb) (t : ℂ) :
    IsLowerUni (1 + Matrix.single cb ca t) := by
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · rw [Matrix.add_apply, Matrix.one_apply_eq, Matrix.single_apply, if_neg, add_zero]
    rintro ⟨rfl, e⟩
    exact h.ne e
  · rw [Matrix.add_apply, Matrix.one_apply_ne hrs.ne, zero_add, Matrix.single_apply, if_neg]
    rintro ⟨rfl, rfl⟩
    exact absurd h (not_lt.2 hrs.le)

theorem minor_analytic {m N : ℕ} {V : Set (Fin m → ℂ)} {A : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun u => A u r s) V) (I J : Finset (Fin N)) :
    AnalyticOnNhd ℂ (fun u => minorIJ (A u) I J) V := by
  unfold minorIJ
  by_cases e : I.card = J.card
  · simp only [dif_pos e, Matrix.det_apply]
    refine Finset.analyticOnNhd_fun_sum _ fun σ _ => ?_
    simp only [Units.smul_def, zsmul_eq_mul]
    exact analyticOnNhd_const.mul (Finset.analyticOnNhd_fun_prod _ fun i _ => hA _ _)
  · simp only [dif_neg e]
    exact analyticOnNhd_const

theorem mul_analytic {m N : ℕ} {V : Set (Fin m → ℂ)} {A : (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ}
    (hA : ∀ r s, AnalyticOnNhd ℂ (fun u => A u r s) V) (C : Matrix (Fin N) (Fin N) ℂ) (r s : Fin N) :
    AnalyticOnNhd ℂ (fun u => (A u * C) r s) V := by
  simp only [Matrix.mul_apply]
  exact Finset.analyticOnNhd_fun_sum _ fun i _ => (hA r i).mul analyticOnNhd_const

variable {Φ : Type} [Field Φ] {y : (Σ k, ι k) → Φ} {Ψ : Type} [Fintype Ψ] [DecidableEq Ψ] {N j : ℕ}

theorem wVec_some (M : FlagModel y Ψ N j) (F : FrameData ι Ψ N M.Ω M.blk) (b : (Σ k, baseIdx ι M.blk k) → ℂ)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (τ : Ψ) (a : Fin N) (k₀ : K) (ca cb : Fin N) (t : ℂ) (k : K) (m : ι k) :
    wVec M F b h τ a k₀ ca cb t ⟨some k, m⟩ = flagPt M F b h ⟨k, m⟩ := rfl

theorem plk_ne_zero (M : FlagModel y Ψ N j) {n : ℕ} (BM : BaseMetric M n) (l : Fin BM.q) {b : BM.Rb.X} (hb : b ∈ BM.O l)
    (h : Ψ → Matrix (Fin N) (Fin N) ℂ) (hh : ∀ τ', IsBlockDiag j (h τ'))
    (hm : ∀ (τ' : Ψ) (i : Fin N), IsProperStep N j i → minorIJ (h τ') (stepCols N j i) (stepCols N j i) ≠ 0)
    (p : Ψ × Fin N) : plk M (BM.F l) (bvec BM l b) (flagPt M (BM.F l) (bvec BM l b) h) p ≠ 0 := by
  have hg := bvec_good K ι Φ y Ψ N j M n BM l b hb
  cases hp : M.blk p with
  | none => simp [plk, hp]
  | some k =>
    rw [plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h p k (BM.isFrame l) hg.1 hg.2.1 hh hp]
    refine hm _ _ ?_
    by_contra hn
    rw [(M.blk_none p).2 hn] at hp
    cases hp

theorem not_mem_top (z : (Σ k, ι k) → ℂ) : z ∉ mcPts (⊤ : Ideal (MRing ι)) := fun h => by
  have := h.2 1 trivial
  simp at this

end GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW


set_option maxHeartbeats 1000000 in
theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.dens_w : ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d) (τ : Ψ) (a b : Fin N) (k₀ : K) (ca cb : Fin N), (b : ℕ) = a + 1 → ((b : ℕ) < j ∨ j ≤ (a : ℕ)) → M.blk (τ, a) = some k₀ → (ca : ℕ) = lastCol N j a → (cb : ℕ) = ca + 1 → ∀ (RW : AnLogRes (mCoordIdeal (M.wCo (τ, a) k₀ ca cb RatFunc.X)) ⊤ (d + 2)) (q : Fin 2 → RW.X → FA.S.X), (∀ i, HoloMap RW.A FA.S.A (q i)) → (∀ x x₀, FA.Re.π x₀ = q 0 x → SameOrbit (FA.Re.R.lift x₀ x₀) (fstPt k₀ (RW.lift x x))) → (∀ x x₀, FA.Re.π x₀ = q 1 x → SameOrbit (FA.Re.R.lift x₀ x₀) (sndPt k₀ (RW.lift x x))) → (Function.Injective fun w => (q 0 w, q 1 w)) → ∀ (l : Fin BM.q) (x : RW.X), FA.pr (q 0 x) ∈ BM.O l → ∀ V, IsOpen V → x ∈ V → ∃ x' ∈ V, FA.pr (q 0 x') ∈ BM.O l \ bdry BM.s ∧ ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (fstPt k₀ (RW.lift x' x')) p ≠ 0 ∧ FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (q 0 x'))) (sndPt k₀ (RW.lift x' x')) p ≠ 0 := by
  intro K _ ι _ Φ _ y Ψ _ _ N j M n d BM FA τ a b k₀ ca cb hb hab hblk hca hcb RW q _ h0 _ _ l x hx V hV hxV
  have harith : IsArithVar (mCoordIdeal y) (d + 2) := FA.Re.arith
  have hsb := FC.DensW.same_block M.j_le hb hab hca hcb
  have hlt : ca < cb := Fin.lt_def.2 (by omega)
  have hbase : ∀ w : RW.X, SameOrbit (basePart M.blk (fstPt k₀ (RW.lift w w)))
      (BM.Rb.lift (FA.pr (q 0 w)) (FA.pr (q 0 w))) := by
    intro w
    obtain ⟨x₀, hx₀⟩ := (FC.re_pi_bijective K ι Φ y Ψ N j M n d BM FA).2 (q 0 w)
    have e1 := h0 w x₀ hx₀
    have e2 := FA.pr_eq x₀
    rw [hx₀] at e2
    exact orbit_trans (orbit_symm (FibreCount.basePart_orbit M.blk e1)) e2
  obtain ⟨h₀, t, hh₀, ho⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flags_of_point K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hblk hca hcb harith l _ hx _
    (RW.mem x x (RW.mem_U x)) (hbase x)
  have hT : ∀ τ', IsLowerUni ((Function.update (fun _ => (1 : Matrix (Fin N) (Fin N) ℂ)) τ
      (1 + Matrix.single cb ca t)) τ') := by
    intro τ'
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact FC.DensW.lowerUni_transv hlt t
    · rw [Function.update_of_ne e]
      exact ⟨fun r => Matrix.one_apply_eq r, fun r s h => Matrix.one_apply_ne h.ne⟩
  have han : ∀ (m : ℕ) (V : Set (Fin m → ℂ)) (bp : (Fin m → ℂ) → BM.Rb.X) (hh : Ψ → (Fin m → ℂ) → Matrix (Fin N) (Fin N) ℂ),
      IsOpen V → ContinuousOn bp V → (∀ k, AnalyticOnNhd ℂ (BM.Rb.A.chart k ∘ bp) (V ∩ bp ⁻¹' (BM.Rb.A.chart k).source)) →
      (∀ u ∈ V, bp u ∈ BM.O l) → (∀ τ' r s, AnalyticOnNhd ℂ (fun u => hh τ' u r s) V) →
      (∀ u ∈ V, ∀ τ', IsBlockDiag j (hh τ' u) ∧ (hh τ' u).det ≠ 0) →
      ∀ q, AnalyticOnNhd ℂ (fun u => FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t q) V := by
    intro m V bp hh hV hc hch hO hhan _ qq
    obtain ⟨hbv, hval⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_val_analytic K ι Φ y Ψ N j M n BM l m V bp hV hc hch hO
    have hreg : ∀ qq I, AnalyticOnNhd ℂ (fun u => valAt M.x ((BM.F l).u qq I) (FC.bvec BM l (bp u))) V := fun qq I =>
      hval _ fun c hcO => ((FC.bvec_good K ι Φ y Ψ N j M n BM l c hcO).2.1.2.1 qq I).1
    obtain ⟨o, mm⟩ := qq
    cases o with
    | none =>
      exact Finset.analyticOnNhd_fun_sum _ fun I _ => (hreg _ I).mul
        (FC.DensW.minor_analytic (FC.DensW.mul_analytic (hhan τ) _) _ _)
    | some k =>
      by_cases hk : ∀ p, M.blk p ≠ some k
      · have e : ∀ u, FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t ⟨some k, mm⟩ =
            FC.bvec BM l (bp u) ⟨⟨k, hk⟩, mm⟩ := fun u => (FC.DensW.wVec_some M (BM.F l) _ _ τ a k₀ ca cb t k mm).trans (dif_pos hk)
        simp only [e]
        exact hbv _
      · obtain ⟨p, hp⟩ := not_forall.1 hk
        have hp' : M.blk p = some k := not_not.1 hp
        have e : ∀ u, FC.wVec M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) τ a k₀ ca cb t ⟨some k, mm⟩ =
            ∑ I, valAt M.x ((BM.F l).u ⟨k, mm⟩ I) (FC.bvec BM l (bp u)) * minorIJ (hh p.1 u) I (stepCols N j p.2) :=
          fun u => (FC.DensW.wVec_some M (BM.F l) _ _ τ a k₀ ca cb t k mm).trans (FC.flagPt_step M (BM.F l) (FC.bvec BM l (bp u)) (fun τ' => hh τ' u) hp' mm)
        simp only [e]
        exact Finset.analyticOnNhd_fun_sum _ fun I _ => (hreg _ I).mul (FC.DensW.minor_analytic (hhan p.1) _ _)
  obtain ⟨x', hx'V, b', hb', h', hh', ho', hmin⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.Dens.dens_core K ι Φ y Ψ N j M n BM (Option K)
    (fun o => ι (o.getD k₀)) _ ⊤ (d + 2) RW rfl l
    (fun c h => FC.wVec M (BM.F l) (FC.bvec BM l c) h τ a k₀ ca cb t) _ hT han
    (fun c hc h hh => _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.WMem.main K ι Φ y Ψ N j M n BM d τ a b k₀ ca cb hb hab hblk hca hcb harith l c hc h t hh)
    x _ hx h₀ hh₀ ho V hV hxV
  have hw := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.fstPt_sndPt_wVec K ι Φ y Ψ N j M τ a b k₀ ca cb hb hab hblk hca hcb (BM.F l) (FC.bvec BM l b') h' t
  have hb'O : b' ∈ BM.O l := hb'.1
  have hg := FC.bvec_good K ι Φ y Ψ N j M n BM l b' hb'O
  have o₀ := FC.DensW.fst_orbit ho'
  have o₁ := FC.DensW.snd_orbit ho'
  rw [hw.1] at o₀
  rw [hw.2] at o₁
  have hpr : FA.pr (q 0 x') = b' := by
    refine BM.Rb.inj _ _ (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.DensW.not_mem_top _) (orbit_trans (orbit_symm (hbase x')) ?_)
    have o₂ := FibreCount.basePart_orbit M.blk o₀
    rw [FC.basePart_flagPt] at o₂
    exact orbit_trans o₂ hg.2.2.2
  refine ⟨x', hx'V, by rw [hpr]; exact hb', fun p => ?_⟩
  rw [hpr]
  refine ⟨(FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p o₀).2
    (FC.DensW.plk_ne_zero M BM l hb'O h' (fun τ' => (hh' τ').1) (fun τ' i hi => (hmin τ' i hi).1) p),
    (FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ p o₁).2
    (FC.DensW.plk_ne_zero M BM l hb'O _ (fun τ' => ?_) (fun τ' i hi => ?_) p)⟩
  · by_cases e : τ' = τ
    · subst e
      rw [Function.update_self]
      exact (hh' τ').1.mul (FC.DensW.blockDiag_transv hsb t)
    · rw [Function.update_of_ne e]
      exact (hh' τ').1
  · have hm := (hmin τ' i hi).2
    by_cases e : τ' = τ
    · subst e
      rw [Function.update_self] at hm ⊢
      exact hm
    · rw [Function.update_of_ne e] at hm ⊢
      rwa [Matrix.mul_one] at hm
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.FlagAnalyticPluckerColumnSwap
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical
open GlobalTheory.CompanionTheory.Ar.PB.WSq

theorem GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_Lca_of_plk_ne
    (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (Φ : Type) [Field Φ] (y : (Σ k, ι k) → Φ) (Ψ : Type)
    [Fintype Ψ] [DecidableEq Ψ] (N j : ℕ) (M : FlagModel y Ψ N j) (n d : ℕ) (BM : BaseMetric M n) (FA : FlagAn BM d)
    (τ : Ψ) (ca cb : Fin N) (hab : ca < cb) (hblk : (cb : ℕ) < N - j ↔ (ca : ℕ) < N - j) (l : Fin BM.q)
    (x₀ : FA.Re.R.X) (hO : FA.pr (FA.Re.π x₀) ∈ BM.O l)
    (hplk : ∀ p, FC.plk M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FA.Re.R.lift x₀ x₀) p ≠ 0) :
    ∃ (c : FC.CIdx Ψ N j τ ca cb → ℂ) (a : ℂ), SameOrbit (FA.Re.R.lift x₀ x₀)
      (FC.flagPt M (BM.F l) (FC.bvec BM l (FA.pr (FA.Re.π x₀))) (FC.Lca τ ca cb c a)) := by
  have hz : FA.Re.R.lift x₀ x₀ ∈ mcPts (mCoordIdeal y) := FA.Re.R.mem x₀ x₀ (FA.Re.R.mem_U x₀)
  obtain ⟨h, hh, horb⟩ := _root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.exists_flagPt_of_orbit K ι Φ y Ψ N j M n BM l _ hO _ hz (FA.pr_eq x₀)
  obtain ⟨hbm, hbg, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.bvec_good K ι Φ y Ψ N j M n BM l _ hO
  have hmin : ∀ τ' (i : Fin N), IsProperStep N j i →
      minorIJ (h τ') (stepCols N j i) (stepCols N j i) ≠ 0 := by
    intro τ' i hi
    obtain ⟨k, hk⟩ : ∃ k, M.blk (τ', i) = some k :=
      Option.ne_none_iff_exists'.1 fun e => (M.blk_none _).1 e hi
    have h1 := (_root_.GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_ne_zero_iff_of_sameOrbit K ι Φ y Ψ N j M (BM.F l) _ _ _ (τ', i) horb).1 (hplk (τ', i))
    rwa [GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.plk_flagPt K ι Φ y Ψ N j M (BM.F l) _ h (τ', i) k (BM.isFrame l) hbm hbg
      (fun τ'' => (hh τ'').1) hk] at h1
  choose B hBd hBt hBdet hBL using fun τ' =>
    GlobalTheory.CompanionTheory.Ar.PB.WSq.BigCell.exists_upper_of_minors N j (h τ') M.j_le (hh τ').1 (hh τ').2 (hmin τ')
  obtain ⟨-, -, hlc, -, -⟩ := GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.LcFam.lc_main Ψ N j τ ca cb hab hblk
  have hL : ∀ τ', IsBlockDiag j (h τ' * B τ') ∧ IsLowerUni (h τ' * B τ') := by
    intro τ'
    refine ⟨fun r s hrs => ?_, hBL τ'⟩
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases ht : ((r : ℕ) < N - j ↔ (t : ℕ) < N - j)
    · rw [hBd τ' t s (fun e => hrs (ht.trans e)), mul_zero]
    · rw [(hh τ').1 r t ht, zero_mul]
  obtain ⟨c, a, e⟩ := hlc _ hL
  refine ⟨c, a, ?_⟩
  rw [e]
  exact orbit_trans horb (orbit_symm
    (GlobalTheory.CompanionTheory.Ar.PB.WSq.FC.sameOrbit_flagPt_mul K ι Φ y Ψ N j M (BM.F l) _ h B fun τ' => ⟨hBd τ', hBt τ', hBdet τ'⟩))
end

-- bundled from Development.AutomorphicSpectrum.Proofs.MetricProofs.ProjectionOfChartAnalytic
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi
open GroundTheory.Heights₂.Heights.LowerBoundFree GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp
open ReciprocityTheory.AnForm (levi)
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.CompanionTheory.Relay.projection_of_chart_analytic : ∀ (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (II : IntersectionSystem) (Ψ : Type) [Fintype Ψ] (Ω : Type) [Field Ω] [Algebra ℚ Ω] (W : Ψ → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module Ω (W τ)] (D : ComponentData II Ψ K J Ω W) (M : XModel D) (a : Fin D.nCharts) (k : Fin M.atlas.n), ∀ t ∈ Metric.ball (0 : Fin D.n → ℂ) 1, M.proj ((D.chart a).γ t) ∈ (M.atlas.chart k).source → AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t ∧ Function.Bijective (fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t) := by
  intro K _ J _ II Ψ _ Ω _ _ W _ _ D M a k t ht hsrc
  have hγ : AnalyticAt ℂ (D.chart a).γ t := (D.chart a).analytic t ht
  have hev : ∀ᶠ t' in 𝓝 t, (D.chart a).γ t' ∈ mcPts (mCoordIdeal D.y) :=
    Filter.eventually_of_mem (Metric.isOpen_ball.mem_nhds ht) fun t' h => (D.chart a).mem t' h
  have hFan : AnalyticAt ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t :=
    LevelTowerAlt.analyticAt_proj D M (LevelTowerAlt.compat_atlas M.atlas k) hγ hev hsrc
  refine ⟨hFan, ?_⟩
  have htend : Tendsto (fun t' => M.proj ((D.chart a).γ t')) (𝓝 t) (𝓝 (M.proj ((D.chart a).γ t))) := by
    have h1 : Tendsto (D.chart a).γ (𝓝 t) (𝓝[mcPts (mCoordIdeal D.y)] ((D.chart a).γ t)) :=
      tendsto_nhdsWithin_iff.mpr ⟨hγ.continuousAt.tendsto, hev⟩
    exact ((M.cont _ ((D.chart a).mem t ht)).tendsto).comp h1
  obtain ⟨U, hUo, hxU, s, hs, hsh⟩ := M.sections (M.proj ((D.chart a).γ t))
  have hHan : ∀ p, AnalyticAt ℂ (fun t' => s (M.proj ((D.chart a).γ t')) p) t :=
    fun p => LevelTowerAlt.analyticAt_holoOn_proj D M (hsh p) hγ hev hxU
  let P : (Σ kk, J kk) → ((Σ kk, J kk) → ℂ) →L[ℂ] ℂ := fun p =>
    ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : (Σ kk, J kk) => ℂ) p
  have hγp : ∀ p, AnalyticAt ℂ (fun t' => (D.chart a).γ t' p) t :=
    fun p => ((P p).analyticAt _).comp hγ
  choose m hm using ((D.chart a).mem t ht).1
  have hrel : ∀ᶠ t' in 𝓝 t, (∃ c : K → ℂ, (∀ kk, c kk ≠ 0) ∧
      s (M.proj ((D.chart a).γ t')) = torusSmul c ((D.chart a).γ t')) ∧
      ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0 := by
    have hU : ∀ᶠ t' in 𝓝 t, M.proj ((D.chart a).γ t') ∈ U := htend (hUo.mem_nhds hxU)
    have hnz : ∀ᶠ t' in 𝓝 t, ∀ kk, (D.chart a).γ t' ⟨kk, m kk⟩ ≠ 0 :=
      Filter.eventually_all.mpr fun kk => (hγp ⟨kk, m kk⟩).continuousAt.eventually_ne (hm kk)
    filter_upwards [hU, hev, hnz] with t' h1 h2 h3
    refine ⟨?_, h3⟩
    obtain ⟨h4, h5⟩ := hs _ h1
    exact (M.fibre _ h2 _ h4).mp h5.symm
  obtain ⟨cf, hcf⟩ : ∃ cf : (Fin D.n → ℂ) → K → ℂ, cf = fun t' kk =>
      s (M.proj ((D.chart a).γ t')) ⟨kk, m kk⟩ / (D.chart a).γ t' ⟨kk, m kk⟩ := ⟨_, rfl⟩
  have hcfeq : ∀ᶠ t' in 𝓝 t, ∀ p : (Σ kk, J kk),
      s (M.proj ((D.chart a).γ t')) p = cf t' p.1 * (D.chart a).γ t' p := by
    filter_upwards [hrel] with t' ht'
    obtain ⟨⟨c, hc, he⟩, hn⟩ := ht'
    have hck : ∀ kk, cf t' kk = c kk := by
      intro kk
      rw [hcf]
      simp only [he, torusSmul]
      exact mul_div_cancel_right₀ _ (hn kk)
    intro p
    rw [hck, he]
    rfl
  have hcf0 : ∀ kk, cf t kk ≠ 0 := by
    obtain ⟨⟨c, hc, he⟩, hn⟩ := hrel.self_of_nhds
    intro kk
    rw [hcf]
    simp only [he, torusSmul]
    rw [mul_div_cancel_right₀ _ (hn kk)]
    exact hc kk
  have hcfan : ∀ kk, AnalyticAt ℂ (fun t' => cf t' kk) t := by
    intro kk
    rw [hcf]
    exact (hHan _).div (hγp _) (hm kk)
  have hFt : M.atlas.chart k (M.proj ((D.chart a).γ t)) ∈ (M.atlas.chart k).target :=
    (M.atlas.chart k).map_source hsrc
  have hGan : ∀ p, AnalyticAt ℂ (fun y => s ((M.atlas.chart k).symm y) p)
      (M.atlas.chart k (M.proj ((D.chart a).γ t))) := by
    intro p
    refine hsh p k _ ⟨hFt, ?_⟩
    simp only [Set.mem_preimage, (M.atlas.chart k).left_inv hsrc]
    exact hxU
  have hG : DifferentiableAt ℂ (fun y => s ((M.atlas.chart k).symm y))
      (M.atlas.chart k (M.proj ((D.chart a).γ t))) :=
    differentiableAt_pi.mpr fun p => (hGan p).differentiableAt
  have hHeq : (fun t' => s (M.proj ((D.chart a).γ t'))) =ᶠ[𝓝 t]
      (fun t' => s ((M.atlas.chart k).symm (M.atlas.chart k (M.proj ((D.chart a).γ t'))))) := by
    filter_upwards [htend ((M.atlas.chart k).open_source.mem_nhds hsrc)] with t' h
    rw [(M.atlas.chart k).left_inv h]
  set L := fderiv ℂ (fun t' : Fin D.n → ℂ => M.atlas.chart k (M.proj ((D.chart a).γ t'))) t with hL
  set G' := fderiv ℂ (fun y => s ((M.atlas.chart k).symm y))
    (M.atlas.chart k (M.proj ((D.chart a).γ t))) with hG'
  have hc0 := hG.hasFDerivAt.comp t hFan.differentiableAt.hasFDerivAt
  have hH : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t'))) (G'.comp L) t :=
    hc0.congr_of_eventuallyEq hHeq
  have hinj : Function.Injective L := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro v hv
    apply (D.chart a).immersion t ht v
    refine ⟨fun kk => -(fderiv ℂ (fun t' => cf t' kk) t v) / cf t kk, ?_⟩
    funext p
    have h1 : HasFDerivAt (fun t' : Fin D.n → ℂ => s (M.proj ((D.chart a).γ t')) p)
        ((P p).comp (G'.comp L)) t :=
      (P p).hasFDerivAt.comp t hH
    have hγ' : HasFDerivAt (fun t' : Fin D.n → ℂ => (D.chart a).γ t' p)
        ((P p).comp (fderiv ℂ (D.chart a).γ t)) t :=
      (P p).hasFDerivAt.comp t hγ.differentiableAt.hasFDerivAt
    have h2 := (hcfan p.1).differentiableAt.hasFDerivAt.mul hγ'
    have h3 := h2.congr_of_eventuallyEq (hcfeq.mono fun t' h => h p)
    have h4 := DFunLike.congr_fun (h1.unique h3) v
    simp only [ContinuousLinearMap.comp_apply, hv, map_zero, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.smul_apply, smul_eq_mul, P, ContinuousLinearMap.proj_apply] at h4
    have h0 := hcf0 p.1
    have h5 : (0 : ℂ) = cf t p.1 * fderiv ℂ (D.chart a).γ t v p +
        (D.chart a).γ t p * fderiv ℂ (fun t' => cf t' p.1) t v := h4
    show fderiv ℂ (D.chart a).γ t v p = -(fderiv ℂ (fun t' => cf t' p.1) t v) / cf t p.1 * (D.chart a).γ t p
    rw [div_mul_eq_mul_div, eq_div_iff h0]
    linear_combination -h5
  exact ⟨hinj, (LinearMap.injective_iff_surjective (f := (L : (Fin D.n → ℂ) →ₗ[ℂ] (Fin D.n → ℂ)))).mp hinj⟩
end

