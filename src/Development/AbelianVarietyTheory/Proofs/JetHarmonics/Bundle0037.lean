module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MvPowerSeriesIntegralBoundedClosure
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0031
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0032
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0030

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsIsoMultiplicative
section
open GlobalTheory.ConvSer

namespace GlobalTheory.ConvSer.HeightOne

theorem exists_root_tower (K : Type) [Field K] [IsAlgClosed K] [CharZero K] (p : ℕ)
    [hp : Fact p.Prime] :
    ∃ ζ : ℕ → K, ζ 0 = 1 ∧ IsPrimitiveRoot (ζ 1) p ∧ (∀ n, ζ (n + 1) ^ p = ζ n) ∧
      ∀ n, ζ n ^ p ^ n = 1 := by
  have hp0 : 0 < p := hp.out.pos
  have : NeZero p := ⟨hp0.ne'⟩
  obtain ⟨z, hz⟩ : ∃ z : K, IsPrimitiveRoot z p := HasEnoughRootsOfUnity.exists_primitiveRoot K p
  choose r hr using fun x : K => IsAlgClosed.exists_pow_nat_eq x hp0
  have h : ∀ n, (fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z) (n + 1) ^ p
      = (fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z) n := by
    intro n
    cases n with
    | zero => exact hz.pow_eq_one
    | succ m =>
      show (r^[m + 1] z) ^ p = r^[m] z
      rw [Function.iterate_succ_apply', hr]
  refine ⟨fun n : ℕ => Nat.casesOn (motive := fun _ => K) n 1 fun m => r^[m] z, rfl, hz, h, ?_⟩
  intro n
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ', pow_mul, h n]; exact ih

theorem norm_le_pow_of_primitive {K : Type} [NormedField K] [IsUltrametricDist K] {p : ℕ}
    (hp : p.Prime) {z : K} (hz : IsPrimitiveRoot z p) :
    ‖(p : K)‖ ≤ ‖z - 1‖ ^ (p - 1) := by
  have hz1 : ‖z‖ = 1 := by
    have h := congrArg norm hz.pow_eq_one
    rw [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) hp.ne_zero).1 h
  have hle : ∀ j : ℕ, ‖1 - z ^ j‖ ≤ ‖z - 1‖ := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      have : 1 - z ^ (j + 1) = (1 - z ^ j) + -(z ^ j * (z - 1)) := by ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ih ?_)
      rw [norm_neg, norm_mul, norm_pow, hz1, one_pow, one_mul]
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp.pos).symm⟩
  have h := hz.prod_one_sub_pow_eq_order
  have h2 : ((m + 1 : ℕ) : K) = ∏ k ∈ Finset.range m, (1 - z ^ (k + 1)) := by
    rw [h]; push_cast; ring
  rw [h2, norm_prod, Nat.add_sub_cancel]
  calc ∏ k ∈ Finset.range m, ‖1 - z ^ (k + 1)‖ ≤ ∏ _k ∈ Finset.range m, ‖z - 1‖ :=
        Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hle _)
    _ = _ := by simp

theorem exists_iso_multiplicative (K : Type) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] [IsAlgClosed K] [CharZero K] (p : ℕ) [hp : Fact p.Prime]
    (F : FormalGroup K) (hF : Intg F.toPowerSeries)
    (h1 : ‖PowerSeries.coeff p (nMul F p)‖ = 1)
    (h2 : ∀ k < p, ‖PowerSeries.coeff k (nMul F p)‖ < 1) :
    ∃ f : PowerSeries K, Intg f ∧ PowerSeries.constantCoeff f = 0 ∧ ‖PowerSeries.coeff 1 f‖ = 1 ∧
      f.subst F.toPowerSeries = f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) +
        f.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) +
        f.subst (MvPowerSeries.X 0 : MvPowerSeries (Fin 2) K) *
          f.subst (MvPowerSeries.X 1 : MvPowerSeries (Fin 2) K) := by
  classical
  obtain ⟨t, ht1, ht0, htne, htp⟩ := GlobalTheory.T.exists_formalGroup_heightOne_torsion_tower K p F hF h1 h2
  obtain ⟨ζ, hζ0, hζ1, hζp, hζn⟩ := exists_root_tower K p
  obtain ⟨-, hpt⟩ := _root_.GlobalTheory.ConvSer.nMul_point K F hF
  obtain ⟨ho1, -, ho3⟩ := _root_.GlobalTheory.ConvSer.tower_exact_order K p F hF t ht1 ht0 htne htp
  obtain ⟨hn1, hn2, hn3, hn4⟩ := _root_.GlobalTheory.ConvSer.TowerNorm.tower_norm K p F hF h1 h2 t ht1 ht0 htne htp
  choose g hgI hgv using fun n => GlobalTheory.T.exists_integral_polynomial_torsion_character_level K p F hF t ht1 ht0 htne htp n (ζ n) (hζn n)
  obtain ⟨bI, -, bP, bC, bX, -, -, bS, -, bf⟩ := GlobalTheory.BddAlg.bdd_alg K (Fin 2)
  obtain ⟨bI1, -, bP1, bC1, -⟩ := GlobalTheory.BddAlg.bdd_alg K Unit
  set P : ℕ → ℕ → K := fun n j => ev1 (nMul F j) (t n) with hP
  have hP0 : ∀ n, P n 0 = 0 := fun n => (hpt _ (ht1 n)).1
  have hPlt : ∀ n j, ‖P n j‖ < 1 := fun n j =>
    (((hpt _ (ht1 n)).2.2.1 j).1).trans_lt (ht1 n)
  set G : ℕ → Finset K := fun n => (Finset.Ico 1 (p ^ n)).image (P n) with hG
  have hpn : ∀ n, 0 < p ^ n := fun n => pow_pos hp.out.pos n
  have hmem : ∀ n x, x ∈ G n ↔ ∃ j, ¬ p ^ n ∣ j ∧ P n j = x := by
    intro n x
    simp only [hG, Finset.mem_image, Finset.mem_Ico]
    constructor
    · rintro ⟨j, ⟨hj1, hj2⟩, rfl⟩
      exact ⟨j, Nat.not_dvd_of_pos_of_lt hj1 hj2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      refine ⟨j % p ^ n, ⟨?_, Nat.mod_lt _ (hpn n)⟩, (ho3 n _ _).2 (Nat.mod_modEq _ _)⟩
      exact Nat.pos_of_ne_zero fun h => hj (Nat.dvd_of_mod_eq_zero h)
  have hmono : Monotone G := by
    refine monotone_nat_of_le_succ fun n x hx => ?_
    obtain ⟨j, hj, rfl⟩ := (hmem n x).1 hx
    refine (hmem _ _).2 ⟨p * j, fun h => hj ?_, ho1 n j⟩
    rw [pow_succ'] at h
    exact Nat.dvd_of_mul_dvd_mul_left hp.out.pos h
  have hr0 : 0 < ‖t 1‖ := norm_pos_iff.2 htne
  have hGr : ∀ n, ∀ x ∈ G n, ‖t 1‖ ≤ ‖x‖ ∧ ‖x‖ < 1 := by
    intro n x hx
    obtain ⟨j, hj, rfl⟩ := (hmem n x).1 hx
    exact ⟨hn3 n j hj, hPlt n j⟩
  have hlim : Filter.Tendsto (fun n => ∏ x ∈ G n, ‖x‖) Filter.atTop (nhds 0) := by
    have : (fun n => ∏ x ∈ G n, ‖x‖) = fun n => ‖(p : K)‖ ^ n := by
      funext n
      rw [← hn4 n, hG]
      refine Finset.prod_image ?_
      intro i hi j hj hij
      simp only [Finset.coe_Ico, Set.mem_Ico] at hi hj
      exact Nat.ModEq.eq_of_lt_of_lt ((ho3 n i j).1 hij) hi.2 hj.2
    rw [this]
    exact tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg _) hn2
  have hgev : ∀ n m j k, P m k = P n j → ev1 (g m : PowerSeries K) (P n j) = ζ m ^ k := by
    intro n m j k h
    rw [((_root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K _ (hPlt n j)).2.2.2.2.1 (g m)).2, ← h]
    exact hgv m k
  obtain ⟨φ, hφI, hφc, hφv⟩ := _root_.GlobalTheory.ConvSer.exists_limit_of_agree_on_points K G ‖t 1‖ hr0 (ht1 1).le hmono hGr hlim
    (fun n => (g n : PowerSeries K))
    (fun n => (bf _).1.2 fun k => by rw [Polynomial.coeff_coe]; exact hgI n k)
    (by
      intro n x hx
      obtain ⟨j, -, rfl⟩ := (hmem n x).1 hx
      rw [hgev n (n + 1) j (p * j) (ho1 n j), hgev n n j j rfl, pow_mul, hζp])
  have hφ0 : PowerSeries.coeff 0 φ = 1 := by
    have h := hφc 0
    have : (fun n => PowerSeries.coeff 0 (g n : PowerSeries K)) = fun _ => (1 : K) := by
      funext n
      have h3 := hgv n 0
      change (g n).eval (P n 0) = _ at h3
      rw [hP0, pow_zero] at h3
      rw [Polynomial.coeff_coe, Polynomial.coeff_zero_eq_eval_zero, h3]
    rw [this] at h
    exact (tendsto_nhds_unique tendsto_const_nhds h).symm
  have hz : ‖(0 : K)‖ < 1 := by simp
  have hφP : ∀ n j, ev1 φ (P n j) = ζ n ^ j := by
    intro n j
    by_cases hj : p ^ n ∣ j
    · have : P n j = 0 := by
        rw [← hP0 n]
        exact (ho3 n _ _).2 ((Nat.modEq_zero_iff_dvd).2 hj)
      rw [this, (_root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K 0 hz).2.2.2.2.2.2.2.2.2.2 φ, hφ0]
      obtain ⟨c, rfl⟩ := hj
      rw [pow_mul, hζn, one_pow]
    · rw [hφv n _ ((hmem _ _).2 ⟨j, hj, rfl⟩)]
      exact hgev n n j j rfl
  have hC1 : Intg (PowerSeries.C (1 : K) : PowerSeries K) := (bC1 1).2.1 (by simp)
  set f : PowerSeries K := φ - PowerSeries.C 1 with hf
  have hfI : Intg f := (bI1 _ _ hφI hC1).2.1
  have hfB : Bdd f := (bP1 _ 0).2.2 hfI
  have hf0 : PowerSeries.coeff 0 f = 0 := by
    rw [hf, map_sub, hφ0]; simp
  have hfP : ∀ n j, ev1 f (P n j) = ζ n ^ j - 1 := by
    intro n j
    have h := _root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K _ (hPlt n j)
    rw [hf, (h.2.1 φ _ ((bP1 _ 0).2.2 hφI) ((bP1 _ 0).2.2 hC1)).2.1, h.2.2.1, hφP]
  refine ⟨f, hfI, by simpa using hf0, ?_, ?_⟩
  · by_contra hne
    have hlt : ‖PowerSeries.coeff 1 f‖ < 1 := lt_of_le_of_ne ((bf f).1.1 hfI 1) hne
    have hv : ev1 f (t 1) = ζ 1 - 1 := by
      have h := hfP 1 1
      rw [pow_one] at h
      rw [← h]
      congr 1
      exact ((hpt _ (ht1 1)).2.1).symm
    have he := ((_root_.GlobalTheory.ConvSer.powerSeriesEvalTsum_unitDisc_properties K _ (ht1 1)).2.2.2.2.2.2.1 f hfI).2.2
    rw [hv, hf0, sub_zero] at he
    have hlt2 : ‖ζ 1 - 1‖ < ‖t 1‖ := by
      have : ζ 1 - 1 = (ζ 1 - 1 - PowerSeries.coeff 1 f * t 1) + PowerSeries.coeff 1 f * t 1 := by
        ring
      rw [this]
      refine (IsUltrametricDist.norm_add_le_max _ _).trans_lt (max_lt (he.trans_lt ?_) ?_)
      · have := ht1 1
        nlinarith
      · rw [norm_mul]
        nlinarith
    have h3 := norm_le_pow_of_primitive hp.out hζ1
    have h4 : ‖ζ 1 - 1‖ ^ (p - 1) < ‖t 1‖ ^ (p - 1) :=
      pow_lt_pow_left₀ hlt2 (norm_nonneg _) (Nat.sub_ne_zero_of_lt hp.out.one_lt)
    linarith
  · have hF0 : MvPowerSeries.constantCoeff F.toPowerSeries = 0 := F.zero_constantCoeff
    have hX : ∀ i : Fin 2, Intg (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) :=
      fun i => (bX i).1
    have hX0 : ∀ i : Fin 2,
        MvPowerSeries.constantCoeff (MvPowerSeries.X i : MvPowerSeries (Fin 2) K) = 0 :=
      fun i => MvPowerSeries.constantCoeff_X i
    have iF := (bS _ f hF hF0).1 hfI
    have i0 := (bS _ f (hX 0) (hX0 0)).1 hfI
    have i1 := (bS _ f (hX 1) (hX0 1)).1 hfI
    have i01 := (bI _ _ i0 i1).1
    have i01' := (bI _ _ i0 i1).2.2
    have iR := (bI _ _ i01 i01').1
    have bd : ∀ S : MvPowerSeries (Fin 2) K, Intg S → Bdd S := fun S h => (bP S 0).2.2 h
    rw [← sub_eq_zero]
    refine _root_.GlobalTheory.ConvSer.eq_zero_of_ev_vanish K G ‖t 1‖ hr0 (ht1 1).le hmono hGr hlim _ (bI _ _ iF iR).2.1 ?_
    intro n x hx y hy
    obtain ⟨i, -, rfl⟩ := (hmem n x).1 hx
    obtain ⟨j, -, rfl⟩ := (hmem n y).1 hy
    obtain ⟨-, eA, -, eX, -, -, -, eS⟩ := _root_.GlobalTheory.ConvSer.ev_algebra K (Fin 2) ![P n i, P n j]
      (Fin.forall_fin_two.2 ⟨hPlt n i, hPlt n j⟩)
    have hs : ev F.toPowerSeries ![P n i, P n j] = P n (i + j) := (hpt _ (ht1 n)).2.2.2.1 i j
    rw [(eA _ _ (bd _ iF) (bd _ iR)).2.1, (eA _ _ (bd _ i01) (bd _ i01')).1,
      (eA _ _ (bd _ i0) (bd _ i1)).1, (eA _ _ (bd _ i0) (bd _ i1)).2.2,
      eS _ f hF hF0 hfB, eS _ f (hX 0) (hX0 0) hfB, eS _ f (hX 1) (hX0 1) hfB, eX, eX, hs]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one]
    rw [hfP, hfP, hfP]
    ring

end GlobalTheory.ConvSer.HeightOne
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsRationalIsometryOfTraceIsometry
section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD
open scoped Matrix

namespace GlobalTheory.TraceIsometry

variable {E : Type} [Field E] [NumberField E] [IsCMField E]


open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq {x y : E} (hx : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc x = -x) (hy : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc y = -y)
    (h : ∀ τ : E →+* ℂ, ‖τ x‖ = ‖τ y‖) : y = x ∨ y = -x := by
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hre : ∀ z : E, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc z = -z → (τ z).re = 0 := by
    intro z hz
    have h1 := _root_.GlobalTheory.PerMove.map_cc τ z
    rw [hz, map_neg] at h1
    have h2 := congrArg Complex.re h1
    simp only [Complex.neg_re, Complex.conj_re] at h2
    linarith
  have hxr := hre x hx
  have hyr := hre y hy
  have key : (τ y).im = (τ x).im ∨ (τ y).im = -(τ x).im := by
    have h2 : ‖τ x‖ ^ 2 = ‖τ y‖ ^ 2 := by rw [h τ]
    rw [Complex.sq_norm, Complex.sq_norm, Complex.normSq_apply, Complex.normSq_apply, hxr,
      hyr] at h2
    exact mul_self_eq_mul_self_iff.mp (by linarith)
  rcases key with k | k
  · left
    apply τ.injective
    apply Complex.ext <;> simp [hxr, hyr, k]
  · right
    apply τ.injective
    rw [map_neg]
    apply Complex.ext <;> simp [hxr, hyr, k]


open NumberField in
open scoped Matrix in
variable {E : Type} [Field E] [NumberField E] [IsCMField E] in
theorem _root_.GlobalTheory.TraceIsometry.exists_gl_of_trace_isometry : ∀ (E : Type) [Field E] [NumberField E]
    [IsCMField E] (r : ℕ) (X X' : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r), (∀ τ : E →+* ℂ, ‖τ X.ξ0‖ = ‖τ X'.ξ0‖) →
    ∀ (gam : X.Λ ≃ₗ[𝓞 E] X'.Λ), (∀ u v : X.Λ, Algebra.trace ℚ E (-X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm
    (gam u : Fin r → E) (gam v : Fin r → E)) = Algebra.trace ℚ E (-X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm
    (u : Fin r → E) (v : Fin r → E))) → ∃ (a : GL (Fin r) E) (ε : E), (ε = 1 ∨ ε = -1) ∧
    X'.ξ0 = ε * X.ξ0 ∧ (∀ v : X.Λ, (a : Matrix (Fin r) (Fin r) E) *ᵥ (v : Fin r → E) =
    (gam v : Fin r → E)) ∧ (∀ v, v ∈ X.Λ ↔ (a : Matrix (Fin r) (Fin r) E) *ᵥ v ∈ X'.Λ) ∧
    ∀ u v, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm ((a : Matrix (Fin r) (Fin r) E) *ᵥ u)
    ((a : Matrix (Fin r) (Fin r) E) *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
  intro E _ _ _ r X X' hξ gam hgam
  obtain ⟨ε, hε1, hεξ⟩ : ∃ ε : E, (ε = 1 ∨ ε = -1) ∧ X'.ξ0 = ε * X.ξ0 := by
    rcases _root_.GlobalTheory.TraceIsometry.eq_or_eq_neg_of_norm_eq X.ξ0_im X'.ξ0_im hξ with h | h
    · exact ⟨1, Or.inl rfl, by rw [h, one_mul]⟩
    · exact ⟨-1, Or.inr rfl, by rw [h, neg_one_mul]⟩
  have hsp : ∀ Y : _root_.ReciprocityTheory.ChartRestriction.G.FD.Data E r, Submodule.span E (Set.range Y.Λ.subtype) = ⊤ := by
    intro Y
    have : Set.range Y.Λ.subtype = (Y.Λ : Set (Fin r → E)) := by ext; simp
    rw [this]
    exact Y.Λ_span
  obtain ⟨A, hA⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X.Λ.subtype
    Subtype.val_injective (hsp X) (X'.Λ.subtype ∘ₗ gam.toLinearMap)
  obtain ⟨B, hB⟩ := _root_.GlobalTheory.FrameFibre.exists_matrix X'.Λ.subtype
    Subtype.val_injective (hsp X') (X.Λ.subtype ∘ₗ gam.symm.toLinearMap)
  have hA' : ∀ v : X.Λ, A *ᵥ (v : Fin r → E) = (gam v : Fin r → E) := fun v => hA v
  have hB' : ∀ w : X'.Λ, B *ᵥ (w : Fin r → E) = (gam.symm w : Fin r → E) := fun w => hB w
  have hBA : B * A = 1 := by
    have hlin : Matrix.mulVecLin (B * A) = LinearMap.id := by
      apply LinearMap.ext_on X.Λ_span
      intro v hv
      simp only [Matrix.mulVecLin_apply, LinearMap.id_apply]
      rw [← Matrix.mulVec_mulVec, show A *ᵥ v = _ from hA' ⟨v, hv⟩, hB']
      simp
    apply Matrix.ext_of_mulVec_single
    intro i
    have h1 := LinearMap.congr_fun hlin (Pi.single i 1)
    simp only [Matrix.mulVecLin_apply, LinearMap.id_apply] at h1
    rw [h1, Matrix.one_mulVec]
  have hsm : ∀ (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (x y : Fin r → E),
      _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G (c • x) y = (c : E) * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm G x y := by
    intro G c x y
    have h1 := _root_.GlobalTheory.FrameFibre.herm_smul_smul G (c : E) 1 x y
    rw [one_smul, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_one, mul_one] at h1
    rw [← h1]
    rfl
  have hL : ∀ u v : X.Λ, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) =
      ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    have hD : -X'.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (gam u) (gam v) - -X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v = 0 := by
      apply _root_.GlobalTheory.FrameFibre.eq_zero_of_trace
      intro c
      have h1 := hgam (c • u) v
      rw [LinearEquiv.map_smul, Submodule.coe_smul, Submodule.coe_smul, hsm, hsm] at h1
      rw [mul_sub, map_sub, sub_eq_zero, mul_left_comm (c : E), mul_left_comm (c : E)]
      exact h1
    rw [hεξ, ← hA' u, ← hA' v] at hD
    have hε2 : ε * ε = 1 := by rcases hε1 with h | h <;> rw [h] <;> ring
    apply mul_left_cancel₀ X.ξ0_ne
    linear_combination (-ε) * hD -
      X.ξ0 * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ (u : Fin r → E)) (A *ᵥ (v : Fin r → E)) * hε2
  have hall : ∀ u v : Fin r → E, _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X'.Gm (A *ᵥ u) (A *ᵥ v) = ε * _root_.ReciprocityTheory.ChartRestriction.G.FD.herm X.Gm u v := by
    intro u v
    obtain ⟨c, u', hc, hu'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) u
    obtain ⟨d, v', hd, hv'⟩ := _root_.GlobalTheory.FrameFibre.exists_smul_eq X.Λ.subtype (hsp X) v
    have h1 := hL u' v'
    have hu'' : (u' : Fin r → E) = (c : E) • u := hu'.symm
    have hv'' : (v' : Fin r → E) = (d : E) • v := hv'.symm
    rw [hu'', hv'', Matrix.mulVec_smul, Matrix.mulVec_smul, _root_.GlobalTheory.FrameFibre.herm_smul_smul,
      _root_.GlobalTheory.FrameFibre.herm_smul_smul] at h1
    have hc' : (c : E) ≠ 0 := by exact_mod_cast hc
    have hd' : (d : E) ≠ 0 := by exact_mod_cast hd
    have hcc : _root_.ReciprocityTheory.ChartRestriction.G.FD.cc (d : E) ≠ 0 := by
      intro h0
      apply hd'
      rw [← _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_cc (d : E), h0, _root_.ReciprocityTheory.ChartRestriction.G.FD.cc_zero]
    apply mul_left_cancel₀ (mul_ne_zero hc' hcc)
    linear_combination h1
  refine ⟨⟨A, B, (mul_eq_one_comm.mp hBA), hBA⟩, ε, hε1, hεξ, hA', ?_, hall⟩
  intro v
  change v ∈ X.Λ ↔ A *ᵥ v ∈ X'.Λ
  constructor
  · intro hv
    rw [show A *ᵥ v = _ from hA' ⟨v, hv⟩]
    exact (gam ⟨v, hv⟩).2
  · intro hv
    have h1 : B *ᵥ (A *ᵥ v) = v := by rw [Matrix.mulVec_mulVec, hBA, Matrix.one_mulVec]
    rw [← h1, show B *ᵥ (A *ᵥ v) = _ from hB' ⟨A *ᵥ v, hv⟩]
    exact (gam.symm _).2

end GlobalTheory.TraceIsometry
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.InvariantHermitianFormNonnegOfCloudEigen
section
open Finset BranchingSupport Formalism.REAL Formalism.QuantumDeterminants
open scoped InnerProductSpace

namespace GlobalTheory

theorem hhJ_nonneg_of_cloud_eigen : ∀ (M : Type) [NormedAddCommGroup M] [InnerProductSpace ℂ M] (n : ℕ) (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ M) (μ : Fin n → ℝ) (kk j : ℕ) (bv : ℝ) (x : Fin n → M), IsMod ε E μ → Shape ε kk μ bv → j ≤ 4 * n ^ 2 + 2 → (∀ c, Lev ε E μ j (x c)) → ∀ s : Fin n, s.val + 1 < kk → splitCas E x = ((-μ s + (1 - (n : ℝ)) / 2 : ℝ) : ℂ) • x → 0 ≤ (hhJ ε x x).re := by
  intro M _ _ n ε E μ kk j bv x hM hS hj hL s hs hx
  obtain ⟨hb, hω, hζ⟩ := GlobalTheory.shape_position n kk j ε μ bv hS hj
  have hO := _root_.GlobalTheory.offDiagPart_sq_le_of_lev M n ε E μ kk j bv x hM hS hj hL
  set ζ : ℝ := -μ s + (1 - (n : ℝ)) / 2 with hζdef
  have hζs : ζ ≤ bv / 32 := ((hζ s).1 hs).2
  have hnode : ∀ c : Fin n, kk ≤ c.val + 1 →
      (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 ≤ ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 := by
    intro c hc
    have h1 := (GlobalTheory.wtNear_diag_bounds M n ε E (lowK ε μ) (j : ℝ) (x c) hM.2.1 (hL c).2).2.1 c (ζ : ℂ)
      (15 * bv / 16) (by positivity) (by
        intro ω hw
        have h2 := ((hω ω hw c).2 hc).1
        rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
        have := neg_abs_le (ζ + ω c)
        linarith)
    have h3 := congrFun hx c
    simp only [splitCas, Pi.smul_apply] at h3
    rw [← Finset.add_sum_erase univ (fun a => E c a (x a)) (mem_univ c)] at h3
    have h4 : (ζ : ℂ) • x c + E c c (x c) = -∑ a ∈ univ.erase c, E c a (x a) := by
      rw [← h3]; abel
    rw [h4, norm_neg] at h1
    exact h1
  have hterm : ∀ c : Fin n, (15 * bv / 16) ^ 2 * ‖x c‖ ^ 2 - 2 * ‖∑ a ∈ univ.erase c, E c a (x a)‖ ^ 2 ≤
      (15 * bv / 16) ^ 2 * ((if ε c then 1 else -1) * ⟪x c, x c⟫_ℂ : ℂ).re := by
    intro c
    have hin : (⟪x c, x c⟫_ℂ : ℂ).re = ‖x c‖ ^ 2 := by
      simpa using inner_self_eq_norm_sq (𝕜 := ℂ) (x c)
    by_cases he : ε c = true
    · rw [if_pos he, one_mul, hin]
      have := sq_nonneg ‖∑ a ∈ univ.erase c, E c a (x a)‖
      linarith
    · have hc : kk ≤ c.val + 1 := by
        by_contra h
        exact he (hS.2.2.2.1 c (not_le.mp h)).1
      rw [if_neg he, neg_one_mul, Complex.neg_re, hin]
      have := hnode c hc
      linarith
  have hsum := Finset.sum_le_sum (fun c (_ : c ∈ (univ : Finset (Fin n))) => hterm c)
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum, ← Complex.re_sum] at hsum
  have hS0 : 0 ≤ ∑ c, ‖x c‖ ^ 2 := Finset.sum_nonneg fun c _ => sq_nonneg _
  have hpos : 0 < (15 * bv / 16) ^ 2 := by positivity
  have hkey : 0 ≤ (15 * bv / 16) ^ 2 * (hhJ ε x x).re := by
    unfold hhJ
    have : 0 ≤ bv ^ 2 * ∑ c, ‖x c‖ ^ 2 := mul_nonneg (sq_nonneg _) hS0
    nlinarith
  exact (mul_nonneg_iff_of_pos_left hpos).mp hkey

end GlobalTheory
end

