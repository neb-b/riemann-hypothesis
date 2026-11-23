module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.LocalToGlobal.LatticeGeometry.OperatorNormFibers.PDescentCutA
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0186
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0163
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBessel
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlag
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.FullFlag

theorem rkK_mono {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [FiniteDimensional K V] {M N : Submodule (𝓞 K) V} (h : M ≤ N) : Formalism.HN.rkK M ≤ Formalism.HN.rkK N :=
  Submodule.finrank_mono (Submodule.span_mono h)

theorem main : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  intro I xf a j S hS
  obtain ⟨h0, hmono, hrk, hsat, hiso⟩ := hS
  set x : I.GA := (1, xf) with hx
  obtain ⟨-, hA, -, -, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨-, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hmain⟩ := PerpStep.main I x
  have hform : ∀ s y : Fin I.n → I.E,
      star s ⬝ᵥ (I.J *ᵥ y) = Formalism.UG.hform (starRingEnd I.E) I.J s y := by
    intro s y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply,
      -star_trivial]
  have hmem : ∀ N y, y ∈ perpIn I x N ↔ y ∈ lamX I x ∧ ∀ s ∈ N, star s ⬝ᵥ (I.J *ᵥ y) = 0 := by
    intro N y
    rw [PerpStep.perpIn_eq, PerpStep.mem_perp]
    simp only [hform]
  have hsatS : ∀ i, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i) := by
    intro i
    have e : S i = lamX I x ⊓ (Submodule.span I.E (S i : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) := by
      ext y
      exact hsat i y
    rw [e]
    exact PerpStep.sat_inf (bas I) (frm I x) hX _ hA _
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      ∀ b, G b = S ⟨min b a, Nat.lt_succ_of_le (min_le_right _ _)⟩ := ⟨_, fun _ => rfl⟩
  have hGS : ∀ i : Fin (a + 1), G i = S i := by
    intro i
    rw [hG]
    congr 1
    ext
    have := i.2
    simp only
    omega
  have hG0 : G 0 = ⊥ := (hGS 0).trans h0
  have hGm : Monotone G := by
    intro b c h
    rw [hG, hG]
    exact hmono (Fin.mk_le_mk.2 (min_le_min_right _ h))
  have hGsat : ∀ b, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G b) := by
    intro b
    rw [hG]
    exact hsatS _
  have hGr : ∀ i : Fin a, Formalism.HN.rkK (G (i + 1)) = Formalism.HN.rkK (G i) + j i := by
    intro i
    have h1 := hGS i.succ
    have h2 := hGS i.castSucc
    rw [Fin.val_succ] at h1
    rw [Fin.val_castSucc] at h2
    rw [h1, h2, hrk]
  have hGsum : ∀ b (hb : b ≤ a), Formalism.HN.rkK (G b) = ∑ i : Fin b, j (Fin.castLE hb i) := by
    intro b
    induction b with
    | zero => intro _; simp [hG0, Formalism.HN.rkK]
    | succ b ih =>
      intro hb
      rw [Fin.sum_univ_castSucc]
      have := hGr ⟨b, hb⟩
      simp only at this
      rw [this, ih (by omega)]
      rfl
  have hGa : Formalism.HN.rkK (G a) = ∑ i, j i := by
    rw [hGsum a le_rfl]; rfl
  have hPr : ∀ b, Formalism.HN.rkK (perpIn I x (G b)) + Formalism.HN.rkK (G b) = I.n :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.1
  have hPP : ∀ b, perpIn I x (perpIn I x (G b)) = G b :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.2.1
  have hPa : ∀ b c, b ≤ c → perpIn I x (G c) ≤ perpIn I x (G b) :=
    fun b c h => (hmain _ _ (hGsat b) (hGsat c) (hGm h)).2.2.2.1
  have hP0 : perpIn I x (G 0) = lamX I x := by
    ext y
    rw [hmem, hG0]
    refine ⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp
  have hmid : G a ≤ perpIn I x (G a) := by
    intro y hy
    have e : G a = S (Fin.last a) := hGS (Fin.last a)
    rw [hmem]
    refine ⟨(hGsat a).1 hy, fun s hs => ?_⟩
    rw [hform]
    rw [e] at hs hy
    exact hiso s hs y hy
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ b, b ≤ a → F b = G b) ∧ ∀ b c, a < b → c = 2 * a + 1 - b → F b = perpIn I x (G c) :=
    ⟨fun b => if b ≤ a then G b else perpIn I x (G (2 * a + 1 - b)), fun b hb => if_pos hb,
      fun b c hb hc => hc ▸ if_neg (by omega)⟩
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun b => ?_
    rcases lt_trichotomy b a with h | rfl | h
    · rw [hF1 b h.le, hF1 (b + 1) h]
      exact hGm (by omega)
    · rw [hF1 b le_rfl, hF2 (b + 1) b (by omega) (by omega)]
      exact hmid
    · rw [hF2 b _ h rfl, hF2 (b + 1) _ (by omega) rfl]
      exact hPa _ _ (by omega)
  have hFtop : ∀ b, 2 * a + 1 ≤ b → F b = lamX I x := fun b hb => by
    rw [hF2 b 0 (by omega) (by omega), hP0]
  refine ⟨F, fun b => Formalism.HN.rkK (F (b + 1)) - Formalism.HN.rkK (F b), ⟨hFm, ?_, ?_, ?_⟩, hFtop _ le_rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF1 0 (by omega), hG0]
  · intro b hb
    rw [hFtop b hb, hFtop _ le_rfl]
  · intro b hb y
    rw [hFtop _ le_rfl, ← hmem]
    by_cases h : b ≤ a
    · rw [hF1 b h, hF2 _ b (by omega) (by omega)]
    · rw [hF2 b _ (by omega) rfl, hPP, hF1 _ (by omega)]
  · intro i
    rw [hF1 i (by have := i.2; omega), hGS]
  · intro b
    have := rkK_mono (hFm (Nat.le_succ b))
    simp only [Nat.succ_eq_add_one] at this ⊢
    omega
  · intro i
    have hi := i.2
    have h1 := hGr i
    have h2 := hPr i
    have h3 := hPr (i + 1)
    simp only
    rw [hF1 i (by omega), hF1 (i + 1) (by omega), hF2 (2 * a - i + 1) i (by omega) (by omega),
      hF2 (2 * a - i) (i + 1) (by omega) (by omega)]
    omega
  · have h2 := hPr a
    simp only
    rw [hF1 a le_rfl, hF2 (a + 1) a (by omega) (by omega)]
    omega
  · intro b hb
    simp only
    rw [hFtop b hb, hFtop _ (by omega), Nat.sub_self]

end GlobalTheory.RadCov.FullFlag
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSizeEqLeast
section
open GlobalTheory.Count Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField MeasureTheory Finset

noncomputable section

namespace GlobalTheory.NearLower

section General

variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] [DecidableEq ι] (b : Module.Basis ι K V)
  (X : InfinitePlace K → Matrix ι ι ℂ)


omit [_root_.NumberField.IsTotallyComplex K] in
theorem le_of_le_span (hX : ∀ v, IsUnit (X v).det) {L S N : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hN : N ≤ L)
    (h : (N : Set V) ⊆ Submodule.span K (S : Set V)) : N ≤ S := by
  have hle : S ⊔ N ≤ L := sup_le hS.1 hN
  have hsp : Submodule.span K ((S ⊔ N : Submodule (𝓞 K) V) : Set V) = Submodule.span K (S : Set V) := by
    apply le_antisymm
    · rw [Submodule.span_le]
      intro y hy
      obtain ⟨s, hs, n, hn, rfl⟩ := Submodule.mem_sup.1 hy
      exact Submodule.add_mem _ (Submodule.subset_span hs) (h hn)
    · exact Submodule.span_mono (SetLike.coe_subset_coe.2 le_sup_left)
  have h1 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hle)).2.1
  have h2 := (plLat K V ι b X hX _ (Submodule.FG.of_le hL hS.1)).2.1
  have h3 : rkK (S ⊔ N) = rkK S := by unfold rkK; rw [hsp]
  have h4 := (satBasic _ _ _ (Formalism.HermitianLatticesTheory.realize b X) L (plLat K V ι b X hX L hL).1).2.2.1 S (S ⊔ N) hS
    le_sup_left hle (by rw [h1, h2, h3])
  exact sup_eq_left.1 h4

theorem exists_size_eq_least (hX : ∀ v, IsUnit (X v).det) {B : Submodule (𝓞 K) V} (hB : B.FG) (h0 : B ≠ ⊥) :
    ∃ N : Submodule (𝓞 K) V, N ≤ B ∧ N ≠ ⊥ ∧ size b X N = leastSize b X B := by
  obtain ⟨-, -, ⟨N, hsat, hN, hsl⟩, -⟩ :=
    muChar _ _ _ (Formalism.HermitianLatticesTheory.realize b X) B (plLat K V ι b X hX B hB).1 h0
  refine ⟨N, hsat.1, hN, ?_⟩
  rw [(sizeMu K V ι b X hX B hB h0).2.2.2.1,
    (sizeMu K V ι b X hX N (Submodule.FG.of_le hB hsat.1) hN).1, hsl]

theorem map_le_of_sizes (hX : ∀ v, IsUnit (X v).det) {L S A : Submodule (𝓞 K) V} (hL : L.FG)
    (hS : IsSat (Formalism.HermitianLatticesTheory.realize b X) L S) (hA : A ≤ L) (ψ : V →ₗ[K] V)
    (hψ : A.map (ψ.restrictScalars (𝓞 K)) ≤ L) {δ t : ℝ} (hδ : 0 < δ)
    (hn : ∀ v y, Formalism.HermitianLatticesTheory.normAt b X v (ψ y) ≤ δ * Formalism.HermitianLatticesTheory.normAt b X v y)
    (hAt : A ≠ ⊥ → largestSize b X A ≤ t)
    (hSt : ∀ N, S < N → N ≤ L → δ * t < sizeQ b X N S) :
    A.map (ψ.restrictScalars (𝓞 K)) ≤ S := by
  have hQ := quotRealize K V ι b X hX L S hL hS
  set U := Submodule.span K (S : Set V) with hU
  obtain ⟨κ, _, _, b', X', hX', hnorm, hq⟩ := hQ
  by_cases h0 : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) = ⊥
  · refine le_of_le_span b X hX hL hS hψ ?_
    rintro _ ⟨y, hy, rfl⟩
    have : (U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K) y ∈ A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) :=
      Submodule.mem_map_of_mem hy
    rw [h0, Submodule.mem_bot] at this
    exact (Submodule.Quotient.mk_eq_zero U).1 this
  exfalso
  have hA0 : A ≠ ⊥ := fun h => h0 (by rw [h, Submodule.map_bot])
  have hAfg : A.FG := Submodule.FG.of_le hL hA
  set B := L.map (U.mkQ.restrictScalars (𝓞 K)) with hB
  have hBfg : B.FG := hL.map _
  have hAB : A.map ((U.mkQ ∘ₗ ψ).restrictScalars (𝓞 K)) ≤ B := by
    rintro _ ⟨y, hy, rfl⟩
    exact ⟨ψ y, hψ ⟨y, hy, rfl⟩, rfl⟩
  have hB0 : B ≠ ⊥ := fun h => h0 (le_bot_iff.1 (h ▸ hAB))
  have hM := sizeIneq K V ι _ κ b X b' X' hX hX' (U.mkQ ∘ₗ ψ) A B hAfg hBfg hAB h0

  have hop : ∀ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ := by
    intro v
    refine Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X b' X' hX _ v δ hδ.le fun y => ?_
    refine le_trans ?_ (hn v y)
    rw [LinearMap.comp_apply, hnorm]
    refine (Submodule.norm_starProjection_apply_le _ _).trans (le_of_eq ?_)
    rw [Formalism.HermitianLatticesTheory.normAt, Formalism.HN.PlaceOperatorNorms.cnorm_eq]
    rfl
  have hf : (0 : ℝ) < nPl K := by
    have : 0 < nPl K := Fintype.card_pos
    exact_mod_cast this
  have hP : (∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ)) ^ ((1 : ℝ) / (nPl K : ℝ)) ≤ δ := by
    have h1 : ∏ v, opNormAt b X b' X' v (U.mkQ ∘ₗ ψ) ≤ δ ^ nPl K := by
      calc _ ≤ ∏ _v : InfinitePlace K, δ := Finset.prod_le_prod₀ (fun v _ => norm_nonneg _) fun v _ => hop v
        _ = δ ^ nPl K := by rw [Finset.prod_const, Finset.card_univ]; rfl
    calc _ ≤ (δ ^ nPl K) ^ ((1 : ℝ) / (nPl K : ℝ)) :=
          Real.rpow_le_rpow (Finset.prod_nonneg fun v _ => norm_nonneg _) h1 (by positivity)
      _ = δ := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hδ.le, mul_one_div_cancel hf.ne', Real.rpow_one]

  obtain ⟨N, hNB, hN0, hNs⟩ := exists_size_eq_least b' X' hX' hBfg hB0
  set N' := L ⊓ N.comap (U.mkQ.restrictScalars (𝓞 K)) with hN'
  have hS0 : ∀ s ∈ S, U.mkQ s = 0 := fun s hs => (Submodule.Quotient.mk_eq_zero U).2 (Submodule.subset_span hs)
  have hSN : S ≤ N' := by
    intro s hs
    refine ⟨hS.1 hs, ?_⟩
    show U.mkQ s ∈ N
    rw [hS0 s hs]; exact N.zero_mem
  have hmap : N'.map (U.mkQ.restrictScalars (𝓞 K)) = N := by
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩; exact hy.2
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := hNB hz
      exact ⟨y, ⟨hy, hz⟩, rfl⟩
  have hne : S ≠ N' := by
    intro h
    apply hN0
    rw [← hmap, ← h, eq_bot_iff]
    rintro _ ⟨s, hs, rfl⟩
    exact hS0 s hs
  have hlt := hSt N' (lt_of_le_of_ne hSN hne) inf_le_left
  rw [(hq N' hSN inf_le_left).2, hmap, hNs] at hlt
  have hpos : 0 < largestSize b X A := by
    rw [(sizeMu K V ι b X hX A hAfg hA0).2.2.2.2.1]; exact Real.exp_pos _
  have h2 := (div_le_iff₀ hpos).1 (hM.trans hP)
  have h3 := mul_le_mul_of_nonneg_left (hAt hA0) hδ.le
  linarith

end General

theorem cnorm_mulVec_le {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (u : Fin n → ℂ) :
    Formalism.HermitianLatticesTheory.cnorm (M *ᵥ u) ≤ Real.sqrt (Formalism.REAL.hs M) * Formalism.HermitianLatticesTheory.cnorm u := by
  unfold Formalism.HermitianLatticesTheory.cnorm Formalism.REAL.hs
  rw [← Real.sqrt_mul (by positivity), Finset.sum_mul]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans ?_ (Finset.sum_mul_sq_le_sq_mul_sq univ (fun j => ‖M i j‖) (fun j => ‖u j‖))
  refine pow_le_pow_left₀ (norm_nonneg _) ?_ 2
  simp only [Matrix.mulVec, dotProduct]
  exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => (norm_mul _ _).le)

theorem hs_conj_sub_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.hs (M.map (starRingEnd ℂ) - 1) = Formalism.REAL.hs (M - 1) := by
  unfold Formalism.REAL.hs
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← Complex.norm_conj ((M - 1) i j)]
  simp only [Matrix.sub_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
  split_ifs <;> simp

theorem normAt_sub_one_le (I : AutInst) (x : I.GA) (g : Matrix (Fin I.n) (Fin I.n) I.E) (w : InfinitePlace I.E)
    {δ : ℝ} (h : Real.sqrt (Formalism.REAL.hs ((frm I x w)⁻¹ * g.map w.embedding * frm I x w - 1)) ≤ δ)
    (y : Fin I.n → I.E) :
    Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w (Matrix.toLin' (g - 1) y) ≤
      δ * Formalism.HermitianLatticesTheory.normAt (bas I) (frm I x) w y := by
  have hX := GlobalTheory.NearLowerCompare.frm_isUnit I x
  have e : (frm I x w)⁻¹ * (LinearMap.toMatrix (bas I) (bas I) (Matrix.toLin' (g - 1))).map w.embedding *
      frm I x w = (frm I x w)⁻¹ * g.map w.embedding * frm I x w - 1 := by
    rw [LinearMap.toMatrix_eq_toMatrix', LinearMap.toMatrix'_toLin', Matrix.map_sub _ (map_sub _),
      Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one,
      Matrix.nonsing_inv_mul _ (hX w)]
  unfold Formalism.HermitianLatticesTheory.normAt
  rw [Formalism.HN.PlaceOperatorNorms.fcoord_map (bas I) (frm I x) (bas I) (frm I x) hX w, e]
  exact (cnorm_mulVec_le _ _).trans (mul_le_mul_of_nonneg_right h (Real.sqrt_nonneg _))

theorem lowers (I : AutInst) (x : I.GA) (de : ℝ) (hde : 0 < de) (γ : GL (Fin I.n) I.E) (a : I.GA)
    (h1 : γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J)
    (h2 : ∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v)
    (h3 : I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)))
    (ha : a ∈ nearSet I x de) (t : ℝ) (ht : 0 < t) :
    (stepLe I x t).map ((Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1)).restrictScalars (𝓞 I.E)) ≤
      stepLe I x (de * t) := by
  have : IsTotallyComplex I.E := I.cm.cmUnram.1
  obtain ⟨-, -, -, -, -, hK, hw⟩ := GlobalTheory.T.autPoint_rational_equivariance I x γ a h1 h2 h3
  have hΛ := hK.1 ha.2.1
  obtain ⟨hA, -, -, -, hAt, -⟩ := _root_.GlobalTheory.CountSteps.steps I x t ht
  obtain ⟨hS, -, -, -, -, -, hSt, -⟩ := _root_.GlobalTheory.CountSteps.steps I x (de * t) (mul_pos hde ht)
  refine map_le_of_sizes (bas I) (frm I x) (GlobalTheory.NearLowerCompare.frm_isUnit I x)
    (GlobalTheory.NearLowerCompare.lamX_isLattice I x).fg hS hA.1 _ ?_ hde ?_ hAt hSt
  · rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ lamX I x := hA.1 hy
    have : Matrix.toLin' (γ : Matrix (Fin I.n) (Fin I.n) I.E) y ∈ lamX I x := by
      rw [← hΛ]; exact ⟨y, hy', rfl⟩
    simpa [map_sub, Matrix.sub_mulVec] using (lamX I x).sub_mem this hy'
  · intro w
    refine normAt_sub_one_le I x _ w ?_
    rcases hw w with h | h
    · rw [h]; exact ha.2.2 _
    · rw [h, hs_conj_sub_one]; exact ha.2.2 _

theorem nearSet_eq (I : AutInst) (x : I.GA) (de : ℝ) (hde : 0 < de) (hde' : de < 1 / 4)
    (hl : 1 / 2 ≤ least I x) : nearSet I x de = {1} := by
  refine Set.eq_singleton_iff_unique_mem.2 ⟨GlobalTheory.Count.Test.one_mem_nearSet I x hde.le, fun a ha => ?_⟩
  by_cases hn : I.n = 0
  · have := GlobalTheory.NearLowerCompare.subsingleton_GA I hn
    exact Subsingleton.elim _ _
  have hn1 : 1 ≤ I.n := Nat.one_le_iff_ne_zero.2 hn
  obtain ⟨γ, h1, h2, h3⟩ := ha.1
  have hlow := lowers I x de hde γ a h1 h2 h3 ha 2 two_pos
  have hbot : stepLe I x (de * 2) = ⊥ :=
    ((_root_.GlobalTheory.CountSteps.steps I x (de * 2) (by positivity)).2.2.2.2.2.2.2.2 hn1).2.1.2 (by linarith)
  have hspan := (GlobalTheory.PointLattice.lamX_selfDual I x).2.2.1
  have h0 : lamX I x ≠ ⊥ := by
    intro h0
    have h1 := hspan
    rw [h0] at h1
    have : Nonempty (Fin I.n) := ⟨⟨0, Nat.pos_of_ne_zero hn⟩⟩
    simp at h1
  have hle : lamX I x ≤ stepLe I x 2 := by
    refine le_sSup ⟨le_rfl, h0, ?_⟩
    rw [(_root_.GlobalTheory.Count.PerpStep.main I x).2.1 hn1]
    exact inv_le_of_inv_le₀ two_pos (by linarith)
  have hz : Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1) = 0 := by
    refine LinearMap.ext_on hspan fun y hy => ?_
    have := hlow ⟨y, hle hy, rfl⟩
    rw [hbot, Submodule.mem_bot] at this
    exact this
  have hγ : (γ : Matrix (Fin I.n) (Fin I.n) I.E) = 1 :=
    sub_eq_zero.1 (Matrix.toLin'.map_eq_zero_iff.1 hz)
  rw [hγ] at h2 h3
  refine Prod.ext (funext fun v => Subtype.ext (Units.ext ?_)) (Subtype.ext (Units.ext ?_))
  · have := h2 v
    rw [Matrix.map_one _ (map_zero _) (map_one _), Matrix.mul_one,
      Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det _).1 (I.P_unit v))] at this
    exact this
  · rw [Matrix.map_one _ (map_zero _) (map_one _)] at h3
    exact h3

theorem near_lowers_steps : ∀ (I : AutInst) (x : I.GA) (de : ℝ), 0 < de → de < 1 / 4 → (∀ (γ : GL (Fin I.n) I.E) (a : I.GA), γ ∈ Formalism.UG.UJ (starRingEnd I.E) I.J → (∀ v, uMat (a.1 v) = (I.P v)⁻¹ * (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (I.φ v) * I.P v) → I.fmat a.2 = (γ : Matrix (Fin I.n) (Fin I.n) I.E).map (Formalism.UG.inclE (F := I.F) (Af I.F)) → a ∈ nearSet I x de → ∀ t : ℝ, 0 < t → (stepLe I x t).map ((Matrix.toLin' ((γ : Matrix (Fin I.n) (Fin I.n) I.E) - 1)).restrictScalars (𝓞 I.E)) ≤ stepLe I x (de * t)) ∧ (1 / 2 ≤ least I x → nearSet I x de = {1}) :=
  fun I x de h0 h1 => ⟨lowers I x de h0, nearSet_eq I x de h0 h1⟩

end GlobalTheory.NearLower
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSkewIntegerNormCoprimePrime
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.SkewUnit

theorem exists_sub_notMem {R : Type} [CommRing R] [IsDedekindDomain R] (σ : R →+* R)
    (hσ : ∀ x, σ (σ x) = x) {p : R} (hp : p ≠ 0) (hσp : σ p = p)
    (h : ∀ P : Ideal R, P.IsMaximal → ∃ θ, θ - σ θ ∉ P) :
    ∃ θ, ∀ P : Ideal R, P.IsMaximal → p ∈ P → θ - σ θ ∉ P := by
  classical
  have hfin : {P : Ideal R | P.IsMaximal ∧ p ∈ P}.Finite := by
    have h1 := (Ideal.finite_factors (I := Ideal.span {p}) (by simpa using hp)).image
      (fun v => v.asIdeal)
    refine h1.subset ?_
    rintro P ⟨hP, hpP⟩
    have hne : P ≠ ⊥ := fun h0 => hp (by simpa [h0] using hpP)
    exact ⟨⟨P, hP.isPrime, hne⟩, by
      simpa [Ideal.dvd_span_singleton] using hpP, rfl⟩
  have : Finite {P : Ideal R // P.IsMaximal ∧ p ∈ P} := hfin.to_subtype
  let x : Ideal R → R := fun P => Classical.epsilon (fun θ => θ - σ θ ∉ P)
  obtain ⟨r, hr⟩ := Ideal.exists_forall_sub_mem_ideal
    (ι := {P : Ideal R // P.IsMaximal ∧ p ∈ P}) (I := fun P => P.1)
    (fun P Q hPQ => by
      have := P.2.1
      have := Q.2.1
      exact Ideal.isCoprime_iff_sup_eq.2
        (Ideal.IsMaximal.coprime_of_ne P.2.1 Q.2.1 (fun e => hPQ (Subtype.ext e))))
    (fun P => x P.1)
  refine ⟨r, fun P hP hpP hmem => ?_⟩
  have hsurj : Function.Surjective σ := fun y => ⟨σ y, hσ y⟩
  have := hP
  have hQ : (P.comap σ).IsMaximal := Ideal.comap_isMaximal_of_surjective σ hsurj
  have hpQ : p ∈ P.comap σ := by rw [Ideal.mem_comap, hσp]; exact hpP
  have hx : x (P.comap σ) = x P := by
    have : (fun θ => θ - σ θ ∉ P.comap σ) = (fun θ => θ - σ θ ∉ P) := by
      funext θ
      rw [Ideal.mem_comap, map_sub, hσ, ← neg_sub, Ideal.neg_mem_iff]
    simp only [x, this]
  have h1 : r - x P ∈ P := hr ⟨P, hP, hpP⟩
  have h2 : r - x (P.comap σ) ∈ P.comap σ := hr ⟨_, hQ, hpQ⟩
  rw [hx, Ideal.mem_comap, map_sub] at h2
  have h3 : x P - σ (x P) ∉ P := Classical.epsilon_spec (h P hP)
  apply h3
  have : x P - σ (x P) = (r - σ r) - (r - x P) + (σ r - σ (x P)) := by ring
  rw [this]
  exact add_mem (sub_mem hmem h1) h2

theorem prod_norm_sq {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {ι : Type} [Fintype ι]
    (φ : ι → E →+* ℂ) (hφ : Function.Bijective (fun v => InfinitePlace.mk (φ v))) (δ : 𝓞 E) :
    ∏ v, ‖φ v (δ : E)‖ ^ 2 = ((Algebra.norm ℤ δ).natAbs : ℝ) := by
  have h1 := InfinitePlace.prod_eq_abs_norm (δ : E)
  rw [← hφ.prod_comp (fun w => w (δ : E) ^ w.mult)] at h1
  simp only [IsTotallyComplex.mult_eq, InfinitePlace.apply] at h1
  rw [h1, ← Algebra.coe_norm_int, Nat.cast_natAbs]
  push_cast
  rfl

theorem exists_skew_norm_coprime : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ (ι : Type) [Fintype ι] (φ : ι → E →+* ℂ), Function.Bijective (fun v => InfinitePlace.mk (φ v)) → ∀ p : ℕ, p.Prime → ∃ (δ : 𝓞 E) (N : ℕ), star (δ : E) = -(δ : E) ∧ ¬ p ∣ N ∧ ∏ v, ‖φ v (δ : E)‖ ^ 2 = N := by
  intro E _ _ _ hE ι _ φ hφ p hp
  have := hE.1
  let σ : 𝓞 E →+* 𝓞 E := RingOfIntegers.mapRingHom (starRingEnd E)
  have hσ : ∀ x, ((σ x : 𝓞 E) : E) = star (x : E) := fun x => rfl
  have hσσ : ∀ x, σ (σ x) = x := fun x => RingOfIntegers.ext (by rw [hσ, hσ, star_star])
  obtain ⟨θ, hθ⟩ := exists_sub_notMem σ hσσ (p := (p : 𝓞 E)) (by exact_mod_cast hp.ne_zero)
    (map_natCast σ p) (fun P hP => by
      obtain ⟨θ, t, ht, hm⟩ := hE.2.2 P hP
      have : σ θ = t := RingOfIntegers.ext (by rw [hσ]; exact ht.symm)
      exact ⟨θ, by rwa [this]⟩)
  refine ⟨θ - σ θ, (Algebra.norm ℤ (θ - σ θ)).natAbs, ?_, ?_, prod_norm_sq φ hφ _⟩
  · rw [← hσ, map_sub σ, hσσ, ← neg_sub θ]
    exact map_neg (algebraMap (𝓞 E) E) _
  · intro hd
    rw [← Ideal.absNorm_span_singleton] at hd
    obtain ⟨P, hP, hu, hdv⟩ := Ideal.exists_isMaximal_dvd_of_dvd_absNorm
      (Nat.prime_iff_prime_int.1 hp) _ (Int.natCast_dvd_natCast.2 hd)
    refine hθ P hP ?_ (Ideal.dvd_span_singleton.1 hdv)
    have : (p : ℤ) ∈ Ideal.under ℤ P := hu ▸ Ideal.mem_span_singleton_self _
    simpa [Ideal.mem_comap] using this

end GlobalTheory.RadCov.SkewUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TendstoVolumeSublevelDivPowStatement
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tendsto_volume_sqrt_sublevel_div_pow_eq_volume_ball : ∀ (d : ℕ) (N : (Fin d → ℝ) → ℝ), ContinuousAt N 0 → N 0 = 0 → (∀ x, ∑ i, x i ^ 2 ≤ N x) → (∀ x, N x ≤ ∑ i, x i ^ 2 + N x ^ 2 / 4) → Filter.Tendsto (fun r : ℝ => volume {x : Fin d → ℝ | Real.sqrt (N x) ≤ r} / ENNReal.ofReal (r ^ d)) (nhdsWithin 0 (Set.Ioi 0)) (nhds (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin d)) 1))) := by
  first | exact @GlobalTheory.tendsto_volume_sublevel_div_pow | exact GlobalTheory.tendsto_volume_sublevel_div_pow | (intros; apply GlobalTheory.tendsto_volume_sublevel_div_pow <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.TorusNormaliserBesselStatement
section
open BranchingSupport GlobalTheory.CellAmp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.torus_normaliser_bessel : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (c : ℂ) (μW μN μG νq : Measure (Mt k r)) (t : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ), t ∈ GG k r → (∀ n, n ∈ Nset k r ↔ t * n * t⁻¹ ∈ Nset k r) → (∀ h ∈ UWset k r z, t * h = h * t) → (∀ n ∈ Nset k r, psi k r z cStd n = psi k r z c (t * n * t⁻¹)) → SideG k r z π u μW μN μG νq → SideG k r z π u μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) μG (νq.map fun x => fun i j => (t⁻¹ * Matrix.of x) i j) ∧ ∀ (R : Rep k r), Formalism.MainNotions.S.IsURepOn (GG k r) R.σ → (∀ B : R.H → Wp, PI.BesselMapUniq.IsBesselMapSm (k := k) (r := r) z (psi k r z c) R.σ π B ↔ IsBes R z π (fun v => B (R.σ t v))) ∧ ∀ l₁ : R.H → Wp, IsBeL R z π μW (μN.map fun x => fun i j => (t⁻¹ * Matrix.of x * t) i j) l₁ → ∀ x ∈ R.sm, ∀ v ∈ R.TK, Formalism.FourierDecayAlt.ThreeDimData.be z c π R.σ μW μN x v = (innerSL ℂ (l₁ (R.σ t⁻¹ v))).smulRight (l₁ (R.σ t⁻¹ x)) := by
  first | exact @GlobalTheory.BesselMove.bessel_move | exact GlobalTheory.BesselMove.bessel_move | (intros; apply GlobalTheory.BesselMove.bessel_move <;> assumption)
end

