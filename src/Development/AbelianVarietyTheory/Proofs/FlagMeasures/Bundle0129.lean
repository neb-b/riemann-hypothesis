module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0115
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBounds
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Formalism.RealPlaceAnalysis.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0008
public import Formalism.LocalToGlobal.HermitianForms.Bundle0002
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0006

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticeInfIsotropicEqSumFractionalIdealSmul
section
noncomputable section

open NumberField

namespace GlobalTheory.RowLatAssembly

open Formalism.MainNotions.S

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : Formalism.BasicNotions.HSpace E} {r : ℕ} {T : E}

lemma Xa_le_X (F : FlagG S r T) (j : ℕ) : F.Xa j ≤ F.X := by
  unfold FlagG.Xa FlagG.X
  exact Submodule.span_mono (Set.image_subset_range _ _)

lemma X_eq_Xa (F : FlagG S r T) : F.X = F.Xa r := by
  unfold FlagG.Xa FlagG.X
  congr 1
  ext v
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨i, i.isLt, rfl⟩
  · rintro ⟨i, -, rfl⟩
    exact ⟨i, rfl⟩

lemma e_mem (F : FlagG S r T) (a : Fin r) : F.e a ∈ F.Xa (a.val + 1) := by
  unfold FlagG.Xa
  exact Submodule.subset_span ⟨a, Nat.lt_succ_self _, rfl⟩

private lemma coefX_linearCombination_eq (F : FlagG S r T) (l : Fin r →₀ E) (a : Fin r) :
    F.coefX (Finsupp.linearCombination E F.e l) a = l a := by
  have hmem : Finsupp.linearCombination E F.e l ∈ Submodule.span E (Set.range F.e) := by
    rw [← Finsupp.range_linearCombination]
    exact LinearMap.mem_range_self _ l
  unfold FlagG.coefX
  rw [dite_eq_left hmem, F.e_indep.repr_eq (l := l) rfl]

private lemma exists_linearCombination_eq_of_mem_flagX (F : FlagG S r T) {y : S.V} (hy : y ∈ F.X) :
    ∃ l : Fin r →₀ E, Finsupp.linearCombination E F.e l = y := by
  unfold FlagG.X at hy
  rw [← Finsupp.range_linearCombination] at hy
  exact LinearMap.mem_range.mp hy

lemma coefX_add (F : FlagG S r T) (a : Fin r) {x y : S.V} (hx : x ∈ F.X) (hy : y ∈ F.X) :
    F.coefX (x + y) a = F.coefX x a + F.coefX y a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  obtain ⟨m, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hy
  rw [← map_add (f := _), coefX_linearCombination_eq, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.add_apply]

lemma coefX_smul (F : FlagG S r T) (a : Fin r) (c : E) {x : S.V} (hx : x ∈ F.X) :
    F.coefX (c • x) a = c * F.coefX x a := by
  obtain ⟨l, rfl⟩ := exists_linearCombination_eq_of_mem_flagX F hx
  rw [← map_smul, coefX_linearCombination_eq, coefX_linearCombination_eq, Finsupp.smul_apply, smul_eq_mul]

lemma coefX_e (F : FlagG S r T) (i a : Fin r) :
    F.coefX (F.e i) a = if i = a then 1 else 0 := by
  have h : F.e i = Finsupp.linearCombination E F.e (Finsupp.single i 1) := by simp
  rw [h, coefX_linearCombination_eq, Finsupp.single_apply]

lemma mem_Xa_of_coefX_eq_zero (F : FlagG S r T) (a : Fin r) {y : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (h0 : F.coefX y a = 0) : y ∈ F.Xa a.val := by
  unfold FlagG.Xa at hy ⊢
  obtain ⟨l, hl, rfl⟩ := (Finsupp.mem_span_image_iff_linearCombination (R := E)).mp hy
  rw [coefX_linearCombination_eq] at h0
  refine (Finsupp.mem_span_image_iff_linearCombination (R := E)).mpr ⟨l, ?_, rfl⟩
  rw [Finsupp.mem_supported'] at hl ⊢
  intro i hi
  simp only [Set.mem_ofPred_eq, not_lt] at hi
  rcases lt_or_eq_of_le hi with h | h
  · exact hl i (by simp only [Set.mem_ofPred_eq]; omega)
  · have hia : i = a := Fin.ext h.symm
    rw [hia]
    exact h0

lemma sub_smul_mem (F : FlagG S r T) (a : Fin r) {y w : S.V} (hy : y ∈ F.Xa (a.val + 1))
    (hw : w ∈ F.Xa (a.val + 1)) (hw1 : F.coefX w a = 1) :
    y - F.coefX y a • w ∈ F.Xa a.val := by
  have hyX := Xa_le_X F _ hy
  have hwX := Xa_le_X F _ hw
  apply mem_Xa_of_coefX_eq_zero F a (Submodule.sub_mem _ hy (Submodule.smul_mem _ _ hw))
  rw [sub_eq_add_neg, ← neg_smul, coefX_add F a hyX (Submodule.smul_mem _ _ hwX),
    coefX_smul F a _ hwX, hw1]
  ring

lemma exists_section (F : FlagG S r T) (Λ : Submodule (𝓞 E) S.V)
    (J : FractionalIdeal (nonZeroDivisors (𝓞 E)) E) (hJ : J ≠ 0) (a : Fin r)
    (h3 : ∀ t : E, t ∈ J → ∃ x ∈ Λ, x ∈ F.Xa (a.val + 1) ∧ F.coefX x a = t) :
    ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = 1 ∧ ∀ t ∈ J, t • w ∈ Λ := by

  have key : ∀ s ∈ J * J⁻¹, ∃ w ∈ F.Xa (a.val + 1), F.coefX w a = s ∧ ∀ t ∈ J, t • w ∈ Λ := by
    intro s hs
    refine FractionalIdeal.mul_induction_on hs ?_ ?_
    · intro i hi j hj
      obtain ⟨x, hxΛ, hxX, hxc⟩ := h3 i hi
      refine ⟨j • x, Submodule.smul_mem _ j hxX, ?_, ?_⟩
      · rw [coefX_smul F a j (Xa_le_X F _ hxX), hxc, mul_comm]
      · intro t ht
        have htj : t * j ∈ J * J⁻¹ := FractionalIdeal.mul_mem_mul ht hj
        rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff] at htj
        obtain ⟨o, ho⟩ := htj
        rw [smul_smul, ← ho, algebraMap_smul]
        exact Λ.smul_mem o hxΛ
    · rintro s₁ s₂ ⟨w₁, hw₁, hc₁, hΛ₁⟩ ⟨w₂, hw₂, hc₂, hΛ₂⟩
      refine ⟨w₁ + w₂, Submodule.add_mem _ hw₁ hw₂, ?_, ?_⟩
      · rw [coefX_add F a (Xa_le_X F _ hw₁) (Xa_le_X F _ hw₂), hc₁, hc₂]
      · intro t ht
        rw [smul_add]
        exact Λ.add_mem (hΛ₁ t ht) (hΛ₂ t ht)
  have h1 : (1 : E) ∈ J * J⁻¹ := by
    rw [mul_inv_cancel₀ hJ, FractionalIdeal.mem_one_iff]
    exact ⟨1, map_one _⟩
  exact key 1 h1

theorem xLam_eq_span : ∀ {E : Type} [Field E] [NumberField E] [StarRing E] (S : Formalism.BasicNotions.HSpace E) (r : ℕ) (T : E) (G : Formalism.MainNotions.S.Lat.LFlag S r T) (Λ : Submodule (𝓞 E) S.V) (J : Fin r → FractionalIdeal (nonZeroDivisors (𝓞 E)) E), (∀ a, J a ≠ 0) → (∀ (a : Fin r) (x : S.V), x ∈ Λ → x ∈ G.fl.Xa (a.val + 1) → G.fl.coefX x a ∈ J a) → (∀ (a : Fin r) (t : E), t ∈ J a → ∃ x ∈ Λ, x ∈ G.fl.Xa (a.val + 1) ∧ G.fl.coefX x a = t) → ∃ e' : Fin r → S.V, (∀ a, e' a - G.fl.e a ∈ G.fl.Xa a.val) ∧ Formalism.MainNotions.S.Lat.XLam Λ G = Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
  intro E _ _ _ S r T G Λ J hJ h2 h3
  have hsec : ∀ a : Fin r, ∃ w ∈ G.fl.Xa (a.val + 1), G.fl.coefX w a = 1 ∧ ∀ t ∈ J a, t • w ∈ Λ :=
    fun a => exists_section G.fl Λ (J a) (hJ a) a (h3 a)
  choose e' he'X he'c he'Λ using hsec
  refine ⟨e', fun a => ?_, ?_⟩
  · have hea : G.fl.coefX (G.fl.e a) a = 1 := by rw [coefX_e, if_pos rfl]
    have h := sub_smul_mem G.fl a (he'X a) (e_mem G.fl a) hea
    rwa [he'c a, one_smul] at h
  · apply le_antisymm
    ·
      have step : ∀ j : ℕ, j ≤ r → ∀ v ∈ Λ, v ∈ G.fl.Xa j →
          v ∈ Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} := by
        intro j
        induction j with
        | zero =>
          intro _ v _ hv
          have hv0 : v = 0 := by
            unfold Formalism.MainNotions.S.FlagG.Xa at hv
            simpa using hv
          rw [hv0]
          exact Submodule.zero_mem _
        | succ j ih =>
          intro hj v hvΛ hv
          obtain ⟨a, rfl⟩ : ∃ a : Fin r, a.val = j := ⟨⟨j, hj⟩, rfl⟩
          have hc : G.fl.coefX v a ∈ J a := h2 a v hvΛ hv
          have hrest : v - G.fl.coefX v a • e' a ∈ G.fl.Xa a.val :=
            sub_smul_mem G.fl a hv (he'X a) (he'c a)
          have hrestΛ : v - G.fl.coefX v a • e' a ∈ Λ := Λ.sub_mem hvΛ (he'Λ a _ hc)
          have hlow := ih (Nat.le_of_succ_le hj) _ hrestΛ hrest
          have htop : G.fl.coefX v a • e' a ∈
              Submodule.span (𝓞 E) {y | ∃ (a : Fin r) (x : E), x ∈ J a ∧ y = x • e' a} :=
            Submodule.subset_span ⟨a, _, hc, rfl⟩
          have hsum := Submodule.add_mem _ hlow htop
          rwa [sub_add_cancel] at hsum
      intro v hv
      obtain ⟨hvΛ, hvX⟩ : v ∈ Λ ∧ v ∈ G.fl.X := hv
      rw [X_eq_Xa] at hvX
      exact step r le_rfl v hvΛ hvX
    · rw [Submodule.span_le]
      rintro y ⟨a, x, hx, rfl⟩
      show x • e' a ∈ Λ ⊓ Formalism.MainNotions.S.Lat.toO S (Formalism.MainNotions.S.Lat.Xsp G)
      exact Submodule.mem_inf.mpr ⟨he'Λ a x hx, (G.fl.X).smul_mem x (Xa_le_X G.fl _ (he'X a))⟩

end GlobalTheory.RowLatAssembly
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LatticePairVolumeBoundsStatement
section
open Formalism.HN Formalism.HermitianLatticesTheory Matrix NumberField Finset
open GlobalTheory.HomCover in
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lattice_pair_volume_bounds :
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] [_root_.NumberField.IsTotallyComplex K] (a b : ℕ)
      (X : InfinitePlace K → Matrix (Fin a) (Fin a) ℂ)
      (X' : InfinitePlace K → Matrix (Fin b) (Fin b) ℂ)
      (A : Submodule (𝓞 K) (Fin a → K)) (B : Submodule (𝓞 K) (Fin b → K)) (lo hi : ℝ),
      (∀ w, IsUnit (X w).det) → (∀ w, IsUnit (X' w).det) → A.FG → B.FG →
      Submodule.span K (A : Set (Fin a → K)) = ⊤ →
      Submodule.span K (B : Set (Fin b → K)) = ⊤ → 0 < lo → 0 < hi →
      (∀ N, N ≤ A → N ≠ ⊥ → lo ≤ Formalism.HN.size (Pi.basisFun K (Fin a)) X N) →
      Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B ≤ hi →
      ∀ T : InfinitePlace K → Matrix (Fin b) (Fin a) ℂ,
        ∃ φ : Matrix (Fin b) (Fin a) K, (∀ y ∈ A, φ *ᵥ y ∈ B) ∧
          Real.sqrt (∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * φ.map w.embedding * X w) i j‖ ^ 2) ≤
            (a : ℝ) * b * Real.sqrt (Formalism.HN.nPl K) *
              |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) * hi / (2 * lo) := by
  intro K _ _ _ _ a b X X' A B lo hi hX hX' hA hB hAs hBs hlo hhi hlow hup T
  set rd : ℝ := |(discr K : ℝ)| ^ ((1 : ℝ) / (2 * (Formalism.HN.nPl K : ℝ))) with hrd
  have hrd0 : 0 < rd := Real.rpow_pos_of_pos (abs_pos.2 (by exact_mod_cast discr_ne_zero K)) _
  have hn : (Fintype.card (InfinitePlace K) : ℝ) = (Formalism.HN.nPl K : ℝ) := rfl
  have hn0 : (0 : ℝ) < Formalism.HN.nPl K := by
    rw [← hn]; exact_mod_cast Fintype.card_pos
  have hs0 : 0 < Real.sqrt (Formalism.HN.nPl K) := Real.sqrt_pos.2 hn0
  have hss : Real.sqrt (Formalism.HN.nPl K) ^ 2 = Formalism.HN.nPl K := Real.sq_sqrt hn0.le
  obtain ⟨y, hy, hle⟩ := _root_.GlobalTheory.TraceCover.cover K (Fin b × Fin a) (Fin b × Fin a) (homLat A B)
    (fun w => frameEquiv (X' w) (X w) (hX' w) (hX w)) (Real.sqrt (Formalism.HN.nPl K) * (lo / (rd * hi)))
    (homLat_fg A B hA hB hAs) (homLat_span A B hA hBs) (by positivity)
    (fun f c hf hint hc => by
      have hc' : ∀ w, c w = fun p => ((X w)⁻¹ * ((toMat f)ᵀ).map w.embedding * X' w) p.2 p.1 :=
        fun w => by
          have h := dual_coord (X' w) (X w) (hX' w) (hX w) (fun i => w.embedding (f i)) (c w) (hc w)
          have e : (toMat fun i => w.embedding (f i))ᵀ = ((toMat f)ᵀ).map w.embedding := by
            ext i j; rfl
          rw [e] at h
          exact h
      have h1 : ∃ y ∈ B, (toMat f)ᵀ *ᵥ y ≠ 0 := by
        by_contra hcon
        push Not at hcon
        have : Matrix.toLin' (toMat f)ᵀ = 0 := LinearMap.ext_on hBs fun x hx => hcon x hx
        have h0 : (toMat f)ᵀ = 0 := by simpa using this
        apply hf
        funext p
        exact congrFun (congrFun h0 p.2) p.1
      have h2 := GlobalTheory.TraceDualHom.different_smul_mem_of_trace_integral K a b A B hA hB hAs hBs
        (Matrix.toLin' (toMat f)ᵀ) (fun S hS => by
          obtain ⟨φ, rfl⟩ := Matrix.toLin'.surjective S
          obtain ⟨m, hm⟩ := hint (fun p => φ p.1 p.2) hS
          refine ⟨m, ?_⟩
          rw [← hm, ← Matrix.toLin'_mul, Matrix.trace_toLin'_eq, dot_eq_trace, toMat_entries])
      have h3 : (Formalism.HN.nPl K : ℝ) * (lo / (rd * hi)) ^ 2 ≤
          ∑ w, ∑ i, ∑ j, ‖((X w)⁻¹ * ((toMat f)ᵀ).map w.embedding * X' w) i j‖ ^ 2 := by
        let ψ := (toMat f)ᵀ
        let φ := Matrix.toLin' ψ
        let A' := B.map (φ.restrictScalars (𝓞 K))
        have hA'fg : A'.FG := hB.map _
        obtain ⟨y, hyB, hy⟩ := h1
        have hA'0 : A' ≠ ⊥ := by
          intro h
          have hy' : φ y ∈ A' := ⟨y, hyB, rfl⟩
          rw [h] at hy'
          exact hy hy'
        have hB0 : B ≠ ⊥ := by
          intro h
          apply hA'0
          simp [A', h]
        have hd : differentIdeal ℤ (𝓞 K) ≠ ⊥ := differentIdeal_ne_bot
        have hleast : lo / rd ≤ Formalism.HN.leastSize (Pi.basisFun K (Fin a)) X A' := by
          refine le_csInf ⟨_, A', le_rfl, hA'0, rfl⟩ ?_
          rintro _ ⟨N, hN, hN0, rfl⟩
          have hNfg : N.FG := Submodule.FG.of_le hA'fg hN
          have hle : differentIdeal ℤ (𝓞 K) • N ≤ A := by
            refine Submodule.smul_le.2 fun δ hδ v hv => ?_
            obtain ⟨z, hz, rfl⟩ := hN hv
            exact h2 δ hδ z hz
          have hspan := Formalism.HN.DualPolygon.twist_span_smul N _ hd
          have hne : differentIdeal ℤ (𝓞 K) • N ≠ ⊥ := by
            intro h
            rw [h] at hspan
            apply hN0
            rw [eq_bot_iff]
            intro v hv
            have hv' : v ∈ Submodule.span K (N : Set (Fin a → K)) :=
              Submodule.subset_span hv
            rw [← hspan] at hv'
            simpa using hv'
          have hsize : Formalism.HN.size (Pi.basisFun K (Fin a)) X
              (differentIdeal ℤ (𝓞 K) • N) =
                Formalism.HN.size (Pi.basisFun K (Fin a)) X N * rd := by
            have hrk : Formalism.HN.rkK (differentIdeal ℤ (𝓞 K) • N) =
                Formalism.HN.rkK N := by
              unfold Formalism.HN.rkK
              rw [hspan]
            have hnorm : (Ideal.absNorm (differentIdeal ℤ (𝓞 K)) : ℝ) =
                |(discr K : ℝ)| := by
              rw [NumberField.absNorm_differentIdeal K (𝓞 K), Nat.cast_natAbs, Int.cast_abs]
            have hj : (Formalism.HN.rkK N : ℝ) ≠ 0 := by
              exact_mod_cast (Formalism.LFunctionChainParameters.slopeLatticeData.rkK_pos hN0).ne'
            unfold Formalism.HN.size rd
            rw [Formalism.LFunctionChainParameters.slopeLatticeData.ht_ideal _ X hX hNfg hd,
              hrk, hnorm, Real.mul_rpow
                (Formalism.LFunctionChainParameters.slopeLatticeData.ht_pos _ X hX hNfg).le
                (pow_nonneg (abs_nonneg (discr K : ℝ)) (Formalism.HN.rkK N)),
              ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _)]
            congr 2
            field_simp [hn0.ne', hj]
          rw [div_le_iff₀ hrd0, ← hsize]
          exact hlow _ hle hne
        have hLpos : 0 < Formalism.HN.largestSize (Pi.basisFun K (Fin b)) X' B := by
          rw [(Formalism.HN.sizeMu K _ _ (Pi.basisFun K (Fin b)) X' hX' B hB hB0).2.2.2.2.1]
          exact Real.exp_pos _
        let opNorm := fun w => Formalism.HN.opNormAt (Pi.basisFun K (Fin b)) X'
          (Pi.basisFun K (Fin a)) X w φ
        have hgeom : lo / (rd * hi) ≤
            (∏ w, opNorm w) ^ ((1 : ℝ) / (Formalism.HN.nPl K : ℝ)) := by
          refine le_trans ?_ (Formalism.HN.sizeIneq K _ _ _ _
            (Pi.basisFun K (Fin b)) X' (Pi.basisFun K (Fin a)) X hX' hX φ B A'
            hB hA'fg le_rfl hA'0)
          rw [← div_div]
          exact div_le_div₀ ((div_pos hlo hrd0).le.trans hleast) hleast hLpos hup
        calc
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (pow_le_pow_left₀ (by positivity) hgeom 2) (Nat.cast_nonneg _)
          _ ≤ _ := _root_.GlobalTheory.DualBound.card_mul_geom_sq_le opNorm
            (fun w => norm_nonneg _)
          _ ≤ _ := by
            refine Finset.sum_le_sum fun w _ => ?_
            have hmatrix : LinearMap.toMatrix (Pi.basisFun K (Fin b)) (Pi.basisFun K (Fin a))
                φ = ψ := by ext i j; simp [φ]
            unfold opNorm Formalism.HN.opNormAt
            rw [hmatrix]
            exact _root_.GlobalTheory.DualBound.opNorm_sq_le_hs _
      rw [mul_pow, hss]
      refine h3.trans (le_of_eq ?_)
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [hc' w, Fintype.sum_prod_type, Finset.sum_comm])
    (fun w p => T w p.1 p.2)
  refine ⟨toMat y, hy, ?_⟩
  have e1 : ∑ w, ∑ i, ∑ j, ‖(T w - (X' w)⁻¹ * (toMat y).map w.embedding * X w) i j‖ ^ 2
      = ∑ w, ∑ p : Fin b × Fin a, ‖T w p.1 p.2 -
        frameEquiv (X' w) (X w) (hX' w) (hX w) (fun j => w.embedding (y j)) p‖ ^ 2 := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fintype.sum_prod_type]
    rfl
  rw [e1]
  refine hle.trans (le_of_eq ?_)
  rw [hn, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  push_cast
  set r := Real.sqrt (Formalism.HN.nPl K)
  rw [← hss]
  field_simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalFrameIdempotentFactorCases
section
open Formalism.BasicNotions Formalism.UG Formalism.L2.Forms NumberField IsDedekindDomain Matrix GlobalTheory.St.G
open scoped TensorProduct

namespace GlobalTheory.St.G

section

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

theorem not_forall_loc_eq_natCast_smul (v : HeightOneSpectrum (𝓞 F))
    (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F)
    (hdiag : ∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a))
    (g : ℕ) (hg : (g : 𝓞 F) ∈ v.asIdeal) (L : Submodule (𝓞 E) (Fin n → E)) (hL : IsLat L) (hn : 0 < n) :
    ¬ ∀ y ∈ loc v L, ∃ z ∈ loc v L, y = (g : E ⊗[F] v.adicCompletion F) • z := by
  classical
  intro h
  have hs := split_integral_local F E v sp hdiag
  have hint : ∀ r ∈ intV E v, (sp r).1 ∈ v.adicCompletionIntegers F := fun r hr => ((hs r).1 hr).1
  have hOE : ∀ c : 𝓞 E, inclE (F := F) (v.adicCompletion F) (c : E) ∈ intV E v := by
    intro c
    have hc : ((c : E) ⊗ₜ[F] (1 : v.adicCompletion F)) ∈ PI.SplitIntLoc.tensInt (v.adicCompletion F)
        (PI.SplitIntLoc.intOE E) (v.adicCompletionIntegers F).toSubring :=
      Subring.subset_closure (Or.inl ⟨⟨(c : E), c, rfl⟩, rfl⟩)
    exact hc
  have hv : Valued.v ((g : v.adicCompletion F)) < 1 := by
    have h1 : v.intValuation (g : 𝓞 F) < 1 := (v.intValuation_lt_one_iff_mem _).2 hg
    have h2 : ((g : v.adicCompletion F)) = algebraMap (𝓞 F) (v.adicCompletion F) (g : 𝓞 F) :=
      (map_natCast _ g).symm
    rw [h2]
    refine lt_of_eq_of_lt (v.valuedAdicCompletion_eq_valuation (g : 𝓞 F)) ?_
    rw [v.valuation_of_algebraMap]
    exact h1
  obtain ⟨hfin, hspan⟩ := hL
  obtain ⟨G, hG⟩ := Module.Finite.iff_fg.1 hfin
  have hgen : ∀ x ∈ L, (fun i => inclE (F := F) (v.adicCompletion F) (x i)) ∈ loc v L :=
    fun x hx => Submodule.subset_span ⟨x, hx, rfl⟩
  set M : Submodule (v.adicCompletionIntegers F) (v.adicCompletion F) := Submodule.span _
    (Set.range fun p : G × Fin n => (sp (inclE (F := F) (v.adicCompletion F) ((p.1 : Fin n → E) p.2))).1) with hMdef
  have hMx : ∀ x ∈ L, ∀ i, (sp (inclE (F := F) (v.adicCompletion F) (x i))).1 ∈ M := by
    intro x hx i
    rw [← hG] at hx
    induction hx using Submodule.span_induction with
    | mem s hsG => exact Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
    | zero => simp
    | add a b _ _ ha hb => simpa using M.add_mem ha hb
    | smul c a _ ha =>
      have hc := hint _ (hOE c)
      have e : (sp (inclE (F := F) (v.adicCompletion F) ((c • a) i))).1 =
          (⟨_, hc⟩ : v.adicCompletionIntegers F) • (sp (inclE (F := F) (v.adicCompletion F) (a i))).1 := by
        rw [Pi.smul_apply, Algebra.smul_def, map_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ ha
  have hM : ∀ y ∈ loc v L, ∀ i, (sp (y i)).1 ∈ M := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨x, hxL, rfl⟩ := hx
      exact hMx x hxL
    | zero => intro i; simp
    | add a b _ _ ha hb => intro i; simpa using M.add_mem (ha i) (hb i)
    | smul r a _ ha =>
      intro i
      have hr := hint _ r.2
      have e : (sp ((r • a) i)).1 = (⟨_, hr⟩ : v.adicCompletionIntegers F) • (sp (a i)).1 := by
        rw [Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_mul, Prod.fst_mul, Algebra.smul_def]
        rfl
      rw [e]
      exact M.smul_mem _ (ha i)
  have hle : M ≤ Ideal.span {((g : v.adicCompletionIntegers F))} • M := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨⟨s, hsG⟩, i⟩, rfl⟩
    have hsL : s ∈ L := hG ▸ Submodule.subset_span hsG
    obtain ⟨z, hz, hyz⟩ := h _ (hgen s hsL)
    have e : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 =
        (g : v.adicCompletionIntegers F) • (sp (z i)).1 := by
      have hi : inclE (F := F) (v.adicCompletion F) (s i) = ((g : E ⊗[F] v.adicCompletion F) • z) i :=
        congrFun hyz i
      rw [hi, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Prod.fst_mul, Algebra.smul_def]
      simp
    change (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈
      ((Ideal.span {((g : v.adicCompletionIntegers F))} • M : Submodule _ _) : Set (v.adicCompletion F))
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem_smul (Ideal.mem_span_singleton_self _) (hM z hz i)
  have hjac : Ideal.span {((g : v.adicCompletionIntegers F))} ≤ Ideal.jacobson ⊥ := by
    rw [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top, Ideal.span_le, Set.singleton_subset_iff,
      SetLike.mem_coe, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hunit
    obtain ⟨b, hb⟩ := hunit.exists_left_inv
    have hb' : (b : v.adicCompletion F) * (g : v.adicCompletion F) = 1 := by
      have := congrArg Subtype.val hb
      simpa using this
    have hbv : Valued.v (b : v.adicCompletion F) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) (K := F) (v := v)).1 b.2
    have hlt : Valued.v ((b : v.adicCompletion F) * (g : v.adicCompletion F)) < 1 := by
      rw [map_mul]
      exact (mul_le_of_le_one_left' hbv).trans_lt hv
    rw [hb', map_one] at hlt
    exact lt_irrefl _ hlt
  have hne : ∃ s ∈ G, ∃ i, s i ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_and, ne_eq, not_not] at hcon
    have hL0 : L = ⊥ := by
      rw [← hG, Submodule.span_eq_bot]
      intro s hs
      funext i
      exact hcon s hs i
    have h1 : (fun _ : Fin n => (1 : E)) ∈ Submodule.span E (L : Set (Fin n → E)) := hspan ▸ Submodule.mem_top
    rw [hL0, Submodule.bot_coe, Submodule.span_zero_singleton, Submodule.mem_bot] at h1
    exact one_ne_zero (congrFun h1 ⟨0, hn⟩)
  obtain ⟨s, hsG, i, hsi⟩ := hne
  have hu : IsUnit (sp (inclE (F := F) (v.adicCompletion F) (s i))) :=
    ((isUnit_iff_ne_zero.2 hsi).map (inclE (F := F) (v.adicCompletion F))).map sp
  have ha : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ≠ 0 :=
    (hu.map (RingHom.fst (v.adicCompletion F) (v.adicCompletion F))).ne_zero
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson_bot _ M (Submodule.fg_span (Set.finite_range _)) hle hjac
  have hmem : (sp (inclE (F := F) (v.adicCompletion F) (s i))).1 ∈ M := Submodule.subset_span ⟨(⟨s, hsG⟩, i), rfl⟩
  rw [hbot, Submodule.mem_bot] at hmem
  exact ha hmem

end

theorem local_idempotent_cases :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (v : HeightOneSpectrum (𝓞 F)) (sp : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), (∀ x, sp (sigR σ (v.adicCompletion F) x) = swapR _ (sp x)) → (∀ a : v.adicCompletion F, sp ((1 : E) ⊗ₜ[F] a) = (a, a)) → ∀ (g : ℕ), (g : 𝓞 F) ∈ v.asIdeal → ∀ (L : Submodule (𝓞 E) (Fin n → E)), IsLat L → 0 < n → ∀ e : E ⊗[F] v.adicCompletion F, e * e = e → e * sigR σ (v.adicCompletion F) e = 0 → (∀ y ∈ loc v L, ∃ z ∈ loc v L, (1 - e - sigR σ (v.adicCompletion F) e) • y = (g : E ⊗[F] v.adicCompletion F) • z) → sp e = (1, 0) ∨ sp e = (0, 1) := by
  intro F E _ _ _ _ _ σ n v sp hsw hdiag g hg L hL hn e he heo hfull
  have hse : sp (sigR σ (v.adicCompletion F) e) = ((sp e).2, (sp e).1) := by
    rw [hsw]
    rfl
  have hidem : sp e * sp e = sp e := by rw [← map_mul, he]
  have horth : sp e * ((sp e).2, (sp e).1) = 0 := by rw [← hse, ← map_mul, heo, map_zero]
  have ha : (sp e).1 * (sp e).1 = (sp e).1 := congrArg Prod.fst hidem
  have hb : (sp e).2 * (sp e).2 = (sp e).2 := congrArg Prod.snd hidem
  have hab : (sp e).1 * (sp e).2 = 0 := congrArg Prod.fst horth
  have ha' : (sp e).1 = 0 ∨ (sp e).1 = 1 := by
    have h0 : (sp e).1 * ((sp e).1 - 1) = 0 := by rw [mul_sub, mul_one, ha, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  have hb' : (sp e).2 = 0 ∨ (sp e).2 = 1 := by
    have h0 : (sp e).2 * ((sp e).2 - 1) = 0 := by rw [mul_sub, mul_one, hb, sub_self]
    rcases mul_eq_zero.1 h0 with h | h
    · exact Or.inl h
    · exact Or.inr (sub_eq_zero.1 h)
  rcases ha' with ha0 | ha1 <;> rcases hb' with hb0 | hb1
  · exfalso
    have he0 : e = 0 := sp.injective (by rw [map_zero]; exact Prod.ext ha0 hb0)
    apply not_forall_loc_eq_natCast_smul v sp hdiag g hg L hL hn
    intro y hy
    obtain ⟨z, hz, hyz⟩ := hfull y hy
    refine ⟨z, hz, ?_⟩
    rw [he0, map_zero, sub_zero, sub_zero, one_smul] at hyz
    exact hyz
  · exact Or.inr (Prod.ext ha0 hb1)
  · exact Or.inl (Prod.ext ha1 hb0)
  · exfalso
    rw [ha1, hb1, one_mul] at hab
    exact one_ne_zero hab

end GlobalTheory.St.G
end

