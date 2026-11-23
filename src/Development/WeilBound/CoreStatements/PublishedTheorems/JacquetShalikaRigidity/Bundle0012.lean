module

public import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.ColumnConjugationMeasure

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.SquareIntegralBound
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace SquareIntegralBound

theorem sqle (a b : ℝ≥0∞) : a * b ≤ a ^ 2 + b ^ 2 := by
  rcases le_total a b with h | h
  · calc a * b ≤ b * b := by gcongr
      _ = b ^ 2 := (sq b).symm
      _ ≤ a ^ 2 + b ^ 2 := le_add_self
  · calc a * b ≤ a * a := by gcongr
      _ = a ^ 2 := (sq a).symm
      _ ≤ a ^ 2 + b ^ 2 := le_self_add

theorem intMul {X : Type} [MeasurableSpace X] {ν : Measure X} {F G : X → ℂ}
    (hF : AEStronglyMeasurable F ν) (hG : AEStronglyMeasurable G ν)
    (hF2 : ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν < ∞) (hG2 : ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν < ∞) :
    Integrable (fun x => F x * conj (G x)) ν := by
  refine ⟨hF.mul (Complex.continuous_conj.comp_aestronglyMeasurable hG), ?_⟩
  unfold HasFiniteIntegral
  calc ∫⁻ x, ‖F x * conj (G x)‖ₑ ∂ν ≤ ∫⁻ x, (‖F x‖ₑ ^ 2 + ‖G x‖ₑ ^ 2) ∂ν := by
        refine lintegral_mono fun x => ?_
        rw [enorm_mul]
        have : ‖conj (G x)‖ₑ = ‖G x‖ₑ := by
          rw [← ofReal_norm, ← ofReal_norm, Complex.norm_conj]
        rw [this]; exact sqle _ _
    _ = ∫⁻ x, ‖F x‖ₑ ^ 2 ∂ν + ∫⁻ x, ‖G x‖ₑ ^ 2 ∂ν := lintegral_add_left' (hF.enorm.pow_const 2) _
    _ < ∞ := ENNReal.add_lt_top.2 ⟨hF2, hG2⟩

theorem bnd (D B C1 C2 s : ℝ) (N : ℕ) (hD : 0 < D) (hB : 0 ≤ B) (hs : 2 ≤ s) (hN : s + 1 ≤ N) (T : ℝ≥0∞)
    (h1 : T ≤ ENNReal.ofReal (C1 * D ^ (-1 : ℝ))) (h2 : T ≤ ENNReal.ofReal (C2 * D ^ (-(N : ℝ)))) :
    ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * max (max C1 C2) 0 * min D D⁻¹ ^ (1 : ℝ)) := by
  set K := max (max C1 C2) 0 with hKdef
  have hK0 : 0 ≤ K := le_max_right _ _
  have hC1 : C1 ≤ K := le_trans (le_max_left _ _) (le_max_left _ _)
  have hC2 : C2 ≤ K := le_trans (le_max_right _ _) (le_max_left _ _)
  have hBs : 0 ≤ B * D ^ s := mul_nonneg hB (Real.rpow_nonneg hD.le _)
  rw [Real.rpow_one]
  rcases le_or_gt D 1 with hD1 | hD1
  · have hmin : min D D⁻¹ = D := min_eq_left (le_trans hD1 (one_le_inv₀ hD |>.mpr hD1))
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C1 * D ^ (-1 : ℝ)) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C1 * D ^ (-1 : ℝ))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-1 : ℝ) = D ^ (s - 1) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - 1) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - 1) ≤ D := by
            calc D ^ (s - 1) ≤ D ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_ge hD hD1 (by linarith)
              _ = D := Real.rpow_one D
          calc B * D ^ s * (C1 * D ^ (-1 : ℝ)) = B * C1 * (D ^ s * D ^ (-1 : ℝ)) := by ring
            _ = B * C1 * D ^ (s - 1) := by rw [e]
            _ ≤ B * K * D ^ (s - 1) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC1 hB) hP0
            _ ≤ B * K * D := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)
  · have hmin : min D D⁻¹ = D⁻¹ := min_eq_right (le_trans (inv_le_one_of_one_le₀ hD1.le) hD1.le)
    rw [hmin]
    calc ENNReal.ofReal (B * D ^ s) * T ≤ ENNReal.ofReal (B * D ^ s) * ENNReal.ofReal (C2 * D ^ (-(N : ℝ))) :=
          by gcongr
      _ = ENNReal.ofReal (B * D ^ s * (C2 * D ^ (-(N : ℝ)))) := (ENNReal.ofReal_mul hBs).symm
      _ ≤ ENNReal.ofReal (B * K * D⁻¹) := by
          apply ENNReal.ofReal_le_ofReal
          have e : D ^ s * D ^ (-(N : ℝ)) = D ^ (s - N) := by rw [← Real.rpow_add hD]; ring_nf
          have hP0 : 0 ≤ D ^ (s - N) := Real.rpow_nonneg hD.le _
          have hPD : D ^ (s - N) ≤ D⁻¹ := by
            calc D ^ (s - N) ≤ D ^ (-1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hD1.le (by linarith)
              _ = D⁻¹ := Real.rpow_neg_one D
          calc B * D ^ s * (C2 * D ^ (-(N : ℝ))) = B * C2 * (D ^ s * D ^ (-(N : ℝ))) := by ring
            _ = B * C2 * D ^ (s - N) := by rw [e]
            _ ≤ B * K * D ^ (s - N) := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC2 hB) hP0
            _ ≤ B * K * D⁻¹ := mul_le_mul_of_nonneg_left hPD (mul_nonneg hB hK0)

end SquareIntegralBound

open SquareIntegralBound in
theorem moderate_growth_of : D0 → N0 → P2 → U0 → U2 → V1 → ThetaDecaying → M0 := by
  intro hD0 hN0 hP2 hU0 hU2 hV1 hG4 E _ _ _ k μ _ hk β hβ ψ hψ S m α α' u f φ hd
  obtain ⟨β₁, hβ₁, hU0a, hU0b⟩ := hU0 E k μ hk β hβ
  obtain ⟨β', hβ', hU2'⟩ := hU2 E k μ ψ hψ (k - 1) (by omega) β₁ hβ₁
  obtain ⟨hDpos, hDmul, hDcont, hDrat, hDU, -⟩ := hD0 E k
  obtain ⟨-, -, -, -, hPchi, hGoodPre, hLu, hLmir, hLcont, hLsupp⟩ := hP2 E k ψ hψ
  obtain ⟨C, hC, hfC⟩ := hd.supp
  obtain ⟨a, ε, Cf, hε, hsq⟩ := hd.sq
  obtain ⟨Φ₀, hΦ1, -, hΦc, hΦI⟩ :=
    exists_continuous_one_zero_of_isCompact hC isClosed_empty (Set.disjoint_empty C)
  obtain ⟨-, -, hV1c⟩ := hV1 E k μ hk β hβ
  have hk1 : k - 1 < k := by omega
  have hDu : ∀ u g : GA E k, UU 0 u → Dt (u * g) = Dt g := fun u g hu => by
    rw [hDmul, hDU 0 u hu, one_mul]
  have hDr : ∀ γ (g : GA E k), Dt (ratGL E k γ * g) = Dt g := fun γ g => by
    rw [hDmul, hDrat, one_mul]
  obtain ⟨Bφ, hBφ⟩ : ∃ B, ∀ g, ‖φ g‖ ≤ B := by
    obtain ⟨B, hB⟩ := hd.dec 0
    have hne : (fun _ => (1 : E) : Fin k → E) ≠ 0 := fun h => by
      have := congrFun h ⟨0, hk⟩; simp at this
    exact ⟨B, fun g => by simpa using hB g _ hne⟩
  have hBφ0 : 0 ≤ Bφ := (norm_nonneg _).trans (hBφ 1)
  refine ⟨β', a / 2 + 1, hβ', fun z hz => ?_⟩
  set χ₁ : GA E k → ℂ := fun g => ((Dt g ^ (a / 2) : ℝ) : ℂ) with hχ₁
  set χ₂ : GA E k → ℂ := fun g => conj ((Dt g : ℂ) ^ (z - ((a / 2 : ℝ) : ℂ))) * (Φ₀ (lastRow g) : ℂ) with hχ₂
  have hχ₁c : Continuous χ₁ := Complex.continuous_ofReal.comp
    (hDcont.rpow_const fun g => Or.inl (hDpos g).ne')
  have hχ₂c : Continuous χ₂ := by
    refine (Complex.continuous_conj.comp ?_).mul (Complex.continuous_ofReal.comp (Φ₀.continuous.comp hLcont))
    exact (Complex.continuous_ofReal.comp hDcont).cpow continuous_const
      fun g => Complex.ofReal_mem_slitPlane.2 (hDpos g)
  have hχ₁u : ∀ u, UU 0 u → ∀ g, χ₁ (u * g) = χ₁ g := fun u hu g => by simp only [hχ₁, hDu u g hu]
  have hχ₁m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₁ (ratGL E k γ * g) = χ₁ g := fun γ _ g => by simp only [hχ₁, hDr]
  have hχ₂u : ∀ u, UU 0 u → ∀ g, χ₂ (u * g) = χ₂ g := fun u hu g => by simp only [hχ₂, hDu u g hu, hLu u g hu]
  have hχ₂m : ∀ γ, IsMir (k - 1) γ → ∀ g, χ₂ (ratGL E k γ * g) = χ₂ g := fun γ hγ g => by
    simp only [hχ₂, hDr, hLmir γ g (by simpa using hγ)]
  obtain ⟨hpre1, hwf, -⟩ := hPchi (k - 1) hk1 f χ₁ hd.pre hχ₁c hχ₁u hχ₁m
  obtain ⟨hpre2, hwφ, hgood2⟩ := hPchi (k - 1) hk1 φ χ₂ (hGoodPre _ _ hd.good) hχ₂c hχ₂u hχ₂m
  have hgood2 := hgood2 hd.good
  have hK : ∀ g, lastRow g ∈ C → χ₁ g * conj (χ₂ g) = (Dt g : ℂ) ^ z := fun g hg => by
    have h1 : Φ₀ (lastRow g) = 1 := hΦ1 hg
    simp only [hχ₁, hχ₂, map_mul, Complex.conj_conj, Complex.conj_ofReal, h1, Complex.ofReal_one, mul_one]
    rw [Complex.ofReal_cpow (hDpos g).le, ← Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (hDpos g).ne')]
    congr 1; ring
  have hW : ∀ g, whit ψ (k - 1) (fun g => χ₁ g * f g) g * conj (whit ψ (k - 1) (fun g => χ₂ g * φ g) g) =
      PW ψ f φ g * (Dt g : ℂ) ^ z := fun g => by
    rw [hwf, hwφ]
    by_cases h0 : whit ψ (k - 1) f g = 0
    · simp [PW, h0]
    · rw [PW, ← hK g (hLsupp (k - 1) hk1 f C hfC g h0), map_mul]; ring
  have hF : ∀ g, χ₁ g * f g * conj (χ₂ g * φ g) = f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    by_cases h0 : f g = 0
    · simp [h0]
    · rw [← hK g (hfC g h0), map_mul]; ring
  have hL2f : ∫⁻ g, ‖χ₁ g * f g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    rw [hU0a (fun g => ‖χ₁ g * f g‖ₑ ^ 2) (hpre1.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre1.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_) (((hV1c ε hε).const_mul Cf).lintegral_lt_top)
    have hterm : ∀ x, ‖χ₁ x * f x‖ₑ ^ 2 = ENNReal.ofReal (Dt x ^ a) * ‖f x‖ₑ ^ 2 := fun x => by
      rw [enorm_mul, mul_pow]
      congr 1
      rw [hχ₁]
      simp only
      rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg (hDpos x).le _),
        ← ENNReal.ofReal_pow (Real.rpow_nonneg (hDpos x).le _), ← Real.rpow_mul_natCast (hDpos x).le]
      norm_num
    simp only [hterm, hDr, ENNReal.tsum_mul_left]
    calc ENNReal.ofReal (Dt g ^ a) * ∑' ξ : RowT E k k, ‖f (ratGL E k (gam ξ) * g)‖ₑ ^ 2
        ≤ ENNReal.ofReal (Dt g ^ a) * ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε * Dt g ^ (-a)) := by
          gcongr; exact hsq g
      _ = ENNReal.ofReal (Cf * min (Dt g) (Dt g)⁻¹ ^ ε) := by
        rw [← ENNReal.ofReal_mul (Real.rpow_nonneg (hDpos g).le _)]
        congr 1
        have hp := Real.rpow_pos_of_pos (hDpos g) a
        rw [Real.rpow_neg (hDpos g).le]
        field_simp
  have hL2φ : ∫⁻ g, ‖χ₂ g * φ g‖ₑ ^ 2 ∂μ.withDensity β₁ < ∞ := by
    obtain ⟨-, hG4b⟩ := hG4 E k hk φ hd.dec
    obtain ⟨s, hs⟩ : ∃ s, s = 2 * z.re - a := ⟨_, rfl⟩
    have hs2 : 2 ≤ s := by linarith
    obtain ⟨N, hN⟩ : ∃ N : ℕ, N = ⌈s⌉₊ + 1 := ⟨_, rfl⟩
    have hNs : s + 1 ≤ (N : ℝ) := by rw [hN]; push_cast; linarith [Nat.le_ceil s]
    obtain ⟨C1, hC1⟩ := hG4b _ hΦc.isCompact k le_rfl
    obtain ⟨C2, hC2⟩ := hG4b _ hΦc.isCompact (k * N) (Nat.le_mul_of_pos_right k (by omega))
    have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    have e1 : -((k : ℕ) : ℝ) / k = -1 := by field_simp
    have e2 : -(((k * N : ℕ)) : ℝ) / k = -(N : ℝ) := by push_cast; field_simp
    rw [e1] at hC1; rw [e2] at hC2
    rw [hU0a (fun g => ‖χ₂ g * φ g‖ₑ ^ 2) (hpre2.cont.measurable.enorm.pow_const 2)
      (fun γ hγ g => congrArg (fun w : ℂ => ‖w‖ₑ ^ 2) (hpre2.left γ hγ g))]
    refine lt_of_le_of_lt (lintegral_mono fun g => ?_)
      (((hV1c 1 one_pos).const_mul (Bφ * max (max C1 C2) 0)).lintegral_lt_top)
    refine le_trans ?_ (SquareIntegralBound.bnd (Dt g) Bφ C1 C2 s N (hDpos g) hBφ0 hs2 hNs _ (hC1 g) (hC2 g))
    rw [← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    refine ENNReal.tsum_le_tsum fun ξ => ?_
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    rw [hφ]
    have hDx : Dt (ratGL E k (gam ξ) * g) = Dt g := hDr _ _
    by_cases hx : lastRow (ratGL E k (gam ξ) * g) ∈ tsupport Φ₀
    · rw [Set.indicator_of_mem hx, one_mul]
      rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_pow (norm_nonneg _),
        ← ENNReal.ofReal_mul (mul_nonneg hBφ0 (Real.rpow_nonneg (hDpos g).le _))]
      refine ENNReal.ofReal_le_ofReal ?_
      have hχn : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ≤ Dt g ^ (z.re - a / 2) := by
        rw [hχ₂]; simp only
        rw [norm_mul, Complex.norm_conj, Complex.norm_cpow_eq_rpow_re_of_pos (hDpos _), Complex.norm_real, hDx]
        simp only [Complex.sub_re, Complex.ofReal_re]
        have h0 := hΦI (lastRow (ratGL E k (gam ξ) * g))
        rw [Real.norm_of_nonneg h0.1]
        exact mul_le_of_le_one_right (Real.rpow_nonneg (hDpos g).le _) h0.2
      have hsq' : Dt g ^ s = (Dt g ^ (z.re - a / 2)) ^ 2 := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (hDpos g).le]; congr 1; rw [hs]; push_cast; ring
      rw [norm_mul, mul_pow, hsq']
      have hφg := hBφ g
      have h3 : ‖χ₂ (ratGL E k (gam ξ) * g)‖ ^ 2 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hχn 2
      have h4 : 0 ≤ (Dt g ^ (z.re - a / 2)) ^ 2 := by positivity
      nlinarith [norm_nonneg (φ g), mul_le_mul_of_nonneg_right h3 (sq_nonneg ‖φ g‖),
        mul_le_mul_of_nonneg_left hφg (mul_nonneg h4 (norm_nonneg (φ g)))]
    · have : Φ₀ (lastRow (ratGL E k (gam ξ) * g)) = 0 := image_eq_zero_of_notMem_tsupport hx
      simp [hχ₂, this]
  obtain ⟨hint, heq⟩ := hU2' _ _ hpre1 hgood2 hL2f hL2φ
  have hmeas : Measurable fun g => χ₁ g * f g * conj (χ₂ g * φ g) :=
    (hpre1.cont.mul (Complex.continuous_conj.comp hpre2.cont)).measurable
  have hinv : ∀ γ, IsMir (k - 1) γ → ∀ g, (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (ratGL E k γ * g) =
      (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g := fun γ hγ g => by
    have h1 := hpre1.left γ hγ g
    have h2 := hpre2.left γ hγ g
    simp only at h1 h2 ⊢
    rw [h1, h2]
  have hintF : Integrable (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) (μ.withDensity β₁) :=
    intMul hpre1.cont.aestronglyMeasurable hpre2.cont.aestronglyMeasurable hL2f hL2φ
  have hsum : ∀ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g =
      sumF f g * conj (φ g) * (Dt g : ℂ) ^ z := fun g => by
    have hφ : ∀ γ g, φ (ratGL E k γ * g) = φ g := hd.inv
    simp only [sumF, hF]
    simp only [hφ, hDr, tsum_mul_right]
  refine ⟨hint.congr (Filter.Eventually.of_forall hW), ?_⟩
  calc ∫ g, sumF f g * conj (φ g) * (Dt g : ℂ) ^ z ∂μ.withDensity β
      = ∫ g, sumF (fun g => χ₁ g * f g * conj (χ₂ g * φ g)) g ∂μ.withDensity β := by simp only [hsum]
    _ = ∫ g, χ₁ g * f g * conj (χ₂ g * φ g) ∂μ.withDensity β₁ := (hU0b _ hmeas hinv hintF).symm
    _ = _ := heq
    _ = ∫ g, PW ψ f φ g * (Dt g : ℂ) ^ z ∂μ.withDensity β' := by simp only [hW]

end PositivityTheory.AdelicQuotientData

end
end

-- bundled from Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaRigidity.TorusPowerExponential
section
noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.jumpWindows PositivityTheory.RgJS
open GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.Spherical
open scoped ENNReal ComplexConjugate

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.AdelicQuotientData

namespace TorusPowerExponential

section Loc

variable (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] (n : ℕ)

theorem torusPow_add (x y : Fin n → ℤ) :
    Iwasawa.torusPow F n (x + y) = Iwasawa.torusPow F n x * Iwasawa.torusPow F n y := by
  simp only [Iwasawa.torusPow, ← map_mul]
  congr 1
  funext i
  simp [_root_.zpow_add]

theorem conj_mem (x : Fin n → ℤ) {u : GL (Fin n) F} (hu : u ∈ Iwasawa.unipotent F n) :
    Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹ ∈ Iwasawa.unipotent F n :=
  Iwasawa.diagGL_mul_mul_inv_mem_unipotent F n hu _

theorem exp_torus_mul (x : Fin n → ℤ) (h : GL (Fin n) F) :
    Iwasawa.iwasawaExponent F n (Iwasawa.torusPow F n x * h) = x + Iwasawa.iwasawaExponent F n h := by
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent F n h
  have key : Iwasawa.torusPow F n x * h = (Iwasawa.torusPow F n x * u * (Iwasawa.torusPow F n x)⁻¹) *
      Iwasawa.torusPow F n (x + Iwasawa.iwasawaExponent F n h) * κ := by
    rw [torusPow_add]
    conv_lhs => rw [e]
    group
  rw [key, Iwasawa.iwasawaExponent_eq F n (conj_mem F n x hu) hκ]

theorem torusPow_zero : Iwasawa.torusPow F n 0 = 1 := by
  simpa using torusPow_add F n 0 0

end Loc

section Glob

variable {E : Type} [Field E] [NumberField E] {k : ℕ}

theorem countable_pl : Countable (Pl E) := by
  classical
  haveI : Countable (𝓞 E) := (RingOfIntegers.basis E).repr.toEquiv.injective.countable
  let f : Pl E → Finset (𝓞 E) := fun v ↦ (IsNoetherian.noetherian v.asIdeal).choose
  refine Function.Injective.countable (f := f) fun v w h ↦ ?_
  have hv := (IsNoetherian.noetherian v.asIdeal).choose_spec
  have hw := (IsNoetherian.noetherian w.asIdeal).choose_spec
  ext1
  rw [← hv, ← hw]
  exact congrArg (fun s : Finset (𝓞 E) ↦ Submodule.span (𝓞 E) (s : Set (𝓞 E))) h

def A (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) : Set (GA E k) :=
  {g | ∀ w : Off E S, Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w}

theorem A_zero (S : Finset (Pl E)) : A (k := k) S 0 = G0 S := by
  ext g
  simp only [A, G0, Set.mem_setOf_eq, Finsupp.coe_zero, Pi.zero_apply]
  exact ⟨fun h w hw => h ⟨w, hw⟩, fun h w => h w.1 w.2⟩

theorem A_cover (S : Finset (Pl E))
    (hfin : ∀ g : GA E k, {w | Iwasawa.iwasawaExponent _ k (cLoc w g) ≠ 0}.Finite) (g : GA E k) :
    ∃ l, g ∈ A S l :=
  ⟨Finsupp.ofSupportFinite (fun w : Off E S => Iwasawa.iwasawaExponent _ k (cLoc w.1 g))
    ((hfin g).preimage Subtype.val_injective.injOn), fun w => rfl⟩

theorem A_disj (S : Finset (Pl E)) : Pairwise (Function.onFun Disjoint (A (k := k) S)) := by
  intro l l' hne
  exact Set.disjoint_left.2 fun g h h' => hne (Finsupp.ext fun w => (h w).symm.trans (h' w))

theorem A_closed (S : Finset (Pl E))
    (hcl : ∀ (w : Pl E) (l : Fin k → ℤ), IsClopen {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w g) = l})
    (l : Off E S →₀ (Fin k → ℤ)) : IsClosed (A S l) := by
  have : A S l = ⋂ w : Off E S, {g : GA E k | Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = l w} := by
    ext; simp [A]
  rw [this]
  exact isClosed_iInter fun w => (hcl w.1 (l w)).isClosed

theorem cLoc_unip (u : GA E k) (hu : UU 0 u) (w : Pl E) : cLoc w u ∈ Iwasawa.unipotent _ k := by
  refine ⟨fun i c hci => ?_, fun i => ?_⟩
  · change ((pLoc E w).comp (pFin E)) (u.val i c) = 0
    rw [hu.1 i c hci, map_zero]
  · change ((pLoc E w).comp (pFin E)) (u.val i i) = 1
    rw [hu.2.1 i, map_one]

theorem A_mul (S : Finset (Pl E)) (l : Off E S →₀ (Fin k → ℤ)) (u g : GA E k) (hu : UU 0 u) :
    u * g ∈ A S l ↔ g ∈ A S l := by
  have h := fun w : Pl E => Iwasawa.iwasawaExponent_mul_of_mem_unipotent _ k (cLoc_unip u hu w) (cLoc w g)
  simp only [A, Set.mem_setOf_eq, map_mul, h]

theorem A_tr (S : Finset (Pl E))
    (hloc : ∀ (w : Pl E) (u : GL (Fin k) (w.adicCompletion E)), cLoc w (fl k w u : GA E k) = u)
    (hoff : ∀ (w v : Pl E) (u : GL (Fin k) (w.adicCompletion E)), v ≠ w → cLoc v (fl k w u : GA E k) = 1)
    (l : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (hw : l w = 0) (x : Fin k → ℤ) (g : GA E k) :
    fl k w.1 (Iwasawa.torusPow _ k x) * g ∈ A S (Finsupp.single w x + l) ↔ g ∈ A S l := by
  simp only [A, Set.mem_setOf_eq, map_mul]
  have key : ∀ v : Off E S, (Iwasawa.iwasawaExponent _ k (cLoc v.1 (fl k w.1 (Iwasawa.torusPow _ k x)) *
      cLoc v.1 g) = (Finsupp.single w x + l) v ↔ Iwasawa.iwasawaExponent _ k (cLoc v.1 g) = l v) := by
    intro v
    by_cases hv : v = w
    · subst hv
      rw [hloc, exp_torus_mul, Finsupp.add_apply, Finsupp.single_eq_same, hw, add_zero]
      constructor
      · intro h; simpa using h
      · intro h; rw [h, add_zero]
    · have e1 : (Finsupp.single w x + l) v = l v := by simp [Finsupp.single_apply, Ne.symm hv]
      rw [hoff w.1 v.1 _ (fun h => hv (Subtype.ext h)), one_mul, e1]
  exact forall_congr' key

theorem Phi_tr (S : Finset (Pl E)) (Φ : GA E k → ℂ) (a : Off E S → (Fin k → ℤ) → ℂ) (hlaw : LawOff S Φ a)
    (ha0 : ∀ w, a w 0 = 1)
    (hcomm : ∀ (w : Pl E) (g : GA E k), cLoc w g = 1 → ∀ u, g * fl k w u = fl k w u * g)
    (hdec : ∀ (w : Pl E) (g : GA E k), ∃ g' : GA E k, cLoc w g' = 1 ∧ g = g' * fl k w (cLoc w g))
    (w : Off E S) (x : Fin k → ℤ) (g : GA E k) (hg : Iwasawa.iwasawaExponent _ k (cLoc w.1 g) = 0) :
    Φ (fl k w.1 (Iwasawa.torusPow _ k x) * g) = a w x * Φ g := by
  obtain ⟨g', h1, hg'⟩ := hdec w.1 g
  obtain ⟨u, hu, κ, hκ, e⟩ := Iwasawa.exists_eq_mul_torusPow_iwasawaExponent _ k (cLoc w.1 g)
  rw [hg] at e
  have h0 : Φ g = Φ g' := by
    rw [hg', e, hlaw w g' h1 u hu κ hκ 0, ha0, mul_one]
  have h2 : fl k w.1 (Iwasawa.torusPow _ k x) * g = g' * fl k w.1
      ((Iwasawa.torusPow _ k x * u * (Iwasawa.torusPow _ k x)⁻¹) * Iwasawa.torusPow _ k x * κ) := by
    conv_lhs => rw [hg', e]
    rw [← mul_assoc, ← hcomm w.1 g' h1, mul_assoc, ← map_mul, torusPow_zero, mul_one]
    congr 2
    group
  rw [h2, hlaw w g' h1 _ (conj_mem _ k x hu) κ hκ x, h0, mul_comm]

end Glob

end TorusPowerExponential

theorem torus_exponential_of_open : jumpWindows.G0 → C0 → C1 → C2 := by
  intro hG hC0 hC1 E _ _ _ k μ _ hk β hβ S Φ a hΦm hΦu hlaw ha0 hint
  obtain ⟨-, -, -, hloc, hoff, -, -, hcomm, -⟩ := hG E k
  obtain ⟨-, -, -, -, hfin, hcl, hdec⟩ := hC0 E k S
  haveI := TorusPowerExponential.countable_pl (E := E)
  have hmeas : ∀ l, MeasurableSet (TorusPowerExponential.A (k := k) S l) := fun l => (TorusPowerExponential.A_closed S hcl l).measurableSet
  let c : Off E S → (Fin k → ℤ) → ℂ := fun w x => (nq w : ℂ) ^ rhoPair x * a w x
  have hc0 : ∀ w, c w 0 = 1 := fun w => by simp [c, rhoPair, ha0]
  have hstep : ∀ (f : Off E S →₀ (Fin k → ℤ)) (w : Off E S) (x : Fin k → ℤ), f w = 0 →
      ∫ g in TorusPowerExponential.A S (Finsupp.single w x + f), Φ g ∂μ.withDensity β =
        c w x * ∫ g in TorusPowerExponential.A S f, Φ g ∂μ.withDensity β := by
    intro f w x hw
    have hUU : ∀ u, UU 0 u → ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ (u * g) =
        (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ g := by
      intro u hu g
      by_cases hg : g ∈ TorusPowerExponential.A S (Finsupp.single w x + f)
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_mul S _ u g hu).2 hg), Set.indicator_of_mem hg, hΦu u hu g]
      · rw [Set.indicator_of_notMem (mt (TorusPowerExponential.A_mul S _ u g hu).1 hg), Set.indicator_of_notMem hg]
    obtain ⟨-, hE⟩ := hC1 E k μ hk β hβ w.1 x ((TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ)
      (hΦm.indicator (hmeas _))
      hUU
      (hint.indicator (hmeas _))
    rw [← integral_indicator (hmeas _), hE, ← integral_indicator (hmeas _)]
    have hpt : ∀ g, (TorusPowerExponential.A S (Finsupp.single w x + f)).indicator Φ
        (fl k w.1 (Iwasawa.torusPow (w.1.adicCompletion E) k x) * g) =
        a w x * (TorusPowerExponential.A S f).indicator Φ g := by
      intro g
      by_cases hg : g ∈ TorusPowerExponential.A S f
      · rw [Set.indicator_of_mem ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).2 hg), Set.indicator_of_mem hg,
          TorusPowerExponential.Phi_tr S Φ a hlaw ha0 hcomm (fun w g => (hdec w g).imp fun g' h => ⟨h.1, h.2.1⟩) w x g
            ((hg w).trans hw)]
      · rw [Set.indicator_of_notMem (fun h => hg ((TorusPowerExponential.A_tr S hloc hoff f w hw x g).1 h)),
          Set.indicator_of_notMem hg, mul_zero]
    simp only [hpt, c, nq]
    rw [integral_const_mul, mul_assoc]
  have hclaim : ∀ l : Off E S →₀ (Fin k → ℤ), ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β =
      (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β := by
    intro l
    induction l using Finsupp.induction with
    | zero => simp [TorusPowerExponential.A_zero]
    | single_add w x f hwf hx ih =>
      have hfw : f w = 0 := Finsupp.notMem_support_iff.1 hwf
      change _ = Finsupp.prod (Finsupp.single w x + f) c * _
      change _ = Finsupp.prod f c * _ at ih
      have hdisj : Disjoint (Finsupp.single w x).support f.support := by
        refine Finset.disjoint_left.2 fun v hv hv' => hwf ?_
        rw [Finsupp.support_single_ne_zero _ hx, Finset.mem_singleton] at hv
        exact hv ▸ hv'
      rw [Finsupp.prod_add_index_of_disjoint hdisj, Finsupp.prod_single_index (hc0 w), hstep f w x hfw, ih]
      simp only [c]
      ring
  have hU : ⋃ l, TorusPowerExponential.A (k := k) S l = Set.univ := Set.iUnion_eq_univ_iff.2 (TorusPowerExponential.A_cover S hfin)
  have hs := hasSum_integral_iUnion hmeas (TorusPowerExponential.A_disj S) hint.integrableOn
  rw [hU, setIntegral_univ] at hs
  have hfun : (fun l => ∫ g in TorusPowerExponential.A S l, Φ g ∂μ.withDensity β) =
      fun l : Off E S →₀ (Fin k → ℤ) => (∏ w ∈ l.support, c w (l w)) * ∫ g in G0 S, Φ g ∂μ.withDensity β :=
    funext hclaim
  rw [hfun] at hs
  exact hs

end PositivityTheory.AdelicQuotientData

end
end

