module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0173
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DepletedCuspEigenformHeckeRelations
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0171
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0153
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0169
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0151
public import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0003
public import Formalism.SharpRestriction.Divisibility.SchurIrreducible
public import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0004

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TwistedLvalueNeZeroEdge
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm

namespace GlobalTheory.EisM.ZEdge

theorem isUnit_of_isCoprime {L : ℕ} {d : ℤ} (h : IsCoprime d (L : ℤ)) : IsUnit (d : ZMod L) := by
  obtain ⟨u, v, huv⟩ := h
  have h2 := congrArg (Int.cast : ℤ → ZMod L) huv
  push_cast at h2
  rw [ZMod.natCast_self, mul_zero, add_zero] at h2
  exact ⟨⟨(d : ZMod L), (u : ZMod L), by rw [mul_comm]; exact h2, h2⟩, rfl⟩

theorem changeLevel_int {n m : ℕ} (χ : DirichletCharacter ℂ n) (h : n ∣ m) (d : ℤ) (hd : IsUnit (d : ZMod m)) :
    DirichletCharacter.changeLevel h χ (d : ZMod m) = χ (d : ZMod n) := by
  have := DirichletCharacter.changeLevel_eq_cast_of_dvd χ h hd.unit
  simp only [IsUnit.unit_spec] at this
  rw [this, ZMod.cast_intCast h]

theorem chi_neg_one (k N : ℕ) (χ : DirichletCharacter ℂ N) (g : ℕ → ℂ) (hk : Odd k) (hg : Prim k N χ g) :
    χ (-1) = -1 := by
  by_contra hne
  have hinv := hg.cf.1.2 (-1) (by simp)
  have hq : ∀ τ : ℍ, qs g τ = 0 := by
    intro τ
    have h1 := hinv τ
    have hs : (-1 : SL(2, ℤ)) • τ = τ := by rw [ModularGroup.SL_neg_smul, one_smul]
    rw [hs] at h1
    simp [ch, hk.neg_one_pow] at h1
    have h3 : qs g τ * (1 + χ (-1)) = 0 := by linear_combination h1
    rcases mul_eq_zero.1 h3 with h | h
    · exact h
    · exact absurd (by linear_combination h) hne
  have hq0 : qs g = qs 0 := by
    funext τ; rw [hq τ]; simp [qs]
  have hp0 : PolyB (0 : ℕ → ℂ) := ⟨0, 0, by simp⟩
  have := _root_.GlobalTheory.EisM.qs_injective g 0 hg.cf.1.1 hp0 hq0
  have h1 := hg.one
  rw [this] at h1
  simp at h1

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem multiplier_agree (N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) :
    ∀ d : ℤ, IsCoprime d ((N * M ^ 2 : ℕ) : ℤ) →
      ch χ d * ch φ d ^ 2 = ch (DirichletCharacter.changeLevel (dvd_mul_right N (M ^ 2)) χ *
        (DirichletCharacter.changeLevel (Dvd.intro_left _ (pow_two M).symm |>.trans (dvd_mul_left _ N)) φ) ^ 2) d := by
  intro d hd
  have hu := isUnit_of_isCoprime hd
  simp only [ch, MulChar.mul_apply, MulChar.pow_apply' _ two_ne_zero]
  rw [changeLevel_int χ _ d hu, changeLevel_int φ _ d hu]

theorem exists_entire (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hk : 1 ≤ k) (hN : 0 < N) (hM : 0 < M) (hg : CF k N (ch χ) g) :
    ∃ Λ : ℂ → ℂ, Differentiable ℂ Λ ∧ ∀ s : ℂ, ((k : ℝ) + 1) / 2 < s.re →
      LSeries (fun n => φ n * g n) s = Λ s := by
  have ht := _root_.GlobalTheory.EisM.CharTwist.cf_twist k N M χ φ g hM hg
  have hmf := (_root_.GlobalTheory.EisM.mf_linear k (N * M ^ 2) _).2.2.2.1 _ _ (multiplier_agree N M χ φ) ht.1
  obtain ⟨Λ, h1, h2⟩ := _root_.GlobalTheory.EisM.lseries_cusp_entire k (N * M ^ 2) (N * M ^ 2) _ _ hk (by positivity) dvd_rfl ⟨hmf, ht.2⟩
  exact ⟨Λ, h1, fun s hs => (h2 s hs).2⟩

theorem norm_b_sq (e n : ℕ) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := by
  rw [norm_div, norm_mul, norm_pow, Complex.norm_natCast, div_pow, mul_pow, ← pow_mul, mul_comm e 2, mul_div_assoc]
  exact mul_le_of_le_one_left (by positivity) (pow_le_one₀ (norm_nonneg _) (DirichletCharacter.norm_le_one φ _))

theorem term_le (e n : ℕ) (s : ℝ) (hs : 0 < s) {M : ℕ} (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) :
    ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s) ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
  rcases n.eq_zero_or_pos with rfl | hn
  · rw [show ((0 : ℕ) : ℝ) = 0 from Nat.cast_zero, Real.zero_rpow (by linarith), Real.zero_rpow (by positivity), div_zero, div_zero]
  · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
    calc _ ≤ (‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e)) / (n : ℝ) ^ (1 + s) :=
          div_le_div_of_nonneg_right (norm_b_sq e n φ g) (by positivity)
      _ = _ := by
          rw [div_div]; congr 1
          rw [← Real.rpow_natCast, ← Real.rpow_add hn']; congr 1; push_cast; ring

theorem lseries_shift (e : ℕ) (a : ℕ → ℂ) (z : ℂ) :
    LSeries (fun n => a n / (n : ℂ) ^ e) z = LSeries a (z + e) := by
  unfold LSeries; congr 1; funext n
  simp only [LSeries.term]
  split_ifs with h
  · rfl
  · rw [cpow_add _ _ (Nat.cast_ne_zero.2 h), cpow_natCast, div_div, mul_comm]

end GlobalTheory.EisM.ZEdge

namespace GlobalTheory.EisM.ZEdge

theorem b_props (e N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ)
    (hN : 0 < N) (hg : Prim (2 * e + 1) N χ g) (hχ : χ (-1) = -1) (hg0 : g 0 = 0) :
    let b : ℕ → ℂ := fun n => φ n * g n / (n : ℂ) ^ e
    let ω : ℕ → ℂ := fun p => χ p * φ p ^ 2
    b 1 = 1 ∧ b 0 = 0 ∧ (∀ m n : ℕ, m.Coprime n → b (m * n) = b m * b n) ∧
    (∀ n, ¬ n.Coprime (N * M) → b n = 0) ∧
    (∀ p r : ℕ, p.Prime → ¬ p ∣ N * M → ‖ω p‖ = 1 ∧ b (p ^ (r + 2)) = b p * b (p ^ (r + 1)) - ω p * b (p ^ r)) ∧
    (∀ p : ℕ, p.Prime → ¬ p ∣ N * M → (p : ZMod (N * M)) = -1 → (b p).re = 0) := by
  intro b ω
  obtain ⟨hmul, hrec, -⟩ := _root_.GlobalTheory.EisM.hecke_relations (2 * e + 1) N χ g (by omega) hN hg
  refine ⟨by simp [b, hg.one], by simp [b, hg0], ?_, ?_, ?_, ?_⟩
  · intro m n hmn
    simp only [b, Nat.cast_mul, map_mul, hmul m n hmn, mul_pow]
    ring
  · intro n hn
    simp only [b]
    by_cases hnN : n.Coprime N
    · have hnM : ¬ n.Coprime M := fun h => hn (Nat.Coprime.mul_right hnN h)
      rw [MulChar.map_nonunit φ (by rwa [ZMod.isUnit_iff_coprime]), zero_mul, zero_div]
    · rw [hg.zero n hnN, mul_zero, zero_div]
  · intro p r hp hpd
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have huN : IsUnit (p : ZMod N) := (ZMod.isUnit_iff_coprime p N).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpN)
    have hp0 : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    refine ⟨?_, ?_⟩
    · simp only [ω, norm_mul, norm_pow]
      have h1 := DirichletCharacter.unit_norm_eq_one χ huN.unit
      simp only [IsUnit.unit_spec] at h1
      rw [h1, one_mul]
      have hpM : ¬ p ∣ M := fun h => hpd (dvd_mul_of_dvd_right h N)
      have huM : IsUnit (p : ZMod M) := (ZMod.isUnit_iff_coprime p M).2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hpM)
      have h2 := DirichletCharacter.unit_norm_eq_one φ huM.unit
      simp only [IsUnit.unit_spec] at h2
      rw [h2, one_pow]
    · simp only [b, Nat.cast_pow, map_pow, hrec p r hp hpN, ω]
      rw [show 2 * e + 1 - 1 = 2 * e by omega]
      field_simp
      ring
  · intro p hp hpd hpm
    have hpN : ¬ p ∣ N := fun h => hpd (dvd_mul_of_dvd_left h M)
    have hcN : (p : ZMod N) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_right N M) (ZMod N)) hpm
      simpa using this
    have hcM : (p : ZMod M) = -1 := by
      have := congrArg (ZMod.castHom (dvd_mul_left M N) (ZMod M)) hpm
      simpa using this
    have hreal := _root_.GlobalTheory.EisMReal.eig_conj (2 * e + 1) N p χ g (by omega) hN hg hp hpN
    simp only [ch, Int.cast_natCast, hcN, hχ] at hreal
    have hre : (g p).re = 0 := by
      have := congrArg Complex.re hreal
      simp at this
      linarith
    have hφ : φ (-1) = 1 ∨ φ (-1) = -1 := by
      have h2 : φ (-1) ^ 2 = 1 := by rw [← map_pow]; simp
      have h3 : (φ (-1) - 1) * (φ (-1) + 1) = 0 := by linear_combination h2
      rcases mul_eq_zero.1 h3 with h | h
      · left; linear_combination h
      · right; linear_combination h
    simp only [b, hcM]
    rw [← Nat.cast_pow, Complex.div_natCast_re]
    rcases hφ with h | h <;> simp [h, hre]

end GlobalTheory.EisM.ZEdge

theorem GlobalTheory.EisM.twisted_lvalue_ne_zero_edge : ∀ (k N M : ℕ) (χ : DirichletCharacter ℂ N) (φ : DirichletCharacter ℂ M) (g : ℕ → ℂ) (w : ℝ), Odd k → 0 < N → 0 < M → Prim k N χ g → ((k : ℝ) + 1) / 2 ≤ w → χ (-1) = -1 ∧ ∃ v : ℂ, v ≠ 0 ∧ Tendsto (fun s : ℝ => LSeries (fun n => φ n * g n) ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 v) := by
  intro k N M χ φ g w hk hN hM hg hw
  have hχ := GlobalTheory.EisM.ZEdge.chi_neg_one k N χ g hk hg
  refine ⟨hχ, ?_⟩
  obtain ⟨e, rfl⟩ := hk
  obtain ⟨Λ, hΛd, hΛ⟩ := GlobalTheory.EisM.ZEdge.exists_entire (2 * e + 1) N M χ φ g (by omega) hN hM hg.cf
  obtain ⟨hg0, ⟨C1, hC1⟩, hsum, ⟨C2, hC2⟩⟩ := _root_.GlobalTheory.rankin_mean_square (2 * e + 1) N (ch χ) g (by omega) hg.cf
  obtain ⟨hb1, hb0, hbm, hbz, hbr, hbre⟩ := GlobalTheory.EisM.ZEdge.b_props e N M χ φ g hN hg hχ hg0
  have hkw : (e : ℝ) + 1 ≤ w := by push_cast at hw; linarith
  have hne : Λ w ≠ 0 := by
    have key := _root_.GlobalTheory.EisM.lseries_ne_zero_edge (N * M) (fun n => φ n * g n / (n : ℂ) ^ e) (fun p => χ p * φ p ^ 2) (max C1 C2)
      (fun z => Λ (z + e)) (by positivity) hb1 hb0 hbm hbz hbr ?_ ?_ ?_ hbre ?_ ?_ (w - e) (by linarith)
    · have hc : (((w - e : ℝ)) : ℂ) + (e : ℂ) = (w : ℂ) := by push_cast; ring
      simpa [hc] using key
    · intro n
      rcases n.eq_zero_or_pos with rfl | hn
      · simp [hg0]
      · have hn' : (0 : ℝ) < n := by exact_mod_cast hn
        calc ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 ≤ ‖g n‖ ^ 2 / (n : ℝ) ^ (2 * e) := GlobalTheory.EisM.ZEdge.norm_b_sq e n φ g
          _ ≤ C1 * (n : ℝ) ^ (2 * e + 1) / (n : ℝ) ^ (2 * e) := div_le_div_of_nonneg_right (hC1 n) (by positivity)
          _ = C1 * n := by field_simp; ring
          _ ≤ max C1 C2 * n := mul_le_mul_of_nonneg_right (le_max_left _ _) hn'.le
    · intro s hs
      exact Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)
    · intro s hs hs1
      calc s * ∑' n : ℕ, ‖φ n * g n / (n : ℂ) ^ e‖ ^ 2 / (n : ℝ) ^ (1 + s)
          ≤ s * ∑' n : ℕ, ‖g n‖ ^ 2 / (n : ℝ) ^ (((2 * e + 1 : ℕ) : ℝ) + s) := by
            apply mul_le_mul_of_nonneg_left _ hs.le
            exact Summable.tsum_le_tsum (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g)
              (Summable.of_nonneg_of_le (fun n => by positivity) (fun n => GlobalTheory.EisM.ZEdge.term_le e n s hs φ g) (hsum s hs)) (hsum s hs)
        _ ≤ C2 := hC2 s hs hs1
        _ ≤ max C1 C2 := le_max_right _ _
    · exact hΛd.comp (differentiable_id.add_const _)
    · intro s hs
      show LSeries (fun n => φ n * g n / (n : ℂ) ^ e) _ = Λ (_ + e)
      rw [GlobalTheory.EisM.ZEdge.lseries_shift e (fun n => φ n * g n)]
      apply hΛ
      simp
      push_cast
      linarith
  refine ⟨Λ w, hne, ?_⟩
  have hc : Tendsto (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (Λ w)) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds
    have : Continuous (fun s : ℝ => Λ ((w + s : ℝ) : ℂ)) :=
      hΛd.continuous.comp (Complex.continuous_ofReal.comp (continuous_const.add continuous_id))
    simpa using this.tendsto 0
  apply hc.congr'
  filter_upwards [self_mem_nhdsWithin] with s hs
  rw [hΛ]
  simp
  push_cast
  have : (0 : ℝ) < s := hs
  linarith
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ValuationComapLtOne
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.SelmerCrystallineCocycles

namespace GlobalTheory.AntiRam

section General

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

theorem valuation_comap_lt_one (c : Ω ≃+* Ω) (A : ValuationSubring Ω) (y : Ω) :
    (A.comap c.symm.toRingHom).valuation y < 1 ↔ A.valuation (c.symm y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_comap,
    ValuationSubring.mem_comap, ← map_inv₀, map_eq_zero_iff _ c.symm.injective]
  rfl

theorem exists_conj_mem_Ine (c : Ω ≃+* Ω) (κ : E → E)
    (hc : ∀ x, c (algebraMap E Ω x) = algebraMap E Ω (κ x)) (hκ : ∀ x, κ (κ x) = x)
    (A : ValuationSubring Ω) (σ : G E Ω) (hσ : σ ∈ Ine (F := E) A) :
    ∃ σ' : G E Ω, (∀ x, σ' x = c (σ (c.symm x))) ∧ σ' ∈ Ine (F := E) (A.comap c.symm.toRingHom) := by
  have hs : ∀ x, c.symm (algebraMap E Ω x) = algebraMap E Ω (κ x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  let σ' : Ω ≃ₐ[E] Ω := AlgEquiv.ofRingEquiv (f := (c.symm.trans (σ : Ω ≃ₐ[E] Ω).toRingEquiv).trans c)
    (fun x => by
      show c (σ (c.symm (algebraMap E Ω x))) = _
      rw [hs, AlgEquiv.commutes, hc, hκ])
  have h' : ∀ x, σ' x = c (σ (c.symm x)) := fun _ => rfl
  have hm : ∀ y, y ∈ A.comap c.symm.toRingHom ↔ c.symm y ∈ A := fun _ => Iff.rfl
  refine ⟨σ', h', ?_, fun x hx => ?_⟩
  · change σ' ∈ Dec (F := E) _
    rw [mem_Dec]
    ext y
    obtain ⟨z, rfl⟩ := σ'.surjective y
    rw [← AlgEquiv.smul_def σ' z, ValuationSubring.smul_mem_pointwise_smul_iff, AlgEquiv.smul_def,
      hm, hm, h', RingEquiv.symm_apply_apply, apply_mem_iff_of_mem_Dec hσ.1]
  · rw [valuation_comap_lt_one, map_sub, h', RingEquiv.symm_apply_apply]
    refine hσ.2 _ ?_
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact (hm x).1 hx

end General

theorem ramExactly_conj : ∀ (D : D7) (M : Type) [CommGroup M] (ψ : G D.host.E D.nd.Om →* M) (Q : Set (PlE D.host)), AntiHom D.ntw.cc ψ → RamExactly ψ Q → ∀ P ∈ Q, ∀ P' : PlE D.host, IsConjPl D.host P P' → P' ∈ Q := by
  intro D M _ ψ Q hA hR P hP P' hPP
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  have hst : ∀ x : D.host.E, IsCMField.complexConj D.host.E x = D.host.conj x :=
    bridge_star_holds D.R D.host
  obtain ⟨⟨j, hj⟩, -⟩ := D.ntw.cc_cm
  have hκ : ∀ x, D.host.conj (D.host.conj x) = x := fun x => by
    rw [← hst, ← hst, IsCMField.complexConj_apply_apply]
  have hc : ∀ x, D.ntw.cc (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    apply j.injective
    rw [hj, ← hst]
    exact (IsCMField.complexEmbedding_complexConj D.host.E
      (j.comp (algebraMap D.host.E D.nd.Om)) x).symm
  have hs : ∀ x, D.ntw.cc.symm (algebraMap D.host.E D.nd.Om x) =
      algebraMap D.host.E D.nd.Om (D.host.conj x) := fun x => by
    rw [RingEquiv.symm_apply_eq, hc, hκ]
  have hpl : IsPlaceOver (D.nd.plOm.1 P) P := D.nd.plOm.2 P
  obtain ⟨σ, hσ, hne⟩ := (hR P _ hpl).2 hP
  obtain ⟨σ', h1, h2⟩ := exists_conj_mem_Ine D.ntw.cc (fun x => D.host.conj x) hc hκ _ σ hσ
  refine (hR P' _ (fun y => ?_)).1 ⟨σ', h2, ?_⟩
  · have hint : IsIntegral ℤ (D.host.conj (y : D.host.E)) := by
      rw [← hst]
      exact (RingOfIntegers.isIntegral_coe y).map
        ((IsCMField.complexConj D.host.E).toRingEquiv.toRingHom.toIntAlgHom)
    rw [valuation_comap_lt_one, hs, ← hPP ⟨_, hint⟩ y (hκ _).symm]
    exact hpl ⟨_, hint⟩
  · rw [hA σ σ' h1]
    exact inv_ne_one.2 hne

end GlobalTheory.AntiRam
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightComponentMem
section
namespace GlobalTheory.WeightSubspaceComponent

open Formalism.BasicNotions.TH

theorem mem_wtSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (x : V) :
    x ∈ wtSub act μ ↔ ∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem weight_component_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ (a : Ix p q), ∀ x ∈ N, act (Eab a a) x ∈ N)
    (S : Finset (Ix p q → ℚ)) (f : (Ix p q → ℚ) → V)
    (hf : ∀ ν, f ν ∈ wtSub act ν) (hS : ∑ ν ∈ S, f ν ∈ N) : ∀ ν ∈ S, f ν ∈ N := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    intro ν hν
    by_cases h : ∃ μ ∈ S, μ ≠ ν
    · obtain ⟨μ, hμ, hne⟩ := h
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      let g : (Ix p q → ℚ) → V := fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l
      have hg : ∀ l, g l ∈ wtSub act l := fun l => Submodule.smul_mem _ _ (hf l)
      have hsum : ∑ l ∈ S.erase μ, g l
          = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l := by
        set_option synthInstance.maxHeartbeats 100000 in
          rw [Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [(mem_wtSub_iff act l (f l)).mp (hf l) a]
        exact sub_smul _ _ _
      have hmem : ∑ l ∈ S.erase μ, g l ∈ N := by
        rw [hsum]
        exact N.sub_mem (hN a _ hS) (N.smul_mem _ hS)
      have hgν := ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν
        (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)
      have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ha.symm
      exact (N.smul_mem_iff hc).mp hgν
    · have hone : ∑ l ∈ S, f l = f ν :=
        Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h
      rwa [hone] at hS

end GlobalTheory.WeightSubspaceComponent
end

