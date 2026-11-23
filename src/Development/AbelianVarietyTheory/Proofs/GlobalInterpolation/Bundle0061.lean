module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.LateralTheory
public import Formalism.LocalToGlobal.KernelLattices.DeterminantCokernelCount.CokernelIndexFactors.Bundle0001
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0055
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0058
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob
public import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Afsplit
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemIffForallMemLocalizeRingOfIntegers

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.AlgebraicDirectionScaledEmbedding
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

noncomputable section

namespace GlobalTheory.AlgDirMom

theorem exists_nat_mul_isIntegral {E : Type} [Field E] [NumberField E] (c : E) :
    ∃ m : ℕ, 0 < m ∧ IsIntegral ℤ ((m : E) * c) := by
  have hc : IsAlgebraic ℤ c :=
    (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic c)
  obtain ⟨z, hz0, hz⟩ := hc.exists_integral_multiple
  refine ⟨z.natAbs, Int.natAbs_pos.2 hz0, ?_⟩
  rw [zsmul_eq_mul] at hz
  rcases Int.natAbs_eq z with h | h
  · rw [h] at hz; simpa using hz
  · rw [h] at hz
    have := hz.neg
    simpa using this

theorem exists_nat_smul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L' : Submodule (𝓞 E) (Fin n → E))
    (hL' : Submodule.span E (L' : Set (Fin n → E)) = ⊤) (v : Fin n → E) :
    ∃ k : ℕ, 0 < k ∧ (k : E) • v ∈ L' := by
  have hv : v ∈ Submodule.span E (L' : Set (Fin n → E)) := hL' ▸ Submodule.mem_top
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_pos, by simpa using hx⟩
  | zero => exact ⟨1, one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨b, hb, hby⟩ := hy
    refine ⟨a * b, Nat.mul_pos ha hb, ?_⟩
    have e : ((a * b : ℕ) : E) • (x + y) = b • ((a : E) • x) + a • ((b : E) • y) := by
      rw [smul_add, ← Nat.cast_smul_eq_nsmul E b, ← Nat.cast_smul_eq_nsmul E a, smul_smul, smul_smul]
      push_cast
      rw [mul_comm (b : E) (a : E)]
    rw [e]
    exact L'.add_mem (L'.toAddSubmonoid.nsmul_mem hax b) (L'.toAddSubmonoid.nsmul_mem hby a)
  | smul c x _ hx =>
    obtain ⟨a, ha, hax⟩ := hx
    obtain ⟨m, hm, hint⟩ := exists_nat_mul_isIntegral c
    refine ⟨m * a, Nat.mul_pos hm ha, ?_⟩
    have h2 : (⟨(m : E) * c, hint⟩ : 𝓞 E) • ((a : E) • x) ∈ L' := L'.smul_mem _ hax
    rw [← algebraMap_smul E] at h2
    convert h2 using 1
    change _ = ((m : E) * c) • ((a : E) • x)
    rw [smul_smul, smul_smul]
    push_cast
    ring_nf

theorem exists_nat_smul_maps {E : Type} [Field E] [NumberField E] {N N' : ℕ}
    (L : Submodule (𝓞 E) (Fin N → E)) (L' : Submodule (𝓞 E) (Fin N' → E)) (hL : L.FG)
    (hL' : Submodule.span E (L' : Set (Fin N' → E)) = ⊤) (y : Matrix (Fin N') (Fin N) E) :
    ∃ k : ℕ, 0 < k ∧ ∀ x ∈ L, ((k : E) • y).mulVec x ∈ L' := by
  obtain ⟨s, hs⟩ := hL
  have hk : ∀ g ∈ s, ∃ k : ℕ, 0 < k ∧ (k : E) • y.mulVec g ∈ L' := fun g _ => exists_nat_smul_mem L' hL' _
  choose! kf hkpos hkmem using hk
  refine ⟨∏ g ∈ s, kf g, Finset.prod_pos fun g hg => hkpos g hg, ?_⟩
  intro x hx
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem g hg =>
    rw [Matrix.smul_mulVec]
    rw [← Finset.mul_prod_erase s kf hg]
    push_cast
    rw [mul_comm, ← smul_smul]
    rw [← Nat.cast_prod, Nat.cast_smul_eq_nsmul]
    exact L'.toAddSubmonoid.nsmul_mem (hkmem g hg) _
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact L'.add_mem hx hy
  | smul r x _ hx =>
    rw [Matrix.mulVec_smul]
    exact L'.smul_mem r hx

end GlobalTheory.AlgDirMom

namespace GlobalTheory.AlgDirMom

theorem embV_natCast_smul {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) {N N' : ℕ} (n : ℕ)
    (y : Matrix (Fin N') (Fin N) D.host.E) :
    embV D B.tor ((n : D.host.E) • y) = (n : ℂ) • embV D B.tor y := by
  funext τ i j
  simp [embV, Base.tor, tor0]

theorem algDir_smul_embV : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ δ₀ : ℂ) (B : Base D cc δ) (N N' : ℕ) (L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)) (L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)), IsCurveIdeal D cc → admitted D N N' L L' → δ / δ₀ ∈ Qbar → δ / δ₀ ≠ 0 → ∀ (g : ℕ) (S : JMB.Setup g) (e : VC D N N' ≃L[ℂ] (Fin g → ℂ)), (∀ x, e x ∈ S.La ↔ x ∈ La D B.tor L L') → ∀ y : Matrix (Fin N') (Fin N) D.host.E, S.AlgDir ((δ₀ / δ) • e (δ • embV D B.tor y)) := by
  intro D cc δ δ₀ B N N' L L' hcc hadm hq hq0 g S e he y
  have hδ : δ ≠ 0 := fun h => hq0 (by simp [h])
  have hδ₀ : δ₀ ≠ 0 := fun h => hq0 (by simp [h])
  obtain ⟨-, -, ⟨hLfg, -, -⟩, ⟨-, hL'sp, -⟩⟩ := hadm
  obtain ⟨n, hn, hnmap⟩ := exists_nat_smul_maps L L' hLfg hL'sp y
  have hNc : Ideal.absNorm cc ≠ 0 := fun h => hcc.1 (Ideal.absNorm_eq_zero_iff.1 h)
  have hA : (n : D.host.E) • y ∈ YYl D L L' :=
    Submodule.subset_span ⟨1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, _, Submodule.subset_span (fun x hx => hnmap x hx),
      (one_smul _ _).symm⟩
  have hw : δ * (Ideal.absNorm cc : ℂ) ∈ B.tor.abelian₂ := by
    change _ ∈ lamOf D cc δ
    exact AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp⟩
  have hx : (δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y) ∈ La D B.tor L L' :=
    AddSubgroup.subset_closure ⟨_, hw, _, hA, rfl⟩
  have hu := (he _).2 hx
  have hc : (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)) ∈ JMB.Qbar := by
    have h1 : δ₀ / δ = (δ / δ₀)⁻¹ := (inv_div δ δ₀).symm
    rw [h1]
    exact div_mem (inv_mem hq) (mul_mem (natCast_mem _ n) (natCast_mem _ _))
  refine ⟨1, fun _ => (δ₀ / δ) / ((n : ℂ) * (Ideal.absNorm cc : ℂ)),
    fun _ => e ((δ * (Ideal.absNorm cc : ℂ)) • embV D B.tor ((n : D.host.E) • y)), fun _ => hc, fun _ => hu, ?_⟩
  rw [Fin.sum_univ_one, embV_natCast_smul, smul_smul, map_smul, map_smul, smul_smul, smul_smul]
  congr 1
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  have hN0 : (Ideal.absNorm cc : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hNc
  field_simp

end GlobalTheory.AlgDirMom
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.BoxSumNeZeroInvariantAffineChangeStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.boxSum_ne_zero_invariant_affineChange : (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (a b : ℕ), (∀ v : Fin a → E, ∃ m : ℕ, ∀ m', m ≤ m' → IntV P (((qOf P : E) ^ m') • v)) ∧ ∀ y : (Fin a → E) →ₗ[E] (Fin b → E), ∃ m : ℕ, ∀ m', m ≤ m' → IntHom P (((qOf P : E) ^ m') • y)) → (∀ (V K : Type) [AddCommGroup V] [Field K] [CharZero K] (f : V → K) (N N' : AddSubgroup V) (S S' : Finset V), N'.relIndex N ≠ 0 → N.relIndex N' ≠ 0 → (∀ v, ∀ u ∈ N, f (v + u) = f v) → (∀ v, ∀ u ∈ N', f (v + u) = f v) → (∀ s ∈ S, ∀ s' ∈ S, s - s' ∈ N → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S, v - s ∈ N) → (∀ s ∈ S', ∀ s' ∈ S', s - s' ∈ N' → s = s') → (∀ v, f v ≠ 0 → ∃ s ∈ S', v - s ∈ N') → (∑ s ∈ S, f s ≠ 0 ↔ ∑ s ∈ S', f s ≠ 0)) → (∀ (E : Type) [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ A B : ℕ, (∀ a ∈ LocE.valsQ E (qOf P) A B, ∀ b ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - b)) → a = b) ∧ ∀ a : E, IntAt P ((qOf P : E) ^ A * a) → ∃ s ∈ LocE.valsQ E (qOf P) A B, IntAt P (((qOf P : E) ^ B)⁻¹ * (a - s))) → ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] [CharZero K] (P : HeightOneSpectrum (𝓞 E)), GlobalTheory.IndefiniteRowSideFullHecke.SourceLatticeInvariance.DegOneUnram P → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (f : (ι → E) → K) (N : ℕ), FunBdd P N f → ∀ (T : (ι → E) ≃ₗ[E] (ι → E)) (b : ι → E), ∃ A₀ B₀ : ℕ, ∀ A B : ℕ, A₀ ≤ A → B₀ ≤ B → (boxSum P A B (fun t => f (T t + b)) ≠ 0 ↔ boxSum P A B f ≠ 0) := by
  first | exact @GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | exact GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine | (intros; apply GlobalTheory.Proof.boxSum_ne_zero_invariant_affineChange.affine <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CoefInWeilOperatorTranslateAlgebraic
section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.CoefWop

lemma Hf_add_left (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T (a + b) w = Hf D T a w + Hf D T b w := by
  simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div]

lemma Hf_add_right (D : D7) (T : Tor D) {N N' : ℕ} (a b w : VC D N N') :
    Hf D T w (a + b) = Hf D T w a + Hf D T w b := by
  simp only [Hf, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib, add_div]

lemma Hf_nsmul (D : D7) (T : Tor D) {N N' : ℕ} (a b : ℕ) (y t : VC D N N') :
    Hf D T (a • y) (b • t) = (a * b : ℂ) * Hf D T y t := by
  simp only [Hf, Pi.smul_apply, nsmul_eq_mul, map_mul, map_natCast, mul_div_assoc', Finset.mul_sum]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma U_U (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (F : VC D N N' → ℂ) (z : VC D N N') :
    U D T y (U D T t F) z
      = Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) * U D T (y + t) F z := by
  simp only [U]
  rw [show z + y + t = z + (y + t) by abel]
  rw [mul_comm (Complex.exp _) (F _ * _), mul_assoc, mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  simp only [Hf_add_left, Hf_add_right]
  ring

lemma taylor_const_mul (D : D7) {N N' : ℕ} (c : ℂ) (G : VC D N N' → ℂ) (hG : ContDiff ℂ ⊤ G)
    (α : Mono D N N') : taylor D (fun z => c * G z) α = c * taylor D G α := by
  simp only [taylor]
  have h := iteratedFDeriv_const_smul_apply (𝕜 := ℂ) (i := (Finsupp.toMultiset α).card) (a := c) (x := (0 : VC D N N'))
    (hG.contDiffAt.of_le (by exact_mod_cast le_top))
  rw [show (fun z => c * G z) = c • G from rfl, h]
  rw [ContinuousMultilinearMap.smul_apply, smul_eq_mul, mul_div_assoc]

lemma contDiff_U (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (F : VC D N N' → ℂ)
    (hF : ContDiff ℂ ⊤ F) : ContDiff ℂ ⊤ (U D T x F) := by
  unfold U Hf
  apply ContDiff.mul
  · exact hF.comp (contDiff_id.add contDiff_const)
  · apply ContDiff.cexp
    apply ContDiff.sub _ contDiff_const
    apply ContDiff.mul contDiff_const
    apply ContDiff.div_const
    apply ContDiff.sum fun τ _ => ContDiff.sum fun i _ => ContDiff.sum fun j _ => ?_
    apply ContDiff.mul _ contDiff_const
    exact (contDiff_apply ℂ _ j).comp ((contDiff_apply ℂ _ i).comp (contDiff_apply ℂ _ τ))

lemma sq_one_alg {c : ℂ} {n : ℕ} (hn : 0 < n) (h : c ^ n = 1) : c ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  apply IsIntegral.isAlgebraic
  exact IsIntegral.of_pow hn (by rw [h]; exact isIntegral_one)

lemma Hf_swap (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') :
    Hf D T t y = (starRingEnd ℂ) (Hf D T y t) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_conj, Complex.conj_ofReal]
  congr 1
  refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => ?_
  ring

lemma wPh_sq (D : D7) (T : Tor D) {N N' : ℕ} (p : ℕ) (y : VC D N N') (m : ℤ) (hm : qH D T y = m) :
    wPh D T p y ^ 2 = 1 := by
  unfold wPh
  split_ifs with hp
  · rw [← Complex.exp_nat_mul, hm]
    have : ((2 : ℕ) : ℂ) * ((Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = (m : ℂ) * (2 * Real.pi * Complex.I) := by
      push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  · have hex : ∃ s : ℂ, ∃ k : ℕ, ∃ m' : ℤ, (p : ℝ) ^ k * qH D T y = m' ∧ s = (-1) ^ m' :=
      ⟨(-1) ^ m, 0, m, by simp [hm], rfl⟩
    obtain ⟨k, m', -, hs⟩ := Classical.epsilon_spec hex
    rw [hs, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul]
    norm_num

lemma root_alg (D : D7) (T : Tor D) {N N' : ℕ} (y t : VC D N N') (a b : ℕ) (ha : 0 < a) (hb : 0 < b) (k : ℤ)
    (hk : (Hf D T (a • y) (b • t)).im = k) :
    Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)) ∈ Qbar := by
  rw [Hf_nsmul] at hk
  have hk' : ((a * b : ℕ) : ℝ) * (Hf D T y t).im = k := by
    rw [← hk]; push_cast
    rw [show ((a : ℂ) * b) = (((a * b : ℝ)) : ℂ) by push_cast; ring, Complex.im_ofReal_mul]
  have hdiff : Hf D T y t - Hf D T t y = 2 * Complex.I * ((Hf D T y t).im : ℂ) := by
    rw [Hf_swap]
    apply Complex.ext <;> simp <;> ring
  apply sq_one_alg (n := 2 * (a * b)) (by positivity)
  rw [hdiff, ← Complex.exp_nat_mul]
  have : ((2 * (a * b) : ℕ) : ℂ) * (-(Real.pi : ℂ) * (2 * Complex.I * ((Hf D T y t).im : ℂ) / 2))
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) := by
    have hk'' : ((a * b : ℕ) : ℂ) * ((Hf D T y t).im : ℂ) = (k : ℂ) := by exact_mod_cast hk'
    push_cast at hk'' ⊢
    linear_combination (-(Real.pi : ℂ) * 2 * Complex.I) * hk''
  rw [this, Complex.exp_int_mul_two_pi_mul_I]

end GlobalTheory.CoefWop

namespace GlobalTheory


open GlobalTheory.CoefWop in
theorem coefIn_Wop_U_translate : ∀ (D : D7) (T : Tor D) (N N' : ℕ) (F : VC D N N' → ℂ) (Λ : AddSubgroup (VC D N N')) (p : ℕ) [Fact p.Prime] (y t : VC D N N'), ContDiff ℂ ⊤ F → (∀ s : VC D N N', (∃ a : ℕ, 0 < a ∧ a • s ∈ Λ) → CoefIn D (U D T s F) Qbar) → (∃ a : ℕ, 0 < a ∧ a • t ∈ Λ) → (∃ a : ℕ, 0 < a ∧ a • y ∈ Λ) → (∀ x ∈ Λ, ∀ x' ∈ Λ, ∃ k : ℤ, (Hf D T x x').im = k) → (∃ m : ℤ, qH D T y = m) → CoefIn D (Wop D T p y (U D T t F)) Qbar := by
  intro D T N N' F Λ p _ y t hF hΛ ⟨b, hb, hbt⟩ ⟨a, ha, hay⟩ hHf ⟨m, hm⟩
  have hfun : Wop D T p y (U D T t F)
      = fun z => (wPh D T p y * Complex.exp (-(Real.pi : ℂ) * ((Hf D T y t - Hf D T t y) / 2)))
          * U D T (y + t) F z := by
    funext z
    simp only [Wop, U_U]
    ring
  have hyt : CoefIn D (U D T (y + t) F) Qbar := by
    refine hΛ _ ⟨a * b, by positivity, ?_⟩
    rw [smul_add, mul_comm a b, mul_smul, mul_comm b a, mul_smul]
    exact Λ.add_mem (Λ.nsmul_mem hay b) (Λ.nsmul_mem hbt a)
  obtain ⟨k, hk⟩ := hHf _ hay _ hbt
  have hw : wPh D T p y ∈ Qbar := sq_one_alg (n := 2) (by norm_num) (wPh_sq D T p y m hm)
  unfold CoefIn
  intro α
  rw [hfun, taylor_const_mul D _ _ (contDiff_U D T _ F hF)]
  exact Qbar.mul_mem (Qbar.mul_mem hw (root_alg D T y t a b ha hb k hk)) (hyt α)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.EqOnPadicIntOfEqOnNaturalsMoment
section
noncomputable section
open NumberField Formalism.BasicNotions Classical Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.L2.Ker

namespace GlobalTheory.MomentPinned

theorem isLocallyConstant_toZModPow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    IsLocallyConstant (PadicInt.toZModPow (p := p) n) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have hq : (0 : ℝ) < (p : ℝ) ^ (-(n : ℤ)) := zpow_pos (by exact_mod_cast (Fact.out : p.Prime).pos) _
  filter_upwards [Metric.ball_mem_nhds x hq] with y hy
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, ← PadicInt.norm_le_pow_iff_mem_span_pow]
  rw [Metric.mem_ball, dist_eq_norm] at hy
  exact hy.le

theorem isLocallyConstant_red {p : ℕ} [Fact p.Prime] (r n : ℕ) :
    IsLocallyConstant (fun a : Fin r → ℤ_[p] => fun i => PadicInt.toZModPow n (a i)) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro x
  have : ∀ i, ∀ᶠ y in nhds x, PadicInt.toZModPow n (y i) = PadicInt.toZModPow n (x i) := fun i =>
    ((isLocallyConstant_toZModPow n).comp_continuous (continuous_apply i)).eventually_eq x
  filter_upwards [Filter.eventually_all.2 this] with y hy using funext hy

theorem continuous_zc {p : ℕ} [Fact p.Prime] : Continuous (JMB.zc : ℤ_[p] → ℂ_[p]) := by
  unfold JMB.zc
  exact (continuous_algebraMap ℚ_[p] ℂ_[p]).comp continuous_subtype_val

theorem continuous_pairD {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) {g : ℕ} (d : ℕ)
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (b : Fin r → Fin g → ℂ) (y : Fin g → ℂ) :
    Continuous (JMB.pairD lam Ω d Hm b y) := by
  unfold JMB.pairD
  have := continuous_zc (p := p)
  fun_prop

theorem continuous_charPart {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) {g : ℕ}
    (Hm : Matrix (Fin g) (Fin g) ℂ) {r : ℕ} (n : ℕ) (b : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) :
    Continuous fun a : Fin r → ℤ_[p] => JMB.lamA lam (JMB.kap Hm (JMB.vecA n b a) Y) :=
  ((isLocallyConstant_red (p := p) r n).comp (fun s : Fin r → ZMod (p ^ n) =>
    JMB.lamA lam (JMB.kap Hm (∑ i, (((s i).val : ℕ) : ℂ) • b i) Y))).continuous

theorem eq_of_natCast : ∀ (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (Ω : ℂ_[p]) (g : ℕ) (S : JMB.Setup g) (r n k : ℕ) (bS : Fin r → Fin g → ℂ) (Y : Fin g → ℂ) (ys : Fin k → Fin g → ℂ) (f : C(Fin r → ℤ_[p], ℂ_[p])), (∀ a : Fin r → ℕ, f (fun i => (a i : ℤ_[p])) = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS (fun i => (a i : ℤ_[p]))) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) (fun i => (a i : ℤ_[p]))) → ∀ a, f a = JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a := by
  intro p _ lam Ω g S r n k bS Y ys f h a
  have hR : Continuous fun a : Fin r → ℤ_[p] =>
      JMB.lamA lam (JMB.kap S.Hm (JMB.vecA n bS a) Y) * ∏ j, JMB.pairD lam Ω S.d S.Hm bS (ys j) a :=
    (continuous_charPart lam S.Hm n bS Y).mul
      (continuous_finsetProd Finset.univ fun j _ => continuous_pairD lam Ω S.d S.Hm bS (ys j))
  have hd : DenseRange (fun a : Fin r → ℕ => fun i => (a i : ℤ_[p])) :=
    DenseRange.piMap fun _ : Fin r => PadicInt.denseRange_natCast (p := p)
  exact congr_fun (hd.equalizer f.continuous hR (funext h)) a

end GlobalTheory.MomentPinned
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsAddEquivField
section
open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct

namespace GlobalTheory.OverResidue

theorem nonempty_equiv_quot {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R)
    (hI : I.IsMaximal) (T : ℕ) (hT : T.Prime) (hc : Nat.card M = T)
    (h0 : ∀ a ∈ I, ∀ m : M, a • m = 0) : Nonempty (M ≃ₗ[R] (R ⧸ I)) := by
  have : Fact T.Prime := ⟨hT⟩
  have : Finite M := Nat.finite_of_card_ne_zero (hc ▸ hT.ne_zero)
  have : Nontrivial M := Finite.one_lt_card_iff_nontrivial.1 (hc ▸ hT.one_lt)
  obtain ⟨m₀, hm₀⟩ := exists_ne (0 : M)
  let f : R →ₗ[R] M := LinearMap.toSpanSingleton R M m₀
  have hsur : Function.Surjective f := by
    intro m
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.1 (mem_zmultiples_of_prime_card hc hm₀ (g' := m))
    exact ⟨(n : R), by simp [f, Int.cast_smul_eq_zsmul]⟩
  have hker : I = LinearMap.ker f := by
    refine hI.eq_of_le ?_ fun a ha => h0 a ha m₀
    rw [Ideal.ne_top_iff_one]
    simpa [f] using hm₀
  subst hker
  exact ⟨(f.quotKerEquivOfSurjective hsur).symm⟩

theorem exists_addEquiv_field {R M k : Type} [CommRing R] [AddCommGroup M] [Module R M] [Field k]
    (ρ : R →+* k) (hρ : Function.Surjective ρ) (e : M ≃ₗ[R] (R ⧸ RingHom.ker ρ)) :
    ∃ ε : M ≃+ k, ∀ (a : R) (m : M), ε (a • m) = ρ a * ε m := by
  refine ⟨e.toAddEquiv.trans (RingHom.quotientKerEquivOfSurjective hρ).toAddEquiv, fun a m => ?_⟩
  show RingHom.quotientKerEquivOfSurjective hρ (e (a • m)) =
      ρ a * RingHom.quotientKerEquivOfSurjective hρ (e m)
  rw [map_smul, Algebra.smul_def, map_mul]
  rfl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {v : HeightOneSpectrum (𝓞 F)}

theorem exists_red (p : E ⊗[F] v.adicCompletion F →+* v.adicCompletion F)
    (hp : ∀ x ∈ intV E v, p x ∈ v.adicCompletionIntegers F)
    (hsur : ∀ a ∈ v.adicCompletionIntegers F, ∃ x ∈ intV E v, p x = a) :
    ∃ ρ : intV E v →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F),
      Function.Surjective ρ ∧ primeOf p = RingHom.ker ρ ∧
      (∀ a : intV E v, a ∈ RingHom.ker ρ ↔ Valued.v (p a) < 1) ∧
      ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = p a →
        ρ a = IsLocalRing.residue _ a' := by
  let q : intV E v →+* v.adicCompletionIntegers F :=
    (p.comp (intV E v).subtype).codRestrict (v.adicCompletionIntegers F) fun x => hp x x.2
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx, hxa⟩ := hsur a a.2
    exact ⟨⟨x, hx⟩, Subtype.ext hxa⟩
  have hk : ∀ a : intV E v, a ∈ RingHom.ker ((IsLocalRing.residue _).comp q) ↔
      Valued.v (p a) < 1 := by
    intro a
    rw [RingHom.mem_ker, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    exact Valuation.mem_maximalIdeal_iff (v := Valued.v) (a := q a)
  refine ⟨(IsLocalRing.residue _).comp q, IsLocalRing.residue_surjective.comp hq, ?_, hk, ?_⟩
  · apply le_antisymm
    · rw [primeOf, Ideal.span_le]
      exact fun a ha => (hk a).2 ha
    · exact fun a ha => Ideal.subset_span ((hk a).1 ha)
  · intro a a' h
    have : q a = a' := Subtype.ext h.symm
    rw [RingHom.comp_apply, this]

theorem residue_of_prime_card : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (s : E ⊗[F] v.adicCompletion F ≃+* v.adicCompletion F × v.adicCompletion F), IsSplitting σ v s → ∀ (M : Type) [AddCommGroup M] [Module (intV E v) M] (T : ℕ), T.Prime → Nat.card M = T → (∀ (a : intV E v) (m : M), Valued.v (prP s a) < 1 → a • m = 0) → (∃ ε : M ≃+ IsLocalRing.ResidueField (v.adicCompletionIntegers F), ∀ (a : intV E v) (a' : v.adicCompletionIntegers F), (a' : v.adicCompletion F) = prP s a → ∀ m, ε (a • m) = a' • ε m) ∧ Nonempty (M ≃ₗ[intV E v] (intV E v ⧸ primeOf (prP s))) ∧ Nat.card (intV E v ⧸ primeOf (prPbar s)) = T := by
  intro F E _ _ _ _ _ σ v s hs M _ _ T hT hc h0
  obtain ⟨ρ, hρ, hρk, hρm, hρa⟩ := exists_red (prP s) (fun x hx => ((hs.2.2 x).1 hx).1)
    (GlobalTheory.OverCompare.sur_prP hs)
  obtain ⟨ρ', hρ', hρk', -, -⟩ := exists_red (prPbar s) (fun x hx => ((hs.2.2 x).1 hx).2)
    (GlobalTheory.OverCompare.sur_prPbar hs)
  rw [hρk, hρk']
  obtain ⟨e⟩ := nonempty_equiv_quot (M := M) (RingHom.ker ρ) (RingHom.ker_isMaximal_of_surjective ρ hρ)
    T hT hc fun a ha m => h0 a m ((hρm a).1 ha)
  obtain ⟨ε, hε⟩ := exists_addEquiv_field ρ hρ e
  refine ⟨⟨ε, fun a a' h m => ?_⟩, ⟨e⟩, ?_⟩
  · rw [hε, hρa a a' h]
    rfl
  · rw [Nat.card_congr (RingHom.quotientKerEquivOfSurjective hρ').toEquiv, ← hc]
    exact (Nat.card_congr ε.toEquiv).symm

end GlobalTheory.OverResidue
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LocalUnfoldingIntegrandBoundedSchwartzStatement
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localUnfoldingIntegrand_boundedSchwartz : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (n' c' n c : ℕ) (psi : E → K) (D N : ℕ) (Psi : Loc.SF E K (n' + c') (n + c)), N ≤ D → CharTo P D psi → HomBdd P N Psi → ∀ xj : (Fin n' → E) →ₗ[E] (Fin n → E), FunBdd P N (integrand psi Psi xj) ∧ ∀ t : Loc.FC n' c' n c → E, Psi (Loc.xx1 xj t) ≠ 0 → IntAt P ((qOf P : E) ^ N * Loc.chArg (Loc.xx1 xj t)) := by
  first | exact @GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | exact GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd | (intros; apply GlobalTheory.Proof.localUnfoldingIntegrand_boundedSchwartz.integrand_bdd <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MulVecMemLocLatIffOfFrame
section
namespace GlobalTheory.OverCompare

open NumberField IsDedekindDomain Matrix Formalism.UG Formalism.BasicNotions GlobalTheory.IndefiniteRowSideFullHecke.SplittingProjection
open scoped TensorProduct


open NumberField IsDedekindDomain Matrix in
open scoped TensorProduct in
theorem _root_.GlobalTheory.OverCompare.exists_intV_mul_inclE_eq_one {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] (v : HeightOneSpectrum (𝓞 F)) (c : 𝓞 F) (hc : c ∉ v.asIdeal) :
    ∃ u ∈ _root_.Formalism.BasicNotions.intV E v, u * _root_.Formalism.UG.inclE (F := F) (v.adicCompletion F) (algebraMap F E (c : F)) = 1 := by
  have hc0 : (c : F) ≠ 0 := by
    intro h
    apply hc
    rw [show c = 0 from RingOfIntegers.coe_eq_zero_iff.mp h]
    exact v.asIdeal.zero_mem
  have hmem : algebraMap F (v.adicCompletion F) (c : F)⁻¹ ∈ v.adicCompletionIntegers F := by
    rw [_root_.GlobalTheory.LocalLattice.algebraMap_mem_adicCompletionIntegers_iff,
      _root_.GlobalTheory.LocalLattice.mem_localRing_iff]
    refine ⟨c, hc, ?_⟩
    rw [Algebra.smul_def, show algebraMap (𝓞 F) F c = (c : F) from rfl, mul_inv_cancel₀ hc0]
    exact Submodule.mem_one.mpr ⟨1, map_one _⟩
  refine ⟨1 ⊗ₜ[F] algebraMap F (v.adicCompletion F) (c : F)⁻¹, ?_, ?_⟩
  · unfold _root_.Formalism.BasicNotions.intV _root_.Formalism.UG.tensInt _root_.Formalism.UG.intOE
    exact Subring.subset_closure (Or.inr ⟨⟨_, hmem⟩, rfl⟩)
  · unfold _root_.Formalism.UG.inclE
    rw [Algebra.TensorProduct.includeLeftRingHom_apply, ← Algebra.TensorProduct.algebraMap_apply,
      ← Algebra.TensorProduct.algebraMap_apply', ← map_mul, inv_mul_cancel₀ hc0, map_one]

end GlobalTheory.OverCompare
end

