module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0006
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Formalism.HarderNarasimhan.ShiftInvariance
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalIntegralLiftOfOrthogon
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsStabilizerNilradicalLiftOfIsotropic
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0137
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0170
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0135
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DiscriminantOrderCommonFixedLatticeEmbeddedData
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0177
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0183
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SigmaFiniteOfRealSmul
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.NilradicalFirstLayerCoveringRadiusLe
section
open GlobalTheory.Count GlobalTheory.IndefiniteRowSideFullHecke.CenteredPerpendicularSets Formalism.MainNotions.S Formalism.HN Formalism.REAL Matrix NumberField Finset

noncomputable section

namespace GlobalTheory.Count.FirstLayer

theorem inNil_sub {A : Type} [CommRing A] {n : ℕ} (s : A →+* A) (J : Matrix (Fin n) (Fin n) A)
    (W : Submodule A (Fin n → A)) (Y Y' : Matrix (Fin n) (Fin n) A)
    (h : InNil s J W Y) (h' : InNil s J W Y') : InNil s J W (Y - Y') := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨g1, g2, g3, g4⟩ := h'
  have l1 : ∀ a b c : Fin n → A, Formalism.UG.hform s J (a - b) c = Formalism.UG.hform s J a c - Formalism.UG.hform s J b c := by
    intro a b c
    simp [Formalism.UG.hform, sub_mul, Finset.sum_sub_distrib]
  have l2 : ∀ a b c : Fin n → A, Formalism.UG.hform s J c (a - b) = Formalism.UG.hform s J c a - Formalism.UG.hform s J c b := by
    intro a b c
    simp [Formalism.UG.hform, mul_sub, Finset.sum_sub_distrib]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u u'
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, l1, l2]
    have a := h1 u u'
    have b := g1 u u'
    linear_combination a - b
  · intro u w hw
    rw [Matrix.sub_mulVec, l2, h2 u w hw, g2 u w hw, sub_zero]
  · intro u hu
    rw [Matrix.sub_mulVec]
    exact W.sub_mem (h3 u hu) (g3 u hu)
  · intro u hu
    rw [Matrix.sub_mulVec, h4 u hu, g4 u hu, sub_zero]

theorem map_mulVec_emb (I : AutInst) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) I.E)
    (y : Fin I.n → I.E) :
    M.map (I.φ v) *ᵥ (fun i => I.φ v (y i)) = fun i => I.φ v ((M *ᵥ y) i) := by
  funext i
  rw [RingHom.map_mulVec]
  rfl

theorem mem_spanAt (I : AutInst) (v : InfinitePlace I.F) (R : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (y : Fin I.n → I.E) (hy : y ∈ R) : (fun i => I.φ v (y i)) ∈ spanAt I R v :=
  Submodule.subset_span ⟨y, hy, rfl⟩

theorem mulVec_mem_of_span (I : AutInst) (v : InfinitePlace I.F) (A : Submodule (𝓞 I.E) (Fin I.n → I.E))
    (M : Matrix (Fin I.n) (Fin I.n) ℂ) (W : Submodule ℂ (Fin I.n → ℂ))
    (h : ∀ y ∈ A, M *ᵥ (fun i => I.φ v (y i)) ∈ W) : ∀ u ∈ spanAt I A v, M *ᵥ u ∈ W := by
  have : spanAt I A v ≤ W.comap (Matrix.mulVecLin M) := by
    unfold spanAt
    rw [Submodule.span_le]
    rintro _ ⟨y, hy, rfl⟩
    exact h y hy
  intro u hu
  exact this hu

theorem frame_inv (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) (M : Matrix (Fin I.n) (Fin I.n) ℂ) :
    uMat (x.1 v)⁻¹ * (I.P v)⁻¹ * M * I.P v * uMat (x.1 v) =
      (I.P v * uMat (x.1 v))⁻¹ * M * (I.P v * uMat (x.1 v)) := by
  rw [Matrix.mul_inv_rev]
  have : uMat (x.1 v)⁻¹ = (uMat (x.1 v))⁻¹ := by
    simp only [uMat, Subgroup.coe_inv, Matrix.coe_units_inv]
  rw [this]
  simp only [Matrix.mul_assoc]

theorem frame_det (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    IsUnit (I.P v * uMat (x.1 v)).det := by
  rw [← Matrix.isUnit_iff_isUnit_det]
  exact (I.P_unit v).mul (Units.isUnit _)

theorem frame_spec (I : AutInst) (x : I.GA) (v : InfinitePlace I.F) :
    (I.P v * uMat (x.1 v))ᴴ * I.J.map (I.φ v) * (I.P v * uMat (x.1 v)) = Jm (I.ε v) := by
  have h : (uMat (x.1 v))ᴴ * Jm (I.ε v) * uMat (x.1 v) = Jm (I.ε v) := (x.1 v).2
  rw [← h, ← I.P_spec v, Matrix.conjTranspose_mul]
  simp only [Matrix.mul_assoc]

theorem arith (n f k j rd lo hi rho : ℝ) (hf : 0 < f) (hrd : 0 ≤ rd) (hkj : k + j = n) (hlo : 0 < lo)
    (hhi : 0 < hi) (hr : hi ≤ rho * lo) :
    Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) ≤
      (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) := by
  have h1 : (k - j) * j ≤ n ^ 2 / 8 := by
    rw [← hkj]; nlinarith [sq_nonneg (k - 3 * j)]
  have h2 : hi / lo ≤ rho := by rwa [div_le_iff₀ hlo]
  have h3 : 0 < hi / lo := div_pos hhi hlo
  have hs : 0 < Real.sqrt (2 * f) := Real.sqrt_pos.2 (by linarith)
  have e : Real.sqrt 2 * Real.sqrt f = Real.sqrt (2 * f) := (Real.sqrt_mul (by norm_num) f).symm
  have e2 : Real.sqrt (2 * f) * Real.sqrt (2 * f) = 2 * f := Real.mul_self_sqrt (by linarith)
  have e3 : (n ^ 2 * f) / 8 * rd * rho / Real.sqrt (2 * f) =
      n ^ 2 / 8 * rho * (Real.sqrt (2 * f) * rd / 2) := by
    rw [div_eq_iff hs.ne']
    linear_combination (-(n ^ 2 / 8 * rho * rd / 2)) * e2
  have e4 : Real.sqrt 2 * ((k - j) * j * Real.sqrt f * rd * hi / (2 * lo)) =
      (k - j) * j * (hi / lo) * (Real.sqrt (2 * f) * rd / 2) := by
    rw [← e]; field_simp
  rw [e3, e4]
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  calc (k - j) * j * (hi / lo) ≤ n ^ 2 / 8 * (hi / lo) := mul_le_mul_of_nonneg_right h1 h3.le
    _ ≤ n ^ 2 / 8 * rho := mul_le_mul_of_nonneg_left h2 (by positivity)

theorem main : ∀ (I : AutInst) (x : I.GA) (R : Submodule (𝓞 I.E) (Fin I.n → I.E)) (lo hi rho : ℝ), IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) R → R ≤ perpIn I x R → 0 < hi → largestSize (bas I) (frm I x) R ≤ hi → (∀ N, R < N → N ≤ lamX I x → lo ≤ sizeQ (bas I) (frm I x) N R) → 0 < lo → hi ≤ rho * lo → ∀ Y ∈ nilReal I R, ∃ Y₀ ∈ nilInt I x R, ∃ Z ∈ cenReal I R, normAt I x (Y - diagEmb I Y₀ - Z) ≤ ((I.n : ℝ) ^ 2 * I.f) / 8 * I.rd * rho / Real.sqrt (2 * I.f) := by
  intro I x R lo hi rho hsat hiso hhi hlarge hlow hlo hr Y hY
  have hpl : perpIn I x R ≤ lamX I x := by
    unfold perpIn
    rw [Submodule.span_le]
    exact fun y hy => hy.1
  have hfg : (lamX I x).FG := (GlobalTheory.T.autPointLatticeIntersection_selfDual_properties I x).2.1
  have hsat' : IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (perpIn I x R) R := by
    refine ⟨hiso, ?_, ?_⟩
    · rintro _ ⟨y, hy, rfl⟩
      exact ⟨y, hiso hy, rfl⟩
    · rintro _ ⟨y, hy, rfl⟩ hz
      exact hsat.2.2 _ ⟨y, hpl hy, rfl⟩ hz
  obtain ⟨-, -, hperp, hnil, -⟩ := _root_.GlobalTheory.RealSpan.spanAt_properties I x R
  have hP : ∀ v u, u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) ↔
      u ∈ spanAt I (perpIn I x R) v := by
    intro v u
    rw [← hperp v]; rfl
  have hmono : ∀ v, spanAt I R v ≤ spanAt I (perpIn I x R) v := fun v =>
    Submodule.span_mono (Set.image_mono hiso)
  obtain ⟨Φ, hΦ0, hΦ1, D, hD, hDn⟩ := _root_.GlobalTheory.Count.SubquotFrame.subquot_frame I x (perpIn I x R) R R lo hi (hfg.of_le hpl) hsat'
    (hfg.of_le hsat.1) hlo hhi (fun N h1 h2 => hlow N h1 (h2.trans hpl)) hlarge Y
    (fun v y hy => (hY v).2.2.2 _ (mem_spanAt I v R y hy))
    (fun v y hy => (hY v).2.2.1 _ ((hP v _).2 (mem_spanAt I v _ y hy)))
  obtain ⟨Y₀, hY₀, hY₀Φ⟩ := _root_.GlobalTheory.NilLift.exists_nilInt_lift I x R hiso Φ hΦ0 hΦ1
  have hA : ∀ v, ∃ A : Matrix (Fin I.n) (Fin I.n) ℂ,
      InNil (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v) A ∧
      (∀ u ∈ perpSet (starRingEnd ℂ) (I.J.map (I.φ v)) (spanAt I R v), A *ᵥ u = D v *ᵥ u) ∧
      hs ((I.P v * uMat (x.1 v))⁻¹ * A * (I.P v * uMat (x.1 v))) ≤
        2 * hs ((I.P v * uMat (x.1 v))⁻¹ * D v * (I.P v * uMat (x.1 v))) := by
    intro v
    refine _root_.GlobalTheory.NilLift.exists_lift I.n (I.ε v) _ _ (D v) _ (frame_det I x v) (frame_spec I x v)
      (fun u hu => (hP v u).2 (hmono v hu)) ?_ ?_
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
        refine mulVec_mem_of_span I v R _ ⊥ ?_ u hu
        intro y hy
        rw [map_mulVec_emb, hΦ0 y hy, Submodule.mem_bot]
        funext i; simp
      rw [hD v u (hmono v hu), Matrix.sub_mulVec, (hY v).2.2.2 u hu, (Submodule.mem_bot ℂ).1 h0, sub_zero]
    · intro u hu
      have h0 : Φ.map (I.φ v) *ᵥ u ∈ spanAt I R v := by
        refine mulVec_mem_of_span I v _ _ _ ?_ u ((hP v u).1 hu)
        intro y hy
        rw [map_mulVec_emb]
        exact mem_spanAt I v R _ (hΦ1 y hy)
      rw [hD v u ((hP v u).1 hu), Matrix.sub_mulVec]
      exact Submodule.sub_mem _ ((hY v).2.2.1 u hu) h0
  choose A hA1 hA2 hA3 using hA
  refine ⟨Y₀, hY₀, Y - diagEmb I Y₀ - A, ?_, ?_⟩
  · intro v
    refine ⟨inNil_sub _ _ _ _ _ (inNil_sub _ _ _ _ _ (hY v) (hnil Y₀ hY₀.1 v)) (hA1 v), ?_⟩
    intro u hu
    have h0 : (Y₀.map (I.φ v) - Φ.map (I.φ v)) *ᵥ u ∈ (⊥ : Submodule ℂ (Fin I.n → ℂ)) := by
      refine mulVec_mem_of_span I v _ _ ⊥ ?_ u ((hP v u).1 hu)
      intro y hy
      rw [Matrix.sub_mulVec, map_mulVec_emb, map_mulVec_emb, hY₀Φ y hy, sub_self]
      exact Submodule.zero_mem _
    rw [Submodule.mem_bot, Matrix.sub_mulVec, sub_eq_zero] at h0
    show (Y v - Y₀.map (I.φ v) - A v) *ᵥ u = 0
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, hA2 v u hu, hD v u ((hP v u).1 hu), Matrix.sub_mulVec, h0,
      sub_self]
  · rw [sub_sub_cancel]
    have hAD : normAt I x A ≤ Real.sqrt 2 * normAt I x D := by
      unfold normAt
      rw [← Real.sqrt_mul (by norm_num), Finset.mul_sum]
      apply Real.sqrt_le_sqrt
      apply Finset.sum_le_sum
      intro v _
      rw [frame_inv, frame_inv]
      exact hA3 v
    have hrk : rkK (perpIn I x R) + rkK R = I.n :=
      ((_root_.GlobalTheory.Count.PerpStep.main I x).2.2.2 R R hsat hsat le_rfl).2.1
    have hf : (0 : ℝ) < I.f := by
      have : 0 < I.f := Module.finrank_pos
      exact_mod_cast this
    have hrd : 0 ≤ I.rd := Real.rpow_nonneg (abs_nonneg _) _
    refine hAD.trans ((mul_le_mul_of_nonneg_left hDn (Real.sqrt_nonneg _)).trans ?_)
    exact arith _ _ _ _ _ _ _ _ hf hrd (by exact_mod_cast hrk) hlo hhi hr

end GlobalTheory.Count.FirstLayer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.PairsIsometryNoFixedVectorCountBound
section
open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.PairNoFix

theorem encard_le_of_fibres {α β : Type} (S : Set α) (T : Set β) (f : α → β) (hf : ∀ a ∈ S, f a ∈ T)
    (c : ℝ≥0∞) (hc : ∀ b ∈ T, ((({a ∈ S | f a = b}).encard : ℕ∞) : ℝ≥0∞) ≤ c) :
    ((S.encard : ℕ∞) : ℝ≥0∞) ≤ ((T.encard : ℕ∞) : ℝ≥0∞) * c := by
  rw [← ENNReal.tsum_set_one S, ← ENNReal.tsum_set_const,
    ← ENNReal.tsum_fiberwise (fun _ : S => (1 : ℝ≥0∞)) (fun a : S => (⟨f a, hf a a.2⟩ : T))]
  refine ENNReal.tsum_le_tsum fun b => ?_
  rw [ENNReal.tsum_set_one]
  refine le_trans ?_ (hc b b.2)
  rw [← (Subtype.val_injective.encard_image _)]
  refine ENat.toENNReal_le.2 (Set.encard_le_encard ?_)
  rintro _ ⟨a, ha, rfl⟩
  exact ⟨a.2, congrArg Subtype.val ha⟩

theorem arith (k f : ℕ) (c e : ℝ) (hc : 0 ≤ c) (x x' D q A : ℝ) (hx : 1 ≤ x) (hx' : 1 ≤ x') (hD : 1 ≤ D)
    (hq : 0 < q) (hA : 0 ≤ A) (h : 1 ≤ q ^ (2 * k * f) * D * x * x') (m : ℕ) (hm : (m : ℝ) = e) :
    (x ^ ((k : ℝ) + c) * (x * D) ^ m) * (x' ^ ((k : ℝ) + c) * (x' * D) ^ m) * A ^ (4 * k * f) ≤
      (x * x') ^ ((k : ℝ) / 2) * (x * x' * D ^ 2) ^ (c + e) * (q ^ (k * f) * A ^ (4 * f) * D * x * x') ^ k := by
  subst hm
  have x0 : 0 < x := by linarith
  have x0' : 0 < x' := by linarith
  have D0 : 0 < D := by linarith
  have h1 : 1 ≤ (x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k := by
    have hs : ((x * x') ^ ((k : ℝ) / 2)) ^ 2 = (x * x') ^ k := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast]
      congr 1; push_cast; ring
    have h2 : 1 ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) ^ 2 := by
      rw [mul_pow, hs]
      have : (x * x') ^ k * ((q ^ (k * f) * D) ^ k) ^ 2 = (q ^ (2 * k * f) * D * x * x') ^ k * D ^ k := by
        ring
      rw [this]
      exact one_le_mul_of_one_le_of_one_le (one_le_pow₀ h) (one_le_pow₀ hD)
    exact (one_le_sq_iff₀ (by positivity)).1 h2
  have h3 : x ^ c * x' ^ c ≤ (x * x' * D ^ 2) ^ c := by
    rw [← Real.mul_rpow x0.le x0'.le]
    refine Real.rpow_le_rpow (by positivity) ?_ hc
    exact le_mul_of_one_le_right (by positivity) (one_le_pow₀ hD)
  rw [Real.rpow_add x0, Real.rpow_add x0', Real.rpow_add (by positivity : 0 < x * x' * D ^ 2)]
  simp only [Real.rpow_natCast]
  calc x ^ k * x ^ c * (x * D) ^ m * (x' ^ k * x' ^ c * (x' * D) ^ m) * A ^ (4 * k * f)
      = 1 * (x ^ c * x' ^ c) * ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by ring
    _ ≤ ((x * x') ^ ((k : ℝ) / 2) * (q ^ (k * f) * D) ^ k) * (x * x' * D ^ 2) ^ c *
        ((x * x' * D ^ 2) ^ m * (A ^ (4 * f) * x * x') ^ k) := by gcongr
    _ = _ := by ring

theorem main : MinkowskiBound → ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : Formalism.HermitianLatticeCounting.S6.HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → GlobalTheory.Mass.PD H.B.flip → ∀ (L₀ : Submodule (𝓞 K) V) (g j D₀ : ℕ), GlobalTheory.Mass.IsIntLat H.B.flip L₀ → GlobalTheory.Mass.discN H.B.flip L₀ = D₀ → GenBy (Formalism.HermitianLatticesTheory.dual H.B.flip L₀) L₀ 1 → 2 ≤ g → ∀ (x x' : ℕ), 1 ≤ x → 1 ≤ x' → ((({p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}).encard : ℕ∞) : ℝ≥0∞) ≤ ENNReal.ofReal (((x : ℝ) * x') ^ (((Module.finrank K V) : ℝ) / 2) * ((x : ℝ) * x' * (D₀ : ℝ) ^ 2) ^ (cf K + 3 * (2 * j + 1)) * ((2 / (g : ℝ)) ^ ((Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)) * ((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ) ^ (4 * (Formalism.HermitianLatticesTheory.fDeg K)) * D₀ * x * x') ^ (Module.finrank K V)) := by
  intro hM K V _ _ _ _ _ _ _ _ H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx'
  rcases Set.eq_empty_or_nonempty {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥} with he | ⟨p₀, hp₀, hfix⟩
  · rw [he]; simp
  have h43 := _root_.GlobalTheory.DegCnt.FixDisc.main K V H hK hPD L₀ g j D₀ hL hD hG hg x x' hx hx' p₀ hp₀
  rw [hfix] at h43
  have hone : GlobalTheory.Mass.discN (GlobalTheory.Mass.hRes H.B.flip (⊥ : Submodule K V))
      (GlobalTheory.Mass.latIn ⊥ (fixLat p₀.1.2)) = 1 := by
    unfold GlobalTheory.Mass.discN GlobalTheory.Mass.idxN
    rw [AddSubgroup.relIndex_eq_one]
    intro y _
    rw [Subsingleton.elim y 0]
    exact zero_mem _
  rw [hone, finrank_bot, Nat.sub_zero, Nat.cast_one] at h43
  have hD1 : 1 ≤ D₀ := by
    rcases Nat.eq_zero_or_pos D₀ with h | h
    · rw [h] at h43; norm_num at h43
    · exact h
  have hcf : 0 ≤ cf K := by
    unfold cf
    have : (1 : ℝ) ≤ Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
    have := Real.logb_nonneg (b := 2) (by norm_num) this
    linarith
  have hA := _root_.GlobalTheory.DegCnt.encard_isDat_le K V H hK hPD L₀ g j D₀ hL hD hG hg x hx
  have hB := _root_.GlobalTheory.DegCnt.encard_isDat_le K V H hK hPD L₀ g j D₀ hL hD hG hg x' hx'
  have hcnt := encard_le_of_fibres {p ∈ Trip H g L₀ j x x' | fixSp p.2.2 = ⊥}
    ({d | IsDat H g L₀ j x d} ×ˢ {d | IsDat H g L₀ j x' d}) (fun p => (p.1, p.2.1))
    (fun p hp => ⟨hp.1.1, hp.1.2.1⟩)
    (((4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K) : ℕ) : ℝ≥0∞) ^ (4 * (Module.finrank K V) * (Formalism.HermitianLatticesTheory.fDeg K)))
    (by
      rintro ⟨d, d'⟩ ⟨hd, hd'⟩
      have h := _root_.GlobalTheory.IsoCount.isoCnt hM K V H hK hPD ⊥ d'.1 d.1 hd'.1.1 hd.1.1
      rw [finrank_bot, Nat.sub_zero] at h
      refine le_trans (ENat.toENNReal_le.2 ?_) h
      refine Set.encard_le_encard_of_injOn (f := fun p => p.2.2) ?_ ?_
      · rintro ⟨a, b, η⟩ ⟨⟨hp, -⟩, he⟩
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        refine ⟨hp.2.2.1, hp.2.2.2.1, ?_⟩
        intro y hy
        rw [(Submodule.mem_bot K).1 hy, map_zero]
      · rintro ⟨a, b, η⟩ ⟨-, he⟩ ⟨a', b', η'⟩ ⟨-, he'⟩ hη
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
        obtain ⟨rfl, rfl⟩ := Prod.mk.inj he'
        simp only at hη
        rw [hη])
  rw [Set.encard_prod, ENat.toENNReal_mul] at hcnt
  refine hcnt.trans ((mul_le_mul_left (mul_le_mul' hA hB) _).trans ?_)
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hg0 : (0 : ℝ) < g := by exact_mod_cast (by omega : 0 < g)
  exact arith _ _ _ _ hcf _ _ _ _ _ (by exact_mod_cast hx) (by exact_mod_cast hx') (by exact_mod_cast hD1)
    (by positivity) (by positivity) h43 _ (by push_cast; ring)

end GlobalTheory.PairNoFix
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.ProdLayerHeightQuotientsEqSq
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.HtProd

theorem prod_shift_eq (N : ℕ) (F : ℕ → ℕ → ℝ) (hF : ∀ b b', N ≤ b' → F b b' = 1) :
    ∏ c ∈ Finset.range N, ∏ b ∈ Finset.range N, F b (b + c + 1) =
      ∏ b ∈ Finset.range N, ∏ b' ∈ Finset.range N, if b < b' then F b b' else 1 := by
  rw [Finset.prod_comm]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [← Finset.prod_filter]
  have h1 : ∏ c ∈ Finset.range N, F b (b + c + 1) = ∏ x ∈ Finset.Ico (b + 1) (b + 1 + N), F b x := by
    rw [Finset.prod_Ico_eq_prod_range]
    simp only [Nat.add_sub_cancel_left]
    refine Finset.prod_congr rfl fun c _ => ?_
    congr 1
    omega
  rw [h1]
  symm
  apply Finset.prod_subset
  · intro x hx
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx ⊢
    omega
  · intro x hx hx'
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hx hx'
    exact hF _ _ (by omega)

theorem prod_range_split (a : ℕ) (g : ℕ → ℝ) :
    ∏ b ∈ Finset.range (2 * a + 1), g b = (∏ i : Fin a, g i) * g a * ∏ i : Fin a, g (2 * a - i) := by
  have e : 2 * a + 1 = (a + 1) + a := by omega
  rw [e, Finset.prod_range_add, Finset.prod_range_succ, Fin.prod_univ_eq_prod_range g a,
    Fin.prod_univ_eq_prod_range (fun i => g (2 * a - i)) a, ← Finset.prod_range_reflect (fun i => g (2 * a - i)) a]
  congr 1
  refine Finset.prod_congr rfl fun x hx => ?_
  rw [Finset.mem_range] at hx
  congr 1
  omega

theorem prod_symm_split {a : ℕ} (P : Fin a → Fin a → ℝ) (hP : ∀ i k, P i k = P k i) :
    ∏ i, ∏ k, P i k = (∏ i, ∏ k, if i < k then P i k else 1) ^ 2 * ∏ i, P i i := by
  have h1 : ∀ i k, P i k = (if i < k then P i k else 1) * (if k < i then P k i else 1) *
      (if i = k then P i k else 1) := by
    intro i k
    rcases lt_trichotomy i k with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · simp [h]
    · simp [h, h.ne', not_lt.mpr h.le, hP i k]
  rw [Finset.prod_congr rfl fun i _ => Finset.prod_congr rfl fun k _ => h1 i k]
  simp only [Finset.prod_mul_distrib]
  rw [Finset.prod_comm (f := fun i k => if k < i then P k i else 1), sq]
  simp

theorem htProd : ∀ (n f a : ℕ) (j : Fin a → ℕ) (r : ℕ → ℕ) (τ : Fin a → ℝ) (h : ℕ → ℝ),
    (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) → r a = n - 2 * ∑ i, j i →
    (∀ b, 2 * a + 1 ≤ b → r b = 0) →
    (∀ i : Fin a, 0 < τ i ∧ h i = τ i ^ (2 * f * j i) ∧ h (2 * a - i) = (τ i ^ (2 * f * j i))⁻¹) →
    h a = 1 → (∀ b, 2 * a + 1 ≤ b → h b = 1) →
    ∏ c ∈ Finset.range (2 * a + 1), ∏ b ∈ Finset.range (2 * a + 1),
      h b ^ r (b + c + 1) / h (b + c + 1) ^ r b = layerProd n f j τ id ^ 2 := by
  intro n f a j r τ h hr hra hr0 hτ ha h1
  rw [prod_shift_eq (2 * a + 1) (fun b b' => h b ^ r b' / h b' ^ r b)
    (fun b b' hb => by simp [hr0 b' hb, h1 b' hb])]
  unfold layerProd
  rw [← hra]
  simp only [prod_range_split, id]
  have c1 : ∀ i : Fin a, (i : ℕ) < a := fun i => i.2
  have c2 : ∀ i k : Fin a, (i : ℕ) < 2 * a - k := fun i k => by omega
  have c3 : ∀ k : Fin a, ¬ a < (k : ℕ) := fun k => by omega
  have c4 : ∀ k : Fin a, a < 2 * a - k := fun k => by omega
  have c5 : ∀ i k : Fin a, ¬ 2 * a - i < (k : ℕ) := fun i k => by omega
  have c6 : ∀ i : Fin a, ¬ 2 * a - i < a := fun i => by omega
  have c7 : ∀ i k : Fin a, (2 * a - i < 2 * a - k) ↔ k < i := fun i k => by
    rw [Fin.lt_def]; omega
  have c8 : ∀ i k : Fin a, ((i : ℕ) < k) ↔ i < k := fun i k => Iff.rfl
  simp only [c1, c2, c3, c4, c5, c6, c7, c8, lt_irrefl, if_true, if_false, ha,
    fun i => (hr i).1, fun i => (hr i).2, fun i => (hτ i).2.1, fun i => (hτ i).2.2,
    Finset.prod_const_one, one_mul, mul_one, one_pow, div_one, Finset.prod_mul_distrib,
    Finset.prod_filter]
  have d1 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k)) ^ j i =
      (τ i / τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [div_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d2 : ∀ i k : Fin a, (τ i ^ (2 * f * j i)) ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ i * τ k) ^ (2 * j i * j k * f) := fun i k => by
    rw [inv_pow, div_inv_eq_mul, mul_pow, ← pow_mul, ← pow_mul]
    congr 2 <;> ring
  have d3 : ∀ i k : Fin a, (τ i ^ (2 * f * j i))⁻¹ ^ j k / (τ k ^ (2 * f * j k))⁻¹ ^ j i =
      (τ k / τ i) ^ (2 * j k * j i * f) := fun i k => by
    rw [← d1, inv_pow, inv_pow, div_inv_eq_mul, mul_comm, div_eq_mul_inv]
  have d4 : ∀ i : Fin a, (τ i ^ (2 * f * j i)) ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← pow_mul]
    congr 1
    ring
  have d5 : ∀ i : Fin a, 1 / (τ i ^ (2 * f * j i))⁻¹ ^ r a = τ i ^ (2 * j i * r a * f) := fun i => by
    rw [← d4, inv_pow, one_div, inv_inv]
  have d6 : ∀ i : Fin a, (τ i * τ i) ^ (2 * j i * j i * f) = ((τ i ^ 2) ^ (j i ^ 2 * f)) ^ 2 := fun i => by
    rw [← sq, ← pow_mul (τ i ^ 2)]
    congr 1
    ring
  simp only [d1, d2, d3, d4, d5]
  rw [Finset.prod_comm (f := fun i k => if k < i then (τ k / τ i) ^ (2 * j k * j i * f) else 1),
    prod_symm_split (fun i k => (τ i * τ k) ^ (2 * j i * j k * f))
      (fun i k => by rw [mul_comm (τ i)]; congr 1; ring)]
  simp only [d6, Finset.prod_pow]
  ring

end GlobalTheory.HtProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RealPlacesMatchIsomorphicCMInstances
section
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.LeviIso

namespace GlobalTheory.LeviIso.Places

noncomputable def placeEquiv (I : AutInst) : InfinitePlace I.F ≃ InfinitePlace I.E :=
  (Equiv.ofBijective _ (GlobalTheory.Count.FrameMajorant.comap_bijective I)).symm

theorem placeEquiv_apply (I : AutInst) (v : InfinitePlace I.F) :
    placeEquiv I v = InfinitePlace.mk (I.φ v) := by
  have h : (I.φ v).comp (algebraMap I.F I.E) = v.embedding := RingHom.ext (I.φ_over v)
  rw [placeEquiv, Equiv.symm_apply_eq]
  show v = (InfinitePlace.mk (I.φ v)).comap (algebraMap I.F I.E)
  rw [InfinitePlace.comap_mk, h, InfinitePlace.mk_embedding]

noncomputable def comapEquiv {K L : Type} [Field K] [Field L] (e : K ≃+* L) :
    InfinitePlace L ≃ InfinitePlace K where
  toFun w := w.comap (e : K →+* L)
  invFun w := w.comap (e.symm : L →+* K)
  left_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]
  right_inv w := by
    beta_reduce; rw [← InfinitePlace.comap_comp]; simp [InfinitePlace.comap_id]

theorem exists_twist {K : Type} [Field K] (φ ψ : K →+* ℂ)
    (h : InfinitePlace.mk φ = InfinitePlace.mk ψ) :
    ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧ ∀ y, φ y = τ (ψ y) := by
  rcases InfinitePlace.mk_eq_iff.mp h with h' | h'
  · exact ⟨RingHom.id ℂ, Or.inl rfl, fun y => by rw [h', RingHom.id_apply]⟩
  · refine ⟨starRingEnd ℂ, Or.inr rfl, fun y => ?_⟩
    rw [← h', ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]

theorem places_match : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E), (∀ y, e (star y) = star (e y)) → ∃ (β : InfinitePlace I.F ≃ InfinitePlace I.E) (σ : InfinitePlace I.F ≃ InfinitePlace I₀.F) (τ τ₀ : InfinitePlace I.F → (ℂ →+* ℂ)), (∀ v, τ v = RingHom.id ℂ ∨ τ v = starRingEnd ℂ) ∧ (∀ v, τ₀ v = RingHom.id ℂ ∨ τ₀ v = starRingEnd ℂ) ∧ (∀ v y, I.φ v y = τ v ((β v).embedding y)) ∧ ∀ v y, I.φ v (e y) = τ₀ v (I₀.φ (σ v) y) := by
  intro I I₀ e _

  let σ : InfinitePlace I.F ≃ InfinitePlace I₀.F :=
    (placeEquiv I).trans ((comapEquiv e).trans (placeEquiv I₀).symm)
  have h1 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v y = τ ((placeEquiv I v).embedding y) := fun v =>
    exists_twist _ _ (by rw [InfinitePlace.mk_embedding, placeEquiv_apply])
  have h2 : ∀ v : InfinitePlace I.F, ∃ τ : ℂ →+* ℂ, (τ = RingHom.id ℂ ∨ τ = starRingEnd ℂ) ∧
      ∀ y, I.φ v (e y) = τ (I₀.φ (σ v) y) := by
    intro v
    refine exists_twist ((I.φ v).comp (e : I₀.E →+* I.E)) (I₀.φ (σ v)) ?_
    rw [← placeEquiv_apply]
    simp only [σ, Equiv.trans_apply, Equiv.apply_symm_apply]
    rw [placeEquiv_apply]
    show _ = (InfinitePlace.mk (I.φ v)).comap (e : I₀.E →+* I.E)
    rw [InfinitePlace.comap_mk]
  choose τ hτ using h1
  choose τ₀ hτ₀ using h2
  exact ⟨placeEquiv I, σ, τ, τ₀, fun v => (hτ v).1, fun v => (hτ₀ v).1, fun v => (hτ v).2,
    fun v => (hτ₀ v).2⟩

end GlobalTheory.LeviIso.Places
end

