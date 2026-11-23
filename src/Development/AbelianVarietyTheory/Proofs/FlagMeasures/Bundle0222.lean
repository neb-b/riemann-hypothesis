module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormFlagZeroMiddleInverseMinorOrthogonal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerHaarUnimodularNormal
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MapConjLebesgueCommonStabilizerNormalForm
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
public import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0048
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0012
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.StabilizerMeasureNormalisationSymm
section
noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.StabMeas

variable {k r : ℕ}

theorem cont_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem cont_lmul (a : Mat k r) : Continuous (lmulM a : Mt k r → Mt k r) :=
  continuous_const.matrix_mul (continuous_id (X := Mat k r))

theorem meas_conj (a : Mat k r) : Measurable (conjM a : Mt k r → Mt k r) :=
  (cont_conj a).measurable

theorem meas_lmul (a : Mat k r) : Measurable (lmulM a : Mt k r → Mt k r) :=
  (cont_lmul a).measurable

theorem conj_conj (a b : Mat k r) : (conjM a : Mt k r → Mt k r) ∘ conjM b = conjM (a * b) := by
  funext x
  show a * (b * Matrix.of x * b⁻¹) * a⁻¹ = a * b * Matrix.of x * (a * b)⁻¹
  rw [Matrix.mul_inv_rev]
  simp only [Matrix.mul_assoc]

theorem conj_one (x : Mt k r) : conjM 1 x = x := by
  show (1 : Mat k r) * Matrix.of x * 1⁻¹ = Matrix.of x
  simp

theorem map_conj_conj (a b : Mat k r) (μ : Measure (Mt k r)) :
    (μ.map (conjM b)).map (conjM a) = μ.map (conjM (a * b)) := by
  rw [Measure.map_map (meas_conj a) (meas_conj b), conj_conj]

def conjEquiv {a : Mat k r} (ha : IsUnit a.det) : Mt k r ≃ᵐ Mt k r where
  toFun := conjM a
  invFun := conjM a⁻¹
  left_inv x := by
    have := congrFun (conj_conj a⁻¹ a) x
    rw [Matrix.nonsing_inv_mul _ ha, conj_one] at this
    exact this
  right_inv x := by
    have := congrFun (conj_conj a a⁻¹) x
    rw [Matrix.mul_nonsing_inv _ ha, conj_one] at this
    exact this
  measurable_toFun := meas_conj a
  measurable_invFun := meas_conj a⁻¹

theorem conj_back {a : Mat k r} (ha : IsUnit a.det) (s : Mat k r) : a * (a⁻¹ * s * a) * a⁻¹ = s := by
  simp only [Matrix.mul_assoc]
  rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one, Matrix.mul_nonsing_inv_cancel_left _ _ ha]

theorem haar_conj {a : Mat k r} (ha : IsUnit a.det) {S S' : Set (Mat k r)} (hS : ∀ x, a * x * a⁻¹ ∈ S' ↔ x ∈ S)
    {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) :
    IsHaarOn S' (μ.map (conjM a)) ∧ IsUnimod S' (μ.map (conjM a)) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  have hb : ∀ s ∈ S', a⁻¹ * s * a ∈ S := fun s hs => (hS _).1 (by rwa [conj_back ha])
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact (conjEquiv ha).measurableEmbedding.sigmaFinite_map
  · intro h0
    exact h2 ((Measure.map_eq_zero_iff (meas_conj a).aemeasurable).1 h0)
  · have := (conjEquiv ha).map_apply (μ := μ) {x | Matrix.of x ∉ S'}
    refine this.trans ?_
    rw [← h3]
    congr 1
    ext x
    exact not_congr (hS (Matrix.of x))
  · conv_rhs => rw [← h4 _ (hb s hs)]
    rw [Measure.map_map (meas_lmul _) (meas_conj a), Measure.map_map (meas_conj a) (meas_lmul _)]
    congr 1
    funext x
    show s * (a * Matrix.of x * a⁻¹) = a * (a⁻¹ * s * a * Matrix.of x) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ ha]
  · conv_rhs => rw [← h5 _ (hb s hs)]
    rw [Measure.map_map (continuous_rmulM _).measurable (meas_conj a),
      Measure.map_map (meas_conj a) (continuous_rmulM _).measurable]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹) * s = a * (Matrix.of x * (a⁻¹ * s * a)) * a⁻¹
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv _ ha, Matrix.mul_one]
  · conv_rhs => rw [← h6]
    rw [Measure.map_map measurable_invM (meas_conj a), Measure.map_map (meas_conj a) measurable_invM]
    congr 1
    funext x
    show (a * Matrix.of x * a⁻¹)⁻¹ = a * (Matrix.of x)⁻¹ * a⁻¹
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ ha, Matrix.mul_assoc]

theorem haar_smul {S : Set (Mat k r)} {μ : Measure (Mt k r)} (h : IsHaarOn S μ) (h' : IsUnimod S μ) {s : ℝ} (hs : 0 < s) :
    IsHaarOn S (ENNReal.ofReal s • μ) ∧ IsUnimod S (ENNReal.ofReal s • μ) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  obtain ⟨h5, h6⟩ := h'
  refine ⟨⟨?_, ?_, ?_, fun s hs => ?_⟩, fun s hs => ?_, ?_⟩
  · exact inferInstanceAs (SigmaFinite (s.toNNReal • μ))
  · intro h0
    have := congrArg (fun m : Measure (Mt k r) => m Set.univ) h0
    simp only [Measure.smul_apply, smul_eq_mul, Measure.coe_zero, Pi.zero_apply, mul_eq_zero,
      ENNReal.ofReal_eq_zero, Measure.measure_univ_eq_zero] at this
    rcases this with h | h
    · exact absurd h (not_le.2 hs)
    · exact h2 h
  · rw [Measure.smul_apply, h3, smul_zero]
  · rw [Measure.map_smul _ (meas_lmul s).aemeasurable, h4 s hs]
  · rw [Measure.map_smul _ (continuous_rmulM s).measurable.aemeasurable, h5 s hs]
  · rw [Measure.map_smul _ measurable_invM.aemeasurable, h6]

theorem isClosedSub_Rset {γ : Mat k r} (hγ : γ ∈ GG k r) : IsClosedSub k r (Rset k r γ) := by
  obtain ⟨n1, n2, n3, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG hγ
  refine ⟨fun x hx => n1 hx.1, ?_, ⟨n3, ?_⟩, fun a ha b hb => ⟨n4 _ ha.1 _ hb.1, ?_⟩, fun a ha => ⟨n5 _ ha.1, ?_⟩⟩
  · have hc : Continuous fun x : Mat k r => γ * x * γ⁻¹ :=
      (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const
    have := n2.inter (n2.preimage hc)
    exact this
  · rwa [Matrix.mul_one, Matrix.mul_nonsing_inv _ hu]
  · convert n4 _ ha.2 _ hb.2 using 1
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  · convert n5 _ ha.2 using 1
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc]

theorem conj_mem_Nset {n : Mat k r} (hn : n ∈ Nset k r) (x : Mat k r) : n * x * n⁻¹ ∈ Nset k r ↔ x ∈ Nset k r := by
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  have hu := isUnit_det_of_mem_GG (n1 hn)
  refine ⟨fun h => ?_, fun h => n4 _ (n4 _ hn _ h) _ (n5 _ hn)⟩
  convert n4 _ (n4 _ (n5 _ hn) _ h) _ hn using 1
  simp only [Matrix.mul_assoc]
  rw [Matrix.nonsing_inv_mul _ hu, Matrix.mul_one, Matrix.nonsing_inv_mul_cancel_left _ _ hu]

theorem conj_mem_Rset {n₁ n₂ : Mat k r} (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g x : Mat k r) :
    n₂⁻¹ * x * n₂⁻¹⁻¹ ∈ Rset k r (n₁ * g * n₂) ↔ x ∈ Rset k r g := by
  have hu := isUnit_det_of_mem_GG (isClosedSub_Nset.1 h₂)
  have e : n₁ * g * n₂ * (n₂⁻¹ * x * n₂⁻¹⁻¹) * (n₁ * g * n₂)⁻¹ = n₁ * (g * x * g⁻¹) * n₁⁻¹ := by
    rw [Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_inv_rev, Matrix.mul_inv_rev]
    simp only [Matrix.mul_assoc]
    rw [Matrix.mul_nonsing_inv_cancel_left _ _ hu, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  show (_ ∧ _) ↔ (_ ∧ _)
  rw [e, conj_mem_Nset h₁, conj_mem_Nset (isClosedSub_Nset.2.2.2.2 _ h₂)]

theorem dmin_N {z z' : Fin (2 * r + k + 1) → ℂ} (hz : inWb k r z) (hz' : inWb k r z') {n₁ n₂ : Mat k r}
    (h₁ : n₁ ∈ Nset k r) (h₂ : n₂ ∈ Nset k r) (g : Mat k r) (l : Fin (r + 2)) :
    Dmin k r z z' (n₁ * g * n₂) l = Dmin k r z z' g l :=
  Formalism.QuantumDeterminants.dInv k r z z' hz hz' n₁ ⟨1, (isClosedSub_UWset z).2.2.1, n₁, h₁, (Matrix.one_mul _).symm⟩
    n₂ ⟨1, (isClosedSub_UWset z').2.2.1, n₂, h₂, (Matrix.one_mul _).symm⟩ g l

theorem stabilizer_measure_normalisation : ∀ (k r j : ℕ) (hj : j ≤ r) (z z' : (Fin (2 * r + k + 1) → ℂ)), ∀ (γ : Mat k r) (s : ℝ) (μR : Measure (Mt k r)), 0 < s → IsNormalFormStabilizerMeasure k r hj z z' γ s μR → γ ∈ GG k r ∧ IsClosedSub k r (Rset k r γ) ∧ IsHaarOn (Rset k r γ) μR ∧ IsUnimod (Rset k r γ) μR ∧ IsNormalFormStabilizerMeasure k r hj z' z γ⁻¹ s (μR.map (conjM γ)) ∧ 0 < Dj k r hj z z' γ ∧ Dj k r hj z' z γ⁻¹ = Dj k r hj z z' γ ∧ ∀ De, DeOK k r z z' γ De → DeOK k r z' z γ⁻¹ De := by
  rintro k r j hj z z' γ s μR hs ⟨hz, hz', hT, n₁, h₁, n₂, h₂, g₀, β, c, hg, rfl, rfl⟩
  obtain ⟨n1, -, -, n4, n5⟩ := isClosedSub_Nset (k := k) (r := r)
  obtain ⟨a1, -, a3, a4, -, a6, -⟩ := _root_.GlobalTheory.Amp.NfMid.normal0_middle k r j hj z z' g₀ β c hz hz' hT hg
  obtain ⟨b1, b2⟩ := _root_.GlobalTheory.Amp.StabHaar.lebesgue_haar_unimodular_stabilizer k r j hj z z' g₀ β c hz hz' hT hg
  have c1 := _root_.GlobalTheory.Amp.RConj.lebR0_map_conjM_eq_of_isNormalZero k r j hj z z' g₀ β c hz hz' hT hg
  have hγ : n₁ * g₀ * n₂ ∈ GG k r :=
    isClosedSub_GG.2.2.2.1 _ (isClosedSub_GG.2.2.2.1 _ (n1 h₁) _ hg.1) _ (n1 h₂)
  have hinv : (n₁ * g₀ * n₂)⁻¹ = n₂⁻¹ * g₀⁻¹ * n₁⁻¹ := by
    rw [Matrix.mul_inv_rev, Matrix.mul_inv_rev, Matrix.mul_assoc]
  obtain ⟨d1, d2⟩ := haar_smul b1 b2 hs
  obtain ⟨e1, e2⟩ := haar_conj (isUnit_det_of_mem_GG (n1 (n5 _ h₂))) (conj_mem_Rset h₁ h₂ g₀) d1 d2
  have hD : ∀ l, ‖Dmin k r z' z (n₁ * g₀ * n₂)⁻¹ l‖ = ‖Dmin k r z z' (n₁ * g₀ * n₂) l‖ := fun l => by
    rw [hinv, dmin_N hz' hz (n5 _ h₂) (n5 _ h₁), dmin_N hz hz' h₁ h₂, a6]
  refine ⟨hγ, isClosedSub_Rset hγ, e1, e2,
    ⟨hz', hz, a1 ▸ hT, n₂⁻¹, n5 _ h₂, n₁⁻¹, n5 _ h₁, g₀⁻¹, β, c⁻¹, a3, hinv, ?_⟩, ?_, hD _, fun De h => ⟨h.1, ?_⟩⟩
  · rw [map_conj_conj, Matrix.mul_nonsing_inv_cancel_right _ _ (isUnit_det_of_mem_GG (n1 h₂)), ← map_conj_conj,
      Measure.map_smul _ (meas_conj g₀).aemeasurable, c1, Matrix.nonsing_inv_nonsing_inv _ (isUnit_det_of_mem_GG (n1 h₁))]
  · unfold Dj at a4 ⊢
    rwa [dmin_N hz hz' h₁ h₂]
  · intro l hl h0
    rw [hD]
    refine h.2 l hl fun h' => h0 ?_
    rw [← norm_eq_zero, hD, h', norm_zero]

end GlobalTheory.Amp.StabMeas
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.VENatEqZero
section
open NumberField IsDedekindDomain ValuativeRel Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc GlobalTheory.HL

namespace GlobalTheory.TypeUnifProd

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private theorem valuation_natCast_prime_eq_one_of_ne_resChar {F : Type} [Field F] [NumberField F] (p : HeightOneSpectrum (𝓞 F))
    {l : ℕ} (hl : l.Prime) (hne : l ≠ Loc.resChar p) : p.valuation F (l : F) = 1 := by
  rw [← map_natCast (algebraMap (𝓞 F) F) l, HeightOneSpectrum.valuation_of_algebraMap,
    HeightOneSpectrum.intValuation_eq_one_iff]
  intro hmem
  apply hne
  have : p.asIdeal.IsPrime := p.isPrime
  have hz : ((l : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk p.asIdeal), Ideal.Quotient.eq_zero_iff_mem]
    exact hmem
  have hdvd : ringChar (𝓞 F ⧸ p.asIdeal) ∣ l := (ringChar.spec _ l).1 hz
  rcases (Nat.dvd_prime hl).1 hdvd with h | h
  · exfalso
    have h1 : ((1 : ℕ) : 𝓞 F ⧸ p.asIdeal) = 0 := (ringChar.spec _ 1).2 (by rw [h])
    simp at h1
  · exact h.symm

private theorem vE_algebraMap_ιF_eq_neg_log_valuation {D : D7} (p : PlF D) (L : Loc.LocE (D.s.atP p).Fp (D.s.atP p).Ep)
    {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) {x : D.host.F} (hx : x ≠ 0) :
    vE L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep ((D.s.atP p).ιF x)) =
      -WithZero.log (p.valuation D.host.F x) := by
  have := (D.s.atP p).lf
  refine GlobalTheory.ResProd.vE_eq_neg_log p L (D.s.atP p).ιF (D.s.atP p).dense ?_ hϖ hx
  intro a b
  rw [← Valuation.Compatible.vle_iff_le]
  exact (D.s.atP p).val a b

private theorem exists_theta_eq_ιF_valuation_eq_g_mul {D : D7} (Z : LocDat D) (p : PlF D) :
    ∃ t : D.host.F, t ≠ 0 ∧ LocNG.theta (Z.M p) = (D.s.atP p).ιF t ∧
      p.valuation D.host.F t = p.valuation D.host.F ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) := by
  obtain ⟨-, -, -, -, -, hsp⟩ := Z.agree p
  have hss := D.s_split p
  have hg0 := D.host.g_prime 0
  have hg1 := D.host.g_prime 1
  have hgne := D.host.g_ne
  unfold LocNG.theta
  cases hM : (Z.M p).split with
  | none =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hS] at hss
      have h0 : D.host.g 0 ≠ Loc.resChar p := fun h => by simp [h] at hss
      have h1 : D.host.g 1 ≠ Loc.resChar p := fun h => by simp [h] at hss
      refine ⟨1, one_ne_zero, (map_one _).symm, ?_⟩
      push_cast
      rw [map_mul, valuation_natCast_prime_eq_one_of_ne_resChar p hg0 h0, valuation_natCast_prime_eq_one_of_ne_resChar p hg1 h1, map_one, mul_one]
    | some sg =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
  | some g =>
    cases hS : (D.s.atP p).split with
    | none =>
      rw [hM, hS] at hsp
      exact (hsp : False).elim
    | some sg =>
      rw [hM, hS] at hsp
      obtain ⟨-, hq⟩ := hsp
      have hl : (Loc.resChar p).Prime := (D.s.atP p).ellPrime.out
      have hmem : Loc.resChar p = D.host.g 0 ∨ Loc.resChar p = D.host.g 1 := by
        have := hss.1 (by rw [hS]; rfl)
        simpa using this
      refine ⟨(Loc.resChar p : D.host.F), Nat.cast_ne_zero.2 hl.ne_zero, ?_, ?_⟩
      · change ((g.q : (D.s.atP p).Fp)) = _
        rw [hq, sg.q_eq, map_natCast]
      · push_cast
        rw [map_mul]
        rcases hmem with h | h
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg1 (by rw [h]; exact hgne.symm), mul_one, h]
        · rw [valuation_natCast_prime_eq_one_of_ne_resChar p hg0 (by rw [h]; exact hgne), one_mul, h]

theorem modK_theta {D : D7} (Z : LocDat D) (p : PlF D) {ϖ : 𝒪[(D.s.atP p).Fp]} (hϖ : Irreducible ϖ) :
    (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (resQ ϖ : ℝ) ^
      (-(2 * vE (Z.M p).L ϖ (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))))) := by
  obtain ⟨hOK, -⟩ := Z.agree p
  obtain ⟨t, ht, hθ, hv⟩ := exists_theta_eq_ιF_valuation_eq_g_mul Z p
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  rw [hθ, (GlobalTheory.BaseModule.modK_algebraMap (Z.M p) hOK ϖ hϖ).2 _ ((map_ne_zero _).2 ht),
    vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ ht, vE_algebraMap_ιF_eq_neg_log_valuation p _ hϖ hx, hv]

noncomputable def placesOf {D : D7} (Z : LocDat D) : Places D.host.F D.host.E D.conjF where
  quad := D.sp.cm.deg2
  loc := D.s.atP
  L := fun p => (Z.M p).L
  L_cj := Z.hcj

theorem card_infinite (D : D7) :
    Fintype.card (InfinitePlace D.host.E) = Module.finrank ℚ D.host.F := by
  have : IsCMField D.host.E := D.host.isCMField_hostE
  have : IsTotallyComplex D.host.E := IsCMField.to_isTotallyComplex
  have h1 := IsTotallyComplex.finrank (K := D.host.E)
  have h2 := D.sp.cm.deg2
  have h3 := Module.finrank_mul_finrank ℚ D.host.F D.host.E
  rw [h2] at h3
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero, zero_add]
  omega

theorem main : ∀ (D : D7) (Z : LocDat D), (Function.mulSupport fun p : PlF D => (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p)))).Finite ∧ ∏ᶠ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) = (((D.host.g 0 * D.host.g 1 : ℕ) : ℝ) ^ (2 * Fintype.card (InfinitePlace D.host.E)))⁻¹ := by
  intro D Z
  have hex : ∀ p : PlF D, ∃ ϖ : 𝒪[(D.s.atP p).Fp], Irreducible ϖ := fun p => by
    have := (D.s.atP p).lf
    exact IsDiscreteValuationRing.exists_irreducible _
  choose ϖ hϖ using hex
  have hx : ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) ≠ 0 :=
    Nat.cast_ne_zero.2 (Nat.mul_ne_zero (D.host.g_prime 0).ne_zero (D.host.g_prime 1).ne_zero)
  obtain ⟨hfin, hprod⟩ := GlobalTheory.ResProd.prod_resQ_zpow (placesOf Z) ϖ hϖ _ hx
  have hfin' : {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
      ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0}.Finite := hfin
  have hprod' : ∏ᶠ p : PlF D, (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp
      (D.s.atP p).Ep ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) =
      |((Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) : ℚ) : ℝ)| := hprod
  have hterm : ∀ p : PlF D, (Z.M p).modK (algebraMap _ _ (LocNG.theta (Z.M p))) =
      (((resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ^ 2)⁻¹ := by
    intro p
    rw [modK_theta Z p (hϖ p), zpow_neg, mul_comm, zpow_mul]
    norm_cast
  have hsub : (Function.mulSupport fun p : PlF D => (resQ (ϖ p) : ℝ) ^ vE (Z.M p).L (ϖ p)
      (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F)))) ⊆
      {p : PlF D | vE (Z.M p).L (ϖ p) (algebraMap (D.s.atP p).Fp (D.s.atP p).Ep
        ((D.s.atP p).ιF ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F))) ≠ 0} := by
    intro p hp
    simp only [Function.mem_mulSupport, ne_eq, Set.mem_ofPred_eq] at hp ⊢
    intro h0
    apply hp
    rw [h0, zpow_zero]
  have hfs := hfin'.subset hsub
  simp_rw [hterm]
  refine ⟨hfs.subset ?_, ?_⟩
  · intro p hp
    simp only [Function.mem_mulSupport, ne_eq] at hp ⊢
    intro h1
    apply hp
    rw [h1, one_pow, inv_one]
  · have hn : Algebra.norm ℚ ((D.host.g 0 * D.host.g 1 : ℕ) : D.host.F) =
        ((D.host.g 0 * D.host.g 1 : ℕ) : ℚ) ^ Module.finrank ℚ D.host.F := by
      rw [← map_natCast (algebraMap ℚ D.host.F), Algebra.norm_algebraMap]
    rw [finprod_inv_distrib, ← finprod_pow hfs, hprod', card_infinite D, hn]
    push_cast
    rw [abs_of_nonneg (by positivity), ← pow_mul]
    ring

end GlobalTheory.TypeUnifProd
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.XLamLeSmulSupXLamAdmissibleFlag
section
open NumberField Module Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt GlobalTheory.LoopC
open scoped ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AdmFlagSub

open IsDedekindDomain Formalism.HermitianLatticesTheory

section Loc

variable {R W : Type} [CommRing R] [AddCommGroup W] [Module R W] (p : Ideal R) [hp : p.IsPrime]

theorem mem_localization_iff (L : Submodule R W) (x : W) :
    x ∈ localization₂ p L ↔ ∃ s, s ∉ p ∧ s • x ∈ L := Iff.rfl

theorem le_localized_self (L : Submodule R W) : L ≤ localization₂ p L := fun x hx =>
  (mem_localization_iff p L x).2 ⟨1, fun h => hp.ne_top ((Ideal.eq_top_iff_one _).2 h), by simpa using hx⟩

theorem localization_le_of_le_localization₂ {L N : Submodule R W} (h : L ≤ localization₂ p N) : localization₂ p L ≤ localization₂ p N := by
  intro x hx
  obtain ⟨s, hs, hsx⟩ := (mem_localization_iff p L x).1 hx
  obtain ⟨t, ht, htx⟩ := (mem_localization_iff p N _).1 (h hsx)
  refine (mem_localization_iff p N x).2 ⟨t * s, fun hm => ?_, by rwa [mul_smul]⟩
  rcases hp.mem_or_mem hm with h1 | h1
  · exact ht h1
  · exact hs h1

end Loc

theorem mem_of_forall_locP {E W : Type} [Field E] [NumberField E] [AddCommGroup W]
    [Module (𝓞 E) W] (N : Submodule (𝓞 E) W) (x : W)
    (h : ∀ P : HeightOneSpectrum (𝓞 E), x ∈ (haveI := P.isPrime; localization₂ P.asIdeal N)) : x ∈ N := by
  by_contra hx
  let I : Ideal (𝓞 E) := N.comap (LinearMap.toSpanSingleton (𝓞 E) W x)
  have hI : I ≠ ⊤ := by
    intro hI
    have : (1 : 𝓞 E) ∈ I := by rw [hI]; trivial
    apply hx
    simpa [I] using this
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  have hM0 : M ≠ ⊥ := Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)
  obtain ⟨s, hs, hsx⟩ := h ⟨M, hM.isPrime, hM0⟩
  exact hs (hIM (by simpa [I] using hsx))

theorem xLam_le_smul_sup_xLam :
    ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (S : HSpace E) (r : ℕ) (T T' : E)
      (Λ : Submodule (𝓞 E) S.V) (g : ℕ) (F : LFlag S r T) (F' : LFlag S r T'),
      IsFixedConv Λ g F → IsFixedConv Λ g F' → IsAdmissible Λ g F F' →
        XLam Λ F ≤ Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' := by
  intro E _ _ _ S r T T' Λ g F F' hF hF' hA x hx
  obtain ⟨ξ, hξ0, hξ1, hξ⟩ := hA
  set N : Submodule (𝓞 E) S.V := Ideal.span {(g : 𝓞 E)} • Λ ⊔ XLam Λ F' with hN
  apply mem_of_forall_locP
  intro P
  haveI := P.isPrime
  by_cases hg : (g : 𝓞 E) ∈ P.asIdeal
  swap
  · refine (mem_localization_iff _ _ _).2 ⟨g, hg, Submodule.mem_sup_left ?_⟩
    exact Submodule.smul_mem_smul (Ideal.subset_span rfl) hx.1
  obtain ⟨c, -, hc1, hc⟩ := hF.1 P
  obtain ⟨c', -, hc1', hc'⟩ := hF'.1 P
  simp only [hc1 hg, one_smul] at hc
  simp only [hc1' hg, one_smul] at hc'
  have he' : ∀ b, F'.fl.e b ∈ localization₂ P.asIdeal N := by
    intro b
    have h1 : F'.fl.e b ∈ localization₂ P.asIdeal (XLam Λ F') := by
      rw [hc']
      exact le_localized_self _ _ (Submodule.subset_span ⟨b, rfl⟩)
    exact localization_le_of_le_localization₂ _ (le_sup_right.trans (le_localized_self _ _)) h1
  have hf : ∀ n : ℕ, ∀ b : Fin r, b.1 = n → F.fl.e b ∈ localization₂ P.asIdeal N := by
    intro n
    induction n using Nat.strong_induction_on with
    | _ n ih =>
      intro b hb
      have h1 : frame F' b.castSucc - frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N :=
        localization_le_of_le_localization₂ _ (le_sup_left.trans (le_localized_self _ _)) (hξ b.castSucc P hg)
      have h2 : frame F' b.castSucc = F'.fl.e b := by simp [frame, FlagG.fvec]
      have h3 : frameAct (frame F) ξ b.castSucc ∈ localization₂ P.asIdeal N := by
        have := Submodule.sub_mem _ (he' b) h1
        rw [h2] at this
        simpa using this
      have h4 : frameAct (frame F) ξ b.castSucc =
          F.fl.e b + ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a := by
        unfold frameAct
        rw [Fin.sum_univ_castSucc, hξ0 (Fin.last r) b.castSucc (Fin.castSucc_lt_last b),
          ← Finset.add_sum_erase _ _ (Finset.mem_univ b), hξ1]
        simp only [frame, FlagG.fvec, Fin.snoc_castSucc, RingOfIntegers.coe_eq_algebraMap, map_zero,
          map_one, zero_smul, add_zero, one_smul, algebraMap_smul]
      have h5 : ∑ a ∈ Finset.univ.erase b, ξ a.castSucc b.castSucc • F.fl.e a ∈
          localization₂ P.asIdeal N := by
        refine Submodule.sum_mem _ fun a ha => ?_
        rcases lt_or_gt_of_ne (Finset.ne_of_mem_erase ha) with hab | hab
        · exact Submodule.smul_mem _ _ (ih a.1 (hb ▸ hab) a rfl)
        · rw [hξ0 _ _ (Fin.castSucc_lt_castSucc_iff.2 hab), zero_smul]
          exact Submodule.zero_mem _
      rw [h4] at h3
      simpa using Submodule.sub_mem _ h3 h5
  have hx' : x ∈ localization₂ P.asIdeal (XLam Λ F) := le_localized_self _ _ hx
  rw [hc] at hx'
  refine localization_le_of_le_localization₂ _ ?_ hx'
  rw [Submodule.span_le]
  rintro _ ⟨a, rfl⟩
  exact hf _ a rfl

end GlobalTheory.AdmFlagSub

end
end

