module

public import Mathlib
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.PhaseAtPf
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0009
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Bundle0013
public import Formalism.SharpRestriction.CuspSpanNormBounds.UnimodularSchurMeasures.SigmaFiniteRestrictSubgroup
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.UnitaryIsometries

@[expose] public section

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianBlockSpans
section
noncomputable section

open scoped ComplexConjugate
open Matrix

namespace Formalism.L2.SG.RealObj.HermitianBlockSpans

open Formalism.L2.SG.HidaSetting

variable {n : ℕ} (ε : Fin n → Bool)

theorem hJ_sub_left (x y w : Fin n → ℂ) : hJ ε (x - y) w = hJ ε x w - hJ ε y w := by
  unfold hJ; rw [star_sub, sub_dotProduct]

theorem hJ_sub_right (x y w : Fin n → ℂ) : hJ ε w (x - y) = hJ ε w x - hJ ε w y := by
  unfold hJ; rw [Matrix.mulVec_sub, dotProduct_sub]

theorem hJ_sum_right {m : ℕ} (c : Fin m → ℂ) (v : Fin m → Fin n → ℂ) (w : Fin n → ℂ) :
    hJ ε w (∑ i, c i • v i) = ∑ i, c i * hJ ε w (v i) := by
  unfold hJ
  rw [Matrix.mulVec_sum, dotProduct_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul]

theorem hJ_conj (x y : Fin n → ℂ) : hJ ε y x = star (hJ ε x y) := by
  unfold hJ Formalism.REAL.Jm
  simp only [Matrix.mulVec_diagonal, dotProduct, star_sum, star_mul']
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp <;> ring

theorem hJ_map {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) (x y : Fin n → ℂ) :
    hJ ε (g *ᵥ x) (g *ᵥ y) = hJ ε x y := by
  unfold hJ
  rw [Matrix.star_mulVec, ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]
  unfold Formalism.REAL.inUJ at hg
  rw [hg]

variable {r : ℕ}

theorem spanLt_eq (e : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r) :
    spanLt e a = Submodule.span ℂ (Set.range fun c : Fin a => e (Fin.castLE ha c)) := by
  unfold spanLt
  congr 1
  ext v
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨⟨b.1, hb⟩, rfl⟩
  · rintro ⟨c, rfl⟩
    exact ⟨Fin.castLE ha c, c.2, rfl⟩

def blk (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r) : Matrix (Fin a) (Fin a) ℂ :=
  Matrix.of fun b c => hJ ε (e (Fin.castLE ha b)) (e' (Fin.castLE ha c))

theorem zero_of_perp_right (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r)
    (hD : a = 0 ∨ (blk ε e e' ha).det ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ spanLt e' a) (hp : ∀ b : Fin a, hJ ε (e (Fin.castLE ha b)) x = 0) : x = 0 := by
  rw [spanLt_eq e' ha, Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, rfl⟩ := hx
  rcases hD with h0 | hdet
  · subst h0
    simp
  · have hM : blk ε e e' ha *ᵥ c
        = 0 := by
      funext b
      have := hp b
      rw [hJ_sum_right] at this
      simpa [blk, Matrix.mulVec, dotProduct, mul_comm] using this
    have := Matrix.eq_zero_of_mulVec_eq_zero hdet hM
    simp [this]

theorem zero_of_perp_left (e e' : Fin r → Fin n → ℂ) {a : ℕ} (ha : a ≤ r)
    (hD : a = 0 ∨ (blk ε e e' ha).det ≠ 0)
    {x : Fin n → ℂ} (hx : x ∈ spanLt e a) (hp : ∀ b : Fin a, hJ ε x (e' (Fin.castLE ha b)) = 0) : x = 0 := by
  refine zero_of_perp_right ε e' e ha ?_ hx fun b => by rw [hJ_conj, hp b, star_zero]
  rcases hD with h0 | hdet
  · exact Or.inl h0
  · right
    have e1 : blk ε e' e ha = (blk ε e e' ha)ᴴ := by
      ext b c
      simp only [blk, Matrix.conjTranspose_apply, Matrix.of_apply]
      rw [← hJ_conj]
    rw [e1, Matrix.det_conjTranspose]
    exact fun h => hdet (star_eq_zero.1 h)

theorem st_triv (e e' : Fin r → Fin n → ℂ) (s : Matrix (Fin n) (Fin n) ℂ)
    (hU : ∀ x y, hJ ε (s *ᵥ x) (s *ᵥ y) = hJ ε x y)
    (h1 : ∀ a : Fin r, (s - 1) *ᵥ e a ∈ spanLt e a.1) (h1' : ∀ a : Fin r, (s - 1) *ᵥ e' a ∈ spanLt e' a.1)
    (h2 : ∀ y, (∀ a, hJ ε (e a) y = 0) → (s - 1) *ᵥ y ∈ spanLt e r)
    (hD : ∀ l (hl : l ≤ r), 1 ≤ l →
      (blk ε e e' hl).det ≠ 0) :
    s = 1 := by
  have hD' : ∀ l (hl : l ≤ r),
      l = 0 ∨ (blk ε e e' hl).det ≠ 0 :=
    fun l hl => by
      rcases Nat.eq_zero_or_pos l with h | h
      · exact Or.inl h
      · exact Or.inr (hD l hl h)
  have hsub : ∀ v : Fin n → ℂ, (s - 1) *ᵥ v = s *ᵥ v - v := fun v => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]

  have step : ∀ a : ℕ, a ≤ r → ∀ c : Fin r, c.1 < a → s *ᵥ e c = e c ∧ s *ᵥ e' c = e' c := by
    intro a
    induction a with
    | zero => intro _ c hc; exact absurd hc (Nat.not_lt_zero _)
    | succ a ih =>
      intro ha c hc
      have ha' : a ≤ r := Nat.le_of_succ_le ha
      have IH := ih ha'
      rcases Nat.lt_succ_iff_lt_or_eq.1 hc with hlt | heq
      · exact IH c hlt
      · have hca : c.1 = a := heq
        constructor
        · have hx := h1 c
          rw [hca] at hx
          have := zero_of_perp_left ε e e' ha' (hD' a ha') hx fun b => by
            have hb := (IH (Fin.castLE ha' b) b.2).2
            rw [hsub, hJ_sub_left, ← hb, hU, hb, sub_self]
          rw [hsub, sub_eq_zero] at this
          exact this
        · have hx := h1' c
          rw [hca] at hx
          have := zero_of_perp_right ε e e' ha' (hD' a ha') hx fun b => by
            have hb := (IH (Fin.castLE ha' b) b.2).1
            rw [hsub, hJ_sub_right, ← hb, hU, hb, sub_self]
          rw [hsub, sub_eq_zero] at this
          exact this
  have hfix : ∀ c : Fin r, s *ᵥ e c = e c ∧ s *ᵥ e' c = e' c := fun c => step r le_rfl c c.2

  ext i j
  suffices hall : ∀ y : Fin n → ℂ, s *ᵥ y = y by
    have := congrFun (hall (Pi.single j 1)) i
    simpa [Matrix.mulVec_single, Matrix.one_apply, Pi.single_apply] using this
  intro y
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hy := h2 y (fun a => a.elim0)
    have h0 : spanLt e 0 = ⊥ := by
      unfold spanLt
      simp
    rw [h0, Submodule.mem_bot, hsub, sub_eq_zero] at hy
    exact hy
  · let M : Matrix (Fin r) (Fin r) ℂ := fun b c => hJ ε (e b) (e' c)
    have hMdet : M.det ≠ 0 := hD r le_rfl hr
    let lam : Fin r → ℂ := M⁻¹ *ᵥ fun b => hJ ε (e b) y
    let x' : Fin n → ℂ := ∑ c, lam c • e' c
    have hMl : M *ᵥ lam = fun b => hJ ε (e b) y := by
      simp only [lam, Matrix.mulVec_mulVec]
      rw [Matrix.mul_nonsing_inv _ (Ne.isUnit hMdet), Matrix.one_mulVec]
    have hperp : ∀ b, hJ ε (e b) (y - x') = 0 := by
      intro b
      rw [hJ_sub_right, hJ_sum_right]
      have := congrFun hMl b
      simp only [Matrix.mulVec, dotProduct, M] at this
      rw [← this]
      simp only [mul_comm, sub_self]
    have hx'fix : s *ᵥ x' = x' := by
      simp only [x', Matrix.mulVec_sum, Matrix.mulVec_smul, (hfix _).2]
    have hw : (s - 1) *ᵥ y ∈ spanLt e r := by
      have := h2 (y - x') hperp
      rwa [Matrix.mulVec_sub, hsub x', hx'fix, sub_self, sub_zero] at this
    have hw0 := zero_of_perp_left ε e e' le_rfl (hD' r le_rfl) hw fun b => by
      have hb := (hfix (Fin.castLE le_rfl b)).2
      rw [hsub, hJ_sub_left, ← hb, hU, hb, sub_self]
    rw [hsub, sub_eq_zero] at hw0
    exact hw0

end Formalism.L2.SG.RealObj.HermitianBlockSpans
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.HermitianModuleBetaCongruence
section
noncomputable section

open scoped Classical ComplexConjugate TensorProduct
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Matrix Formalism.L2.SG.TermOp Formalism.L2.SG.HidaSetting
  Formalism.L2.SG.Pf.unitaryCongruence

namespace Formalism.L2.SG.NormCut

section GoodNC

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

theorem ncong_inv {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : NCong X x⁻¹ := by
  refine ⟨inv_e X.B.I X.B.g X.e0 hx hn.1, ?_⟩
  rw [inv_id]
  refine neg_mem (pres X.B.I (K_inv X.B.I hx) X.B.g _ _ (sub_Mo X.B.I) ?_ (mL_Mo X.B.I) _ hn.2)
  rintro _ ⟨b, rfl⟩
  exact Mo_mono X.B.I (Set.image_subset_range _ _) (inv_e X.B.I X.B.g X.e0 hx hn.1 b)

theorem hermitian_module_beta_congruence {m : VA X.B.I} (hm : m ∈ Mo X.B.I X.B.g (Set.range X.e0)) (j : Fin D.R.k) :
    ZMod' X.B.I X.B.g (hA X.B.I m (X.bw j)) := by
  rw [hA_symm]
  refine Z_sig X.B.I X.B.g (Z_pair_Mo X (X.vectorsInLattice.2.2 j).1 ?_ _ hm)
  rintro _ ⟨a, rfl⟩
  rw [hA_symm]
  exact Z_sig X.B.I X.B.g ((X.weightVectorsIntegral j).2.2 a).1

theorem par_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) (hni : NCong X x⁻¹) : Par X x := by
  obtain ⟨hE0, hF0, hZ0, hB, hBd⟩ := frame_Lf X
  refine ⟨hx, fun a => ?_, fun j => ?_⟩
  · rw [show X.B.I.fmat x *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x - 1) *ᵥ X.e0 a by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
    exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hn.1 a))
  · refine mem_Mo_eb X (K_mv X.B.I hx (hB j)) (fun a => ?_) ?_ (fun l => ?_)
    · rw [hA_adj]
      refine hermitian_module_beta_congruence X ?_ j
      rw [show X.B.I.fmat x⁻¹ *ᵥ X.e0 a = X.e0 a + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.e0 a by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel]
      exact add_mem (sub_Mo X.B.I ⟨a, rfl⟩) (Mo_mono X.B.I (Set.image_subset_range _ _) (hni.1 a))
    · rw [hA_adj, show X.B.I.fmat x⁻¹ *ᵥ X.z0 = X.z0 + (X.B.I.fmat x⁻¹ - 1) *ᵥ X.z0 by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec]; abel, hA_add_left]
      exact Z_add X.B.I X.B.g (X.weightVectorsIntegral j).1 (hermitian_module_beta_congruence X hni.2 j)
    · have e : hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j) = 0 := by
        rw [X.bw_w l, X.bw_w j, Matrix.mulVec_smul, hA_smul_left, hA_smul_right]
        have := X.ew_orth
        linear_combination (hA X.B.I (X.bw l) (X.B.I.fmat x *ᵥ X.bw j)) * this
      rw [e]; exact Z_zero X.B.I X.B.g

theorem good_of_ncong {x : X.B.I.Gf} (hx : x ∈ X.B.I.Kset) (hn : NCong X x) : Good X x := by
  have hni := ncong_inv X hx hn
  have hxi : x⁻¹ ∈ X.B.I.Kset := by
    simp only [Formalism.MainNotions.S.AutInst.Kset, Set.mem_setOf_eq] at hx ⊢
    simpa using inv_mem hx
  exact ⟨par_of_ncong X hx hn hni, par_of_ncong X hxi hni (by simpa using hn)⟩

end GoodNC

section AdmParPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)} (cs : ColSys X u what₂) (cs' : ColSys X u' rows')


variable (F0 F0') in
def TermK : Prop :=
  ∀ t : GTerm X u u' F0 F0' what₂ rows',
    kOf X u u' (cs.h (cs.base t.lam) : X.B.I.Gf) (cs'.h (cs'.base t.lam') : X.B.I.Gf) t.pt ∈ X.B.I.Kset

theorem adm_parity_of_norm (hK : TermK F0 F0' cs cs') (hN : AdmN F0 F0' cs cs') : AdmPar F0 F0' cs cs' := by
  intro t
  exact good_of_ncong _ (hK t) (hN t)

end AdmParPf

end Formalism.L2.SG.NormCut
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.JacConstGE
section
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace Formalism.L2.SG.Pf.GE

open Formalism.QuantumDeterminants Formalism.L2.SG.Pf Formalism.L2.SG.Pf.BH Formalism.L2.SG.Pf.WB

theorem isHaarOn_smul {k r : ℕ} {S : Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ)}
    {ν : Measure (Mt k r)} (h : Formalism.MainNotions.S.IsHaarOn S ν) {c : NNReal} (hc : 0 < c) :
    Formalism.MainNotions.S.IsHaarOn S (c • ν) := by
  obtain ⟨hσ, h0, hconc, hl⟩ := h
  have := hσ
  refine ⟨inferInstance, ?_, ?_, fun s hs => ?_⟩
  · intro h
    apply h0
    exact (smul_eq_zero.1 h).resolve_left hc.ne'
  · rw [Measure.smul_apply, hconc, smul_zero]
  · have hmeas := (Formalism.FourierDecayAlt.P.B2x1.lmulM_cont (k := k) (r := r) s).measurable
    rw [Measure.map_smul c hmeas.aemeasurable, hl s hs]

theorem toReal_smul_apply {α : Type*} [MeasurableSpace α] (c : NNReal) (ν : Measure α) (A : Set α) :
    ((c • ν) A).toReal = (c : ℝ) * (ν A).toReal := by
  rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, ENNReal.toReal_mul, ENNReal.coe_toReal]

theorem gaugeWb_of (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hSW : GaugeShiftW) (hLW : RhsWLim) :
    ∀ k r : ℕ, ∃ μ : Measure (Mt k r), IsGaugeOn (Formalism.FourierDecayAlt.B2.UWb k r) μ := by
  intro k r
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact hU r
  obtain ⟨z, z', μW, μW', a, a', μsec, D⟩ := hD k r hk
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  have hw := wbConst_pos (k := k) D.T_pos D.T'_pos D.a_pos D.a'_pos
  set w := wbConst k (Tz k r z) (Tz k r z') a a' with hwdef
  refine ⟨(Real.toNNReal w) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 hw), ?_⟩
  have hlim := (hLW k r z z' μW μW' a a' μsec D).const_mul w
  rw [mul_inv_cancel₀ hw.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hSW k r z z' ν μW μW' a a' μsec D hν ρ hρ
  have h1 : ∫⁻ x, (mBall k r z z' μsec ρ).indicator 1 x ∂ν = ν (mBall k r z z' μsec ρ) :=
    lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal w • ν) (bBall k r ρ)).toReal / bVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ hw.le, mul_div_assoc]

theorem gaugeExists_of (hR : RhsHaar) (hRW : RhsWHaar) (hD : WbDataEx) (hU : ExistsGaugeMeasureForEachRank) (hS : GaugeShift)
    (hSW : GaugeShiftW) (hL : RhsLim) (hLW : RhsWLim) : GaugeExists := by
  intro k r
  have hb := gaugeWb_of hRW hD hU hSW hLW k r
  refine ⟨?_, hb⟩
  obtain ⟨μb, hμb⟩ := hb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  have h2r : (0 : ℝ) < 2 ^ r := by positivity
  refine ⟨(Real.toNNReal (2 ^ r)) • ν, isHaarOn_smul hν (Real.toNNReal_pos.2 h2r), ?_⟩
  have hlim := (hL k r μb hμb).const_mul ((2 : ℝ) ^ r)
  rw [mul_inv_cancel₀ h2r.ne'] at hlim
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ρ hρ
  obtain ⟨hm, he⟩ := hS k r ν hν ρ hρ
  have h1 : ∫⁻ x, (wBall k r ρ).indicator 1 x ∂ν = ν (wBall k r ρ) := lintegral_indicator_one hm
  have h2 := hνφ _ (measurable_one.indicator hm)
  rw [h1, he] at h2
  show _ = ((Real.toNNReal (2 ^ r) • ν) (gBall k r ρ)).toReal / gVol k r ρ
  rw [toReal_smul_apply, h2, Real.coe_toNNReal _ h2r.le, mul_div_assoc]

theorem iterGauge_of (hR : RhsHaar) : IterGauge := by
  intro k r μ μb hμ hμb
  obtain ⟨ν, hν, hνφ⟩ := hR k r μb hμb
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.unitary_group_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hμ.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.unitary_group_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

theorem rankGauge_of (hRW : RhsWHaar) : RankGauge := by
  intro k r z z' μb μW μW' a a' μsec D hμb
  obtain ⟨ν, hν, hνφ⟩ := hRW k r z z' μW μW' a a' μsec D
  obtain ⟨ν0, h0⟩ := Formalism.FourierDecayAlt.P.opposite_weyl_haar_exists k r
  obtain ⟨c1, hc1, hc1', e1⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hμb.1
  obtain ⟨c2, hc2, hc2', e2⟩ := Formalism.MainNotions.LeviCoordinates.left_haar_eq_smul_biinvariant (Formalism.FourierDecayAlt.P.opposite_weyl_subgroup_closed k r) h0 hν
  have hne : c1 / c2 ≠ ∞ := (ENNReal.div_lt_top hc1' hc2).ne
  refine ⟨(c1 / c2).toNNReal, ENNReal.toNNReal_pos (ENNReal.div_pos_iff.2 ⟨hc1, hc2'⟩).ne' hne,
    fun φ hφ => ?_⟩
  rw [ENNReal.coe_toNNReal hne, ← hνφ φ hφ, e1, e2, lintegral_smul_measure, lintegral_smul_measure, smul_eq_mul, smul_eq_mul, ← mul_assoc,
    ENNReal.div_mul_cancel hc2 hc2']

theorem bruhatHaar_of_rhsHaar (hR : RhsHaar) (hS : GaugeShift) (hW : Sandwich) (hV : VolLim) : BruhatHaar :=
  bruhatHaar_of_iterGauge (iterGauge_of hR) hS hW hV

theorem wbHaar_of_rhsWHaar (hRW : RhsWHaar) (hSW : GaugeShiftW) (hLW : RhsWLim) : WbHaar :=
  wbHaar_of (rankGauge_of hRW) hSW hLW

end Formalism.L2.SG.Pf.GE
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NormSqLine
section
noncomputable section

open MeasureTheory Matrix
open scoped ComplexConjugate

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL

section Pos

variable {n r k : ℕ} (ε : Fin n → Bool)

def hJL (x : Fin n → ℂ) : (Fin n → ℂ) →ₗ[ℂ] ℂ where
  toFun v := hJ ε x v
  map_add' v w := UnitaryIsometries.hJ_add_right ε x v w
  map_smul' a v := by simp [UnitaryIsometries.hJ_smul_right]

end Pos

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames
end
end

-- bundled from Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RootCoordinateFrames
section
noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S
open scoped InnerProductSpace ComplexConjugate ENNReal
open Matrix

namespace Formalism.L2.SG.RealObj.RootCoordinateFrames

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NRealize : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ),
    (∀ a b, hJ ε (e a) (e b) = 0) → (∀ a b, hJ ε (f a) (f b) = 0) →
    (∀ a b, hJ ε (e a) (f b) = if a = b then 1 else 0) →
    (∀ a, hJ ε (e a) z = 0 ∧ hJ ε (f a) z = 0) → hJ ε z z ≠ 0 →
    ∀ P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ, IsLoUni P →
      ∃ s : Formalism.REAL.UJ ε, InN ε e z (uMat s) ∧ ∀ a, uMat s *ᵥ fam e z a = ∑ c, P a c • fam e z c

def RootCoordFrame : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (e f : Fin r → Fin n → ℂ) (z : Fin n → ℂ),
    (∀ a b, hJ ε (f a) (e b) = if a = b then 1 else 0) → (∀ a, hJ ε (f a) z = 0) →
    ∀ (g : Matrix (Fin n) (Fin n) ℂ) (P : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
      (∀ a, g *ᵥ fam e z a = ∑ c, P a c • fam e z c) →
      ∀ a : Fin r, rootCoord ε e f z g a = P a.succ a.castSucc

def TraceSum : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (g : ℕ) (x : X.B.I.E),
    ∏ v, Complex.exp (2 * Real.pi * Complex.I * ((X.B.I.φ v x + star (X.B.I.φ v x)) / (g : ℂ))) =
      Formalism.L2.SG.PairVal.psiInf g (X.ιE x)

def ZhatNAct : Prop :=
  ∀ (n r : ℕ) (ε : Fin n → Bool) (f f' : Fin (r + 1) → Fin n → ℂ) (s si s' g : Matrix (Fin n) (Fin n) ℂ)
    (P P' : Matrix (Fin (r + 1)) (Fin (r + 1)) ℂ),
    si * s = 1 → (∀ x y, hJ ε (s *ᵥ x) (s *ᵥ y) = hJ ε x y) →
    (∀ a, s *ᵥ f a = ∑ c, P a c • f c) → (∀ b, s' *ᵥ f' b = ∑ c, P' b c • f' c) →
    Zhat ε f f' (si * g * s') = P.map star * Zhat ε f f' g * P'.transpose

def FrameAtV : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F),
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0) ∧
    (∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.eR b)) = if a = b then 1 else 0) ∧
    (∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 ∧
      hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0) ∧
    hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw u : ℂ) ∧ Tw u ≠ 0

end Formalism.L2.SG.RealObj.RootCoordinateFrames
end
end

