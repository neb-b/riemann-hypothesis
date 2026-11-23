module

public import Mathlib
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.HermitianLattices.HermitianLatticesProofs.MassTelescope
public import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
public import Formalism.FlagUnipotentLattices.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LValEtaBounds
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0009
public import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0002
public import Formalism.FormalDegreeBessel.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicLeviEmbeddingHomomorphismProperties
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicStabilizerRadicalStructure
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnipotentLeviRadicalCoordsHomeomorph
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0215
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRadicalNormalFormPairOfFlags
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.CuspFrame
public import Development.AbelianVarietyTheory.BlockTheory.SiegelWeilLocal.Bundle0001
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0019
public import Formalism.LocalToGlobal.Divisibility.Bundle0004
public import Formalism.LocalToGlobal.GroupLattices.JointServices.LevelOperatorFixesImage
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0221

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.OneLeRatioMul
section
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.MainNotions.S
open scoped ENNReal Classical

namespace GlobalTheory.MassRatioInvBound

attribute [local instance] Formalism.BasicNotions.Host.cmStar

private lemma sqrt_pow_eq_pow_sqrt (a : ℝ) (ha : 0 ≤ a) (f : ℕ) : Real.sqrt (a ^ f) = Real.sqrt a ^ f := by
  rw [← Real.sqrt_sq (pow_nonneg (Real.sqrt_nonneg a) f), ← pow_mul, mul_comm, pow_mul,
    Real.sq_sqrt ha]

private lemma one_le_factorial_mul_exp_div_pow (k : ℕ) (hk : 1 ≤ k) :
    1 ≤ ((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hk0 : (0 : ℝ) < (k : ℝ) ^ k := pow_pos hkpos k
  have hn : (k - 1).factorial * k = k.factorial := by
    rw [mul_comm]; exact Nat.mul_factorial_pred (by omega)
  have hf : ((k - 1).factorial : ℝ) * k = (k.factorial : ℝ) := by exact_mod_cast hn
  rw [hf, le_div_iff₀ hk0, one_mul, Real.exp_one_pow]
  have h := Real.pow_div_factorial_le_exp (x := (k : ℝ)) (Nat.cast_nonneg k) k
  have hfac : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  rw [div_le_iff₀ hfac] at h
  rw [mul_comm]
  exact h

theorem one_le_ratio_mul (f k : ℕ) (v L : ℝ) (hv : 0 < v) (hk : 1 ≤ k) (hL : ((2 : ℝ) ^ f)⁻¹ ≤ L) :
    1 ≤ (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt ((2 * v) ^ f) * L *
      ((Real.exp 1 * Real.pi / (k * v)) ^ (k * f) * (2 * (k : ℝ) * (2 * v) ^ ((1 : ℝ) / 2)) ^ f) := by
  have hkpos : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hpi := Real.pi_pos
  have hs0 : 0 < Real.sqrt (2 * v) := Real.sqrt_pos.mpr (by linarith)
  have hrp : (2 * v) ^ ((1 : ℝ) / 2) = Real.sqrt (2 * v) := by rw [Real.sqrt_eq_rpow]
  rw [hrp, sqrt_pow_eq_pow_sqrt (2 * v) (by linarith) f, pow_mul]

  have hcol : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) ^ f / Real.sqrt (2 * v) ^ f * L *
      (((Real.exp 1 * Real.pi / (k * v)) ^ k) ^ f * (2 * (k : ℝ) * Real.sqrt (2 * v)) ^ f) =
      ((((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
        (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v)) ^ f * L := by
    rw [div_pow, mul_pow, mul_pow]
    ring

  have hbase : (((k - 1).factorial : ℝ) * (v / Real.pi) ^ k) * (Real.exp 1 * Real.pi / (k * v)) ^ k *
      (2 * (k : ℝ) * Real.sqrt (2 * v)) / Real.sqrt (2 * v) =
      (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) * 2 := by
    have hv0 : v ≠ 0 := hv.ne'
    have hk0 : (k : ℝ) ≠ 0 := hkpos.ne'
    have hp0 : Real.pi ≠ 0 := hpi.ne'
    have hs : Real.sqrt (2 * v) ≠ 0 := hs0.ne'
    rw [div_pow, div_pow, mul_pow, mul_pow]
    field_simp
  rw [hcol, hbase, mul_pow]
  have hA := one_le_factorial_mul_exp_div_pow k hk
  have hAf : 1 ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f := one_le_pow₀ hA
  have h2 : 1 ≤ (2 : ℝ) ^ f * L := by
    have h := mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 2 ^ f)
    rwa [mul_inv_cancel₀ (by positivity)] at h
  calc (1 : ℝ) = 1 * 1 := by ring
    _ ≤ (((k - 1).factorial : ℝ) * k * (Real.exp 1) ^ k / (k : ℝ) ^ k) ^ f * ((2 : ℝ) ^ f * L) :=
        mul_le_mul hAf h2 zero_le_one (by linarith)
    _ = _ := by ring

theorem stdH_eq (D : D7) (j : ℕ) : Cnt.stdH D.host.E j = massTelescope_form D.host.E j := rfl

theorem stdLat_eq (D : D7) (j : ℕ) : Cnt.stdLat D.host.E j = massTelescope_lat D.host.E j := by
  unfold Cnt.stdLat massTelescope_lat
  congr 2
  funext i
  simp [Pi.basisFun_apply]

theorem massS_eq (D : D7) (j : ℕ) :
    Cnt.massS D j = mass (massTelescope_form D.host.E j) (massTelescope_lat D.host.E j) := by
  unfold Cnt.massS Cnt.massU
  rw [stdH_eq, stdLat_eq]

theorem mass_pred_le : ∀ D : D7, UnitaryVolumeMass.stMassRatio D → Cnt.massS D (D.R.k - 1) ≤ Cnt.massS D D.R.k * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) * (2 * (D.R.k : ℝ) * D.host.rdE ^ ((1 : ℝ) / 2)) ^ D.R.f) := by
  intro D hM
  have hk : 5 ≤ D.R.k := D.R.k_ge
  have hrd : D.host.rdE = 2 * D.host.v := by
    unfold Formalism.BasicNotions.Host.v
    ring
  have hv : 0 < D.host.v := by
    unfold Formalism.BasicNotions.Host.v Formalism.BasicNotions.Host.rdE
    have hd : (0 : ℝ) < |(NumberField.discr D.host.E : ℝ)| :=
      abs_pos.mpr (Int.cast_ne_zero.mpr (NumberField.discr_ne_zero D.host.E))
    exact div_pos (Real.rpow_pos_of_pos hd _) two_pos
  have hK : Formalism.HermitianLatticesTheory.IsCMUnram D.host.E := D.sp.cm.cmUnram
  have hL := (GlobalTheory.EtaValueBound.lValEta_bounds D.host.E hK D.R.k (by omega)).1
  rw [Formalism.MainNotions.StandardLattice.fDeg_host] at hL
  have hrat := hM D.R.k (by omega) (Fin D.R.k → D.host.E) (Fin (D.R.k - 1) → D.host.E)
    (massTelescope_form D.host.E D.R.k) (massTelescope_form D.host.E (D.R.k - 1))
    (massTelescope_lat D.host.E D.R.k) (massTelescope_lat D.host.E (D.R.k - 1))
    (massTelescope_symm D.host.E _) (massTelescope_symm D.host.E _)
    (massTelescope_ortho D.host.E _) (massTelescope_ortho D.host.E _)
  unfold massRatioRightSide at hrat
  rw [Formalism.MainNotions.StandardLattice.fDeg_host, Formalism.MainNotions.StandardLattice.vInv_host] at hrat
  have key := one_le_ratio_mul D.R.f D.R.k D.host.v (lValEta D.host.E D.R.k) hv (by omega) hL
  rw [massS_eq, massS_eq, hrd]
  set a := mass (massTelescope_form D.host.E D.R.k) (massTelescope_lat D.host.E D.R.k) with ha
  set b := mass (massTelescope_form D.host.E (D.R.k - 1)) (massTelescope_lat D.host.E (D.R.k - 1))
    with hb
  set R := (((D.R.k - 1).factorial : ℝ) * (D.host.v / Real.pi) ^ D.R.k) ^ D.R.f /
    Real.sqrt ((2 * D.host.v) ^ D.R.f) * lValEta D.host.E D.R.k with hR

  have hb0 : 0 ≤ b := by
    rw [hb]
    unfold mass
    split_ifs
    · exact Finset.sum_nonneg fun _ _ => by positivity
    · exact le_rfl
  have hRpos : 0 < R := by
    have h2 : (0 : ℝ) < (2 ^ D.R.f)⁻¹ := by positivity
    have hLpos : 0 < lValEta D.host.E D.R.k := lt_of_lt_of_le h2 hL
    have hpi := Real.pi_pos
    rw [hR]
    positivity
  have hbne : b ≠ 0 := by
    intro h0
    rw [h0, div_zero] at hrat
    linarith
  have hab : a = R * b := by rw [← hrat, div_mul_cancel₀ a hbne]
  rw [hab]
  calc b = b * 1 := (mul_one b).symm
    _ ≤ b * (R * ((Real.exp 1 * Real.pi / (D.R.k * D.host.v)) ^ (D.R.k * D.R.f) *
        (2 * (D.R.k : ℝ) * (2 * D.host.v) ^ ((1 : ℝ) / 2)) ^ D.R.f)) :=
        mul_le_mul_of_nonneg_left key hb0
    _ = _ := by ring

end GlobalTheory.MassRatioInvBound
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RootMeasureEqNormalFormRootMeasure
section
noncomputable section

open MeasureTheory Matrix Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf GlobalTheory.Amp
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.RootNormal

variable {k r : ℕ}

theorem continuous_conj (a : Mat k r) : Continuous (conjM a : Mt k r → Mt k r) :=
  (continuous_const.matrix_mul (continuous_id (X := Mat k r))).matrix_mul continuous_const

theorem det_Hpk : IsUnit (Hpk k r).det :=
  Matrix.isUnit_det_of_right_inverse (hpkFacts k r).2.1

theorem unit_det {g : Mat k r} (hg : g ∈ GG k r) : IsUnit g.det :=
  ((uHGroup _ _ det_Hpk).2.2 g hg).1

theorem mem_S (z : Fin (2 * r + k + 1) → ℂ) {n : Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, ⟨(uHGroup _ _ det_Hpk).1, fun a => by simp, by simp⟩, n, hn, by simp⟩

theorem twoFl_of {z z' : Fin (2 * r + k + 1) → ℂ} {n n' g : Mat k r} (hn : n ∈ Nset k r) (hn' : n' ∈ Nset k r)
    (h : TwoFl k r z z' (n * g * n')) : TwoFl k r z z' g := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  refine ⟨h1, h2, h3, h4, ?_, ?_, ?_⟩
  · have G := uHGroup _ _ (det_Hpk (k := k) (r := r))
    have e : g = n⁻¹ * (n * g * n') * n'⁻¹ := by
      rw [Matrix.mul_assoc n, Matrix.nonsing_inv_mul_cancel_left _ _ (unit_det hn.1),
        Matrix.mul_nonsing_inv_cancel_right _ _ (unit_det hn'.1)]
    rw [e]
    exact G.2.1 _ (G.2.1 _ (G.2.2 _ hn.1).2 _ h5) _ (G.2.2 _ hn'.1).2
  · rwa [gInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h6
  · unfold Dr at h7 ⊢
    rwa [dInv k r z z' h1 h2 _ (mem_S z hn) _ (mem_S z' hn')] at h7

def patEquiv (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    UTin (fun a : Fin r => blockIdx p.1 a.val) ≃ rootPat p :=
  Equiv.ofBijective
    (fun q => ⟨(q.1.1.1.castSucc, q.1.1.2.castSucc), by
      simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨Fin.castSucc_lt_castSucc_iff.2 q.1.2, q.2⟩⟩)
    (by
      constructor
      · rintro ⟨⟨⟨a, b⟩, h1⟩, h2⟩ ⟨⟨⟨c, d⟩, h3⟩, h4⟩ e
        simp only [Subtype.mk.injEq, Prod.mk.injEq, Fin.castSucc_inj] at e
        obtain ⟨rfl, rfl⟩ := e
        rfl
      · rintro ⟨⟨a, b⟩, hq⟩
        simp only [rootPat, Finset.mem_filter, Finset.mem_univ, true_and] at hq
        obtain ⟨h1, h2⟩ := hq
        have h1' : a.val < b.val := h1
        have ha : a.val < r := by omega
        have hb : b.val < r := by
          by_contra hb
          have : b.val = r := by omega
          exact h ⟨a.val, ha⟩ (h2.trans (congrArg (blockIdx p.1) this))
        exact ⟨⟨⟨(⟨a.val, ha⟩, ⟨b.val, hb⟩), h1'⟩, h2⟩, rfl⟩)

theorem card_le (p : Point ℂ (r + 1)) (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) :
    (rootPat p).card ≤ r ^ 2 := by
  rw [← Fintype.card_coe, ← Fintype.card_congr (patEquiv p h)]
  refine (Fintype.card_subtype_le _).trans ((Fintype.card_subtype_le _).trans ?_)
  simp [sq]

theorem measurable_rootCoords (z : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1)) :
    Measurable (rootCoords k r z p) := by
  refine Continuous.measurable (continuous_pi fun q => ?_)
  unfold rootCoords flagMat
  split_ifs
  · unfold Matrix.mulVec dotProduct
    simp only [Matrix.of_apply]
    fun_prop
  all_goals exact continuous_const

theorem measurable_in (β : Fin r → ℕ) :
    Measurable fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r) := by
  have : Continuous fun x : UTin β → ℂ => uEmb k r (upperIn β x) := by
    refine (NCoord.cont_uEmb k r).comp (continuous_pi fun q => ?_)
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
  exact (show Continuous (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) from this).measurable

theorem pOf_mem (q : PPar k r) : pOf k r q ∈ Nset k r :=
  (((Rad.radical k r).1 _ _).2.2.2 ((Rad.radical k r).2.1 _ _)).1

theorem pOf_e (q : PPar k r) (a : Fin r) : pOf k r q *ᵥ bvec (eI k r a) = bvec (eI k r a) :=
  ((Rad.radical k r).1 _ _).1 a

theorem pOf_inv_e (q : PPar k r) (a : Fin r) : (pOf k r q)⁻¹ *ᵥ bvec (eI k r a) = bvec (eI k r a) := by
  conv_lhs => rw [← pOf_e q a]
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (unit_det (pOf_mem q).1), Matrix.one_mulVec]

theorem conj_entry (q : PPar k r) (u : Matrix (Fin r) (Fin r) ℂ) (a b : Fin r) :
    (((pOf k r q)⁻¹ * uEmb k r u * pOf k r q) *ᵥ bvec (eI k r b)) (eI k r a) = u a b := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, pOf_e, UEmb.uEmb_eI, Matrix.mulVec_sum]
  simp only [Matrix.mulVec_smul, pOf_inv_e]
  simp [bvec, Pi.single_apply, UEmb.eI_inj, Finset.sum_apply]

theorem conj_mem {P Q g x : Mat k r} (hP : P ∈ Nset k r) (hQ : Q ∈ Nset k r) (hg : g ∈ GG k r) (hx : x ∈ Rset k r g) :
    P * x * P⁻¹ ∈ Rset k r (Q * g * P⁻¹) := by
  have N := nSubgroup k r
  refine ⟨N.2.1 _ (N.2.1 _ hP _ hx.1) _ (N.2.2 _ hP), ?_⟩
  have e : Q * g * P⁻¹ * (P * x * P⁻¹) * (Q * g * P⁻¹)⁻¹ = Q * (g * x * g⁻¹) * Q⁻¹ := by
    have hu := unit_det hP.1
    simp only [Matrix.mul_inv_rev, Matrix.nonsing_inv_nonsing_inv _ hu, Matrix.mul_assoc,
      Matrix.nonsing_inv_mul_cancel_left _ _ hu]
  rw [e]
  exact N.2.1 _ (N.2.1 _ hQ _ hx.2) _ (N.2.2 _ hQ)

theorem eq_map (z' : Fin (2 * r + k + 1) → ℂ) (p : Point ℂ (r + 1))
    (h : ∀ a : Fin r, blockIdx p.1 a.val ≠ blockIdx p.1 r) {g : Mat k r} (hg : g ∈ GG k r) (p₁ p₀ : PPar k r)
    (hN : IsNormal k r (fun a => blockIdx p.1 a.val) (pOf k r p₁ * g * (pOf k r p₀)⁻¹))
    (μ : Measure (Mt k r)) (c : ℝ≥0∞) (h0 : μ {x | Matrix.of x ∉ Rset k r g} = 0)
    (h1 : μ.map (rootCoords k r z' p) = c • volume) :
    μ = (c • lebR k r (fun a => blockIdx p.1 a.val)).map (conjM (pOf k r p₀)⁻¹) := by
  set β : Fin r → ℕ := fun a => blockIdx p.1 a.val with hβ
  have hu := unit_det (pOf_mem p₀).1
  let E : (rootPat p → ℂ) → (UTin β → ℂ) := fun y q => y (patEquiv p h q)
  have hE : MeasurePreserving E volume volume :=
    (volume_measurePreserving_piCongrLeft (fun _ : rootPat p => ℂ) (patEquiv p h)).symm _
  have hF := measurable_in (k := k) β
  have hC := (continuous_conj (pOf k r p₀)⁻¹).measurable
  have hR := measurable_rootCoords z' p
  have key : ∀ x : Mt k r, Matrix.of x ∈ Rset k r g →
      conjM (pOf k r p₀)⁻¹ (Matrix.of.symm (uEmb k r (upperIn β (E (rootCoords k r z' p x))))) = x := by
    intro x hx
    have h2 := conj_mem (pOf_mem p₀) (pOf_mem p₁) hg hx
    rw [(_root_.GlobalTheory.Amp.StabNormal.stabiliser_normal k r _ _ hN).1] at h2
    obtain ⟨y, hy⟩ := h2
    have hx' : Matrix.of x = (pOf k r p₀)⁻¹ * uEmb k r (upperIn β y) * pOf k r p₀ := by
      simp only at hy
      rw [hy]
      simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu, Matrix.nonsing_inv_mul _ hu, Matrix.mul_one]
    have hy' : E (rootCoords k r z' p x) = y := by
      funext q
      change flagMat k r z' (Matrix.of x) q.1.1.1.castSucc q.1.1.2.castSucc = _
      unfold flagMat fvec
      rw [dif_pos (show q.1.1.1.castSucc.val < r from q.1.1.1.2), dif_pos (show q.1.1.2.castSucc.val < r from q.1.1.2.2), hx']
      refine (conj_entry p₀ _ q.1.1.1 q.1.1.2).trans ?_
      unfold upperIn upper
      rw [dif_pos q.1.2]
      exact dif_pos q.2
    rw [hy']
    unfold conjM
    rw [Matrix.nonsing_inv_nonsing_inv _ hu]
    exact hx'.symm
  have hae : (conjM (pOf k r p₀)⁻¹ ∘ (fun x : UTin β → ℂ => (Matrix.of.symm (uEmb k r (upperIn β x)) : Mt k r)) ∘ E ∘
      rootCoords k r z' p) =ᵐ[μ] id := by
    apply measure_mono_null _ h0
    intro x hx
    exact fun hx' => hx (key x hx')
  have := Measure.map_congr (mβ := inferInstance) hae
  rw [Measure.map_id, ← Measure.map_map hC (hF.comp (hE.measurable.comp hR)), ← Measure.map_map hF (hE.measurable.comp hR),
    ← Measure.map_map hE.measurable hR, h1] at this
  refine this.symm.trans ?_
  congr 1
  unfold lebR
  rw [Measure.map_smul c hE.measurable.aemeasurable, hE.map_eq, Measure.map_smul c hF.aemeasurable]

theorem rootMeas_normR : ∀ (D : D7) (z z' : (Fin (2 * D.R.rS + D.R.k + 1) → ℂ)) (p : Point ℂ (D.R.rS + 1)) (γ : MatKR D.R.k D.R.rS) (μR : Measure (Mt D.R.k D.R.rS)) (θ' : ℝ), TwoFl D.R.k D.R.rS z z' γ → IsRootMeasR D z z' p γ μR → 0 ≤ θ' → 0 ≤ D.host.ka / gg D → (rootPat p).card ≤ D.R.rS ^ 2 ∧ NormR D.R.k D.R.rS γ (θ' * (2 * D.host.ka / gg D / (2 * Real.pi)) ^ (rootPat p).card) (ENNReal.ofReal θ' • μR) := by
  intro D z z' p γ μR θ' hT hR hθ _
  obtain ⟨n, hn, n', hn', g, rfl, hZ, μ, h0, h1, rfl⟩ := hR
  have hg := twoFl_of hn hn' hT
  obtain ⟨p₁, p₀, -, hN, -, h⟩ := _root_.GlobalTheory.Amp.NormalEx.normal_form _ _ z z' g p hg hZ
  have N := nSubgroup D.R.k D.R.rS
  have hu₀ := unit_det (pOf_mem p₀).1
  have hu₁ := unit_det (pOf_mem p₁).1
  refine ⟨card_le p h, n * (pOf _ _ p₁)⁻¹, N.2.1 _ hn _ (N.2.2 _ (pOf_mem p₁)), pOf _ _ p₀ * n',
    N.2.1 _ (pOf_mem p₀) _ hn', _, _, hN, ?_, ?_⟩
  · simp only [Matrix.mul_assoc, Matrix.nonsing_inv_mul_cancel_left _ _ hu₀, Matrix.nonsing_inv_mul_cancel_left _ _ hu₁]
  · have e1 : (fun x : Mt D.R.k D.R.rS => fun i j => (n'⁻¹ * Matrix.of x * n') i j) = conjM n'⁻¹ := by
      funext x
      unfold conjM
      rw [Matrix.nonsing_inv_nonsing_inv _ (unit_det hn'.1)]
    have e2 : (conjM (pOf _ _ p₀ * n')⁻¹ : Mt D.R.k D.R.rS → _) = conjM n'⁻¹ ∘ conjM (pOf _ _ p₀)⁻¹ := by
      funext x
      change (pOf _ _ p₀ * n')⁻¹ * Matrix.of x * (pOf _ _ p₀ * n')⁻¹⁻¹ =
        n'⁻¹ * ((pOf _ _ p₀)⁻¹ * Matrix.of x * (pOf _ _ p₀)⁻¹⁻¹) * n'⁻¹⁻¹
      simp only [Matrix.mul_inv_rev, Matrix.mul_assoc]
    rw [e1, e2, eq_map z' p h hg.2.2.2.2.1 p₁ p₀ hN μ _ h0 h1,
      Measure.map_map (continuous_conj _).measurable (continuous_conj _).measurable,
      ENNReal.ofReal_mul hθ, mul_smul, Measure.map_smul (ENNReal.ofReal θ')
        (((continuous_conj _).measurable.comp (continuous_conj _).measurable).aemeasurable)]

end GlobalTheory.Amp.RootNormal
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.SummableOfSupport
section
open NumberField Finset Formalism.MainNotions.S GlobalTheory.Count

namespace GlobalTheory.FarTerms

private lemma indicator_eq_indicator_inter_support {α : Type} (S : Set α) (F : α → ℝ) :
    S.indicator F = ({a | a ∈ S ∧ F a ≠ 0} : Set α).indicator F := by
  funext a
  by_cases hS : a ∈ S <;> by_cases hF : F a = 0 <;> simp [Set.indicator, hS, hF]

theorem summable_of_support {α : Type} (S : Set α) (F : α → ℝ) (C : ℝ)
    (h : Summable (fun γ : {a // a ∈ S ∧ F a ≠ 0} => F γ.1) ∧
      ∑' γ : {a // a ∈ S ∧ F a ≠ 0}, F γ.1 ≤ C) :
    Summable (fun γ : S => F γ.1) ∧ ∑' γ : S, F γ.1 ≤ C := by
  obtain ⟨hs, hle⟩ := h
  have key := indicator_eq_indicator_inter_support S F
  have hT : Summable (({a | a ∈ S ∧ F a ≠ 0} : Set α).indicator F) :=
    (summable_subtype_iff_indicator (s := {a | a ∈ S ∧ F a ≠ 0}) (f := F)).1 hs
  rw [← key] at hT
  refine ⟨(summable_subtype_iff_indicator (s := S) (f := F)).2 hT, ?_⟩
  rw [tsum_subtype S F, key, ← tsum_subtype {a | a ∈ S ∧ F a ≠ 0} F]
  exact hle

private lemma one_le_n_of_sigIs_of_one_le_q (B : RowsAut) (p q : ℕ) (hS : SigIs B p q) (hq : 1 ≤ q) :
    1 ≤ B.I.n := by
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace B.I.F))
  have h1 : B.I.qAt v = q := (hS v).2
  have h2 : B.I.qAt v ≤ B.I.n := by
    show (Finset.univ.filter fun a => B.I.ε v a = false).card ≤ B.I.n
    exact (Finset.card_filter_le _ _).trans (by simp)
  omega

theorem farBound_of_ptBound : GlobalTheory.Deep.PtBound → GlobalTheory.Deep.FarBound := by
  intro hP B d p q h ep hDS hSig hqm hq1 hGap hep0 hepc hlog hhep hhep2 h120 x
  have hn : 1 ≤ B.I.n := one_le_n_of_sigIs_of_one_le_q B p q hSig hq1
  have h120' : 120 * (B.I.n : ℝ) * ((min p q : ℕ) : ℝ) ^ ((3 : ℝ) / 2) ≤ h := by
    rw [← hqm]; exact h120
  obtain ⟨hdec, hbd, -, -, -, hK, -⟩ := hP B d p q h hDS hSig hGap h120'
  rw [← hqm] at hdec
  have hdec' := hdec hq1
  have hne : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, phe B d (x⁻¹ * γ.1 * x) ≠ 0 := by
    intro γ h0
    exact γ.2.2 (by simp [h0])
  have hM0 : 0 ≤ (∏ v, d v) * (B.e 1).re := (norm_nonneg _).trans (hbd 1)
  rcases eq_or_lt_of_le hM0 with hM | hM
  · haveI : IsEmpty {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} :=
      ⟨fun γ => hne γ (norm_eq_zero.1 (le_antisymm ((hbd _).trans_eq hM.symm) (norm_nonneg _)))⟩
    refine summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x)
      (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨summable_empty, ?_⟩
    rw [tsum_empty, ← hM]
    simp
  · have hMne : (∏ v, d v) * (B.e 1).re ≠ 0 := hM.ne'
    have hA : 0 ≤ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x := by
      unfold GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor; positivity
    have hq1r : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    have hc : 0 < Real.sqrt (2 * (q : ℝ)) := Real.sqrt_pos.2 (by linarith)
    have hdist : ∀ (γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}) (v : InfinitePlace B.I.F),
        0 ≤ GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) := by
      intro γ v; unfold GlobalTheory.Count.dHS; exact Real.sqrt_nonneg _
    have hcount : ∀ r : InfinitePlace B.I.F → ℝ, (∀ v, 0 ≤ r v) →
        {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}.Finite ∧
        (({γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v}.ncard : ℕ) : ℝ) ≤
          GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x * Real.exp (2 * (B.I.n : ℝ) ^ 2 * ∑ v, r v) := by
      intro r hr
      obtain ⟨hfin, hcard⟩ := GlobalTheory.AutBall.autBallCount B.I hn x r hr
      have hmaps : ∀ γ ∈ {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v},
          (γ.1 : B.I.GA) ∈ GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.ballSet B.I x r := by
        intro γ hγ
        have hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1 := γ.2.1
        show γ.1 ∈ B.I.GFset ∧ (x⁻¹ * γ.1 * x).2 ∈ B.I.Kset ∧
          ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v
        exact ⟨hm.1, hK _ (hne γ), hγ⟩
      have hinj : Set.InjOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1)
          {γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} | ∀ v, GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ≤ r v} :=
        fun a _ b _ hab => Subtype.ext hab
      refine ⟨(hfin.preimage Subtype.val_injective.injOn).subset hmaps, ?_⟩
      have hle := Set.ncard_le_ncard_of_injOn (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => γ.1) hmaps hinj hfin
      have hAB : GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x = GlobalTheory.IndefiniteRowSideFullHecke.AutomorphicBallCount.bigA B.I x := rfl
      rw [hAB]
      exact (Nat.cast_le.2 hle).trans hcard
    have hfar : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ∃ v, ep < GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) := by
      intro γ
      have hm : γ.1 ∈ B.I.GFset ∧ ¬ GlobalTheory.Count.IsNear B d ep x γ.1 := γ.2.1
      by_contra hcon
      push_neg at hcon
      exact hm.2 (by unfold GlobalTheory.Count.IsNear; exact ⟨hm.1, hne γ, hcon⟩)
    have hw : ∀ γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, 0 ≤ ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ∧
        ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re) ≤
          ∏ v, Real.exp (-(h / 8) * min (GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) ^ 2)
            (GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)) / Real.sqrt (2 * (q : ℝ)))) := by
      intro γ
      refine ⟨div_nonneg (norm_nonneg _) hM.le, ?_⟩
      rw [div_le_iff₀ hM]
      exact le_of_le_of_eq (hdec' (x⁻¹ * γ.1 * x)) (mul_comm _ _)
    obtain ⟨hsum, hle⟩ := GlobalTheory.sum_over_dyadic_shells {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} (InfinitePlace B.I.F)
      (fun γ v => GlobalTheory.Count.dHS (uMat ((x⁻¹ * γ.1 * x).1 v)))
      (fun γ => ‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re))
      (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x) (2 * (B.I.n : ℝ) ^ 2) h ep (Real.sqrt (2 * (q : ℝ)))
      hA (by positivity) hep0 hc hepc hlog (by linarith) hhep2 hdist hcount hfar hw
    have hfun : (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖) =
        fun γ => (∏ v, d v) * (B.e 1).re * (‖phe B d (x⁻¹ * γ.1 * x)‖ / ((∏ v, d v) * (B.e 1).re)) := by
      funext γ
      rw [mul_div_assoc', mul_comm, mul_div_assoc, div_self hMne, mul_one]
    have hs' : Summable (fun γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0} => ‖phe B d (x⁻¹ * γ.1 * x)‖) := by
      rw [hfun]; exact hsum.mul_left _
    have hle' : ∑' γ : {a // a ∈ GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x ∧ ‖phe B d (x⁻¹ * a * x)‖ ≠ 0}, ‖phe B d (x⁻¹ * γ.1 * x)‖ ≤
        (∏ v, d v) * (B.e 1).re * GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
          (2 * (B.I.f : ℝ) * 3 ^ B.I.f * Real.exp (-(h * ep ^ 2 / 16))) := by
      rw [hfun, tsum_mul_left]
      calc _ ≤ (∏ v, d v) * (B.e 1).re * (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.latFactor B.I x *
              (2 * (Fintype.card (InfinitePlace B.I.F) : ℝ) * 3 ^ Fintype.card (InfinitePlace B.I.F) *
                Real.exp (-(h * ep ^ 2 / 16)))) := mul_le_mul_of_nonneg_left hle hM.le
        _ = _ := by rw [GlobalTheory.Count.FrameMajorant.card_places B.I]; ring
    exact summable_of_support (GlobalTheory.IndefiniteRowSideFullHecke.FarTermsLatticeBound.farSet B d ep x)
      (fun a => ‖phe B d (x⁻¹ * a * x)‖) _ ⟨hs', hle'⟩

end GlobalTheory.FarTerms
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.V0MapIotaEqTopDefinite
section
open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Indef NumberField

theorem GlobalTheory.V0_map_iota_eq_top_of_definite : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 I0 Ty T : Type) (m : ℕ) (A3 : FamIn3 D.what₂.LL G Pl0 I0 Ty T m) (P0 : Subgroup G) (ψ0 : P0 →* D.what₂.LLˣ) (Ps : Subgroup G) (ψs : Ps →* D.what₂.LLˣ) (Zs : DefSub A3.fam3.amb3) (S0 : IndefData (A3.side3 P0 ψ0 Zs)) (S1 : IndefData (A3.side3 Ps ψs Zs)) (X0 : BaseLevelRowSide D) (Dc : DefCols (A3.side3 Ps ψs Zs)) (Sp : SPer Dc) (C : ColData Dc Sp S1) (NuC : ∀ u, Submodule (𝓞 D.what₂.LL) (Fin (Dc.a u) → D.what₂.LL)) (I : DivisionCompatibilityDataThreeSided D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc), DivDef3 D A3 P0 ψ0 Ps ψs Zs S0 S1 X0 C NuC I → (∃ s, A3.A.fam.Ok s) → Function.Surjective ((A3.side3 Ps ψs Zs).Pq A3.A.μ0).mulVec → Function.Surjective (S1.ι A3.A.μ0).mulVec → (D.what₂.V0 D.what₂.mu0).map (D.what₂.iota D.what₂.mu0) = ⊤ := by
  intro D G _ _ Pl0 I0 Ty T m A3 P0 ψ0 Ps ψs Zs S0 S1 X0 Dc Sp C NuC I hD hOk hPq hι
  obtain ⟨s, hs⟩ := hOk

  have key := GlobalTheory.rowSide_iota_maps_fixedColumns_onto_of_matrices D (I.tup A3.A.μ0) _ _ _ _
    (I.jA A3.A.μ0) (rE D A3.A Ps ψs A3.A.μ0) (rV0 D A3.A Ps ψs A3.A.μ0)
    ((A3.side3 Ps ψs Zs).Pq A3.A.μ0) (S1.ι A3.A.μ0) I.eRR
    (fun x => (hD.sharp.forms A3.A.μ0).op_eq x)
    (fun F => Formalism.L2.G.ServJoint.level_operator_fixes_image hs Ps ψs (A3.fam3.toSub2 Zs) A3.A.μ0 F)
    hPq hι (fun F => hD.sharp.iota A3.A.μ0 F)
  rw [hD.tup.mu0] at key
  exact key
end

