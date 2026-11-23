module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
public import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.Bundle0001
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.Vanish
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0013
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.PlacesOf
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Formalism.SharpRestriction.CuspSpanNormBounds.LeadMinorK
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralLeOfHighest
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CayleyExistsAndAny
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.BesselSubgroupProductMeasureIsHaar
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0073
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0051
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0094
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusWeightEigenAndRootShift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0108
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianStabiliserRationalUnitriangularPairs
public import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
public import Formalism.SharpRestriction.CuspSpanNormBounds.PsiEDef
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
public import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitriangularStabilizerPointMatrixBlockDiagonal
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0001
public import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
public import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.RealObj
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0057
public import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermWeightEqCharacterMulInv
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HL.TermPhase

section Tri

variable {E V : Type} [CommRing E] [AddCommGroup V] [Module E V] {r : ℕ}

def lowSpan (E : Type) [CommRing E] [Module E V] (f : Fin (r + 1) → V) (b : ℕ) : Submodule E V := Submodule.span E (f '' {c | (c : ℕ) < b})

theorem lowSpan_mono (f : Fin (r + 1) → V) {b b' : ℕ} (h : b ≤ b') :
    lowSpan E f b ≤ lowSpan E f b' :=
  Submodule.span_mono (Set.image_mono fun _ hc => lt_of_lt_of_le hc h)

abbrev IsTriW (f : Fin (r + 1) → V) (g : V ≃ₗ[E] V) : Prop := ∀ b : Fin (r + 1), g (f b) - f b ∈ lowSpan E f b

theorem map_lowSpan {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : IsTriW f g) (b : ℕ) :
    ∀ x ∈ lowSpan E f b, g x ∈ lowSpan E f b := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨c, hc, rfl⟩ := hy
    have h1 : f c ∈ lowSpan E f b := Submodule.subset_span ⟨c, hc, rfl⟩
    have h2 : g (f c) - f c ∈ lowSpan E f b := lowSpan_mono f (le_of_lt hc) (hg c)
    have := add_mem h2 h1
    simpa using this
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx

theorem exists_pre_lowSpan {f : Fin (r + 1) → V} {g : V ≃ₗ[E] V} (hg : IsTriW f g) :
    ∀ b : ℕ, ∀ x ∈ lowSpan E f b, ∃ y ∈ lowSpan E f b, g y = x := by
  intro b
  induction b with
  | zero =>
    intro x hx
    have h0 : lowSpan E f 0 = ⊥ := by simp [lowSpan]
    rw [h0, Submodule.mem_bot] at hx
    exact ⟨0, zero_mem _, by simp [hx]⟩
  | succ b ih =>
    intro x hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨c, hc, rfl⟩ := hy
      have hc' : (c : ℕ) < b ∨ (c : ℕ) = b := by
        have : (c : ℕ) < b + 1 := hc
        omega
      rcases hc' with hlt | heq
      · obtain ⟨w, hw, hgw⟩ := ih (f c) (Submodule.subset_span ⟨c, hlt, rfl⟩)
        exact ⟨w, lowSpan_mono f (Nat.le_succ b) hw, hgw⟩
      · obtain ⟨w, hw, hgw⟩ := ih (g (f c) - f c) (by rw [← heq]; exact hg c)
        refine ⟨f c - w, sub_mem (Submodule.subset_span ⟨c, hc, rfl⟩) (lowSpan_mono f (Nat.le_succ b) hw), ?_⟩
        rw [map_sub, hgw]; abel
    | zero => exact ⟨0, zero_mem _, map_zero g⟩
    | add x x' _ _ hx hx' =>
      obtain ⟨y, hy, rfl⟩ := hx
      obtain ⟨y', hy', rfl⟩ := hx'
      exact ⟨y + y', add_mem hy hy', map_add g y y'⟩
    | smul a x _ hx =>
      obtain ⟨y, hy, rfl⟩ := hx
      exact ⟨a • y, Submodule.smul_mem _ a hy, map_smul g a y⟩

def triSub (f : Fin (r + 1) → V) : Subgroup (V ≃ₗ[E] V) where
  carrier := {g | IsTriW f g}
  one_mem' := by
    rw [Set.mem_ofPred_eq]; intro b
    show f b - f b ∈ lowSpan E f b
    simp
  mul_mem' := by
    intro g g' hg hg'
    rw [Set.mem_ofPred_eq] at hg hg' ⊢
    intro b
    show g (g' (f b)) - f b ∈ lowSpan E f b
    have : g (g' (f b)) - f b = g (g' (f b) - f b) + (g (f b) - f b) := by rw [map_sub]; abel
    rw [this]
    exact add_mem (map_lowSpan hg b _ (hg' b)) (hg b)
  inv_mem' := by
    intro g hg
    rw [Set.mem_ofPred_eq] at hg ⊢
    intro b
    show g.symm (f b) - f b ∈ lowSpan E f b
    obtain ⟨y, hy, hgy⟩ := exists_pre_lowSpan hg b (f b - g (f b)) (by
      have := neg_mem (hg b)
      simpa using this)
    have : g.symm (f b) - f b = g.symm (f b - g (f b)) := by
      rw [map_sub, LinearEquiv.symm_apply_apply]
    rw [this, ← hgy, LinearEquiv.symm_apply_apply]
    exact hy

end Tri

theorem hf_add_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (x x' y : Fin n → E) :
    hf L Hm (x + x') y = hf L Hm x y + hf L Hm x' y := by
  simp [hf, add_mul, Finset.sum_add_distrib]

theorem hf_smul_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (a : E) (x y : Fin n → E) :
    hf L Hm (a • x) y = a * hf L Hm x y := by
  simp [hf, Finset.mul_sum, mul_assoc]

theorem hf_zero_left' {F E : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [CommRing E] [Algebra F E]
    [TopologicalSpace E] (L : Loc.LocE F E) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E) (y : Fin n → E) :
    hf L Hm 0 y = 0 := by
  simp [hf]

section Loc

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Loc.Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

theorem nset_sub {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) :
    Fr.NSet ⊆ ((triSub (E := E) Fr.f : Subgroup (V ≃ₗ[E] V)) : Set (V ≃ₗ[E] V)) := by
  rintro g ⟨-, hF, hP⟩ b
  induction b using Fin.lastCases with
  | last =>
    have hz : Fr.f (Fin.last r) ∈ H.perp (H.X Fr.f) := by
      show ∀ x ∈ H.X Fr.f, H.h (Fr.f (Fin.last r)) x = 0
      intro x hx
      have h0 : H.h x (Fr.f (Fin.last r)) = 0 := by
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨a, rfl⟩ := hy
          exact Fr.h_iso _ _ (Or.inl (Fin.castSucc_lt_last a).ne)
        | zero => exact H.h_zero_left _
        | add x y _ _ hx hy => rw [H.h_add_left, hx, hy, add_zero]
        | smul a x _ hx => rw [H.h_smul_left, hx, mul_zero]
      rw [H.h_herm x, h0, map_zero]
    have h1 := hP _ hz
    have h2 : H.X Fr.f ≤ lowSpan E Fr.f (Fin.last r : ℕ) := by
      refine Submodule.span_le.mpr ?_
      rintro _ ⟨a, rfl⟩
      exact Submodule.subset_span ⟨a.castSucc, by simp, rfl⟩
    exact h2 h1
  | cast a =>
    have hv : Fr.f a.castSucc ∈ Fr.Fj (a.val + 1) := Submodule.subset_span ⟨a, by simp, rfl⟩
    have h1 := hF (a.val + 1) (by have := a.isLt; omega) _ hv
    simp only [Nat.add_sub_cancel] at h1
    have h2 : Fr.Fj a.val ≤ lowSpan E Fr.f (a.castSucc : ℕ) := by
      refine Submodule.span_mono ?_
      rintro _ ⟨a', ha', rfl⟩
      exact ⟨a'.castSucc, by simpa using ha', rfl⟩
    exact h2 h1

theorem mem_span_of_mem_N {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) {n : V ≃ₗ[E] V} (hn : n ∈ Fr.N)
    (b : Fin (r + 1)) : n (Fr.f b) ∈ Submodule.span E (Set.range Fr.f) := by
  have hT : IsTriW Fr.f n := (Subgroup.closure_le (triSub (E := E) Fr.f)).mpr (nset_sub Fr) hn
  have h1 : lowSpan E Fr.f b ≤ Submodule.span E (Set.range Fr.f) :=
    Submodule.span_mono (Set.image_subset_range _ _)
  have := add_mem (h1 (hT b)) (Submodule.subset_span ⟨b, rfl⟩ : Fr.f b ∈ Submodule.span E (Set.range Fr.f))
  simpa using this

theorem coef_eq {H : Loc.HermSp M V} (Fr : LocNG.FrameD H r) {n : ℕ} (Hm : Matrix (Fin n) (Fin n) E)
    (e : V ≃ₗ[E] (Fin n → E)) (g : Fin (r + 1) → Fin n → E) (gs : Fin r → Fin n → E)
    (hg : ∀ a, g a = e (Fr.f a)) (hd : ∀ a j, hf M.L Hm (g a) (gs j) = if a = j.castSucc then 1 else 0)
    (j : Fin r) (x : V) (hx : x ∈ Submodule.span E (Set.range Fr.f)) :
    H.h x (Fr.es j) = hf M.L Hm (e x) (gs j) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨a, rfl⟩ := hy
    rw [← hg a, hd a j]
    induction a using Fin.lastCases with
    | last =>
      have h0 : H.h (Fr.f (Fin.last r)) (Fr.es j) = 0 := by
        rw [H.h_herm (Fr.es j) (Fr.f (Fin.last r)), Fr.h_sz j, map_zero]
      rw [h0, if_neg (Fin.castSucc_lt_last j).ne']
    | cast i =>
      rw [Fr.h_es i j]
      simp [Fin.castSucc_inj]
  | zero => rw [H.h_zero_left, map_zero, hf_zero_left']
  | add x y _ _ hx hy => rw [H.h_add_left, map_add (f := _), hf_add_left', hx, hy]
  | smul a x _ hx => rw [H.h_smul_left, map_smul, hf_smul_left', hx]

end Loc

theorem om_eq_psi_mul_inv : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Loc.Model F E) {V : Type} [AddCommGroup V] [Module E V] (H : Loc.HermSp M V) (r k : ℕ) (P : LocNG.FPair H r) (S : Frames M.L r k) (c : WCoord P S) (d : LocNG.Datum P) (t : Loc.Term V M r), LocNG.IsTermOver P d t → ∀ m m' : S.GLV, (∀ b, c.e (t.f b) = m (S.f b)) → (∀ b, c.e (t.f' b) = m' (S.f' b)) → LocNG.om P t = S.psi m * (S.psi' m')⁻¹ := by
  intro F _ _ _ E _ _ _ _ M V _ _ H r k P S c d t hT m m' hm hm'
  obtain ⟨-, -, ⟨n, hn, hfn, -⟩, ⟨n', hn', hfn', -⟩, -⟩ := hT
  have hth : LocNG.theta M = S.th := by
    unfold LocNG.theta Frames.th
    cases hs : M.split with
    | none => simp [c.gg_none hs]
    | some g =>
      obtain ⟨h1, h2⟩ := c.gg_some g hs
      simp [h1, h2]
  have h1 : (∑ a : Fin r, H.h (t.f a.succ) (P.A.es a)) = ∑ j, S.h (m (S.f j.succ)) (S.es j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hm]
    refine coef_eq P.A S.Hm c.e S.f S.es c.f_eq (fun a j => S.dual a j) j _ ?_
    rw [hfn]; exact mem_span_of_mem_N P.A hn _
  have h2 : (∑ a : Fin r, H.h (t.f' a.succ) (P.B.es a)) = ∑ j, S.h (m' (S.f' j.succ)) (S.es' j) := by
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← hm']
    refine coef_eq P.B S.Hm c.e S.f' S.es' c.f'_eq (fun a j => S.dual' a j) j _ ?_
    rw [hfn']; exact mem_span_of_mem_N P.B hn' _
  simp only [LocNG.om, LocNG.FrameD.psiOf, LocNG.FrameD.coefSum, Frames.psi, Frames.psi', Frames.psiOf,
    Frames.coef, hth, h1, h2]

end GlobalTheory.HL.TermPhase
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.MassBoundLowTypesSum
section
noncomputable section

namespace GlobalTheory.MomOne

section prelim

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

theorem single_moment_le (Ω : Type) [MeasurableSpace Ω] (ν : Measure Ω) (r q : ℕ) (len : Fin (r + 1) → Ω → ℝ)
    (Ph : Ω → ℝ) (A Rr : ℝ) (hm : ∀ a, AEMeasurable (len a) ν) (hpos : ∀ a, ∀ᵐ x ∂ν, 0 < len a x)
    (hPh : AEMeasurable Ph ν) (h0 : ∀ x, 0 ≤ Ph x) (hmass : ∫⁻ x, ENNReal.ofReal (Ph x) ∂ν = 1) (hA : 0 ≤ A)
    (hR : 1 ≤ Rr)
    (h1 : ∀ q' ≤ (r + 1) * q, ∫⁻ x, ENNReal.ofReal (len 0 x ^ (2 * q') * Ph x) ∂ν ≤ ENNReal.ofReal (A ^ q'))
    (h2 : ∀ a : Fin r, ∀ q' ≤ (r + 1) * q,
      ∫⁻ x, ENNReal.ofReal ((len a.succ x / len a.castSucc x) ^ (2 * q') * Ph x) ∂ν
        ≤ ENNReal.ofReal (Rr ^ (2 * q'))) (a : Fin (r + 1)) :
    ∫⁻ x, ENNReal.ofReal (len a x ^ (2 * q) * Ph x) ∂ν ≤ ENNReal.ofReal ((A * Rr ^ (2 * r)) ^ q) := by
  choose l hlm hlp hle using fun a => GlobalTheory.MomentHolder.exists_pos_version ν (len a) (hm a) (hpos a)
  have hall : ∀ᵐ x ∂ν, ∀ a, len a x = l a x := ae_all_iff.2 hle
  set μ : Measure Ω := ν.withDensity fun x => ENNReal.ofReal (Ph x) with hμ
  have : IsProbabilityMeasure μ := ⟨by
    rw [hμ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ, hmass]⟩
  have hR0 : 0 ≤ Rr := zero_le_one.trans hR
  have hsq : ∀ q : ℕ, Real.sqrt A ^ (2 * q) = A ^ q := fun q => by
    rw [pow_mul, Real.sq_sqrt hA]
  have hup := Formalism.HermitianLatticeCounting.P.corollary_upper_estimate_holds Ω μ r q l (Real.sqrt A) Rr hlm hlp
    (Real.sqrt_nonneg A) hR0
    (fun q hq => by
      rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0 _ ((hlm 0).pow_const _), hsq]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h1 q hq)
      filter_upwards [hall] with x hx
      rw [hx])
    (fun c q hq => by
      rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0
        (fun ω => (l c.succ ω / l c.castSucc ω) ^ (2 * q)) (((hlm _).div (hlm _)).pow_const _)]
      refine le_of_eq_of_le (lintegral_congr_ae ?_) (h2 c q hq)
      filter_upwards [hall] with x hx
      rw [hx, hx]) a
  rw [hμ, GlobalTheory.MomentHolder.lintegral_density ν Ph hPh h0 _ ((hlm a).pow_const _), hsq] at hup
  refine le_of_eq_of_le (lintegral_congr_ae ?_) (hup.trans (ENNReal.ofReal_le_ofReal ?_))
  · filter_upwards [hall] with x hx
    rw [hx]
  · rw [mul_pow, ← pow_mul Rr]
    refine mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hR ?_) (by positivity)
    have := Nat.mul_le_mul_left (2 * q) (Nat.lt_succ_iff.1 a.isLt)
    calc 2 * q * a.val ≤ 2 * q * r := this
      _ = 2 * r * q := by ring

variable {k r : ℕ}

theorem lenA_mul_unitary (z : Fin (2 * r + k + 1) → ℂ) (x : Mx k r) {g : Mx k r}
    (hg : g ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ) (a : Fin (r + 1)) :
    lenA k r z (x * g) a = lenA k r z x a := by
  have h1 : star g * g = 1 := Matrix.mem_unitaryGroup_iff'.1 hg
  have h2 : g * star g = 1 := Matrix.mem_unitaryGroup_iff.1 hg
  have hinv : g⁻¹ = star g := Matrix.inv_eq_left_inv h1
  let L : EuclideanSpace ℂ (Fin (2 * r + k + 1)) →ₗ[ℂ] EuclideanSpace ℂ (Fin (2 * r + k + 1)) :=
    Matrix.toEuclideanLin (star g)
  have hL : ∀ v, WithLp.toLp 2 (star g *ᵥ v) = L (WithLp.toLp 2 v) := fun v => rfl
  have hiso : Isometry L := by
    refine AddMonoidHomClass.isometry_of_norm L ((LinearMap.norm_map_iff_inner_map_map L).2 fun v w => ?_)
    rw [EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
    show (star g *ᵥ w.ofLp) ⬝ᵥ star (star g *ᵥ v.ofLp) = _
    rw [Matrix.star_mulVec, dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.vecMul_vecMul,
      ← Matrix.star_eq_conjTranspose, star_star, h2, Matrix.vecMul_one, dotProduct_comm]
  unfold lenA
  simp only [Matrix.mul_inv_rev, hinv, ← Matrix.mulVec_mulVec, hL]
  rw [← Set.image_image L, ← Submodule.map_span, Submodule.map_coe, Metric.infDist_image hiso]

theorem lintegral_rmul {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp]
    {z : Fin (2 * r + k + 1) → ℂ} {π : Mx k r → (Wp →L[ℂ] Wp)} {u : ℕ → ℝ}
    {μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)} (hS : SideG k r z π u μW μN μG νq) (F : Mx k r → ℝ)
    (hF : ContinuousOn F (GG k r)) (hinv : ∀ s ∈ Formalism.QuantumDeterminants.Sset k r z, ∀ x ∈ GG k r, F (s * x) = F x)
    {g : Mx k r} (hg : g ∈ GG k r) :
    ∫⁻ x, ENNReal.ofReal (F (Matrix.of x * g)) ∂νq = ∫⁻ x, ENNReal.ofReal (F (Matrix.of x)) ∂νq := by
  classical
  obtain ⟨hz, hT, -, -, hW, hN, hG, hq⟩ := hS
  obtain ⟨hGG, hGH⟩ := GlobalTheory.unitaryGroup_matGroup_unimodular k r
  obtain ⟨hGH1, hGH2⟩ := hGH μG hG
  obtain ⟨hSG, hsub, hS1, hS2⟩ := GlobalTheory.muSof_isHaar k r z μW μN hz hT hW hN
  have hset : PI.QuotientSetting (GG k r) (Formalism.QuantumDeterminants.Sset k r z) μG (muSof μW μN) νq :=
    ⟨hGG, hSG, hsub, hGH1, hS1, hGH2, hS2, hq⟩
  obtain ⟨h0, h1⟩ := Formalism.FourierDecayAlt.P.DDSmoothness.muSof_facts hW hN
  have hae := Formalism.FourierDecayAlt.P.DDSmoothness.ae_UH_of_quot hG.2.2.1 h0 h1 hq
  set A : Set (Formalism.QuantumDeterminants.Mt k r) := {x | Matrix.of x ∈ GG k r} with hA
  have hAm : MeasurableSet A := by
    have := (Formalism.FourierDecayAlt.P.DDSmoothness.uh_measurableSet (k := k) (r := r)).compl
    convert this using 1
    ext x
    simp [hA]
  have hc : ContinuousOn (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) A := hF
  have hm : Measurable (A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0)) :=
    hc.measurable_piecewise continuousOn_const hAm
  have hval : ∀ x : Formalism.QuantumDeterminants.Mt k r, Matrix.of x ∈ GG k r →
      A.piecewise (fun x : Formalism.QuantumDeterminants.Mt k r => F (Matrix.of x)) (fun _ => 0) x = F (Matrix.of x) :=
    fun x hx => Set.piecewise_eq_of_mem _ _ _ hx
  have key := GlobalTheory.QuotRightInv.quotInv _ _ _ _ _ _ hset _ hm.ennreal_ofReal (fun s hs x hx => by
    rw [hval x hx]
    exact congrArg ENNReal.ofReal
      ((hval (fun i j => (s * Matrix.of x) i j) (hGG.2.2.1 s (hsub hs) _ hx)).trans (hinv s hs _ hx))) g hg
  refine Eq.trans (lintegral_congr_ae (hae.mono fun x hx => ?_))
    (key.trans (lintegral_congr_ae (hae.mono fun x hx => congrArg ENNReal.ofReal (hval x hx))))
  exact congrArg ENNReal.ofReal (hval (fun i j => (Matrix.of x * g) i j) (hGG.2.2.1 _ hx g hg)).symm

theorem conj_back {ε : Fin (2 * r + k + 1) → Bool} {Q g : Mx k r} (hQ : PI.UpqRep.IsCayleyU k r ε Q)
    (hg : g ∈ PI.UpqRep.Kset ε) :
    Q⁻¹ * g * Q ∈ GG k r ∧ Q⁻¹ * g * Q ∈ Matrix.unitaryGroup (Fin (2 * r + k + 1)) ℂ := by
  have q1 : Qᴴ * Q = 1 := Matrix.mem_unitaryGroup_iff'.1 hQ.2
  have q2 : Q * Qᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hQ.2
  have qi : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv q1
  have hJ : gᴴ * PI.UpqRep.Jm ε * g = PI.UpqRep.Jm ε := GlobalTheory.CayleyChoice.Kset_sub hg
  have hH : Qᴴ * PI.UpqRep.Jm ε * Q = Formalism.QuantumDeterminants.Hpk k r := hQ.1.2
  rw [qi]
  refine ⟨?_, Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hQ.2) hg.1) hQ.2⟩
  show (Qᴴ * g * Q)ᴴ * Formalism.QuantumDeterminants.Hpk k r * (Qᴴ * g * Q) = Formalism.QuantumDeterminants.Hpk k r
  rw [← hH]
  calc (Qᴴ * g * Q)ᴴ * (Qᴴ * PI.UpqRep.Jm ε * Q) * (Qᴴ * g * Q)
      = Qᴴ * (gᴴ * (Q * Qᴴ) * PI.UpqRep.Jm ε * (Q * Qᴴ) * g) * Q := by
        simp only [conjTranspose_mul, conjTranspose_conjTranspose, Matrix.mul_assoc]
    _ = _ := by rw [q2, Matrix.mul_one, Matrix.mul_one, hJ]

theorem norm_sq_scaled {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] (t : ℝ) (q : ℕ) {d : ℝ}
    (hd : 0 ≤ d) (v : Wp) : ‖((t ^ q * Real.sqrt d : ℝ) : ℂ) • v‖ ^ 2 = t ^ (2 * q) * (d * ‖v‖ ^ 2) := by
  rw [norm_smul, mul_pow, Complex.norm_real, Real.norm_eq_abs, sq_abs, mul_pow, Real.sq_sqrt hd]
  ring

end prelim

section main

open BranchingSupport GlobalTheory.CellAmp GlobalTheory.Amp Formalism.BasicNotions Formalism.MainNotions.S Formalism.QuantumDeterminants Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

end main

end GlobalTheory.MomOne
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalCommonStabiliserUnitriangularCoords
section
open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.HL GlobalTheory.LocOver
open scoped Pointwise ENNReal Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.HL.StCoord

theorem zh_eq (D : D7) (Z : LocDat D) {T T' : D.host.E} (F0 : LFlag (D.sp.Y 0) D.R.rS T) (F0' : LFlag (D.sp.Y 0) D.R.rS T')
    (FP : ∀ p : PlF D, LocNG.FPair (locH Z p) D.R.rS) (G : GFrames (placesOf Z) D.R.rS D.R.k)
    (c : GCoord Z F0 F0' FP G) : G.Zh = ZhatL F0 F0' := by
  have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
    rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
  funext a b
  have := c.h_eq (frame F0' b) (frame F0 a)
  simp only [GFrames.Zh, Matrix.of_apply, c.f_eq, c.f'_eq]
  simp only [hs]
  exact this

theorem stab_coords : ∀ (D : D7) (X : HidaSetting D) (Y : Full X) (u u' : D.what₂.Word), Formalism.MainNotions.S.Cnt.Stand D u u' → 4 * D.R.rS + 7 ≤ D.R.k → ∀ (w : Point D.host.E (D.R.rS + 1)) (F00 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u).A.T : ℕ) : D.host.E)) (F'0 : LFlag (D.sp.Y 0) D.R.rS (((D.mem u').A.T : ℕ) : D.host.E)) (FP : ∀ p : PlF D, LocNG.FPair (locH (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p) D.R.rS), ZhatOM (ZhatL F00 F'0) = ptMat w → Gval F00 F'0 ≠ 0 → (∀ p, AtBase (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) p F00 F'0 (Tu D u) (Tu D u') (FP p) ∧ (FP p).RelG (LocNG.theta (Y.M p))) → ∀ (G : GFrames (placesOf (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D)) D.R.rS D.R.k) (c : GCoord (⟨Y.δ, Y.M, Y.agree⟩ : LocDat D) F00 F'0 FP G), (∀ x ∈ G.St, ∃ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B ∧ (∀ b, x (G.f' b) = ∑ a, B a b • G.f' a) ∧ ∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) ∧ ∀ B : Formalism.L2.SG.PairVal.MatR D, IsUpUni B → (∀ a b : Fin (D.R.rS + 1), Formalism.L2.SG.RealObj.blkOf w.1 a.1 ≠ Formalism.L2.SG.RealObj.blkOf w.1 b.1 → B a b = 0) → ∃! x, x ∈ G.St ∧ ∀ b, x (G.f' b) = ∑ a, B a b • G.f' a := by
  intro D X Y u u' _ _ w F00 F'0 FP hw _ _ G c
  have hZ : Formalism.MainNotions.S.ZhatOM G.Zh = Formalism.MainNotions.S.ptMat w := by rw [zh_eq D _ F00 F'0 FP G c]; exact hw
  have hinv : ∀ x, (D.conjF : D.host.E →+* D.host.E) ((D.conjF : D.host.E →+* D.host.E) x) = x := by
    intro x
    have hs : ∀ x : D.host.E, D.conjF x = star x := fun x => by
      rw [D.conjF_eq]; exact (Formalism.BasicNotions.Examples₂.star_eq_conj D.host x).symm
    show D.conjF (D.conjF x) = x
    rw [hs, hs, star_star]
  obtain ⟨hb1, hb2⟩ := _root_.GlobalTheory.PointStab.stab_blockDiag (D.conjF : D.host.E →+* D.host.E) hinv D.R.rS w G.Zh hZ
  have up : ∀ s : Matrix (Fin (D.R.rS + 1)) (Fin (D.R.rS + 1)) D.host.E,
      ((∀ i j, j < i → s i j = 0) ∧ (∀ i, s i i = 1)) ↔ Formalism.MainNotions.S.IsUpUni s := by
    intro s
    constructor
    · rintro ⟨h1, h2⟩ i j; exact ⟨h1 i j, fun h => h ▸ h2 i⟩
    · intro h; exact ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩
  refine ⟨fun x hx => ?_, fun B hB hBb => ?_⟩
  · obtain ⟨s, s', hs, hs', hf, hf'⟩ := _root_.GlobalTheory.HL.StTri.stab_unitriangular _ _ _ G x hx
    have hZs := (_root_.GlobalTheory.HL.RatStab.stab_rat _ _ _ G s s' hs hs').2 ⟨x, hx, hf, hf'⟩
    exact ⟨s', (up s').1 hs', hf', hb1 s s' ((up s).1 hs) ((up s').1 hs') hZs⟩
  · obtain ⟨s, hs, hZs⟩ := hb2 B hB hBb
    obtain ⟨h, hh, -, hh'⟩ := (_root_.GlobalTheory.HL.RatStab.stab_rat _ _ _ G s B ((up s).2 hs) ((up B).2 hB)).1 hZs
    refine ⟨h, ⟨hh, hh'⟩, fun y ⟨hy, hy'⟩ => ?_⟩
    have h1 : h⁻¹ * y = 1 := by
      refine _root_.GlobalTheory.HL.StabFix.eq_one_of_fix _ _ _ G _ (G.St.mul_mem (G.St.inv_mem hh) hy) fun b => ?_
      show h.symm (y (G.f' b)) = G.f' b
      rw [hy', ← hh' b, LinearEquiv.symm_apply_apply]
    calc y = h * (h⁻¹ * y) := by group
      _ = h := by rw [h1, mul_one]

end GlobalTheory.HL.StCoord
end

