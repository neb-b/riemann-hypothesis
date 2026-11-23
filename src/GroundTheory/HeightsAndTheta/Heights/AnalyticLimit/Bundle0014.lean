module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0013
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0012
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0006
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0007
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0008
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Stokes
public import ReciprocityTheory.AnalyticForms.PotentialTheory.SNCAtlas
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0002
public import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLCurveA
public import ReciprocityTheory.AnalyticForms.PotentialTheory.PLLocalStatement
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import ReciprocityTheory.AnalyticForms.PotentialTheory.AtlasIndep
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassReplace
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassError
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0004
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0009

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.OfListTailLog
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

theorem GreenMassStep.full : GreenMassStep.Statement := GreenMassStep.proof

theorem GreenMassReplace.full : GreenMassReplace.Statement := GreenMassReplace.proof

theorem GreenMassError.full : GreenMassError.Statement := GreenMassError.proof

theorem UniformIntegrability.full : UniformIntegrability.Statement :=
  UniformIntegrability.of_greenMass GreenMassStep.full GreenMassReplace.full GreenMassError.full

theorem ListTailLog.of_lemmaE (hE : LemmaETailLog.Statement) (hM : ListMono.Statement)
    (hC : RegSection.Statement) (hS : TailShift.Statement) : ListTailLog.Statement :=
  ListTailLog.proof hE hM hC hS

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M

theorem lemmaEEnergy_step {n : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (A : FinHolAtlas (n + 1) X) (Om : KaehlerForm A) (u : Fin (n + 1) → X → ℝ) (w : X → ℝ)
    (hu : ∀ i, A.Smooth (u i)) (hpsh : ∀ i, IsPsh A (potForm Om.pot (u i))) (j : Fin (n + 1))
    (hj : ∀ x, -1 ≤ u j x ∧ u j x ≤ 0) (hw : A.Smooth w) (hwp : IsPsh A (potForm Om.pot w)) :
    mInt A (fun i => potForm Om.pot (u i)) (fun x => -w x) ≤
      mInt A (fun i => potForm Om.pot (Function.update u j 0 i)) (fun x => -w x) + Om.vol := by
  set σ : Equiv.Perm (Fin (n + 1)) := Equiv.swap 0 j with hσdef
  have hσ : ∀ i : Fin n, σ i.succ ≠ j := by
    intro i h
    have h' : σ (σ i.succ) = σ j := congrArg σ h
    rw [Equiv.swap_apply_self, hσdef, Equiv.swap_apply_right] at h'
    exact Fin.succ_ne_zero i h'
  let d : EnergyStep.Data A Om :=
    { w := w, v := u j, f := fun i => u (σ i.succ), M := 1, w_smooth := hw, w_psh := hwp,
      v_smooth := hu j, v_nonpos := fun x => (hj x).2, le_v := fun x => (hj x).1,
      f_smooth := fun _ => hu _, f_psh := fun _ => hpsh _ }
  have h := EnergyStep.proof A Om d
  rw [← mIntSymm A _ σ, ← mIntSymm A (fun i => potForm Om.pot (Function.update u j 0 i)) σ]
  have e1 : mInt A ((fun i => potForm Om.pot (u i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons (Om.pot + LocPot.ofFun d.v) d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [σ, d, potForm]
    · simp [d, EnergyStep.Data.T, potForm]
  have e2 : mInt A ((fun i => potForm Om.pot (Function.update u j 0 i)) ∘ σ) (fun x => -w x) =
      mInt A (Fin.cons Om.pot d.T) (fun x => -w x) := by
    apply st_mInt_congr_phi
    intro i
    refine Fin.cases ?_ (fun i => ?_) i
    · funext x y
      simp [σ, potForm, locPot_add_φ, LocPot.ofFun]
    · simp [d, EnergyStep.Data.T, potForm, Function.update_of_ne (hσ i)]
  rw [e1, e2]
  simpa [d] using h

theorem LemmaEEnergy.proof : LemmaEEnergy.Statement := by
  intro D X _ _ _ A Om v w hv hpsh hb hw hwp
  cases D with
  | zero =>
    have e : (fun i : Fin 0 => potForm Om.pot (v i)) = fun _ => Om.pot := funext fun i => i.elim0
    simp [e]
  | succ n =>
    let u : ℕ → Fin (n + 1) → X → ℝ := fun k i => if (i : ℕ) < k then v i else 0
    have hu : ∀ k i, A.Smooth (u k i) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hv i, st_smooth_const A 0]
    have hup : ∀ k i, IsPsh A (potForm Om.pot (u k i)) := fun k i => by
      dsimp only [u]; split_ifs
      exacts [hpsh i, isPsh_add_const Om.isPsh 0]
    have key : ∀ k ≤ n + 1, mInt A (fun i => potForm Om.pot (u k i)) (fun x => -w x) ≤
        mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) + k * Om.vol := by
      intro k
      induction k with
      | zero => intro _; simp
      | succ k ih =>
        intro hk
        have hupd : Function.update (u (k + 1)) ⟨k, hk⟩ 0 = u k := by
          funext i
          by_cases h : i = ⟨k, hk⟩
          · subst h; simp [u]
          · rw [Function.update_of_ne h]
            have hik : (i : ℕ) ≠ k := fun e => h (Fin.ext e)
            by_cases hlt : (i : ℕ) < k
            · simp [u, hlt, Nat.lt_succ_of_lt hlt]
            · have : ¬ (i : ℕ) < k + 1 := by omega
              simp [u, hlt, this]
        have step := lemmaEEnergy_step A Om (u (k + 1)) w (hu _) (hup _) ⟨k, hk⟩
          (fun x => by simpa [u] using hb ⟨k, hk⟩ x) hw hwp
        rw [hupd] at step
        have := ih (by omega)
        push_cast
        linarith
    have h1 := key (n + 1) le_rfl
    have e1 : (fun i => potForm Om.pot (u (n + 1) i)) = fun i => potForm Om.pot (v i) :=
      funext fun i => by simp [u, i.isLt]
    have e0 : mInt A (fun i => potForm Om.pot (u 0 i)) (fun x => -w x) =
        mInt A (fun _ => Om.pot) (fun x => -w x) := by
      apply st_mInt_congr_phi
      intro i
      funext x y
      simp [u, potForm, locPot_add_φ, LocPot.ofFun]
    rw [e1, e0] at h1
    simpa using h1

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaEScale
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt maMeasure isPotentialAdd
  isPotentialRsmul isPotential_ofFun isPshAdd isPshRsmul maMeasureMono maMeasure_thm mIntegrableCont
  mIntSymm mIntRsmul st_mInt_congr_phi)

theorem isPsh_of_φ_eq {e : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas e X}
    {P Q : LocPot X} (hP : IsPsh A P) (hU : ∀ x, Q.U x ⊆ P.U x) (hφ : Q.φ = P.φ) : IsPsh A Q := by
  intro x j y hy w
  rw [hφ]
  exact hP x j y ⟨hy.1, hU x hy.2⟩ w

theorem mInt_update_rsmul {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (j : Fin e) (g : X → ℝ) :
    mInt A (Function.update Φ j ((Φ j).rsmul c)) g = c * mInt A Φ g := by
  obtain _ | n := e
  · exact j.elim0
  set q := Φ ∘ Equiv.swap 0 j with hq
  have h1 : Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j =
      Fin.cons ((q 0).rsmul c) (Fin.tail q) := by
    funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [hq]
    · have hne : Equiv.swap 0 j i.succ ≠ j := by
        intro h
        rw [Equiv.swap_apply_eq_iff, Equiv.swap_apply_right] at h
        exact Fin.succ_ne_zero _ h
      simp only [Function.comp_apply, Fin.cons_succ, Fin.tail, hq, Function.update_of_ne hne]
  calc mInt A (Function.update Φ j ((Φ j).rsmul c)) g
      = mInt A (Function.update Φ j ((Φ j).rsmul c) ∘ Equiv.swap 0 j) g := (mIntSymm A _ _ g).symm
    _ = mInt A (Fin.cons ((q 0).rsmul c) (Fin.tail q)) g := by rw [h1]
    _ = c * mInt A (Fin.cons (q 0) (Fin.tail q)) g :=
        mIntRsmul A c _ _ (hΦ _) (fun i => hΦ _) g
    _ = c * mInt A Φ g := by rw [Fin.cons_self_tail, hq, mIntSymm]

theorem mInt_rsmul_all {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) (c : ℝ)
    (Φ : Fin e → LocPot X) (hΦ : ∀ i, IsPotential A (Φ i)) (g : X → ℝ) :
    mInt A (fun i => (Φ i).rsmul c) g = c ^ e * mInt A Φ g := by
  have key : ∀ k ≤ e, mInt A (fun i : Fin e => if (i : ℕ) < k then (Φ i).rsmul c else Φ i) g =
      c ^ k * mInt A Φ g := by
    intro k
    induction k with
    | zero => intro _; simp
    | succ k ih =>
      intro hk
      set Ψ : Fin e → LocPot X := fun i => if (i : ℕ) < k then (Φ i).rsmul c else Φ i with hΨ
      have hΨp : ∀ i, IsPotential A (Ψ i) := fun i => by
        simp only [hΨ]; split_ifs
        · exact isPotentialRsmul A c _ (hΦ i)
        · exact hΦ i
      have h : (fun i : Fin e => if (i : ℕ) < k + 1 then (Φ i).rsmul c else Φ i) =
          Function.update Ψ ⟨k, hk⟩ ((Ψ ⟨k, hk⟩).rsmul c) := by
        funext i
        by_cases hi : i = ⟨k, hk⟩
        · subst hi; simp [hΨ]
        · have hi' : (i : ℕ) ≠ k := fun h => hi (Fin.ext h)
          rw [Function.update_of_ne hi, hΨ]
          simp only [Nat.lt_succ_iff_lt_or_eq, hi', or_false]
      rw [h, mInt_update_rsmul A c Ψ hΨp, ih (Nat.le_of_succ_le hk), pow_succ]
      ring
  simpa using key e le_rfl

theorem LemmaEScale.proof : LemmaEScale.Statement := by
  intro D X _ _ _ A Om M v hM hv hpsh
  let _ : MeasurableSpace X := borel X
  have _ : BorelSpace X := ⟨rfl⟩
  have hM0 : M ≠ 0 := by positivity
  have hP : ∀ i, IsPotential A (potForm Om.pot (v i)) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ (hv i))
  have hW : ∀ i, IsPotential A (potForm Om.pot fun x => v i x / M) := fun i =>
    isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A _ fun j => (hv i j).div_const M)
  have hQ := isPotentialRsmul A (M - 1) _ Om.isPot
  have hQpsh := isPshRsmul A (M - 1) _ (by linarith) Om.isPot Om.isPsh
  refine ⟨fun i => ?_, fun g hg hg0 => ?_⟩
  · have h1 := isPshRsmul A M⁻¹ _ (by positivity) (hP i) (hpsh i)
    have h2 := isPshRsmul A (1 - M⁻¹) _ (by rw [sub_nonneg]; exact inv_le_one_of_one_le₀ hM)
      Om.isPot Om.isPsh
    refine isPsh_of_φ_eq (isPshAdd A _ _ (isPotentialRsmul A _ _ (hP i))
      (isPotentialRsmul A _ _ Om.isPot) h1 h2) (fun x y hy => ⟨hy, hy.1⟩) ?_
    funext x y
    show Om.pot.φ x y + v i y / M = M⁻¹ * (Om.pot.φ x y + v i y) + (1 - M⁻¹) * Om.pot.φ x y
    field_simp
    ring
  have hmono := maMeasureMono A _ (fun _ => Om.pot.rsmul (M - 1)) hP hpsh (fun _ => hQ)
    (fun _ => hQpsh)
  have hS : ∀ i, IsPotential A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPotentialAdd A _ _ (hP i) hQ
  have hSpsh : ∀ i, IsPsh A (potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) := fun i =>
    isPshAdd A _ _ (hP i) hQ (hpsh i) hQpsh
  obtain ⟨_, hT'⟩ := maMeasure_thm A _ hP hpsh
  obtain ⟨_, hS'⟩ := maMeasure_thm A _ hS hSpsh
  have hgm := hg.measurable
  have e1 := (hT' g hgm).2 (mIntegrableCont A _ hP g hg)
  have e2 := (hS' g hgm).2 (mIntegrableCont A _ hS g hg)
  have hint := (hS' g hgm).1.1 (mIntegrableCont A _ hS g hg)
  have hle : mInt A (fun i => potForm Om.pot (v i)) g ≤
      mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g := by
    rw [e1, e2]
    exact integral_mono_measure hmono (Filter.Eventually.of_forall hg0) hint
  have e3 : mInt A (fun i => potForm Om.pot (v i) + Om.pot.rsmul (M - 1)) g =
      mInt A (fun i => (potForm Om.pot fun x => v i x / M).rsmul M) g := by
    refine st_mInt_congr_phi A (fun i => ?_) g
    funext x y
    show Om.pot.φ x y + v i y + (M - 1) * Om.pot.φ x y = M * (Om.pot.φ x y + v i y / M)
    field_simp
    ring
  rw [e3, mInt_rsmul_all A M _ hW] at hle
  exact hle

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETailMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh)

theorem LemmaETailMass.proof (hT : LemmaETrunc.Statement) (hC : LemmaETruncMass.Statement)
    (hB : LemmaETruncTail.Statement) : LemmaETailMass.Statement := by
  intro X _ _ _ D A Om L s hL hs hd hle C₁ hC₁
  obtain ⟨K, hK0, hK⟩ := hB D A Om L s hL hs hd hle
  refine ⟨(C₁ + 2) ^ D * K, fun u hu R₀ hR₀ => ?_⟩
  have htr : ∀ R, Real.exp 1 ≤ R → ∀ i, ∃ v : X → ℝ, A.Smooth v ∧ IsPsh A (potForm Om.pot v) ∧
      (∀ x, -(C₁ * Real.log R + 2) ≤ v x ∧ v x ≤ 0) ∧
      ∃ c : ℝ, ∀ x ∈ secOpen s, rSec L s x < R → v x = u i x + c := fun R hR i =>
    hT A Om (secOpen s) (rSec L s) C₁ (u i) (isOpen_secOpen hL hs) hd
      (fun x _ => exp_one_le_rSec hle x) hC₁ (hu i).smooth (hu i).nonneg (hu i).nonpos (hu i).le_u
      (hu i).smooth_or_pole R hR
  classical
  let ut : ℝ → Fin D → X → ℝ := fun R i =>
    if h : Real.exp 1 ≤ R then Classical.choose (htr R h i) else fun _ => 0
  have hut : ∀ R (h : Real.exp 1 ≤ R) i, ut R i = Classical.choose (htr R h i) := fun R h i => by
    simp only [ut, dif_pos h]
  obtain ⟨hint, hle₁⟩ := hC D A Om (secOpen s) (rSec L s) u ut (isOpen_secOpen hL hs)
    (continuousOn_rSec hL hs) (fun i => (hu i).smooth) (fun i => (hu i).nonneg)
    (fun R hR i => by
      rw [hut R hR i]
      obtain ⟨h1, h2, -, h4⟩ := Classical.choose_spec (htr R hR i)
      exact ⟨h1, h2, h4⟩) R₀ hR₀
  refine ⟨hint, hle₁.trans ?_⟩
  have hlog : 1 ≤ Real.log R₀ := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hR₀
  have hM : 1 ≤ C₁ * Real.log R₀ + 2 := by nlinarith
  have hb := hK (C₁ * Real.log R₀ + 2) hM (ut R₀)
    (fun i => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).1)
    (fun i => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).2.1)
    (fun i x => by rw [hut R₀ hR₀ i]; exact (Classical.choose_spec (htr R₀ hR₀ i)).2.2.1 x) R₀ hR₀
  refine hb.trans ?_
  have hR₀pos : 0 < R₀ := lt_of_lt_of_le (Real.exp_pos 1) hR₀
  have hMle : C₁ * Real.log R₀ + 2 ≤ (C₁ + 2) * Real.log R₀ := by nlinarith
  have hpow : (C₁ * Real.log R₀ + 2) ^ D ≤ (C₁ + 2) ^ D * Real.log R₀ ^ D := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (by linarith) hMle D
  have hnum : (C₁ * Real.log R₀ + 2) ^ D * K ≤ (C₁ + 2) ^ D * K * Real.log R₀ ^ D := by
    calc (C₁ * Real.log R₀ + 2) ^ D * K ≤ (C₁ + 2) ^ D * Real.log R₀ ^ D * K :=
          mul_le_mul_of_nonneg_right hpow hK0
      _ = (C₁ + 2) ^ D * K * Real.log R₀ ^ D := by ring
  exact div_le_div_of_nonneg_right hnum hR₀pos.le

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLogNormSecIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection MIntegrable logNormSec locDens
  locDensCont)

theorem abs_log_mul_exp_le {a : ℝ} (t : ℝ) (ha : 0 ≤ a) :
    |Real.log (a * Real.exp t)| ≤ |Real.log a| + |t| := by
  rcases ha.eq_or_lt with h | h
  · subst h; simp
  · rw [Real.log_mul h.ne' (Real.exp_pos t).ne', Real.log_exp]; exact abs_add_le _ _

theorem LogNormSecIntegrable.proof : LogNormSecIntegrable.Statement := by
  intro D X _ A L s hL hs _ Φ hΦ j K hK hKc
  refine LocallyIntegrableOn.integrableOn_compact_subset ?_ hK hKc
  intro u0 hu0
  set c := A.chart j with hc
  set p := c.symm u0
  set V := c.target ∩ c.symm ⁻¹' L.U p with hVdef
  have hV : IsOpen V := c.isOpen_inter_preimage_symm (L.isOpen_U p)
  have hu0V : u0 ∈ V := ⟨hu0, L.mem_U p⟩
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hV u0 hu0V
  set B := Metric.closedBall u0 (r / 2) with hBdef
  have hBV : B ⊆ V := (Metric.closedBall_subset_ball (by linarith)).trans hball
  have hBc : IsCompact B := isCompact_closedBall _ _
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  refine ⟨B, mem_nhdsWithin_of_mem_nhds (Metric.closedBall_mem_nhds _ (by linarith)), ?_⟩
  set f : (Fin D → ℂ) → ℂ := s p ∘ c.symm with hfdef
  have hf : AnalyticOnNhd ℂ f V := hs.1 p j
  set φ : (Fin D → ℂ) → ℝ := L.φ p ∘ c.symm with hφdef
  have hφc : ContinuousOn φ V := (hL.1 p j).continuousOn
  have hF : ∀ u ∈ V, logNormSec L s (c.symm u) = Real.log (‖f u‖ * Real.exp (-φ u)) := fun u hu =>
    congrArg Real.log (hs.2 _ p _ ⟨L.mem_U _, hu.2⟩)
  have hDc : ContinuousOn (locDens A Φ j) B :=
    (locDensCont A Φ hΦ j).mono (hBV.trans Set.inter_subset_left)
  obtain ⟨M, hM⟩ := hBc.exists_bound_of_continuousOn hDc
  have hlogf : IntegrableOn (fun u => Real.log ‖f u‖) B :=
    (ReciprocityTheory.ChartRestriction.G.Geo.logAbsLocInt' D V f hV hf).integrableOn_compact_subset hBV hBc
  have hφi : IntegrableOn φ B := (hφc.mono hBV).integrableOn_compact hBc
  have hfc : ContinuousOn f B := fun u hu => (hf u (hBV hu)).continuousAt.continuousWithinAt
  have hmeas : AEStronglyMeasurable (fun u => Real.log (‖f u‖ * Real.exp (-φ u)) *
      locDens A Φ j u) (volume.restrict B) := by
    have h1 : AEStronglyMeasurable (fun u => ‖f u‖ * Real.exp (-φ u)) (volume.restrict B) :=
      (hfc.norm.mul (Real.continuous_exp.comp_continuousOn (hφc.mono hBV).neg)).aestronglyMeasurable
        hBm
    exact (Real.measurable_log.comp_aemeasurable h1.aemeasurable).aestronglyMeasurable.mul
      (hDc.aestronglyMeasurable hBm)
  have hint : IntegrableOn (fun u => Real.log (‖f u‖ * Real.exp (-φ u)) * locDens A Φ j u) B := by
    refine Integrable.mono' ((hlogf.norm.add hφi.norm).mul_const M) hmeas ?_
    refine ae_restrict_of_forall_mem hBm fun u hu => ?_
    rw [norm_mul]
    have hb := abs_log_mul_exp_le (-φ u) (norm_nonneg (f u))
    rw [abs_neg] at hb
    simp only [Real.norm_eq_abs] at hb ⊢
    exact mul_le_mul hb (hM u hu) (abs_nonneg _) (add_nonneg (abs_nonneg _) (abs_nonneg _))
  refine hint.congr_fun (fun u hu => ?_) hBm
  simp only
  rw [hF u (hBV hu)]

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

