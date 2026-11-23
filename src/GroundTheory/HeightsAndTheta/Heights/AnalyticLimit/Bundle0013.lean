module

public import Mathlib
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.RegularizedMaxC2ExampleRealLine
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0002
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Assembly
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0003
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0008
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.IsOpenKappaOpenNeighbourhood
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0010
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0001
public import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInt
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Pullback
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0005
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.SystemIndependence
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.UniformIntegrability
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0016
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0009
public import GroundTheory.HeightsAndTheta.Heights.Regularisation.Bundle0007
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0018
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0011
public import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Bundle0012

@[expose] public section

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Assembly
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open GroundTheory.Heights₂.Heights.LowerBoundFree

theorem BoundingKaehler.full : BoundingKaehler.Statement := BoundingKaehler.proof

theorem GreenMassZero.full : GreenMassZero.Statement := GreenMassZero.proof

theorem UniformIntegrability.of_greenMass (h₁ : GreenMassStep.Statement)
    (h₂ : GreenMassReplace.Statement) (h₃ : GreenMassError.Statement) :
    UniformIntegrability.Statement :=
  UniformIntegrability.proof GreenMassZero.full h₁ h₂ h₃

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PGreenMassStep
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open MeasureTheory
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh MIntegrable mInt logNormSec
  isPotential_ofFun mIntSymm mIntAdd mIntRsmul mIntLinear mIntNonneg mIntegrableCont
  logNormIntegrable poincareLelong byPartsSymm isPotentialRsmul)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (ell)

noncomputable section

theorem GreenMassStep.proof : GreenMassStep.Statement := by
  intro D W _ _ _ S a ha ε t hε ht hℓ
  set a' : Fin (D + 1) := ⟨a, ha⟩ with ha'
  have hform := S.form a' t ht hℓ
  have hu : S.A.Smooth (S.u a' t) := hform.2
  have hΦ : ∀ i, IsPotential S.A (S.rest a t i) := S.rest_isPotential ht hℓ a
  have hth : IsPotential S.A (S.th a') := hform.1.th_pot
  have huP : IsPotential S.A (LocPot.ofFun (S.u a' t)) := isPotential_ofFun S.A _ hu
  have hf : S.A.Smooth fun x => Real.log (secNorm S.L S.s x ^ 2 + ε) :=
    smooth_log_secNorm_sq_add S.L_pot S.s_sec hε
  have hDd : IsPotential S.A (formDiff S.Om.pot (S.th a')) := isPotential_formDiff S.Om.isPot hth
  have hcons := fun (P : LocPot W) (hP : IsPotential S.A P) =>
    forall_cons_of (p := IsPotential S.A) (Φ := S.rest a t) hP hΦ
  have hGi := fun (P : LocPot W) (hP : IsPotential S.A P) =>
    mIntegrable_greenSplit S.L_pot S.s_sec S.s_snc hε _ (hcons P hP)
  have hG := fun Ψ => mInt_greenEp_eq_split (A := S.A) (Φ := Ψ) S.s_sec S.s_snc hε

  have hJ1 : S.J (a + 1) ε t =
      mInt S.A (Fin.cons (S.th a' + LocPot.ofFun (S.u a' t)) (S.rest a t)) (greenSplit S.L S.s ε) := by
    have h := mixedForms_cycle S.Om.pot (S.T t) a ha (a + 1) (Or.inr rfl)
    have h0 : mixedForms S.Om.pot (S.T t) (a + 1) a' = S.th a' + LocPot.ofFun (S.u a' t) := by
      simp [mixedForms, a', UIData.T, curForms, potForm]
    rw [h0] at h
    show mInt S.A (mixedForms S.Om.pot (S.T t) (a + 1)) (greenEp S.L S.s ε) = _
    rw [← mIntSymm S.A (mixedForms S.Om.pot (S.T t) (a + 1)) (Fin.cycleRange a').symm, h, hG]
    rfl
  have hJ0 : S.J a ε t = mInt S.A (Fin.cons S.Om.pot (S.rest a t)) (greenEp S.L S.s ε) := by
    have h := mixedForms_cycle S.Om.pot (S.T t) a ha a (Or.inl rfl)
    have h0 : mixedForms S.Om.pot (S.T t) a a' = S.Om.pot := by simp [mixedForms, a']
    rw [h0] at h
    show mInt S.A (mixedForms S.Om.pot (S.T t) a) (greenEp S.L S.s ε) = _
    rw [← mIntSymm S.A (mixedForms S.Om.pot (S.T t) a) (Fin.cycleRange a').symm, h]
    rfl

  have hOm : mInt S.A (Fin.cons S.Om.pot (S.rest a t)) (greenEp S.L S.s ε) =
      mInt S.A (Fin.cons (S.th a') (S.rest a t)) (greenSplit S.L S.s ε) +
        mInt S.A (Fin.cons (formDiff S.Om.pot (S.th a')) (S.rest a t)) (greenSplit S.L S.s ε) := by
    rw [hG, ReciprocityTheory.AnForm.M.PLC.mInt_congr_phi S.A _
      (Fin.cons (S.th a' + formDiff S.Om.pot (S.th a')) (S.rest a t)) ?_]
    · exact mIntAdd S.A _ _ _ hth hDd hΦ _ (hGi _ hth) (hGi _ hDd)
    · intro i x y
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [Fin.cons_zero]
        exact (add_formDiff_φ _ _ x y).symm
      · simp only [Fin.cons_succ]
  have hpos : 0 ≤ mInt S.A (Fin.cons (formDiff S.Om.pot (S.th a')) (S.rest a t))
      (greenSplit S.L S.s ε) := by
    rw [← hG]
    exact mIntNonneg S.A _ (hcons _ hDd)
      (forall_cons_of (p := IsPsh S.A) (isPsh_formDiff S.Om.isPot hth hform.1.th_le)
        (S.rest_isPsh ht hℓ a)) _ (greenEp_nonneg S.L S.s hε.le)

  have hU : mInt S.A (Fin.cons (LocPot.ofFun (S.u a' t)) (S.rest a t)) (greenSplit S.L S.s ε) =
      mInt S.A (Fin.cons (LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε)) (S.rest a t))
          (S.u a' t) + 2 * mInt S.A (Fin.cons S.L (S.rest a t)) (S.u a' t) -
        2 * S.divInt (S.rest a t) (S.u a' t) := by
    have hlin := mIntLinear S.A _ (hcons _ huP) (-2) (logNormSec S.L S.s)
      (fun x => Real.log (secNorm S.L S.s x ^ 2 + ε))
      (logNormIntegrable S.A S.L S.s S.mult S.comp S.L_pot S.s_sec S.s_snc _ (hcons _ huP))
      (mIntegrableCont S.A _ (hcons _ huP) _ (ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A hf))
    have hpl := poincareLelong S.A S.L S.s S.mult S.comp S.B S.L_pot S.s_sec S.s_snc S.B_holo
      (S.u a' t) hu (S.rest a t) hΦ
    have hbp := byPartsSymm S.A _ (S.u a' t) hf hu (S.rest a t) hΦ
    have hdiv : S.divInt (S.rest a t) (S.u a' t) = ∑ k, (S.mult k : ℝ) * mInt (S.B k)
        (fun i => (S.rest a t i).pullback Subtype.val continuous_subtype_val)
        (S.u a' t ∘ Subtype.val) := rfl
    show mInt S.A _ (fun x => (-2) * logNormSec S.L S.s x + Real.log (secNorm S.L S.s x ^ 2 + ε)) = _
    rw [hlin, hpl, hbp, hdiv]
    ring

  have hpl : S.plTerm a ha ε t =
      2 * mInt S.A (Fin.cons S.L (S.rest a t)) (S.u a' t) +
        mInt S.A (Fin.cons (LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε)) (S.rest a t))
          (S.u a' t) - 2 * S.divInt (S.rest a t) (S.u a' t) := by
    have hcu := ReciprocityTheory.AnForm.M.PLC.continuous_of_smooth S.A hu
    have hL2 : IsPotential S.A (S.L.rsmul 2) := isPotentialRsmul S.A 2 S.L S.L_pot
    have hfP := isPotential_ofFun S.A _ hf
    show mInt S.A (Fin.cons (S.L.rsmul 2 + LocPot.ofFun fun x => Real.log (secNorm S.L S.s x ^ 2 + ε))
      (S.rest a t)) (S.u a' t) - 2 * S.divInt (S.rest a t) (S.u a' t) = _
    rw [mIntAdd S.A _ _ _ hL2 hfP hΦ _ (mIntegrableCont S.A _ (hcons _ hL2) _ hcu)
      (mIntegrableCont S.A _ (hcons _ hfP) _ hcu), mIntRsmul S.A 2 S.L _ S.L_pot hΦ]
  rw [hJ1, hJ0, hOm, mIntAdd S.A _ _ _ hth huP hΦ _ (hGi _ hth) (hGi _ huP), hU, hpl]
  linarith

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.PLemmaETrunc
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.A (regMax tmax regMax_thm)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh isPotentialAdd isPotential_ofFun
  st_smooth_continuous)

theorem LemmaETrunc.proof : LemmaETrunc.Statement := by
  intro D X _ A Om Yo r C₁ u hYo hd hr hC hu hnn hu0 hlow hcase R hR
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = -(C₁ * Real.log R + 2) + 1 := ⟨_, rfl⟩
  have hlogR : 1 ≤ Real.log R := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hR
  have hCR : 0 ≤ C₁ * Real.log R := mul_nonneg hC (by linarith)
  obtain ⟨-, -, -, hbd, hfix, -⟩ := (regMax_thm (Fin 2)).1 1 one_pos

  have hb : ∀ a : ℝ, a ≤ 0 →
      -(C₁ * Real.log R + 2) ≤ regMax 1 ![a, c] - 1 ∧ regMax 1 ![a, c] - 1 ≤ 0 := by
    intro a ha
    obtain ⟨h1, h2⟩ := hbd ![a, c]
    have hc1 : (![a, c] : Fin 2 → ℝ) 1 ≤ tmax ![a, c] := by
      unfold tmax
      exact Finset.le_sup' _ (Finset.mem_univ _)
    have hc2 : tmax ![a, c] ≤ 0 := by
      unfold tmax
      refine Finset.sup'_le _ _ fun i _ => ?_
      fin_cases i
      · simpa using ha
      · simp only [Fin.mk_one, Matrix.cons_val_one, Matrix.cons_val_zero]
        linarith
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at hc1
    constructor <;> linarith

  have hfixU : ∀ a : ℝ, c + 1 ≤ a → regMax 1 ![a, c] = a := fun a ha => by
    have := hfix ![a, c] 0 fun j hj => by
      fin_cases j
      · simp at hj
      · simpa using ha
    simpa using this
  have hfixC : ∀ a : ℝ, a + 1 ≤ c → regMax 1 ![a, c] = c := fun a ha => by
    have := hfix ![a, c] 1 fun j hj => by
      fin_cases j
      · simpa using ha
      · simp at hj
    simpa using this
  have hnear : ∀ x ∈ Yo, r x < R → c + 1 ≤ u x := by
    intro x hx hxR
    have h1 : Real.log (r x) ≤ Real.log R :=
      Real.log_le_log (lt_of_lt_of_le (Real.exp_pos 1) (hr x hx)) hxR.le
    have h2 := mul_le_mul_of_nonneg_left h1 hC
    have h3 := hlow x hx
    rw [hc]
    linarith
  rcases hcase with hsm | hpole
  ·
    have hle : ∀ x, u x ≤ 0 := by
      have hcl : closure Yo ⊆ {x | u x ≤ 0} :=
        closure_minimal hu0 (isClosed_le (st_smooth_continuous A hsm) continuous_const)
      intro x
      exact hcl (hd.closure_eq ▸ Set.mem_univ x)
    have hpot : IsPotential A (potForm Om.pot u) :=
      isPotentialAdd A _ _ Om.isPot (isPotential_ofFun A u hsm)
    have hint : interior Yoᶜ = ∅ := by
      rw [interior_compl, hd.closure_eq, Set.compl_univ]
    have hpsh := isPsh_of_formNonneg hint hpot hnn
    have hnnU : FormNonneg A Set.univ (potForm Om.pot u) := fun x k y hy w =>
      hpsh x k y ⟨hy.1, hy.2.2⟩ w
    obtain ⟨hs, hp⟩ := trunc_smooth_psh A Om isOpen_univ hsm hnnU c one_pos
      (fun p => regMax 1 ![u p, c] - 1) (fun _ _ => rfl) (fun p hp => absurd (Set.mem_univ p) hp)
    refine ⟨_, hs, hp, fun x => hb (u x) (hle x), -1, fun x hx hxR => ?_⟩
    show regMax 1 ![u x, c] - 1 = u x + -1
    rw [hfixU _ (hnear x hx hxR)]
    ring
  ·
    classical
    let v : X → ℝ := fun p => if p ∈ Yo then regMax 1 ![u p, c] - 1 else c - 1
    have hvC : ∀ p ∉ Yo, ∃ N : Set X, IsOpen N ∧ p ∈ N ∧ ∃ κ : ℝ, ∀ q ∈ N, v q = κ := by
      intro p hp
      have hev : ∀ᶠ q in 𝓝[Yo] p, u q ≤ c - 1 := tendsto_atBot.1 (hpole p hp) (c - 1)
      obtain ⟨N, hN, hpN, hNs⟩ := mem_nhdsWithin.1 hev
      refine ⟨N, hN, hpN, c - 1, fun q hq => ?_⟩
      by_cases hqY : q ∈ Yo
      · have hq' : u q ≤ c - 1 := hNs ⟨hq, hqY⟩
        simp only [v, if_pos hqY]
        rw [hfixC _ (by linarith)]
      · simp only [v, if_neg hqY]
    obtain ⟨hs, hp⟩ := trunc_smooth_psh A Om hYo hu hnn c one_pos v
      (fun p hp => by simp only [v, if_pos hp]) hvC
    refine ⟨v, hs, hp, fun x => ?_, -1, fun x hx hxR => ?_⟩
    · by_cases hx : x ∈ Yo
      · simp only [v, if_pos hx]
        exact hb _ (hu0 x hx)
      · simp only [v, if_neg hx]
        constructor <;> linarith
    · simp only [v, if_pos hx]
      rw [hfixU _ (hnear x hx hxR)]
      ring

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEEnergy
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt)

def LemmaEEnergy.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (v : Fin D → X → ℝ) (w : X → ℝ), (∀ i, A.Smooth (v i)) →
    (∀ i, IsPsh A (potForm Om.pot (v i))) → (∀ i x, -1 ≤ v i x ∧ v i x ≤ 0) → A.Smooth w →
    IsPsh A (potForm Om.pot w) →
    mInt A (fun i => potForm Om.pot (v i)) (fun x => -w x) ≤
      mInt A (fun _ => Om.pot) (fun x => -w x) + D * Om.vol

section Inhabitants

open ReciprocityTheory.AnForm.M (p1)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEScale
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt)

def LemmaEScale.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (M : ℝ) (v : Fin D → X → ℝ), 1 ≤ M → (∀ i, A.Smooth (v i)) →
    (∀ i, IsPsh A (potForm Om.pot (v i))) →
    (∀ i, IsPsh A (potForm Om.pot fun x => v i x / M)) ∧
    ∀ g : X → ℝ, Continuous g → (∀ x, 0 ≤ g x) →
      mInt A (fun i => potForm Om.pot (v i)) g ≤
        M ^ D * mInt A (fun i => potForm Om.pot fun x => v i x / M) g

section Inhabitants

open ReciprocityTheory.AnForm.M (p1)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncMass
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsPsh mInt MIntegrable)

def LemmaETruncMass.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (Yo : Set X) (r : X → ℝ) (u : Fin D → X → ℝ) (v : ℝ → Fin D → X → ℝ),
    IsOpen Yo → ContinuousOn r Yo → (∀ i, A.SmoothOn Yo (u i)) →
    (∀ i, FormNonneg A Yo (potForm Om.pot (u i))) →
    (∀ R : ℝ, Real.exp 1 ≤ R → ∀ i, A.Smooth (v R i) ∧ IsPsh A (potForm Om.pot (v R i)) ∧
      ∃ c : ℝ, ∀ x ∈ Yo, r x < R → v R i x = u i x + c) →
    ∀ R₀ : ℝ, Real.exp 1 ≤ R₀ →
      MIntegrable A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1) ∧
      mInt A (fun i => potForm Om.pot (u i)) ((tail Yo r R₀).indicator 1) ≤
        mInt A (fun i => potForm Om.pot (v R₀ i)) ({x | x ∉ Yo ∨ R₀ ≤ r x}.indicator 1)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaETruncTail
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh mInt)

def LemmaETruncTail.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    Dense (secOpen s) → (∀ y, ‖s y y‖ * Real.exp (-L.φ y y) ≤ 1) →
    ∃ K : ℝ, 0 ≤ K ∧ ∀ M : ℝ, 1 ≤ M → ∀ v : Fin D → X → ℝ, (∀ i, A.Smooth (v i)) →
      (∀ i, IsPsh A (potForm Om.pot (v i))) → (∀ i x, -M ≤ v i x ∧ v i x ≤ 0) →
      ∀ ρ : ℝ, Real.exp 1 ≤ ρ →
        mInt A (fun i => potForm Om.pot (v i))
            ({x | x ∉ secOpen s ∨ ρ ≤ rSec L s x}.indicator 1) ≤ M ^ D * K / ρ

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLemmaEWeight
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection IsPsh)

def LemmaEWeight.Statement : Prop :=
  ∀ {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (D : ℕ) (A : FinHolAtlas D X)
    (Om : KaehlerForm A) (L : LocPot X) (s : X → X → ℂ), IsPotential A L → IsSection A L s →
    ∃ c₀ : ℝ, 0 < c₀ ∧ ∀ l : ℝ, 1 ≤ l → ∃ w : X → ℝ, A.Smooth w ∧ IsPsh A (potForm Om.pot w) ∧
      (∀ x ∈ secOpen s, min (c₀ * rSec L s x) l ≤ -w x ∧ -w x ≤ c₀ * rSec L s x + 1) ∧
      (∀ x, x ∉ secOpen s → l ≤ -w x)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

-- bundled from GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.StLogNormSecIntegrable
section
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential IsSection MIntegrable logNormSec)

def LogNormSecIntegrable.Statement : Prop :=
  ∀ {D : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas D X) (L : LocPot X)
    (s : X → X → ℂ), IsPotential A L → IsSection A L s → Dense (secOpen s) →
    ∀ Φ : Fin D → LocPot X, (∀ i, IsPotential A (Φ i)) → MIntegrable A Φ (logNormSec L s)

section Inhabitants

open ReciprocityTheory.AnForm.M (p1 fsPot projectiveLinePairSection projLine_isSmoothPotential projLine_isHolomorphicSection)

end Inhabitants

end GroundTheory.Heights₂.Heights.AnalyticLimit
end

