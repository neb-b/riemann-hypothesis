module

public import Mathlib
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.Bundle0001
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0004
public import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.DiscreteSpectrumKFiniteDecomposition
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.HeightProofs.Bundle0015
public import Formalism.LocalToGlobal.Columns.Bundle0011
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.Columns.TiedValLatG
public import Formalism.LocalToGlobal.Columns.Bundle0022
public import Formalism.LocalToGlobal.Columns.CoefficientsModP.FkMapInitMinor
public import Formalism.LocalToGlobal.Columns.Bundle0024
public import Formalism.LocalToGlobal.Columns.Bundle0012
public import Formalism.LocalRingCardinality.Bundle0005
public import Formalism.QuotientMetricDivisors.ReductionLemmaZero
public import Formalism.QuotientMetricDivisors.FinalW
public import Formalism.LocalToGlobal.Divisibility.FramesLemmas
public import Formalism.LocalRingCardinality.DataArith
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0142

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HighestWeightLineOfKTypeMultiplicityOne
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.RealPar.HwLine

open GlobalTheory.RealPar.HwGen (PosRoot mono drop drop_cons mono_weight mono_stable weight_of_mem_span cnt)

variable {p q n : ℕ}

def ht : Ix p q → ℝ := Sum.elim (fun i => -(i : ℝ)) (fun j => -(j : ℝ))

theorem ht_lt {a b : Ix p q} (h : posC a b) : ht b < ht a := by
  rcases a with i | i <;> rcases b with j | j <;> simp [posC] at h <;> simp [ht] <;> exact_mod_cast h

theorem ht_drop_cons (r : PosRoot p q) (l : List (PosRoot p q)) :
    ∑ x, ht x * drop l x < ∑ x, ht x * drop (r :: l) x := by
  have hr := ht_lt r.2
  simp only [drop_cons, mul_add, Finset.sum_add_distrib, mul_sub, mul_ite, mul_one, mul_zero,
    Finset.sum_sub_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  linarith

theorem ht_drop_nonneg (l : List (PosRoot p q)) : 0 ≤ ∑ x, ht x * drop l x := by
  induction l with
  | nil => simp [drop, cnt]
  | cons r l ih => exact (lt_of_le_of_lt ih (ht_drop_cons r l)).le

theorem eq_smul_of_mem_span {V : Type*} [AddCommGroup V] [Module ℂ V] {act : Mat p q →ₗ[ℂ] Module.End ℂ V}
    (h : IsLieAct act) {μ : Ix p q → ℚ} {v : V} (hv : ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) {w : V}
    (hw : w ∈ Submodule.span ℂ (Set.range (mono act v))) (hwt : ∀ a, act (Eab a a) w = ((μ a : ℚ) : ℂ) • w) :
    ∃ c : ℂ, c • v = w := by
  classical
  let m' : {l : List (PosRoot p q) // l ≠ []} → V := fun l => mono act v l.1
  have hle : Submodule.span ℂ (Set.range (mono act v)) ≤
      Submodule.span ℂ {v} ⊔ Submodule.span ℂ (Set.range m') := by
    rw [Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    cases l with
    | nil => exact Submodule.mem_sup_left (Submodule.mem_span_singleton_self v)
    | cons r l =>
      exact Submodule.mem_sup_right (Submodule.subset_span ⟨⟨r :: l, List.cons_ne_nil r l⟩, rfl⟩)
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 (hle hw)
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy
  refine ⟨c, ?_⟩
  by_contra hne
  have hz0 : z ≠ 0 := fun h0 => hne (by rw [h0, add_zero])
  have hzw : ∀ a, act (Eab a a) z = ((μ a : ℚ) : ℂ) • z := by
    intro a
    have h1 := hwt a
    rw [map_add (f := _), map_smul, hv a, smul_add, smul_comm c] at h1
    exact add_left_cancel h1
  obtain ⟨⟨l, hl0⟩, hl⟩ := weight_of_mem_span (fun a => act (Eab a a)) m'
    (fun l a => ((((μ a : ℚ) : ℝ) - drop l.1 a : ℝ) : ℂ)) (fun l a => mono_weight h hv l.1 a)
    (fun a => ((μ a : ℚ) : ℂ)) z hz hz0 hzw
  have hd : ∀ a, drop l a = 0 := by
    intro a
    have h1 : ((((μ a : ℚ) : ℝ) - drop l a : ℝ) : ℂ) = (((μ a : ℚ) : ℝ) : ℂ) := by
      rw [Complex.ofReal_ratCast]; exact congrFun hl a
    have h2 := Complex.ofReal_injective h1
    linarith
  obtain ⟨r, l', rfl⟩ := List.exists_cons_of_ne_nil hl0
  have h3 := ht_drop_cons r l'
  have h4 := ht_drop_nonneg l'
  simp only [hd, mul_zero, Finset.sum_const_zero] at h3
  linarith

variable {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} {T : GrpData p q} (R : DSRep T)
  {σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)}

theorem isKTypeOf_span (h : BlockOrd e ε) (hσ : Factors R.U e σ) (μ : Ix p q → ℚ) {v : R.HK.V}
    (hv : Formalism.BasicNotions.TH.IsHW R.HK.act μ v) :
    IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) ((Submodule.span ℂ (Set.range (mono R.HK.act v))).map R.ι) := by
  classical
  set W := Submodule.span ℂ (Set.range (mono R.HK.act v)) with hWdef
  have hlie : IsLieAct R.HK.act := R.HK.lie
  have hv0 : v ≠ 0 := hv.1
  obtain ⟨hvw, hvr⟩ := (mem_hwSub R.HK.act μ v).1 hv.2
  have hvW : v ∈ W := Submodule.subset_span ⟨[], rfl⟩
  have hWst : KStable R.HK.act W := mono_stable hlie hvw hvr
  have hWle : ∀ W' : Submodule ℂ R.HK.V, v ∈ W' → KStable R.HK.act W' → W ≤ W' := by
    intro W' hvW' hW'
    rw [hWdef, Submodule.span_le]
    rintro _ ⟨l, rfl⟩
    induction l with
    | nil => exact hvW'
    | cons r l ih => exact hW' _ (HwGen.isKC_Eab r.2) _ ih
  obtain ⟨W0, hW0f, hvW0, hW0s⟩ := R.HK.kfin v
  have := hW0f
  have hWf : FiniteDimensional ℂ W := Submodule.finiteDimensional_of_le (hWle W0 hvW0 hW0s)
  have hι : Function.Injective R.ι := R.ι_inj
  have hKs : IsKStableOn ε σ (W.map R.ι) := isKStableOn_of_kStable p q n e ε T R σ h hσ W hWf hWst
  refine ⟨inferInstance, hKs, ?_, ?_, ?_⟩
  · intro S' hS'le hS'
    have hS'f : FiniteDimensional ℂ S' := Submodule.finiteDimensional_of_le hS'le
    have : CompleteSpace S' := FiniteDimensional.complete ℂ S'
    have hCK : IsKStableOn ε σ (S'ᗮ ⊓ W.map R.ι) := fun g hg x hx =>
      Submodule.mem_inf.2 ⟨kstable_orthogonal R h hσ hS' g hg x (Submodule.mem_inf.1 hx).1,
        hKs g hg x (Submodule.mem_inf.1 hx).2⟩
    have hCf : FiniteDimensional ℂ ↥(S'ᗮ ⊓ W.map R.ι) := Submodule.finiteDimensional_of_le inf_le_right
    obtain ⟨-, hS0map, hS0st⟩ := comap_kstable R h hσ hS'f hS'
    obtain ⟨-, -, hC0st⟩ := comap_kstable R h hσ hCf hCK
    have hdisj : ∀ x, x ∈ S'.comap R.ι → x ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι → x = 0 := by
      intro x hx1 hx2
      apply hι
      rw [map_zero]
      have hbot := Submodule.inf_orthogonal_eq_bot S'
      rw [Submodule.eq_bot_iff] at hbot
      exact hbot _ (Submodule.mem_inf.2 ⟨hx1, (Submodule.mem_inf.1 hx2).1⟩)
    have hsup : S' ⊔ S'ᗮ ⊓ W.map R.ι = W.map R.ι :=
      Submodule.sup_orthogonal_inf_of_hasOrthogonalProjection hS'le
    have hιv : R.ι v ∈ S' ⊔ S'ᗮ ⊓ W.map R.ι := hsup.symm ▸ Submodule.mem_map_of_mem hvW
    obtain ⟨s', hs', c', hc', hsc⟩ := Submodule.mem_sup.1 hιv
    obtain ⟨s, hsW, rfl⟩ := Submodule.mem_map.1 (hS'le hs')
    obtain ⟨t, -, rfl⟩ := Submodule.mem_map.1 (Submodule.mem_inf.1 hc').2
    have hs : s ∈ S'.comap R.ι := Submodule.mem_comap.2 hs'
    have ht : t ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι := Submodule.mem_comap.2 hc'
    have hvst : v = s + t := hι (by rw [map_add (f := _)]; exact hsc.symm)
    have hsw : ∀ a, R.HK.act (Eab a a) s = ((μ a : ℚ) : ℂ) • s := by
      intro a
      have hK : IsKC (Eab a a) := isKC_Eab ((h.sameBlock_iff a a).2 rfl)
      have e1 := hvw a
      rw [hvst, map_add (f := _), smul_add] at e1
      have hm1 : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s ∈ S'.comap R.ι :=
        Submodule.sub_mem _ (hS0st _ hK _ hs) (Submodule.smul_mem _ _ hs)
      have hm2 : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s ∈ (S'ᗮ ⊓ W.map R.ι).comap R.ι := by
        have he : R.HK.act (Eab a a) s - ((μ a : ℚ) : ℂ) • s =
            ((μ a : ℚ) : ℂ) • t - R.HK.act (Eab a a) t := by
          rw [sub_eq_sub_iff_add_eq_add, e1]; abel
        rw [he]
        exact Submodule.sub_mem _ (Submodule.smul_mem _ _ ht) (hC0st _ hK _ ht)
      exact sub_eq_zero.1 (hdisj _ hm1 hm2)
    obtain ⟨c, hc⟩ := eq_smul_of_mem_span hlie hvw hsW hsw
    by_cases hc0 : c = 0
    · left
      have htv : t = v := by rw [hvst, ← hc, hc0, zero_smul, zero_add]
      have hWC : W ≤ (S'ᗮ ⊓ W.map R.ι).comap R.ι := hWle _ (htv ▸ ht) hC0st
      have hS0bot : S'.comap R.ι = ⊥ := by
        rw [Submodule.eq_bot_iff]
        intro x hx
        obtain ⟨y, hyW, hyx⟩ := Submodule.mem_map.1 (hS'le (Submodule.mem_comap.1 hx))
        obtain rfl : y = x := hι hyx
        exact hdisj y hx (hWC hyW)
      rw [← hS0map, hS0bot, Submodule.map_bot]
    · right
      have hvS0 : v ∈ S'.comap R.ι := by
        have hv' : v = c⁻¹ • s := by rw [← hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
        rw [hv']
        exact Submodule.smul_mem _ _ hs
      have hWS : W ≤ S'.comap R.ι := hWle _ hvS0 hS0st
      refine le_antisymm hS'le ?_
      calc W.map R.ι ≤ (S'.comap R.ι).map R.ι := Submodule.map_mono hWS
        _ = S' := hS0map
  · refine ⟨R.ι v, Submodule.mem_map_of_mem hvW, fun h0 => hv0 (hι (by rw [h0, map_zero])), ?_⟩
    refine (TorusWt.isWtOn_iff p q n e ε T R σ h hσ _ v).2 fun a => ?_
    simp only [hvw a, Equiv.symm_apply_apply, Complex.ofReal_ratCast]
  · intro ν x hx hx0 hxw
    obtain ⟨w, hwW, rfl⟩ := Submodule.mem_map.1 hx
    have hw0 : w ≠ 0 := fun h0 => hx0 (by rw [h0, map_zero])
    have hww := (TorusWt.isWtOn_iff p q n e ε T R σ h hσ ν w).1 hxw
    obtain ⟨l, hl⟩ := weight_of_mem_span (fun a => R.HK.act (Eab a a)) (mono R.HK.act v)
      (fun l a => ((((μ a : ℚ) : ℝ) - drop l a : ℝ) : ℂ)) (fun l a => mono_weight hlie hvw l a)
      (fun a => ((ν (e a) : ℝ) : ℂ)) w hwW hw0 hww
    have hl' : ∀ a, ((μ a : ℚ) : ℝ) - drop l a = ν (e a) :=
      fun a => Complex.ofReal_injective (congrFun hl a)
    have key : ∀ x, ∑ i, ∑ j, (cnt l (e.symm i) (e.symm j) : ℝ) * Formalism.REAL.root i j (e x) = drop l x := by
      intro x
      rw [← Equiv.sum_comp e]
      refine (Finset.sum_congr rfl fun a _ => (Equiv.sum_comp e _).symm).trans ?_
      simp only [Equiv.symm_apply_apply, root_apply e, drop]
    refine ⟨fun i j => cnt l (e.symm i) (e.symm j), fun i j hij => ?_, ?_⟩
    · have := (h.posC_iff _ _).1 (HwGen.posC_of_cnt l _ _ hij)
      simpa using this
    · funext k
      obtain ⟨x, rfl⟩ := e.surjective k
      simp only [Pi.sub_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Equiv.symm_apply_apply]
      linarith [key x, hl' x]

theorem finrank_hwSub_eq_one : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ μ : Ix p q → ℚ, (∃ S, IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S) → (∀ S S', IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S → IsKTypeOf ε σ (fun i => (μ (e.symm i) : ℝ)) S' → S = S') → Module.finrank ℂ ↥(hwSub R.HK.act μ) = 1 := by
  intro p q n e ε T R σ h hσ μ hex huniq
  classical
  obtain ⟨S, hS⟩ := hex
  obtain ⟨v, hv⟩ := isHW_of_isKTypeOf R h hσ μ hS
  have hlie : IsLieAct R.HK.act := R.HK.lie
  obtain ⟨hvw, -⟩ := (mem_hwSub R.HK.act μ v).1 hv.2
  rw [finrank_eq_one_iff_of_nonzero' (⟨v, hv.2⟩ : hwSub R.HK.act μ)
    (fun h0 => hv.1 (congrArg Subtype.val h0))]
  rintro ⟨w, hw⟩
  by_cases hw0 : w = 0
  · exact ⟨0, Subtype.ext (by simp [hw0])⟩
  have hwHW : Formalism.BasicNotions.TH.IsHW R.HK.act μ w := ⟨hw0, hw⟩
  obtain ⟨hww, -⟩ := (mem_hwSub R.HK.act μ w).1 hw
  have hEq := huniq _ _ (isKTypeOf_span R h hσ μ hv) (isKTypeOf_span R h hσ μ hwHW)
  have hιw : R.ι w ∈ (Submodule.span ℂ (Set.range (mono R.HK.act v))).map R.ι := by
    rw [hEq]; exact Submodule.mem_map_of_mem (Submodule.subset_span ⟨[], rfl⟩)
  obtain ⟨y, hy, hyw⟩ := Submodule.mem_map.1 hιw
  obtain rfl : y = w := R.ι_inj hyw
  obtain ⟨c, hc⟩ := eq_smul_of_mem_span hlie hvw hy hww
  exact ⟨c, Subtype.ext hc⟩

end GlobalTheory.RealPar.HwLine
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InConeOfKTypesAbove
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverCone

theorem inCone_of_kTypesAbove : GlobalTheory.Dec.KTypesAbove → ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → ∀ (μ : Ix p q → ℚ) v, IsHW R.HK.act μ v → InCone (blockPar P e) μ := by
  intro KTA p q n e P T R σ hb hσ hds μ v hv
  obtain ⟨S, hS⟩ := GlobalTheory.RealPar.isKTypeOf_of_isHW R hb hσ μ ⟨v, hv⟩
  obtain ⟨c, hc, hμ⟩ := KTA n P.sgn P.lam R.U.H σ P.hc hds _ S hS
  refine ⟨fun a b => c (e a) (e b), fun a b hab => ?_, ?_⟩
  · have h2 := P.hc.1 (hc _ _ hab)
    rw [← GlobalTheory.RealPar.ratEntry_cast, ← GlobalTheory.RealPar.ratEntry_cast] at h2
    exact_mod_cast h2
  · funext x
    apply Rat.cast_injective (α := ℝ)
    have hx := congrFun hμ (e x)
    simp only [Equiv.symm_apply_apply] at hx
    push_cast
    rw [hx, GlobalTheory.RealPar.blattner_eq P hb (lam := GlobalTheory.RealPar.blockPar P e) (fun a => GlobalTheory.RealPar.ratEntry_cast P (e a)) x]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.add_apply]
    congr 1
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← e.sum_comp]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [GlobalTheory.RealPar.root_apply]
    split_ifs <;> simp

end GlobalTheory.CoverCone
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MatrixUnitDerivativeDiscreteSeriesMatrixCoeff
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

noncomputable section

namespace GlobalTheory.CoeffEab

variable {p q n : ℕ}

open scoped Matrix.Norms.Operator in
theorem reindex_exp (e : Ix p q ≃ Fin n) (A : Mat p q) :
    Matrix.reindex e e (NormedSpace.exp A) = NormedSpace.exp (Matrix.reindex e e A) := by
  exact NormedSpace.map_exp (Matrix.reindexAlgEquiv ℂ ℂ e) (continuous_id.matrix_reindex e e) A

theorem mem_upq_iff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} (h : BlockOrd e ε) (Y : Mat p q) :
    Y ∈ upq p q ↔ Formalism.REAL.inG ε (Matrix.reindex e e Y) := by
  unfold Formalism.REAL.inG
  rw [← h.reindex_Jm, Matrix.conjTranspose_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  have := (Matrix.reindex e e).injective.eq_iff (a := Yᴴ * Jm p q + Jm p q * Y) (b := 0)
  exact this.symm

theorem Jm_herm (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)ᴴ = Formalism.REAL.Jm ε := by
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a <;> simp [h]

theorem inG_of_J {ε : Fin n → Bool} {X : Matrix (Fin n) (Fin n) ℂ}
    (h : Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε = -X) : Formalism.REAL.inG ε X := by
  unfold Formalism.REAL.inG
  have : Xᴴ * Formalism.REAL.Jm ε = -(Formalism.REAL.Jm ε * X) := by
    calc Xᴴ * Formalism.REAL.Jm ε = Formalism.REAL.Jm ε * (Formalism.REAL.Jm ε * Xᴴ * Formalism.REAL.Jm ε) := by
          rw [← mul_assoc, ← mul_assoc, Formalism.REAL.Jm_mul_self, one_mul]
      _ = -(Formalism.REAL.Jm ε * X) := by rw [h, mul_neg]
  rw [this, neg_add_cancel]

theorem inG_cpart1 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (Formalism.REAL.cpart1 ε Z) := by
  apply inG_of_J
  unfold Formalism.REAL.cpart1
  rw [conjTranspose_smul, conjTranspose_sub, conjTranspose_mul, conjTranspose_mul, Jm_herm,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_sub, sub_mul, mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]
  have : star (1 / 2 : ℂ) = 1 / 2 := by simp
  rw [this, ← smul_neg, neg_sub]

theorem inG_cpart2 (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.inG ε (Formalism.REAL.cpart2 ε Z) := by
  apply inG_of_J
  unfold Formalism.REAL.cpart2
  rw [conjTranspose_smul, conjTranspose_add, conjTranspose_mul, conjTranspose_mul, Jm_herm,
    conjTranspose_conjTranspose]
  simp only [Matrix.mul_smul, Matrix.smul_mul, mul_add, add_mul, mul_assoc]
  rw [← mul_assoc (Formalism.REAL.Jm ε) (Formalism.REAL.Jm ε), Formalism.REAL.Jm_mul_self, one_mul, mul_one]
  have : star (1 / (2 * Complex.I)) = -(1 / (2 * Complex.I)) := by
    rw [show star (1 / (2 * Complex.I)) = (starRingEnd ℂ) (1 / (2 * Complex.I)) from rfl]
    simp only [map_div₀, map_one, map_mul, Complex.conj_I, map_ofNat]
    rw [mul_neg, div_neg]
  rw [this, neg_smul, add_comm]

theorem cpart_sum (ε : Fin n → Bool) (Z : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.cpart1 ε Z + Complex.I • Formalism.REAL.cpart2 ε Z = Z := by
  unfold Formalism.REAL.cpart1 Formalism.REAL.cpart2
  rw [smul_smul, show Complex.I * (1 / (2 * Complex.I)) = 1 / 2 by field_simp]
  module

theorem Rd_coeff {e : Ix p q ≃ Fin n} {ε : Fin n → Bool} {T : GrpData p q} (R : DSRep T)
    {σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)} (h : BlockOrd e ε) (hF : Factors R.U e σ)
    {X : Matrix (Fin n) (Fin n) ℂ} (hX : Formalism.REAL.inG ε X) (v : R.HK.V) (w : R.U.H)
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ UJset ε) :
    Formalism.REAL.Rd X (fun x => inner ℂ w (σ x (R.ι v))) g =
      inner ℂ w (σ g (R.ι (R.HK.act ((Matrix.reindex e e).symm X) v))) := by
  obtain ⟨Y, rfl⟩ := (Matrix.reindex e e).surjective X
  rw [Equiv.symm_apply_apply]
  have hY : Y ∈ upq p q := (mem_upq_iff h Y).2 hX
  obtain ⟨x, rfl⟩ := h.cov_surj T hg
  have hs : ∀ t : ℝ, t • Y ∈ upq p q := by
    intro t
    have h0 : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
    show (t • Y)ᴴ * Jm p q + Jm p q * (t • Y) = 0
    rw [conjTranspose_smul, star_trivial, Matrix.smul_mul, Matrix.mul_smul, ← smul_add, h0, smul_zero]
  have key : ∀ t : ℝ, σ (Matrix.reindex e e ((T.cov x : GL (Ix p q) ℂ) : Mat p q) *
      NormedSpace.exp ((t : ℂ) • Matrix.reindex e e Y)) = R.U.π x * R.U.π (T.expt (t • Y)) := by
    intro t
    rw [← map_mul, hF (x * _), map_mul, Units.val_mul, T.expt_cov _ (hs t)]
    congr 1
    have : (t : ℂ) • Matrix.reindex e e Y = Matrix.reindex e e (t • Y) := by
      ext i j; simp
    rw [this, ← reindex_exp]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  unfold Formalism.REAL.Rd
  simp only [key, ← hF x]
  have hd := R.der Y hY v
  have hl := (((innerSL ℂ w).comp (R.U.π x)).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hd
  exact hl.deriv

theorem eab_coeff : ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (ε : Fin n → Bool) (T : GrpData p q) (R : DSRep T) (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)), BlockOrd e ε → Factors R.U e σ → ∀ (a b : Ix p q) (v : R.HK.V) (w : R.U.H), ∀ g ∈ UJset ε, Formalism.REAL.Eab ε (e a) (e b) (fun x => inner ℂ w (σ x (R.ι v))) g = inner ℂ w (σ g (R.ι (R.HK.act (Eab a b) v))) := by
  intro p q n e ε T R σ h hF a b v w g hg
  unfold Formalism.REAL.Eab Formalism.REAL.Ec
  rw [Rd_coeff R h hF (inG_cpart1 ε _) v w hg, Rd_coeff R h hF (inG_cpart2 ε _) v w hg]
  have hE : Eab a b = (Matrix.reindex e e).symm (Formalism.REAL.cpart1 ε (Matrix.single (e a) (e b) 1)) +
      Complex.I • (Matrix.reindex e e).symm (Formalism.REAL.cpart2 ε (Matrix.single (e a) (e b) 1)) := by
    ext i j
    have := congrFun (congrFun (cpart_sum ε (Matrix.single (e a) (e b) (1 : ℂ))) (e i)) (e j)
    simp only [Matrix.add_apply, Matrix.smul_apply] at this
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.reindex_symm, Matrix.reindex_apply,
      Matrix.submatrix_apply, Equiv.symm_symm]
    rw [this]
    simp [Eab, Matrix.single_apply]
  rw [hE]
  simp only [map_add (f := _), map_smul, LinearMap.add_apply, LinearMap.smul_apply, inner_add_right, inner_smul_right]

end GlobalTheory.CoeffEab

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PairVrGramPRatPosDef
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.CoefGram

theorem posDef_of_hasSignature {n : ℕ} (G : Matrix (Fin n) (Fin n) ℂ) (h : Formalism.UG.HasSignature G n 0) : G.PosDef := by
  obtain ⟨e, P, hP⟩ := h
  have hJ : Formalism.UG.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [Formalism.UG.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  have hcT : Formalism.UG.cT (starRingEnd ℂ) P.val = P.valᴴ := by
    ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
  rw [hcT, hJ] at hP
  have h1 : (P.valᴴ * G.reindex e e * P.val).PosDef := by rw [hP]; exact Matrix.PosDef.one
  have h2 : (G.reindex e e).PosDef := (Matrix.IsUnit.posDef_star_left_conjugate_iff P.isUnit).1 h1
  have h3 : G = (G.reindex e e).submatrix e e := by ext i j; simp
  rw [h3]
  exact h2.submatrix e.injective

end GlobalTheory.Core.CoefGram
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.PtFieldMain
section
open Module NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Forms
open scoped Matrix ComplexOrder

namespace GlobalTheory

theorem ptField_main : ∀ D : D7, IsTotallyComplex D.what₂.LL ∧ (∃ v0 : InfinitePlace D.what₂.LL, Formalism.DivisionValues.IsConjAt v0) ∧ ∀ (u : D.what₂.Word) (c : (D.fm u).clsP), Nat.card ((D.fm u).stabilizer₂ c) ∣ (D.mem u).C.DGam := by
  intro D
  refine ⟨D.tcLL, GlobalTheory.isConjAt_exists_main D.what₂.LL ⟨D.what₂.embLL, D.starLL_cx⟩, ?_⟩
  intro u c
  exact (Subgroup.card_dvd_of_injective _ ((D.fm u).stabMap_inj c)).trans
    ((D.mem u).C.dvd_DGam _ le_rfl _)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEq
section
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.GelfandTwo

theorem sum_rhoStd_sq (n : ℕ) :
    ∑ a : Fin n, (Formalism.QuantumDeterminants.rhoStd n a : ℂ) * (Formalism.QuantumDeterminants.rhoStd n a : ℂ) = ((Formalism.BasicNotions.TH.rhoSq n : ℚ) : ℂ) := by
  simp only [Formalism.QuantumDeterminants.rhoStd, Formalism.BasicNotions.TH.rhoSq]
  push_cast
  rw [Fin.sum_univ_eq_sum_range (fun i => (((n : ℂ) - 1) / 2 - (i : ℂ)) * (((n : ℂ) - 1) / 2 - (i : ℂ))) n]
  exact Finset.sum_congr rfl fun i _ => (sq _).symm

theorem gelfVal_two (n : ℕ) (lam : Fin n → ℂ) :
    GlobalTheory.Dec.gelfVal lam 2 = ∑ a, lam a ^ 2 - ((Formalism.BasicNotions.TH.rhoSq n : ℚ) : ℂ) := by
  rw [GlobalTheory.CasimirEigen.gelfVal_two_eq, sum_rhoStd_sq]
  simp only [sq]

end GlobalTheory.GelfandTwo
end

