module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0025
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0347
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.CosInj
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSingle
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0050
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.PoincareInHH
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHAlg
public import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0339
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0329
public import Development.AbelianVarietyTheory.Proofs.FlagMeasures.Bundle0080
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RestrictedBlockUnipotentSymmetric
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0342
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0335
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WordElementConjOrthProjHyperbolicNegativeSpanEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0336
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HzUnit
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualSplitComponentIsLatticeStabilizerEq
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0337

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ResiduePairStabilizerKeepsIntegralLastCoordDiv
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.SeeSaw GlobalTheory.LatPair GlobalTheory.SplitWeil
open GlobalTheory.Unf GlobalTheory.Grow GlobalTheory.FinPl ValuativeRel IsLocalRing
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.AdForm
open GlobalTheory.AdForm

namespace GlobalTheory.PairKeep

theorem res_zero_iff {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (c τ : k) (q : Unif k) (hτ : valuation k τ = valuation k ((q.1 : 𝒪[k]) : k)) (hc : valuation k c = 1)
    (x : k) (s : 𝒪[k]) (hs : (s : k) = c * x) :
    IsLocalRing.residue 𝒪[k] s = 0 ↔ ∃ t ∈ 𝒪[k], x = τ * t := by
  have hq := q.ne_zero
  have hvq : valuation k ((q.1 : 𝒪[k]) : k) ≠ 0 := by simpa using hq
  have hτ0 : τ ≠ 0 := by
    intro h; rw [h, map_zero] at hτ; exact hvq hτ.symm
  have hc0 : c ≠ 0 := by
    intro h; rw [h, map_zero] at hc; exact zero_ne_one hc
  rw [IsLocalRing.residue_eq_zero_iff, q.mem_max_iff]
  constructor
  · rintro ⟨t, ht⟩
    have h1 : ((q.1 : 𝒪[k]) : k) / (c * τ) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨_, mul_mem h1 t.2, ?_⟩
    have h2 : c * x = ((q.1 : 𝒪[k]) : k) * (t : k) := by rw [← hs, ht]; rfl
    field_simp
    linear_combination h2
  · rintro ⟨t, ht, rfl⟩
    have h1 : (c * τ) / ((q.1 : 𝒪[k]) : k) ∈ 𝒪[k] := by
      rw [Valuation.mem_integer_iff, map_div₀, map_mul, hc, hτ, one_mul, div_self hvq]
    refine ⟨⟨_, mul_mem h1 ht⟩, Subtype.ext ?_⟩
    rw [hs]
    change _ = ((q.1 : 𝒪[k]) : k) * (c * τ / ((q.1 : 𝒪[k]) : k) * t)
    field_simp

theorem keep : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (m' m : ℕ) (hm : m' = m) (b b' : Matrix (Fin m') (Fin m') k), b * b' = 1 → b' * b = 1 →
    ∀ P : Pair k (Fin m'), (∀ x, x ∈ P.lat ↔ ∀ r, (b *ᵥ x) r ∈ 𝒪[k]) →
    ∀ (c τ : k) (q : Unif k), valuation k τ = valuation k ((q.1 : 𝒪[k]) : k) → valuation k c = 1 →
    (∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) → ∀ r0 : Fin m', r0.1 + 1 = m' →
      ∃ s : 𝒪[k], (s : k) = c * u r0 ∧ P.HasVal (b' *ᵥ u) (IsLocalRing.residue 𝒪[k] s)) →
    ∀ g : GL (Fin m') k, g • P = P →
      (b * g.val * b').reindex (finCongr hm) (finCongr hm) * (b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm) = 1 ∧
      (∀ u : Fin m → k, ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], u r0 = τ * s) ↔
        ((∀ r, ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r ∈ 𝒪[k]) ∧
          ∀ r0 : Fin m, r0.1 + 1 = m → ∃ s ∈ 𝒪[k], ((b * g.val * b').reindex (finCongr hm) (finCongr hm) *ᵥ u) r0 = τ * s)) ∧
      (∀ u : Fin m → k, (∀ r, u r ∈ 𝒪[k]) ↔
        ∀ r, (((b * (g⁻¹).val * b').reindex (finCongr hm) (finCongr hm))ᵀ *ᵥ u) r ∈ 𝒪[k]) := by
  intro k _ _ _ _ m' m hm b b' hbb hb'b P hP c τ q hτ hc hval g hg
  subst hm
  simp only [finCongr_refl, Matrix.reindex_refl_refl]
  have hmul : ∀ g₁ g₂ : GL (Fin m') k, g₁ * g₂ = 1 → (b * g₁.val * b') * (b * g₂.val * b') = 1 := by
    intro g₁ g₂ h
    have h' : g₁.val * g₂.val = 1 := by rw [← Units.val_mul, h, Units.val_one]
    calc (b * g₁.val * b') * (b * g₂.val * b') = b * (g₁.val * (b' * b) * g₂.val) * b' := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [hb'b, Matrix.mul_one, h', Matrix.mul_one, hbb]
  have hb' : ∀ (g : GL (Fin m') k) (u : Fin m' → k), b' *ᵥ ((b * g.val * b') *ᵥ u) = g • (b' *ᵥ u) := by
    intro g u
    change _ = g.val *ᵥ (b' *ᵥ u)
    rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← Matrix.mul_assoc, hb'b, Matrix.one_mul]
  have hlat : ∀ u : Fin m' → k, b' *ᵥ u ∈ P.lat ↔ ∀ r, u r ∈ 𝒪[k] := by
    intro u
    rw [hP, Matrix.mulVec_mulVec, hbb, Matrix.one_mulVec]
  have hint : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu
    rw [← hlat, hb']
    have := ((P.hasVal_fn ⟨_, (hlat u).2 hu⟩).gl_smul g)
    rw [hg] at this
    exact this.mem
  have hlast : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k,
      ((∀ r, u r ∈ 𝒪[k]) ∧ ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], u r0 = τ * s) →
      ((∀ r, ((b * g.val * b') *ᵥ u) r ∈ 𝒪[k]) ∧
        ∀ r0 : Fin m', r0.1 + 1 = m' → ∃ s ∈ 𝒪[k], ((b * g.val * b') *ᵥ u) r0 = τ * s) := by
    intro g hg u ⟨hu, hu'⟩
    refine ⟨hint g hg u hu, fun r0 hr0 => ?_⟩
    obtain ⟨s, hs, hv⟩ := hval u hu r0 hr0
    obtain ⟨s', hs', hv'⟩ := hval _ (hint g hg u hu) r0 hr0
    have h1 := hv.gl_smul g
    rw [hg, ← hb'] at h1
    rw [← res_zero_iff c τ q hτ hc _ s' hs', hv'.unique h1, res_zero_iff c τ q hτ hc _ s hs]
    exact hu' r0 hr0
  have htr : ∀ g : GL (Fin m') k, g • P = P → ∀ u : Fin m' → k, (∀ r, u r ∈ 𝒪[k]) →
      ∀ r, ((b * g.val * b')ᵀ *ᵥ u) r ∈ 𝒪[k] := by
    intro g hg u hu r
    have h1 := hint g hg (Pi.single r 1) (fun j => by
      rw [Pi.single_apply]
      split_ifs
      exacts [one_mem _, zero_mem _])
    rw [Matrix.mulVec_single_one] at h1
    change ∑ j, (b * g.val * b')ᵀ r j * u j ∈ 𝒪[k]
    exact sum_mem fun j _ => mul_mem (h1 j) (hu j)
  have hg' : g⁻¹ • P = P := by rw [inv_smul_eq_iff, hg]
  refine ⟨hmul _ _ (mul_inv_cancel g), fun u => ⟨hlast g hg u, fun h => ?_⟩, fun u => ⟨htr _ hg' u, fun h => ?_⟩⟩
  · have := hlast _ hg' _ h
    rwa [Matrix.mulVec_mulVec, hmul _ _ (inv_mul_cancel g), Matrix.one_mulVec] at this
  · have := htr _ hg _ h
    rwa [Matrix.mulVec_mulVec, ← Matrix.transpose_mul, hmul _ _ (inv_mul_cancel g), Matrix.transpose_one,
      Matrix.one_mulVec] at this

end GlobalTheory.PairKeep
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.RootExchangeEntriesMemSchwartzBruhat
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.QPl ValuativeRel
open GlobalTheory.PosOne (toOne Covers TriPos SymDbl OneDbl comb)
open GlobalTheory.IndefiniteRowSideFullHecke.FourierJacobiAverage (app HasTensorVal fl opEFJ IsQuotIntFJ RFJ)
open GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum (IsCO)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.EntrySB
open scoped Pointwise

theorem exists_nhds_add_eq {M E : Type*} [TopologicalSpace M] [AddCommGroup M] [IsTopologicalAddGroup M] [Zero E]
    {F : M → E} (hl : IsLocallyConstant F) (hc : HasCompactSupport F) :
    ∃ V ∈ nhds (0 : M), ∀ x, ∀ v ∈ V, F (x + v) = F x := by
  letI : TopologicalSpace E := ⊥
  haveI : DiscreteTopology E := ⟨rfl⟩
  have hT : (F '' tsupport F).Finite := (hc.isCompact.image hl.continuous).finite_of_discrete
  have hsep : ∀ a : E, ∃ W ∈ nhds (0 : M), a ≠ 0 → F ⁻¹' {a} + W ⊆ F ⁻¹' {a} := by
    intro a
    by_cases ha : a = 0
    · exact ⟨Set.univ, Filter.univ_mem, fun h => (h ha).elim⟩
    · have hsub : F ⁻¹' {a} ⊆ tsupport F := fun y hy =>
        subset_tsupport F (by simp only [Set.mem_preimage, Set.mem_singleton_iff] at hy; simp [Function.mem_support, hy, ha])
      have hK : IsCompact (F ⁻¹' {a}) := hc.isCompact.of_isClosed_subset (hl.isClopen_fiber a).isClosed hsub
      obtain ⟨W, hW, hW'⟩ := compact_open_separated_add_right hK (hl.isOpen_fiber a) le_rfl
      exact ⟨W, hW, fun _ => hW'⟩
  choose W hW hWs using hsep
  refine ⟨⋂ a ∈ F '' tsupport F, (W a ∩ -W a), (Filter.biInter_mem hT).2 fun a _ =>
    Filter.inter_mem (hW a) (neg_mem_nhds_zero M (hW a)), ?_⟩
  intro x v hv
  simp only [Set.mem_iInter, Set.mem_inter_iff, Set.mem_neg] at hv
  by_cases hx : F x = 0
  · by_contra hne
    have hxv : x + v ∈ tsupport F := subset_tsupport F (by rw [Function.mem_support]; rwa [hx] at hne)
    have hb : F (x + v) ≠ 0 := fun h => hne (h.trans hx.symm)
    have := hWs (F (x + v)) hb (Set.add_mem_add (a := x + v) (b := -v) rfl (hv _ ⟨_, hxv, rfl⟩).2)
    simp only [add_neg_cancel_right, Set.mem_preimage, Set.mem_singleton_iff] at this
    exact hne this.symm
  · have hxs : x ∈ tsupport F := subset_tsupport F hx
    have := hWs (F x) hx (Set.add_mem_add (a := x) (b := v) rfl (hv _ ⟨_, hxs, rfl⟩).1)
    simpa using this

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Aff
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

theorem affPt_add (p : ℕ) (x₀ v : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    affPt p (x₀ + v) e = affPt p x₀ e + fromBlocks v 0 0 0 := by
  ext r s
  rcases r with r | r <;> rcases s with s | s <;> simp [affPt, basePt] <;> ring

theorem ch_add (x y : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) : ch (x + y) = ch x + ch y := by
  simp [ch, Finset.sum_add_distrib]

theorem ch_fromBlocks (v : Matrix n n' k) :
    ch (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) = 0 := by
  simp [ch]

theorem corner_affPt (p : ℕ) (x₀ : Matrix n n' k)
    (e : {rs : (n ⊕ Fin c) × (n' ⊕ Fin (c + 1)) // Free p rs} → k) :
    (Matrix.of fun i j => affPt p x₀ e (Sum.inl i) (Sum.inl j)) = x₀ := by
  ext i j
  simp [affPt, basePt, Free]

variable [MeasurableSpace k] [BorelSpace k]

theorem opE_mem_SB (ψ : AddChar k Circle) (ν : Measure k) (p : ℕ)
    {F : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ} (hF : F ∈ SB _) :
    GlobalTheory.RootEx.opE ψ ν p F ∈ SB (Matrix n n' k) := by
  obtain ⟨hl, hc⟩ := hF
  refine ⟨?_, ?_⟩
  · obtain ⟨V, hV, hVF⟩ := exists_nhds_add_eq hl hc
    have hι : Continuous fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k) :=
      continuous_id.matrix_fromBlocks continuous_const continuous_const continuous_const
    have hW : (fun v : Matrix n n' k =>
        (fromBlocks v 0 0 0 : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)) ⁻¹' V ∈ nhds (0 : Matrix n n' k) := by
      apply hι.continuousAt.preimage_mem_nhds
      simpa [fromBlocks_zero] using hV
    refine (IsLocallyConstant.iff_eventually_eq _).2 fun x₀ => ?_
    rw [← map_add_left_nhds_zero x₀, Filter.eventually_map]
    filter_upwards [hW] with v hv
    simp only [GlobalTheory.RootEx.opE]
    congr 1
    funext e
    rw [affPt_add, hVF _ _ hv, ch_add, ch_fromBlocks, add_zero]
  · have hpr : Continuous fun M : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k =>
        (Matrix.of fun i j => M (Sum.inl i) (Sum.inl j) : Matrix n n' k) :=
      continuous_matrix fun i j => continuous_id.matrix_elem _ _
    refine HasCompactSupport.intro (hc.isCompact.image hpr) fun x₀ hx₀ => ?_
    have h0 : ∀ e, F (affPt p x₀ e) = 0 := fun e => image_eq_zero_of_notMem_tsupport fun hm =>
      hx₀ ⟨_, hm, corner_affPt p x₀ e⟩
    simp [GlobalTheory.RootEx.opE, h0]

end Aff

end GlobalTheory.EntrySB


open GlobalTheory.EntrySB in
theorem GlobalTheory.StepData.xi_mem_SB : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k]
    (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (ψ : AddChar k Circle), Continuous ψ →
  ∀ (ν : Measure k), ν.IsAddHaarMeasure → ∀ (μ : kˣ →* ℂˣ) (Φ : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k))
    (J : Subgroup (GL (n ⊕ Fin c) k)) (b : GL (n ⊕ Fin c) k) (h' : GL (n' ⊕ Fin (c + 1)) k) (h : GL (n ⊕ Fin c) k),
    xi ψ ν μ Φ.1 J b h' h ∈ SB (Matrix n n' k) := by
  intro k _ _ _ _ _ _ n n' _ _ _ _ c ψ _ ν _ μ Φ J b h' h
  have := Submodule.smul_mem (SB (Matrix n n' k)) ((((volNat ν b (Cgrp J h))⁻¹ : ℝ) : ℂ))
    (opE_mem_SB ψ ν 1 (GlobalTheory.SplitWeil.om_mem_SB μ h' h Φ.2))
  convert this using 1
  funext x
  simp [xi, flat]
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarComplementFrameDiagModConductor
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.DIV GlobalTheory.FlagBasis GlobalTheory.LevNorm
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ScalW

set_option maxHeartbeats 800000 in
theorem scalar_diag_mod_g : ∀ (D : D7) (X : HidaSetting D) (u : D.what₂.Word) (β : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)), IsLiftFrame X.B.I X.B.g (flagVec X.e0 X.f0 X.z0 X.bw X.bwd) β → ∀ c : Formalism.L2.Herm.intAf X.B.I.F X.B.I.E, c * sigInt X.B.I c = 1 → (∀ N : ℕ, Nat.Coprime N X.B.g → ZMod' X.B.I N (1 - c.1)) → ∃ h ∈ Hfin X u, (∀ h' ∈ Hfin X u, h * h' = h' * h) ∧ ∃ x : GL (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E), frGL β x = (((X.xu u)⁻¹ * h * X.xu u : X.B.I.Gf) : GL (Fin X.B.I.n) (X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F)) ∧ ∀ i j, ZMod' X.B.I X.B.g (((x : Matrix (Fin X.B.I.n) (Fin X.B.I.n) (Formalism.L2.Herm.intAf X.B.I.F X.B.I.E)) - midDiag X.B.I.n D.R.rS D.R.k 1 c) i j).1 := by
  intro D X u β hβ c hc hN
  have hg1 : 1 ≤ X.B.g := Formalism.L2.SG.PoincareInHH.Cut.one_le_g X
  obtain ⟨M6, hM6, hz6⟩ := _root_.GlobalTheory.TorusCong.one_sub_T_zmod D X u
  have hTg : Nat.Coprime (D.mem u).A.T X.B.g := _root_.GlobalTheory.TorusCop.natCoprime_of_zmod_mul_one_sub X.B.I X.B.g _ M6 hg1 hM6 hz6
  have hT0 : (D.mem u).A.T ≠ 0 := (D.mem u).A.T_prime.ne_zero
  obtain ⟨Mb, hMb, hb7⟩ := _root_.GlobalTheory.ScalW.ef_near_ref D X
  obtain ⟨Mc, hMc, hc7⟩ := _root_.GlobalTheory.ScalW.znear_term D X u
  have hc' : c.1 * sigA X.B.I c.1 = 1 := by
    have := congrArg Subtype.val hc
    simpa [sigInt_coe] using this
  obtain ⟨hfix, hfz, hidem⟩ := _root_.GlobalTheory.ScalW.prj_fix_idem D X u
  obtain ⟨h, hh, hhi⟩ := _root_.GlobalTheory.unitTorus_unit X.B.I (GlobalTheory.ScalW.prjM X u) c.1
    (fun y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, hidem])
    (fun x y => by rw [GlobalTheory.ScalW.prjM_mulVec, GlobalTheory.ScalW.prjM_mulVec, _root_.GlobalTheory.ScalW.prj_selfAdjoint]) hc'
  have hh' : X.B.I.fmat h = GlobalTheory.ScalW.hMat X u c.1 := hh
  have hhi' : X.B.I.fmat h⁻¹ = GlobalTheory.ScalW.hMat X u (sigA X.B.I c.1) := hhi
  obtain ⟨hH, hcomm⟩ := _root_.GlobalTheory.ScalW.hMat_mem_hfin_comm D X u c.1 h hfix hfz hh'
  obtain ⟨hP0, hfl⟩ := _root_.GlobalTheory.RefProjFlag.prj0_flagVec_mem_mL_or_sub_mem_mL D X

  set P' : VA X.B.I → VA X.B.I := fun y => X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.prj X u (X.B.I.fmat (X.xu u) *ᵥ y)
    with hP'
  set M := Mb * Mc * M6 * (D.mem u).A.T with hMdef
  have hMg : Nat.Coprime M X.B.g := by
    simp only [hMdef, Nat.coprime_mul_iff_left]
    exact ⟨⟨⟨hMb, hMc⟩, hM6⟩, hTg⟩
  have smulL : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ X.B.I.Lf → s • y ∈ X.B.I.Lf := fun hs _ hy => X.B.I.Lf.smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have smulM : ∀ {s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F}, s ∈ IntAf X.B.I.F X.B.I.E → ∀ {y : VA X.B.I},
      y ∈ mL X.B.I X.B.g → s • y ∈ mL X.B.I X.B.g := fun hs _ hy => (mL X.B.I X.B.g).smul_mem (⟨_, hs⟩ : IntAf X.B.I.F X.B.I.E) hy
  have hnear : ∀ y ∈ X.B.I.Lf, (M : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro y hy
    rw [hP']
    beta_reduce
    rw [_root_.GlobalTheory.ScalW.Conj.prj_conj]
    simp only [GlobalTheory.ScalW.prj0]
    have hA1 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) -
        ∑ a, hA X.B.I (X.f0 a) y • X.e0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).1
    have hA2 : (Mb : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • ((∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) -
        ∑ a, hA X.B.I (X.e0 a) y • X.f0 a) ∈ mL X.B.I X.B.g := by
      rw [← Finset.sum_sub_distrib, Finset.smul_sum]
      exact Submodule.sum_mem _ fun a _ => (hb7 y hy a).2
    have hZ := hc7 y hy
    have hw0 : hA X.B.I X.z0 y • X.z0 ∈ X.B.I.Lf :=
      X.B.I.Lf.smul_mem (⟨_, GlobalTheory.St.G.FrameClose.hA_int X.vectorsInLattice.2.1 hy⟩ : IntAf X.B.I.F X.B.I.E) X.vectorsInLattice.2.1
    have hW : ((M6 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) * (1 - (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F))) •
        (hA X.B.I X.z0 y • X.z0) ∈ mL X.B.I X.B.g := Formalism.L2.SG.PoincareInHH.Cut.GU.smul_mL X hz6 hw0
    have hTd : (((D.mem u).A.T : ℕ) : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) *
        divN X.B.I (D.mem u).A.T (hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y) =
        hA X.B.I (X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u) y := Formalism.L2.SG.Pf.unitaryCongruence.gmul_divN X.B.I _ hT0 _
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.fV X a) y • GlobalTheory.ScalW.eV X a) = S1 at hA1 ⊢
    generalize (∑ a, hA X.B.I (GlobalTheory.ScalW.eV X a) y • GlobalTheory.ScalW.fV X a) = S2 at hA2 ⊢
    generalize (∑ a, hA X.B.I (X.f0 a) y • X.e0 a) = S3 at hA1 ⊢
    generalize (∑ a, hA X.B.I (X.e0 a) y • X.f0 a) = S4 at hA2 ⊢
    generalize X.B.I.fmat (X.xu u)⁻¹ *ᵥ GlobalTheory.ScalW.zV X u = z' at hZ hTd ⊢
    generalize divN X.B.I (D.mem u).A.T (hA X.B.I z' y) = dd at hTd ⊢
    generalize hA X.B.I X.z0 y • X.z0 = w0 at hZ hW ⊢
    rw [← hTd] at hZ
    rw [hMdef, Nat.cast_mul, Nat.cast_mul, Nat.cast_mul, GlobalTheory.ScalW.scalW_ident]
    have hN' : ∀ m : ℕ, (m : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) ∈ IntAf X.B.I.F X.B.I.E := fun m => natCast_mem _ m
    exact sub_mem (sub_mem (add_mem (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA1)
      (smulM (mul_mem (mul_mem (hN' _) (hN' _)) (hN' _)) hA2)) (smulM (mul_mem (hN' _) (hN' _)) hZ))
      (smulM (mul_mem (hN' _) (hN' _)) hW)
  have key : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, ZMod' X.B.I M (1 - s) → ∀ y ∈ X.B.I.Lf,
      (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) ∈ mL X.B.I X.B.g := by
    intro s hzs y hy
    obtain ⟨t, ht, e⟩ := hzs
    rw [e, mul_comm, mul_smul]
    exact smulM ht (hnear y hy)
  have hint : ∀ s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F, s ∈ IntAf X.B.I.F X.B.I.E → ZMod' X.B.I M (1 - s) →
      ∀ y ∈ X.B.I.Lf, s • y + (1 - s) • P' y ∈ X.B.I.Lf := by
    intro s hs hzs y hy
    have e : s • y + (1 - s) • P' y = s • y + (1 - s) • (P' y - GlobalTheory.ScalW.prj0 X y) + (1 - s) • GlobalTheory.ScalW.prj0 X y := by
      rw [smul_sub]; abel
    rw [e]
    exact add_mem (add_mem (smulL hs hy) (GlobalTheory.St.G.FrameClose.mL_le _ (key s hzs y hy)))
      (smulL (sub_mem (one_mem _) hs) (hP0 y hy))
  have hact : ∀ (s : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) (k : X.B.I.Gf), X.B.I.fmat k = GlobalTheory.ScalW.hMat X u s →
      ∀ y, X.B.I.fmat ((X.xu u)⁻¹ * k * X.xu u) *ᵥ y = s • y + (1 - s) • P' y := by
    intro s k hk y
    rw [Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, Formalism.L2.SG.PoincareInHH.Cut.fmat_mul, ← mulVec_mulVec, ← mulVec_mulVec, hk,
      GlobalTheory.ScalW.hMat_mulVec, mulVec_add, mulVec_smul, mulVec_smul, mulVec_mulVec,
      Formalism.L2.SG.PoincareInHH.Cut.fmat_inv_mul, one_mulVec]
  have hcM : ZMod' X.B.I M (1 - c.1) := hN M hMg
  have hsM : ZMod' X.B.I M (1 - sigA X.B.I c.1) := by
    have := Formalism.L2.SG.Pf.unitaryCongruence.Z_sig X.B.I M hcM
    rwa [map_sub, map_one] at this
  have hinvY : ((X.xu u)⁻¹ * h * X.xu u)⁻¹ = (X.xu u)⁻¹ * h⁻¹ * X.xu u := by group
  set d : Fin X.B.I.n → Formalism.L2.Herm.intAf X.B.I.F X.B.I.E :=
    fun i => if D.R.rS ≤ i.val ∧ i.val < D.R.rS + D.R.k then c else 1 with hd
  obtain ⟨x, hx1, hx2⟩ := _root_.GlobalTheory.FrameDiag.diag_mod_in_frame X.B.I X.B.g _ β ((X.xu u)⁻¹ * h * X.xu u) d hβ
    (fun y hy => by rw [hact _ h hh']; exact hint _ c.2 hcM y hy)
    (fun y hy => by
      rw [hinvY, hact _ _ hhi']
      exact hint _ (Formalism.L2.SG.Pf.unitaryCongruence.sigA_mem X.B.I c.2) hsM y hy)
    (fun j => by
      obtain ⟨hbL, hW, hnW⟩ := hfl j.val
      rw [hact _ h hh']
      have hk := key c.1 hcM _ hbL
      by_cases hj : D.R.rS ≤ j.val ∧ j.val < D.R.rS + D.R.k
      · have e1 : (d j).1 = c.1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          rw [smul_sub]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hW hj))
      · have e1 : (d j).1 = 1 := by simp [hd, hj]
        rw [e1]
        have e : c.1 • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val + (1 - c.1) • P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val)
            - (1 : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F) • flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val =
            (1 - c.1) • (P' (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val))
            + (1 - c.1) • (GlobalTheory.ScalW.prj0 X (flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) - flagVec X.e0 X.f0 X.z0 X.bw X.bwd j.val) := by
          simp only [smul_sub, sub_smul, one_smul]; abel
        rw [e]
        exact add_mem hk (smulM (sub_mem (one_mem _) c.2) (hnW hj)))
  refine ⟨h, hH, hcomm, x, hx1, fun i j => ?_⟩
  have e : midDiag X.B.I.n D.R.rS D.R.k 1 c = Matrix.diagonal d := by
    simp only [midDiag, hd]
  rw [e]
  exact hx2 i j

end GlobalTheory.ScalW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SeeSawFixedLevelCombinationEqSinglePlaceOnVacuum
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.GSuppComb

theorem foldr_extract {ι X : Type} [DecidableEq ι] (g : ι → X → X) (i : ι)
    (hc : ∀ a, a ≠ i → ∀ x, g a (g i x) = g i (g a x)) :
    ∀ (l : List ι) (x : X), i ∈ l → l.foldr g x = g i ((l.erase i).foldr g x) := by
  intro l x hi
  induction l with
  | nil => simp at hi
  | cons a t ih =>
    by_cases ha : a = i
    · subst ha
      simp
    · have hit : i ∈ t := by
        rcases List.mem_cons.1 hi with h | h
        · exact absurd h.symm ha
        · exact h
      have he : (a :: t).erase i = a :: t.erase i := by
        simp [List.erase_cons, ha]
      rw [he, List.foldr_cons, List.foldr_cons, ih hit, hc a ha]

variable {D : D7}

theorem latO_mono {S T : HSp D} (LS : Set (Fin S.rank → D.host.E)) (LT : Set (Fin T.rank → D.host.E))
    {P P' : Pl D → Prop} (h : ∀ p, P p → P' p) : latO S T LS LT P ≤ latO S T LS LT P' := by
  apply AddSubgroup.closure_mono
  rintro w ⟨α, hα, hv, rest⟩
  exact ⟨α, hα, fun p hp => hv p fun hq => hp (h p hq), rest⟩

theorem vac_mono {ψ : AddChar (AF D.host.F) ℂ} {S T : HSp D} {LS : Lat S} {LT : Lat T} {P P' : Pl D → Prop}
    (h : ∀ p, P p → P' p) {f : WO S T → ℂ} (hf : Vac ψ S T LS LT P' f) : Vac ψ S T LS LT P f :=
  ⟨hf.1, fun u hu => hf.2.1 u (latO_mono _ _ h hu), fun e he u hu hh => hf.2.2 e he u (latO_mono _ _ h hu) hh⟩

theorem eg_combAt {c : Comm D} {v : VCom c} (G : GLoc v) (j : ℕ) (hj : j ≤ G.s) : CombAt (· = G.q.v) (G.eg j) := by
  intro u hu a b
  have h := (G.eg_is j (G.s - j) (by omega)).1 u hu a b
  exact (GlobalTheory.FinPl.FrameLat.idem_iff G.q _).2 h

theorem comb_eq_at_place : ∀ {D : D7} {c : Comm D} {v : VCom c} {n : ℕ}, c.Is → v.Is → ∀ (G : Fin n → GLoc v), GPin G → ∀ (j : ℕ), j + 1 < D.R.m → ∀ (Ψ : WO (c.V j) (c.V (j + 1)) → ℂ), Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· ∈ v.gP) Ψ → ∀ (i : Fin n), ∃ F, Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) F ∧ comb c.ψ _ _ (v.eG j) Ψ = comb c.ψ _ _ ((G i).eg j) F := by
  intro D c v n hc hv G hG j hj Ψ hΨ i
  have hI := _root_.GlobalTheory.DisjComb.main D c.ψ hc.std (c.V j) (c.V (j + 1))
  have hca : ∀ i', CombAt (· = (G i').q.v) ((G i').eg j) := fun i' =>
    eg_combAt (G i') j (by have := (G i').hs; omega)
  have hdisj : ∀ a b : Fin n, a ≠ b → ∀ p, p = (G a).q.v → ¬ p = (G b).q.v := fun a b hab p ha hb =>
    hab (hG.inj (ha.symm.trans hb))
  let g : Fin n → (WO (c.V j) (c.V (j + 1)) → ℂ) → (WO (c.V j) (c.V (j + 1)) → ℂ) :=
    fun a f => comb c.ψ _ _ ((G a).eg j) f
  refine ⟨((List.finRange n).erase i).foldr g Ψ, ?_, ?_⟩
  · have h0 : Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) Ψ :=
      vac_mono (fun p hp => by rw [hp]; exact (hG.places _).2 ⟨i, rfl⟩) hΨ
    have key : ∀ l : List (Fin n), (∀ a ∈ l, a ≠ i) → Vac c.ψ _ _ (v.N j) (v.N (j + 1)) (· = (G i).q.v) (l.foldr g Ψ) := by
      intro l
      induction l with
      | nil => intro _; exact h0
      | cons a t ih =>
        intro hl
        exact ((hI (· = (G a).q.v) (· = (G i).q.v) (hdisj a i (hl a (List.mem_cons_self ..)))).2.1 _ (hca a)).2 _ _ _
          (ih fun b hb => hl b (List.mem_cons_of_mem _ hb))
    exact key _ fun a ha => ((List.nodup_finRange n).mem_erase_iff.1 ha).1
  · rw [hG.eG j hj Ψ hΨ.1]
    exact foldr_extract g i (fun a ha x => (hI _ _ (hdisj a i ha)).1 _ _ (hca a) (hca i) x) _ Ψ (List.mem_finRange i)

end GlobalTheory.GSuppComb

end
end

