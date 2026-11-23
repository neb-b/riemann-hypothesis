module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0015
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsStepWeil
public import Formalism.SatakeDualWeyl.KpqSubgroupCompact
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalThetaPairExistence
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0154
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0150
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0057
public import Formalism.LocalToGlobal.KernelLattices.KerStd
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0012
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.FourthPowerTheta
public import Formalism.LocalToGlobal.InertKernelTheory.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0147
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0095
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.GelfandKazhdanDual
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0138
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0149
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0132
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0124
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0153
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.IsTemperedGLOfIsUnitaryLSeg

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.HoweUnramifiedAllVacua
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Polynomial
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx
open scoped TensorProduct InnerProductSpace
open GlobalTheory.Hk3

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Hk3

theorem comb_of_scalar {X A M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s) (cA : A →₀ ℂ) :
    ∃ C : X →₀ ℂ, ∀ s, vac s → (cA.sum fun p z => z • a p s) = C.sum fun x z => z • r x s := by
  choose ca hca using ha
  refine ⟨Finsupp.linearCombination ℂ ca cA, fun s hs => ?_⟩
  have h : Finsupp.linearCombination ℂ (fun x => r x s) (Finsupp.linearCombination ℂ ca cA) =
      Finsupp.linearCombination ℂ (fun p => a p s) cA := by
    rw [LinearMap.map_finsupp_linearCombination]
    congr 2
    funext p
    exact (Finsupp.linearCombination_apply ℂ (ca p)).trans (hca p s hs).symm
  calc (cA.sum fun p z => z • a p s) = Finsupp.linearCombination ℂ (fun p => a p s) cA :=
        (Finsupp.linearCombination_apply ℂ cA).symm
    _ = _ := h.symm
    _ = _ := Finsupp.linearCombination_apply ℂ _

theorem comb_transfer {X A B M : Type} [AddCommGroup M] [Module ℂ M] (vac : M → Prop) (r : X → Module.End ℂ M)
    (a : A → Module.End ℂ M) (b : B → Module.End ℂ M)
    (hmodel : ∀ c : X →₀ ℂ, ∀ s, s ≠ 0 → vac s → (c.sum fun x z => z • r x s) = 0 →
      ∀ s', vac s' → (c.sum fun x z => z • r x s') = 0)
    (ha : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → a p s = c.sum fun x z => z • r x s)
    (hb : ∀ p, ∃ c : X →₀ ℂ, ∀ s, vac s → b p s = c.sum fun x z => z • r x s)
    (cA : A →₀ ℂ) (cB : B →₀ ℂ) (s0 : M) (h0 : s0 ≠ 0) (hv : vac s0)
    (heq : (cA.sum fun p z => z • a p s0) = cB.sum fun p z => z • b p s0) :
    ∀ s, vac s → (cA.sum fun p z => z • a p s) = cB.sum fun p z => z • b p s := by
  obtain ⟨CA, hA⟩ := comb_of_scalar vac r a ha cA
  obtain ⟨CB, hB⟩ := comb_of_scalar vac r b hb cB
  have hsub : ∀ s, ((CA - CB).sum fun x z => z • r x s) =
      (CA.sum fun x z => z • r x s) - CB.sum fun x z => z • r x s := by
    intro s
    have e : ∀ C : X →₀ ℂ, (C.sum fun x z => z • r x s) = Finsupp.linearCombination ℂ (fun x => r x s) C :=
      fun C => (Finsupp.linearCombination_apply ℂ C).symm
    rw [e, e, e, map_sub]
  have h0' : ((CA - CB).sum fun x z => z • r x s0) = 0 := by
    rw [hsub, ← hA _ hv, ← hB _ hv, heq, sub_self]
  intro s hs
  have h := hmodel (CA - CB) s0 h0 hv h0' s hs
  rw [hsub, sub_eq_zero, ← hA s hs, ← hB s hs] at h
  exact h

theorem howe_on_span (hH : HoweUnram) {L : Type} [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    {ϖ : L} {σ : L →+* L} {q : ℕ} {δ : L} {n n' : ℕ} {JS : GL (Fin n) L} {JT : GL (Fin n') L} {ψ : AddChar L ℂ}
    {M : Type} [AddCommGroup M] [Module ℂ M] {ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M}
    {ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M}
    (hp : LocPair ϖ σ q δ JS JT ψ ρ ω) (s0 : M) (h0 : s0 ≠ 0) (hv : LocVac ρ s0) :
    (∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ g : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L),
        (g : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (g, 1) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun h => ω (1, h) s0)) ∧
    ∀ w ∈ Submodule.span ℂ (Set.range fun x => ρ x s0),
      (∀ h : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L),
        (h : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, h) w = w) →
      w ∈ Submodule.span ℂ (Set.range fun g => ω (g, 1) s0) := by
  have scal := _root_.GlobalTheory.Hk3.locPair_act_vac_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  set M0 := Submodule.span ℂ (Set.range fun x => ρ x s0) with hM0
  have hs0 : s0 ∈ M0 := by
    refine Submodule.subset_span ⟨0, ?_⟩
    simp [hp.rho_zero]
  have hρ : ∀ x, ∀ m ∈ M0, ρ x m ∈ M0 := by
    intro x m hm
    have hle : M0 ≤ M0.comap (ρ x) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ρ x (ρ y s0) = (ρ x * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.rho_mul x y]
      exact M0.smul_mem _ (Submodule.subset_span ⟨x + y, rfl⟩)
    exact hle hm
  have hω : ∀ p, ∀ m ∈ M0, ω p m ∈ M0 := by
    rintro ⟨g, h⟩ m hm
    have hle : M0 ≤ M0.comap (ω (g, h)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨y, rfl⟩
      have e : ω (g, h) (ρ y s0) = (ω (g, h) * ρ y) s0 := rfl
      simp only [SetLike.mem_coe, Submodule.mem_comap]
      rw [e, hp.norm g h y]
      refine hρ _ _ ?_
      obtain ⟨c, hc⟩ := scal (g, h)
      rw [hc s0 hv]
      exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨c, rfl⟩
    exact hle hm
  let ρ0 : Matrix (Fin n') (Fin n) L → Module.End ℂ M0 := fun x => (ρ x).restrict (hρ x)
  let ω0 : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M0 :=
    { toFun := fun p => (ω p).restrict (hω p)
      map_one' := by
        ext m
        simp
      map_mul' := by
        intro p p'
        ext m
        simp }
  have ρ0_val : ∀ x (m : M0), ((ρ0 x m : M0) : M) = ρ x m := fun _ _ => rfl
  have ω0_val : ∀ p (m : M0), ((ω0 p m : M0) : M) = ω p m := fun _ _ => rfl
  let t0 : M0 := ⟨s0, hs0⟩
  have hv0 : LocVac ρ0 t0 := fun u hu => Subtype.ext (hv u hu)
  have ht0 : t0 ≠ 0 := fun h => h0 (congrArg Subtype.val h)
  have hspan : Submodule.span ℂ (Set.range fun x => ρ0 x t0) = ⊤ := by
    have e : (Set.range fun x => ρ0 x t0) = (Subtype.val ⁻¹' (Set.range fun x => ρ x s0) : Set M0) := by
      ext m
      constructor
      · rintro ⟨x, rfl⟩
        exact ⟨x, rfl⟩
      · rintro ⟨x, hx⟩
        exact ⟨x, Subtype.ext hx⟩
    rw [e]
    exact Submodule.span_span_coe_preimage
  have hp0 : LocPair ϖ σ q δ JS JT ψ ρ0 ω0 :=
    { unr := hp.unr
      odd := hp.odd
      intS := hp.intS
      intT := hp.intT
      hermS := hp.hermS
      hermT := hp.hermT
      delta := hp.delta
      psi_int := hp.psi_int
      psi_ne := hp.psi_ne
      rho_zero := by
        ext m
        simp [ρ0, hp.rho_zero]
      rho_mul := by
        intro x y
        ext m
        have h := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.rho_mul x y)
        exact h
      span := by
        rw [eq_top_iff, ← hspan]
        refine Submodule.span_mono ?_
        rintro _ ⟨x, rfl⟩
        exact ⟨x, t0, hv0, rfl⟩
      norm := by
        intro g h x
        ext m
        have e := congrArg (fun T : Module.End ℂ M => T (m : M)) (hp.norm g h x)
        exact e
      fix := by
        intro g h hg hh s hs
        exact Subtype.ext (hp.fix g h hg hh s (fun u hu => congrArg Subtype.val (hs u hu))) }
  obtain ⟨h1, h2⟩ := hH L ϖ σ q δ n n' JS JT ψ M0 ρ0 ω0 hp0 t0 ht0 hv0 hspan
  constructor
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h1 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h
  · intro w hw hfix
    have h := Submodule.mem_map_of_mem (f := M0.subtype) (h2 ⟨w, hw⟩ (fun g hg => Subtype.ext (hfix g hg)))
    rw [Submodule.map_span, ← Set.range_comp] at h
    exact h

theorem howe_all_vacua : HoweUnram → ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L) (σ : L →+* L) (q : ℕ) (δ : L) (n n' : ℕ) (JS : GL (Fin n) L) (JT : GL (Fin n') L) (ψ : AddChar L ℂ) (M : Type) [AddCommGroup M] [Module ℂ M] (ρ : Matrix (Fin n') (Fin n) L → Module.End ℂ M) (ω : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) × Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →* Module.End ℂ M), LocPair ϖ σ q δ JS JT ψ ρ ω → (∀ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L), (k : GL (Fin n') L) ∈ Formalism.UG.GLint (Fin n') (Formalism.UG.intL L) → ω (1, k) (cT.sum fun b z => z • ω (1, b) s) = cT.sum fun b z => z • ω (1, b) s) → ∃ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, ∀ s, LocVac ρ s → (cT.sum fun b z => z • ω (1, b) s) = cS.sum fun a z => z • ω (a, 1) s) ∧ ∀ cS : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L) →₀ ℂ, (∀ s, LocVac ρ s → ∀ k : Formalism.UG.UJ σ (JS : Matrix (Fin n) (Fin n) L), (k : GL (Fin n) L) ∈ Formalism.UG.GLint (Fin n) (Formalism.UG.intL L) → ω (k, 1) (cS.sum fun a z => z • ω (a, 1) s) = cS.sum fun a z => z • ω (a, 1) s) → ∃ cT : Formalism.UG.UJ σ (JT : Matrix (Fin n') (Fin n') L) →₀ ℂ, ∀ s, LocVac ρ s → (cS.sum fun a z => z • ω (a, 1) s) = cT.sum fun b z => z • ω (1, b) s := by
  intro hH L _ _ _ _ ϖ σ q δ n n' JS JT ψ M _ _ ρ ω hp
  have scal := _root_.GlobalTheory.Hk3.locPair_act_vac_comb L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  have model := _root_.GlobalTheory.Hk3.locVac_rel_indep L ϖ σ q δ n n' JS JT ψ M ρ ω hp
  by_cases hz : ∃ s0 : M, s0 ≠ 0 ∧ LocVac ρ s0
  · obtain ⟨s0, h0, hv⟩ := hz
    obtain ⟨hA, hB⟩ := howe_on_span hH hp s0 h0 hv
    refine ⟨fun cT hT => ?_, fun cS hS => ?_⟩
    · have hw : (cT.sum fun b z => z • ω (1, b) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun b => ω (1, b)) (fun b => scal (1, b)) cT
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cS, hcS⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hB _ hw (hT s0 hv))
      exact ⟨cS, comb_transfer (LocVac ρ) ρ (fun b => ω (1, b)) (fun a => ω (a, 1)) model
        (fun b => scal (1, b)) (fun a => scal (a, 1)) cT cS s0 h0 hv hcS.symm⟩
    · have hw : (cS.sum fun a z => z • ω (a, 1) s0) ∈ Submodule.span ℂ (Set.range fun x => ρ x s0) := by
        obtain ⟨C, hC⟩ := comb_of_scalar (LocVac ρ) ρ (fun a => ω (a, 1)) (fun a => scal (a, 1)) cS
        rw [hC s0 hv]
        exact Finsupp.mem_span_range_iff_exists_finsupp.2 ⟨C, rfl⟩
      obtain ⟨cT, hcT⟩ := Finsupp.mem_span_range_iff_exists_finsupp.1 (hA _ hw (hS s0 hv))
      exact ⟨cT, comb_transfer (LocVac ρ) ρ (fun a => ω (a, 1)) (fun b => ω (1, b)) model
        (fun a => scal (a, 1)) (fun b => scal (1, b)) cS cT s0 h0 hv hcT.symm⟩
  · have hz' : ∀ s, LocVac ρ s → s = 0 := by
      intro s hs
      by_contra hne
      exact hz ⟨s, hne, hs⟩
    refine ⟨fun cT _ => ⟨0, fun s hs => ?_⟩, fun cS _ => ⟨0, fun s hs => ?_⟩⟩
    · simp [hz' s hs, Finsupp.sum]
    · simp [hz' s hs, Finsupp.sum]

end GlobalTheory.Hk3

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntOfHomAt
section
open NumberField IsDedekindDomain Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV
open GlobalTheory.GO.ChRoot GlobalTheory.TopStep

namespace GlobalTheory.ColPeriod.EntQ

section Val

variable {K : Type} [Field K] [NumberField K] (w : HeightOneSpectrum (𝓞 K))

theorem val_of_pow {a : K} {k : ℕ} (hk : 0 < k) (h : w.valuation K (a ^ k) = 1) : w.valuation K a = 1 := by
  rw [map_pow] at h
  exact (pow_eq_one_iff_of_nonneg zero_le' hk.ne').1 h

theorem val_nat {q : ℕ} (hq : (q : 𝓞 K) ∉ w.asIdeal) : w.valuation K (q : K) = 1 := by
  have := (w.valuation_eq_one_iff_notMem (K := K) (r := (q : 𝓞 K))).2 hq
  simpa using this

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)}

theorem val_unitV (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.unitV χ a) ≤ 1 ∧ w.valuation K (LocE.unitV χ a)⁻¹ ≤ 1 := by
  by_cases h : LocE.unitV χ a = 0
  · simp [h]
  · obtain ⟨k, hk, h1⟩ := unitV_root χ a h
    have := val_of_pow w hk (a := LocE.unitV χ a) (by rw [h1, map_one])
    simp [this]

theorem val_locChar (q : ℕ) {cq : K} (hc : w.valuation K cq = 1) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (a : E) :
    w.valuation K (LocE.locChar q cq χ a) ≤ 1 ∧ w.valuation K (LocE.locChar q cq χ a)⁻¹ ≤ 1 := by
  unfold LocE.locChar
  rw [mul_inv, map_mul, map_mul, map_inv₀ _ (cq ^ _), map_zpow₀, hc, one_zpow, inv_one, one_mul, one_mul]
  exact val_unitV w χ _

theorem val_om {a b : ℕ} {mu : E → K} (hmu : ∀ t, w.valuation K (mu t) ≤ 1 ∧ w.valuation K (mu t)⁻¹ ≤ 1) (v : E → ℤ)
    {sq : K} (hsq : w.valuation K sq = 1) (g₀ : (Fin a → E) ≃ₗ[E] (Fin a → E)) (h : (Fin b → E) ≃ₗ[E] (Fin b → E))
    {Φ : Loc.SF E K a b} (hΦ : ∀ x, w.valuation K (Φ x) ≤ 1) (x) : w.valuation K (Loc.om mu v sq g₀ h Φ x) ≤ 1 := by
  unfold Loc.om
  simp only [map_mul, map_zpow₀, hsq, one_zpow, mul_one]
  exact mul_le_one' (mul_le_one' (hmu _).1 (hmu _).2) (hΦ _)

theorem val_PhiQ (q : ℕ) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ) (x) :
    w.valuation K (LocE.PhiQ q χ k₀ r c' n' c n x) ≤ 1 := by
  unfold LocE.PhiQ
  split_ifs
  · exact (val_unitV w χ _).1
  · simp

end Val

section Supp

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

theorem exists_fIdx {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) : ∃ s, s < n + c ∧ LocE.fIdx k₀ c n s = l := by
  refine ⟨LocE.fPos k₀ c n l, ?_, ?_⟩
  · unfold LocE.fPos
    split_ifs <;> omega
  · unfold LocE.fIdx LocE.fPos
    split_ifs <;> omega

theorem int_of_PhiQ {q : ℕ} {χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ} {k₀ r c' n' c n : ℕ} (hk' : k₀ ≤ n') (hk : k₀ ≤ n)
    {x : HomE E (n' + c') (n + c)} (hx : LocE.PhiQ q χ k₀ r c' n' c n x ≠ 0) {v : Sp E (n' + c')}
    (hv : v ∈ stdAt E (n' + c') P) : x v ∈ stdAt E (n + c) P := by
  unfold LocE.PhiQ at hx
  split_ifs at hx with h
  · rw [mem_stdAt] at hv ⊢
    intro i
    rw [apply_eq_sum]
    refine intAt_sum _ fun j _ => (hv j).mul ?_
    obtain ⟨p, hp, e⟩ := exists_fIdx hk i.2
    obtain ⟨p', hp', e'⟩ := exists_fIdx hk' j.2
    have h1 := h.1 p p' hp hp'
    have h2 : Loc.eN E (n' + c') j.1 = Pi.single j 1 := by
      funext l
      simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
    simpa [LocE.entB, e, e', LocE.scE, Loc.atN, h2] using h1
  · exact absurd rfl hx

theorem intAt_chArg {n' c' n c : ℕ} (a : E) (x : HomE E (n' + c') (n + c))
    (h : ∀ v ∈ stdAt E (n' + c') P, a • x v ∈ stdAt E (n + c) P) : IntAt P (a * Loc.chArg x) := by
  unfold Loc.chArg
  rw [Finset.mul_sum]
  refine intAt_sum _ fun i _ => ?_
  unfold Loc.atN
  split_ifs with hi
  · exact mem_stdAt.1 (h _ eN_mem) ⟨n + i, hi⟩
  · simpa using intAt_zero

theorem int_of_homAt {a b : ℕ} {z : HomE E a b} (hz : z ∈ homAt {P} (stdLat E a) (stdLat E b)) (B : ℕ) (s : Fin a) (l : Fin b) :
    IntAt P (((qOf P : E) ^ B)⁻¹ * (((qOf P : E) ^ B) • z) (Pi.single s 1) l) := by
  have h := mem_stdAt.1 (hz P (Finset.mem_singleton_self P) _ (single_mem_stdAt s)) l
  have hq := qOf_ne_zero (P := P)
  rwa [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, inv_mul_cancel_left₀ (pow_ne_zero _ hq)]

end Supp

theorem k_le_N (R : Ranks) (j : ℕ) : R.k ≤ R.N j := by
  unfold Ranks.N
  omega

theorem entryAtQ (hV : VolumeAtQ) : EntryAtQ := by
  intro X Pr R Ch sel S mu cst L G m2 hL P w hP hdeg hq hmu
  have hm := hL.hm
  have hqv := val_nat w hq
  have hsq : w.valuation X.K (cst.sq P) = 1 := val_of_pow w two_pos (by rw [hL.cst_ok.sq_sq, hqv])
  have hom : ∀ i, i < R.m → ∀ hal h x, w.valuation X.K (omPhi Ch sel mu cst i P hal h x) ≤ 1 := by
    intro i hi hal h x
    refine val_om w (fun t => val_locChar w _ (hmu i hi) _ t) _ hsq _ _ (fun y => ?_) x
    rw [PhiAt, if_neg hP]
    exact val_PhiQ w _ _ _ _ _ _ _ _ y
  refine ⟨fun i hi al be => ⟨fun x => ?_, fun x z hz => hL.xiInv i hi al be P x _ (int_of_homAt hz _)⟩,
    fun al y => ⟨fun x => hom m2 (by omega) _ _ _, fun x z hz => hL.psiInvX al P x _ y (int_of_homAt hz _)⟩⟩
  unfold XiAt E1at Loc.E1
  rw [map_mul, map_mul, map_pow, map_inv₀ _ (_ ^ cst.B), map_pow, hqv, one_pow, inv_one, one_pow, one_mul]
  refine mul_le_one' (hV X Pr R _ _ _ _ w hP hdeg hq) (Valuation.map_sum_le _ fun t _ => ?_)
  generalize Loc.xx1 x t = y
  by_cases h0 : omPhi Ch sel mu cst i P (L.h i al P) (L.h (i + 1) be P) y = 0
  · simp [h0]
  rw [map_mul]
  refine mul_le_one' (hom i (by omega) _ _ _) (le_of_eq ?_)
  have h1 := right_ne_zero_of_mul h0
  rw [PhiAt, if_neg hP] at h1
  have hb := hL.boundQ i al P hP
  have hb' := hL.boundQ (i + 1) be P hP
  have hD := hL.depthQ' P hP
  simp only [lamYat, hP, if_false, mem_lamY_zero] at hb hb'
  have hint : IntAt P.1 ((qOf P.1 : X.E) ^ (i + 1) * Loc.chArg y) := by
    refine intAt_chArg _ y fun v hv => ?_
    have h2 := (hb' _ (int_of_PhiQ (k_le_N R _) (k_le_N R _) h1 (hb v hv).1)).2
    have h3 : (L.h i al P) ((L.h i al P)⁻¹ v) = v := LinearEquiv.apply_symm_apply _ v
    simpa [h3] using h2
  have hint' : IntAt P.1 ((qOf P.1 : X.E) ^ cst.D P * -Loc.chArg y) := by
    obtain ⟨d, hd⟩ : ∃ d, cst.D P = d + (i + 1) := ⟨cst.D P - (i + 1), by omega⟩
    rw [hd, pow_add, mul_neg, mul_assoc]
    exact intAt_neg ((intAt_pow (intAt_nat _) _).mul hint)
  exact val_of_pow w (pow_pos (qOf_pos _) _) (by rw [psi_root hL.cst_ok P _ hint', map_one])

end GlobalTheory.ColPeriod.EntQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralJetsNormalisedThetaTranslatesAwayDisc
section
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Ker Formalism.L2.Col Classical
open Formalism.L2.Th1.H (cmL CmOK matH IsIsom taylorMv)
open Formalism.L2.Th1.GD (LocNorm InMul frameM thetaLin)
open Formalism.L2.Th1.E (IntCurve curveL Unif)
open Formalism.DworkPowerSeriesWeights (JetsIntegral)

open scoped ComplexConjugate

theorem GlobalTheory.ThLoc.jetsIntegral_three (hIn : GlobalTheory.ThLoc.Inputs) {a₀ : ℕ} {b₀ c₀ : ℤ} {dK : ℕ} (ha : 0 < a₀) (hd : 0 < dK)
    (lam : ℂ) (hlam : lam ≠ 0) (hd3 : dK % 3 = 2) {n : Type} [Fintype n] [DecidableEq n] (h : Matrix n n ℂ)
    (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (ι : ℂ ≃+* ℂ_[3])
    (hL : GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ dK ha hd lam hlam h Λ θ 3 ι) (W : WeierstrassCurve ℂ_[3])
    (hU : Unif 3 (cmL a₀ b₀ dK ha hd lam hlam) ι W) (hW : IntCurve W)
    {κx : Type} [Fintype κx] (r : κx → ℂ_[3]) (t : κx → n → ℂ) (M : ℕ) (hr : ∀ k, ‖r k‖ ≤ 1) (hM : 0 < M)
    (hpM : ¬ 3 ∣ M) (ht : ∀ k, (M : ℂ) • t k ∈ Λ) {J : Type} [Fintype J] (v : J → n → ℂ)
    (hv : ∀ j, InMul (cmL a₀ b₀ dK ha hd lam hlam) Λ (v j)) {ν : Type} [Fintype ν] (A : J → ν → ℂ_[3])
    (hA : ∀ j x, ‖A j x‖ ≤ 1) :
    JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[3]) h θ r t (frameM (ι : ℂ →+* ℂ_[3]) v A)) := by
  obtain ⟨hcmok, l2, l3, l4, l5⟩ := hL
  obtain ⟨-, -, hcm⟩ := GlobalTheory.ThLoc.LocJets.data ha hd lam hlam hcmok
  have hω : lam * (a₀ : ℂ) ∈ (cmL a₀ b₀ dK ha hd lam hlam).lattice :=
    (cmL a₀ b₀ dK ha hd lam hlam).ω₁_mem_lattice
  have hω1 : Formalism.L2.Th1.CM.omegaK dK * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok 1 (Or.inl rfl)
    simpa [Formalism.L2.Th1.CM.omegaK] using this
  have hω2 : conj (Formalism.L2.Th1.CM.omegaK dK) * (lam * (a₀ : ℂ) / 2) ∉ (cmL a₀ b₀ dK ha hd lam hlam).lattice := by
    have := GlobalTheory.ThLoc.LocJets.half_notMem ha hd lam hlam hcmok (-1) (Or.inr rfl)
    rw [GlobalTheory.ThLoc.LocJets.conj_omegaK]
    simpa [sub_eq_add_neg] using this
  obtain ⟨g₁, ε, hiso, hidx, hidx', hε, hten⟩ := l5
  obtain ⟨Dm, q0, hD, hq0, hfac, hgram⟩ :=
    GlobalTheory.ThLoc.LocJets.gram_transfer a₀ b₀ c₀ dK ha hd lam hlam hcmok n h Λ g₁ hiso 3 ι hidx J v hv
  obtain ⟨Cm, q1, hCm, -, hfacC, -⟩ :=
    Formalism.L2.Th1.GD.FrameCompose_proof ℂ_[3] (Fin 4 × n) n J ν
      (fun w w' => ι (g₁.symm (Pi.single w' 1) w)) Dm (fun i j => ι (v j i))
      (fun j k => ι (Formalism.L2.Th1.GD.hOK (cmL a₀ b₀ dK ha hd lam hlam) h (v j) (v k))) _ q0 A hD hq0 hA hfac hgram
  have key : ∀ k, JetsIntegral (Formalism.L2.Th1.G.linSub (frameM (ι : ℂ →+* ℂ_[3]) v A)
        (MvPowerSeries.map (ι : ℂ →+* ℂ_[3]) (taylorMv (Formalism.L2.Th1.H.opU (matH h) (t k) θ)))) := by
    intro k
    obtain ⟨κ, _, r', s', N', hr', hN', h2N', hs', he⟩ := GlobalTheory.ThLoc.LocJets.fourth_power_theta a₀ b₀ c₀ dK ha hd
      lam hlam hcmok n h Λ l2 l3 θ l4 3 ι g₁ ε hiso hidx hidx' hε hten (t k) M hM hpM (ht k)
    have hj := hIn.jetsThree dK _ hcmok.2.2.1 hd3 hcm ι W hU hW (lam * a₀) hω hω1 hω2
      (Fin 4 × n) κ r' s' N' hr' hN' h2N' hs'
    rw [← he] at hj
    exact GlobalTheory.ThLoc.LocJets.jets_linear ℂ_[3] n _ _ hj ν (frameM (ι : ℂ →+* ℂ_[3]) v A) Cm hCm hfacC
  exact GlobalTheory.ThLoc.LocJets.jets_comb r _ hr key

theorem GlobalTheory.ThLoc.jetsIntegral_away_disc : GlobalTheory.ThLoc.Inputs → ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → ∀ (a₀ : ℕ) (b₀ c₀ : ℤ) (ha : 0 < a₀) (hd : 0 < D.host.d) (lam : ℂ) (hlam : lam ≠ 0), CmOK a₀ b₀ c₀ D.host.d → (cmL a₀ b₀ D.host.d ha hd lam hlam).lattice.toAddSubgroup = TaylorLogMetric.lamOf D cc δ → ∀ (n : Type) [Fintype n] [DecidableEq n] (h : Matrix n n ℂ) (Λ : AddSubgroup (n → ℂ)) (θ : (n → ℂ) → ℂ) (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]), GlobalTheory.ThLoc.LatAt a₀ b₀ c₀ D.host.d ha hd lam hlam h Λ θ p ι → p ≠ D.host.d → (p = 3 → D.host.d % 3 = 2) → ∀ (κx : Type) [Fintype κx] (r : κx → ℂ_[p]) (t : κx → n → ℂ) (M : ℕ), (∀ k, ‖r k‖ ≤ 1) → 0 < M → ¬ p ∣ M → (∀ k, (M : ℂ) • t k ∈ Λ) → ∀ (J : Type) [Fintype J] (v : J → n → ℂ), (∀ j, InMul (cmL a₀ b₀ D.host.d ha hd lam hlam) Λ (v j)) → ∀ (ν : Type) [Fintype ν] (A : J → ν → ℂ_[p]), (∀ j x, ‖A j x‖ ≤ 1) → JetsIntegral (thetaLin (ι : ℂ →+* ℂ_[p]) h θ r t (frameM (ι : ℂ →+* ℂ_[p]) v A)) := by
  intro hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat n _ _ h Λ θ p _ ι hL hpd h3 κx _ r t M hr hM hpM ht
    J _ v hv ν _ A hA
  have hpr : p.Prime := Fact.out
  by_cases hp2 : p = 2
  · subst hp2
    obtain ⟨l1, l2, l3, l4, l5⟩ := hL
    obtain ⟨W, hU, hW, ha1⟩ := GlobalTheory.ThLoc.goodModelTwo_scaleOne hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact (hIn.jetsTwo a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 ι W hU hW ha1 l5 κx r t M hr hM hpM ht
      J v hv ν A hA).1
  by_cases hp3 : p = 3
  · subst hp3
    obtain ⟨W, hU, hW⟩ := GlobalTheory.ThLoc.ModelThree.goodModelThree hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat ι
    exact GlobalTheory.ThLoc.jetsIntegral_three hIn ha hd lam hlam (h3 rfl) h Λ θ ι hL W hU hW r t M hr hM hpM ht v hv A hA
  obtain ⟨l1, l2, l3, l4, l5⟩ := hL
  have h4 : p ≠ 4 := by rintro rfl; exact absurd hpr (by decide)
  have h5 : 5 ≤ p := by have := hpr.two_le; omega
  have hW := GlobalTheory.GoodModelFive.goodModel_five hIn D cc δ hcc hδ a₀ b₀ c₀ ha hd lam hlam hcmok hlat p h5 ι
  have hnd : ¬ p ∣ D.host.d := fun hdv => hpd ((Nat.prime_dvd_prime_iff_eq hpr l1.2.2.2).1 hdv)
  exact (hIn.jetsOdd a₀ b₀ c₀ _ ha hd lam hlam l1 n h Λ l2 l3 θ l4 p hp2 hnd ι hW l5 κx r t M hr hM hpM ht
    J v hv ν A hA).1
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGlobalOfGelfandKazhdan
section
open NumberField GlobalTheory.CuspRep GlobalTheory.ContraPair

namespace GlobalTheory

theorem galoisRepOfPolarizedCuspidal_iff_pair : GlobalTheory.Published.GelfandKazhdanDual →
    (GlobalTheory.Published.CaraianiLocalGlobalDual → GlobalTheory.Published.CaraianiLocalGlobal) ∧
    (GlobalTheory.Published.GaloisRepOfPolarizedPair → GlobalTheory.Published.GaloisRepOfPolarizedCuspidal) := by
  intro hGK
  refine ⟨fun hC => ?_, fun hP => ?_⟩
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π hcsd hcoh
    have hd : DualIsConj π :=
      (dualIsConjBy_one π).1 (GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π 1 (hGK E a _) ((GlobalTheory.GalOfCusp.isConjDualBy_one π).2 hcsd))
    exact hC E Ω l ι a ha π hd hcoh
  · intro E Ω _ _ _ _ _ _ l _ ι a ha π χ hr hpol
    exact hP E Ω l ι a ha π χ hr
      ⟨hpol.sign, GlobalTheory.T.cuspContragredientIsCMConjTwist_of_paired_invTranspose E a π (GlobalTheory.GalOfCusp.compNorm E χ) (hGK E a _) hpol.dual⟩

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.OneAddMaximalMatrixIntegralInverseStatement
section
open Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.one_add_maximal_matrix_integral_inverse : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (n : ℕ) (X : Matrix (Fin n) (Fin n) L), (∀ i j, Valued.v (X i j) < 1) →
  ∃ k : GL (Fin n) L, (k : Matrix (Fin n) (Fin n) L) = 1 + X ∧ ∀ i j, ((k⁻¹ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j ∈ Formalism.UG.intL L := by
  first | exact @GlobalTheory.Hk3.one_add_maximal_inv_int | exact GlobalTheory.Hk3.one_add_maximal_inv_int | (intros; apply GlobalTheory.Hk3.one_add_maximal_inv_int <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TemperedRepTemperedParameterStatement
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tempered_rep_tempered_parameter : ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (h : IsPlaceOver A w) (rc : IrrGL (k := w.adicCompletion E) → WD h), IsRec h rc → ∀ (n : ℕ) (σ : IrrRep (GL (Fin n) (w.adicCompletion E))), GlobalTheory.LocGL.IsTemperedGL σ.ρ → (rc (cls σ)).tempered := by
  first | exact @GlobalTheory.LocLanglands.tempered_of_isTemperedGL | exact GlobalTheory.LocLanglands.tempered_of_isTemperedGL | (intros; apply GlobalTheory.LocLanglands.tempered_of_isTemperedGL <;> assumption)
end

