module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0014
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0007
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0104
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.Bundle0002
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsCuspidalIffCompositions
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlockTriMemParab
public import Formalism.LocalToGlobal.GroupLattices.PendingLemmas.Bundle0003

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOneOfCompact
section
noncomputable section

namespace GlobalTheory.XiOver

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.RowTie GlobalTheory.SplitRead

section Coeff

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} (N : NData R H what₂) (A : NAut N) (i : N.Loc)

theorem norm_iota_le_one (b : N.O i) : ‖iotaOQ N A i b‖ ≤ 1 := by
  obtain ⟨C, hC⟩ := GlobalTheory.CoeffEmbedding.exists_norm_le N A i
  by_contra h
  rw [not_le] at h
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C h
  have := hC (b ^ n)
  rw [map_pow, norm_pow] at this
  linarith

theorem norm_iota_lt_one {c : N.O i} (hc : c ∈ IsLocalRing.maximalIdeal (N.O i)) :
    ‖iotaOQ N A i c‖ < 1 := by
  obtain ⟨e, he⟩ := GlobalTheory.CoeffEmbedding.exists_pow_le_span N A i
  have h1 : c ^ e ∈ Ideal.span {((N.l i : ℕ) : N.O i)} := he (Ideal.pow_mem_pow hc e)
  obtain ⟨b, hb⟩ := Ideal.mem_span_singleton.1 h1
  have hl : ‖iotaOQ N A i ((N.l i : ℕ) : N.O i)‖ < 1 := by
    rw [map_natCast, ← map_natCast (algebraMap ℚ_[N.l i] (Qbar (N.l i))), norm_algebraMap']
    exact Padic.norm_p_lt_one
  by_contra h
  rw [not_lt] at h
  have h2 := one_le_pow₀ h (n := e)
  rw [← norm_pow, ← map_pow, hb, map_mul, norm_mul] at h2
  exact absurd ((mul_le_of_le_one_right (norm_nonneg _) (norm_iota_le_one N A i b)).trans_lt hl) (not_lt.2 h2)

theorem isUnit_of_norm {c : N.O i} (hc : ‖iotaOQ N A i c‖ = 1) : IsUnit c := by
  by_contra hu
  have := norm_iota_lt_one N A i (c := c) ((IsLocalRing.mem_maximalIdeal c).2 hu)
  linarith

theorem norm_iota_unit {c : N.O i} (hc : IsUnit c) : ‖iotaOQ N A i c‖ = 1 := by
  obtain ⟨u, rfl⟩ := hc
  have h1 := norm_iota_le_one N A i (u : N.O i)
  have h2 := norm_iota_le_one N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)
  have h3 : ‖iotaOQ N A i (u : N.O i)‖ * ‖iotaOQ N A i ((u⁻¹ : (N.O i)ˣ) : N.O i)‖ = 1 := by
    rw [← norm_mul, ← map_mul, Units.mul_inv, map_one, norm_one]
  nlinarith [norm_nonneg (iotaOQ N A i (u : N.O i)), norm_nonneg (iotaOQ N A i ((u⁻¹ : (N.O i)ˣ) : N.O i))]

theorem iota_inj : Function.Injective (iotaOQ N A i) :=
  (A.iotaQ i).injective.comp (IsFractionRing.injective (N.O i) (FractionRing (N.O i)))

theorem iota_smul (z : ℤ_[N.l i]) (y : N.O i) :
    iotaOQ N A i (z • y) = algebraMap ℚ_[N.l i] (Qbar (N.l i)) (z : ℚ_[N.l i]) * iotaOQ N A i y := by
  rw [Algebra.smul_def, map_mul]
  congr 1
  exact A.iotaQ_alg i z

theorem isClosed_range_iota : IsClosed (Set.range (iotaOQ N A i)) := by
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := ℤ_[N.l i]) (M := N.O i)
  let f : (s → ℤ_[N.l i]) → Qbar (N.l i) := fun c =>
    ∑ y : s, algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c y : ℚ_[N.l i]) * iotaOQ N A i y
  have hf : Continuous f := by
    refine continuous_finsetSum _ fun y _ => ?_
    exact ((continuous_algebraMap ℚ_[N.l i] (Qbar (N.l i))).comp
      ((continuous_subtype_val : Continuous fun x : ℤ_[N.l i] => (x : ℚ_[N.l i])).comp
        (continuous_apply y))).mul continuous_const
  have hr : Set.range (iotaOQ N A i) = Set.range f := by
    ext x
    constructor
    · rintro ⟨b, rfl⟩
      have hb : b ∈ Submodule.span ℤ_[N.l i] (s : Set (N.O i)) := hs ▸ Submodule.mem_top
      obtain ⟨c, -, rfl⟩ := Submodule.mem_span_finset.1 hb
      refine ⟨fun y => c y, ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [f, iota_smul]
      exact Finset.sum_coe_sort s (fun y => algebraMap ℚ_[N.l i] (Qbar (N.l i)) (c y : ℚ_[N.l i]) * iotaOQ N A i y)
    · rintro ⟨c, rfl⟩
      refine ⟨∑ y : s, c y • (y : N.O i), ?_⟩
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simp only [f, iota_smul]
  rw [hr]
  exact (isCompact_range hf).isClosed

theorem mem_range_of_norm {x : FractionRing (N.O i)} (hx : ‖A.iotaQ i x‖ = 1) :
    A.iotaQ i x ∈ Set.range (iotaOQ N A i) := by
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  rcases ValuationRing.isInteger_or_isInteger (N.O i) x with ⟨c, hc⟩ | ⟨c, hc⟩
  · exact ⟨c, by rw [← hc]; rfl⟩
  · have h1 : ‖iotaOQ N A i c‖ = 1 := by
      show ‖A.iotaQ i (algebraMap _ _ c)‖ = 1
      rw [hc, map_inv₀, norm_inv, hx, inv_one]
    obtain ⟨u, rfl⟩ := isUnit_of_norm N A i h1
    refine ⟨((u⁻¹ : (N.O i)ˣ) : N.O i), ?_⟩
    show A.iotaQ i (algebraMap _ _ _) = _
    congr 1
    have h2 : algebraMap (N.O i) (FractionRing (N.O i)) (u : N.O i) * algebraMap (N.O i) (FractionRing (N.O i)) ((u⁻¹ : (N.O i)ˣ) : N.O i) = 1 := by
      rw [← map_mul, Units.mul_inv, map_one]
    rw [hc] at h2
    field_simp at h2
    exact h2

theorem norm_eq_one_of_compact {Γ k : Type} [Group Γ] [TopologicalSpace Γ] [CompactSpace Γ] [NormedField k]
    (d : Γ →* k) (hd : Continuous d) (g : Γ) : ‖d g‖ = 1 := by
  obtain ⟨C, hC⟩ := (isCompact_range (continuous_norm.comp hd)).bddAbove
  have hle : ∀ g, ‖d g‖ ≤ 1 := by
    intro g
    by_contra hlt
    rw [not_le] at hlt
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt C hlt
    have : ‖d (g ^ n)‖ ≤ C := hC ⟨g ^ n, rfl⟩
    rw [map_pow, norm_pow] at this
    linarith
  have h1 : ‖d g‖ * ‖d g⁻¹‖ = 1 := by rw [← norm_mul, ← map_mul, mul_inv_cancel, map_one, norm_one]
  have := hle g; have := hle g⁻¹; have := norm_nonneg (d g); have := norm_nonneg (d g⁻¹)
  nlinarith

theorem mem_pow_of_norm_lt (k : ℕ) : ∃ δ : ℝ, 0 < δ ∧ ∀ y : N.O i, ‖iotaOQ N A i y‖ < δ →
    y ∈ IsLocalRing.maximalIdeal (N.O i) ^ k := by
  obtain ⟨p, hp⟩ := IsDiscreteValuationRing.exists_irreducible (N.O i)
  have hp0 : iotaOQ N A i p ≠ 0 := by
    intro h
    have : p = 0 := iota_inj N A i (by simpa using h)
    exact hp.ne_zero this
  refine ⟨‖iotaOQ N A i p‖ ^ k, pow_pos (norm_pos_iff.2 hp0) k, fun y hy => ?_⟩
  rcases eq_or_ne y 0 with rfl | hy0
  · exact zero_mem _
  obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hy0 hp
  rw [map_mul, norm_mul, norm_iota_unit N A i u.isUnit, one_mul, map_pow, norm_pow] at hy
  have hlt : ‖iotaOQ N A i p‖ < 1 := norm_iota_lt_one N A i (by
    rw [hp.maximalIdeal_eq]; exact Ideal.mem_span_singleton_self p)
  have hkn : k ≤ n := by
    by_contra h
    rw [not_le] at h
    exact absurd hy (not_lt.2 (pow_le_pow_of_le_one (norm_nonneg _) hlt.le h.le))
  rw [hp.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
  exact (pow_dvd_pow p hkn).mul_left _

theorem exists_integral_char (d : G H.E N.Om →* Qbar (N.l i)) (hd : Continuous d) (S : Set (G H.E N.Om))
    (hS : closure S = Set.univ) (hv : ∀ σ ∈ S, d σ ∈ Set.range (A.iotaQ i)) :
    ∃ ξ : G H.E N.Om →* (N.O i)ˣ, Continuous (fun g => ((ξ g : (N.O i)ˣ) : N.O i)) ∧
      ∀ g, iotaOQ N A i ((ξ g : (N.O i)ˣ) : N.O i) = d g := by
  have : IsGalois H.E N.Om := {}
  have hn := norm_eq_one_of_compact d hd
  have hinj := iota_inj N A i
  have hall : ∀ g, d g ∈ Set.range (iotaOQ N A i) := by
    have hsub : closure S ⊆ d ⁻¹' Set.range (iotaOQ N A i) :=
      closure_minimal (fun σ hσ => by
        obtain ⟨x, hx⟩ := hv σ hσ
        have := mem_range_of_norm N A i (x := x) (by rw [hx]; exact hn σ)
        rw [hx] at this
        exact this) ((isClosed_range_iota N A i).preimage hd)
    intro g
    exact hsub (hS ▸ Set.mem_univ g)
  choose u hu using hall
  let ξ0 : G H.E N.Om →* N.O i :=
    { toFun := u
      map_one' := hinj (by rw [hu, map_one, map_one])
      map_mul' := fun a b => hinj (by rw [hu, map_mul, map_mul, hu, hu]) }
  refine ⟨ξ0.toHomUnits, ?_, fun g => ?_⟩
  · have hval : (fun g => ((ξ0.toHomUnits g : (N.O i)ˣ) : N.O i)) = u := funext fun g => rfl
    rw [hval, continuous_iff_continuousAt]
    intro g
    rw [ContinuousAt, ← tendsto_sub_nhds_zero_iff,
      (N.O_adic i).hasBasis_nhds_zero.tendsto_right_iff]
    intro k _
    obtain ⟨δ, hδ, hk⟩ := mem_pow_of_norm_lt N A i k
    have hcd : ∀ᶠ x in nhds g, ‖d x - d g‖ < δ := by
      have := (hd.tendsto g)
      exact (Metric.tendsto_nhds.1 this δ hδ).mono fun x hx => by simpa [dist_eq_norm] using hx
    filter_upwards [hcd] with x hx
    apply hk
    rw [map_sub, hu, hu]
    exact hx
  · exact hu g

end Coeff

section Main

open Formalism.L2.Host

theorem inf_int (D : D7) (hA : Formalism.MainNotions.SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) (z : ℂ)
    (hz : z ∈ D.naut.infG D.naut.etaTinv τ) : ∃ k : ℤ, z + ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = (k : ℂ) := by
  obtain ⟨v, hv⟩ := D.R.t_odd
  have hs : ((-(D.R.t : ℝ) / 2 : ℝ) : ℂ) = -(v : ℂ) - 1 / 2 := by
    rw [hv]
    push_cast
    ring
  obtain ⟨h1, h3⟩ := hA.2.1 τ
  rw [h3] at hz
  rcases h1 with h1 | h1
  · rw [h1] at hz
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz
    subst hz
    exact ⟨-(v : ℤ) - 1, by rw [hs]; push_cast; ring⟩
  · rw [h1] at hz
    simp only [Multiset.map_singleton, Multiset.mem_singleton] at hz
    subst hz
    exact ⟨-(v : ℤ), by rw [hs]; push_cast; ring⟩

theorem frob_value (D : D7) (C : CharFrame D) (nch : NChoice D) (Tp : TupTied D C nch)
    (T : NCharTied D C nch Tp) (V : ValLL0 D C) (w : PlE D.host) :
    ∃ x : D.what₂.LL, D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) =
      {D.what₂.embLL x} := by
  obtain ⟨v, hv⟩ := D.R.t_odd
  have hu := (D.naut.etaTinv_def w).1
  have hU := (T.unr_iff _ w).1 hu
  have hf := T.frob _ w hU
  rw [T.etaTinv] at hf hU
  have hE : C.eta.UnrAt w := by simpa using hU.inv
  obtain ⟨y, hy⟩ := V.eta w hE
  have hq : ((normV w : ℕ) : ℂ) ≠ 0 := by
    have := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
    exact Nat.cast_ne_zero.2 Nat.card_pos.ne'
  have hn : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
    simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hy' : D.what₂.embLL (y : D.what₂.LL) =
      ((C.eta.val w : ℂˣ) : ℂ) * ((normV w : ℕ) : ℂ) ^ (-(((1 / 2 : ℝ)) : ℂ)) := by
    have e : D.what₂.embLL (y : D.what₂.LL) = C.eta.valTw (1 / 2) w := hy
    rw [e, HChar.valTw, hn]
  refine ⟨(y : D.what₂.LL) * (((normV w : ℕ) : D.what₂.LL)⁻¹) ^ v, ?_⟩
  rw [D.naut.frobEig_tw _ _ hu, hf, Multiset.map_singleton, HChar.val_inv, inv_inv]
  congr 1
  rw [map_mul, map_pow, map_inv₀, map_natCast, hy', mul_assoc]
  congr 1
  have e1 : (((-(D.R.t : ℝ) / 2 : ℝ)) : ℂ) = -(((1 / 2 : ℝ)) : ℂ) + -(v : ℂ) := by
    rw [hv]
    push_cast
    ring
  rw [e1, Complex.cpow_add _ _ hq, Complex.cpow_neg _ (v : ℂ), Complex.cpow_natCast, inv_pow]

end Main

end GlobalTheory.XiOver
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ParahoricVectorTwoBlockProductExistsPermNeZero
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel
open GlobalTheory.IndefiniteRowSideFullHecke.CuspidalSupportClasses GlobalTheory.TypeDim

noncomputable section

namespace GlobalTheory.ParahoricPerm

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {r t : ℕ} {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  {σ₁ : Representation ℂ (GL (Fin r) k) V} {σ₂ : Representation ℂ (GL (Fin t) k) W}

theorem act_incl {χ : kˣ →* ℂˣ} {f : IndSp (part r t) ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)}
    (hf : IsParahoricVec χ (prod₂ σ₁ σ₂) f) {h : GL (Fin (r + t)) 𝒪[k]} {a : GL (Fin r) 𝒪[k]}
    {d : GL (Fin t) 𝒪[k]} (hb : HasBlocks h a d) :
    prod₂ σ₁ σ₂ (incl k (r + t) h) f = (χ (Matrix.GeneralLinearGroup.det (incl k t d)) : ℂ) • f := by
  refine hf (incl k (r + t) h) ⟨h, rfl⟩ (fun i j => ?_) _ ?_
  · rw [incl_val]
    exact Valuation.Integer.not_isUnit_iff_valuation_lt_one.mp (hb.2.2 i j)
  · rw [Matrix.GeneralLinearGroup.val_det_apply]
    congr 1
    exact Matrix.ext fun i j => by rw [Matrix.submatrix_apply, incl_val, incl_val, hb.2.1]

theorem val_mul_of_smul {f : IndSp (part r t) ((extTensor σ₁ σ₂).comp (leviTwo k (Fin r) (Fin t)).symm.toMonoidHom)}
    (x y : GL (Fin (r + t)) k) (c : ℂ) (hy : prod₂ σ₁ σ₂ y f = c • f) : f.1.1 (x * y) = c • f.1.1 x := by
  have : f.1.1 (x * y) = (prod₂ σ₁ σ₂ y f).1.1 x := rfl
  rw [this, hy]
  rfl

theorem exists_perm_ne_zero : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V] (W : Type) [AddCommGroup W] [Module ℂ W] (σ₁ : Representation ℂ (GL (Fin r) k) V) (σ₂ : Representation ℂ (GL (Fin t) k) W) (f : _), f ≠ 0 → IsParahoricVec χ (prod₂ σ₁ σ₂) f → ∃ w : Equiv.Perm (Fin (r + t)), f.1.1 (GlobalTheory.Parabolic.permGL k w) ≠ 0 := by
  intro k _ _ _ _ r t χ V _ _ W _ _ σ₁ σ₂ f hf0 hf
  by_contra hall
  push_neg at hall
  apply hf0
  have hg : ∀ g, f.1.1 g = 0 := by
    intro g
    obtain ⟨p, w, S, a, a₁, h, d, -, -, hb, rfl⟩ := GlobalTheory.TypeDim.Coset.coset k r t g
    have h1 : f.1.1 (GlobalTheory.Parabolic.permGL k w * diagOne k r t a) = 0 := by
      rw [← incl_diagO_one, val_mul_of_smul _ _ _ (act_incl hf (hasBlocks_diagO a 1)), hall w, smul_zero]
    have h2 : f.1.1 (GlobalTheory.Parabolic.permGL k w * diagOne k r t a * incl k (r + t) h) = 0 := by
      rw [val_mul_of_smul _ _ _ (act_incl hf hb), h1, smul_zero]
    rw [f.1.2 p _, h2]
    simp
  exact Subtype.ext (Subtype.ext (funext hg))

end GlobalTheory.ParahoricPerm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.RingHomWittAlgClosureEqOfCongrModPrime
section
namespace GlobalTheory

open Formalism.L2.G.Pend in
theorem wittKbar_eq_zero_of_forall_dvd (p : ℕ) [Fact p.Prime] (z : WW p)
    (h : ∀ N : ℕ, (p : WW p) ^ N ∣ z) : z = 0 := by
  have hc : wToC p z = wToC p 0 := by
    rw [map_zero]
    apply eq_of_close
    intro N
    obtain ⟨b, hb⟩ := h N
    rw [sub_zero, hb]
    exact norm_wToC_pow_mul p N b
  exact wToC_injective p hc

theorem dvd_pow_pow_sub_self_of_dvd {W : Type} [CommRing W] (p n : ℕ)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (x : W) :
    ∀ j : ℕ, (p : W) ∣ x ^ (p ^ (n * j)) - x := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have e : x ^ (p ^ (n * (j + 1))) = (x ^ (p ^ (n * j))) ^ (p ^ n) := by
      rw [← pow_mul, ← pow_add, mul_add, mul_one]
    rw [e]
    have := dvd_add (h (x ^ (p ^ (n * j)))) ih
    simpa [sub_add_sub_cancel] using this

theorem ringHom_wittKbar_eq_of_modp (p : ℕ) [Fact p.Prime] (n : ℕ) (W : Type) [CommRing W] (hn : 0 < n)
    (h : ∀ x : W, (p : W) ∣ x ^ (p ^ n) - x) (f g : W →+* Formalism.L2.G.Pend.WW p)
    (hfg : ∀ x, (p : Formalism.L2.G.Pend.WW p) ∣ f x - g x) : f = g := by
  have key : ∀ k : ℕ, ∀ x : W, (p : Formalism.L2.G.Pend.WW p) ^ k ∣ f x - g x := by
    intro k
    induction k with
    | zero => intro x; simp
    | succ k ih =>
      intro x
      obtain ⟨y, hy⟩ := dvd_pow_pow_sub_self_of_dvd p n h x k
      have hx : x = x ^ (p ^ (n * k)) - (p : W) * y := by rw [← hy]; ring
      have h1 : (p : Formalism.L2.G.Pend.WW p) ^ (n * k + 1) ∣ (f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k)) :=
        dvd_sub_pow_of_dvd_sub (hfg x) (n * k)
      have hk : k + 1 ≤ n * k + 1 := by
        have : k ≤ n * k := Nat.le_mul_of_pos_left k hn
        omega
      have h1' := (pow_dvd_pow (p : Formalism.L2.G.Pend.WW p) hk).trans h1
      have h2 : (p : Formalism.L2.G.Pend.WW p) ^ (k + 1) ∣ (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        rw [pow_succ']
        exact mul_dvd_mul_left _ (ih y)
      have e : f x - g x = ((f x) ^ (p ^ (n * k)) - (g x) ^ (p ^ (n * k))) - (p : Formalism.L2.G.Pend.WW p) * (f y - g y) := by
        conv_lhs => rw [hx]
        simp only [map_sub, map_mul, map_pow, map_natCast]
        ring
      rw [e]
      exact dvd_sub h1' h2
  refine RingHom.ext fun x => ?_
  have := wittKbar_eq_zero_of_forall_dvd p (f x - g x) (fun N => key N x)
  exact sub_eq_zero.mp this

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameIwahoriTorusCharVectorOfParahoricDetCharVect
section
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.SplitRead GlobalTheory.ThetaGL GlobalTheory.TameIwahori ValuativeRel

noncomputable section

namespace GlobalTheory.TameParahoric

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

theorem residue_eq_zero_iff_val_lt (x : 𝒪[k]) :
    IsLocalRing.residue 𝒪[k] x = 0 ↔ valuation k (algebraMap 𝒪[k] k x) < 1 := by
  rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
    (Valuation.integer.integers (valuation k)).isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne x.2 h, fun h => h.ne⟩

theorem val_det_sub_one_lt {m : Type} [Fintype m] [LinearOrder m] (A : Matrix m m 𝒪[k])
    (hl : ∀ i j, j < i → valuation k (algebraMap 𝒪[k] k (A i j)) < 1)
    (hd : ∀ i, valuation k (algebraMap 𝒪[k] k (A i i) - 1) < 1) :
    valuation k ((A.map (algebraMap 𝒪[k] k)).det - 1) < 1 := by
  have h1 : (A.map (IsLocalRing.residue 𝒪[k])).det = 1 := by
    rw [Matrix.det_of_upperTriangular]
    · refine Finset.prod_eq_one fun i _ => ?_
      have := (residue_eq_zero_iff_val_lt (A i i - 1)).2 (by simpa using hd i)
      rw [map_sub, map_one, sub_eq_zero] at this
      simpa using this
    · intro i j hij
      exact (residue_eq_zero_iff_val_lt _).2 (hl i j hij)
  have h2 : IsLocalRing.residue 𝒪[k] (A.det - 1) = 0 := by
    rw [map_sub, map_one, RingHom.map_det, sub_eq_zero]
    simpa using h1
  have := (residue_eq_zero_iff_val_lt _).1 h2
  rwa [map_sub, map_one, RingHom.map_det] at this

theorem isIwVec_of_isParahoricVec (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (r t : ℕ) (χ : kˣ →* ℂˣ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin (r + t)) k) V) (v : V) (hχ : IsTame χ) (hv : IsParahoricVec χ π v) :
    IsIwVec (Fin.append (fun _ : Fin r => (1 : kˣ →* ℂˣ)) (fun _ : Fin t => χ)) π v := by
  have hlt : ∀ (i : Fin t) (j : Fin r), Fin.castAdd t j < Fin.natAdd r i := by
    intro i j
    rw [Fin.lt_iff_val_lt_val]
    simp only [Fin.coe_castAdd, Fin.coe_natAdd]
    omega
  refine ⟨fun h hK hl hd => ?_, fun s hs => ?_⟩
  · obtain ⟨h₀, hh⟩ := hK
    have hval : ∀ i j, h.val i j = algebraMap 𝒪[k] k (h₀.val i j) := by
      intro i j
      rw [← hh]
      rfl
    have hsub : h.val.submatrix (Fin.natAdd r) (Fin.natAdd r) =
        (h₀.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).map (algebraMap 𝒪[k] k) := by
      ext i j
      simp [hval]
    have hdet : valuation k ((h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det - 1) < 1 := by
      rw [hsub]
      refine val_det_sub_one_lt _ (fun i j hij => ?_) (fun i => ?_)
      · simpa [hval] using hl (Fin.natAdd r i) (Fin.natAdd r j) (by simpa using hij)
      · simpa [hval] using hd (Fin.natAdd r i)
    have hne : (h.val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det ≠ 0 := by
      intro h0
      rw [h0, zero_sub, Valuation.map_neg, Valuation.map_one] at hdet
      exact lt_irrefl _ hdet
    have hu : χ (Units.mk0 _ hne) = 1 := hχ _ (by simpa using hdet)
    rw [hv h ⟨h₀, hh⟩ (fun i j => hl _ _ (hlt i j)) (Units.mk0 _ hne) rfl, hu]
    simp
  · have hD : ((∏ j : Fin t, s (Fin.natAdd r j) : kˣ) : k) =
        ((diagT k (Fin (r + t)) s).val.submatrix (Fin.natAdd r) (Fin.natAdd r)).det := by
      rw [val_diagT, Matrix.submatrix_diagonal _ _ (Fin.natAdd_injective _ _), Matrix.det_diagonal]
      simp [Units.coe_prod]
    have hlow : ∀ (i : Fin t) (j : Fin r),
        valuation k ((diagT k (Fin (r + t)) s).val (Fin.natAdd r i) (Fin.castAdd t j)) < 1 := by
      intro i j
      rw [val_diagT, Matrix.diagonal_apply_ne _ (hlt i j).ne']
      simp
    rw [hv _ (iwahori_le_KO k (Fin (r + t)) (diagT_mem_iwahori hs)) hlow _ hD]
    congr 2
    rw [GlobalTheory.SmGL.torusChar_apply, Fin.prod_univ_add, map_prod]
    simp [Fin.append_left, Fin.append_right]

end GlobalTheory.TameParahoric
end
end

