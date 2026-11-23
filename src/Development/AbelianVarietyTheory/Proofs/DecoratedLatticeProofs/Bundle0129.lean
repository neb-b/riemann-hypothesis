module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0122
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
public import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0008
public import Formalism.LocalToGlobal.IndefiniteReal.OrthogonalComplementCharacterisation
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsHeightLeTwoMulQuotHeight
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.WittDecompSymplInclIsotropicInclAnisotropic
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0019
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0021
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0017
public import Development.AbelianVarietyTheory.Definitions.Divisors.CmHostImaginaryGeneratorNeZero
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0123
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0124

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralOfKeepsSelfDualLatticeLineColon
section
noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow GlobalTheory.Unf GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing GlobalTheory.FinPl
open GlobalTheory.IndefiniteRowSideFullHecke.UnramifiedCharacter (compFin ExtUnramAt CharUnramAt)
open scoped TensorProduct Pointwise
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1600000

namespace GlobalTheory.ColonInt

theorem mem_int_of_pow {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E))
    (c y : Q.adicCompletion E) (hc : c ≠ 0) (h : ∀ n : ℕ, c * y ^ n ∈ Q.adicCompletionIntegers E) :
    y ∈ Q.adicCompletionIntegers E := by
  have h' : ∀ n : ℕ, Valued.v (c * y ^ n) ≤ 1 := fun n =>
    (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).1 (h n)
  refine (IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers (K := E) (v := Q)).2 ?_
  by_contra hy
  push_neg at hy
  have hc' : Valued.v c ≠ 0 := (Valuation.ne_zero_iff _).2 hc
  have hy0 : Valued.v y ≠ 0 := ne_of_gt (lt_trans zero_lt_one hy)
  obtain ⟨a, ha⟩ := WithZero.ne_zero_iff_exists.1 hc'
  obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.1 hy0
  have hb1 : (1 : Multiplicative ℤ) < b := by
    rw [← hb] at hy
    exact WithZero.coe_lt_coe.1 hy
  have h2 := h' (Int.natAbs (Multiplicative.toAdd a) + 1)
  rw [Valuation.map_mul, Valuation.map_pow, ← ha, ← hb, ← WithZero.coe_pow, ← WithZero.coe_mul] at h2
  have h3 : a * b ^ (Int.natAbs (Multiplicative.toAdd a) + 1) ≤ 1 := WithZero.coe_le_coe.1 h2
  have h4 : Multiplicative.toAdd a + (Int.natAbs (Multiplicative.toAdd a) + 1 : ℕ) * Multiplicative.toAdd b ≤ 0 := by
    have := Multiplicative.toAdd_le.2 h3
    simpa [toAdd_mul, toAdd_pow] using this
  have h5' : 0 < Multiplicative.toAdd b := by
    have := Multiplicative.toAdd_lt.2 hb1
    simpa using this
  have h5 : 1 ≤ Multiplicative.toAdd b := by omega
  push_cast at h4
  have h6 : (0:ℤ) ≤ |Multiplicative.toAdd a| := abs_nonneg _
  have h7 : -Multiplicative.toAdd a ≤ |Multiplicative.toAdd a| := neg_le_abs _
  nlinarith

variable {D : D7}

def evQ {E : Type} [Field E] [NumberField E] (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 E)) :
    FiniteAdeleRing (𝓞 E) E →+* Q.adicCompletion E where
  toFun x := x Q
  map_one' := rfl
  map_mul' _ _ := rfl
  map_zero' := rfl
  map_add' _ _ := rfl

theorem herm_cols {S : HSp D} {ρ : ℕ} (A B : Mx D S.rank ρ) (κ a : AE D) (l l' : Fin ρ) :
    GlobalTheory.IwaPlace.hermAt S (fun j => a * A j l) (fun i => κ * B i l') = cA D κ * a * (adj B * (gA S * A)) l' l := by
  simp only [GlobalTheory.IwaPlace.hermAt, Matrix.mul_apply, adj, Matrix.transpose_apply, Matrix.map_apply, map_mul,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

theorem mul_incA_mem {v : Pl D} {a : AE D} (ha : a ∈ intAt D (· = v)) (o : 𝓞 D.host.E) :
    a * incA D (o : D.host.E) ∈ intAt D (· = v) := by
  refine ⟨Ideal.mul_mem_right _ _ ha.1, ?_⟩
  rw [map_mul]
  refine GlobalTheory.FinPl.FrameLat.mul_mem_intAE ha.2 (AddSubgroup.subset_closure ⟨1, fun w => ?_, o, ?_⟩)
  · rw [map_one]; exact one_mem _
  · rfl

theorem exists_den {ι κ : Type} [Fintype ι] [Fintype κ] (M : Matrix ι κ D.host.E) :
    ∃ t : 𝓞 D.host.E, t ≠ 0 ∧ ∀ k l, ∃ o : 𝓞 D.host.E, (t : D.host.E) * M k l = o := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples (nonZeroDivisors (𝓞 D.host.E))
    (Finset.univ : Finset (ι × κ)) (fun p => M p.1 p.2)
  refine ⟨b, nonZeroDivisors.coe_ne_zero b, fun k l => ?_⟩
  obtain ⟨o, ho⟩ := hb (k, l) (Finset.mem_univ _)
  refine ⟨o, ?_⟩
  rw [show ((o : 𝓞 D.host.E) : D.host.E) = algebraMap (𝓞 D.host.E) D.host.E o from rfl, ho, Algebra.smul_def]

theorem colon_int : ∀ (D : D7) (S S₀ : HSp D) (ρ : ℕ) (d : HypDec S S₀ ρ) (L : Lat S) (L₀ : Lat S₀) (v : Pl D), Tame D v → IsSelfDualC S L → MonoAt d L L₀ v → ∀ (i j : Fin ρ) (x : AE D), x - 1 ∈ idAt D (· = v) → (∀ r ∈ idAt D (· = v), (∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * a) ∈ latV S L (· = v)) → ∀ a : AE D, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (r * x * a) ∈ latV S L (· = v)) → x - 1 ∈ intAt D (· = v) := by
  intro D S S₀ ρ d L L₀ v _ hL _ i j x hx hK
  obtain ⟨hsupp, ⟨m, hm, hmul⟩, hchar⟩ := GlobalTheory.IwaPlace.LocSD.isSDAt_latV D S L v hL
  obtain ⟨ε, hcε, hε, hεa⟩ := GlobalTheory.IwaPlace.LocSD.exists_idem (D := D) v
  have hεε : ε * ε = ε := hεa ε hε.1
  obtain ⟨t, ht0, ht⟩ := exists_den (Matrix.fromCols d.e d.e')
  set T : AE D := incA D (t : D.host.E) with hT
  have hX : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jX k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inl l)
    have e : T * d.jX k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inl, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hY : ∀ κ : AE D, κ ∈ intAt D (· = v) → ∀ l k, κ * (T * d.jY k l) ∈ intAt D (· = v) := by
    intro κ hκ l k
    obtain ⟨o, ho⟩ := ht k (Sum.inr l)
    have e : T * d.jY k l = incA D (o : D.host.E) := by
      rw [← ho, Matrix.fromCols_apply_inr, map_mul]; rfl
    rw [e]; exact mul_incA_mem hκ o
  have hU : ∀ l (a : AE D), colMul d.jX l a ∈ latV S L (· = v) →
      ((m : AE D) * ε * cA D T) * a ∈ intAt D (· = v) := by
    intro l a ha
    have hxΛ : (fun k => ((m : AE D) * (ε * T)) * d.jY k l) ∈ latV S L (· = v) := by
      have := hmul (fun k => ε * (T * d.jY k l)) (fun k => hY ε hε l k)
      convert this using 1
      funext k; simp only [Pi.smul_apply, smul_eq_mul]; ring
    have h1 := ((hchar _ (hsupp _ ha)).1 ha) _ hxΛ
    rw [show colMul d.jX l a = fun j => a * d.jX j l from rfl, herm_cols, d.gram_YX, Matrix.one_apply_eq,
      mul_one] at h1
    convert h1 using 1
    rw [map_mul, map_mul, map_natCast, hcε]; ring
  obtain ⟨β, hβ⟩ : ∃ β : AE D, β = (m : AE D) * ε * cA D T := ⟨_, rfl⟩
  rw [← hβ] at hU
  have hβI : β ∈ idAt D (· = v) := by
    rw [hβ]; exact Ideal.mul_mem_right _ _ (Ideal.mul_mem_left _ _ hε.1)
  have hc0 : colMul d.jX j ((m : AE D) * (ε * T)) ∈ latV S L (· = v) := by
    have := hmul (fun k => ε * (T * d.jX k j)) (fun k => hX ε hε j k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul]; ring
  obtain ⟨c, hc⟩ : ∃ c : AE D, c = (m : AE D) * (T * β) := ⟨_, rfl⟩
  have hcK : ∀ a, colMul d.jX j a ∈ latV S L (· = v) → colMul d.jX i (c * a) ∈ latV S L (· = v) := by
    intro a ha
    have := hmul (fun k => (β * a) * (T * d.jX k i)) (fun k => hX _ (hU j a ha) i k)
    convert this using 1
    funext k; simp only [colMul, Pi.smul_apply, smul_eq_mul, hc]; ring
  have hcI : c ∈ idAt D (· = v) := by
    rw [hc]; exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_left _ _ hβI)
  have hit : ∀ n : ℕ, c * x ^ n ∈ idAt D (· = v) ∧ ∀ a, colMul d.jX j a ∈ latV S L (· = v) →
      colMul d.jX i (c * x ^ n * a) ∈ latV S L (· = v) := by
    intro n
    refine ⟨Ideal.mul_mem_right _ _ hcI, ?_⟩
    induction n with
    | zero => rw [pow_zero, mul_one]; exact hcK
    | succ n ih =>
      rw [pow_succ, ← mul_assoc]
      exact hK _ (Ideal.mul_mem_right _ _ hcI) ih
  have hbd : ∀ n : ℕ, β * (c * x ^ n * ((m : AE D) * (ε * T))) ∈ intAt D (· = v) := fun n =>
    hU i _ ((hit n).2 _ hc0)
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  refine ⟨hx, (hΦ.int _).2 fun Q => ?_⟩
  obtain ⟨ψ, hψ⟩ : ∃ ψ : AE D →+* Q.adicCompletion D.host.E, ∀ z, ψ z = Φ z Q :=
    ⟨(evQ Q).comp Φ, fun _ => rfl⟩
  have hψinc : ∀ e : D.host.E, ψ (incA D e) = algebraMap D.host.E _ e := fun e => by
    rw [hψ, hΦ.inc]; rfl
  have hεQ : ψ ε = 0 ∨ ψ ε = 1 := by
    have h := congrArg ψ hεε
    rw [map_mul] at h
    rcases mul_eq_zero.1 (show ψ ε * (ψ ε - 1) = 0 by rw [mul_sub, h, mul_one, sub_self]) with h0 | h1
    · exact Or.inl h0
    · exact Or.inr (sub_eq_zero.1 h1)
  rw [← hψ]
  rcases hεQ with h0 | h1
  · rw [← hεa _ hx, map_mul, h0, zero_mul]; exact zero_mem _
  · rw [map_sub, map_one]
    refine sub_mem ?_ (one_mem _)
    have ht' : (t : D.host.E) ≠ 0 := by exact_mod_cast ht0
    have hκ : (m : D.host.E) ^ 4 * star (t : D.host.E) ^ 2 * (t : D.host.E) ^ 2 ≠ 0 :=
      mul_ne_zero (mul_ne_zero (pow_ne_zero _ (Nat.cast_ne_zero.2 hm.ne')) (pow_ne_zero _ (star_ne_zero.2 ht')))
        (pow_ne_zero _ ht')
    refine mem_int_of_pow Q _ (ψ x) ((map_ne_zero (algebraMap D.host.E _)).2 hκ) fun n => ?_
    have h := (hΦ.int _).1 (hbd n).2 Q
    rw [← hψ] at h
    have e1 : ψ T = algebraMap D.host.E _ (t : D.host.E) := hψinc _
    have e2 : ψ (cA D T) = algebraMap D.host.E _ (star (t : D.host.E)) := hψinc _
    rw [hc, hβ] at h
    simp only [RingHom.map_mul, RingHom.map_pow, map_natCast, h1] at h ⊢
    rw [← e1, ← e2]
    convert h using 1
    ring

end GlobalTheory.ColonInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsWeilDatumConjNegHermitianSpaces
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.ConjWeil

open GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger GlobalTheory.ChiGrid

variable {D : D7}

theorem cj_id_cj_id {X : Type} (f : X → ℂ) : cj id (cj id f) = f := cj_cj id id (fun _ => rfl) f

theorem cj_id_apply {X : Type} (f : X → ℂ) (x : X) : cj id f x = starRingEnd ℂ (f x) := rfl

theorem hecke_inv {χ : (AE D)ˣ →* Circle} (h : IsHeckeChar D χ) : IsHeckeChar D χ⁻¹ :=
  ⟨(h.1.inv : Continuous fun x => (χ x)⁻¹), fun x => by rw [MonoidHom.inv_apply, h.2 x, inv_one]⟩

theorem enorm_conj (z : ℂ) : ‖starRingEnd ℂ z‖ₑ = ‖z‖ₑ := by
  simp [enorm]

theorem mt_negGA_symm (V : HSp D) (g : GA D (negSp V)) : mt V ((negGA V).symm g) = mt (negSp V) g := by
  rw [← mt_negGA, MulEquiv.apply_symm_apply]

theorem continuous_negGA_symm (V : HSp D) : Continuous (negGA V).symm :=
  Continuous.subtype_mk continuous_subtype_val _

theorem UJ_neg {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] (σ : A →+* A) (J : Matrix n n A) :
    Formalism.UG.UJ σ (-J) = Formalism.UG.UJ σ J := by
  ext g
  show Formalism.UG.cT σ (g : Matrix n n A) * (-J) * (g : Matrix n n A) = -J ↔
    Formalism.UG.cT σ (g : Matrix n n A) * J * (g : Matrix n n A) = J
  rw [Matrix.mul_neg, Matrix.neg_mul, neg_inj]

theorem negGA_symm_mem_GQ (V : HSp D) (γ : GA D (negSp V)) (h : γ ∈ GQ (negSp V)) : (negGA V).symm γ ∈ GQ V := by
  unfold GQ HFinIn HFin at *
  erw [Subgroup.mem_subgroupOf] at h ⊢
  convert h using 2 <;> first | rfl | exact (UJ_neg _ _).symm

theorem splitFacO_inv (χS χT : (AE D)ˣ →* Circle) (x y : (AE D)ˣ) :
    ((splitFacO χS⁻¹ χT⁻¹ x y : Circle) : ℂ) = starRingEnd ℂ (splitFacO χS χT x y) := by
  rw [← Circle.coe_inv_eq_conj]
  congr 1
  simp only [splitFacO, MonoidHom.inv_apply, inv_inv, _root_.mul_inv_rev]
  exact mul_comm _ _

theorem conjTarget_apply {S T : HSp D} (om : Om S T) (p : GA D S × GA D (negSp T)) (f : WO S T → ℂ) :
    conjTarget om p f = cj id (om (p.1, (negGA T).symm p.2) (cj id f)) := rfl

theorem conjSource_apply {S T : HSp D} (om : Om S T) (p : GA D (negSp S) × GA D T) (f : WO S T → ℂ) :
    conjSource om p f = cj id (om ((negGA S).symm p.1, p.2) (cj id f)) := rfl

theorem actO_negT (S T : HSp D) (g : GA D S) (h : GA D (negSp T)) (w : WO S T) :
    actO S (negSp T) g h w = actO S T g ((negGA T).symm h) w := by
  unfold actO; rw [mt_negGA_symm]

theorem actO_negS (S T : HSp D) (g : GA D (negSp S)) (h : GA D T) (w : WO S T) :
    actO (negSp S) T g h w = actO S T ((negGA S).symm g) h w := by
  unfold actO; rw [← map_inv (negGA S).symm g, mt_negGA_symm]

theorem weil_conjTarget (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T) (hw : IsWeilDatumO ψ S T χS χT om) :
    IsWeilDatumO ψ S (negSp T) χS⁻¹ χT⁻¹ (conjTarget om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thT : ∀ f : WO S (negSp T) → ℂ, IsThetaFunO ψ S (negSp T) f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).1
    rwa [cj_id_cj_id] at this
  have hzT : ∀ (w : WO S T) (f : WO S (negSp T) → ℂ),
      heisO ψ S (negSp T) w f = cj id (heisO ψ S T w (cj id f)) := fun w f => by
    have := (I.2 w (cj id f)).1
    rwa [cj_id_cj_id] at this
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [conjTarget_apply, thT, cj_id_cj_id]
    exact hw.om_pres _ _ ((thT f).1 hf)
  · intro g h w₀ f hf
    rw [conjTarget_apply, conjTarget_apply, hzT w₀ f, cj_id_cj_id, hw.om_heis _ _ _ _ ((thT f).1 hf),
      hzT _ (cj id _), cj_id_cj_id, actO_negT]
  · intro γ hγ γ' hγ' f hf
    rw [conjTarget_apply]
    show starRingEnd ℂ (om (γ, (negGA T).symm γ') (cj id f) 0) = f 0
    rw [hw.om_aut γ hγ _ (negGA_symm_mem_GQ T γ' hγ') _ ((thT f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thT f).1 hf) w
    simp only [conjTarget_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (continuous_fst.prodMk ((continuous_negGA_symm T).comp continuous_snd)))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF (p.1, (negGA T).symm p.2) (cj id f) ((thT f).1 hf)
    simp only [conjTarget_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he g ((negGA T).symm h) hg
      (by unfold SuppAt; rw [mt_negGA_symm]; exact hh) x y hx (by unfold IsDetAt; rw [mt_negGA_symm]; exact hy)
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om (g, (negGA T).symm h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ S T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← (I.2 u f').1, hℓ u hu (cj id f') ((I.1 f').1.2 hf')]) (cj id f) ((thT f).1 hf)
    rw [cj_id_cj_id, ← conjTarget_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem weil_conjSource (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T) (hw : IsWeilDatumO ψ S T χS χT om) :
    IsWeilDatumO ψ (negSp S) T χS⁻¹ χT⁻¹ (conjSource om) := by
  have I := GlobalTheory.CjNeg.theta_heis_neg D ψ hw.std S T
  have thS : ∀ f : WO (negSp S) T → ℂ, IsThetaFunO ψ (negSp S) T f ↔ IsThetaFunO ψ S T (cj id f) := fun f => by
    have := (I.1 (cj id f)).2
    rwa [cj_id_cj_id] at this
  have hzS : ∀ (w : WO S T) (f : WO (negSp S) T → ℂ),
      heisO ψ (negSp S) T w f = cj id (heisO ψ S T w (cj id f)) := fun w f => by
    have := (I.2 w (cj id f)).2
    rwa [cj_id_cj_id] at this
  refine
    { std := hw.std
      hecS := hecke_inv hw.hecS
      hecT := hecke_inv hw.hecT
      resS := resEta_inv hw.resS
      resT := resEta_inv hw.resT
      om_pres := ?_
      om_heis := ?_
      om_aut := ?_
      om_cont := ?_
      om_unit := ?_
      om_split := ?_ }
  · intro p f hf
    rw [conjSource_apply, thS, cj_id_cj_id]
    exact hw.om_pres _ _ ((thS f).1 hf)
  · intro g h w₀ f hf
    rw [conjSource_apply, conjSource_apply, hzS w₀ f, cj_id_cj_id, hw.om_heis _ _ _ _ ((thS f).1 hf),
      hzS _ (cj id _), cj_id_cj_id, actO_negS]
  · intro γ hγ γ' hγ' f hf
    rw [conjSource_apply]
    show starRingEnd ℂ (om ((negGA S).symm γ, γ') (cj id f) 0) = f 0
    rw [hw.om_aut _ (negGA_symm_mem_GQ S γ hγ) γ' hγ' _ ((thS f).1 hf)]
    show starRingEnd ℂ (starRingEnd ℂ (f 0)) = f 0
    simp
  · intro f hf w
    have hc := hw.om_cont _ ((thS f).1 hf) w
    simp only [conjSource_apply]
    exact Complex.continuous_conj.comp
      (hc.comp (((continuous_negGA_symm S).comp continuous_fst).prodMk continuous_snd))
  · intro μ 𝓕 hμ hF p f hf
    have hu := hw.om_unit μ 𝓕 hμ hF ((negGA S).symm p.1, p.2) (cj id f) ((thS f).1 hf)
    simp only [conjSource_apply, cj_id_apply, enorm_conj] at hu ⊢
    exact hu
  · intro e he g h hg hh x y hx hy
    obtain ⟨r, hr, H⟩ := hw.om_split e he ((negGA S).symm g) h
      (by unfold SuppAt; rw [mt_negGA_symm]; exact hg) hh x y (by unfold IsDetAt; rw [mt_negGA_symm]; exact hx) hy
    refine ⟨r, hr, fun ℓ hℓ f hf => ?_⟩
    let ℓ' : (WO S T → ℂ) →ₗ[ℂ] ℂ :=
      { toFun := fun f => starRingEnd ℂ (ℓ (cj id f))
        map_add' := fun a b => by
          have : cj id (a + b) = cj id a + cj id b := by funext z; simp [cj_id_apply]
          rw [this, map_add (f := _), map_add (f := _)]
        map_smul' := fun c a => by
          have : cj id (c • a) = starRingEnd ℂ c • cj id a := by funext z; simp [cj_id_apply]
          rw [this, map_smul, smul_eq_mul, map_mul, Complex.conj_conj]; rfl }
    have h1 : starRingEnd ℂ (ℓ (cj id (om ((negGA S).symm g, h) (cj id f)))) =
        (r : ℂ) * (splitFacO χS χT x y : ℂ) * starRingEnd ℂ (ℓ (cj id (cj id f))) :=
      H ℓ' (fun u hu f' hf' => by
        show starRingEnd ℂ (ℓ (cj id (heisO ψ S T u f'))) = starRingEnd ℂ (ℓ (cj id f'))
        rw [← (I.2 u f').2, hℓ u hu (cj id f') ((I.1 f').2.2 hf')]) (cj id f) ((thS f).1 hf)
    rw [cj_id_cj_id, ← conjSource_apply om (g, h) f] at h1
    rw [splitFacO_inv]
    have h2 := congrArg (starRingEnd ℂ) h1
    simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal] at h2
    exact h2

theorem conj_isWeilDatumO : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : Om S T), IsWeilDatumO ψ S T χS χT om →
      IsWeilDatumO ψ S (GlobalTheory.ChiGrid.negSp T) χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjTarget om) ∧
      IsWeilDatumO ψ (GlobalTheory.ChiGrid.negSp S) T χS⁻¹ χT⁻¹ (GlobalTheory.IndefiniteRowSideFullHecke.ConjugateAdjointDagger.conjSource om) :=
  fun D ψ S T χS χT om hw => ⟨weil_conjTarget D ψ S T χS χT om hw, weil_conjSource D ψ S T χS χT om hw⟩

end GlobalTheory.ConjWeil
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SchwartzBruhatTensorIndicatorCharacterFactsStatement
section
open GlobalTheory.FinPl GlobalTheory.LatPair GlobalTheory.SplitWeil ValuativeRel IsLocalRing Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.schwartzBruhat_tensor_indicator_character_facts : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'], (∀ (Ψ : Matrix n n' k → ℂ) (a : (n → k) → ℂ), Ψ ∈ SB (Matrix n n' k) → a ∈ SB (n → k) → GlobalTheory.FinPl.tensCol Ψ a ∈ SB (Matrix n (n' ⊕ Fin 1) k)) ∧ (∀ (Λ : Submodule 𝒪[k] (n → k)), Λ.IsFullLattice k → GlobalTheory.FinPl.vecInd Λ ∈ SB (n → k)) ∧ ∀ (χ : AddChar 𝓀[k] ℂ) (Q : Pair k n), GlobalTheory.FinPl.charInd χ Q ∈ SB (n → k) := by
  intro k _ _ _ _ n n' _ _ _ _
  refine ⟨fun Ψ a hΨ ha => GlobalTheory.FinPl.Comm.tensCol_mem hΨ ha, ?_,
    fun χ Q => GlobalTheory.FinPl.SBFacts.charInd_mem χ Q⟩
  intro Λ hΛ
  have := hΛ
  exact GlobalTheory.FinPl.Comm.vecInd_mem Λ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TransvectionIsUnitaryAdelic
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Grow
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Unf

namespace GlobalTheory.TransvAdelic

theorem transv_unitary : ∀ D : D7, GlobalTheory.IndefiniteRowSideFullHecke.TransvectionAction.TransvUnitary D :=
  fun D => (transv_unitary_conj D).1

end GlobalTheory.TransvAdelic
end

