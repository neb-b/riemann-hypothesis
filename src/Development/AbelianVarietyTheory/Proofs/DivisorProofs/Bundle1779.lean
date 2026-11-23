module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0099
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.BlockTheory.PoincareCuspForms.SmallUnipotentElements

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistCharacterOfArtin
section
set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.L2.Host GlobalTheory.HeckeGal
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp GlobalTheory.SeriesTie

namespace GlobalTheory.TwistChr

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance 10000] GlobalTheory.GalChar.isTorsionFree_field

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

theorem hecke_eq_of_frob {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {art : Ideles E →* Gab E Ω} (ha : IsGlobalArtin art) (r : G E Ω →* ℂˣ) (hr : IsOpen (r.ker : Set (G E Ω))) (χ : HChar E)
    (S : Finset (HeightOneSpectrum (𝓞 E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G E Ω, IsFrob (F := E) A (normV v) σ → r σ = (χ.val v)⁻¹)
    (x : Ideles E) (σ : G E Ω) (hx : art x = toAb E Ω σ) : χ.1 x = r σ := by
  have hc := continuous_of_isOpen_ker' r hr
  have h : (liftAb r hc).comp art * χ.1⁻¹ = 1 := by
    refine GlobalTheory.FrobDense.eq_one_of_away _ (((continuous_liftAb r hc).comp ha.quot.continuous).mul χ.2.1.inv) (fun k => ?_) S
      fun v hv => ?_
    · have hk : diagUnits E k ∈ art.ker := by
        rw [ha.ker]
        exact Subgroup.le_topologicalClosure _ (Subgroup.mem_sup_left ⟨k, rfl⟩)
      rw [MonoidHom.mul_apply, MonoidHom.inv_apply, χ.2.2, MonoidHom.comp_apply, MonoidHom.mem_ker.mp hk, map_one, inv_one, one_mul]
    · refine GlobalTheory.FrobDense.eq_one_of_unif (((liftAb r hc).comp art * χ.1⁻¹).comp (localIdele E v)) fun y hy => ?_
      obtain ⟨A, hA⟩ := exists_isPlaceOver Ω v
      obtain ⟨τ, hτ, e⟩ := (ha.frob v A hA _).mp ⟨y, hy, rfl⟩
      have h1 : χ.1 (localIdele E v y) = χ.val v := χ.val_eq (hu v hv) y hy
      rw [MonoidHom.comp_apply, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, ← e, liftAb_toAb, map_inv,
        hf v hv A hA τ hτ, inv_inv, h1, mul_inv_cancel]
  have h2 := DFunLike.congr_fun h x
  rw [MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.comp_apply, hx, liftAb_toAb, MonoidHom.one_apply, mul_inv_eq_one] at h2
  exact h2.symm

theorem chrEq_charOf {D : D7} {Ω : Type} [Field Ω] [Algebra D.host.E Ω] [IsAlgClosure D.host.E Ω] {a : Recip D Ω} (ha : a.Good)
    {R : Type} [CommRing R] (f : R →+* ℂ) (ψ : G D.host.E Ω →* Rˣ) (hψ : IsOpen (ψ.ker : Set (G D.host.E Ω))) {n : ℕ} (hn : n ≠ 0)
    (hp : ∀ σ, ψ σ ^ n = 1) (χ : HChar D.host.E) (S : Finset (HeightOneSpectrum (𝓞 D.host.E))) (hu : ∀ v ∉ S, χ.UnrAt v)
    (hf : ∀ v ∉ S, ∀ A : ValuationSubring Ω, IsPlaceOver A v → ∀ σ : G D.host.E Ω, IsFrob (F := D.host.E) A (normV v) σ →
      f (ψ σ : Rˣ) = (((χ.val v)⁻¹ : ℂˣ) : ℂ)) : ChrEq (charOf a f ψ) χ := by
  have key : ∀ x, ((charOf a f ψ x : Circle) : ℂ) = ((χ.1 (Units.map a.κ.toMonoidHom x) : ℂˣ) : ℂ) := fun x => by
    obtain ⟨σ, hσ⟩ := a.exists_sym x
    rw [charOf_eq a f hψ hσ hn (hp σ), hecke_eq_of_frob ha.artin ((Units.map f.toMonoidHom).comp ψ)
      (Subgroup.isOpen_mono (H₁ := ψ.ker) (fun g hg => by
        rw [MonoidHom.mem_ker] at hg ⊢
        rw [MonoidHom.comp_apply, hg, map_one]) hψ) χ S hu (fun v hv A hA τ hτ => Units.ext (hf v hv A hA τ hτ)) _ σ hσ]
    rfl
  refine ⟨⟨?_, fun k => ?_⟩, fun P e he k x hx => ?_⟩
  · refine continuous_induced_rng.2 ?_
    exact (Units.continuous_val.comp (χ.2.1.comp (Continuous.units_map _ ha.cont))).congr fun x => (key x).symm
  · refine Circle.ext ?_
    rw [key, show Units.map a.κ.toMonoidHom (Units.map (incA D).toMonoidHom k) = diagUnits D.host.E k from Units.ext (ha.rat k), χ.2.2]
    rfl
  · rw [key, show Units.map a.κ.toMonoidHom x = localIdele D.host.E P (atFin P k) from Units.ext (by
      change a.κ (x : AE D) = _
      rw [hx, ha.loc P e he k])]
    rfl

theorem chrEq_mul {D : D7} {c c' : (AE D)ˣ →* Circle} {χ χ' : HChar D.host.E} (h : ChrEq c χ) (h' : ChrEq c' χ') :
    ChrEq (c * c') (χ * χ') := by
  refine ⟨⟨h.1.1.mul h'.1.1, fun x => ?_⟩, fun P e he k x hx => ?_⟩
  · rw [MonoidHom.mul_apply, h.1.2, h'.1.2, one_mul]
  · rw [MonoidHom.mul_apply, Circle.coe_mul, h.2 P e he k x hx, h'.2 P e he k x hx]
    rfl

theorem finite_placesOver (E : Type) [Field E] [NumberField E] {l : ℕ} (hl : l ≠ 0) : (Formalism.BasicNotions.placesOver E l).Finite := by
  have h0 : Ideal.span {((l : ℕ) : 𝓞 E)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact_mod_cast hl
  exact (Ideal.finite_factors h0).subset fun v hv => Ideal.dvd_span_singleton.mpr hv

section Point

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ} {p : PtAt ex Csz} {w : D.what₂.places.Pl}

theorem chrEq_tw (h : RecTies p) (hw : D.what₂.muAt w ≠ D.what₂.mu0)
    (hψ : IntegralHeckeForms.TwOK (ex.nch.twI w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w))
    {ρ : Setup D.ntw} (hρ : ρ.Good) (hA : Adapted p w ρ) :
    ChrEq (ρ.tw (ex.nch.twI w) (ex.nch.sd w) (ex.nch.k' w) (ex.nch.Q w) (GlobalTheory.TwistIndex.chosenChar ex.nch w)).chi (p.Tp.psi w) := by
  classical
  obtain ⟨-, -, hopen, -, hzk, -, -⟩ := hψ
  obtain ⟨-, e, he, he'⟩ := hA
  have hl : D.ntw.l (ex.nch.twI w) ≠ 0 := (D.ntw.lPrime _).out.ne_zero
  have hz : D.ntw.zk (ex.nch.twI w) (ex.nch.k' w) ^ (D.ntw.l (ex.nch.twI w) ^ ex.nch.k' w) = 1 :=
    Units.ext (by simpa using (D.ntw.zk_prim (ex.nch.twI w) (ex.nch.k' w)).pow_eq_one)
  have hfin := finite_placesOver D.host.E (l := D.what₂.places.resChar w) (ex.nch.twI_l w ▸ hl)
  refine chrEq_charOf hρ.rc _ _ hopen (pow_ne_zero (ex.nch.k' w) hl) (fun σ => ?_) _ (ex.nch.Q w ∪ hfin.toFinset)
    (fun v hv => ((p.Tp.psi_is w hw).ram v).2 fun hQ => hv (Finset.mem_union_left _ hQ)) fun v hv A hA σ hσ => ?_
  · obtain ⟨m, hm⟩ := hzk σ
    rw [← hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz, one_zpow]
  · obtain ⟨y, hy, hy'⟩ := h.psi_read w hw v (fun hQ => hv (Finset.mem_union_left _ hQ))
      (fun hQ => hv (Finset.mem_union_right _ (hfin.mem_toFinset.2 hQ))) A σ hA hσ
    rw [← he', ← hy', he, hy]

theorem xi_eq (hw : D.what₂.muAt w ≠ D.what₂.mu0) {ρ : Setup D.ntw} (hP : RealPin p.R p.cG ρ) (j : Fin D.R.m) (b : Bool)
    {c : (AE D)ˣ →* Circle} (hc : ChrEq c (p.Tp.psi w)) :
    p.R.xi (p.R.mu (D.plEq w)) = (ρ.B (ex.nch.twI w) j b).de.chi * c := by
  have h1 := p.charW.base.lev.xi (p.R.mu (D.plEq w))
  have h2 : p.R.toRealDat.toLevCh.xiH (p.R.mu (D.plEq w)) = p.R.C.delAt (D.ntw.l (ex.nch.twI w)) * p.Tp.psi w := by
    rw [← p.tupAt w, p.tupXi _ (Or.inr ⟨w, rfl⟩), (D.what₂.muAt_or w).resolve_left hw, p.Tp.xi_tw, ex.nch.twI_l]
  exact GlobalTheory.ChrEqUnique.idc_unique D _ _ _ h1 (h2 ▸ chrEq_mul (hP.delta _ j b) hc)

end Point

end GlobalTheory.TwistChr

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoBinomialRatioBounds
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

namespace GlobalTheory.BinomRatio
open Finset

theorem fact_mul_choose_eq_prod (T a n : ℕ) :
    ((n.factorial : ℕ) : ℝ) * (((T + a + n).choose n : ℕ) : ℝ)
      = ∏ i ∈ range n, ((T : ℝ) + a + 1 + i) := by
  have h := Nat.ascFactorial_eq_factorial_mul_choose (T + a) n
  rw [Nat.ascFactorial_eq_prod_range] at h
  have h2 : ((∏ i ∈ range n, (T + a + 1 + i) : ℕ) : ℝ) = ((n.factorial * (T + a + n).choose n : ℕ) : ℝ) := by
    rw [h]
  push_cast at h2
  rw [← h2]

theorem prod_upper (T a n : ℕ) :
    ∏ i ∈ range n, ((T : ℝ) + a + 1 + i)
      ≤ (1 + (a : ℝ) / (T + 1)) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hc : (1 + (a : ℝ) / (T + 1)) ^ n = ∏ _i ∈ range n, (1 + (a : ℝ) / (T + 1)) := by simp
  rw [hc, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _; positivity
  · intro i _
    have hT : (0 : ℝ) < T + 1 := by positivity
    have hi : (0 : ℝ) ≤ i := by positivity
    have ha : (0 : ℝ) ≤ a := by positivity
    have e : (1 + (a : ℝ) / (T + 1)) * ((T : ℝ) + 0 + 1 + i) = (T + 1 + i) + a + a * i / (T + 1) := by
      field_simp; ring
    rw [e]
    have : 0 ≤ (a : ℝ) * i / (T + 1) := by positivity
    linarith

theorem prod_lower (T c n : ℕ) (hc : (c : ℝ) ≤ T) (hT : 0 < T) :
    (1 - (c : ℝ) / T) ^ n * ∏ i ∈ range n, ((T : ℝ) + c + 1 + i)
      ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
  have hT' : (0 : ℝ) < T := by exact_mod_cast hT
  have hcp : (1 - (c : ℝ) / T) ^ n = ∏ _i ∈ range n, (1 - (c : ℝ) / T) := by simp
  rw [hcp, ← prod_mul_distrib]
  apply prod_le_prod₀
  · intro i _
    have : (0 : ℝ) ≤ 1 - c / T := by rw [sub_nonneg, div_le_one hT']; exact hc
    positivity
  · intro i _
    have hi : (0 : ℝ) ≤ i := by positivity
    have hc0 : (0 : ℝ) ≤ c := by positivity
    have e : (1 - (c : ℝ) / T) * ((T : ℝ) + c + 1 + i) = (T + 1 + i) - (c * c + c * (1 + i)) / T := by
      field_simp; ring
    rw [e]
    have : 0 ≤ ((c : ℝ) * c + c * (1 + i)) / T := by positivity
    linarith

end GlobalTheory.BinomRatio

namespace GlobalTheory.BinomRatio
open Finset

theorem first_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n := by
  have e1 : T + 3 * n + 10 = T + (2 * n + 10) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hA := fact_mul_choose_eq_prod T (2 * n + 10) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hU := prod_upper T (2 * n + 10) n
  set x : ℝ := ((2 * n + 10 : ℕ) : ℝ) / (T + 1) with hx
  have hT1 : (0 : ℝ) < T + 1 := by positivity
  have hx0 : 0 ≤ x := by positivity
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hnx : (n : ℝ) * x ≤ 0.65 := by
    rw [hx, mul_div_assoc', div_le_iff₀ hT1]
    push_cast
    nlinarith
  have hpow : (1 + x) ^ n ≤ 2 := by
    calc (1 + x) ^ n ≤ (Real.exp x) ^ n := by
          apply pow_le_pow_left₀ (by positivity)
          have := Real.add_one_le_exp x; linarith
      _ = Real.exp (n * x) := by rw [← Real.exp_nat_mul]
      _ ≤ Real.exp (Real.log 2) := by
          apply Real.exp_le_exp.mpr
          have := Real.log_two_gt_d9; linarith
      _ = 2 := Real.exp_log (by norm_num)
  have hP : 0 ≤ ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := by
    apply prod_nonneg; intro i _; positivity
  have key : ((n.factorial : ℕ) : ℝ) * (((T + (2 * n + 10) + n).choose n : ℕ) : ℝ)
      ≤ ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hA]
    calc ∏ i ∈ range n, ((T : ℝ) + ((2 * n + 10 : ℕ) : ℝ) + 1 + i)
        ≤ (1 + x) ^ n * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := hU
      _ ≤ 2 * ∏ i ∈ range n, ((T : ℝ) + 0 + 1 + i) := mul_le_mul_of_nonneg_right hpow hP
      _ = ((n.factorial : ℕ) : ℝ) * ((2 * (T + 0 + n).choose n : ℕ) : ℝ) := by
          push_cast at hB ⊢
          rw [← hB]; ring
  have := le_of_mul_le_mul_left key hf
  exact_mod_cast this

theorem second_ratio (T n : ℕ) (hn : 2 ≤ n) (hT : 11 * n ^ 2 ≤ T) :
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) := by
  have e1 : T + 2 * n + 6 = T + (n + 6) + n := by ring
  have e2 : T + n = T + 0 + n := by ring
  rw [e1, e2]
  have hf : (0 : ℝ) < ((n.factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hTR : (11 : ℝ) * n ^ 2 ≤ T := by exact_mod_cast hT
  have hT0 : 0 < T := by nlinarith
  have hTR0 : (0 : ℝ) < T := by exact_mod_cast hT0
  have hc : (((n + 6 : ℕ)) : ℝ) ≤ T := by push_cast; nlinarith
  have hA := fact_mul_choose_eq_prod T (n + 6) n
  have hB := fact_mul_choose_eq_prod T 0 n
  have hL := prod_lower T (n + 6) n hc hT0
  have hbern : 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) ≤ (1 + -((((n + 6 : ℕ)) : ℝ)) / T) ^ n := by
    apply one_add_mul_le_pow
    rw [neg_div, neg_le_neg_iff, div_le_iff₀ hTR0]
    linarith
  have hC : (0 : ℝ) ≤ (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by positivity
  have step : (1 - (n : ℝ) * (n + 6) / T) * (((T + (n + 6) + n).choose n : ℕ) : ℝ)
      ≤ (1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ) := by
    apply mul_le_mul_of_nonneg_right _ hC
    have h1 : (1 : ℝ) - (n : ℝ) * (n + 6) / T = 1 + (n : ℝ) * (-((((n + 6 : ℕ)) : ℝ)) / T) := by
      push_cast; ring
    have h2 : (1 : ℝ) - (((n + 6 : ℕ)) : ℝ) / T = 1 + -((((n + 6 : ℕ)) : ℝ)) / T := by ring
    rw [h1, h2]; exact hbern
  have key : ((n.factorial : ℕ) : ℝ) * ((1 - (((n + 6 : ℕ)) : ℝ) / T) ^ n * (((T + (n + 6) + n).choose n : ℕ) : ℝ))
      ≤ ((n.factorial : ℕ) : ℝ) * (((T + 0 + n).choose n : ℕ) : ℝ) := by
    rw [hB, mul_left_comm, hA]
    simpa only [Nat.cast_zero] using hL
  have := le_of_mul_le_mul_left key hf
  linarith

theorem two_binom_ratios : ∀ T n : ℕ, 2 ≤ n → 11 * n ^ 2 ≤ T →
    (T + 3 * n + 10).choose n ≤ 2 * (T + n).choose n ∧
    (1 - (n : ℝ) * (n + 6) / T) * ((T + 2 * n + 6).choose n : ℕ) ≤ ((T + n).choose n : ℕ) :=
  fun T n hn hT => ⟨first_ratio T n hn hT, second_ratio T n hn hT⟩

end GlobalTheory.BinomRatio
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsDirectSumComponents
section
open NumberField Module ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds GlobalTheory.ShareOn

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

def onComp (M : TwoLevels E r U C) (c : C) : Submodule ℂ (C → M.dom → ℂ) where
  carrier := {v | ∀ c', c' ≠ c → v c' = 0}
  add_mem' := by
    intro a b ha hb c' hc
    simp [ha c' hc, hb c' hc]
  zero_mem' := by
    intro c' _
    rfl
  smul_mem' := by
    intro t a ha c' hc
    simp [ha c' hc]

def cut (M : TwoLevels E r U C) (c : C) : (C → M.dom → ℂ) →ₗ[ℂ] (C → M.dom → ℂ) where
  toFun v := fun c' => if c' = c then v c' else 0
  map_add' := by
    intro a b
    funext c' x
    by_cases h : c' = c <;> simp [h]
  map_smul' := by
    intro t a
    funext c' x
    by_cases h : c' = c <;> simp [h]

theorem cut_apply (M : TwoLevels E r U C) (c : C) (v : C → M.dom → ℂ) (c' : C) :
    cut M c v c' = if c' = c then v c' else 0 := rfl

theorem cutF_mem_SS (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {F : C → Frame M.Ψ r → ℂ}
    (hF : F ∈ M.SS la) : (fun c' => if c' = c then F c' else 0) ∈ M.SS la := by
  intro c'
  by_cases h : c' = c
  · simpa [h] using hF c'
  · simp only [h, if_false]
    exact ⟨BoundedSectionAlgebra.bdd_zero _ _, fun ξ _ x _ => BoundedSectionAlgebra.fj_zero _ _ ξ x 0⟩

theorem cut_mem_cusp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) : cut M c v ∈ M.cusp la := by
  have : (M.cusp la).map (cut M c) ≤ M.cusp la := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, cutF_mem_SS M la c hF, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

theorem mem_span_of_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (c : C) {v : C → M.dom → ℂ}
    (hv : v ∈ M.cusp la) (hc : v ∈ onComp M c) :
    v ∈ Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
  have hcut : cut M c v = v := by
    funext c' x
    by_cases h : c' = c
    · simp [cut_apply, h]
    · simp [cut_apply, h, hc c' h]
  rw [← hcut]
  have : (M.cusp la).map (cut M c) ≤
      Submodule.span ℂ (M.res '' {F | F ∈ M.SS la ∧ ∀ c', c' ≠ c → F c' = 0}) := by
    unfold TwoLevels.cusp
    rw [Submodule.map_span, Submodule.span_le]
    rintro _ ⟨_, ⟨F, hF, rfl⟩, rfl⟩
    refine Submodule.subset_span ⟨_, ⟨cutF_mem_SS M la c hF, fun c' hc' => by simp [hc']⟩, ?_⟩
    funext c' x
    simp [TwoLevels.res, cut_apply]
    split_ifs <;> rfl
  exact this ⟨v, hv, rfl⟩

end GlobalTheory.ShareOn.Decomp

end

namespace GlobalTheory.ShareOn.Decomp

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [MulAction U C]
  [DecidableEq C]

theorem pullRep_onComp (M : TwoLevels E r U C) (la : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp la))
    (hρ : IsPullRep M la ρ) (g : U) (c : C) (w : M.cusp la) (hw : (w : C → M.dom → ℂ) ∈ onComp M c) :
    ((ρ g⁻¹ w : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) := by
  obtain ⟨a, ha⟩ := hρ
  obtain ⟨w, hwc⟩ := w
  have hs := mem_span_of_onComp M la c hwc hw
  clear hw
  revert hwc
  suffices H : ∀ h' : w ∈ M.cusp la, ((ρ g⁻¹ ⟨w, h'⟩ : M.cusp la) : C → M.dom → ℂ) ∈ onComp M (g⁻¹ • c) from fun h' => H h'
  induction hs using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨F, ⟨hF, hFc⟩, rfl⟩ := hy
    intro h' c' hc'
    funext x
    have hgc : g • c' ≠ c := fun h => hc' (eq_inv_smul_iff.2 h)
    have := ha g F hF c' x
    rw [this]
    simp [TwoLevels.pull, hFc _ hgc]
  | zero =>
    intro h'
    have : (⟨0, h'⟩ : M.cusp la) = 0 := rfl
    rw [this, map_zero]
    exact (onComp M (g⁻¹ • c)).zero_mem
  | add x y hx hy ihx ihy =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have hy' : y ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hy
    have : (⟨x + y, h'⟩ : M.cusp la) = ⟨x, hx'⟩ + ⟨y, hy'⟩ := rfl
    rw [this, map_add (f := _), Submodule.coe_add]
    exact (onComp M (g⁻¹ • c)).add_mem (ihx hx') (ihy hy')
  | smul t x hx ihx =>
    intro h'
    have hx' : x ∈ M.cusp la := (Submodule.span_le.2 (by
      rintro _ ⟨F, ⟨hF, -⟩, rfl⟩; exact Submodule.subset_span ⟨F, hF, rfl⟩)) hx
    have : (⟨t • x, h'⟩ : M.cusp la) = t • ⟨x, hx'⟩ := rfl
    rw [this, map_smul, Submodule.coe_smul]
    exact (onComp M (g⁻¹ • c)).smul_mem t (ihx hx')

end GlobalTheory.ShareOn.Decomp


open GlobalTheory.ShareOn.Decomp in
theorem GlobalTheory.ShareOn.cusp_decomp : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (U C : Type) [Group U] [Finite C]
    [DecidableEq C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)),
    IsPullRep M ka ρ → ∃ A : C → Submodule ℂ (M.cusp ka), DirectSum.IsInternal A ∧
      ∀ (h : U) (c : C), ∀ v ∈ A c, ρ h v ∈ A (h • c) := by
  intro E _ _ _ r U C _ _ _ _ M ka ρ hρ
  have : Fintype C := Fintype.ofFinite C
  refine ⟨fun c => (onComp M c).comap (M.cusp ka).subtype, ?_, ?_⟩
  · apply DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
    · rw [iSupIndep_def]
      intro i
      rw [Submodule.disjoint_def]
      intro x hx hx2
      have hle : (⨆ j, ⨆ (_ : j ≠ i), (onComp M j).comap (M.cusp ka).subtype) ≤
          LinearMap.ker ((LinearMap.proj i : (C → M.dom → ℂ) →ₗ[ℂ] (M.dom → ℂ)) ∘ₗ (M.cusp ka).subtype) := by
        refine iSup₂_le fun j hj => ?_
        intro y hy
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype]
        exact hy i (Ne.symm hj)
      have h0 := hle hx2
      simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj,
          Function.eval, Submodule.coe_subtype] at h0
      apply Subtype.ext
      funext c'
      by_cases h : c' = i
      · subst h; simpa using h0
      · simpa using hx c' h
    · rw [eq_top_iff]
      rintro ⟨v, hv⟩ -
      have hsum : (⟨v, hv⟩ : M.cusp ka) = ∑ c, ⟨GlobalTheory.ShareOn.Decomp.cut M c v, cut_mem_cusp M ka c hv⟩ := by
        apply Subtype.ext
        rw [Submodule.coe_sum]
        funext c' x
        simp only [Finset.sum_apply, GlobalTheory.ShareOn.Decomp.cut_apply]
        have hh : ∀ c, (if c' = c then v c' else 0) x = if c' = c then v c' x else 0 := fun c => by
          split_ifs <;> rfl
        simp only [hh]
        rw [Finset.sum_ite_eq]
        simp
      rw [hsum]
      refine Submodule.sum_mem_iSup fun c => ?_
      intro c' hc'
      simp [GlobalTheory.ShareOn.Decomp.cut_apply, hc']
  · intro h c v hv
    have := pullRep_onComp M ka ρ hρ h⁻¹ c v hv
    simp only [inv_inv] at this
    exact this
end

