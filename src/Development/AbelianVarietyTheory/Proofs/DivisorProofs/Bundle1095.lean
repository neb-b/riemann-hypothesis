module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0024
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsFinWeil
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0879
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1083
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0070
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0964
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0956
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0929
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1060
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1072
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DefiniteUnitaryClassSetFinite
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.EquivSigLamOfIsDS
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Arbitrary
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0010
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0009
public import ReciprocityTheory.ReductiveGroups.DiscreteSeries.DiscreteSeriesExistence.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousProduct
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum GlobalTheory.WeilParts MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct Topology
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.WeilProduct

open GlobalTheory.FinWeilO GlobalTheory.FinWeil GlobalTheory.SplitScalar

variable {D : D7} {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
  {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
  {χS χT : (AE D)ˣ →* Circle} {of oi : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)}

theorem actO_mul (g g' : GA D S) (h h' : GA D T) (u : WO S T) :
    actO S T (g * g') (h * h') u = actO S T g h (actO S T g' h' u) := by
  unfold actO
  rw [_root_.mul_inv_rev, mt_mul, mt_mul]
  simp only [Matrix.mul_assoc]

theorem actO_one (u : WO S T) : actO S T 1 1 u = u := by
  unfold actO
  rw [inv_one, mt_one, mt_one, Matrix.one_mul, Matrix.mul_one]

theorem exists_parts (p : GA D S × GA D T) : ∃ a ∈ GinfC S, ∃ b ∈ GinfC T, ∃ k ∈ GfC S, ∃ l ∈ GfC T,
    p = (a, b) * (k, l) ∧ p = (k, l) * (a, b) := by
  obtain ⟨a, ha, k, hk, e1⟩ := (GlobalTheory.UnitarySplit.real_finite_split D S).1 p.1
  obtain ⟨b, hb, l, hl, e2⟩ := (GlobalTheory.UnitarySplit.real_finite_split D T).1 p.2
  refine ⟨a, ha, b, hb, k, hk, l, hl, Prod.ext e1 e2, Prod.ext ?_ ?_⟩
  · exact e1.trans ((GlobalTheory.UnitarySplit.real_finite_split D S).2.1 a ha k hk)
  · exact e2.trans ((GlobalTheory.UnitarySplit.real_finite_split D T).2.1 b hb l hl)

theorem fin_eq_smul (hψ : IsStdChar D ψ (-1)) (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {w : 𝓞 D.host.E} {lam : ℕ →* ℂ}
    (hlam : GlobalTheory.FinWeil.GoodNorm (sgO D) lam) {Om : GA D S × GA D T →* Module.End ℂ (thetaSub ψ S T)}
    (h : IsLatRep hψ.1 ΛS ΛT w lam Om) (p : GA D S × GA D T) :
    ∃ c : ℂ, ∀ f : thetaSub ψ S T, of p f = c • (Om p f : WO S T → ℂ) := by
  obtain ⟨a, ha, b, hb, k, hk, l, hl, -, rfl⟩ := exists_parts p
  obtain ⟨om, hom⟩ := exists_extend (thetaSub ψ S T) Om
  have ho : ∀ p f (hf : IsThetaFunO ψ S T f), om p f = (Om p ⟨f, hf⟩ : WO S T → ℂ) := fun p f hf => hom p ⟨f, hf⟩
  obtain ⟨c, -, hc⟩ := _root_.GlobalTheory.ThetaSchur.schur D ψ hψ S T (of (k, l) * om (k⁻¹, l⁻¹))
    (fun f h1 => by
      rw [Module.End.mul_apply, ho _ f h1]
      exact hf.pres _ _ (Om _ ⟨f, h1⟩).2)
    (fun u f h1 => by
      obtain ⟨f', e1, e2⟩ := h.Heisenberg₂ hψ (inv_mem hk) (inv_mem hl) u ⟨f, h1⟩
      have e1' : (f' : WO S T → ℂ) = heisO ψ S T u f := e1
      rw [Module.End.mul_apply, Module.End.mul_apply, ← e1', hom, e2, hf.Heisenberg₂ k hk l hl _ _ (Om _ ⟨f, h1⟩).2,
        ← actO_mul, mul_inv_cancel, mul_inv_cancel, actO_one, ho _ f h1])
    (fun μ 𝓕 hμ h𝓕 f h1 => by
      rw [Module.End.mul_apply, ho _ f h1, hf.unit μ 𝓕 hμ h𝓕 _ _ (Om _ ⟨f, h1⟩).2]
      exact h.unit hlam μ 𝓕 hμ h𝓕 _ ⟨f, h1⟩)
  refine ⟨c, fun f => ?_⟩
  have e := hc _ (Om (k, l) f).2
  rw [Module.End.mul_apply, hom, ← Module.End.mul_apply, ← map_mul,
    show ((k⁻¹, l⁻¹) : GA D S × GA D T) * (k, l) = 1 from inv_mul_cancel ((k, l) : GA D S × GA D T), map_one,
    Module.End.one_apply] at e
  rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, hf.triv a ha b hb _ f.2, h.real_triv ha hb, e]

theorem fin_inf_comm (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) (p q : GA D S × GA D T) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) : of p (oi q f) = oi q (of p f) := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  obtain ⟨a, ha, b, hb, k, hk, l, hl, rfl, -⟩ := exists_parts q
  let L : thetaSub ψ S T →ₗ[ℂ] thetaSub ψ S T := (oi (a, b)).restrict fun g hg => hi.pres _ g hg
  have hL : ∀ m, (L m : WO S T → ℂ) = oi (a, b) m := fun _ => rfl
  have e := congrArg Subtype.val (h.comm L (fun x v => Subtype.ext (by
    have e1 := congrArg XF.val (rhoF_real ha hb x)
    rw [coe_rhoF] at e1
    rw [hL, coe_opF, coe_opF, hL, map_smul, hi.Heisenberg₂ a ha b hb _ _ v.2, e1])) p ⟨f, h1⟩)
  rw [map_mul, Module.End.mul_apply, Module.End.mul_apply, hi.triv k hk l hl _ h1,
    hi.triv k hk l hl _ (hf.pres _ _ h1), hc ⟨f, h1⟩, map_smul, ← hL, ← e, ← hc]
  rfl

theorem eventually_smul (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) {f : WO S T → ℂ} (h1 : IsThetaFunO ψ S T f) :
    ∀ᶠ p in 𝓝 (1 : GA D S × GA D T), ∃ c : ℂ, of p f = c • f := by
  obtain ⟨lam, hlam, -⟩ := GlobalTheory.FinWeil.exists_goodNorm D
  obtain ⟨w, Om, h⟩ := exists_isLatRep hψ hS hT hlam
  filter_upwards [h.eventually_fix hS hT ⟨f, h1⟩] with p hp
  obtain ⟨c, hc⟩ := fin_eq_smul hψ hf hlam h p
  exact ⟨c, by rw [hc ⟨f, h1⟩, hp]⟩

theorem continuous_product (hψ : IsStdChar D ψ (-1)) (hS : IsSelfDualC S ΛS) (hT : IsSelfDualC T ΛT)
    (hf : IsFinWeil ψ S T ΛS ΛT χS χT of) (hi : IsInfWeil ψ θ S T oi) {f : WO S T → ℂ}
    (h1 : IsThetaFunO ψ S T f) (u : WO S T) : Continuous fun p : GA D S × GA D T => of p (oi p f) u := by
  haveI : IsTopologicalGroup (GA D S) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig S.gram))
  haveI : IsTopologicalGroup (GA D T) := inferInstanceAs (IsTopologicalGroup (HR (AF D.host.F) D.sp.cm.sig T.gram))
  refine continuous_iff_continuousAt.2 fun q => ?_
  have h2 : Filter.Tendsto (fun p => p * q⁻¹) (𝓝 q) (𝓝 1) :=
    (continuous_id.mul continuous_const).tendsto' q 1 (mul_inv_cancel q)
  have h3 := hf.pres q f h1
  have h4 : ∀ᶠ p in 𝓝 q, ∃ c : ℂ, of p f = c • of q f := by
    filter_upwards [h2.eventually (eventually_smul hψ hS hT hf h3)] with p hp
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right] at hp
  by_cases h0 : of q f = 0
  · refine continuousAt_const.congr (f := fun _ => (0 : ℂ)) ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, h0, smul_zero, map_zero]
    rfl
  · obtain ⟨x, hx⟩ := Function.ne_iff.1 h0
    have hx' : of q f x ≠ 0 := hx
    refine (((hf.cont f h1 x).div_const (of q f x)).mul (hi.cont _ h3 u)).continuousAt.congr ?_
    filter_upwards [h4] with p hp
    obtain ⟨c, hc⟩ := hp
    show of p f x / of q f x * oi p (of q f) u = _
    rw [fin_inf_comm hψ hS hT hf hi p p h1, hc, map_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul,
      mul_div_cancel_right₀ _ hx']

end GlobalTheory.WeilProduct

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteFormStabilizerFiniteAwayFromP
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.DefStab

variable {p : ℕ} [Fact p.Prime]

theorem psi_bound (G : HTGroup p) (B : GlobalTheory.LKDef.DForm G) : ∃ K : ℝ, ∀ y : GlobalTheory.LKCx.grp G B.β,
    ∀ (w : InfinitePlace G.F) (a b : Fin G.n), ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
      K * Real.sqrt ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) := by
  let f : InfinitePlace G.F → (Fin G.n → ℂ) → ℝ := fun w x =>
    if sigPosH (G.gram_herm w) = 1 then (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
    else -(star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re
  have hK : ∀ w, ∃ K : ℝ, ∀ (A : Matrix (Fin G.n) (Fin G.n) ℂ) (s : ℝ), 0 ≤ s →
      (∀ x, f w (A *ᵥ x) = s * f w x) → ∀ a b, ‖A a b‖ ≤ K * Real.sqrt s := by
    intro w
    apply GlobalTheory.LKCx.PsiBound.bound_of_form
    · by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; fun_prop
      · simp only [f, h, if_false]; fun_prop
    · intro t x
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]
      · simp only [f, h, if_false]; rw [GlobalTheory.LKCx.PsiBound.form_smul, Complex.re_ofReal_mul]; ring
    · intro x hx
      have hp := B.posR w x hx
      by_cases h : sigPosH (G.gram_herm w) = 1
      · simp only [f, h, if_true]; exact hp.1 h
      · have h2 : (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x).re < 0 := hp.2 h
        simp only [f, h, if_false]; linarith
  choose K hK using hK
  refine ⟨∑ w, |K w|, fun y w a b => ?_⟩
  set s : ℝ := ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) with hs
  have hs0 : 0 < s := by rw [hs]; exact_mod_cast y.2.2
  set A := G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) with hA
  have hsim : ∀ x : Fin G.n → ℂ, star (A *ᵥ x) ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ (A *ᵥ x) =
      (s : ℂ) * (star x ⬝ᵥ GlobalTheory.LKCx.herm G w B.β *ᵥ x) := by
    intro x
    have h := GlobalTheory.LKCx.grp_similitude_herm p G w B.β y
    have h' : Aᴴ * GlobalTheory.LKCx.herm G w B.β * A =
        (((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ)) : ℂ) • GlobalTheory.LKCx.herm G w B.β := h
    rw [← GlobalTheory.LKCx.PsiBound.form_conj, h', smul_mulVec, dotProduct_smul, smul_eq_mul, hs, Complex.ofReal_ratCast]
  have hinv : ∀ x, f w (A *ᵥ x) = s * f w x := by
    intro x
    by_cases h : sigPosH (G.gram_herm w) = 1
    · simp only [f, h, if_true]; rw [hsim, Complex.re_ofReal_mul]
    · simp only [f, h, if_false]; rw [hsim, Complex.re_ofReal_mul]; ring
  calc ‖A a b‖ ≤ K w * Real.sqrt s := hK w A s hs0.le hinv a b
    _ ≤ |K w| * Real.sqrt s := mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _)
    _ ≤ (∑ u, |K u|) * Real.sqrt s := mul_le_mul_of_nonneg_right
        (Finset.single_le_sum (f := fun u => |K u|) (fun u _ => abs_nonneg _) (Finset.mem_univ w))
        (Real.sqrt_nonneg _)

theorem isTest_indicator_comm (G : HTGroup p) (K' : Subgroup (Gr G 1))
    (hK : Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw)) :
    IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' (Set.indicator (K' : Set (Gr G 1)) 1) := by
  have hθ : ∀ g, sigG G 1 g = g := GlobalTheory.LKCx.sigG_one G
  refine ⟨hK, ?_, fun k hk g => ?_, ?_⟩
  · rintro _ ⟨k, hk, rfl⟩; rw [hθ]; exact hk
  · rw [hθ]
    by_cases hg : g ∈ K'
    · have h' : k⁻¹ * g * k ∈ K' := K'.mul_mem (K'.mul_mem (K'.inv_mem hk) hg) hk
      simp [Set.indicator_apply, hg, h']
    · have h' : k⁻¹ * g * k ∉ K' := fun h => hg (by
        have e : g = k * (k⁻¹ * g * k) * k⁻¹ := by group
        rw [e]; exact K'.mul_mem (K'.mul_mem hk h) (K'.inv_mem hk))
      simp [Set.indicator_apply, hg, h']
  · set K₀ := KHT p G.m G.n 1 G.Fw
    haveI : (K₀.subgroupOf K').FiniteIndex := Subgroup.isFiniteRelIndex_iff_finiteIndex.mp hK.2
    haveI : Finite (K' ⧸ K₀.subgroupOf K') := Subgroup.finite_quotient_of_finiteIndex
    haveI : Fintype (K' ⧸ K₀.subgroupOf K') := Fintype.ofFinite _
    refine ⟨Finset.univ.image fun q : K' ⧸ K₀.subgroupOf K' => ((Quotient.out q : K') : Gr G 1), fun g hg => ?_⟩
    have hgK : g ∈ K' := by
      by_contra hn; exact hg (by simp [Set.indicator_apply, hn])
    set q : K' ⧸ K₀.subgroupOf K' := QuotientGroup.mk ⟨g, hgK⟩
    have hq : (Quotient.out q)⁻¹ * (⟨g, hgK⟩ : K') ∈ K₀.subgroupOf K' := by
      rw [← QuotientGroup.eq, QuotientGroup.out_eq']
    rw [Subgroup.mem_subgroupOf] at hq
    refine ⟨((Quotient.out q : K') : Gr G 1), Finset.mem_image_of_mem _ (Finset.mem_univ _), 1, K₀.one_mem, _, hq,
      ?_⟩
    simp

theorem finite_locPart : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p), G.a = 1 → ∀ (L : G.Level) (K' : Subgroup (Gr G 1)),
    Subgroup.Commensurable K' (KHT p G.m G.n 1 G.Fw) → ∀ (B : GlobalTheory.LKDef.DForm G) (x : G.GAf × Gr G 1),
    Finite (GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x) := by
  intro p _ G _ L K' hK B x
  have hp : p.Prime := Fact.out
  obtain ⟨xx, tt, hx, heq⟩ : ∃ (xx : (AfP p ⊗[ℚ] G.C)ˣ) (tt : (AfP p)ˣ) (hx : Triv G (AfP p) B.β xx tt),
      B.emb = B.embAt xx tt hx := ⟨_, _, B.trivAf.choose_spec.choose_spec, rfl⟩
  set fK : G.GAf → ℂ := Set.indicator (L.K.toSubgroup : Set G.GAf) 1 with hfK
  set fK' : Gr G 1 → ℂ := Set.indicator (K' : Set (Gr G 1)) 1 with hfK'
  have hf : IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup fK := isTest_indicator _ _ (by simp)
  have hf' : IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' fK' := isTest_indicator_comm G K' hK
  set S : Set (GlobalTheory.LKCx.grp G B.β) := {y | fK (x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1) ≠ 0 ∧
    fK' (x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2) ≠ 0} with hS
  have hSfin : S.Finite := by
    obtain ⟨D, hD, hAf⟩ := GlobalTheory.LKCx.BoundedDen.main p G B.β xx tt hx L fK hf x.1
    obtain ⟨k, hP⟩ := GlobalTheory.AtP.main p G B.β K' fK' hf' x.2
    obtain ⟨R, hR⟩ := GlobalTheory.CoordArch.coord_bound p G
    obtain ⟨Kb, hKb⟩ := psi_bound G B
    obtain ⟨N, hNdef⟩ : ∃ N : ℕ, N = D * p ^ k := ⟨_, rfl⟩
    have hN : 0 < N := hNdef ▸ Nat.mul_pos hD (pow_pos hp.pos k)
    obtain ⟨R', hR'⟩ : ∃ R' : ℝ,
        R' = |R| * (Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N)) := ⟨_, rfl⟩
    let φ : GlobalTheory.LKCx.grp G B.β → (Fin (Module.finrank ℚ G.C) → ℚ) :=
      fun y => (Module.finBasis ℚ G.C).repr (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C)
    have hφ : Function.Injective φ := fun y y' h =>
      GlobalTheory.FinFix.grp_val_injective G B.β ((Module.finBasis ℚ G.C).repr.injective (Finsupp.ext fun i => congrFun h i))
    refine Set.Finite.subset
      (Set.Finite.preimage hφ.injOn (Set.Finite.pi fun _ => GlobalTheory.FinFix.finite_den_bdd N hN R')) ?_
    rintro y ⟨hf1, hf2⟩
    have hs : (0 : ℚ) < (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) := y.2.2
    obtain ⟨m, hm⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD ((((y : G.Cˣ × ℚˣ).2)⁻¹ : ℚˣ) : ℚ)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).2) (hP y hf2).2
    have hsN : ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) : ℝ) ≤ N := by
      have hm' : ((N : ℚ)) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ = m := by
        rw [hNdef, ← hm, Units.val_inv_eq_inv_val]
      have hmpos : (0 : ℚ) < m := by
        rw [← hm']; exact mul_pos (by exact_mod_cast hN) (inv_pos.2 hs)
      have hm1 : (1 : ℚ) ≤ m := by exact_mod_cast (show (0 : ℤ) < m by exact_mod_cast hmpos)
      have h2 : (1 : ℚ) ≤ (N : ℚ) * ((((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ))⁻¹ := hm' ▸ hm1
      have h3 : (((y : G.Cˣ × ℚˣ).2 : ℚˣ) : ℚ) ≤ N := by
        have := mul_le_mul_of_nonneg_right h2 hs.le
        rwa [one_mul, mul_assoc, inv_mul_cancel₀ hs.ne', mul_one] at this
      exact_mod_cast h3
    intro i _
    obtain ⟨m2, hm2⟩ := GlobalTheory.FinFix.exists_int_of_den_le (p := p) D k hD (φ y i)
      (fun ℓ hℓ => (hAf y hf1 ℓ hℓ).1 i) ((hP y hf2).1 i)
    refine ⟨⟨m2, ?_⟩, ?_⟩
    · rw [hNdef, mul_comm]; exact hm2
    · show |((φ y i : ℚ) : ℝ)| ≤ R'
      refine (hR _ i).trans ?_
      have hb : ∀ w a b, ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤ max Kb 0 * Real.sqrt N := by
        intro w a b
        exact (hKb y w a b).trans
          (mul_le_mul (le_max_left _ _) (Real.sqrt_le_sqrt hsN) (Real.sqrt_nonneg _) (le_max_right _ _))
      have hsum : ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ ≤
          Fintype.card (InfinitePlace G.F) * G.n * G.n * (max Kb 0 * Real.sqrt N) := by
        calc _ ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n, max Kb 0 * Real.sqrt N :=
              Finset.sum_le_sum fun w _ => Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ => hb w a b
          _ = _ := by simp [Finset.sum_const, Finset.card_univ]; ring
      have hnn : 0 ≤ ∑ w : InfinitePlace G.F, ∑ a : Fin G.n, ∑ b : Fin G.n,
          ‖G.psi w (((y : G.Cˣ × ℚˣ).1 : G.Cˣ) : G.C) a b‖ := by positivity
      rw [hR']
      calc R * _ ≤ |R| * _ := mul_le_mul_of_nonneg_right (le_abs_self R) hnn
        _ ≤ _ := mul_le_mul_of_nonneg_left hsum (abs_nonneg R)
  have hsub : ((GlobalTheory.LKLoc.locPart B.emb.range (L.K.toSubgroup.prod K') x : Subgroup (G.GAf × Gr G 1)) :
      Set (G.GAf × Gr G 1)) ⊆ B.emb '' S := by
    intro e he
    rw [SetLike.mem_coe, GlobalTheory.LKLoc.locPart, Subgroup.mem_inf, MonoidHom.mem_range, Subgroup.mem_map] at he
    obtain ⟨⟨y, rfl⟩, ⟨c, hc, hce⟩⟩ := he
    rw [Subgroup.mem_prod] at hc
    have hc' : x⁻¹ * B.emb y * x = c := by
      rw [← hce]; simp [MulAut.conj_apply, mul_assoc]
    have he1 : (B.emb y).1 = GlobalTheory.LKCx.toAfF G B.β xx tt hx y := by rw [heq]; rfl
    have he2 : (B.emb y).2 = GlobalTheory.LKCx.toP1 G B.β y := by rw [heq]; rfl
    have h1 : x.1⁻¹ * GlobalTheory.LKCx.toAfF G B.β xx tt hx y * x.1 = c.1 := by
      rw [← he1, ← hc']; rfl
    have h2 : x.2⁻¹ * GlobalTheory.LKCx.toP1 G B.β y * x.2 = c.2 := by
      rw [← he2, ← hc']; rfl
    refine ⟨y, ⟨?_, ?_⟩, rfl⟩
    · rw [hfK, h1, Set.indicator_of_mem hc.1]; exact one_ne_zero
    · rw [hfK', h2, Set.indicator_of_mem hc.2]; exact one_ne_zero
  exact ((hSfin.image _).subset hsub).to_subtype

end GlobalTheory.DefStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryFinitePartMulInjectiveRange
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.BCT.FinPart

open GlobalTheory.DefU.ClassFin

section Ring

variable {R S : Type} [CommRing R] [CommRing S] {n : ℕ}

def tw (n : ℕ) (c : R →+* R) : GL (Fin n) R →* GL (Fin n) R := (invT n R).comp (GeneralLinearGroup.map c)

theorem tw_inv_val (c : R →+* R) (g : GL (Fin n) R) : ((tw n c g)⁻¹).val = cT c g.val := rfl

theorem tw_eq_iff (c : R →+* R) (g : GL (Fin n) R) : tw n c g = g ↔ cT c g.val * g.val = 1 := by
  rw [← tw_inv_val, ← Units.val_mul, Units.val_eq_one, inv_mul_eq_one]

theorem map_tw (p : R →+* S) (c : R →+* R) (d : S →+* S) (h : ∀ y, p (c y) = d (p y)) (g : GL (Fin n) R) :
    GeneralLinearGroup.map p (tw n c g) = tw n d (GeneralLinearGroup.map p g) := by
  apply Units.ext
  ext i j
  exact h _

end Ring

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def pU : finU (E := E) (n := n) →* GL (Fin n) (Af E) :=
  ((GeneralLinearGroup.map (pFin E)).comp (UA E n).subtype).comp (finU (E := E) (n := n)).subtype

theorem finGL_pU (k : finU (E := E) (n := n)) : finGL E n (pU k) = k.1.1 := finGL_pFin k

theorem pU_injective : Function.Injective (pU (E := E) (n := n)) := fun a b h =>
  Subtype.ext (Subtype.ext (by rw [← finGL_pU, h, finGL_pU]))

theorem tw_pU (k : finU (E := E) (n := n)) : tw n (conjFin (cc E)) (pU k) = pU k := (tw_eq_iff _ _).2 (cT_pFin k.1)

def sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : finU (E := E) (n := n) :=
  ⟨⟨finGL E n g, finGL_mem_UA _ ((tw_eq_iff _ _).1 h)⟩, pInf_finGL _⟩

theorem pU_sU (g : GL (Fin n) (Af E)) (h : tw n (conjFin (cc E)) g = g) : pU (sU g h) = g := pFin_finGL g

theorem ratF_tw (g : GL (Fin n) E) :
    ratF E n (tw n (cc E).toRingHom g) = tw n (conjFin (cc E)) (ratF E n g) :=
  map_tw _ _ _ (fun y => (conjFin_algebraMap (cc E) y).symm) g

theorem mem_UE (g : GL (Fin n) E) : g ∈ UE E n ↔ tw n (cc E).toRingHom g = g := by
  rw [tw_eq_iff]
  change cT _ g.val * 1 * g.val = 1 ↔ _
  rw [mul_one]

theorem ratF_injective : Function.Injective (ratF E n) := fun a b h => by
  apply Units.ext
  ext i j
  obtain ⟨w⟩ : Nonempty (HeightOneSpectrum (𝓞 E)) := by
    obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 E)
    exact ⟨⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E)⟩⟩
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h' : (ratF E n a).val = (ratF E n b).val := congrArg Units.val h
  exact (algebraMap E (Af E)).injective (congrFun₂ h' i j)

theorem pU_finPt (γ : UE E n) : pU (finPt γ) = ratF E n γ.1 := by
  have h : tw n (conjFin (cc E)) (ratF E n γ.1) = ratF E n γ.1 := by rw [← ratF_tw, (mem_UE _).1 γ.2]
  have e : finPt γ = sU _ h := by
    have h1 : toSub (UA E n) (finGL E n (ratF E n γ.1)) = (sU _ h).1 := dif_pos (sU _ h).1.2
    rw [finPt, h1]
    exact dif_pos (sU _ h).2
  rw [e, pU_sU]

theorem mem_ratFinU (k : finU (E := E) (n := n)) : k ∈ ratFinU E n ↔ pU k ∈ (ratF E n).range := by
  constructor
  · rintro ⟨g, -, hg⟩
    exact ⟨g, (pFin_finGL _).symm.trans (congrArg (GeneralLinearGroup.map (pFin E)) hg)⟩
  · rintro ⟨g, hg⟩
    refine ⟨g, (mem_UE g).2 (ratF_injective ?_), (congrArg (finGL E n) hg).trans (finGL_pU k)⟩
    rw [ratF_tw, hg, tw_pU]

theorem finPt_props : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ), (∀ a b : UE E n, finPt (a * b) = finPt a * finPt b) ∧ Function.Injective (finPt : UE E n → finU (E := E) (n := n)) ∧ ∀ x : finU (E := E) (n := n), x ∈ ratFinU E n ↔ ∃ γ : UE E n, finPt γ = x := by
  intro E _ _ _ n
  refine ⟨fun a b => pU_injective ?_, fun a b h => Subtype.ext (ratF_injective ?_), fun x => ?_⟩
  · rw [map_mul, pU_finPt, pU_finPt, pU_finPt, Subgroup.coe_mul, map_mul]
  · rw [← pU_finPt, ← pU_finPt, h]
  · rw [mem_ratFinU]
    constructor
    · rintro ⟨g, hg⟩
      have hU : g ∈ UE E n := (mem_UE g).2 (ratF_injective (by rw [ratF_tw, hg, tw_pU]))
      exact ⟨⟨g, hU⟩, pU_injective (by rw [pU_finPt, hg])⟩
    · rintro ⟨γ, rfl⟩
      exact ⟨γ.1, (pU_finPt γ).symm⟩

end GlobalTheory.BCT.FinPart
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteUnitaryLocalComponentMemIntegralGLCofini
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.SuppFin

theorem cLoc_mem_KGL_cofinite : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (y : UA E n),
    ∀ᶠ w in cofinite, cLoc w y ∈ GlobalTheory.LFun.KGL w (n := n) := by
  intro E _ _ _ n y
  set P : GL (Fin n) (Af E) := GeneralLinearGroup.map (pFin E) (y : GA E n) with hP
  have h1 : ∀ᶠ w in cofinite, ∀ i j, (P.val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact (P.val i j).2
  have h2 : ∀ᶠ w in cofinite, ∀ i j, ((P⁻¹).val i j) w ∈ HeightOneSpectrum.adicCompletionIntegers E w := by
    rw [eventually_all]; intro i; rw [eventually_all]; intro j
    exact ((P⁻¹).val i j).2
  filter_upwards [h1, h2] with w hw1 hw2
  have hmul : ∀ (A B : GL (Fin n) (Af E)), A * B = 1 →
      (A.val.map (pLoc E w)) * (B.val.map (pLoc E w)) = 1 := by
    intro A B h
    rw [← Matrix.map_mul, ← Units.val_mul, h, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]
  let M : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨(P.val i j) w, hw1 i j⟩
  let N : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.of fun i j => ⟨((P⁻¹).val i j) w, hw2 i j⟩
  have hM : M.map (Ov E w).subtype = P.val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hN : N.map (Ov E w).subtype = (P⁻¹).val.map (pLoc E w) := Matrix.ext fun i j => rfl
  have hinj : Function.Injective (fun A : Matrix (Fin n) (Fin n) (Ov E w) => A.map (Ov E w).subtype) :=
    Matrix.map_injective Subtype.val_injective
  let k : GL (Fin n) (Ov E w) :=
    { val := M
      inv := N
      val_inv := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (mul_inv_cancel P))
      inv_val := hinj (by
        simp only
        rw [Matrix.map_mul, hM, hN, Matrix.map_one _ (map_zero _) (map_one _)]
        exact hmul _ _ (inv_mul_cancel P)) }
  exact ⟨k, Units.ext (Matrix.ext fun i j => rfl)⟩

end GlobalTheory.BCT.SuppFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqDiscreteSeriesOfLowestKTypeCasimir
section
noncomputable section

open ReciprocityTheory.ChartRestriction.DS

namespace GlobalTheory.PsCo.PcEF

theorem eq_discreteSeries_of_lowestKType_casimir : DatumEquiv := by
  intro n ε lam hgap H _ _ _ σ hσ hirr V hV hV0 hc X _ _ D hD
  haveI : CompleteSpace X := hD.1
  have hσD : IsURepOn (UJset ε) D := hD.2.2.1
  have hVK : ∀ k ∈ Kset ε, ∀ v ∈ V, ∃ w ∈ V, (w : H) = σ k v :=
    kStable_of_isKStableSub hσ (isDerivedOn_smE hσ) V hV.1 hV.2.1
  obtain ⟨V', hV', hV0', hVK', hc'⟩ := arb_datum hD (casOnSmooth_of_isDS hD hgap)
  have htop := data_closGen_eq_top hgap hσ (isDerivedOn_smE hσ) hV hc hVK hirr hV0
  have htop' := data_closGen_eq_top hgap hσD (isDerivedOn_smE hσD) hV' hc' hVK' hD.2.2.2.1 hV0'
  obtain ⟨U, hU⟩ := data_unitary_equiv hgap hσ (isDerivedOn_smE hσ) hV hc hVK hV0
    hσD (isDerivedOn_smE hσD) hV' hc' hVK' hV0'
  refine ⟨((LinearIsometryEquiv.ofTop _ _ htop).symm.trans U).trans (LinearIsometryEquiv.ofTop _ _ htop'),
    fun g hg x => ?_⟩
  simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.ofTop_apply]
  apply hU g hg
  simp only [LinearIsometryEquiv.ofTop_symm_apply_coe]

end GlobalTheory.PsCo.PcEF
end
end

