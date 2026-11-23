module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1176
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0111
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.DifferentialTranslates.Bundle0006

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdCompact
section
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit UpperTheory.V.Lit.Dr
open GroundTheory.Automorphic GroundTheory.Automorphic.CuspidalSpectrum
open UpperTheory.V.Lit.Geo
open scoped TensorProduct

private theorem cont_ev {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}
    {U : Subgroup (GL (Fin a) (Af E))} (hU : IsOpen (U : Set (GL (Fin a) (Af E)))) {Ξ : AlgRep E a}
    {m : Sm E a ⊗[ℂ] (Fin Ξ.d → ℂ)}
    (hm : m ∈ Submodule.span ℂ {x | ∃ φ v, IsLevelFn U Ξ φ ∧ x = φ ⊗ₜ[ℂ] v}) : Continuous (ev m) := by
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨φ, v, hφ, rfl⟩ := hx
    let S : Subgroup (GL (Fin a) (Af E)) :=
      { carrier := {k | finRep E a k φ = φ}
        one_mem' := by simp
        mul_mem' := fun {x y} hx hy => by
          have hx' : finRep E a x φ = φ := hx
          have hy' : finRep E a y φ = φ := hy
          change finRep E a (x * y) φ = φ
          rw [map_mul, Module.End.mul_apply, hy', hx']
        inv_mem' := fun {x} hx => by
          have hx' : finRep E a x φ = φ := hx
          change finRep E a x⁻¹ φ = φ
          conv_lhs => rw [← hx']
          rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] }
    have hS : IsOpen (S : Set (GL (Fin a) (Af E))) := Subgroup.isOpen_mono (H₁ := U) (fun u hu => hφ.2.1 u hu) hU
    exact (ContAut.continuous_of_isOpen_stab E a φ hS).smul continuous_const
  | zero => rw [map_zero]; exact continuous_const
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact hx.add hy
  | smul c x _ hx => rw [map_smul]; exact hx.const_smul c

theorem UpperTheory.V.Lit.Geo.bdCompact :
    BdCompact := by
  intro E _ _ _ a U hU Ξ q α hα R
  obtain ⟨T, B, hB, hT⟩ := bdBasis E a Ξ q
  obtain ⟨K, hK, hR⟩ := (qhtFacts E a).2.2.2 R
  have hb : ∀ X : Fin q → Herm E a, ∃ c : ℝ, ∀ g ∈ K, ‖ev (α X) (retractOne g : KernelIndexFullLattice.G1 E a).1‖ ≤ c := fun X =>
    hK.exists_bound_of_continuousOn
      ((cont_ev hU (hα.val X)).comp (continuous_subtype_val.comp continuous_retractOne)).continuousOn
  choose c hc using hb
  refine ⟨B * ∑ X ∈ T, |c X|, by positivity, fun g hg => hT α g _ (by positivity) fun X hX => ?_⟩
  obtain ⟨γ, t, h⟩ := hR g hg
  have e := hc X _ h
  rw [(retrFacts E a).2.1, ((levelVal E a U Ξ _).1 (hα.val X)).1] at e
  exact (e.trans (le_abs_self _)).trans (Finset.single_le_sum (f := fun X => |c X|) (fun _ _ => abs_nonneg _) hX)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.BdGrowth
section
open UpperTheory.V.Lit.Geo NumberField GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr UpperTheory.V.Lit.Bor

theorem UpperTheory.V.Lit.Geo.bdGrowth :
    BdGrowth := by
  intro E _ _ _ a Ξ q α
  obtain ⟨T, B, hB, hT⟩ := bdBasis E a Ξ q
  have hq := (qhtFacts E a).1
  have hr : ∀ g, qht (E := E) (a := a)
      (GroundTheory.Automorphic.CuspidalSpectrum.retractOne g : KernelIndexFullLattice.G1 E a).1 = qht g := fun g => by
    obtain ⟨t, ht⟩ := (retrFacts E a).1 g
    have h := (qhtFacts E a).2.1 1 t g
    rw [map_one, one_mul] at h
    rw [ht, h]
  have hs : ∀ (C : _ → ℝ), ∀ X ∈ T, C X ≤ ∑ X ∈ T, |C X| := fun C X hX =>
    (le_abs_self _).trans (Finset.single_le_sum (f := fun X => |C X|) (fun _ _ => abs_nonneg _) hX)
  refine ⟨fun ⟨N, h⟩ => ?_, fun h N => ?_⟩
  · choose C hC using h
    have h0 : 0 ≤ ∑ X ∈ T, |C X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨N, B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩
    have q0 : 0 < qht g := one_pos.trans_le (hq g)
    rw [mul_assoc]
    refine hT α g _ (by positivity) fun X hX => (hC X _).trans ?_
    rw [hr]
    exact mul_le_mul_of_nonneg_right (hs C X hX) (by positivity)
  · choose C hC using fun X => h X N
    have h0 : 0 ≤ ∑ X ∈ T, |C X| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine ⟨B * ∑ X ∈ T, |C X|, mul_nonneg hB h0, fun g => ?_⟩
    have q0 : 0 < qht g := one_pos.trans_le (hq g)
    rw [mul_div_assoc]
    refine hT α g _ (by positivity) fun X hX => ?_
    rw [le_div_iff₀ (by positivity), ← hr g]
    exact (hC X _).trans (hs C X hX)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAltSz
section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem sz_ball {X Y : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] (f : X → Y) (hf : ContDiff ℝ ∞ f) (k : ℕ) (c : ℝ) :
    ∃ C : ℝ, ∀ x : X, ‖x‖ ≤ c → Sz k f x C := by
  have hc : Continuous fun x => ∑ i ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ i f x‖ :=
    continuous_finsetSum _ fun i _ => (hf.continuous_iteratedFDeriv (by exact_mod_cast le_top)).norm
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : X) c).bddAbove_image hc.continuousOn
  refine ⟨C, fun x hx i hi => ?_⟩
  refine le_trans ?_ (hC ⟨x, mem_closedBall_zero_iff.2 hx, rfl⟩)
  exact Finset.single_le_sum (f := fun i => ‖iteratedFDeriv ℝ i f x‖) (fun _ _ => norm_nonneg _)
    (Finset.mem_range.2 (Nat.lt_succ_of_le hi))

private theorem alt_fin (V F : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ F] (q : ℕ) : FiniteDimensional ℝ (V [⋀^Fin q]→L[ℝ] F) := by
  let b := Module.finBasis ℝ V
  let E : (V [⋀^Fin q]→L[ℝ] F) →ₗ[ℝ] ((Fin q → Fin (Module.finrank ℝ V)) → F) :=
    { toFun := fun a k => a fun i => b (k i)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine FiniteDimensional.of_injective E fun a a' h => ?_
  apply ContinuousAlternatingMap.toAlternatingMap_injective
  exact Module.Basis.ext_alternating b fun k _ => congrFun h k

theorem UpperTheory.V.Lit.Geo.Cs.altSz :
    AltSz := by
  intro V F _ _ _ _ _ _ q k c
  have h : ContDiff ℝ ∞ (fun L : V →L[ℝ] V => (ContinuousAlternatingMap.compContinuousLinearMapCLM L :
      (V [⋀^Fin q]→L[ℝ] F) →L[ℝ] (V [⋀^Fin q]→L[ℝ] F))) := by
    haveI := alt_fin V F q
    rw [contDiff_clm_apply_iff]
    intro w
    rw [contDiff_iff_contDiffAt]
    intro L
    refine UpperTheory.V.Lit.Dr.altSmooth _ V F q _ L fun v => ?_
    exact UpperTheory.V.Lit.Dr.applySmooth (V →L[ℝ] V) V F q (fun _ => w) (fun i L => L (v i)) L contDiffAt_const
      fun i => (contDiffAt_id.clm_apply contDiffAt_const)
  exact ⟨h, sz_ball _ h k c⟩
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsAppSz
section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.appSz :
    AppSz := by
  intro V W F _ _ _ _ _ _ k x
  refine ⟨?_, ?_, ?_⟩
  · intro f g a b hf hg ha hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    obtain ⟨u, hu, hfu⟩ := (hf.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨v, hv, hgv⟩ := (hg.of_le hi').contDiffOn (m := i) le_rfl (by simp)
    obtain ⟨s, hs, hso, hxs⟩ := mem_nhds_iff.1 (Filter.inter_mem hu hv)
    have key := norm_iteratedFDerivWithin_clm_apply (n := i)
      (hfu.mono fun y hy => (hs hy).1) (hgv.mono fun y hy => (hs hy).2) hso.uniqueDiffOn hxs le_rfl
    simp only [iteratedFDerivWithin_of_isOpen _ hso hxs] at key
    refine key.trans ?_
    have h0 := ha.nonneg
    have h1 := hb.nonneg
    calc _ ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * a * b := by
          refine Finset.sum_le_sum fun j hj => ?_
          have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
          have e1 := ha j (hj'.trans hi)
          have e2 := hb (i - j) ((Nat.sub_le _ _).trans hi)
          gcongr
      _ = 2 ^ i * a * b := by
          rw [← Finset.sum_mul, ← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
          simp
      _ ≤ 2 ^ k * a * b := by
          gcongr
          norm_num
  · intro L g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := L.iteratedFDeriv_comp_left hg (i := i) hi'
    have e : (fun y => L (g y)) = L ∘ g := rfl
    rw [e, key]
    exact (L.norm_compContinuousMultilinearMap_le _).trans
      (mul_le_mul_of_nonneg_left (hb i hi) (norm_nonneg _))
  · intro ι s g b hg hb i hi
    have hi' : (i : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
    have key := iteratedFDeriv_fun_sum_apply (n := i) (u := s) (f := g) (x := x)
      (fun j hj => (hg j hj).of_le hi')
    rw [key]
    exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j hj => hb j hj i hi)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsCompSz
section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.compSz :
    CompSz := by
  intro V W F _ _ _ _ _ _ k c
  have hD1 : (1 : ℝ) ≤ max 1 c := le_max_left _ _
  have hD0 : (0 : ℝ) ≤ max 1 c := zero_le_one.trans hD1
  refine ⟨(k.factorial : ℝ) * (max 1 c) ^ k, by positivity, ?_⟩
  intro g f x b hf hg hc hb i hi
  have hb0 : 0 ≤ b := hb.nonneg
  have hk : ((k : ℕ) : WithTop ℕ∞) ≤ ∞ := by exact_mod_cast le_top
  have hne : ((k : ℕ) : WithTop ℕ∞) ≠ ∞ := by exact_mod_cast ENat.coe_ne_top k
  have hf' := (hf.of_le hk).eventually hne
  have hg' := (hg.of_le hk).eventually hne
  obtain ⟨t, ht, hto, hxt⟩ := eventually_nhds_iff.1 hg'
  have hpre : ∀ᶠ y in 𝓝 x, f y ∈ t := hf.continuousAt.preimage_mem_nhds (hto.mem_nhds hxt)
  obtain ⟨s, hs, hso, hxs⟩ := eventually_nhds_iff.1 (hf'.and hpre)
  have hgt : ContDiffOn ℝ k g t := fun y hy => (ht y hy).contDiffWithinAt
  have hfs : ContDiffOn ℝ k f s := fun y hy => (hs y hy).1.contDiffWithinAt
  have key := norm_iteratedFDerivWithin_comp_le (𝕜 := ℝ) (n := i) (C := b) (D := max 1 c) hgt hfs
    (by exact_mod_cast hi) hto.uniqueDiffOn hso.uniqueDiffOn (fun y hy => (hs y hy).2) hxs
    (fun j hj => by
      rw [iteratedFDerivWithin_of_isOpen j hto hxt]
      exact hb j (hj.trans hi))
    (fun j hj1 hj => by
      rw [iteratedFDerivWithin_of_isOpen j hso hxs]
      exact ((hc j hj1 (hj.trans hi)).trans (le_max_right 1 c)).trans
        (le_self_pow₀ hD1 (by omega)))
  rw [iteratedFDerivWithin_of_isOpen i hso hxs] at key
  refine key.trans ?_
  have h1 : (i.factorial : ℝ) ≤ k.factorial := by exact_mod_cast Nat.factorial_le hi
  have h2 : (max 1 c) ^ i ≤ (max 1 c) ^ k := pow_le_pow_right₀ hD1 hi
  calc (i.factorial : ℝ) * b * (max 1 c) ^ i = ((i.factorial : ℝ) * (max 1 c) ^ i) * b := by ring
    _ ≤ _ := by gcongr
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDescEx
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.Lit.Dr
open UpperTheory.V.Lit.Geo UpperTheory.V.Lit.Geo.Cs

section

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

private theorem exists_unitary {g h : GL (Fin a) (Cinf E)} (e : sand g (hOne E a) = sand h (hOne E a)) :
    ∃ k : Kinf E a, h = g * Unitary.toUnits k := by
  have comp : ∀ (g h : GL (Fin a) (Cinf E)) (v : HV E a), sand g (sand h v) = sand (g * h) v := fun g h v => by
    rw [map_mul]; rfl
  have h1 : sand (g⁻¹ * h) (hOne E a) = hOne E a := by
    rw [← comp, ← e, comp, inv_mul_cancel, map_one]; rfl
  have h2 : (g⁻¹ * h).val * star (g⁻¹ * h).val = 1 := by
    have h3 := sand_val (g⁻¹ * h) (hOne E a)
    rw [h1, hOne_val, mul_one] at h3
    exact h3.symm
  refine ⟨⟨(g⁻¹ * h).val, Matrix.mem_unitaryGroup_iff.2 h2⟩, ?_⟩
  rw [← inv_mul_eq_iff_eq_mul]
  exact Units.ext rfl

end

theorem UpperTheory.V.Lit.Geo.Cs.descEx :
    DescEx := by
  classical
  intro E _ _ _ a U f Y C c f₀ hf
  refine ⟨fun s p => if h : p ∈ cone E a then f (pt h.choose s.out) else 0, fun g x => ?_⟩
  have hp : sand g (hOne E a) ∈ cone E a := ⟨g, rfl⟩
  obtain ⟨k, hk⟩ := exists_unitary hp.choose_spec.symm
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul U x
  beta_reduce
  rw [dite_eq_left hp, hk, pt_mul, hf.f_cpt, hu, pt, pt, map_mul (finGL E a), ← mul_assoc, hf.f_lev _ u.2]
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsDescFun
section
noncomputable section

open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af GlobalTheory.UnitaryBC UpperTheory.V.Lit.Dr
open scoped ContDiff

namespace UpperTheory.V.Lit.Geo.Cs

variable {E : Type} [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] {a : ℕ}

private theorem rat_pt (γ : GL (Fin a) E) (g : GL (Fin a) (Cinf E)) (x : GL (Fin a) (Af E)) :
    pt (GeneralLinearGroup.map (pInf E) (ratGL E a γ) * g) (GeneralLinearGroup.map (algebraMap E (Af E)) γ * x) =
      ratGL E a γ * pt g x := by
  unfold pt
  refine ga_ext ?_ ?_
  · simp only [map_mul, pInf_infGL, pInf_finGL, mul_one]
  · simp only [map_mul, pFin_infGL, pFin_finGL, one_mul]
    rfl

private theorem centre_zero : splitCentre E a 0 = 1 := by
  have h : (expU fun _ : InfinitePlace E => ((0 : ℝ) : ℂ)) = 1 := by
    ext w
    simp [expU]
  rw [splitCentre, h, map_one, map_one]

private theorem scal_ex (r : ℝ) (hr : 0 < r) : ∃ (t : ℝ) (c : GL (Fin a) (Cinf E)),
    infGL E a c = splitCentre E a t ∧ ∀ p : HV E a, sand c p = r • p := by
  refine ⟨Real.log r / 2, _, rfl, fun p => Subtype.ext ?_⟩
  have h : (Units.map (Matrix.scalar (Fin a)).toMonoidHom
      (expU fun _ : InfinitePlace E => ((Real.log r / 2 : ℝ) : ℂ)) : GL (Fin a) (Cinf E)).val =
      Real.exp (Real.log r / 2) • (1 : Matrix (Fin a) (Fin a) (Cinf E)) := by
    ext i j w
    by_cases hij : i = j <;> simp [expU, hij, Matrix.one_apply]
  have e : Real.exp (Real.log r / 2) * Real.exp (Real.log r / 2) = r := by
    rw [← Real.exp_add, add_halves, Real.exp_log hr]
  change Matrix.of (sand _ p).1 = r • Matrix.of p.1
  rw [sand_val, h, star_smul, star_one, star_trivial, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul, e]

end UpperTheory.V.Lit.Geo.Cs

open UpperTheory.V.Lit.Geo.Cs

theorem UpperTheory.V.Lit.Geo.Cs.descFun :
    DescFun := by
  intro E _ _ _ a ho U Ξ f Y C c f₀ hS Φ hΦ
  refine ⟨fun s p₀ hp₀ => ?_, ?_, ?_⟩
  · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨τ, hτ, hs⟩ := locSec E a p₀ hp₀
    refine ContDiffAt.contDiffWithinAt ?_
    obtain ⟨φ, hφ, -⟩ := hS.f_sm
    have h0 := (contDiffAt_chart φ.2 (finGL E a x) (val_mem_invSet (τ p₀))).comp p₀ hτ
    simp only [Function.comp_def, chart_val, hφ] at h0
    have h1 := Complex.reCLM.contDiff.contDiffAt.comp p₀ h0
    refine h1.congr_of_eventuallyEq (hs.mono fun p hp => ?_)
    have := hΦ (τ p) x
    rw [hp] at this
    rw [this, pt, infGL_comm]
    simp
  · rintro γ s p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    have hs : ∀ p : HV E a, (geo ho U Ξ).ρ γ (sand g p) =
        sand (GeneralLinearGroup.map (pInf E) (ratGL E a γ.1) * g) p := fun p => by
      rw [geo_ρ, map_mul]; rfl
    have hσ : (geo ho U Ξ).σ γ (x : GL (Fin a) (Af E) ⧸ U) =
        ((GeneralLinearGroup.map (algebraMap E (Af E)) γ.1 * x : GL (Fin a) (Af E)) : GL (Fin a) (Af E) ⧸ U) := rfl
    have hl := hS.f_left γ.1 0 (pt g x)
    rw [centre_zero, mul_one] at hl
    rw [hσ, hs, hΦ, hΦ, rat_pt, hl]
  · rintro s r hr p ⟨g, rfl⟩
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective s
    obtain ⟨t, c, hc, hp⟩ := scal_ex (E := E) (a := a) r hr
    have hl := hS.f_left 1 t (pt g x)
    rw [map_one, one_mul, ← hc, pt, ← mul_assoc, ← map_mul] at hl
    have hs : ∀ p : HV E a, r • sand g p = sand (c * g) p := fun p => by
      rw [map_mul, ContinuousLinearMap.mul_apply, hp]
    rw [hs, hΦ, hΦ]
    exact hl
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsFlowSz
section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff

private theorem norm_id_le (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] (j : ℕ) (p : V) :
    ‖iteratedFDeriv ℝ (j + 1) (fun x : V => x) p‖ ≤ 1 := by
  rw [← norm_iteratedFDeriv_fderiv]
  have e : fderiv ℝ (fun x : V => x) = fun _ => ContinuousLinearMap.id ℝ V := by
    funext x
    exact fderiv_id
  rw [e]
  rcases j with _ | j
  · simpa using ContinuousLinearMap.norm_id_le
  · rw [iteratedFDeriv_const_of_ne (Nat.succ_ne_zero j)]
    simp

theorem UpperTheory.V.Lit.Geo.Cs.flowSz :
    FlowSz := by
  intro V _ _ k c W t p ht hW hS
  have e : UpperTheory.V.Lit.Geo.flow W t = (fun x : V => x) + t • W := rfl
  have h1 : ContDiffAt ℝ ∞ (UpperTheory.V.Lit.Geo.flow W t) p := by
    rw [e]
    exact contDiffAt_id.add (hW.const_smul t)
  have h4 : ∀ i, 1 ≤ i → i ≤ k + 1 → ‖iteratedFDeriv ℝ i (UpperTheory.V.Lit.Geo.flow W t) p‖ ≤ 1 + c := by
    intro i h1i hi
    obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
    have hWj : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) W p := hW.of_le (by exact_mod_cast le_top)
    have hid : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (fun x : V => x) p := contDiffAt_id
    have htW : ContDiffAt ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (t • W) p := hWj.const_smul t
    rw [e, iteratedFDeriv_add_apply hid htW, iteratedFDeriv_const_smul_apply hWj]
    refine (norm_add_le _ _).trans (add_le_add (norm_id_le V j p) ?_)
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_of_le_one_left (norm_nonneg _) ht).trans (hS _ hi)
  refine ⟨h1, h1.fderiv_right (by simp), fun i hi => ?_, h4⟩
  rw [norm_iteratedFDeriv_fderiv]
  exact h4 _ (by omega) (by omega)
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.LieGeometryGrowth.CsGeoCut
section
open UpperTheory.V.Lit.Geo.Cs
open scoped ContDiff Topology

theorem UpperTheory.V.Lit.Geo.Cs.geoCut :
    GeoCut := by
  intro Γ V S _ _ _ _ d G Φ hΦ R q η hη hinv
  classical
  set χ : ℝ → ℝ := fun t => Real.smoothTransition (2 * (t - R) - 1) with hχ
  have hχc : ContDiff ℝ ∞ χ :=
    Real.smoothTransition.contDiff.comp ((contDiff_const.mul (contDiff_id.sub contDiff_const)).sub contDiff_const)
  have hχ0 : ∀ t, t ≤ R + 1 / 2 → χ t = 0 := fun t ht =>
    Real.smoothTransition.zero_of_nonpos (by linarith)
  have hχ1 : ∀ t, R + 1 ≤ t → χ t = 1 := fun t ht =>
    Real.smoothTransition.one_of_one_le (by linarith)
  let f : S → V → V [⋀^Fin q]→L[ℝ] (Fin d → ℂ) :=
    fun s p => if p ∈ G.Y ∧ R < Φ s p then χ (Φ s p) • η s p else 0
  have hf : f ∈ G.Om q := by
    show ∀ s, ContDiffOn ℝ ∞ (f s) G.Y ∧ ∀ p ∉ G.Y, f s p = 0
    refine fun s => ⟨?_, fun p hp => by simp [f, hp]⟩
    apply contDiffOn_of_locally_contDiffOn
    intro p hp
    by_cases hR : R < Φ s p
    · refine ⟨G.Y ∩ Φ s ⁻¹' Set.Ioi R, (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Ioi,
        ⟨hp, hR⟩, ?_⟩
      have hsm : ContDiffOn ℝ ∞ (fun x => χ (Φ s x) • η s x) (G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) :=
        ((hχc.comp_contDiffOn (hΦ.1 s)).mono (fun x (hx : x ∈ G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) => hx.1)).smul
          ((hη s).mono (fun x (hx : x ∈ G.Y ∩ (G.Y ∩ Φ s ⁻¹' Set.Ioi R)) => ⟨hx.2.1, hx.2.2⟩))
      refine hsm.congr (fun x hx => ?_)
      have hx' : x ∈ G.Y ∧ R < Φ s x := ⟨hx.2.1, hx.2.2⟩
      simp only [f, if_pos hx']
    · push_neg at hR
      refine ⟨G.Y ∩ Φ s ⁻¹' Set.Iio (R + 1 / 2),
        (hΦ.1 s).continuousOn.isOpen_inter_preimage G.isOpen isOpen_Iio,
        ⟨hp, show Φ s p < R + 1 / 2 by linarith⟩, ?_⟩
      refine (contDiffOn_const (c := (0 : V [⋀^Fin q]→L[ℝ] (Fin d → ℂ)))).congr (fun x hx => ?_)
      have hx2 : Φ s x < R + 1 / 2 := hx.2.2
      simp only [f]
      split_ifs with h
      · rw [hχ0 _ hx2.le, zero_smul]
      · rfl
  refine ⟨⟨f, hf⟩, ?_, ?_⟩
  · intro γ
    apply Subtype.ext
    funext s p
    show G.tr q γ (f (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) = f s p
    have hρ : ∀ x, G.ρ γ (G.ρ γ⁻¹ x) = x := by
      intro x
      rw [← ContinuousLinearMap.mul_apply, ← map_mul, mul_inv_cancel, map_one]
      rfl
    by_cases hp : p ∈ G.Y
    · have hp' : G.ρ γ⁻¹ p ∈ G.Y := G.maps _ _ hp
      have hΦ' : Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) = Φ s p := hΦ.2.1 γ⁻¹ s p hp
      by_cases hR : R < Φ s p
      · have h1 : G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p) := ⟨hp', by rw [hΦ']; exact hR⟩
        have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, hR⟩
        simp only [f, if_pos h1, if_pos h2]
        rw [hΦ', map_smul, hinv γ s p hp hR]
      · have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := by
          rw [hΦ']
          exact fun h => hR h.2
        have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hR h.2
        simp only [f, if_neg h1, if_neg h2, map_zero]
    · have hp' : G.ρ γ⁻¹ p ∉ G.Y := fun h => hp (by simpa [hρ] using G.maps γ _ h)
      have h1 : ¬ (G.ρ γ⁻¹ p ∈ G.Y ∧ R < Φ (G.σ γ⁻¹ s) (G.ρ γ⁻¹ p)) := fun h => hp' h.1
      have h2 : ¬ (p ∈ G.Y ∧ R < Φ s p) := fun h => hp h.1
      simp only [f, if_neg h1, if_neg h2, map_zero]
  · intro s p hp h1
    have h2 : p ∈ G.Y ∧ R < Φ s p := ⟨hp, by linarith⟩
    show f s p = η s p
    simp only [f, if_pos h2, hχ1 _ h1, one_smul]
end

