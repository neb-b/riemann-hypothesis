module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.Bundle0020
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
public import Formalism.RealPlaceAnalysis.Bundle0003
public import Formalism.RealPlaceAnalysis.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ModelsAreCoverSeries
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0200
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0310
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0008
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0009
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsAdmOnOfFiniteDimensional
public import Formalism.RealPlaceAnalysis.RealPlaceTaylor.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralInverseOnConjugateHalf
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.LiftLevel

namespace GlobalTheory.HalfUnit

theorem cc_star (D : D7) (x : D.host.E) : cc (star x) = x := by
  first
  | exact star_star x
  | rfl
  | simp [cc]

theorem mem_conjI_of (D : D7) (P : Ideal (𝓞 D.host.E)) (s : 𝓞 D.host.E)
    (h : Formalism.L2.Col.cO D.host.E s ∈ P) : s ∈ conjI P :=
  Ideal.subset_span ⟨_, h, (cc_star D (s : D.host.E)).symm⟩

theorem exists_int_inv_half : ∀ (D : D7) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (e : AE D), IsIdemSum e P →
    ∀ s : 𝓞 D.host.E, (∀ PP ∈ P, s ∉ conjI PP.asIdeal) →
    ∃ t : AE D, finPart D t ∈ intAE D ∧ t * incA D (s : D.host.E) * cA D e = cA D e := by
  intro D P e he s hs
  have hee : e * e = e := GlobalTheory.PlaceVec.idemSum_mul_self he
  obtain ⟨⟨es, hes, rfl⟩, -⟩ := he
  by_cases hP : P = ∅
  · subst hP
    refine ⟨0, by rw [map_zero]; exact zero_mem _, ?_⟩
    simp
  obtain ⟨tableDegreeThreeBase, hPP0⟩ := Finset.nonempty_iff_ne_empty.2 hP
  have hs0 : s ≠ 0 := by
    rintro rfl
    exact hs tableDegreeThreeBase hPP0 (zero_mem _)
  have hsE : (s : D.host.E) ≠ 0 := by
    intro h; apply hs0; exact RingOfIntegers.ext (by simpa using h)
  refine ⟨cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹), ?_, ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    · rw [map_sum, Finset.sum_mul, map_sum]
      refine sum_mem fun PP hPP => ?_
      have hc0 : Formalism.L2.Col.cO D.host.E s ≠ 0 := by
        intro h0; apply hs0
        rw [← Formalism.L2.Col.cO_cO s, h0, map_zero]
      have hnot : Formalism.L2.Col.cO D.host.E s ∉ PP.asIdeal := fun hm => hs PP hPP (mem_conjI_of D _ s hm)
      have hint := not_not.1 (mt ((hes PP hPP).2 _ hc0).2 hnot)
      have := GlobalTheory.MovedIdem.finPart_conj_mem hint
      have hst : star (((Formalism.L2.Col.cO D.host.E s : 𝓞 D.host.E) : D.host.E)⁻¹) = (s : D.host.E)⁻¹ := by
        rw [star_inv₀]
        congr 1
        exact star_star (s : D.host.E)
      rwa [hst] at this
  · have h1 : incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) = 1 := by
      rw [← map_mul, inv_mul_cancel₀ hsE, map_one]
    calc cA D (∑ PP ∈ P, es PP) * incA D ((s : D.host.E)⁻¹) * incA D (s : D.host.E) * cA D (∑ PP ∈ P, es PP)
        = cA D ((∑ PP ∈ P, es PP) * (∑ PP ∈ P, es PP)) := by
          rw [mul_assoc (cA D _), h1, mul_one, map_mul]
      _ = cA D (∑ PP ∈ P, es PP) := by rw [hee]

end GlobalTheory.HalfUnit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKEquivariantGraphGoursat
section
open MeasureTheory Matrix Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar UEquiv gelfVal)
open GlobalTheory.Orb (IsPseudoCoeff ujMat ujRep)
open scoped InnerProductSpace

namespace GlobalTheory.KStableGraph

theorem exists_partner {n : ℕ} {ε : Fin n → Bool} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] {ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {S S' U : Submodule ℂ H}
    (hS : Formalism.MainNotions.S.IsKStableOn ε ρ S) (hS' : Formalism.MainNotions.S.IsKStableOn ε ρ S')
    (hU : Formalism.MainNotions.S.IsKStableOn ε ρ U)
    (irr : ∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S)
    (hle : U ≤ S ⊔ S') (hUS' : U ⊓ S' = ⊥) (hU0 : U ≠ ⊥) :
    ∀ s ∈ S, ∃ s' ∈ S', s + s' ∈ U := by
  have hT : Formalism.MainNotions.S.IsKStableOn ε ρ (S ⊓ (U ⊔ S')) := by
    intro g hg v hv
    obtain ⟨hvS, hvU⟩ := Submodule.mem_inf.mp hv
    obtain ⟨u, hu, t, ht, rfl⟩ := Submodule.mem_sup.mp hvU
    refine Submodule.mem_inf.mpr ⟨hS g hg _ hvS, ?_⟩
    rw [map_add (f := _)]
    exact Submodule.add_mem_sup (hU g hg u hu) (hS' g hg t ht)
  rcases irr _ inf_le_left hT with h | h
  · exfalso
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    obtain ⟨s, hs, t, ht, hst⟩ := Submodule.mem_sup.mp (hle hu)
    have hsT : s ∈ S ⊓ (U ⊔ S') := by
      refine Submodule.mem_inf.mpr ⟨hs, ?_⟩
      have : s = u - t := by rw [← hst]; abel
      rw [this]
      exact Submodule.sub_mem_sup hu ht
    rw [h] at hsT
    have hs0 : s = 0 := (Submodule.mem_bot ℂ).mp hsT
    have hut : u = t := by rw [← hst, hs0, zero_add]
    have : u ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨hu, hut ▸ ht⟩
    rw [hUS'] at this
    exact hu0 ((Submodule.mem_bot ℂ).mp this)
  · intro s hs
    have hs' : s ∈ S ⊓ (U ⊔ S') := h.symm ▸ hs
    obtain ⟨u, hu, t, ht, hut⟩ := Submodule.mem_sup.mp (Submodule.mem_inf.mp hs').2
    refine ⟨-t, S'.neg_mem ht, ?_⟩
    have : s + -t = u := by rw [← hut]; abel
    rw [this]; exact hu

theorem exists_kMap_onto : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (S S' U : Submodule ℂ H), Formalism.MainNotions.S.IsKStableOn ε ρ S → Formalism.MainNotions.S.IsKStableOn ε ρ S' → Formalism.MainNotions.S.IsKStableOn ε ρ U → (∀ T : Submodule ℂ H, T ≤ S → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S) → (∀ T : Submodule ℂ H, T ≤ S' → Formalism.MainNotions.S.IsKStableOn ε ρ T → T = ⊥ ∨ T = S') → S ⊓ S' = ⊥ → U ≤ S ⊔ S' → U ⊓ S = ⊥ → U ⊓ S' = ⊥ → U ≠ ⊥ → ∃ φ : H →ₗ[ℂ] H, (∀ k ∈ Formalism.REAL.Kset ε, ∀ u ∈ S, φ (ρ k u) = ρ k (φ u)) ∧ S.map φ = S' := by
  intro n ε H _ _ ρ S S' U hS hS' hU irrS irrS' hSS' hle hUS hUS' hU0
  have ex := exists_partner hS hS' hU irrS hle hUS' hU0
  have ex' := exists_partner hS' hS hU irrS' (by rwa [sup_comm]) hUS hU0
  have uniq : ∀ s ∈ S, ∀ a ∈ S', ∀ b ∈ S', s + a ∈ U → s + b ∈ U → a = b := by
    intro s _ a ha b hb h1 h2
    have h3 := U.sub_mem h1 h2
    rw [add_sub_add_left_eq_sub] at h3
    have : a - b ∈ U ⊓ S' := Submodule.mem_inf.mpr ⟨h3, S'.sub_mem ha hb⟩
    rw [hUS'] at this
    exact sub_eq_zero.mp ((Submodule.mem_bot ℂ).mp this)
  choose g hg using ex
  let f : S →ₗ[ℂ] S' :=
    { toFun := fun x => ⟨g x x.2, (hg x x.2).1⟩
      map_add' := fun x y => by
        apply Subtype.ext
        show g ((x + y : S) : H) (x + y).2 = g x x.2 + g y y.2
        refine uniq _ (x + y).2 _ (hg _ _).1 _ (S'.add_mem (hg x x.2).1 (hg y y.2).1) (hg _ _).2 ?_
        have := U.add_mem (hg x x.2).2 (hg y y.2).2
        rw [Submodule.coe_add]
        convert this using 1
        abel
      map_smul' := fun c x => by
        apply Subtype.ext
        show g ((c • x : S) : H) (c • x).2 = c • g x x.2
        refine uniq _ (c • x).2 _ (hg _ _).1 _ (S'.smul_mem c (hg x x.2).1) (hg _ _).2 ?_
        have := U.smul_mem c (hg x x.2).2
        rw [Submodule.coe_smul]
        convert this using 1
        rw [smul_add] }
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl S
  let φ : H →ₗ[ℂ] H := S'.subtype ∘ₗ f ∘ₗ S.projectionOnto C hC
  have hφ : ∀ u (hu : u ∈ S), φ u = g u hu := by
    intro u hu
    have := Submodule.linearProjOfIsCompl_apply_left hC ⟨u, hu⟩
    change ((f (S.projectionOnto C hC ((⟨u, hu⟩ : S) : H)) : S') : H) = _
    rw [this]
    rfl
  refine ⟨φ, ?_, ?_⟩
  · intro k hk u hu
    have hku : ρ k u ∈ S := hS k hk u hu
    rw [hφ _ hku, hφ u hu]
    refine uniq _ hku _ (hg _ hku).1 _ (hS' k hk _ (hg u hu).1) (hg _ hku).2 ?_
    rw [← map_add (f := _)]
    exact hU k hk _ (hg u hu).2
  · apply le_antisymm
    · rintro _ ⟨u, hu, rfl⟩
      rw [hφ u hu]
      exact (hg u hu).1
    · intro s' hs'
      obtain ⟨s, hs, hsU⟩ := ex' s' hs'
      refine Submodule.mem_map.mpr ⟨s, hs, ?_⟩
      rw [hφ s hs]
      exact uniq s hs _ (hg s hs).1 s' hs' (hg s hs).2 (by rwa [add_comm])

end GlobalTheory.KStableGraph
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsKFiniteIsometryDiscreteSeriesModelDetCover
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.KFiniteTie

open GlobalTheory.CoverModel GlobalTheory.Chain.RealIt.LocalFromCover
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (toFrame)

section Semi

variable {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {cj : Bool} {U : H → H'}

theorem cjc_ofReal (cj : Bool) (r : ℝ) : cjc cj (r : ℂ) = r := by
  cases cj <;> simp [cjc]

theorem exists_real (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hb : Function.Bijective U) (hn : ∀ x, ‖U x‖ = ‖x‖) : ∃ L : H ≃ₗᵢ[ℝ] H', ∀ x, L x = U x := by
  let L₀ : H →ₗᵢ[ℝ] H' :=
    { toFun := U
      map_add' := hadd
      map_smul' := fun r x => by
        rw [← Complex.coe_smul, hs, cjc_ofReal, Complex.coe_smul, RingHom.id_apply]
      norm_map' := hn }
  exact ⟨LinearIsometryEquiv.ofSurjective L₀ hb.2, fun _ => rfl⟩

theorem inner_map (hadd : ∀ x y, U (x + y) = U x + U y) (hs : ∀ (z : ℂ) x, U (z • x) = cjc cj z • U x)
    (hn : ∀ x, ‖U x‖ = ‖x‖) (w x : H) : ⟪U w, U x⟫_ℂ = cjc cj ⟪w, x⟫_ℂ := by
  have hre : ∀ w x : H, (⟪U w, U x⟫_ℂ).re = (⟪w, x⟫_ℂ).re := fun w x => by
    have h1 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) (U w) (U x)
    have h2 := re_inner_eq_norm_add_mul_self_sub_norm_mul_self_sub_norm_mul_self_div_two (𝕜 := ℂ) w x
    rw [← hadd, hn, hn, hn, ← h2] at h1
    exact h1
  have h1 := hre w x
  have h2 := hre w (Complex.I • x)
  rw [hs, inner_smul_right, inner_smul_right] at h2
  cases cj
  · apply Complex.ext <;> simp_all [cjc]
  · apply Complex.ext
    · simp only [cjc, if_true, Complex.conj_re]
      exact h1
    · simp only [cjc, if_true, Complex.conj_im] at h2 ⊢
      simpa using h2

end Semi

theorem isFormIso_phi {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) (br : Bool) :
    IsFormIso ε (phi br e) := by
  cases br
  · exact isFormIso_plainMat h
  · exact isFormIso_barMat h

theorem exists_kTie : ∀ (D : D7) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S) (τ : D.what₂.Tau) (p q : ℕ) (T : GrpData p q) (R : DSRep T) (lam : Ix p q → ℚ) (c : ℚ) (br cj : Bool) (e : Ix p q ≃ Fin V.rank) (m : ℤ) (U : M.H τ → R.U.H), IsParam lam → IsOrd (M.ε τ) (M.lam τ) lam c (sg br cj) e → (m : ℚ) = 2 * c → Comparison₂ R M τ br cj e m U → (∀ x v, U x = R.ι v → (IsHighestUnit (M.ε τ) (M.lam τ) (M.σ τ) x ↔ UnitHW R (blattner lam) v)) → ∃ u, KTie R M τ lam c br cj e u := by
  intro D V S M τ p q T R lam c br cj e m U hpar hord hm hT hhi
  have hφ := isFormIso_phi hord.1 br
  obtain ⟨L, hL⟩ := exists_real hT.add hT.smul hT.bij hT.norm
  have hr : ∀ v : kfin M τ, ∃ y, R.ι y = U v := by
    rintro ⟨v, hv⟩
    change U v ∈ LinearMap.range R.ι
    induction hv using Submodule.span_induction with
    | mem x hx => exact (hT.kfin x).1 hx
    | zero => rw [← hL, map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [hT.add]; exact add_mem hx hy
    | smul z x _ hx => rw [hT.smul]; exact Submodule.smul_mem _ _ hx
  choose u hu using hr
  have hmC : (m : ℂ) = 2 * (c : ℂ) := by exact_mod_cast hm
  have hgrp : ∀ (g : T.G) (x : M.H τ), U (M.σ τ (phi br e ((T.cov g : GL (Ix p q) ℂ) : Mat p q)) x) =
      ((T.sq g : ℂˣ) : ℂ) ^ m • R.U.π g (U x) := fun g x => by
    rw [hT.grp, smul_smul, ← zpow_add₀ (Units.ne_zero _), add_neg_cancel, zpow_zero, one_smul]
  refine ⟨u, hpar, hord, fun x y => R.ι_inj ?_, fun z x => R.ι_inj ?_, ⟨fun x y h => ?_, fun y => ?_⟩, ?_,
    fun Z hZ v v' => ?_, fun v => hhi _ _ (hu v).symm, fun m' hm' g v w => ?_⟩
  · rw [map_add (f := _), hu, hu, hu, Submodule.coe_add, hT.add]
  · rw [map_smul, hu, hu, Submodule.coe_smul, hT.smul]
  · exact Subtype.ext (hT.bij.1 (by rw [← hu, ← hu, h]))
  · obtain ⟨x, hx⟩ := hT.bij.2 (R.ι y)
    exact ⟨⟨x, Submodule.subset_span ((hT.kfin x).2 ⟨y, hx.symm⟩)⟩, R.ι_inj (by rw [hu]; exact hx)⟩
  · change (fun Z => toFrame M τ (phi br e Z)) '' _ = _
    rw [← toFrame_image M τ, ← Set.image_image (toFrame M τ) (phi br e)]
    congr 1
    ext Y
    obtain ⟨Z, rfl⟩ := hφ.bij.2 Y
    rw [hφ.bij.1.mem_set_image, ← hφ.mem_lie]
    rfl
  · have h1 := (hasDerivAt_sq_zpow T m hZ).fun_smul (R.der Z hZ (u v))
    have h2 : HasDerivAt (fun t : ℝ => L (M.rep τ (NormedSpace.exp (t • phiFr (M.fr τ) br e Z)) (v : M.H τ)))
        (R.ι (R.HK.act Z (u v) + ((c : ℂ) * Z.trace) • u v)) 0 := by
      convert (preTransparency := .reducible) h1 using 1
      · funext t
        have h3 := rep_exp M τ (phi br e Z) t
        rw [hL, show phiFr (M.fr τ) br e Z = toFrame M τ (phi br e Z) from rfl, h3, hφ.exp,
          ← T.expt_cov _ (GlobalTheory.RealPar.KStabLie.smul_mem_upq hZ t), hgrp, hu]
      · rw [hmC, show 2 * (c : ℂ) * (Z.trace / 2) = c * Z.trace by ring]
        simp [T.expt_zero]
    constructor
    · intro h
      have h3 := L.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h
      refine R.ι_inj ?_
      rw [hu, ← hL]
      exact h3.unique h2
    · intro h
      rw [← h, hu, ← hL] at h2
      have h3 := L.symm.toContinuousLinearEquiv.toContinuousLinearMap.hasFDerivAt.comp_hasDerivAt (0 : ℝ) h2
      unfold VecDer
      convert h3 using 1
      · funext t; simp
      · simp
  · obtain rfl : m' = m := by exact_mod_cast hm'.trans hm.symm
    rw [← inner_map hT.add hT.smul hT.norm, hgrp, inner_smul_right, hu, hu]

end GlobalTheory.ArchRec.KFiniteTie

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitarySpan
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.SpanMod

variable {r s : ℕ}

theorem exists_unitary_span (r s : ℕ) (W U I : Type) [AddCommGroup W] [Module ℂ W] [NormedAddCommGroup U]
    [InnerProductSpace ℂ U] (a : Mat r s →ₗ[ℂ] Module.End ℂ W) (b : Mat r s → Module.End ℂ U)
    (j : I → W →ₗ[ℂ] U) (ha : IsGK a) (hb : IsUAct b)
    (hj : ∀ i, ∀ Z ∈ upq r s, ∀ P, j i (a Z P) = b Z (j i P)) :
    ∃ (MM : UGKMod r s) (inc : MM.M.V →ₗ[ℂ] U), Function.Injective inc ∧
      LinearMap.range inc = Submodule.span ℂ {y | ∃ i P, y = j i P} ∧
      ∀ Z ∈ upq r s, ∀ y, inc (MM.M.act Z y) = b Z (inc y) := by
  first
  | exact @_root_.GlobalTheory.RealPartAdjointAction.main
  | exact _root_.GlobalTheory.RealPartAdjointAction.main
  | (apply _root_.GlobalTheory.RealPartAdjointAction.main <;> assumption)
  | (intros; apply _root_.GlobalTheory.RealPartAdjointAction.main <;> assumption)
  | (intros; apply @_root_.GlobalTheory.RealPartAdjointAction.main <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.RealPartAdjointAction.main ..)

end GlobalTheory.ArchRec.SpanMod
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsZonalSphericalFunctionUnramifiedUnitary
section
open Formalism.UG (IsUnramInv GU KU Hecke dosetInd)

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists

open Formalism.UG

section Generic

variable {G : Type} [Group G] {K : Subgroup G}

def cosetsIn (K : Subgroup G) (g : G) : Set (G ⧸ K) := {x | ∃ a b : K, x.out = (a : G) * g * b}

theorem mem_cosetsIn_iff (x : G ⧸ K) (t : G) :
    x ∈ cosetsIn K t ↔ x.out ∈ DoubleCoset.doubleCoset t (K : Set G) K := by
  rw [DoubleCoset.mem_doubleCoset]
  exact ⟨fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩, fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩⟩

theorem cosetsIn_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    cosetsIn K g' = cosetsIn K g := by
  ext x
  rw [mem_cosetsIn_iff, mem_cosetsIn_iff, DoubleCoset.doubleCoset_eq_of_mem h]

theorem dosetInd_eq {g g' : G} (h : g' ∈ DoubleCoset.doubleCoset g (K : Set G) K) :
    dosetInd ℂ K g' = dosetInd ℂ K g := by
  rw [dosetInd, dosetInd, DoubleCoset.doubleCoset_eq_of_mem h]

theorem cosetsIn_ncard_ne_zero (hK : IsCommensurated K) (g : G) : (cosetsIn K g).ncard ≠ 0 := by
  refine ((Set.ncard_pos (P.finite_cosets_in_doset hK g)).2 ⟨(g : G ⧸ K), ?_⟩).ne'
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

theorem cosetsIn_one : cosetsIn K 1 = {((1 : G) : G ⧸ K)} := by
  ext x
  rw [Set.mem_singleton_iff]
  constructor
  · rintro ⟨a, b, e⟩
    rw [← QuotientGroup.out_eq' x, e]
    exact QuotientGroup.eq.2 (by simpa using K.inv_mem (K.mul_mem a.2 b.2))
  · rintro rfl
    refine ⟨⟨((1 : G) : G ⧸ K).out, ?_⟩, 1, by simp⟩
    have := QuotientGroup.eq.1 (QuotientGroup.out_eq' ((1 : G) : G ⧸ K))
    simpa using K.inv_mem this

end Generic

theorem exists_isZonal : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L] (ϖ : L)
    (σ : L →+* L) (q n : ℕ), IsUnramInv ϖ σ q → ∀ α : Fin (n / 2) → ℂˣ, ∃ w : GU σ n → ℂ,
      GlobalTheory.IndefiniteRowSideFullHecke.SphericalSectionVariables.IsZonal ϖ q α w := by
  intro L _ _ _ ϖ σ q n hU α
  classical
  have hK := P.isCommensurated_integral_unitary_of_unramified hU n
  have law := GlobalTheory.LFun.SatCompare.satU_laws (n := n) hU α
  have hN : ∀ g : GU σ n, ((cosetsIn (KU σ n) g).ncard : ℂ) ≠ 0 := fun g =>
    Nat.cast_ne_zero.2 (cosetsIn_ncard_ne_zero hK g)
  let w : GU σ n → ℂ := fun g =>
    SatU ϖ q (dosetInd ℂ (KU σ n) g) (fun i => (α i : ℂ)) / ((cosetsIn (KU σ n) g).ncard : ℂ)
  have hw : ∀ g g' : GU σ n, g' ∈ DoubleCoset.doubleCoset g (KU σ n : Set (GU σ n)) (KU σ n) → w g' = w g :=
    fun g g' h => by simp only [w, dosetInd_eq h, cosetsIn_eq h]
  refine ⟨w, fun a b g => hw _ _ (DoubleCoset.mem_doubleCoset.2 ⟨a, a.2, b, b.2, rfl⟩), ?_, fun h hh => ?_⟩
  · simp only [w, law.2.2, cosetsIn_one, Set.ncard_singleton, Nat.cast_one, div_one]
  refine GlobalTheory.LFun.hecke_induction (K := KU σ n)
    (p := fun f => hAct (KU σ n) f w 1 = SatU ϖ q f fun i => (α i : ℂ)) ?_ ?_ ?_ hh
  · simpa [hAct] using (law.2.1 0 0 (zero_mem _)).symm
  · intro f hf f' hf' e e'
    have fin : ∀ f ∈ Hecke ℂ (KU σ n), (Function.support fun x : GU σ n ⧸ KU σ n => f x.out • w (1 * x.out)).Finite :=
      fun f hf => (P.finite_support_cosets hK hf.2).subset fun x hx h0 => hx (by simp [h0])
    rw [law.1 _ hf _ hf', ← e, ← e', hAct, hAct, hAct]
    simp only [Pi.add_apply, add_smul]
    exact finsum_add_distrib (fin f hf) (fin f' hf')
  · intro r g
    have hfin := P.finite_cosets_in_doset hK g
    have hterm : ∀ x ∈ hfin.toFinset, (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = r * w g := fun x hx => by
      have hm := (mem_cosetsIn_iff x g).1 ((Set.Finite.mem_toFinset _).1 hx)
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_mem hm, one_mul, hw g _ hm]
      simp
    rw [law.2.1 r _ (Final.DosetIndMem _ _ ℂ g), hAct,
      finsum_eq_sum_of_support_subset (s := hfin.toFinset), Finset.sum_congr rfl hterm,
      Finset.sum_const, ← Set.ncard_eq_toFinset_card _ hfin, nsmul_eq_mul]
    · have := hN g
      simp only [w]
      rw [← cosetsIn]
      field_simp
    · intro x hx
      rw [Set.Finite.coe_toFinset]
      by_contra h
      refine hx ?_
      show (r • dosetInd ℂ (KU σ n) g) x.out • w (1 * x.out) = 0
      rw [Pi.smul_apply, dosetInd, Set.indicator_of_notMem (fun h' => h ((mem_cosetsIn_iff x g).2 h'))]
      simp

end GlobalTheory.IndefiniteRowSideFullHecke.ZonalExists
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableMatrixCoeffKAverageRight
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.FlagMeas GlobalTheory.GKModule GlobalTheory.RealInd GlobalTheory.OpTrace
open GlobalTheory.SmoothGlob (lieSet)
open GlobalTheory.Dec (IsHaarSub HasInfChar IsSqIntIrr)
open GlobalTheory.Orb (ujMat ujRep CcMat IsBiFinite IsUnitEquiv IsCharFn IsRegSS cent HasOrbInt quotMeas)
open GlobalTheory.AutomorphicL2Unitary (IsTopIrreducible)
open GlobalTheory.HCChar GlobalTheory.Published GlobalTheory.Published.Langlands
open scoped InnerProductSpace Topology ENNReal ComplexConjugate

noncomputable section

namespace GlobalTheory.AvgRightLp

end GlobalTheory.AvgRightLp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsDiscreteSeriesConjugateReverseContragredient
section
open Formalism.MainNotions.S GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec

theorem isDS_conj_rev : ∀ (n : ℕ) (ε : Fin n → Bool) (lam : Fin n → ℝ) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (σ : Mn n → (H →L[ℂ] H)), IsDS ε lam σ → IsDS (fun a => ε a.rev) (fun a => -lam a.rev) (fun g => σ ((g.map (starRingEnd ℂ)).submatrix Fin.rev Fin.rev)) :=
  fun _ _ _ _ _ _ _ hσ => GlobalTheory.CoverModel.isDS_barRev (fun _ => rfl) hσ

end GlobalTheory.ArchRec
end

