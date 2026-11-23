module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVector
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0495
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.PoitouTateNormalised
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0445
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0494
public import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormSqLeDominantRearrangement
section
noncomputable section

open Matrix Finset
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.DiracKType0

open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCount.InjHw GlobalTheory.CompanionTheory.DiracK

variable {n : ℕ}

theorem norm_sq_le_dominant_rearrangement (a : Fin n → ℝ) (π : Equiv.Perm (Fin n)) :
    Formalism.REAL.nsq (a + rhoV n ∘ π) ≤ nsq (domC a + rhoV n) := by
  set s : Equiv.Perm (Fin n) := Tuple.sort (fun i => -a i) with hs
  have hanti : Antitone (a ∘ s) := by
    intro i j hij
    have := Tuple.monotone_sort (fun i => -a i) hij
    simpa [Function.comp] using this
  have hρ : Antitone (rhoV n) := by
    intro i j hij
    simp only [rhoV]
    have : ((i : ℕ) : ℝ) ≤ (j : ℕ) := by exact_mod_cast hij
    linarith
  have hmv : Monovary (a ∘ s) (rhoV n) := hanti.monovary hρ
  have hr := hmv.sum_mul_comp_perm_le_sum_mul (σ := s.trans π)
  have e1 : ∑ i, a i ^ 2 = ∑ i, (a ∘ s) i ^ 2 := (Equiv.sum_comp s (fun i => a i ^ 2)).symm
  have e2 : ∑ i, rhoV n (π i) ^ 2 = ∑ i, rhoV n i ^ 2 := Equiv.sum_comp π (fun i => rhoV n i ^ 2)
  have e3 : ∑ i, a i * rhoV n (π i) = ∑ i, (a ∘ s) i * rhoV n ((s.trans π) i) :=
    (Equiv.sum_comp s (fun i => a i * rhoV n (π i))).symm
  have l : Formalism.REAL.nsq (a + rhoV n ∘ π) =
      ∑ i, a i ^ 2 + 2 * ∑ i, a i * rhoV n (π i) + ∑ i, rhoV n (π i) ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, Function.comp, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have r : nsq (domC a + rhoV n) =
      ∑ i, (a ∘ s) i ^ 2 + 2 * ∑ i, (a ∘ s) i * rhoV n i + ∑ i, rhoV n i ^ 2 := by
    simp only [nsq, domC, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by
      simp only [hs, Function.comp]
      ring
  rw [l, r, e1, e2, e3]
  linarith

theorem dirac_ineq0 : ∀ {n : ℕ} (lam : Fin n → ℤ) (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (E1 E2 : Fin n → Fin n → Module.End ℂ V) (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)),
    IsCoreMod0 (infOf lam) E1 E2 σ → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (c : Fin n → Fin n → Matrix ι ι ℂ),
      IsCliff c → ∀ (τ : Fin n → ℝ) (x : ι → V), x ≠ 0 → Formalism.REAL.KHighest (fun _ => true) (yF (kF E1 E2) c) τ x →
        ∑ a, (m0 lam a) ^ 2 ≤ ∑ a, (τ a + rhoV n a) ^ 2 := by
  intro n lam V _ _ E1 E2 σ h ι _ _ c hc τ x hx hK
  obtain ⟨hc1, hc2⟩ := hc
  have hcl : IsCliff c := ⟨hc1, hc2⟩
  have hp := h.pair

  set L := lft (V := V) ι with hL
  set Rr := rgt (ι := ι) V with hRr
  set p : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (pF E1 E2 a b) with hpdef
  set k : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => L (kF E1 E2 a b) with hkdef
  set g : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (c a b) with hgdef
  set s : Fin n → Fin n → Module.End ℂ (ι → V) := fun a b => Rr (spinM c a b) with hsdef
  set D := dirac (pF E1 E2) c with hD
  have hDe : D = ∑ a, ∑ b, p a b * g b a := rfl
  have hks : ∀ a b c' d, k a b * s c' d = s c' d * k a b := fun a b c' d => lft_mul_rgt _ _
  have hglK : Formalism.REAL.GlRel (kF E1 E2) := glRel_add E1 E2 hp.gl1 hp.gl2 hp.comm
  have hGk : Formalism.REAL.GlRel k := glRel_map L.toRingHom hglK
  have hGs : Formalism.REAL.GlRel s := glRel_map Rr.toRingHom (spinM_glRel c hcl)
  have hYe : yF (kF E1 E2) c = fun a b => k a b + s a b := by
    funext a b
    exact yF_eq _ _ a b
  have hGY : Formalism.REAL.GlRel (yF (kF E1 E2) c) := by
    rw [hYe]
    exact glRel_add k s hGk hGs hks
  have hCY := Formalism.REAL.compactCasimirOnHighestWeight_holds (ι → V) n (fun _ => true) _ τ x hGY hK
  have hCK : Formalism.REAL.CasK (fun _ : Fin n => true) (yF (kF E1 E2) c) = Formalism.REAL.Cas (yF (kF E1 E2) c) := by
    simp [Formalism.REAL.CasK, Formalism.REAL.Cas]
  rw [hCK, rhoC_true] at hCY

  have hg : ∀ a b d e, g a b * g d e + g d e * g a b = if a = e ∧ b = d then (2 : ℂ) • (1 : Module.End ℂ (ι → V)) else 0 := by
    intro a b d e
    have h1 := congrArg Rr (cliff_hg hcl a b d e)
    simp only [map_add (f := _), map_mul] at h1
    rw [show g a b * g d e + g d e * g a b = Rr (c a b) * Rr (c d e) + Rr (c d e) * Rr (c a b) from rfl, h1]
    split_ifs
    · rw [map_smul, map_one]
    · exact map_zero Rr
  have hpp : ∀ a b c' d, p a b * p c' d - p c' d * p a b =
      (if b = c' then k a d else 0) - (if d = a then k c' b else 0) := by
    intro a b c' d
    have h1 := congrArg L (bracket_p E1 E2 hp.gl1 hp.gl2 hp.comm a b c' d)
    simp only [map_sub, map_mul] at h1
    have h2 : p a b * p c' d - p c' d * p a b = L (E1 a b - E2 a b) * L (E1 c' d - E2 c' d) -
        L (E1 c' d - E2 c' d) * L (E1 a b - E2 a b) := rfl
    rw [h2]
    simp only [map_sub]
    rw [h1]
    by_cases h5 : b = c' <;> by_cases h6 : d = a <;> simp [h5, h6, hkdef, kF]
  have hsq := dirac_sq_ring p k g hg hpp (fun a b c' d => lft_mul_rgt _ _)
  have hsE : ∀ d a, ((1 / 2 : ℂ) • ∑ e, g d e * g e a - if d = a then ((n : ℂ) / 2) • (1 : Module.End ℂ (ι → V)) else 0) =
      s d a := by
    intro d a
    have : s d a = Rr (spinM c d a) := rfl
    rw [this]
    unfold spinM
    by_cases h1 : d = a <;> simp [h1, map_sub, map_smul, map_sum, map_mul, hgdef]
  simp only [hsE] at hsq
  rw [← hDe] at hsq
  have hCasY := cas_add k s hks
  rw [← hYe] at hCasY
  have hCasP : (∑ a, ∑ b, p a b * p b a) + Formalism.REAL.Cas k =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) := by
    have h1 := congrArg L (cas_p_add_k E1 E2)
    simp only [two_mul] at h1
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Formalism.REAL.Cas, map_add (f := _), map_sum, map_mul, hpdef, hkdef, pF, kF]
  have hCasS : Formalism.REAL.Cas s = (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    have h1 := congrArg Rr (spinM_cas c hcl)
    simp only [map_smul, map_one] at h1
    rw [← h1]
    set_option synthInstance.maxHeartbeats 100000 in
      simp [Formalism.REAL.Cas, map_sum, map_mul, hsdef]
  have hTot : D * D + Formalism.REAL.Cas (yF (kF E1 E2) c) =
      L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) +
        (((n : ℂ) ^ 3 - n) / 4) • (1 : Module.End ℂ (ι → V)) := by
    rw [← hCasP, ← hCasS, hsq, hCasY]
    abel

  set R : ℝ := ∑ a, (rhoV n a) ^ 2 with hR
  set S : ℝ := (∑ a, (m0 lam a) ^ 2) / 4 with hS
  have hv : ∀ b : Bool, GlobalTheory.Dec.gelfVal (infOf lam b) 2 = ((S - R : ℝ) : ℂ) := by
    intro b
    rw [gelfVal_two_eq, infOf_sq, Complex.ofReal_sub, hS, hR]
    push_cast
    rfl
  have hC1 : ∀ v : V, Formalism.REAL.Cas E1 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_two, h.ch1 2 v, hv]
  have hC2 : ∀ v : V, Formalism.REAL.Cas E2 v = ((S - R : ℝ) : ℂ) • v := by
    intro v
    rw [← gelA_bar_two, h.ch2 2 v, hv]
  have hn : (((n : ℂ) ^ 3 - n) / 4) = ((3 * R : ℝ) : ℂ) := by
    rw [hR, sum_rhoV_sq]
    push_cast
    ring
  set T : ℝ := Formalism.REAL.nsq (τ + rhoV n) - Formalism.REAL.nsq (rhoV n) with hT
  have hDD : D (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := by
    have h1 := congrArg (fun f : Module.End ℂ (ι → V) => f x) hTot
    simp only [LinearMap.add_apply, Module.End.mul_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
    rw [hCY] at h1
    have h2 : L (Formalism.REAL.Cas E1 + Formalism.REAL.Cas E1 + (Formalism.REAL.Cas E2 + Formalism.REAL.Cas E2)) x =
        ((4 * (S - R) : ℝ) : ℂ) • x := by
      funext i
      simp only [hL, lft_apply, LinearMap.add_apply, hC1, hC2, Pi.smul_apply]
      push_cast
      module
    rw [h2, hn] at h1
    rw [eq_sub_of_add_eq h1]
    push_cast
    module

  have hsk := dirac_skew (pF E1 E2) c hp.unitP hc2 x (D x)
  have hN : 0 < ∑ i, ‖x i‖ ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hx
    exact Finset.sum_pos' (fun _ _ => by positivity) ⟨i, Finset.mem_univ _, by
      have : x i ≠ 0 := hi
      positivity⟩
  have hM : 0 ≤ ∑ i, ‖D x i‖ ^ 2 := Finset.sum_nonneg fun _ _ => by positivity
  have hEq : ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) = -(((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
    have e1 : ∑ i, ⟪dirac (pF E1 E2) c x i, D x i⟫_ℂ = ((∑ i, ‖D x i‖ ^ 2 : ℝ) : ℂ) := by
      push_cast
      exact Finset.sum_congr rfl fun i _ => by
        rw [inner_self_eq_norm_sq_to_K]
        rfl
    have e2 : ∑ i, ⟪x i, dirac (pF E1 E2) c (D x) i⟫_ℂ =
        (((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2 : ℝ) : ℂ) := by
      have : dirac (pF E1 E2) c (D x) = ((4 * (S - R) + 3 * R - T : ℝ) : ℂ) • x := hDD
      rw [this]
      push_cast
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by
        rw [Pi.smul_apply, inner_smul_right, inner_self_eq_norm_sq_to_K]
        push_cast
        rfl
    rw [← e1, hsk, e2]
  have hEq' : (∑ i, ‖D x i‖ ^ 2) = -((4 * (S - R) + 3 * R - T) * ∑ i, ‖x i‖ ^ 2) := by
    exact_mod_cast hEq
  have hle : 4 * (S - R) + 3 * R - T ≤ 0 := by
    by_contra hcon
    push_neg at hcon
    have := mul_pos hcon hN
    linarith
  have hT' : T = ∑ a, (τ a + rhoV n a) ^ 2 - R := by
    rw [hT, hR]
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot, Pi.add_apply, pow_two]
  rw [hT'] at hle
  have : ∑ a, (m0 lam a) ^ 2 = 4 * S := by
    rw [hS]
    ring
  rw [this]
  linarith

theorem dirac_inequality_k_types : DiracInequalityWithoutSplitComponent := by
  intro n lam _ V _ _ E1 E2 σ hc ν hν
  obtain ⟨x, hxh, hx⟩ := (Submodule.ne_bot_iff _).1 hν
  obtain ⟨S, hfd, hvS, -, hKS, -⟩ := hc.der.2 x
  have hGl : Formalism.REAL.GlRel (kF E1 E2) := GlobalTheory.CompanionTheory.RealMult.DiracProof.kF_gl hc.pair
  have hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) ν x := hxh
  have hint : ∀ a, ∃ m : ℤ, ν a = m := fun a =>
    GlobalTheory.CompanionTheory.RealMult.DiracProof.weight_int hc.der a (ν a) hx (hK.1 a)
  choose m hm using hint
  have hνm : wtR m = ν := by
    funext a
    exact (hm a).symm
  obtain ⟨ι, i1, i2, c, hcl, hconds⟩ := _root_.GlobalTheory.CompanionTheory.SpinPRV.spin_parthasarathy_rao_varadarajan n
  have hK' : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR m) x := by rwa [hνm]
  obtain ⟨w, -, y, hy, hyh⟩ := hconds V (kF E1 E2) S m x hGl hc.pair.unitK hfd hKS hvS hx hK'
  have hn := dirac_ineq0 lam V E1 E2 σ hc ι c hcl _ y hy hyh
  rw [hνm] at hn
  have e1 : LSq lam = ∑ a, (m0 lam a) ^ 2 := by
    simp only [LSq, nsq, m0, rhoV]
    exact Finset.sum_congr rfl fun a _ => by ring
  have e2 : Formalism.REAL.nsq (ν - rhoV n + rhoV n ∘ w.symm) = ∑ a, (ν (w a) - rhoV n (w a) + rhoV n a) ^ 2 := by
    simp only [Formalism.REAL.nsq, Formalism.REAL.dot]
    rw [← Equiv.sum_comp w]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [Pi.add_apply, Pi.sub_apply, Function.comp, Equiv.symm_apply_apply]
    ring
  rw [e1]
  have h3 := norm_sq_le_dominant_rearrangement (ν - rhoV n) w.symm
  rw [e2] at h3
  exact hn.trans h3

end GlobalTheory.CompanionTheory.DiracKType0
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.NormalisedLocalInvariantExists
section
open NumberField IsDedekindDomain Representation Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.Published GlobalTheory.Published.PoitouTate

namespace GlobalTheory.CompanionTheory.LocalInvariant

theorem exists_bijective_isNormalised :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ)
      [Fact l.Prime] (r : ℕ), 0 < r → ∀ ζ : Ω, IsPrimitiveRoot ζ (l ^ r) →
      ∀ (A : ValuationSubring Ω) (v : HeightOneSpectrum (𝓞 F)), IsPlaceOver A v →
      ∃ f : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r),
        Function.Bijective f ∧ IsNormalised ζ A v f := by
  intro F Ω _ _ _ _ _ l _ r hr ζ hζ A v hA
  obtain ⟨e⟩ := _root_.GlobalTheory.CompanionTheory.LocalInv.nonempty_H2_muLoc_equiv_zmod F Ω l r hr A v hA
  by_cases hN : IsNormalised ζ A v (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r))
  · exact ⟨e, e.bijective, hN⟩
  · simp only [IsNormalised, not_forall] at hN
    obtain ⟨ϖ, y, κ, χ, z, h1, h2, h3, h4, h5, h6, h7, h8, -⟩ := hN
    have hgen := GlobalTheory.T.local_invariant_cup_uniformizer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
    set c : H2 (muLoc F l r A) := Submodule.Quotient.mk z with hc

    obtain ⟨a, ha⟩ : ∃ a : ZMod (l ^ r), a * e c = 1 := by
      have hmem : e.symm 1 ∈ Submodule.span (ZMod (l ^ r)) {c} := by
        rw [hgen]; trivial
      obtain ⟨a, hac⟩ := Submodule.mem_span_singleton.1 hmem
      refine ⟨a, ?_⟩
      have := congrArg e hac
      simpa using this
    have ha' : e c * a = 1 := by rw [mul_comm]; exact ha
    refine ⟨a • (e : H2 (muLoc F l r A) →ₗ[ZMod (l ^ r)] ZMod (l ^ r)), ⟨?_, ?_⟩, ?_⟩
    · intro x x' hxx
      have hxx' : a * e x = a * e x' := by simpa using hxx
      apply e.injective
      calc e x = e c * (a * e x) := by rw [← mul_assoc, ha', one_mul]
        _ = e c * (a * e x') := by rw [hxx']
        _ = e x' := by rw [← mul_assoc, ha', one_mul]
    · intro t
      refine ⟨e.symm (e c * t), ?_⟩
      simp [← mul_assoc, ha]
    · intro ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      have hz := GlobalTheory.T.local_invariant_cup_kummer F Ω l r hr ζ hζ A v hA ϖ y κ χ z h1 h2 h3 h4 h5 h6 h7 h8
        ϖ' y' κ' χ' z' g1 g2 g3 g4 g5 g6 g7 g8
      rw [← hz]
      simpa using ha

end GlobalTheory.CompanionTheory.LocalInvariant
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientRankZero
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.PcZero

theorem blockMatrix_zero {R : Type} [Zero R] {p : ℕ} (hn : 0 + p = p) (a : Matrix (Fin 0) (Fin 0) R)
    (b : Matrix (Fin 0) (Fin p) R) (c : Matrix (Fin p) (Fin 0) R) : bl hn a b c 0 = 0 := by
  ext i j
  obtain ⟨i, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective i
  obtain ⟨j, rfl⟩ := (finSumFinEquiv.trans (finCongr hn)).surjective j
  rcases i with i | i
  · exact i.elim0
  rcases j with j | j
  · exact j.elim0
  simp only [bl, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply]

theorem nzx_eq_one {D : D7} {p : ℕ} {hn : 0 + p = p} (M : Maps D hn) (z : hermA D 0) (x : Mx D 0 p) :
    M.nzx z x = 1 := by
  apply Subtype.ext
  apply Units.ext
  have h : mat (M.nzx z x) = 1 := by
    rw [M.nzx_mat, blockMatrix_zero]
    unfold blk4
    rw [Matrix.fromBlocks_one, Matrix.submatrix_one_equiv]
  exact h

theorem chz_eq_one {D : D7} (ψ : AddChar (AF D.host.F) ℂ) (b₀ : HermE D 0) (z : hermA D 0) : chz ψ b₀ z = 1 := by
  unfold chz halfTr trA
  simp [Matrix.trace]

theorem zc_eq {D : D7} {p : ℕ} {hn : 0 + p = p} (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ)
    (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p) : zc M m ψ b₀ F g = F g := by
  unfold zc
  simp only [nzx_eq_one, chz_eq_one, one_mul, map_one, mul_one]
  rw [setIntegral_const, Measure.real, m.hz.2.2]
  simp

theorem pc_eq : ∀ (D : D7) (p : ℕ) (hn : 0 + p = p) (M : Maps D hn) (m : Meas D 0 p) (ψ : AddChar (AF D.host.F) ℂ)
    (b₀ : HermE D 0) (F : G D p → ℂ) (g : G D p), pc M m ψ b₀ F g = F g := by
  intro D p hn M m ψ b₀ F g
  unfold PositivityTheory.Rg.Rsw.pc
  simp only [zc_eq, nzx_eq_one, one_mul]
  rw [setIntegral_const, Measure.real, m.hμ.2.2]
  simp

end GlobalTheory.CompanionTheory.PcZero

end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PartialCoefficientUniformLimit
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct Topology
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC PositivityTheory.PfSWUS PositivityTheory.Rg.Rsw
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.FJLim

theorem fj_tendsto : PcBound → ∀ (D : D7) (n ρ p : ℕ) (hn : ρ + p = n) (M : Maps D hn) (m : Meas D ρ p) (ψ : AddChar (AF D.host.F) ℂ), IsCharAF D.host.F ψ → ∀ (b₀ : HermE D ρ) {ι : Type} (l : Filter ι) (Fs : ι → G D n → ℂ) (A : G D n → ℂ), Continuous A → LeftInv (GF D n) A → (∀ᶠ i in l, Continuous (Fs i) ∧ LeftInv (GF D n) (Fs i)) → (∀ C : Set (G D n), IsCompact C → ∀ ε : ℝ, 0 < ε → ∀ᶠ i in l, ∀ c ∈ C, ‖Fs i c - A c‖ ≤ ε) → (∀ᶠ i in l, ∀ (y : Mx D ρ p) (g : G D n), pc M m ψ b₀ (Fs i - A) (M.sh y * g) = pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) → ∀ (g : G D n) (φ : Mx D ρ p → ℂ), Integrable φ m.μ → Tendsto (fun i => FJ M m ψ b₀ (Fs i) g φ) l (𝓝 (FJ M m ψ b₀ A g φ)) := by
  intro hPc D n ρ p hn M m ψ hψ b₀ ι l Fs A hAc hAinv hFs hunif hadd g φ hφ
  haveI : BorelSpace (Mx D ρ p) := ⟨rfl⟩
  obtain ⟨hcont, hbd⟩ := hPc D n ρ p hn M m ψ hψ b₀
  obtain ⟨C, hC, -, hCb⟩ := hbd g
  have hφc : Integrable (fun y => conj (φ y)) m.μ := Complex.conjCLE.toContinuousLinearMap.integrable_comp hφ
  have hint : ∀ F : G D n → ℂ, Continuous F → LeftInv (GF D n) F →
      Integrable (fun y => pc M m ψ b₀ F (M.sh y * g) * conj (φ y)) m.μ := by
    intro F hF hinv
    obtain ⟨B, hB⟩ := hC.exists_bound_of_continuousOn hF.continuousOn
    have hc : Continuous fun y => pc M m ψ b₀ F (M.sh y * g) :=
      (hcont F hF hinv).comp (M.sh_cont.mul continuous_const)
    exact hφc.bdd_mul hc.aestronglyMeasurable (Eventually.of_forall fun y => hCb F hF hinv B hB y)
  rw [Metric.tendsto_nhds]
  intro ε hε
  set N : ℝ := ∫ y, ‖φ y‖ ∂m.μ with hN
  have hN0 : 0 ≤ N := integral_nonneg fun _ => norm_nonneg _
  have hδ : 0 < ε / (N + 1) := by positivity
  filter_upwards [hFs, hadd, hunif C hC _ hδ] with i hi hai hui
  have hsub : Continuous (Fs i - A) := hi.1.sub hAc
  have hsinv : LeftInv (GF D n) (Fs i - A) := fun γ hγ x => by
    simp only [Pi.sub_apply, hi.2 γ hγ x, hAinv γ hγ x]
  have hpt : ∀ y, ‖pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)‖ ≤ ε / (N + 1) := by
    intro y
    rw [← hai y g]
    exact hCb _ hsub hsinv _ (fun c hc => by simpa using hui c hc) y
  have hdiff : FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ =
      ∫ y, (pc M m ψ b₀ (Fs i) (M.sh y * g) - pc M m ψ b₀ A (M.sh y * g)) * conj (φ y) ∂m.μ := by
    unfold FJ
    rw [← integral_sub (hint _ hi.1 hi.2) (hint _ hAc hAinv)]
    simp only [sub_mul]
  have hle : ‖FJ M m ψ b₀ (Fs i) g φ - FJ M m ψ b₀ A g φ‖ ≤ ε / (N + 1) * N := by
    rw [hdiff, hN, ← integral_const_mul]
    refine norm_integral_le_of_norm_le (hφ.norm.const_mul _) (Eventually.of_forall fun y => ?_)
    rw [norm_mul, RCLike.norm_conj]
    exact mul_le_mul_of_nonneg_right (hpt y) (norm_nonneg _)
  rw [dist_eq_norm]
  refine lt_of_le_of_lt hle ?_
  rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
  nlinarith

end GlobalTheory.CompanionTheory.FJLim
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.PeriodizationIntegralUnfolding
section
noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.EC GlobalTheory.CompanionTheory.EisUnfold
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CompanionTheory.EisUnfold.Lattice

theorem tsum_setIntegral_sub_rat : ∀ (D : D7) (m r : ℕ) (μr : Measure (Mx D m r)) (𝓕r : Set (Mx D m r)), IsCovolOne (ratMx D m r) μr 𝓕r →
    ∀ f : Mx D m r → ℂ, Continuous f → ∀ B : ℝ≥0, (∀ y, ∑' p : Matrix (Fin m) (Fin r) D.host.E, ‖f (y - rat p)‖ₑ ≤ B) →
      Integrable f μr ∧ ∑' p : Matrix (Fin m) (Fin r) D.host.E, ∫ y in 𝓕r, f (y - rat p) ∂μr = ∫ t, f t ∂μr := by
  intro D m r μr 𝓕r h f hf B hB
  obtain ⟨hHaar, hFD, hvol⟩ := h
  haveI := hHaar
  haveI : BorelSpace (Mx D m r) := ⟨rfl⟩
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.toEquiv.symm
  haveI : Countable (Matrix (Fin m) (Fin r) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin r → D.host.E))
  have hinc : Function.Injective (Formalism.L2.Theta.incA D) := by
    have h0 : Function.Injective (algebraMap ↥D.host.F (AF ↥D.host.F)) :=
      NumberField.AdeleRing.algebraMap_injective _ _
    exact Algebra.TensorProduct.includeRight_injective h0
  have hmem : ∀ p : Matrix (Fin m) (Fin r) D.host.E, rat p ∈ ratMx D m r :=
    fun p => AddMonoidHom.mem_range.mpr ⟨p, rfl⟩
  obtain ⟨e, he⟩ : ∃ e : Matrix (Fin m) (Fin r) D.host.E ≃ ratMx D m r,
      ∀ p, ((e p : ratMx D m r) : Mx D m r) = rat p := by
    refine ⟨Equiv.ofBijective (fun p => ⟨rat p, hmem p⟩) ⟨fun p q hpq => ?_, fun g => ?_⟩, fun p => rfl⟩
    · have h2 : p.map (Formalism.L2.Theta.incA D) = q.map (Formalism.L2.Theta.incA D) :=
        congrArg Subtype.val hpq
      exact Matrix.map_injective hinc h2
    · obtain ⟨p, hp⟩ := AddMonoidHom.mem_range.mp g.2
      exact ⟨p, Subtype.ext hp⟩
  haveI : Countable (ratMx D m r) := Countable.of_equiv _ e
  haveI : VAddInvariantMeasure (ratMx D m r) (Mx D m r) μr :=
    ⟨fun c s _ => measure_preimage_add μr (c : Mx D m r) s⟩
  have hv : ∀ (p : Matrix (Fin m) (Fin r) D.host.E) (x : Mx D m r), -(e p) +ᵥ x = x - rat p := by
    intro p x
    change ((-(e p) : ratMx D m r) : Mx D m r) + x = x - rat p
    rw [AddSubgroup.coe_neg, he]
    exact neg_add_eq_sub (rat p) x
  haveI : ContinuousSub (Mx D m r) := IsTopologicalAddGroup.to_continuousSub
  have hmeas : ∀ p : Matrix (Fin m) (Fin r) D.host.E, Measurable (fun x => ‖f (x - rat p)‖ₑ) :=
    fun p => (hf.comp (continuous_id.sub continuous_const)).measurable.enorm
  have hlin : ∫⁻ x, ‖f x‖ₑ ∂μr ≤ B := by
    rw [hFD.lintegral_eq_tsum', ← e.tsum_eq]
    simp_rw [hv]
    rw [← lintegral_tsum (fun p => (hmeas p).aemeasurable)]
    calc ∫⁻ x in 𝓕r, ∑' p, ‖f (x - rat p)‖ₑ ∂μr ≤ ∫⁻ _ in 𝓕r, (B : ℝ≥0∞) ∂μr :=
          lintegral_mono fun x => hB x
      _ = B := by rw [lintegral_const, Measure.restrict_apply_univ, hvol, mul_one]
  have hint : Integrable f μr := ⟨hf.aestronglyMeasurable, lt_of_le_of_lt hlin ENNReal.coe_lt_top⟩
  refine ⟨hint, ?_⟩
  rw [hFD.integral_eq_tsum' f hint, ← e.tsum_eq]
  simp_rw [hv]

end GlobalTheory.CompanionTheory.EisUnfold.Lattice
end
end

