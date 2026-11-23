module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.AbsoluteConvergence.Bundle0012
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacDataOf

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacCore
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem genAt (hG : AbsSt.GenCore) (c : ℂ) (hT : TAll) (hAux : AuxiliaryPrimeFunction) (hFM : FockMem) (hLo : LocOpEx)
    (hLI : LocInst) (hGS : GSplit) (hGI : GIinv) (hGD : GIdil) (hPK : PolyKFin) (hSK : SecK) (hEW : EisWk)
    (d : SD σ) (R : RD d) (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w)
    {φ : PX d.m d.n →ₗ[ℂ] d.Fn} (hφ : R.IsLift w Ψ φ)
    (hvac : ∀ x, HolValueAt (fun z => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ 1) x))
    (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ P) x) := by
  have hEA := eisAll_of hSK hEW d
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, -, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (om_mem d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← Tl_apply, map_sub, Tl_apply, Tl_apply, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => c • d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _), I_add d hTT hTA (hφ P).1 (hφ Q).1, smul_add]
      map_smul' := fun a P => by rw [map_smul, I_smul d hTT a (hφ P).1, RingHom.id_apply, smul_comm] }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (secl d).comp φ
  obtain ⟨-, -, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hCore : AbsSt.GlobCore (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n)
      d.Ht sl Il :=
    { ιcont := R.cont w
      split := by
        intro g
        obtain ⟨x, y, c, r, hr, hg, hx⟩ := hGS F E σ d R w L hL Ψ hΨ φ hφ g
        refine ⟨x, y, c, r, hr, hg, fun y' => ⟨(hx y').1, fun P => ?_⟩⟩
        rw [hsL]
        exact (hx y').2 P
      Icont := by
        show Continuous (c • d.I (φ 1))
        exact ((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.1.const_smul c
      Ileft := by
        intro γ hγ g
        show c * d.I (φ 1) (γ * g) = c * d.I (φ 1) g
        rw [((hTA F E σ d).2.2 (φ 1) (hφ 1).1).2.2 γ hγ g]
      Ik := by
        intro P g k hk
        show c * thetaMean d.om d.S d.μ d.D (φ P) (g * R.ι w k) = c * thetaMean d.om d.S d.μ d.D (φ (ρ k P)) g
        unfold thetaMean
        simp only [map_mul, Module.End.mul_apply, (hTT F E σ d (φ P) (hφ P).1).2, hom k hk P]
      Iinv := by
        intro g a b P
        show c * d.I (φ (hOp (fun _ => true) (2 * Real.pi) a b P)) g = 0
        rw [hGI F E σ d R w Ψ hΨ φ hφ g a b P, mul_zero]
      Idil := by
        intro g X a ha
        obtain ⟨U, H, hU, hR, hc, hH⟩ := hGD F E σ d R w Ψ hΨ φ hφ g X a ha
        refine ⟨U, fun y z => c * H y z, hU, hR, continuousOn_const.mul hc,
          fun y => ⟨(hH y).1.const_mul c, fun t => ?_, fun r => ?_⟩⟩
        · show c * H y t = c * d.I (φ 1) (g * R.ι w (y * a t))
          rw [(hH y).2.1 t]
        · show iteratedDeriv r (fun z => c * H y z) 0 = c * d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y)
          rw [iteratedDeriv_const_mul' c r (H y)]
          show c * iteratedDeriv r (H y) 0 = _
          rw [(hH y).2.2 r]
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ }
  have hVac : AbsSt.VacData (par2 σ d.Y) (rat2 σ d.Y) (s0 d.m d.n) d.Ht sl Il := by
    obtain ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩ := vacData_of (fun z g => d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z g)
      (s0 d.m d.n) (fun g => c * d.I (φ 1) g) U pp Ê t hUo hRD hs0 hp hhol hcont (fun z hz g => (hconv z hz).2 g)
      hvac
    exact ⟨r, Fv, hr, hFc, hFd, hF0, hFv⟩
  exact hG d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il hCore hVac P x

end PositivityTheory.SiegelWeilFormula.Atop

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.VacLin
section
noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Atop

open PositivityTheory.SiegelWeilFormula.KMain

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem cosetSum_const_mul {G : Type} [Group G] (Pp Γ : Subgroup G) (a : ℂ) (f : G → ℂ) (g : G) :
    GlobalTheory.Eis.cosetSum Pp Γ (fun y => a * f y) g = a * GlobalTheory.Eis.cosetSum Pp Γ f g := by
  simp only [GlobalTheory.Eis.cosetSum, GlobalTheory.Eis.term]
  exact tsum_mul_left

theorem ident_lincomb (hT : TAll) (hSK : SecK) (hEW : EisWk) (d : SD σ) (c : ℂ) {k : ℕ} (a : Fin k → ℂ)
    (Ψ : Fin k → d.Fn) (hK : ∀ i, d.KFin (Ψ i))
    (hI : ∀ i x, HolValueAt (fun z => d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (Ψ i) x))
    (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (c * d.I (∑ i, a i • Ψ i) x) := by
  have hsch : ∀ i, a i • Ψ i ∈ d.sch := fun i => d.sch.smul_mem _ (hK i).1
  have hv : d.I (∑ i, a i • Ψ i) x = ∑ i, a i * d.I (Ψ i) x := by
    rw [I_sum d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [I_smul d hT.2.2.2.1 (a i) (hK i).1]
    rfl
  have key : ∀ i, HolValueAt (fun z => a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x) (s0 d.m d.n)
      (a i * (c * d.I (Ψ i) x)) := fun i => (holValueAt_const (a i) _).mul (hI i x)
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := eisAll_of hSK hEW d _ (hK i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 (∑ i, a i • Ψ i) = fun y => ∑ i, a i * d.sec0 (Ψ i) y := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← secl_apply, map_sum, Finset.sum_apply]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul]
    rfl
  have heq : EqRight (fun z => ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have hc' : ∀ i ∈ Finset.univ, GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
        (fun y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x := fun i _ =>
      (htt i z (hz' i)).of_norm_le (C := ‖a i‖) fun y => (norm_mul _ _).le
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y)) x hc'
    show ∑ i, a i * d.eis (d.sec0 (Ψ i)) (s0 d.m d.n) z x = d.eis (d.sec0 (∑ i, a i • Ψ i)) (s0 d.m d.n) z x
    rw [hsec]
    unfold SD.eis
    have e2 : (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * ∑ i, a i * d.sec0 (Ψ i) y) =
        fun y => ∑ i, a i * (((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (Ψ i) y) := by
      funext y
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [e2, this]
    exact Finset.sum_congr rfl fun i _ => (cosetSum_const_mul _ _ _ _ _).symm
  have hval : c * d.I (∑ i, a i • Ψ i) x = ∑ i, a i * (c * d.I (Ψ i) x) := by
    rw [hv, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hval]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq

end PositivityTheory.SiegelWeilFormula.Atop

end
end

