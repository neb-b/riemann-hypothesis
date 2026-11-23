module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.MainEq
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.LiftedSchrodingerDatum
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0033
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.FockVacuumBounds.Bundle0001
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.VacuumIwasawa.VacCut
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.AwayActions.InFrameInvOf
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0031
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.Bundle0028
public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.DilationDecomposition.Bundle0003

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainEq
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
open PositivityTheory.SiegelWeilFormula.KMain
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem fc_smul_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (c : ℂ) (f : d.G → ℂ) (nb : nA σ d.Y d.b → d.G) (lam : Measure (nA σ d.Y d.b))
    (𝓖 : Set (nA σ d.Y d.b)) (T : nF σ d.Y d.b) (x : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (c • f) T x = c * fc d.B.ψ d.b nb lam 𝓖 f T x := by
  unfold fc
  simp only [Pi.smul_apply, smul_eq_mul, mul_assoc]
  exact integral_const_mul c _
theorem perLiftC_k (c : ℂ) (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k)
    (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k)
    (hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hnm : d.n ≤ d.m) (hEA : d.EisAll)
    (hW : ∀ Φ, d.KFin Φ → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k c d Φ) (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d)
    (w : InfinitePlace F) {Ψ : Mx F E d.m d.n → ℂ} (hΨ : Ψ ∈ R.away w) {φ : PX d.m d.n →ₗ[ℂ] d.Fn}
    (hφ : R.IsLift w Ψ φ) (P : PX d.m d.n) (x : d.G) :
    HolValueAt (fun z => d.eis (d.sec0 (φ P)) (s0 d.m d.n) z x) (s0 d.m d.n) (c * d.I (φ P) x) := by
  obtain ⟨hTB, -, -, hTT, hTA⟩ := hT
  obtain ⟨L, hL⟩ := hLo F E σ d R w
  obtain ⟨sL, ρ, p, q, e, hgood, hLD, hsL, hρ⟩ := hLI F E σ d R w L hL
  have hfock := (hFM F E σ d R).2.1 w Ψ hΨ
  have hKF : ∀ P, d.KFin (φ P) := fun P =>
    hPK F E σ d R (φ P) (hφ P).1 (by rw [(hφ P).2]; exact hfock.1 P)
  have hom : ∀ k : GR d.n, InK (mR k) → ∀ P, d.om (R.ι w k) (φ P) = φ (ρ k P) := by
    intro k hk P
    have h1 := (hL k (fP P) (isSw_fP P)).2 Ψ hfock.2 (φ P) (hφ P).1 (hφ P).2
    rw [hρ k P hk] at h1
    have hmem : d.om (R.ι w k) (φ P) - φ (ρ k P) ∈ d.sch := d.sch.sub_mem (_root_.PositivityTheory.SiegelWeilFormula.KMain.om_mem_k d _ (hφ P).1) (hφ _).1
    refine sub_eq_zero.mp ((hTB F E σ d).2.2 _ hmem ?_)
    rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, h1, (hφ _).2, sub_self]
  let Il : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) :=
    { toFun := fun P => c • d.I (φ P)
      map_add' := fun P Q => by rw [map_add (f := _), _root_.PositivityTheory.SiegelWeilFormula.KMain.I_add_k d hTT hTA (hφ P).1 (hφ Q).1, smul_add]
      map_smul' := fun a P => by rw [map_smul, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_smul_k d hTT a (hφ P).1, RingHom.id_apply, smul_comm] }
  let sl : PX d.m d.n →ₗ[ℂ] (d.G → ℂ) := (_root_.PositivityTheory.SiegelWeilFormula.KMain.secl_k d).comp φ
  obtain ⟨-, ⟨ε, ww, hww, -⟩, hTG, hLC, hT2, hSC⟩ := hAux F E σ d
  have hsec1 : IsSec d.K d.χ (s0 d.m d.n) (d.sec0 (φ 1)) := hSK F E σ d (φ 1) (hKF 1)
  have hE1 : d.Eis (d.sec0 (φ 1)) (s0 d.m d.n) := hEA (φ 1) (hKF 1)
  obtain ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩ := hE1 (s0 d.m d.n)
  have hGDat : GlobData (fun _ => true) (2 * Real.pi) sL ρ d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht
      sl Il d.lamSet :=
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
      eis := ⟨U, pp, Ê, t, hUo, hRD, hs0, hp, hhol, hcont, hinv, hconv⟩
      Λadd := fun l hl => (hLB F E σ d l hl).1
      Λbd := fun l hl => (hLB F E σ d l hl).2
      Λsing := fun f hf hinv hz => hLS F E σ d R w f hf hinv hz
      Λval := by
        rintro l ⟨nb, lam, 𝓖, T, x, hcd, hT, rfl⟩
        obtain ⟨t', ht'⟩ := hU F E σ d _ _ hsec1 hE1
        have hWh := hW (φ 1) (hKF 1) nb lam 𝓖 hcd ε ww hww T hT x
        have hC := hTC F E σ d (φ 1) (hφ 1).1 nb lam 𝓖 hcd T x
        show HolValueAt (fun z => fc d.B.ψ d.b nb lam 𝓖 (d.eis (d.sec0 (φ 1)) (s0 d.m d.n) z) T x) (s0 d.m d.n)
          (fc d.B.ψ d.b nb lam 𝓖 (c • d.I (φ 1)) T x)
        rw [_root_.PositivityTheory.SiegelWeilFormula.Atop.fc_smul_k, hC]
        exact hWh.congr ⟨t', fun z hz => ((ht' z hz nb lam 𝓖 hcd ε ww hww x).2 T hT).symm⟩ }
  exact hA d.m d.n (fun _ => true) (2 * Real.pi) (2 * Real.pi * ((R.sg w : ℤ) : ℝ)) p q e sL ρ hLD (hgood hnm)
    d.G (par2 σ d.Y) (rat2 σ d.Y) (R.ι w) (s0 d.m d.n) d.Ht sl Il d.lamSet hGDat P x
theorem mainC_of_k (c : ℂ) (hA : AbsThm) (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hTC : _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k) (hRD : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hFM : _root_.PositivityTheory.SiegelWeilFormula.FockMem_k)
    (hLE : _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k) (hLo : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hLI : _root_.PositivityTheory.SiegelWeilFormula.LocInst_k) (hGS : _root_.PositivityTheory.SiegelWeilFormula.GSplit_k) (hGI : _root_.PositivityTheory.SiegelWeilFormula.GIinv_k) (hGD : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k) (hKP : _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k)
    (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hLB : _root_.PositivityTheory.SiegelWeilFormula.LamBd_k) (hLS : _root_.PositivityTheory.SiegelWeilFormula.LamSing_k) (hU : _root_.PositivityTheory.SiegelWeilFormula.Unfold_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (hnm : d.n ≤ d.m)
    (hEA : d.EisAll) (hW : ∀ Φ, d.KFin Φ → _root_.PositivityTheory.SiegelWeilFormula.WhitAt_k c d Φ) : _root_.PositivityTheory.SiegelWeilFormula.MainC_k c d := by
  intro Φ hΦ x
  obtain ⟨R⟩ := hRD F E σ d
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  obtain ⟨k, P, Ψ, hΨ, hsum⟩ := (hFM F E σ d R).2.2 w _ (hKP F E σ d R Φ hΦ)
  choose φ hφ using fun i => hLE F E σ d R w (Ψ i) (hΨ i)
  have hsch : ∀ i, φ i (P i) ∈ d.sch := fun i => (hφ i (P i)).1
  have eT : ∀ i, d.T (φ i (P i)) = R.tens w (fP (P i)) (Ψ i) := fun i => (hφ i (P i)).2
  have hΦeq : Φ = ∑ i, φ i (P i) := by
    have hmem : Φ - ∑ i, φ i (P i) ∈ d.sch := d.sch.sub_mem hΦ.1 (d.sch.sum_mem fun i _ => hsch i)
    refine sub_eq_zero.mp ((hT.1 F E σ d).2.2 _ hmem ?_)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← _root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, map_sub, map_sum]
    simp only [_root_.PositivityTheory.SiegelWeilFormula.KMain.Tl_apply_k, eT, hsum, sub_self]
  have key : ∀ i, HolValueAt (fun z => d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x) (s0 d.m d.n)
      (c * d.I (φ i (P i)) x) := fun i =>
    _root_.PositivityTheory.SiegelWeilFormula.Atop.perLiftC_k c hA hT hTC hAux hFM hLo hLI hGS hGI hGD hPK hSK hLB hLS hU d hnm hEA hW R w (hΨ i) (hφ i) (P i) x
  have hv : d.I Φ x = ∑ i, d.I (φ i (P i)) x := by
    rw [hΦeq, _root_.PositivityTheory.SiegelWeilFormula.KMain.I_sum_k d hT.2.2.2.1 hT.2.2.2.2 Finset.univ _ (fun i _ => hsch i), Finset.sum_apply]
  have hKi : ∀ i, d.KFin (φ i (P i)) := fun i =>
    hPK F E σ d R _ (hsch i) (by rw [eT]; exact ((hFM F E σ d R).2.1 w (Ψ i) (hΨ i)).1 (P i))
  have hconv : ∀ i, ∃ t : ℝ, ∀ z : ℂ, t < z.re → GlobalTheory.Eis.CosetConv (par2 σ d.Y) (rat2 σ d.Y)
      (fun y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x := by
    intro i
    obtain ⟨U, pp, Ê, t, -, -, -, -, -, -, -, hc⟩ := hEA _ (hKi i) (s0 d.m d.n)
    refine ⟨t, fun z hz => ?_⟩
    obtain ⟨u, hu, hle⟩ := (hc z hz).1 {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => hle x rfl q) hu
  choose tt htt using hconv
  have hsec : d.sec0 Φ = fun y => ∑ i, d.sec0 (φ i (P i)) y := by
    funext y
    set_option synthInstance.maxHeartbeats 100000 in
      rw [hΦeq, ← _root_.PositivityTheory.SiegelWeilFormula.KMain.secl_apply_k, map_sum, Finset.sum_apply]
    rfl
  have heq : EqRight (fun z => ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x)
      (fun z => d.eis (d.sec0 Φ) (s0 d.m d.n) z x) := by
    refine ⟨∑ i, |tt i|, fun z hz => ?_⟩
    have hz' : ∀ i, tt i < z.re := fun i =>
      lt_of_le_of_lt ((le_abs_self _).trans
        (Finset.single_le_sum (fun j _ => abs_nonneg (tt j)) (Finset.mem_univ i))) hz
    have := cosetSum_finsum (par2 σ d.Y) (rat2 σ d.Y) Finset.univ
      (fun i y => ((d.Ht y : ℝ) : ℂ) ^ (z - s0 d.m d.n) * d.sec0 (φ i (P i)) y) x (fun i _ => htt i z (hz' i))
    show ∑ i, d.eis (d.sec0 (φ i (P i))) (s0 d.m d.n) z x = d.eis (d.sec0 Φ) (s0 d.m d.n) z x
    rw [hsec]
    unfold _root_.PositivityTheory.SiegelWeilFormula.SD_k.eis
    simp only [Finset.mul_sum]
    exact this.symm
  rw [hv, Finset.mul_sum]
  exact (holValueAt_finsum Finset.univ fun i _ => key i).congr heq
theorem eisAll_of_k (hSK : _root_.PositivityTheory.SiegelWeilFormula.SecK_k) (hEW : _root_.PositivityTheory.SiegelWeilFormula.EisWk_k) (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.EisAll :=
  fun Φ hΦ => hEW F E σ d (s0 d.m d.n) (d.sec0 Φ) (hSK F E σ d Φ hΦ)
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
def MainEqOf_k : Prop :=
  AbsThm → _root_.PositivityTheory.SiegelWeilFormula.TAll_k → _root_.PositivityTheory.SiegelWeilFormula.ThetaCoef_k → _root_.PositivityTheory.SiegelWeilFormula.RDEx_k → _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties → _root_.PositivityTheory.SiegelWeilFormula.FockMem_k → _root_.PositivityTheory.SiegelWeilFormula.LiftEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k → _root_.PositivityTheory.SiegelWeilFormula.LocInst_k → _root_.PositivityTheory.SiegelWeilFormula.GSplit_k → _root_.PositivityTheory.SiegelWeilFormula.GIinv_k → _root_.PositivityTheory.SiegelWeilFormula.GIdil_k → _root_.PositivityTheory.SiegelWeilFormula.KFinPoly_k →
    _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k → _root_.PositivityTheory.SiegelWeilFormula.SecK_k → _root_.PositivityTheory.SiegelWeilFormula.LamBd_k → _root_.PositivityTheory.SiegelWeilFormula.LamSing_k → _root_.PositivityTheory.SiegelWeilFormula.Unfold_k → _root_.PositivityTheory.SiegelWeilFormula.EisWk_k → _root_.PositivityTheory.SiegelWeilFormula.WhitEq_k → _root_.PositivityTheory.SiegelWeilFormula.MainEq_k
theorem Atop.mainEq_of_k : _root_.PositivityTheory.SiegelWeilFormula.MainEqOf_k := by
  intro hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU hEW hWE F E _ _ _ _ _ σ d hmn
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.mainC_of_k 2 hA hT hTC hRD hAux hFM hLE hLo hLI hGS hGI hGD hKP hPK hSK hLB hLS hU d hmn.ge
    (_root_.PositivityTheory.SiegelWeilFormula.Atop.eisAll_of_k hSK hEW d) (fun Φ hΦ => hWE F E σ d hmn Φ hΦ)
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAtopMainLe
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Atop
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem LD.n_succ_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (L : _root_.PositivityTheory.SiegelWeilFormula.LD_k d) : L.n + 1 = d.n := by
  have h1 : Finset.univ.image L.em = Finset.univ.erase L.i₀ := by
    ext i
    rw [Finset.mem_image, Finset.mem_erase]
    simp only [Finset.mem_univ, true_and, and_true]
    exact ((L.rng i).trans Set.mem_range).symm
  have h2 := congrArg Finset.card h1
  rw [Finset.card_image_of_injective _ L.inj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Finset.card_univ, Fintype.card_fin, Fintype.card_fin] at h2
  have := L.i₀.pos
  omega
theorem mainInequality_by_corank (hRD : _root_.PositivityTheory.SiegelWeilFormula.RDEx_k) (hLD : _root_.PositivityTheory.SiegelWeilFormula.LDEx_k) (hVK : _root_.PositivityTheory.SiegelWeilFormula.VacK_k) (hPK : _root_.PositivityTheory.SiegelWeilFormula.PolyKFin_k) (hEq : _root_.PositivityTheory.SiegelWeilFormula.MainEq_k) (hStep : _root_.PositivityTheory.SiegelWeilFormula.Step_k)
    (hVA : _root_.PositivityTheory.SiegelWeilFormula.VacAll_k) (k : ℕ) : ∀ d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ, d.m ≤ d.n → d.n - d.m = k → _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 d := by
  induction k with
  | zero =>
    intro d h hk
    exact hEq F E σ d (by omega)
  | succ k ih =>
    intro d h hk
    have hm := d.ok.hm
    obtain ⟨L⟩ := hLD F E σ d (by omega)
    have hL := _root_.PositivityTheory.SiegelWeilFormula.Atop.LD.n_succ_k L
    obtain ⟨R⟩ := hRD F E σ d
    obtain ⟨R'⟩ := hRD F E σ L.sd
    have hC' : _root_.PositivityTheory.SiegelWeilFormula.MainC_k 2 L.sd := ih L.sd (by show d.m ≤ L.n; omega) (by show L.n - d.m = k; omega)
    have hV' : _root_.PositivityTheory.SiegelWeilFormula.MainV_k 2 R' := fun Φ hΦ hv x => hC' Φ (hPK F E σ L.sd R' Φ hΦ ((hVK F E σ L.sd R').2.1 hv)) x
    exact hVA F E σ d R 2 (hStep F E σ d R L R' (by omega) hV')
end PositivityTheory.SiegelWeilFormula.Atop
namespace PositivityTheory.SiegelWeilFormula
theorem Atop.mainLeOf_k : _root_.PositivityTheory.SiegelWeilFormula.MainLeOf_k := by
  intro hRD hLD hVK hPK hEq hStep hVA F E _ _ _ _ _ σ d h
  exact _root_.PositivityTheory.SiegelWeilFormula.Atop.mainInequality_by_corank hRD hLD hVK hPK hEq hStep hVA _ d h rfl
end PositivityTheory.SiegelWeilFormula
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilAvacVacCut
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.Avac
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
def vg_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) (g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ) (X : Mx F E d.m d.n) : ℂ :=
  (∏ w, fP 1 (R.loc w X)) * g fun k => (d.crd X k).2
theorem vg_mem_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) {g : (Fin d.m × Fin d.n × Fin 2 → Af F) → ℂ} (hg : g ∈ SB _) : _root_.PositivityTheory.SiegelWeilFormula.Avac.vg_k R g ∈ R.vac :=
  Submodule.subset_span ⟨g, hg, rfl⟩
theorem vac_le_fock_k {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} (R : _root_.PositivityTheory.SiegelWeilFormula.RD_k d) : R.vac ≤ R.fock := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨g, hg, rfl⟩
  exact Submodule.subset_span ⟨fun _ => 1, g, hg, rfl⟩
def Tl_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : d.Fn →ₗ[ℂ] (Mx F E d.m d.n → ℂ) where
  toFun := d.T
  map_add' Φ Ψ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.add_apply, ← map_add (f := _)]
    congr 1
    funext z
    exact mul_add _ _ _
  map_smul' c Φ := funext fun X => by
    simp only [_root_.PositivityTheory.SiegelWeilFormula.SD_k.T, Pi.smul_apply, RingHom.id_apply, ← map_smul]
    congr 1
    funext z
    exact mul_left_comm _ _ _
theorem T_inj_k (hB : _root_.PositivityTheory.SiegelWeilFormula.TBij_k) {d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ} {Φ Ψ : d.Fn} (hΦ : Φ ∈ d.sch) (hΨ : Ψ ∈ d.sch) (h : d.T Φ = d.T Ψ) : Φ = Ψ := by
  have e : d.T (Φ - Ψ) = 0 := by
    have := (_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k d).map_sub Φ Ψ
    simp only [_root_.PositivityTheory.SiegelWeilFormula.Avac.Tl_k, LinearMap.coe_mk, AddHom.coe_mk] at this
    rw [this, h, sub_self]
  exact sub_eq_zero.1 ((hB F E σ d).2.2 _ (sub_mem hΦ hΨ) e)
end PositivityTheory.SiegelWeilFormula.Avac
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKawayDec
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix
open NumberField Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl
namespace PositivityTheory.SiegelWeilFormula.KAway
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
theorem inFrame_inv_of_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (x : d.G) (N : Matrix (Fin d.n ⊕ Fin d.n) (Fin d.n ⊕ Fin d.n) (AE F E))
    (h : inFrame d.b x * N = 1) : inFrame d.b x⁻¹ = N := by
  calc inFrame d.b x⁻¹ = inFrame d.b x⁻¹ * (inFrame d.b x * N) := by rw [h, Matrix.mul_one]
    _ = N := by rw [← Matrix.mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, inv_mul_cancel, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_one_k, Matrix.one_mul]
theorem adDecomp_k : _root_.PositivityTheory.SiegelWeilFormula.AdDecomp_k := by
  intro F E _ _ _ _ _ σ d ε w hw e he x hx
  obtain ⟨ε₀, hε₀⟩ := d.ok.frame.1
  have hcm : IsCMExt F E σ := d.ok.good.cm
  set X := inFrame d.b x with hXdef
  set A := X.toBlocks₁₁ with hA
  set B := X.toBlocks₁₂ with hB
  set C := X.toBlocks₂₁ with hC
  set D := X.toBlocks₂₂ with hD
  have hXb : X = fromBlocks A B C D := (fromBlocks_toBlocks X).symm
  have heA : e • A = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hA, ← smul_toBlocks₁₁, hx, smul_toBlocks₁₁, one_toBlocks₁₁]
  have heB : e • B = 0 := by
    rw [hB, ← smul_toBlocks₁₂, hx, smul_toBlocks₁₂, one_toBlocks₁₂, smul_zero]
  have heC : e • C = 0 := by
    rw [hC, ← smul_toBlocks₂₁, hx, smul_toBlocks₂₁, one_toBlocks₂₁, smul_zero]
  have heD : e • D = e • (1 : Matrix (Fin d.n) (Fin d.n) (AE F E)) := by
    rw [hD, ← smul_toBlocks₂₂, hx, smul_toBlocks₂₂, one_toBlocks₂₂]
  have hε₀2 : (ε₀ : ℤ) * (ε₀ : ℤ) = 1 := by rw [← Units.val_mul, Int.units_mul_self, Units.val_one]
  obtain ⟨t, ht, het, hunit⟩ := free_etale_sheaf_zmod_exists_hom_sending_generator hcm (ε₀ : ℤ) hε₀2 X (_root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d x) e he heA
  obtain ⟨x₁, hx₁⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM t) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) t).2 ht)
  have hx₁i : inFrame d.b x₁⁻¹ = nM (-t) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₁ _ (by
    rw [hx₁, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  set A' := A - t * C with hA'
  set B' := B - t * D with hB'
  have hY : inFrame d.b (x₁⁻¹ * x) = fromBlocks A' B' C D := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hx₁i, ← hXdef, hXb, nM, fromBlocks_multiply]
    simp [hA', hB', sub_eq_add_neg]
  have h11 := upper_block_rank_one_update (cA σ).toRingHom (ε₀ : ℤ) _ (_root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ (x₁⁻¹ * x))
  rw [hY, toBlocks_fromBlocks₁₁, toBlocks_fromBlocks₂₁] at h11
  have hA'u : IsUnit A'.det := hunit
  set c₀ := C * A'⁻¹ with hc₀
  set c := ((ε : ℤ) : AE F E) • c₀ with hcdef
  have hcc := cond_c (cA σ).toRingHom (ε₀ : ℤ) A' C hA'u hε₀2 h11 (ε : ℤ)
  obtain ⟨x₂, hx₂⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM c) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) c).2 hcc)
  have hεε : ((ε : ℤ) : AE F E) * ((ε : ℤ) : AE F E) = 1 := by
    rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self, Units.val_one, Int.cast_one]
  have hwi : inFrame d.b w⁻¹ = fromBlocks 0 (((ε : ℤ) : AE F E) • 1) 1 0 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d w _ (by
    rw [hw, fromBlocks_multiply]; simp [smul_smul, hεε, fromBlocks_one])
  have hL : inFrame d.b (w * x₂ * w⁻¹) = fromBlocks 1 0 c₀ 1 := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hw, hx₂, hwi, nM, fromBlocks_multiply, fromBlocks_multiply]
    simp [hcdef, smul_smul, hεε]
  have hLi : inFrame d.b (w * x₂ * w⁻¹)⁻¹ = fromBlocks 1 0 (-c₀) 1 := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d _ _ (by
    rw [hL, fromBlocks_multiply]; simp [fromBlocks_one])
  have hcA : c₀ * A' = C := by rw [hc₀, Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA'u, Matrix.mul_one]
  have hZ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x)) = fromBlocks A' B' 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hLi, hY, fromBlocks_multiply]
    simp [hcA, sub_eq_add_neg, add_comm]
  obtain ⟨hz1, hz2⟩ := blkUpper (cA σ).toRingHom (ε₀ : ℤ) A' B' (D - c₀ * B') (by rw [← hZ]; exact _root_.PositivityTheory.SiegelWeilFormula.KAway.inU_inFrame_k hε₀ _)
  have hbb := cond_b (cA σ).toRingHom (ε₀ : ℤ) (cA_cA hcm) A' B' (D - c₀ * B') hA'u hz1 hz2
  obtain ⟨x₄, hx₄⟩ := _root_.PositivityTheory.SiegelWeilFormula.KAway.exists_of_inU_k hε₀ (nM (A'⁻¹ * B')) ((nM_cond_iff (cA σ).toRingHom (ε₀ : ℤ) _).2 hbb)
  have hx₄i : inFrame d.b x₄⁻¹ = nM (-(A'⁻¹ * B')) := _root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_inv_of_k d x₄ _ (by
    rw [hx₄, nM, nM, fromBlocks_multiply]; simp [fromBlocks_one])
  have hx₃ : inFrame d.b ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹) = fromBlocks A' 0 0 (D - c₀ * B') := by
    rw [_root_.PositivityTheory.SiegelWeilFormula.KAway.inFrame_mul_k, hZ, hx₄i, nM, fromBlocks_multiply]
    simp [Matrix.mul_nonsing_inv_cancel_left _ _ hA'u]
  have hdet := _root_.PositivityTheory.SiegelWeilFormula.KAway.isUnit_det_inFrame_k d ((w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹)
  rw [hx₃, det_fromBlocks_zero₁₂] at hdet
  have hDu : IsUnit (D - c₀ * B').det := isUnit_of_mul_isUnit_right hdet
  have heB' : e • B' = 0 := by rw [hB', smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, heB, sub_zero]
  refine ⟨x₁, x₂, (w * x₂ * w⁻¹)⁻¹ * (x₁⁻¹ * x) * x₄⁻¹, x₄, t, c, A'⁻¹ * B', nonsingInvUnit A' hA'u,
    nonsingInvUnit (D - c₀ * B') hDu, by group, hx₁, hx₂, hx₃, hx₄, het, ?_, ?_, ?_, ?_⟩
  · rw [hcdef, smul_comm, hc₀, ← Matrix.smul_mul, heC, Matrix.zero_mul, smul_zero]
  · rw [← Matrix.mul_smul, heB', Matrix.mul_zero]
  · change e • (A - t * C) = _
    rw [smul_sub, ← Matrix.smul_mul, het, Matrix.zero_mul, sub_zero, heA]
  · change e • (D - c₀ * B') = _
    rw [smul_sub, ← Matrix.mul_smul, heB', Matrix.mul_zero, sub_zero, heD]
end PositivityTheory.SiegelWeilFormula.KAway
end
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKdilAssembly
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
open GlobalTheory.Doubling (absE)
namespace PositivityTheory.SiegelWeilFormula.Kdil
theorem gIdil_of_k (hT : _root_.PositivityTheory.SiegelWeilFormula.TAll_k) (hAux : _root_.PositivityTheory.SiegelWeilFormula.SiegelWeilDatumProperties) (hLE : _root_.PositivityTheory.SiegelWeilFormula.LocOpEx_k) (hTP : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaPt_k) (hFP : FPSw) (hMC : MatCount)
    (hSD : _root_.PositivityTheory.SiegelWeilFormula.Kdil.SplitDom_k) (hTB : _root_.PositivityTheory.SiegelWeilFormula.Kdil.ThetaBdd_k) (hLF : _root_.PositivityTheory.SiegelWeilFormula.Kdil.LocFamG_k) (hBD : BigDense) (hHM : HolMean)
    (hDC : DerCont) (hSO : StripOK) : _root_.PositivityTheory.SiegelWeilFormula.GIdil_k := by
  intro F E _ _ _ _ _ σ d R w Ψ hΨ φ hφ g X a ha
  obtain ⟨-, -, -, -, hTA⟩ := hT
  obtain ⟨hμ0, hμT, hTA'⟩ := hTA F E σ d
  obtain ⟨-, -, hGtop, -, -, -⟩ := hAux F E σ d
  obtain ⟨L, hL⟩ := hLE F E σ d R w
  obtain ⟨y₀, Ψ', hrep, hmaj⟩ := hSD F E σ d R w L hL Ψ hΨ g
  obtain ⟨Gf, hreal, hhol, hcont, hbd, hder⟩ := hLF F E σ d R w L hL X a ha
  obtain ⟨hUo, hUR, hUb⟩ := hSO d.n X
  have hcount := hMC E d.m d.n
  set U := strip X with hU
  have h0U : (0 : ℂ) ∈ U := by simpa using hUR 0
  set Fm : GR d.n → ℂ → UA σ d.A.J → Matrix (Fin d.m) (Fin d.n) E → ℂ := fun y z h Xr =>
    Gf (y₀ * y) z (R.loc w (mat h⁻¹ * incM F Xr)) * Ψ' (mat h⁻¹ * incM F Xr) with hFm
  set ν : Measure (UA σ d.A.J) := (d.μ.restrict d.D Set.univ)⁻¹ • d.μ.restrict d.D with hν
  have hav : ∀ f : UA σ d.A.J → ℂ, (⨍ h in d.D, f h ∂d.μ) = ∫ h, f h ∂ν := fun f => rfl
  have hc : (d.μ.restrict d.D Set.univ)⁻¹ ≠ ⊤ := by
    rw [ENNReal.inv_ne_top, Measure.restrict_apply_univ]; exact hμ0
  haveI : IsFiniteMeasure (d.μ.restrict d.D) := isFiniteMeasure_restrict.mpr hμT
  have hI : ∀ Φ ∈ d.sch, ∀ x, d.I Φ x =
      ∫ h, ∑' Xr : Matrix (Fin d.m) (Fin d.n) E, d.T (d.om x Φ) (mat h⁻¹ * incM F Xr) ∂ν := by
    intro Φ hΦ x
    rw [← hav]
    show (⨍ h in d.D, thetaSum F (d.om x (d.S h Φ)) ∂d.μ) = _
    simp_rw [hTP F E σ d Φ hΦ x]
  have hT1 : ∀ P y', d.T (d.om (g * R.ι w y') (φ P)) = R.tens w (L (y₀ * y') (fP P)) Ψ' := fun P y' =>
    hrep (φ P) (hφ P).1 (fP P) (hFP _ _ P) (hφ P).2 y'
  obtain ⟨hHc, hHd, hHr⟩ := hHM (GR d.n) (UA σ d.A.J) (Matrix (Fin d.m) (Fin d.n) E) ν U hUo hUb Fm
    (fun p h Xr => (hhol (y₀ * p) _).mul_const _)
    (fun h Xr => ((hcont (R.loc w (mat h⁻¹ * incM F Xr))).comp (f := fun q : GR d.n × ℂ => (y₀ * q.1, q.2))
      (by fun_prop) (fun q (hq : q ∈ Set.univ ×ˢ U) => ⟨trivial, hq.2⟩)).mul continuousOn_const)
    (by
      intro p t _
      have e : (fun h => ∑' k, Fm p t h k) = fun h => thetaSum F (d.om (g * R.ι w (p * a t)) (d.S h (φ 1))) := by
        funext h
        rw [hTP F E σ d (φ 1) (hφ 1).1, hT1 1 (p * a t)]
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
      rw [e]
      exact ((hTA' (φ 1) (hφ 1).1).1 _).aestronglyMeasurable.smul_measure _)
    (by
      rintro ⟨p, z⟩ ⟨-, hz⟩
      obtain ⟨N, hN, C, δ, hδ, hCb⟩ := hbd (y₀ * p, z) ⟨trivial, hz⟩
      obtain ⟨K, hK⟩ := hTB F E σ d _ (hmaj δ hδ)
      refine ⟨(fun q : GR d.n × ℂ => (y₀ * q.1, q.2)) ⁻¹' N,
        (Continuous.continuousAt (by fun_prop)).preimage_mem_nhds hN,
        fun h Xr => |C| * ‖R.tens w (fun u => (Real.exp (-δ * sq u) : ℂ)) Ψ' (mat h⁻¹ * incM F Xr)‖,
        fun _ => |C| * K, fun h => (hK h).1.mul_left _, (integrable_const _).smul_measure hc, ?_, ?_⟩
      · intro h
        rw [tsum_mul_left]
        exact mul_le_mul_of_nonneg_left (hK h).2 (abs_nonneg C)
      · intro q' hq' hq'U h Xr
        have hb1 := hCb (y₀ * q'.1, q'.2) hq' hq'U (R.loc w (mat h⁻¹ * incM F Xr))
        have he : 0 ≤ Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr))) := (Real.exp_pos _).le
        simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg he]
        calc ‖Gf (y₀ * q'.1) q'.2 (R.loc w (mat h⁻¹ * incM F Xr))‖ * ‖Ψ' (mat h⁻¹ * incM F Xr)‖
            ≤ (C * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ :=
              mul_le_mul_of_nonneg_right hb1 (norm_nonneg _)
          _ ≤ (|C| * Real.exp (-δ * sq (R.loc w (mat h⁻¹ * incM F Xr)))) * ‖Ψ' (mat h⁻¹ * incM F Xr)‖ := by
              gcongr; exact le_abs_self C
          _ = _ := by ring)
  clear_value Fm
  refine ⟨U, fun y z => ∫ h, ∑' k, Fm y z h k ∂ν, hUo, hUR, hHc, fun y => ⟨hHd y, ?_, ?_⟩⟩
  · intro t
    beta_reduce
    rw [hI (φ 1) (hφ 1).1, hT1 1 (y * a t)]
    congr 1
    funext h
    congr 1
    funext Xr
    simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens, hreal, mul_assoc]
  · intro r
    have key : ∀ y', ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0 →
        iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 =
          d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') := by
      intro y' hy'
      rw [hHr y' 0 h0U r, hI _ (hφ _).1, hT1]
      congr 1
      funext h
      congr 1
      funext Xr
      simp only [hFm, _root_.PositivityTheory.SiegelWeilFormula.RD_k.tens]
      rw [iteratedDeriv_mul_const' (fun z => Gf (y₀ * y') z (R.loc w (mat h⁻¹ * incM F Xr))) _ r]
      beta_reduce
      rw [hder (y₀ * y') hy' r]
    have hDC' := hDC (GR d.n) U hUo (fun y' z => ∫ h, ∑' k, Fm y' z h k ∂ν) hHc hHd r
    have hpair : Continuous fun y' : GR d.n => (y', (0 : ℂ)) := by fun_prop
    have hcL : Continuous fun y' => iteratedDeriv r (fun z => ∫ h, ∑' k, Fm y' z h k ∂ν) 0 :=
      hDC'.comp_continuous hpair (fun _ => ⟨trivial, h0U⟩)
    have hcR : Continuous fun y' => d.I (φ ((dil (2 * Real.pi) X ^ r) 1)) (g * R.ι w y') :=
      (hTA' _ (hφ _).1).2.1.comp (continuous_const.mul (R.cont w))
    have hden : Dense {y' : GR d.n | ((mR (y₀ * y')).toBlocks₂₂).det ≠ 0} :=
      (hBD d.n).preimage (isOpenMap_mul_left y₀)
    exact congrFun (hcL.ext_on hden hcR key) y
end PositivityTheory.SiegelWeilFormula.Kdil
end
end
end

