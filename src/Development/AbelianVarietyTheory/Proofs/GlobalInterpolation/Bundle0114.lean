module

public import Mathlib
public import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.GlobalTheory.GL3.PThIndep
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.DifferentiableOnOfTendstoLocallyUniformlyOn
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0085
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.StandardRankOneLatticeOfLocal
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0091
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0110
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ZerosDisc
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChebyshevPsiProgressionRelativeError
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimeCountRelativeErrorOfPsiRelativeError

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NegDefiniteSelfDualStabilizerVolumeOne
section
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.NegDefStab

theorem jpq_zero_left (n : ℕ) : Formalism.UG.Jpq 0 n = -1 := by
  ext i j
  rcases i with i | i
  · exact i.elim0
  · rcases j with j | j
    · exact j.elim0
    · simp [Formalism.UG.Jpq, Matrix.one_apply]

theorem unitary_of_negative_definite {n m : ℕ} (e : Fin m ≃ Fin 0 ⊕ Fin n) (A : Matrix (Fin 0 ⊕ Fin n) (Fin m) ℂ)
    (Jt X : Matrix (Fin m) (Fin m) ℂ) (hJ : IsUnit Jt.det)
    (hA : A.conjTranspose * Formalism.UG.Jpq 0 n * A = Jt)
    (hX : X.conjTranspose * Jt * X = Jt) : ∃ b : Formalism.BasicNotions.UpqT 0 n, Formalism.BasicNotions.UpqT.mat b * A = A * X := by
  rw [jpq_zero_left, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul] at hA
  have hA' : A.conjTranspose * A = -Jt := by rw [← hA, neg_neg]
  have hJ' : IsUnit (-Jt).det := by
    rw [Matrix.det_neg]; exact ((isUnit_one.neg).pow _).mul hJ
  have hX' : X.conjTranspose * (-Jt) * X = -Jt := by
    rw [Matrix.mul_neg, Matrix.neg_mul, hX]
  let L : Matrix (Fin m) (Fin 0 ⊕ Fin n) ℂ := (-Jt)⁻¹ * A.conjTranspose
  have hLA : L * A = 1 := by
    simp only [L, Matrix.mul_assoc, hA']
    exact Matrix.nonsing_inv_mul _ hJ'
  have hAL : A * L = 1 := (Matrix.mul_eq_one_comm_of_equiv (A := A) (B := L) e.symm).mpr hLA
  let bm : Matrix (Fin 0 ⊕ Fin n) (Fin 0 ⊕ Fin n) ℂ := A * X * L
  have hbb : bm.conjTranspose * bm = 1 := by
    have : bm.conjTranspose * bm = L.conjTranspose * (X.conjTranspose * (A.conjTranspose * A) * X) * L := by
      simp only [bm, Matrix.conjTranspose_mul, Matrix.mul_assoc]
    rw [this, hA', hX', ← hA']
    rw [show L.conjTranspose * (A.conjTranspose * A) * L = (A * L).conjTranspose * (A * L) by
      simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]]
    rw [hAL, Matrix.conjTranspose_one, Matrix.one_mul]
  have hbb' : bm * bm.conjTranspose = 1 :=
    (Matrix.mul_eq_one_comm_of_equiv (A := bm.conjTranspose) (B := bm) (Equiv.refl _)).mp hbb
  let g : GL (Fin 0 ⊕ Fin n) ℂ := ⟨bm, bm.conjTranspose, hbb', hbb⟩
  have hg : g ∈ Formalism.UG.Upq 0 n := by
    show Formalism.UG.cT (starRingEnd ℂ) bm * Formalism.UG.Jpq 0 n * bm = Formalism.UG.Jpq 0 n
    have e' : Formalism.UG.cT (starRingEnd ℂ) bm = bm.conjTranspose := by
      ext i j; simp [Formalism.UG.cT, Matrix.conjTranspose_apply]
    rw [e', jpq_zero_left, Matrix.mul_neg, Matrix.mul_one, Matrix.neg_mul, hbb]
  refine ⟨(⟨g, hg⟩ : Formalism.UG.Upq 0 n), ?_⟩
  show bm * A = A * X
  simp only [bm, Matrix.mul_assoc, hLA, Matrix.mul_one]


open Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.StabFin in
theorem measure_SFin_negDef : ∀ (D : D7) (W : HSpace D.host.E) (n : ℕ), W.SigOK → (∀ τ, W.sig τ = (0, n)) →
    ∀ μ : Measure (HA (AF D.host.F) D.sp.cm.sig W.gram), IsVolMeas D W 0 n μ →
    μ (StabFin.SFin D.sp.cm.sig W.gram (L0c D W) : Set (HA (AF D.host.F) D.sp.cm.sig W.gram)) = 1 := by
  intro D W n hW hsig μ hμ
  obtain ⟨θ, hθ⟩ := hμ.2.1
  obtain ⟨A, hA⟩ := (hμ.2.2 θ hθ).1
  have h := (hμ.2.2 θ hθ).2 A hA (fun _ => Set.univ) (fun _ => MeasurableSet.univ)
  have hp : D.cd.cd 0 n Set.univ = 1 := GlobalTheory.CompactDualSwap.cd_zero_univ D.cd n
  simp only [hp, Finset.prod_const_one] at h
  convert h using 2
  ext g
  constructor
  · intro hg
    refine ⟨hg, fun ρ => ?_⟩
    have h0 := hW (embOf D ρ)
    rw [hsig] at h0
    obtain ⟨e, P', hP⟩ := h0
    have hJ : IsUnit (W.gram.map (embOf D ρ)).det := by
      have hd := congrArg Matrix.det hP
      rw [jpq_zero_left, Matrix.det_mul, Matrix.det_mul, Matrix.det_reindex_self] at hd
      refine isUnit_iff_ne_zero.mpr fun h0 => ?_
      rw [h0, mul_zero, zero_mul, Matrix.det_neg, Matrix.det_one, mul_one] at hd
      exact pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero) hd.symm
    obtain ⟨b, hb⟩ := unitary_of_negative_definite e (A ρ) _ _ hJ (hA ρ)
      (infMat_unitary D.sp.cm.sig (fun _ => rfl) (fun x => (D.sp.cm.fixed _).mpr ⟨x, rfl⟩) (embOf D ρ)
        (D.sp.cm.cmUnram.2.1 _) (θ ρ) (hθ ρ) W.gram g)
    exact ⟨b, Set.mem_univ _, hb⟩
  · intro hg; exact hg.1

end GlobalTheory.NegDefStab
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalisedFamilyLatticeHypAndSmooth
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.ThetaMove
  GlobalTheory.ThetaMove.SeamMoves Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity

noncomputable section

namespace GlobalTheory.ThetaMove.LatticeFacts

theorem exp_pi_int (b : ℤ) : Complex.exp ((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))
    = Complex.exp (-((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ))) := by
  have h : (Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)
      = -((Real.pi : ℂ) * Complex.I * ((b : ℝ) : ℂ)) + (b : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    push_cast; ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  congr 1
  push_cast; ring

theorem al_sign (D : D7) (T : TaylorLogMetric.Tor D) {N N' : ℕ} (x : TaylorLogMetric.VC D N N') : TaylorLogMetric.al D T x = 1 ∨ TaylorLogMetric.al D T x = -1 := by
  unfold TaylorLogMetric.al
  rcases Int.even_or_odd (round (Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D T x x).re)) with h | h
  · exact Or.inl h.neg_one_zpow
  · exact Or.inr h.neg_one_zpow

theorem latAll {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.LatAll := by
  have h0 : δ ≠ 0 := delta_ne_zero B
  refine ⟨fun N N' L L' hA => ⟨?_, fun x _ => al_sign D _ x, ?_⟩, fun N N' L₁ L₁' L₂ L₂' h₁ h₂ =>
    ⟨IO.La_index_ne_zero cc hcc δ L₁ L₂ L₁' L₂' h₁ h₂, IO.La_index_ne_zero cc hcc δ L₂ L₁ L₂' L₁' h₂ h₁⟩⟩
  · have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    apply le_antisymm
    · intro v hv
      exact self_dual_lattice D cc hcc δ hδ h0 N N' L L' hA v (fun y hy => hv y hy)
    · intro v hv y hy
      obtain ⟨a, b, -, hab⟩ := hI v hv y hy
      refine ⟨b, ?_⟩
      show (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) v y).im = (b : ℝ)
      rw [hab]; simp
  · intro x hx y hy
    have hI := hermitian_form_integral_values D cc hcc δ hδ h0 N N' L L' hA
    have hs := IO.semiChar_of_HfInt _ hI x hx y hy
    obtain ⟨a, b, -, hab⟩ := hI x hx y hy
    have him : (TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im = (b : ℝ) := by rw [hab]; simp
    rw [hs]
    congr 1
    show Complex.exp (-((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ)))
      = Complex.exp ((Real.pi : ℂ) * Complex.I * (((TaylorLogMetric.Hf D (TaylorLogMetric.tor0 D cc δ) x y).im : ℝ) : ℂ))
    rw [him]; exact (exp_pi_int b).symm

theorem laHyp_and_eSmooth : ∀ (D : D7) (X : Fields) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Formalism.L2.Ker.Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ → B.VecP χ → Even a → Even b → (ambOf s B χ cD).LaHyp a b ∅ ∧ (ambOf s B χ cD).ESmooth a b := by
  intro D X s cc δ B χ cD a b hX hs hcc hδ hV ha hb
  have hL := latAll B hcc hδ
  obtain ⟨hsd, hlam⟩ := GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  have hq := qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  refine ⟨⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, by simp, fun P hP => absurd hP (Finset.notMem_empty P),
    aa_fg s B χ cD, fun N N' h h' => ?_⟩, fun N N' h h' k => ?_⟩
  · obtain ⟨h1, h2, h3⟩ := (Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N N') (lam (ambOf s B χ cD) N N') (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N'))
      (TaylorLogMetric.La D B.tor (s.lat N) (s.lat N')) 0 (form_reidx s _ a b) (hlam a b N N') (hlam a b N N')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N N' h h') (reidx s a b x) ((hlam a b N N' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N N' h h')).1 (hL.1 a b _ _ (hadm N N' h h')).2).1
    exact ⟨h3 (B.eNat χ a b (s.lat N) (s.lat N')) (hV a b _ _ (hadm N N' h h')).1.2, h1, h2⟩
  · have hd : ContDiff ℂ (k : WithTop ℕ∞) (B.eNat χ a b (s.lat N) (s.lat N')) :=
      GlobalTheory.SCV.contDiff_of_differentiable (hV a b _ _ (hadm N N' h h')).1.1 _
    exact hd.comp (reidx s a b).toLinearMap.toContinuousLinearMap.contDiff

end GlobalTheory.ThetaMove.LatticeFacts
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PeriodLatticeHalfLatticeInclusionsSplitPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.L2.Th1.H GlobalTheory.IndefiniteRowSideFullHecke.JetSumTable GlobalTheory.MomT

namespace GlobalTheory.MomT.HalfIncl

section Loc

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W]

theorem mem_of_loc {M : Submodule (𝓞 E) W} {x : W} (h : ∀ Q : HeightOneSpectrum (𝓞 E), x ∈ localization₂ Q.asIdeal M) : x ∈ M := by
  by_contra hx
  have hne : M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) ≠ ⊤ := fun e => hx (by
    have : (1 : 𝓞 E) ∈ M.comap (LinearMap.toSpanSingleton (𝓞 E) W x) := e ▸ Submodule.mem_top
    simpa using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  obtain ⟨s, hs, hsx⟩ := h ⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩
  exact hs (hle (by simpa using hsx))

theorem loc_self (Q : HeightOneSpectrum (𝓞 E)) {M : Submodule (𝓞 E) W} {x : W} (hx : x ∈ M) : x ∈ localization₂ Q.asIdeal M :=
  ⟨1, Q.asIdeal.primeCompl.one_mem, by rwa [one_smul]⟩

variable [Module E W] [IsScalarTower (𝓞 E) E W]

theorem loc_smul {Q : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) W} {x : W} {k k' : E}
    (hx : k' • x ∈ localization₂ Q.asIdeal M) (r s : 𝓞 E) (hs : s ∉ Q.asIdeal) (h : (s : E) * k = (r : E) * k') :
    k • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨t, ht, hx⟩ := hx
  refine ⟨t * s, Q.asIdeal.primeCompl.mul_mem ht hs, ?_⟩
  have : (t * s) • k • x = r • t • k' • x := by
    simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_mul]
    congr 1
    have h' : algebraMap (𝓞 E) E s * k = algebraMap (𝓞 E) E r * k' := h
    linear_combination (algebraMap (𝓞 E) E t) * h'
  rw [this]
  exact M.smul_mem _ hx

theorem loc_smul' {Q : HeightOneSpectrum (𝓞 E)} {M : Submodule (𝓞 E) W} {x : W} {k : E}
    (hx : x ∈ localization₂ Q.asIdeal M) (r s : 𝓞 E) (hs : s ∉ Q.asIdeal) (h : (s : E) * k = (r : E)) :
    k • x ∈ localization₂ Q.asIdeal M :=
  loc_smul (k' := 1) (by rwa [one_smul]) r s hs (by rwa [mul_one])

theorem mem_twO (M : Submodule (𝓞 E) W) (c : ℕ) (e : HeightOneSpectrum (𝓞 E) → ℤ) (y : W) :
    y ∈ twist₂ M c e ↔ ∀ Q : HeightOneSpectrum (𝓞 E), ((c : E) ^ e Q)⁻¹ • y ∈ localization₂ Q.asIdeal M := by
  simp [twist₂, Submodule.mem_iInf]

theorem mem_mulLat (M : Submodule (𝓞 E) W) {c : ℕ} (hc : c ≠ 0) (y : W) :
    y ∈ mulLat c M ↔ (c : E)⁻¹ • y ∈ M := by
  have hcE : (c : E) ≠ 0 := by exact_mod_cast hc
  have e : ∀ m : W, (c : 𝓞 E) • m = (c : E) • m := fun m => by
    rw [← algebraMap_smul E, map_natCast]
  constructor
  · rintro ⟨m, hm, rfl⟩
    simpa [e, smul_smul, hcE] using hm
  · intro h
    exact ⟨_, h, by simp [e, smul_smul, hcE]⟩

theorem nat_notMem {Q : HeightOneSpectrum (𝓞 E)} {n p : ℕ} (h : Nat.Coprime n p) (hp : (p : 𝓞 E) ∈ Q.asIdeal) :
    (n : 𝓞 E) ∉ Q.asIdeal := fun hn => by
  obtain ⟨u, v, huv⟩ : IsCoprime (n : 𝓞 E) (p : 𝓞 E) := h.cast
  exact Q.isPrime.ne_top ((Ideal.eq_top_iff_one _).2
    (huv ▸ Q.asIdeal.add_mem (Q.asIdeal.mul_mem_left _ hn) (Q.asIdeal.mul_mem_left _ hp)))

theorem exists_prime_over {p : ℕ} (hp : p.Prime) : ∃ Q : HeightOneSpectrum (𝓞 E), (p : 𝓞 E) ∈ Q.asIdeal := by
  have hu : ¬ IsUnit (p : 𝓞 E) := fun h => by
    have : IsUnit (p : ℤ) := isUnit_of_map_unit (algebraMap ℤ (𝓞 E)) _ (by simpa using h)
    exact hp.one_lt.ne' (by simpa [Int.isUnit_iff_natAbs_eq] using this)
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal (Ideal.span {(p : 𝓞 E)}) (by simpa [Ideal.span_singleton_eq_top] using hu)
  exact ⟨⟨m, hm.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hm (RingOfIntegers.not_isField E)⟩,
    hle (Ideal.mem_span_singleton_self _)⟩

theorem expS_conj [StarRing E] {S : Finset (HeightOneSpectrum (𝓞 E))} (hS : ∀ P ∈ S, conjPrime₂ P ∉ S)
    (Q : HeightOneSpectrum (𝓞 E)) : expS S (conjPrime₂ Q) = -expS S Q := by
  unfold expS
  rw [GlobalTheory.CharValCompare.conjP_conjP]
  by_cases h1 : Q ∈ S
  · simp [h1, hS Q h1]
  · by_cases h2 : conjPrime₂ Q ∈ S <;> simp [h1, h2]

theorem expS_cases [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) (Q : HeightOneSpectrum (𝓞 E)) :
    (Q ∈ S ∧ expS S Q = 1) ∨ (Q ∉ S ∧ conjPrime₂ Q ∈ S ∧ expS S Q = -1) ∨ (Q ∉ S ∧ conjPrime₂ Q ∉ S ∧ expS S Q = 0) := by
  unfold expS
  by_cases h1 : Q ∈ S
  · simp [h1]
  · by_cases h2 : conjPrime₂ Q ∈ S <;> simp [h1, h2]

end Loc

theorem half_inclusions : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S SG : Finset (HeightOneSpectrum (𝓞 X.E))) (ϖ : 𝓞 X.E) (p g cA : ℕ) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), Ctx A a b S SG ϖ p g cA → IsSdLat N → IsSdLat N' → A.AA ≠ ⊥ ∧ (∀ y ∈ per A N N', ((g : X.E) * ((ϖ : X.E) / star (ϖ : X.E))) • y ∈ halfBO S (per A N N') (p * g)) ∧ (∀ y ∈ halfBO S (per A N N') (p * g), ((g : X.E) * (star (ϖ : X.E) / (ϖ : X.E))) • y ∈ per A N N') ∧ (∀ x ∈ divLat cA (homAt S N N'), x ∈ homAt (divs ϖ) N N' → ∀ t ∈ halfAO S (per A N N') (cA * (p * g)), t - x ∈ mulLat (p * g) (homAt S N N') → ((cA * g : ℕ) : X.E) • t ∈ per A N N') ∧ (∀ y ∈ per A N N', y ∈ homAt S N N' ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ halfAO S (per A N N') (cA * (p * g)) ∧ (((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt SG N N') ∧ ((((cA * g : ℕ) : X.E) * star (ϖ : X.E)) • y ∈ mulLat (p * g) (homAt S N N') ↔ y ∈ smulLat (ϖ : X.E) (per A N N'))) ∧ (∀ (y : HomE X.E a b) (n : ℕ), Nat.Coprime n p → (n : X.E) • y ∈ smulLat ((ϖ : X.E) / star (ϖ : X.E)) (per A N N') → y ∈ mulLat p (homAt (divs ϖ) N N')) ∧ (∀ x ∈ halfBO S (per A N N') (p * g), ∀ y ∈ halfBO S (per A N N') (p * g), ∃ n : ℤ, coc A x y = n) ∧ ∀ x ∈ halfAO S (per A N N') (cA * (p * g)), ∀ y ∈ halfAO S (per A N N') (cA * (p * g)), ∃ n : ℤ, coc A x y = n := by
  intro X A a b S SG ϖ p g cA N N' hC hN hN'
  obtain ⟨hX, ⟨hδ, -, hSc, hAS, hfg, hLa⟩, hAc, -, hp, hϖ, hcop, hS, hSG, hg, hcA⟩ := hC
  have hp0 : p ≠ 0 := hp.ne_zero
  have hg0 : g ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hg)
  have hcA0 : cA ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hcA)
  have hpE : (p : X.E) ≠ 0 := by exact_mod_cast hp0
  have hgE : (g : X.E) ≠ 0 := by exact_mod_cast hg0
  have hcE : (cA : X.E) ≠ 0 := by exact_mod_cast hcA0
  have hpO : (p : 𝓞 X.E) ≠ 0 := by exact_mod_cast hp0
  have hϖO : ϖ ≠ 0 := left_ne_zero_of_mul (hϖ ▸ hpO)
  obtain ⟨w, hw⟩ : ∃ w, w = X.conjO ϖ := ⟨_, rfl⟩
  have hstar : star (ϖ : X.E) = (w : X.E) := by rw [hw]; rfl
  have hconj : ∀ Q : HeightOneSpectrum (𝓞 X.E), w ∈ Q.asIdeal → conjPrime₂ Q ∈ S := fun Q h =>
    (hS _).2 (Or.inl (by rw [hw] at h; exact h))
  rw [← hw] at hϖ hcop hAc
  have hwO : w ≠ 0 := right_ne_zero_of_mul (hϖ ▸ hpO)
  have hpE' : (p : X.E) = (ϖ : X.E) * (w : X.E) := by
    have := congrArg (algebraMap (𝓞 X.E) X.E) hϖ
    rw [map_mul, map_natCast] at this
    exact this.symm
  have hϖE : (ϖ : X.E) ≠ 0 := left_ne_zero_of_mul (hpE' ▸ hpE)
  have hwE : (w : X.E) ≠ 0 := right_ne_zero_of_mul (hpE' ▸ hpE)
  have hSw : ∀ Q ∈ S, w ∉ Q.asIdeal := fun Q hQ h => hSc Q hQ (hconj Q h)
  have hnS : ∀ Q : HeightOneSpectrum (𝓞 X.E), Q ∉ S → ϖ ∉ Q.asIdeal := fun Q hQ h => hQ ((hS Q).2 (Or.inl h))
  have hpm : ∀ Q : HeightOneSpectrum (𝓞 X.E), ϖ ∈ Q.asIdeal → (p : 𝓞 X.E) ∈ Q.asIdeal := fun Q h =>
    hϖ ▸ Q.asIdeal.mul_mem_right _ h
  have hone : ∀ Q : HeightOneSpectrum (𝓞 X.E), (1 : 𝓞 X.E) ∉ Q.asIdeal := fun Q => Q.asIdeal.primeCompl.one_mem
  have hmul : ∀ (Q : HeightOneSpectrum (𝓞 X.E)) {s t : 𝓞 X.E}, s ∉ Q.asIdeal → t ∉ Q.asIdeal → s * t ∉ Q.asIdeal :=
    fun Q _ _ hs ht => Q.asIdeal.primeCompl.mul_mem hs ht
  have hAA : A.AA ≠ ⊥ := by
    obtain ⟨Q, hQ⟩ := exists_prime_over (E := X.E) hp
    have h1 : localization₂ Q.asIdeal A.AA = localization₂ Q.asIdeal 1 := by
      rcases Q.isPrime.mem_or_mem (hϖ ▸ hQ) with h | h
      · exact hAS Q ((hS Q).2 (Or.inl h))
      · exact hAc Q ((mem_divs hwO Q).2 h)
    intro h0
    have h2 : (1 : X.E) ∈ localization₂ Q.asIdeal A.AA := h1 ▸ loc_self Q (Submodule.mem_one.2 ⟨1, map_one _⟩)
    obtain ⟨s, hs, h3⟩ := h2
    rw [h0, Submodule.mem_bot, Algebra.smul_def, mul_one, RingOfIntegers.coe_eq_zero_iff] at h3
    exact hs (h3 ▸ Q.asIdeal.zero_mem)
  have hloc := fun P hP => (_root_.GlobalTheory.MomT.LatFin.per_lattice_facts X A a b N N' hfg hAA hN hN').2.2.2 P (hAS P hP)
  have hhom : ∀ T : Finset (HeightOneSpectrum (𝓞 X.E)), (∀ P ∈ T, P ∈ S) → ∀ y : HomE X.E a b,
      y ∈ homAt T N N' ↔ ∀ P ∈ T, y ∈ localization₂ P.asIdeal (per A N N') := fun T hT y =>
    forall₂_congr fun P hP => (hloc P (hT P hP) y).symm
  have hhS := hhom S fun _ h => h
  have hhG := hhom SG fun P h => (hS P).2 (Or.inr h)
  have hhD := hhom (divs ϖ) fun P h => (hS P).2 (Or.inl ((mem_divs hϖO P).1 h))
  have hcoc := (GlobalTheory.MomT.CocInt.cocycle_integral X A a b N N' hX hδ (hLa N N' hN hN').2).2.2
  have hpg : p * g ≠ 0 := mul_ne_zero hp0 hg0
  simp only [hstar]
  refine ⟨hAA, fun y hy => ?_, fun y hy => ?_, fun x _ hx t ht htx => ?_, fun y hy => ⟨?_, ?_, ?_, ?_⟩,
    fun y n hn hy => ?_, fun x hx y hy => ?_, fun x hx y hy => ?_⟩
  · refine (mem_twO _ _ _ _).2 fun Q => ?_
    rw [smul_smul]
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> rw [e]
    · refine loc_smul' (loc_self Q hy) 1 (w * w) (hmul Q (hSw Q h1) (hSw Q h1)) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (g * g * ϖ * ϖ) 1 (hone Q) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (g * ϖ) w (fun h => h2 (hconj Q h)) ?_
      push_cast; field_simp
  · refine mem_of_loc fun Q => ?_
    have h := (mem_twO _ _ _ _).1 hy Q
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> rw [e] at h
    · refine loc_smul h (g * g * w * w) 1 (hone Q) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul h 1 (ϖ * ϖ) (hmul Q (hnS Q h1) (hnS Q h1)) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul h (g * w) ϖ (hnS Q h1) ?_
      push_cast; field_simp
  · refine mem_of_loc fun Q => ?_
    have h := (mem_twO _ _ _ _).1 ht Q
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> simp only [e, neg_zero, neg_neg] at h
    · by_cases hQ : ϖ ∈ Q.asIdeal
      · have h3 := (hhD x).1 hx Q ((mem_divs hϖO Q).2 hQ)
        have h4 := (hhS _).1 ((mem_mulLat _ hpg _).1 htx) Q h1
        have h5 : (1 : X.E) • (t - x) ∈ localization₂ Q.asIdeal (per A N N') := by
          refine loc_smul h4 (p * g) 1 (hone Q) ?_
          push_cast; field_simp
        rw [one_smul] at h5
        have h6 := add_mem h3 h5
        rw [add_sub_cancel] at h6
        refine loc_smul' h6 (cA * g) 1 (hone Q) ?_
        push_cast; field_simp
      · refine loc_smul h 1 p (hSG Q (((hS Q).1 h1).resolve_left hQ)) ?_
        push_cast; field_simp
    · refine loc_smul h (cA * g * (cA * (p * g))) 1 (hone Q) ?_
      push_cast; field_simp
    · refine loc_smul h (cA * g) 1 (hone Q) ?_
      push_cast; field_simp
  · exact (hhS y).2 fun P _ => loc_self P hy
  · refine (mem_twO _ _ _ _).2 fun Q => ?_
    rw [smul_smul]
    rcases expS_cases S Q with ⟨h1, e⟩ | ⟨h1, h2, e⟩ | ⟨h1, h2, e⟩ <;> simp only [e, neg_zero, neg_neg]
    · refine loc_smul' (loc_self Q hy) (cA * (p * g) * (cA * g * w)) 1 (hone Q) ?_
      push_cast; field_simp
    · refine loc_smul' (loc_self Q hy) 1 ϖ (hnS Q h1) ?_
      push_cast; simp only [hpE']; field_simp
    · refine loc_smul' (loc_self Q hy) (cA * g * w) 1 (hone Q) ?_
      push_cast; field_simp
  · refine (mem_mulLat _ hpg _).2 ((hhG _).2 fun P hP => ?_)
    rw [smul_smul]
    refine loc_smul' (loc_self P hy) cA ϖ (fun h => hSG P hP (hpm P h)) ?_
    push_cast; simp only [hpE']; field_simp
  · rw [mem_mulLat _ hpg, hhS, smul_smul, mem_smulLat]
    constructor
    · intro h
      refine ⟨(ϖ : X.E)⁻¹ • y, mem_of_loc fun Q => ?_, by rw [smul_smul, mul_inv_cancel₀ hϖE, one_smul]⟩
      by_cases hQ : ϖ ∈ Q.asIdeal
      · refine loc_smul (h Q ((hS Q).2 (Or.inl hQ))) 1 cA (nat_notMem hcA (hpm Q hQ)) ?_
        push_cast; simp only [hpE']; field_simp
      · refine loc_smul' (loc_self Q hy) 1 ϖ hQ ?_
        push_cast; field_simp
    · rintro ⟨m, hm, rfl⟩ P _
      rw [smul_smul]
      refine loc_smul' (loc_self P hm) cA 1 (hone P) ?_
      push_cast; simp only [hpE']; field_simp
  · obtain ⟨m, hm, e⟩ := hy
    have hn0 : (n : X.E) ≠ 0 := by
      have : n ≠ 0 := by rintro rfl; exact hp.one_lt.ne' (by simpa using hn)
      exact_mod_cast this
    have e' : y = ((n : X.E)⁻¹ * ((ϖ : X.E) / (w : X.E))) • m := by
      have e2 : ((ϖ : X.E) / (w : X.E)) • m = (n : X.E) • y := e
      rw [mul_smul, e2, smul_smul, inv_mul_cancel₀ hn0, one_smul]
    refine (mem_mulLat _ hp0 _).2 ((hhD _).2 fun P hP => ?_)
    have hP' := (mem_divs hϖO P).1 hP
    have hw' := hSw P ((hS P).2 (Or.inl hP'))
    rw [e', smul_smul]
    refine loc_smul' (loc_self P hm) 1 (n * (w * w)) (hmul P (nat_notMem hn (hpm P hP')) (hmul P hw' hw')) ?_
    push_cast; simp only [hpE']; field_simp
  · refine hcoc x y fun Q => ⟨((p * g : ℕ) : X.E) ^ expS S Q, zpow_ne_zero _ (by exact_mod_cast hpg),
      (mem_twO _ _ _ _).1 hx Q, ?_⟩
    have h := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [expS_conj hSc, zpow_neg, inv_inv, ← star_natCast (R := X.E), ← star_zpow₀] at h
  · refine hcoc x y fun Q => ⟨((cA * (p * g) : ℕ) : X.E) ^ (-expS S Q),
      zpow_ne_zero _ (by exact_mod_cast mul_ne_zero hcA0 hpg), (mem_twO _ _ _ _).1 hx Q, ?_⟩
    have h := (mem_twO _ _ _ _).1 hy (conjPrime₂ Q)
    rwa [expS_conj hSc, zpow_neg, inv_inv, ← star_natCast (R := X.E), ← star_zpow₀] at h

end GlobalTheory.MomT.HalfIncl
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.PrimesInProgressionsRelativeError
section
open Complex DirichletCharacter ArithmeticFunction MeasureTheory Filter Topology GlobalTheory.Lin
open scoped Classical

namespace GlobalTheory.Lin

theorem sign_of_sq_eq_one {M : ℕ} [NeZero M] (χ : DirichletCharacter ℂ M) (h : χ ^ 2 = 1) (b : ℕ)
    (hb : Nat.Coprime b M) (θ : ℤ) (hθ : χ (b : ZMod M) = (θ : ℂ)) : θ = 1 ∨ θ = -1 := by
  have hu : IsUnit (b : ZMod M) := (ZMod.isUnit_iff_coprime b M).2 hb
  have h1 : (χ ^ 2) (b : ZMod M) = 1 := by rw [h]; exact MulChar.one_apply hu
  rw [MulChar.pow_apply' χ (by norm_num), hθ] at h1
  have h2 : θ ^ 2 = 1 := by exact_mod_cast h1
  have h3 : (θ - 1) * (θ + 1) = 0 := by linear_combination h2
  rcases mul_eq_zero.1 h3 with h4 | h4
  · left; omega
  · right; omega

theorem primesRel_holds : GlobalTheory.Lin.PrimesRel := by
  obtain ⟨a, ha, hA⟩ := _root_.GlobalTheory.ExceptionalPair.main
  obtain ⟨a', ha', hA'⟩ := _root_.GlobalTheory.Lin.PsiRel.psiAP_relative
  have hc₁ : 0 < min (1 / 8 : ℝ) (min a a') := lt_min (by norm_num) (lt_min ha ha')
  obtain ⟨c, hc, hE⟩ := hA _ hc₁ ((min_le_right _ _).trans (min_le_left _ _))
  obtain ⟨c₂, c₃, C, h₂, h₃, hC, hP⟩ := hA' _ hc₁ ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨c₂', c₃', C', h₂', h₃', hC', hQ⟩ := _root_.GlobalTheory.Lin.pi_rel_of_psi_rel c₂ c₃ C c h₂ h₃ hC hc
  refine ⟨_, c₂', c₃', C', c, hc₁, min_le_left _ _, h₂', h₃', hC', hc, fun M _ hM => ?_⟩
  obtain ⟨hU, hB, -⟩ := hE M hM
  refine ⟨hU, fun χ β h => (hB χ β h).2.2.2.2, fun b θ β hb hD X hX => ?_⟩
  have hM3 : (3 : ℝ) ≤ M := by exact_mod_cast hM
  have hφ1 : (1 : ℝ) ≤ (M.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  have hφ2 : (M.totient : ℝ) ≤ M := by exact_mod_cast Nat.totient_le M
  have hθ : θ = 0 ∨ ((θ = 1 ∨ θ = -1) ∧ 7 / 8 ≤ β ∧ c / (M : ℝ) ^ 3 ≤ 1 - β) := by
    rcases hD with h | ⟨χ, hχ, hb'⟩
    · exact Or.inl h.1
    · obtain ⟨-, h78, -, -, hS⟩ := hB χ β hχ
      refine Or.inr ⟨sign_of_sq_eq_one χ hχ.1 b hb θ hb', h78, le_trans ?_ hS⟩
      have hl : 0 < Real.log M := Real.log_pos (by linarith)
      have hl2 : Real.log M ≤ M := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
      apply div_le_div_of_nonneg_left hc.le (by positivity)
      calc (M : ℝ) ^ 2 * Real.log M ≤ (M : ℝ) ^ 2 * M := by gcongr
        _ = (M : ℝ) ^ 3 := by ring
  have := hQ M M.totient β θ (fun n => n ≡ b [MOD M]) hM3 hφ1 hφ2 hθ
    (fun u hu => by
      have := hP M b θ β u hM hb hD hu
      unfold psiAP at this
      convert this) X hX
  convert this

end GlobalTheory.Lin
end

