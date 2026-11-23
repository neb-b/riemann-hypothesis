module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.ProjectiveLattices.HostRank
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0013
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0077
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0092
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0105
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0097
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0093
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0102
public import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
public import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
public import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0065
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0069
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0071
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0088
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0100
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0099

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.DeltaNeZero
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

noncomputable section

namespace GlobalTheory.ThetaMove.SeamMoves

variable {X : Fields} {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ)
  (cD : D.what₂.Tau → ℂ)

def reidx (a b : ℕ) : VCx X.Tau a b ≃ₗ[ℂ] TaylorLogMetric.VC D a b := LinearEquiv.funCongrLeft ℂ (Fin b → Fin a → ℂ) s.iT.symm

theorem form_reidx (A : ℝ) (a b : ℕ) (x y : VCx X.Tau a b) :
    formV A D.what₂.Tau a b (reidx s a b x) (reidx s a b y) = Formalism.L2.Ker.HV A⁻¹ x y := by
  change (∑ τ, ∑ i, ∑ j, x (s.iT.symm τ) i j * (starRingEnd ℂ) (y (s.iT.symm τ) i j)) / (A : ℂ) =
    ((A⁻¹ : ℝ) : ℂ) * ∑ τ, ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)
  rw [Equiv.sum_comp s.iT.symm (fun τ => ∑ i, ∑ j, x τ i j * (starRingEnd ℂ) (y τ i j)), Complex.ofReal_inv, div_eq_inv_mul]

theorem isHerm_formV (A : ℝ) (n : Type) [Fintype n] (a b : ℕ) : IsHerm (formV A n a b) := by
  intro x y
  set_option synthInstance.maxHeartbeats 100000 in
    simp [formV, map_sum, mul_comm]

theorem iop_eq {a b : ℕ} (Λ₁ Λ₂ : AddSubgroup (TaylorLogMetric.VC D a b)) (G : TaylorLogMetric.VC D a b → ℂ) :
    TaylorLogMetric.Iop D B.tor Λ₁ Λ₂ G = inter (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (TaylorLogMetric.al D B.tor) Λ₁ Λ₂ G := rfl

theorem alV_eq {a b : ℕ} (x : VCx X.Tau a b) {m : ℤ}
    (hm : Real.sqrt D.host.d / 2 * (TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x)).re = (m : ℝ)) :
    alV D.host.d (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x = TaylorLogMetric.al D B.tor (reidx s a b x) := by
  have h1 : TaylorLogMetric.Hf D B.tor (reidx s a b x) (reidx s a b x) = Formalism.L2.Ker.HV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ))⁻¹ x x :=
    form_reidx s _ a b x x
  unfold TaylorLogMetric.al
  rw [hm, round_intCast]
  rw [h1] at hm
  unfold alV alphaQ Formalism.L2.Th1.H.qOf
  rw [hm, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  push_cast
  ring

include B in
theorem delta_ne_zero : δ ≠ 0 := by
  rintro rfl
  have h1 : B.L.ω₁ ∈ B.L.lattice.toAddSubgroup := B.L.ω₁_mem_lattice
  have h2 : TaylorLogMetric.lamOf D cc 0 ≤ ⊥ := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro w ⟨c, -, rfl⟩
    simp
  rw [B.lat] at h1
  have h3 : B.L.ω₁ = 0 := AddSubgroup.mem_bot.1 (h2 h1)
  exact B.L.indep.ne_zero 0 h3

theorem aa_ne_bot (hcc : cc ≠ ⊥) : (ambOf s B χ cD).AA ≠ ⊥ := by
  intro h
  have h1 : ((Ideal.absNorm cc : ℕ) : X.E) ∈ (ambOf s B χ cD).AA := by
    refine Submodule.subset_span ⟨_, Ideal.absNorm_mem cc, 1, Formalism.L2.Pj.one_mem_inverse_halfDifferent D, ?_⟩
    simp
  rw [h, Submodule.mem_bot, Nat.cast_eq_zero, Ideal.absNorm_eq_zero_iff] at h1
  exact hcc h1

theorem aa_fg : (ambOf s B χ cD).AA.FG := by
  let j : 𝓞 D.host.E →+* 𝓞 X.E := RingOfIntegers.mapRingHom (s.iE.symm : D.host.E →+* X.E)
  have hj : ∀ a : 𝓞 D.host.E, ((j a : 𝓞 X.E) : X.E) = s.iE.symm (a : D.host.E) := fun _ => rfl
  obtain ⟨z, hz, hden⟩ := D.host.AA0.isFractional
  have hz0 : j z ≠ 0 := fun h => nonZeroDivisors.ne_zero hz (by
    have h1 := hj z
    rw [h] at h1
    have h2 : (z : D.host.E) = 0 := s.iE.symm.injective (by rw [← h1]; simp)
    exact RingOfIntegers.coe_injective (by simpa using h2))
  have hfr : IsFractional (nonZeroDivisors (𝓞 X.E)) (ambOf s B χ cD).AA := by
    refine (FractionalIdeal.isFractional_span_iff).2 ⟨j z, mem_nonZeroDivisors_of_ne_zero hz0, ?_⟩
    rintro r ⟨c, -, t, ht, rfl⟩
    obtain ⟨w, hw⟩ := hden t ht
    refine ⟨j (algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w), ?_⟩
    rw [Algebra.smul_def]
    change ((j _ : 𝓞 X.E) : X.E) = ((j z : 𝓞 X.E) : X.E) * _
    rw [hj, hj, ← map_mul]
    congr 1
    have e : ((algebraMap (𝓞 D.host.K) (𝓞 D.host.E) c * w : 𝓞 D.host.E) : D.host.E) =
      ((c : D.host.K) : D.host.E) * (w : D.host.E) := rfl
    have hw' : (w : D.host.E) = (z : D.host.E) * t := by rw [Algebra.smul_def] at hw; exact hw
    rw [e, hw']
    ring
  exact FractionalIdeal.fg_of_isNoetherianRing le_rfl ⟨_, hfr⟩

theorem vac_eq {a b : ℕ} (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))
    (h : Base.chiFac χ a b (s.lat N) (s.lat N') ≠ 0) :
    vac (ambOf s B χ cD) N N' = fun z => B.thMoved a b (s.lat N) (s.lat N') (reidx s a b z) := by
  funext z
  exact inv_mul_cancel_left₀ h _

theorem moves_ambOf : ∀ (X : Fields) (D : D7) (s : Seam D X) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (a b : ℕ), X.Ok → s.Ok → TaylorLogMetric.IsCurveIdeal D cc → TaylorLogMetric.IsChi D χ → B.EqP χ → B.LatAll → B.ThZeroMem a b → Even a → Even b → Moves (ambOf s B χ cD) a b := by
  intro X D s cc δ B χ cD a b hX hs hcc hχ hE hL hZ ha hb
  obtain ⟨hsd, hlam⟩ := _root_.GlobalTheory.PeriodTransport.seam_lattices X D s cc δ B χ cD hs
  obtain ⟨hth, hm1, hm2⟩ := _root_.GlobalTheory.ThetaMove.Moved.thMoved_mem_and_moves D cc δ B χ a b hχ hE hL hZ ha hb
  have hq := _root_.GlobalTheory.ThetaMove.qIntAll_of_latAll D cc δ B hL
  have hadm : ∀ (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)), IsSdLat N → IsSdLat N' →
      TaylorLogMetric.admitted D a b (s.lat N) (s.lat N') := fun N N' h h' => ⟨ha, hb, hsd _ _ h, hsd _ _ h'⟩
  have key := fun (N₁ N₂ : Submodule (𝓞 X.E) (Sp X.E a)) (N₁' N₂' : Submodule (𝓞 X.E) (Sp X.E b)) (h : IsSdLat N₂)
      (h' : IsSdLat N₂') (θ : TaylorLogMetric.VC D a b → ℂ) =>
    Transport.inter_transport _ _ (reidx s a b) (Formalism.L2.Ker.HV (ambOf s B χ cD).sc)
      (formV (TaylorLogMetric.area (TaylorLogMetric.lamOf D cc δ)) D.what₂.Tau a b) (alV (ambOf s B χ cD).d (ambOf s B χ cD).sc) (TaylorLogMetric.al D B.tor)
      (lam (ambOf s B χ cD) N₁ N₁') (lam (ambOf s B χ cD) N₂ N₂') (TaylorLogMetric.La D B.tor (s.lat N₁) (s.lat N₁'))
      (TaylorLogMetric.La D B.tor (s.lat N₂) (s.lat N₂')) θ (form_reidx s _ a b) (hlam a b N₁ N₁') (hlam a b N₂ N₂')
      (fun x hx => by
        obtain ⟨m, hm⟩ := hq a b _ _ (hadm N₂ N₂' h h') (reidx s a b x) ((hlam a b N₂ N₂' x).1 hx)
        exact alV_eq s B x hm)
      (isHerm_formV _ _ _ _) (hL.1 a b _ _ (hadm N₂ N₂' h h')).1 (hL.1 a b _ _ (hadm N₂ N₂' h h')).2
  refine ⟨delta_ne_zero B, Fintype.card_pos_iff.1 hX.f_pos, aa_fg s B χ cD, aa_ne_bot s B χ cD hcc.1, ?_, ?_, ?_⟩
  · intro N N' h h'
    obtain ⟨hc, han, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    obtain ⟨h1, h2, h3⟩ := (key N N N' N' h h' 0).1
    refine ⟨hc, ?_, h1, h2⟩
    rw [vac_eq s B χ cD N N' hc]
    refine ⟨fun z _ => ?_, h3 _ hfix⟩
    exact (han _ (Set.mem_univ _)).comp ((reidx s a b).toLinearMap.toContinuousLinearMap.analyticAt z)
  · intro N N' N'' h h' h''
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N N'' (hth _ _ (hsd _ _ h) (hsd _ _ h'')).1,
      (key N N N' N'' h h'' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N N'' h h'')).1,
      hm1 _ _ _ (hsd _ _ h) (hsd _ _ h') (hsd _ _ h''), iop_eq]
  · intro N N₁ N' h h₁ h'
    obtain ⟨hc, -, hfix⟩ := hth _ _ (hsd _ _ h) (hsd _ _ h')
    rw [vac_eq s B χ cD N N' hc, vac_eq s B χ cD N₁ N' (hth _ _ (hsd _ _ h₁) (hsd _ _ h')).1,
      (key N N₁ N' N' h₁ h' _).2 hfix (hL.2 a b _ _ _ _ (hadm N N' h h') (hadm N₁ N' h₁ h')).1,
      hm2 _ _ _ (hsd _ _ h) (hsd _ _ h₁) (hsd _ _ h'), iop_eq]

end GlobalTheory.ThetaMove.SeamMoves
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsNatMulIntegral
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions Formalism.L2.Th1.H GlobalTheory.ThetaMove GlobalTheory.IndefiniteRowSideFullHecke.IndexExponentDegree

namespace GlobalTheory.ThetaMove.CommonRef

section

variable {E : Type} [Field E] [NumberField E] {W : Type} [AddCommGroup W] [Module (𝓞 E) W] [Module E W] [IsScalarTower (𝓞 E) E W]

theorem exists_nat_mul_integral (a : E) : ∃ n : ℕ, 0 < n ∧ ∃ r : 𝓞 E, (n : E) * a = algebraMap (𝓞 E) E r := by
  have ha : IsAlgebraic ℤ a := (IsFractionRing.isAlgebraic_iff ℤ ℚ E).2 (Algebra.IsAlgebraic.isAlgebraic a)
  obtain ⟨y, hy, hint⟩ := ha.exists_integral_multiple
  refine ⟨y.natAbs, Int.natAbs_pos.2 hy, ?_⟩
  have h2 : IsIntegral ℤ ((y.natAbs : E) * a) := by
    rw [zsmul_eq_mul] at hint
    rcases Int.natAbs_eq y with h | h
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_natCast] at this
      rwa [this] at hint
    · have := congrArg (Int.cast : ℤ → E) h
      rw [Int.cast_neg, Int.cast_natCast] at this
      rw [this, neg_mul] at hint
      simpa using hint.neg
  exact ⟨⟨_, h2⟩, rfl⟩

theorem full_of_span {M : Submodule (𝓞 E) W} (hM : Submodule.span E (M : Set W) = ⊤) : Full M := by
  intro x
  have hx : x ∈ Submodule.span E (M : Set W) := hM ▸ Submodule.mem_top
  induction hx using Submodule.span_induction with
  | mem x hx => exact ⟨1, Nat.one_pos, by simpa using hx⟩
  | zero => exact ⟨1, Nat.one_pos, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, hy⟩ := hy
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    rw [smul_add]
    refine M.add_mem ?_ ?_
    · rw [Nat.cast_mul, mul_comm, mul_smul]; exact M.smul_mem _ hx
    · rw [Nat.cast_mul, mul_smul]; exact M.smul_mem _ hy
  | smul a x _ hx =>
    obtain ⟨n, hn, hx⟩ := hx
    obtain ⟨m, hm, r, hr⟩ := exists_nat_mul_integral a
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have : ((n * m : ℕ) : 𝓞 E) • a • x = r • (n : 𝓞 E) • x := by
      simp only [← algebraMap_smul E (_ : 𝓞 E), smul_smul, map_natCast, ← hr]
      congr 1
      push_cast
      ring
    rw [this]
    exact M.smul_mem _ hx

omit [Module E W] [IsScalarTower (𝓞 E) E W] in
theorem exists_nat_smul_le {M N : Submodule (𝓞 E) W} (hM : Full M) (hN : N.FG) :
    ∃ m : ℕ, 0 < m ∧ ∀ x ∈ N, (m : 𝓞 E) • x ∈ M := by
  first
  | exact @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg
  | (apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FinitelyGeneratedNatMultiple.exists_nat_smul_mem_of_fg ..)

theorem smul_mem_locP {M N : Submodule (𝓞 E) W} {m : ℕ} (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (Q : HeightOneSpectrum (𝓞 E))
    {x : W} (hx : x ∈ localization₂ Q.asIdeal N) : (m : E) • x ∈ localization₂ Q.asIdeal M := by
  obtain ⟨s, hs, hx⟩ := hx
  refine ⟨s, hs, ?_⟩
  have := h _ hx
  rwa [smul_comm, Nat.cast_smul_eq_nsmul, ← Nat.cast_smul_eq_nsmul E] at this

theorem mem_localization_of_inv_smul_mem {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m) (h : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M)
    (Q : HeightOneSpectrum (𝓞 E)) {x : W} (hx : (m : E)⁻¹ • x ∈ localization₂ Q.asIdeal N) : x ∈ localization₂ Q.asIdeal M := by
  have hmE : (m : E) ≠ 0 := by exact_mod_cast hm.ne'
  have := smul_mem_locP h Q hx
  rwa [smul_smul, mul_inv_cancel₀ hmE, one_smul] at this

theorem dom_twO [StarRing E] (S : Finset (HeightOneSpectrum (𝓞 E))) {M N : Submodule (𝓞 E) W} {m : ℕ} (hm : 0 < m)
    (h₁ : ∀ x ∈ N, (m : 𝓞 E) • x ∈ M) (h₂ : ∀ x ∈ M, (m : 𝓞 E) • x ∈ N)
    (hQ : ∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M = localization₂ Q.asIdeal N) :
    Dom S M (twist₂ N m (expS S)) ∧ Dom S (twist₂ N m fun Q => -expS S Q) M := by
  have hb := expS_bound S
  have hb' : ∀ Q, -1 ≤ -expS S Q ∧ -expS S Q ≤ 1 := fun Q => by have := hb Q; omega
  refine ⟨⟨fun P hP x hx => ?_, fun Q hS x hx => ?_⟩, fun P hP x hx => ?_, fun Q hS x hx => ?_⟩
  · rw [mem_localization_twist N hm hb] at hx
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_one] at hx
    exact mem_localization_of_inv_smul_mem hm h₁ P hx
  · rw [mem_localization_twist N hm hb]
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, zpow_neg_one, inv_inv]
      exact smul_mem_locP h₂ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, zpow_zero, inv_one, one_smul, ← hQ Q hS hc]
      exact hx
  · rw [mem_localization_twist N hm hb']
    have e : expS S P = 1 := by simp [expS, hP]
    rw [e, zpow_neg_one, inv_inv]
    exact smul_mem_locP h₂ P hx
  · rw [mem_localization_twist N hm hb'] at hx
    by_cases hc : conjPrime₂ Q ∈ S
    · have e : expS S Q = -1 := by simp [expS, hS, hc]
      rw [e, neg_neg, zpow_one] at hx
      exact mem_localization_of_inv_smul_mem hm h₁ Q hx
    · have e : expS S Q = 0 := by simp [expS, hS, hc]
      rw [e, neg_zero, zpow_zero, inv_one, one_smul, ← hQ Q hS hc] at hx
      exact hx

end

theorem common_refinement : ∀ (E : Type) [Field E] [NumberField E] [StarRing E] (n : ℕ) (M₁ M₂ : Submodule (𝓞 E) (Sp E n)) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ P ∈ S, conjPrime₂ P ∉ S) → IsSdLat M₁ → IsSdLat M₂ → (∀ Q : HeightOneSpectrum (𝓞 E), Q ∉ S → conjPrime₂ Q ∉ S → localization₂ Q.asIdeal M₁ = localization₂ Q.asIdeal M₂) → ∃ F G : Submodule (𝓞 E) (Sp E n), IsSdLat F ∧ IsSdLat G ∧ Dom S M₁ F ∧ Dom S M₂ F ∧ Dom S G M₁ ∧ Dom S G M₂ := by
  intro E _ _ _ n M₁ M₂ S hS h₁ h₂ hQ
  have hfull (L : Submodule (𝓞 E) (Sp E n)) (hL : IsSdLat L) : Full L := by
    apply full_of_span
    let W := Submodule.span E (L : Set (Sp E n))
    change W = ⊤
    by_contra h
    let e : Sp E n ≃ₗ⋆[E] Sp E n := starLinearEquiv E
    let g : Sp E n →ₗ[E] Module.Dual E W :=
      (LinearMap.domRestrict' W).comp ((hStd E n).comp e.toLinearMap)
    have hdim : Module.finrank E (Module.Dual E W) < Module.finrank E (Sp E n) := by
      rw [Subspace.dual_finrank_eq]
      exact Submodule.finrank_lt h
    obtain ⟨x, hx, hx₀⟩ :=
      Submodule.exists_mem_ne_zero_of_ne_bot (LinearMap.ker_ne_bot_of_finrank_lt (f := g) hdim)
    have hsmul (a : E) : a • e x ∈ L := by
      rw [← hL.2, dualBasic_mem_dual]
      intro y hy
      apply hStd_mem_one_symm
      have hxy : hStd E n (e x) y = 0 :=
        congrArg (fun f : Module.Dual E W => f ⟨y, Submodule.subset_span hy⟩) (LinearMap.mem_ker.mp hx)
      simp [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hxy]
    let i : E →ₗ[𝓞 E] L :=
      ((LinearMap.toSpanSingleton E _ (e x)).restrictScalars (𝓞 E)).codRestrict L hsmul
    let : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.1.fg
    let : Module.Finite (𝓞 E) E := Module.Finite.of_injective i fun a b hab =>
      smul_left_injective E (fun hzero => hx₀ (e.map_eq_zero_iff.mp hzero)) (congrArg Subtype.val hab)
    exact RingOfIntegers.not_isField E
      (isField_of_isIntegral_of_isField (IsFractionRing.injective (𝓞 E) E) (Field.toIsField E))
  obtain ⟨a, ha, hA⟩ := exists_nat_smul_le (hfull M₁ h₁) h₂.1.fg
  obtain ⟨b, hb, hB⟩ := exists_nat_smul_le (hfull M₂ h₂) h₁.1.fg
  have hm : 0 < a * b := Nat.mul_pos ha hb
  have hA' : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₁ := fun x hx => by
    rw [Nat.cast_mul, mul_comm, mul_smul]; exact M₁.smul_mem _ (hA x hx)
  have hB' : ∀ x ∈ M₁, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => by
    rw [Nat.cast_mul, mul_smul]; exact M₂.smul_mem _ (hB x hx)
  have hC : ∀ x ∈ M₂, ((a * b : ℕ) : 𝓞 E) • x ∈ M₂ := fun x hx => M₂.smul_mem _ hx
  obtain ⟨hF, hG⟩ := GlobalTheory.ThetaMove.TwistSd.isSdLat_twO_expS E n M₂ (a * b) S hS h₂ hm
  obtain ⟨d₁, d₂⟩ := dom_twO S hm hA' hB' hQ
  obtain ⟨d₃, d₄⟩ := dom_twO S hm hC hC fun _ _ _ => rfl
  exact ⟨_, _, hF, hG, d₁, d₃, d₂, d₄⟩

end GlobalTheory.ThetaMove.CommonRef
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsWeightsInWindows
section
namespace GlobalTheory.EX

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem exists_weights_in_windows : ∀ (eps : ℝ) (C : FC), 0 < eps → eps < 1 / 52 → Std C → ∃ x0 : ℝ,
    ∀ (s : Scale) (R : Ranks) (H : Host R), s.eps = eps → x0 ≤ s.x → RankVal s R →
      ∃ a b : R.A → ℤ, WinOK s C.GK H a b := by
  intro eps C h0 h1 hS
  have hLa : 1 ≤ C.GK.La := hS.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1 _ (by simp [FC.cMid])
  obtain ⟨CN, x1, hN⟩ := GlobalTheory.topCount_and_lambda_bounds eps h0 h1
  obtain ⟨x2, hP⟩ := GlobalTheory.scale_poly_comparison eps 17 1 h0 one_pos
  obtain ⟨x3, hR⟩ := GlobalTheory.EX.rank_basic_bounds eps h0 h1
  refine ⟨max x1 (max x2 x3), fun s R H he hx hRV => ?_⟩
  have hx1 : x1 ≤ s.x := le_trans (le_max_left _ _) hx
  have hx2 : x2 ≤ s.x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx3 : x3 ≤ s.x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  obtain ⟨-, -, hK⟩ := hN s he hx1
  have hLa1 := (hK C.GK hLa).1
  obtain ⟨-, -, hb, -, hb', -⟩ := hP s he hx2
  obtain ⟨-, -, hr, hkr, -⟩ := hR s R he hx3 hRV
  have hx1' : 1 ≤ s.x := s.one_lt_alt.le
  have hxp : 0 < s.x := lt_of_lt_of_le one_pos hx1'
  have hk5 : (R.k : ℝ) ≤ s.x ^ (5 : ℝ) := le_trans (by exact_mod_cast hkr) hr
  have hk0 : (0 : ℝ) < R.k := by
    have := R.m_add_three_le_k
    exact_mod_cast (by omega : 0 < R.k)
  have hX : 1 ≤ s.X' := Real.one_le_exp (Real.rpow_nonneg hxp.le _)
  rw [Real.rpow_one] at hb
  rw [sub_self, Real.rpow_zero, one_mul] at hb'
  have h17 : 0 < s.x ^ (17 : ℝ) := Real.rpow_pos_of_pos hxp _
  have hb17 : s.x ^ (17 : ℝ) ≤ s.b := le_trans (le_mul_of_one_le_right h17.le hX) hb
  have hA : 1 ≤ s.a / ((R.k : ℝ) * s.x ^ (Scale.A / 2)) := by
    have h13 : 0 < s.x ^ (Scale.A / 2) := Real.rpow_pos_of_pos hxp _
    rw [le_div_iff₀ (mul_pos hk0 h13), one_mul]
    calc (R.k : ℝ) * s.x ^ (Scale.A / 2) ≤ s.x ^ (5 : ℝ) * s.x ^ (Scale.A / 2) :=
          mul_le_mul_of_nonneg_right hk5 h13.le
      _ = s.x * s.x ^ (17 : ℝ) := by
          rw [← Real.rpow_add hxp, ← Real.rpow_one_add' hxp.le (by norm_num)]
          congr 1
          unfold Scale.A
          norm_num
      _ ≤ s.a := mul_le_mul_of_nonneg_left hb17 hxp.le
  have hB : 1 ≤ 2 * (R.n : ℝ) * s.delta1 * s.x ^ s.eps * G.La C.GK s * s.b' / (R.k : ℝ) := by
    rw [le_div_iff₀ hk0, one_mul]
    have hn : (1 : ℝ) ≤ R.n := by
      have : 1 ≤ R.n := R.ord_pos
      exact_mod_cast this
    have hd : 1 ≤ s.delta1 * s.x ^ s.eps := by
      unfold Scale.delta1
      rw [← Real.rpow_add hxp]
      exact Real.one_le_rpow hx1' (by have := s.eps_pos; linarith)
    have hL : 1 ≤ G.La C.GK s := le_trans (Real.one_le_rpow hx1' s.eps_pos.le) hLa1
    have hkb : (R.k : ℝ) ≤ s.b' :=
      le_trans hk5 (le_trans (Real.rpow_le_rpow_of_exponent_le hx1' (by norm_num)) hb')
    have h2 : (1 : ℝ) ≤ 2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s :=
      one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by linarith) hd) hL
    calc (R.k : ℝ) ≤ s.b' := hkb
      _ ≤ (2 * (R.n : ℝ) * (s.delta1 * s.x ^ s.eps) * G.La C.GK s) * s.b' :=
          le_mul_of_one_le_left (le_trans hk0.le hkb) h2
      _ = _ := by ring
  refine ⟨fun _ => ⌈s.a⌉, fun _ => ⌈s.b'⌉, fun t _ => ⟨⟨Int.le_ceil _, ?_⟩, Int.le_ceil _, ?_⟩⟩
  · have := Int.ceil_lt_add_one s.a
    linarith
  · have := Int.ceil_lt_add_one s.b'
    linarith

end GlobalTheory.EX
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FixAndWinOfNumAt
section
namespace GlobalTheory.EX.DC

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

theorem fix_and_win_of_numAt (eps : ℝ) (C : FC) (Fm : FamP eps) (hS : Std C) (hO : Fm.cOut = C.cOut)
    (hN : ∀ x (i : Fm.Ix x), Nonempty (NumAt C (Fm.L x i))) : DC.PageFix Fm ∧ DC.PageWin Fm := by
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, sCt⟩, sCc, -, -, scw, sCYL, -, sCp, seP, scTO, -, sCe, -⟩ := hS
  simp only [FamP.cOut, FC.cOut, List.cons.injEq] at hO
  obtain ⟨oCt, oCc, -, -, -, ocw, oCYL, -, -, -, oCp, oeP, ocTO, -, oCe, -⟩ := hO
  refine ⟨⟨oCp.trans sCp, oeP.trans seP, ?_, ?_, oCe.trans sCe, oCc.trans sCc, ocw.trans scw, oCYL.trans sCYL,
    fun x hx i => ?_⟩, fun x hx i => ?_⟩
  · rw [ocTO, oeP, scTO, seP]; norm_num
  · rw [ocTO, oCt, scTO, sCt]; norm_num
  · obtain ⟨N⟩ := hN x i
    refine ⟨N.ccK_top, N.cloud1, N.g_le, N.pde_lt.1, N.pde_lt.2, N.logFiveDepth_eq, ?_, ?_⟩
    · have h := N.Lw_eq
      rw [Fm.L_x x i hx, Fm.L_eps x i, ← oCt] at h
      exact h
    · have h := (Fm.parT x hx i).TO_eq
      rw [Fm.parT_cTO, Fm.L_x x i hx] at h
      exact h
  · obtain ⟨N⟩ := hN x i
    have h := N.win
    rw [Fm.L_x x i hx, Fm.L_eps x i] at h
    exact h

end GlobalTheory.EX.DC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.HasWithDutyWallAndChoices
section
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

namespace GlobalTheory.EX.DC

theorem has_withDuty_wall_and_choices {Q : PtProp} {C : FC} {cD ch C8 C5 c6 Cb : ℝ} (p : Pt C) {R : Ranks} {H : Host R} {q0 : ℕ}
    {a b : R.A → ℤ} {M : ℕ} {c : Fin M → Fin (R.k - 2) → Bool} {u0 : ℕ} (hC : Std C) (hT : H.CT2 = C.CT2)
    (hH : HostGood p.L.sc C8 C5 c6 Cb H q0) (hq : (q0 : ℝ) < p.L.sc.X')
    (h0 : ∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) (hW : WOK p.L.sc cD ch C.GK H a b)
    (hV : Val C cD ch p.L) (hF : p.From H a b c u0) (hI : CanonInst p.ta.Gx) (hQ : p.Has Q) :
    p.Has ((withDuty Q).and WallPt) ∧ ThickSetLowerBound p.L ∧ ChBad_at p.ta.Gx Cb ∧ ChQD_at p.D p.L.sc.x p.L.sc.eps C5 := by
  have hw := GlobalTheory.EX.wreq_of_wok C cD ch p R H a b M c u0 hC hV hF hI h0 hW
  obtain ⟨hv, -, hT2, -, hQD, hBox, -, -, hBad, -, -, -, ⟨hp, hmod, -, hne, hne'⟩, hlev⟩ := hH
  have hb := GlobalTheory.EX.chBad_of_from C p R H a b M c u0 Cb hF hI hBad
  have eS := hF.QS_eq
  have hBW := hF.boxesW hBox
  have hQW := hF.qdRowsW hBox
  obtain ⟨eR, -, eT2, eq, ed, eg, ep, ep', hsub, -⟩ := hF
  subst eR
  have hq0 : (0 : ℝ) < q0 := by exact_mod_cast hp.pos
  have hXb := X'_le_b p.L.sc
  refine ⟨⟨⟨hQ, hw, ?_, ?_, q0, hsub (by rw [hlev]; simp), hp, ?_, ?_, hq, ?_, ?_, ?_⟩,
    ⟨hV.mem_box.1, hV.mem_box.2, hw⟩⟩, ?_, hb, ?_⟩
  · exact hBW
  · exact hQW
  · rw [eS, eq, ed]; exact hmod
  · rw [Real.log_le_iff_le_exp hq0]
    exact hq.le.trans hXb
  · rw [ep]; exact hne
  · rw [ep']; exact hne'
  · intro i hi
    have hg := (hv.2.2.2.2.1 i).1
    rw [← eg, ← hi] at hg
    have hk : (1 : ℝ) ≤ p.D.R.k := by
      have := p.D.R.m_add_three_le_k
      exact_mod_cast (by omega : 1 ≤ p.D.R.k)
    have hb1 : 1 ≤ p.L.sc.b := Real.one_le_exp (Real.rpow_nonneg (by linarith [p.L.sc.one_lt_alt]) _)
    have h5 : p.L.sc.b ≤ (p.D.R.k : ℝ) * p.L.sc.b := le_mul_of_one_le_left (by linarith) hk
    have h6 : (p.D.R.k : ℝ) * p.L.sc.b ≤ ((p.D.R.k : ℝ) * p.L.sc.b) ^ 8 := le_self_pow₀ (by linarith) (by norm_num)
    linarith
  · unfold ThickSetLowerBound Host.secondSet_card_lower_bound
    rw [eT2, hV.secondConstant_eq, hV.host.2.2.2.2.2.1, ← hT, ← hv.2.2.2.2.2.1]
    exact hT2
  · unfold ChQD_at
    rw [eq, ed]
    exact hQD

end GlobalTheory.EX.DC
end

