module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0107
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0104
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SmallTorsionKilledByPrimePowers
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0121
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0119
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0124
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.WeightFloorInequalities
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpSeriesMultiplicativeShiftCompAndSubst
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.CmLatticeWeylOperatorEqThetaRootOfUnityShift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0105

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TranslateCoprimeOrderNotIncreaseThetaCombNorm
section
noncomputable section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslNorm

lemma inOK_zero (d : ℕ) : InOK d 0 := ⟨0, 0, by simp⟩

lemma inOK_natMul {d : ℕ} {z : ℂ} (n : ℕ) (h : InOK d z) : InOK d ((n : ℂ) * z) := by
  obtain ⟨u, v, rfl⟩ := h
  exact ⟨n * u, n * v, by push_cast; ring⟩

lemma not_inOK_half {d : ℕ} (hd : 0 < d) : ¬ InOK d (0 - 1 / 2) := by
  rintro ⟨u, v, h⟩
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr (by exact_mod_cast hd)
  have him := congrArg Complex.im h
  have hre := congrArg Complex.re h
  simp [wK] at him hre
  have hv : v = 0 := by
    rcases him with h | h
    · exact h
    · exfalso; first | exact hs.ne' h | omega
  subst hv
  simp at hre
  have h2 : ((2 * u : ℤ) : ℝ) = ((-1 : ℤ) : ℝ) := by push_cast; rw [← hre]; norm_num
  have h3 : 2 * u = -1 := by exact_mod_cast h2
  omega

lemma exists_common {d q m : ℕ} (s : Fin m → ℂ) (t : ℂ) (hs : ∀ j, PrimeTo d q (s j)) (ht : PrimeTo d q t) :
    ∃ S : ℕ, 0 < S ∧ Nat.Coprime S q ∧ InOK d ((S : ℂ) * t) ∧ ∀ j, InOK d ((S : ℂ) * s j) := by
  classical
  choose n hn0 hnq hn using hs
  obtain ⟨k, hk0, hkq, hk⟩ := ht
  refine ⟨k * ∏ j, n j, Nat.mul_pos hk0 (Finset.prod_pos fun j _ => hn0 j),
    Nat.Coprime.mul_left hkq (Nat.Coprime.prod_left fun j _ => hnq j), ?_, fun j => ?_⟩
  · have := inOK_natMul (∏ j, n j) hk
    convert this using 1
    rw [Nat.cast_mul]; ring
  · have := inOK_natMul (k * ∏ i ∈ Finset.univ.erase j, n i) (hn j)
    convert this using 1
    rw [← Finset.mul_prod_erase Finset.univ n (Finset.mem_univ j)]
    simp only [Nat.cast_mul]; ring

lemma differentiable_U1 (d : ℕ) (x : ℂ) {F : ℂ → ℂ} (hF : Differentiable ℂ F) : Differentiable ℂ (U1 d x F) := by
  unfold U1 h1
  fun_prop

variable {q : ℕ} [Fact q.Prime]

lemma bd_pow {f : ℂ_[q]⟦X⟧} (hf : Bd 1 f) (a : ℕ) : Bd 1 (f ^ a) := by
  induction a with
  | zero =>
    intro n
    rw [pow_zero, coeff_one]
    split_ifs <;> simp
  | succ a ih =>
    have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ ih hf).2
    rwa [one_mul, ← pow_succ] at this

lemma hat_mul (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {F G : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (hG : AnalyticAt ℂ G 0) :
    hat ι ℓ (fun z => F z * G z) = hat ι ℓ F * hat ι ℓ G :=
  ((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 F G hF hG).2.1

lemma hat_pow (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {F : ℂ → ℂ}
    (hF : AnalyticAt ℂ F 0) (a : ℕ) : hat ι ℓ (fun z => F z ^ a) = hat ι ℓ F ^ a := by
  induction a with
  | zero =>
    have := (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 1
    simpa using this
  | succ a ih =>
    simp only [pow_succ]
    rw [hat_mul ι hl (F := fun z => F z ^ a) (by fun_prop) hF, ih]

lemma hat_comb (ι : ℂ ≃+* ℂ_[q]) {ℓ : ℂ_[q]⟦X⟧} (hl : constantCoeff ℓ = 0) {κ : Type} (T : Finset κ)
    (c : κ → ℂ_[q]) (F : κ → ℂ → ℂ) (hF : ∀ j, AnalyticAt ℂ (F j) 0) (a : ℕ) :
    hat ι ℓ (fun z => ∑ j ∈ T, ι.symm (c j) * F j z ^ a) = ∑ j ∈ T, C (c j) * hat ι ℓ (F j) ^ a := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have := (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1 0
    simpa using this
  | insert i T hi ih =>
    simp only [Finset.sum_insert hi]
    have hi' := hF i
    have h1 : AnalyticAt ℂ (fun z => ι.symm (c i) * F i z ^ a) 0 := by fun_prop
    have h2 : AnalyticAt ℂ (fun z => ∑ j ∈ T, ι.symm (c j) * F j z ^ a) 0 :=
      Finset.analyticAt_fun_sum _ fun j _ => by have := hF j; fun_prop
    rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).1 _ _ h1 h2).1, ih,
      hat_mul ι hl (F := fun _ => ι.symm (c i)) (G := fun z => F i z ^ a) analyticAt_const (by fun_prop),
      hat_pow ι hl hi', (GlobalTheory.MomOne.TaylorRead.hat_laws q ι ℓ hl).2.1]
    simp

lemma bd_scale_iff (ι : ℂ ≃+* ℂ_[q]) (ω : ℂ_[q]) {S : ℕ} (hS : Nat.Coprime S q) {G : ℂ → ℂ}
    (hG : AnalyticAt ℂ G 0) (B : ℝ) :
    Bd B (hat ι (C ω * logS) (fun z => G ((S : ℂ) * z))) ↔ Bd B (hat ι (C ω * logS) G) := by
  rw [(GlobalTheory.MomOne.hat_multiplicative_chart q ι ω G hG).2.2.1 (S : ℂ) (S : ℤ_[q]) (by simp [zc])]
  refine (GlobalTheory.MomOne.MulSeries.mulS_laws q).2.2.2.1 _ _ _ ?_
  exact PadicInt.norm_natCast_eq_one_iff.mpr hS.symm

theorem translate_bd : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → ∀ (a m : ℕ) (c : Fin m → ℂ_[q]) (s : Fin m → ℂ) (t : ℂ) (B : ℝ), (∀ j, PrimeTo d q (s j)) → PrimeTo d q t → ¬ InOK d (t - 1 / 2) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d (s j) θ) ^ a) → Bd B (∑ j, C (c j) * hat M.ι (C ω * logS) (U1 d t (U1 d (s j) θ)) ^ a) := by
  intro d q _ M ω θ hd hd16 hsp hL hM hθ a m c s t B hs ht ht2 hB
  obtain ⟨S, hS0, hSq, hSt, hSs⟩ := exists_common s t hs ht
  have hl : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hM.2.1
  have hSne : (S : ℂ) ≠ 0 := by exact_mod_cast hS0.ne'
  have hθd : Differentiable ℂ θ := hθ.1
  have hθt : θ t ≠ 0 := fun h => ht2 (hθ.2.2.2.2 t h)
  have hU : ∀ j, Differentiable ℂ (U1 d (s j) θ) := fun j => differentiable_U1 d _ hθd
  have hUU : ∀ j, Differentiable ℂ (U1 d t (U1 d (s j) θ)) := fun j => differentiable_U1 d _ (hU j)
  have hUt : Differentiable ℂ (U1 d t θ) := differentiable_U1 d _ hθd
  have E := fun j => GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ (s j) S hS0 hSq (hSs j)
  have Et := (GlobalTheory.MomOne.ScaledQuot.scaled_quotient_elliptic d q M ω θ hd hd16 hsp hL hM hθ t S hS0 hSq hSt).2.2.2.1
  simp only at E
  set t' : ℂ := t / S with ht'
  have hSt' : (S : ℂ) * t' = t := by rw [ht']; field_simp
  set φ : ℂ → ℂ := fun z => ∑ j, M.ι.symm (c j) * (U1 d (s j) θ ((S : ℂ) * z) / θ ((S : ℂ) * z)) ^ a with hφ
  have hφan : ∀ p, θ ((S : ℂ) * p) ≠ 0 → AnalyticAt ℂ φ p := fun p hp =>
    Finset.analyticAt_fun_sum _ fun j _ => analyticAt_const.fun_mul (((E j).2.2.1 p hp).fun_pow a)
  have hφper : ∀ l ∈ M.L.lattice, ∀ z, φ (z + l) = φ z := fun l hl z =>
    Finset.sum_congr rfl fun j _ => by
      have := (E j).1.2 l hl z
      simp only at this
      rw [this]
  have hφmer : ∀ p, MeromorphicAt φ p := fun p =>
    MeromorphicAt.fun_sum fun j _ => (MeromorphicAt.const _ _).fun_mul (((E j).1.1 p).fun_pow a)
  have h0 : θ ((S : ℂ) * 0) ≠ 0 := by rw [mul_zero, hθ.2.1]; exact one_ne_zero
  have h0' : θ ((S : ℂ) * t') ≠ 0 := by rw [hSt']; exact hθt
  have hφ0 := hφan 0 h0
  have hφt := hφan t' h0'
  have hφt0 : AnalyticAt ℂ (fun z => φ (z + t')) 0 :=
    AnalyticAt.comp_of_eq hφt (f := fun z => z + t') (by fun_prop) (zero_add _)
  have hθS : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z)) 0 :=
    (show Differentiable ℂ (fun z => θ ((S : ℂ) * z)) by fun_prop).analyticAt 0
  have hUtS : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z)) 0 :=
    (show Differentiable ℂ (fun z => U1 d t θ ((S : ℂ) * z)) by fun_prop).analyticAt 0

  have hBφ : Bd B (hat M.ι (C ω * logS) φ) := by
    have hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ z ^ a) := by fun_prop
    rw [← hat_comb M.ι hl _ c _ (fun j => (hU j).analyticAt 0),
      ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)] at hB
    have hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) 0 :=
      (show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a) by
        fun_prop).analyticAt 0
    have hpr : AnalyticAt ℂ (fun z => θ ((S : ℂ) * z) ^ a * φ z) 0 := (hθS.fun_pow a).fun_mul hφ0
    have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d (s j) θ ((S : ℂ) * z) ^ a)
        = θ ((S : ℂ) * z) ^ a * φ z := by
      refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
      filter_upwards [hθS.continuousAt.eventually_ne h0] with z hz
      rw [hφ, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [div_pow]; field_simp
    rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev,
      hat_mul M.ι hl (hθS.fun_pow a) hφ0, hat_pow M.ι hl hθS] at hB
    have h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => θ ((S : ℂ) * z))) :=
      (bd_scale_iff M.ι ω hSq (hθd.analyticAt 0) 1).mpr (_root_.GlobalTheory.MomOne.theta_series_integral d q M ω θ hd hd16 hsp hL hM hθ)
    refine (GlobalTheory.MomOne.sup_norm_laws q).2.2.2.2.2 _ _ 0 B (bd_pow h1 a) ?_ (by rwa [pow_zero, one_mul])
    rw [map_pow, (GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).2.2.2.1]
    simp [hθ.2.1]

  have hBφt : Bd B (hat M.ι (C ω * logS) (fun z => φ (z + t'))) := by
    by_cases hsm : M.Small t'
    · have hpt : PrimeTo d q t' :=
        ⟨S * S, Nat.mul_pos hS0 hS0, Nat.Coprime.mul_left hSq hSq, by
          rw [Nat.cast_mul, mul_assoc, hSt']; exact hSt⟩
      have hin := (hL t').mpr ((_root_.GlobalTheory.MomOne.smallTors d q M ω hd hd16 hsp hL hM).2.2.1 t' hpt hsm)
      have : (fun z => φ (z + t')) = φ := funext fun z => hφper t' hin z
      rwa [this]
    · refine _root_.GlobalTheory.MomOne.TransNorm.translate_norm_le q M _ φ t' B hM ⟨hφmer, hφper⟩ hφ0 hφt (fun p hp => ?_) hsm ?_ hBφ
      · refine Et p 0 ⟨1, one_pos, Nat.coprime_one_left q, by simpa using inOK_zero d⟩
          (not_inOK_half hd.pos) ?_
        by_contra hne
        rw [add_zero] at hne
        exact absurd (hφan p hne).meromorphicOrderAt_nonneg (not_le.mpr hp)
      · refine _root_.GlobalTheory.MomOne.EllBdd.bdd_hat_of_ell q M _ _ hM ⟨fun p => ?_, fun l hl z => ?_⟩ hφt0 (fun p hp => ?_)
        · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + t') (hφmer _) (by fun_prop)
        · show φ (z + l + t') = φ (z + t')
          rw [add_right_comm, hφper l hl]
        · refine Et p t ht ht2 ?_
          by_contra hne
          have h2 : AnalyticAt ℂ φ (p + t') := hφan _ (by rwa [mul_add, hSt'])
          have h3 : AnalyticAt ℂ (fun z => φ (z + t')) p :=
            AnalyticAt.comp_of_eq h2 (f := fun z => z + t') (by fun_prop) rfl
          exact absurd h3.meromorphicOrderAt_nonneg (not_le.mpr hp)

  have hG : Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) z ^ a) := by fun_prop
  rw [← hat_comb M.ι hl _ c _ (fun j => (hUU j).analyticAt 0),
    ← bd_scale_iff M.ι ω hSq (hG.analyticAt 0)]
  have hGS : AnalyticAt ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) 0 :=
    (show Differentiable ℂ (fun z => ∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a) by
      fun_prop).analyticAt 0
  have hpr : AnalyticAt ℂ (fun z => U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t')) 0 := (hUtS.fun_pow a).fun_mul hφt0
  have hev : ∀ᶠ z in 𝓝[≠] (0 : ℂ), (∑ j, M.ι.symm (c j) * U1 d t (U1 d (s j) θ) ((S : ℂ) * z) ^ a)
      = U1 d t θ ((S : ℂ) * z) ^ a * φ (z + t') := by
    refine Filter.Eventually.filter_mono nhdsWithin_le_nhds ?_
    have hc : ContinuousAt (fun z => θ ((S : ℂ) * z + t)) 0 :=
      (show Differentiable ℂ (fun z => θ ((S : ℂ) * z + t)) by fun_prop).continuous.continuousAt
    filter_upwards [hc.eventually_ne (y := 0) (by simpa using hθt)] with z hz
    rw [hφ, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have key : U1 d t (U1 d (s j) θ) ((S : ℂ) * z) = U1 d t θ ((S : ℂ) * z) *
        (U1 d (s j) θ ((S : ℂ) * (z + t')) / θ ((S : ℂ) * (z + t'))) := by
      rw [mul_add, hSt']
      generalize U1 d (s j) θ = F
      simp only [U1]
      field_simp
    rw [key, mul_pow]; ring
  rw [((GlobalTheory.MomOne.TaylorRead.hat_laws q M.ι _ hl).1 _ _ hGS hpr).2.2.1 hev,
    hat_mul M.ι hl (hUtS.fun_pow a) hφt0, hat_pow M.ι hl hUtS]
  have h1 : Bd 1 (hat M.ι (C ω * logS) (fun z => U1 d t θ ((S : ℂ) * z))) :=
    (bd_scale_iff M.ι ω hSq (hUt.analyticAt 0) 1).mpr (_root_.GlobalTheory.MomOne.TranslateNorm.bd_translate d q M ω θ hd hd16 hsp hL hM hθ t ht ht2)
  have := ((GlobalTheory.MomOne.sup_norm_laws q).1 _ _ _ _ (bd_pow h1 a) hBφt).2
  rwa [one_mul] at this

end GlobalTheory.MomOne.TranslNorm
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightExponentsEmbeddingsDegree
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

noncomputable section

namespace GlobalTheory.WeightExponents

theorem tauEmb_injective (D : D7) : Function.Injective (DV.tauEmb D) := by
  intro s t h
  exact D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem conjEmb_eq {E : Type} [Field E] (τ : E →+* ℂ) :
    (starRingEnd ℂ).comp τ = ComplexEmbedding.conjugate τ := by
  ext x; simp

theorem not_inPsi_conj {D : D7} {Q : Par D} (hp : Q.PinHost) (t : D.what₂.Tau) :
    ¬ InPsi Q.H (ComplexEmbedding.conjugate (DV.tauEmb D t)) := fun h =>
  ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.not_inPsi_both Q.H _ ⟨hp.2.2.2 t, h⟩

theorem tauEmb_ne_conj {D : D7} {Q : Par D} (hp : Q.PinHost) (s t : D.what₂.Tau) :
    DV.tauEmb D s ≠ ComplexEmbedding.conjugate (DV.tauEmb D t) := fun h =>
  not_inPsi_conj hp t (h ▸ (hp.2.2.2 s : InPsi Q.H (DV.tauEmb D s)))

open Classical in
theorem wtA_apply {D : D7} {j : ℕ} (w : WeightFamilies.Wt D j) (τ : D.host.E →+* ℂ) (i : ℕ) :
    wtA w (τ, i) = ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ext0 (w.aP t) i else 0) +
      if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then ext0 (w.aM t) i else 0) := by
  unfold wtA
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← conjEmb_eq]
  rfl

theorem wtA_tauEmb {D : D7} {Q : Par D} (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  rw [wtA_apply, Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tauEmb_ne_conj hp t t), add_zero]
  · intro s _ hs
    rw [if_neg fun h => hs (tauEmb_injective D h).symm, if_neg (tauEmb_ne_conj hp t s), add_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem wtA_conj {D : D7} {Q : Par D} (hp : Q.PinHost) {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  classical
  rw [wtA_apply, Finset.sum_eq_single t]
  · rw [if_pos rfl, if_neg (tauEmb_ne_conj hp t t).symm, zero_add]
  · intro s _ hs
    rw [if_neg (tauEmb_ne_conj hp s t).symm, if_neg fun h =>
      hs (tauEmb_injective D ((ComplexEmbedding.involutive_conjugate _).injective h)).symm, add_zero]
  · intro h; exact absurd (Finset.mem_univ t) h

theorem DF_wtA {D : D7} {Q : Par D} (hQ : Q.Pins) {j : ℕ} (hj : InR D j) (w : WeightFamilies.Wt D j) :
    Formalism.L2.Pj.DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w := by
  classical
  unfold Formalism.L2.Pj.DF WeightAlgebra.DF WeightAlgebra.degP
  obtain ⟨hp, hq, -⟩ := hQ.2.2.2 j hj
  have hsw : ∀ τ : D.host.E →+* ℂ, ∑ i : Fin ((Q.Dw j).mult τ), wtA w (τ, (i : ℕ)) =
      ∑ t : D.what₂.Tau, ((if τ = DV.tauEmb D t then ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aP t) (i : ℕ) else 0) +
        if τ = ComplexEmbedding.conjugate (DV.tauEmb D t) then
          ∑ i : Fin ((Q.Dw j).mult τ), ext0 (w.aM t) (i : ℕ) else 0) := by
    intro τ
    simp only [wtA_apply]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_add_distrib]
    split_ifs <;> simp
  have hs : ∀ {p m : ℕ} (f : Fin p → ℕ), m = p → ∑ i : Fin m, ext0 f i = ∑ i, f i := by
    rintro p m f rfl
    exact Finset.sum_congr rfl fun i _ => by simp [ext0, i.isLt]
  rw [Finset.sum_congr rfl fun τ _ => hsw τ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  simp only [Finset.mem_univ, if_true]
  have ht := hQ.1.2.2.2 t
  have hc : ¬ ComplexEmbedding.conjugate (DV.tauEmb D t) (Q.H.rt : D.host.E) = Q.H.rt0 := not_inPsi_conj hQ.1 t
  rw [hs _ (by rw [Datum.mult, if_pos ht, hp]), hs _ (by rw [Datum.mult, if_neg hc, hq])]

theorem weight_exponents : ∀ (D : D7) (Q : Par D), Q.Pins → ∀ j, InR D j → ∀ w : WeightFamilies.Wt D j, DF (Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ Function.Injective (DV.tauEmb D) ∧ (∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t) ∧ (∀ τ, ¬ InPsi Q.H τ ↔ ∃ t, τ = ComplexEmbedding.conjugate (DV.tauEmb D t)) ∧ ∀ t i, wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i ∧ wtA w (ComplexEmbedding.conjugate (DV.tauEmb D t), i) = ext0 (w.aM t) i := by
  intro D Q hQ j hj w
  have hΨ : ∀ τ, InPsi Q.H τ ↔ ∃ t, τ = DV.tauEmb D t := fun τ =>
    ⟨ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.exists_tau_of_inPsi Q hQ.1 τ, by rintro ⟨t, rfl⟩; exact hQ.1.2.2.2 t⟩
  refine ⟨DF_wtA hQ hj w, tauEmb_injective D, hΨ, fun τ => ⟨fun h => ?_, ?_⟩,
    fun t i => ⟨wtA_tauEmb hQ.1 w t i, wtA_conj hQ.1 w t i⟩⟩
  · obtain ⟨t, ht⟩ := (hΨ _).1 ((ReciprocityTheory.ChartRestriction.G.PullbackSections.CVA.inPsi_or Q.H τ).resolve_left h)
    exact ⟨t, by rw [← ht, ComplexEmbedding.involutive_conjugate _ τ]⟩
  · rintro ⟨t, rfl⟩
    exact not_inPsi_conj hQ.1 t

end GlobalTheory.WeightExponents
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeilOperatorThetaTranslateShiftPrimeToQ
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

namespace GlobalTheory.MomOne.TranslateLaw

variable {q : ℕ} [Fact q.Prime]

theorem inOK_natMul {d : ℕ} (s : ℕ) {v : ℂ} (h : InOK d v) : InOK d ((s : ℂ) * v) := by
  obtain ⟨a, b, rfl⟩ := h
  exact ⟨s * a, s * b, by push_cast; ring⟩

theorem cmLatticeCommutatorPairing_natMul_right (d s : ℕ) (x y : ℂ) : kap1 d x ((s : ℂ) * y) = kap1 d x y ^ s := by
  unfold kap1
  rw [← Complex.exp_nat_mul]
  congr 1
  have : h1 d x ((s : ℂ) * y) = ((s : ℝ) : ℂ) * h1 d x y := by
    simp only [h1, map_mul, map_natCast, Complex.ofReal_natCast]; ring
  rw [this, Complex.im_ofReal_mul]
  push_cast
  ring

theorem norm_natCast_eq_one {s : ℕ} (h : Nat.Coprime s q) : ‖(s : ℤ_[q])‖ = 1 := by
  rw [PadicInt.norm_natCast_eq_one_iff]
  exact h.symm

theorem zc_natCast (s : ℕ) : zc (s : ℤ_[q]) = (s : ℂ_[q]) := by
  simp [zc]

theorem hasSubst_mulS (a : ℤ_[q]) : HasSubst (mulS a : ℂ_[q]⟦X⟧) :=
  HasSubst.of_constantCoeff_zero' ((MulSeries.mulS_laws q).1 a).2.1

theorem subst_mulS_cancel {a : ℤ_[q]} (ha : ‖a‖ = 1) {f g : ℂ_[q]⟦X⟧}
    (h : f.subst (mulS a : ℂ_[q]⟦X⟧) = g.subst (mulS a : ℂ_[q]⟦X⟧)) : f = g := by
  obtain ⟨u, rfl⟩ := PadicInt.isUnit_iff.mpr ha
  have key : ∀ f : ℂ_[q]⟦X⟧, PowerSeries.subst (mulS ((u⁻¹ : ℤ_[q]ˣ) : ℤ_[q]) : ℂ_[q]⟦X⟧)
      (show ℂ_[q]⟦X⟧ from f.subst (mulS (u : ℤ_[q]) : ℂ_[q]⟦X⟧)) = f := by
    intro f
    dsimp only
    rw [subst_comp_subst_apply (hasSubst_mulS _) (hasSubst_mulS _), (MulSeries.mulS_laws q).2.1,
      Units.mul_inv, (MulSeries.mulS_laws q).2.2.1]
    rw [← map_algebraMap_eq_subst_X]
    simp
  have h1 := key f
  have h2 := key g
  dsimp only at h1 h2
  rw [← h1, h, h2]

theorem main : ∀ (d q : ℕ) [Fact q.Prime] (M : Mdl q) (ω : ℂ_[q]) (θ : ℂ → ℂ), d.Prime → d % 16 = 7 → Split d q → IsOK d M.L → M.MChart ω → IsTh d θ → (∀ (n : ℕ) (y : ℂ), Good M.ι d n 1 y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ M.At ω (M.ι (kap1 d 1 y)) y) → ∀ (t y : ℂ) (n s : ℕ), Nat.Coprime s q → InOK d ((s : ℂ) * t) → Good M.ι d n s y → M.ι (kap1 d 1 y) ^ (q ^ n) = 1 ∧ hat M.ι (C ω * logS) (W1 d y (U1 d t θ)) = shiftS (M.ι (kap1 d 1 y)) (hat M.ι (C ω * logS) (U1 d t θ)) := by
  intro d q hq M ω θ hd hd16 hsp hOK hM hθ hgood t y n s hs ht hy
  obtain ⟨v, hv, hvn, hyv⟩ := hy
  have hs0 : 0 < s := by
    rcases Nat.eq_zero_or_pos s with h | h
    · subst h
      exact absurd ((Nat.coprime_zero_left q).mp hs) hq.out.one_lt.ne'
    · exact h
  have hsC : (s : ℂ) ≠ 0 := by exact_mod_cast hs0.ne'
  have hsn : ‖(s : ℤ_[q])‖ = 1 := norm_natCast_eq_one hs
  have hιs : M.ι (s : ℂ) = zc (s : ℤ_[q]) := by rw [zc_natCast, map_natCast]
  set y' : ℂ := v / (q : ℂ) ^ n with hy'
  have hyy : y = (s : ℂ) * y' := by rw [hyv, hy']; ring
  have hg' : Good M.ι d n 1 y' := ⟨v, hv, hvn, by rw [hy']; simp⟩
  have hg : Good M.ι d n 1 y := by
    refine ⟨(s : ℂ) * v, inOK_natMul s hv, ?_, by rw [hyv]; simp⟩
    rw [map_mul, map_mul, map_natCast, hιs, norm_mul, (MulSeries.mulS_laws q).2.2.2.2.2, hsn, one_mul]
    exact hvn
  obtain ⟨hζ, hAt⟩ := hgood n y hg
  obtain ⟨hζ', hAt'⟩ := hgood n y' hg'
  refine ⟨hζ, ?_⟩
  have hζζ : M.ι (kap1 d 1 y) = M.ι (kap1 d 1 y') ^ s := by rw [hyy, cmLatticeCommutatorPairing_natMul_right, map_pow]
  have hℓ : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hM.2.1
  obtain ⟨hring, -⟩ := TaylorRead.hat_laws q M.ι (C ω * logS) hℓ
  obtain ⟨-, -, hdiff, -⟩ := _root_.GlobalTheory.MomOne.heisenbergOne d hd.pos
  have hθd : Differentiable ℂ θ := hθ.1
  have hθ0 : θ 0 ≠ 0 := by rw [hθ.2.1]; exact one_ne_zero
  have hUd : Differentiable ℂ (U1 d t θ) := (hdiff t θ hθd).1
  have hWUd : Differentiable ℂ (W1 d y (U1 d t θ)) := (hdiff y _ hUd).2
  have hWd : Differentiable ℂ (W1 d y θ) := (hdiff y _ hθd).2
  set f : ℂ → ℂ := fun z => U1 d t θ z / θ z with hf
  have hfa : AnalyticAt ℂ f 0 := (hUd.analyticAt 0).div (hθd.analyticAt 0) hθ0
  obtain ⟨hEll, hφa, -, -, hφb⟩ := GlobalTheory.T.scaledThetaTranslationQuotient_elliptic d q M ω θ hd hd16 hsp hOK hM hθ t s hs0 hs ht
  have hscale : ∀ G : ℂ → ℂ, AnalyticAt ℂ G 0 → hat M.ι (C ω * logS) (fun z => G ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) G).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) :=
    fun G hG => (hat_multiplicative_chart q M.ι ω G hG).2.2.1 _ _ hιs
  have hφf : hat M.ι (C ω * logS) (fun z => U1 d t θ ((s : ℂ) * z) / θ ((s : ℂ) * z)) =
      (hat M.ι (C ω * logS) f).subst (mulS (s : ℤ_[q]) : ℂ_[q]⟦X⟧) := hscale f hfa
  have hfb : Bdd (hat M.ι (C ω * logS) f) := by
    obtain ⟨B, hB⟩ := hφb
    rw [hφf] at hB
    exact ⟨B, ((MulSeries.mulS_laws q).2.2.2.1 _ _ B hsn).mp hB⟩
  have hθb : Bdd (hat M.ι (C ω * logS) θ) := ⟨1, _root_.GlobalTheory.MomOne.theta_series_integral d q M ω θ hd hd16 hsp hOK hM hθ⟩
  obtain ⟨ψ, hψa, hψ, hψh⟩ := _root_.GlobalTheory.MomOne.Transfer.shift_eq_hat_translate q M ω _ y' _ hM hAt' hEll hφa hφb
  rw [hφf] at hψh
  have hsc := ((_root_.GlobalTheory.MomOne.ShiftComp.main q).2 _ n s (s : ℤ_[q]) _ hζ' (by
    rw [sub_self, norm_zero]; positivity) hfb).2
  rw [hsc, ← hζζ] at hψh

  have hlin : Differentiable ℂ (fun z : ℂ => (s : ℂ) * z) := by fun_prop
  have hne : ∀ᶠ z in 𝓝[≠] (0 : ℂ), θ ((s : ℂ) * z + y) ≠ 0 := by
    have hA : AnalyticOnNhd ℂ (fun z : ℂ => θ ((s : ℂ) * z + y)) Set.univ :=
      fun z _ => (hθd.comp (hlin.add_const y)).analyticAt z
    rcases (hA 0 trivial).eventually_eq_zero_or_eventually_ne_zero with h | h
    · exfalso
      have := hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero isPreconnected_univ (Set.mem_univ 0) h
        (Set.mem_univ (-y / (s : ℂ)))
      apply hθ0
      have e : (s : ℂ) * (-y / (s : ℂ)) + y = 0 := by field_simp; ring
      simpa [e] using this
    · exact h
  have hWs : AnalyticAt ℂ (fun z => W1 d y θ ((s : ℂ) * z)) 0 := (hWd.comp hlin).analyticAt 0
  have hWUs : AnalyticAt ℂ (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) 0 := (hWUd.comp hlin).analyticAt 0
  have hprod : hat M.ι (C ω * logS) (fun z => ψ z * W1 d y θ ((s : ℂ) * z)) =
      hat M.ι (C ω * logS) (fun z => W1 d y (U1 d t θ) ((s : ℂ) * z)) := by
    refine (hring _ _ (hψa.mul hWs) hWUs).2.2.1 ?_
    filter_upwards [hψ, hne] with z h1z h2z
    have e : (s : ℂ) * (z + y') = (s : ℂ) * z + y := by rw [hyy]; ring
    change ψ z * W1 d y θ ((s : ℂ) * z) = _
    rw [h1z, e]
    simp only [W1]
    generalize U1 d t θ = G
    simp only [U1]
    field_simp
  rw [(hring _ _ hψa hWs).2.1, hψh, hscale _ (hWd.analyticAt 0), hscale _ (hWUd.analyticAt 0),
    ← subst_mul (hasSubst_mulS _)] at hprod
  rw [← subst_mulS_cancel hsn hprod, _root_.GlobalTheory.MomOne.ThShift.theta_shift d q M ω θ hd hd16 hsp hOK hM hθ hgood n y hg,
    ← ((Shift.shift_laws q _ hAt.2.1).2.1 _ _ hfb hθb).2, ← (hring _ _ hfa (hθd.analyticAt 0)).2.1]
  congr 1
  refine (hring _ _ (hfa.mul (hθd.analyticAt 0)) (hUd.analyticAt 0)).2.2.1 ?_
  have : ∀ᶠ z in 𝓝 (0 : ℂ), θ z ≠ 0 := hθd.continuous.continuousAt.eventually_ne hθ0
  filter_upwards [nhdsWithin_le_nhds this] with z hz
  change U1 d t θ z / θ z * θ z = _
  field_simp

end GlobalTheory.MomOne.TranslateLaw
end

