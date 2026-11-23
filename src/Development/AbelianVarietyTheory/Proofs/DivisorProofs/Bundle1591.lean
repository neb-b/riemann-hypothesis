module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1491
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilOperatorRationalTranslateMemThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1523
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1568
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1547
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1550
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1564
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1531
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1490
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilFixesCosetVectorCongruentOneModIdeal
section
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.FixKey

theorem hatId_mul {D : D7} {I : Ideal (𝓞 D.host.E)} {s y : AE D} (hs : s ∈ OhE D) (hy : y ∈ hatId D I) :
    s * y ∈ hatId D I := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, t, ht, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨b, hb, s * t, mul_mem hs ht, by ring⟩
  | zero => simp
  | add x y _ _ hx hy => rw [mul_add]; exact add_mem hx hy
  | neg x _ hx => rw [mul_neg]; exact neg_mem hx

theorem zeroAt_zero (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem suppSplit_one (D : D7) (N : ℕ) : SuppSplit D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q

theorem suppInert_one (D : D7) (N : ℕ) : SuppInert D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero D q

theorem wd_smul (D : D7) (T : Tor D) {N N' : ℕ} (x : VC D N N') (c : ℂ) (F : VC D N N' → ℂ) :
    Wd D T x (c • F) = c • Wd D T x F := by
  funext z; simp only [Wd, U, Pi.smul_apply, smul_eq_mul]; ring

theorem TT_smul {D : D7} {T : Tor D} {N N' : ℕ} (c : ℂ) {F : VC D N N' → ℂ} (hF : F ∈ TT D T N N') :
    c • F ∈ TT D T N N' := by
  obtain ⟨hd, m, hm, h⟩ := hF
  exact ⟨hd.const_smul c, m, hm, fun x hx => by rw [wd_smul, h x hx]⟩

theorem weylTranslate_add_of_mem_baseLattice {D : D7} {δ : ℂ} (hc : Crv D ⊤ δ) {a d : ℕ} {e0 : VC D a d → ℂ}
    (he : e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d)) (hne : e0 ≠ 0) {x y : VC D a d}
    (hx : x ∈ La0 D (tor0 D ⊤ δ) a d) (hy : y ∈ La0 D (tor0 D ⊤ δ) a d) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (Wd D (tor0 D ⊤ δ) y F) = Wd D (tor0 D ⊤ δ) (x + y) F := by
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) :=
    VacMove.klat _ (VacMove.moves_one D a) (VacMove.moves_one D d)
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) x y
  have h2 := hφ e0
  rw [VacMove.wd_fix h1 hc k0 he hy, VacMove.wd_fix h1 hc k0 he hx,
    VacMove.wd_fix h1 hc k0 he (add_mem hx hy)] at h2
  have h3 : φ = 1 := by
    by_contra hne'
    apply hne
    have : (φ - 1) • e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne')
  rw [hφ, h3, one_smul]

theorem unitBlock_int (D : D7) (o a d : ℕ) : ∀ i j, ∃ b : 𝓞 D.host.E, unitBlock D o a d i j = (b : D.host.E) := by
  intro i j
  by_cases h : i.1 = o + j.1
  · exact ⟨1, by simp [unitBlock, h]⟩
  · exact ⟨0, by simp [unitBlock, h]⟩

theorem om_cosetV_of_congOne : ∀ (D : D7) (δ t0 : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), oddE0 D ⊤ δ t0 a d e0 → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → IsCoprime 𝔪 (D.host.conj • 𝔪) → (∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (𝔪 * D.host.conj • 𝔪) → W.chV'.f u = 1) → ∀ o : ℕ, o + a ≤ d → ∀ k ∈ intG D a, CongOne D 𝔪 k → W.Om k 1 (cosetV D δ 𝔪 o a d e0) = cosetV D δ 𝔪 o a d e0 := by
  intro D δ t0 hc a d e0 hv W 𝔪 h𝔪 hcop hch o ho k hk hck
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have he := hv.1
  have hT := VacMove.vac_TT h1 hc he

  have hk0 : W.Om k 1 e0 = e0 := by
    obtain ⟨ks, ki, x, hkk, hks, hki, hss, hsi, hxq, hxd, hxu, η, hη, hx1⟩ := _root_.GlobalTheory.UnitaryFactor.exists_split_inert_factor D k hk
    have hi : W.Om ki 1 e0 = e0 :=
      W.inert ki 1 ((mem_intG ki).1 hki) ((mem_intG 1).1 (one_mem _)) hsi (suppInert_one D d)
    have hs : W.Om ks 1 e0 = e0 := by
      have hm : Moves D (ks : GL (Fin a) (AE D)) (stdL D a) := by
        simpa using VacMove.moves_mul_int hks (VacMove.moves_one D a)
      have hx : W.chV'.f x = 1 := hch x hxu (by rw [hx1]; exact hatId_mul hη (_root_.GlobalTheory.FunObj.StdDatum.DetCong.det_sub_one_mem D 𝔪 hcop k hk hck))
      rw [W.split ks 1 x 1 (stdL D a) (stdL D d) hss (suppSplit_one D d)
        (fun q hq hi => ⟨hxq q hq hi, by simpa using zeroAt_zero D q⟩) hxd (by simp) hm (VacMove.moves_one D d)]
      simp only [hx, map_one, one_zpow, mul_one, Units.val_one, one_mul]
      exact VacMove.iop_self D _ (La0 D (tor0 D ⊤ δ) a d) he
    have := W.mul ks ki 1 1 e0 hT
    rw [mul_one, ← hkk] at this
    rw [this, hi, hs]

  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔪 h𝔪 hcop d
  have hsd : SD D (skewLat D 𝔪 d) := VacMove.sd_of_moves hg'm
  have hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) •
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔪 d) (suppSplit_one D a) hg's
      (fun q hq hi => ⟨by simpa using zeroAt_zero D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]
    rfl
  have hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 =
      ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hJT : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 ∈
      TT D (tor0 D ⊤ δ) a d := by
    rw [hJe]; exact TT_smul _ (W.maps 1 g' e0 hT)
  have hkJ : W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) =
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
    have e1 := W.mul k 1 1 g' e0 hT
    have e2 := W.mul 1 k g' 1 e0 hT
    rw [mul_one, one_mul] at e1
    rw [one_mul, mul_one, hk0] at e2
    rw [hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2]

  have hx₀ := pt_unitBlock_mem (D := D) δ o a d
  obtain ⟨m, hm, hlift⟩ := W.lift k 1 (unitBlock D o a d) _ hJT
  obtain ⟨w, hw𝔪, hclose⟩ := _root_.GlobalTheory.CongApprox.exists_closeTo_congOne D 𝔪 h𝔪 k hk hck (unitBlock D o a d) (unitBlock_int D o a d) m hm
  have hw := GlobalTheory.T.thetaPoint_mem_standard_and_skewLattice_of_entries_mem D δ 𝔪 w hw𝔪
  have hBk : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) :=
    VacMove.klat _ (VacMove.moves_one D a) hg'm
  have hJB := _root_.GlobalTheory.SkewTheta.iop_mem_thSp D δ hc e0 he 𝔪 hsd
  have hWJ := hlift _ hclose
  rw [hkJ, VacMove.pt_add, ← weylTranslate_add_of_mem_baseLattice hc he W.nz hx₀ hw.1, VacMove.wd_fix h1 hc hBk hJB hw.2] at hWJ
  unfold cosetV
  rw [W.smul _ _ _ _ (GlobalTheory.FinWeil.RatTransl.wd_mem_TT D h1 ⊤ δ hc a d _ _ hJT), hWJ]

end GlobalTheory.FunObj.FixKey
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilIntegralPointSkewLatticeUnitVectorSameEigen
section
open scoped Pointwise nonZeroDivisors
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section
namespace GlobalTheory.FunObj.EigUnit

theorem conj_smul_smul (D : D7) (I : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • I = I := by
  have h2 : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun x => VacMove.conj_conj D x
  rw [smul_smul, h2, one_smul]

theorem conj_smul_mul (D : D7) (I J : Ideal (𝓞 D.host.E)) :
    D.host.conj • (I * J) = D.host.conj • I * D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def, Ideal.map_mul]

theorem conj_smul_mono (D : D7) {I J : Ideal (𝓞 D.host.E)} (h : I ≤ J) : D.host.conj • I ≤ D.host.conj • J := by
  simp only [Ideal.pointwise_smul_def]; exact Ideal.map_mono h

theorem coprime_rep (D : D7) (𝔪 : Ideal (𝓞 D.host.E)) (h𝔪 : 𝔪 ≠ ⊥) :
    ∃ 𝔫 : Ideal (𝓞 D.host.E), 𝔫 ≠ ⊥ ∧ IsCoprime 𝔫 (D.host.conj • 𝔫) ∧
      𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪 := by
  induction 𝔪 using UniqueFactorizationMonoid.induction_on_prime with
  | h₁ => exact absurd rfl h𝔪
  | h₂ x hx =>
    rw [Ideal.isUnit_iff] at hx
    subst hx
    exact ⟨⊤, top_ne_bot, by rw [Ideal.isCoprime_iff_sup_eq]; exact top_sup_eq _, rfl⟩
  | h₃ x p hx hp ih =>
    obtain ⟨n, hn, hcop, hxn⟩ := ih hx
    have hpb : p ≠ ⊥ := hp.ne_zero
    have hpP : p.IsPrime := Ideal.isPrime_of_prime hp
    have hpM : p.IsMaximal := hpP.isMaximal hpb
    have hsb : D.host.conj • p ≠ ⊥ := GlobalTheory.BotPairSmall.conj_smul_ne_bot D hpb
    have hsM : (D.host.conj • p).IsMaximal := (Ideal.IsPrime.smul D.host.conj).isMaximal hsb
    by_cases hfix : D.host.conj • p = p
    · refine ⟨n, hn, hcop, ?_⟩
      rw [conj_smul_mul, hfix, mul_assoc, hxn]
      ring
    by_cases hdiv : n ≤ D.host.conj • p
    · obtain ⟨n', rfl⟩ := Ideal.dvd_iff_le.2 hdiv
      refine ⟨n', fun h0 => hn (by rw [h0, Ideal.mul_bot]), ?_, ?_⟩
      · rw [conj_smul_mul] at hcop
        exact (hcop.of_mul_left_right).of_mul_right_right
      · simp only [conj_smul_mul, conj_smul_smul] at hxn ⊢
        calc p * x * D.host.conj • n' = x * p * D.host.conj • n' := by ring
          _ = D.host.conj • p * n' * D.host.conj • x := by rw [mul_assoc, hxn]
          _ = n' * (D.host.conj • p * D.host.conj • x) := by ring
    · refine ⟨p * n, mul_ne_zero hpb hn, ?_, ?_⟩
      · have hnot : ¬ D.host.conj • n ≤ p := fun h => hdiv (by
          have := conj_smul_mono D h
          rwa [conj_smul_smul] at this)
        have c1 : IsCoprime p (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • p := hpM.eq_of_le hne le_sup_left
          exact hfix (hsM.eq_of_le hpM.ne_top (le_sup_right.trans h3.ge))
        have c2 : IsCoprime p (D.host.conj • n) := by
          rw [Ideal.isCoprime_iff_sup_eq]
          by_contra hne
          have h3 : p = p ⊔ D.host.conj • n := hpM.eq_of_le hne le_sup_left
          exact hnot (le_sup_right.trans h3.ge)
        have c3 : IsCoprime n (D.host.conj • p) := by
          rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
          by_contra hne
          have h3 : D.host.conj • p = D.host.conj • p ⊔ n := hsM.eq_of_le hne le_sup_left
          exact hdiv (le_sup_right.trans h3.ge)
        rw [conj_smul_mul]
        exact IsCoprime.mul_left (IsCoprime.mul_right c1 c2) (IsCoprime.mul_right c3 hcop)
      · rw [conj_smul_mul, conj_smul_mul]
        calc p * x * (D.host.conj • p * D.host.conj • n) = p * D.host.conj • p * (x * D.host.conj • n) := by ring
          _ = p * D.host.conj • p * (n * D.host.conj • x) := by rw [hxn]
          _ = p * n * (D.host.conj • p * D.host.conj • x) := by ring

theorem zeroAt_zero' (D : D7) (q : ℕ) : ZeroAt D q 0 :=
  fun _ => ⟨1, one_pos, Nat.coprime_one_left q, 0, zero_mem _, by simp⟩

theorem suppSplit_one' (D : D7) (N : ℕ) : SuppSplit D ((1 : GA D N) : GL (Fin N) (AE D)) :=
  fun q _ _ i j => by rw [OneMemClass.coe_one, Units.val_one, sub_self]; exact zeroAt_zero' D q

theorem skewLat_eq (D : D7) {𝔪 𝔫 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥) (h𝔫 : 𝔫 ≠ ⊥)
    (h : 𝔪 * D.host.conj • 𝔫 = 𝔫 * D.host.conj • 𝔪) (N : ℕ) : skewLat D 𝔪 N = skewLat D 𝔫 N := by
  have e : ((𝔪 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔪 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) =
      ((𝔫 : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E) /
      ((D.host.conj • 𝔫 : Ideal (𝓞 D.host.E)) : FractionalIdeal (𝓞 D.host.E)⁰ D.host.E)) := by
    rw [div_eq_div_iff (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔪))
      (FractionalIdeal.coeIdeal_ne_zero.2 (GlobalTheory.BotPairSmall.conj_smul_ne_bot D h𝔫)), ← FractionalIdeal.coeIdeal_mul,
      ← FractionalIdeal.coeIdeal_mul, h]
  unfold skewLat
  rw [e]

theorem eig_unit : ∀ (D : D7) (δ : ℂ), Crv D ⊤ δ → ∀ {a d : ℕ} (e0 : VC D a d → ℂ), e0 ∈ Th D (tor0 D ⊤ δ) (stdL D a) (stdL D d) → ∀ (W : WeilO D ⊤ δ a d e0) (𝔪 : Ideal (𝓞 D.host.E)), 𝔪 ≠ ⊥ → ∀ (r : GA D a), r ∈ intG D a → ∀ c : ℂ, W.Om r 1 e0 = c • e0 → W.Om r 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0) = c • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔪 d)) e0 := by
  intro D δ hc a d e0 he W 𝔪 h𝔪 r hr c hrc
  have h1 := (GlobalTheory.InducedType.induced_type D).1
  have hT := VacMove.vac_TT h1 hc he
  obtain ⟨𝔫, h𝔫, hcop, hmn⟩ := coprime_rep D 𝔪 h𝔪
  rw [skewLat_eq D h𝔪 h𝔫 hmn d]
  obtain ⟨g', x', hg's, hg'm, hx'q, hx'd⟩ := GlobalTheory.T.exists_splitSupported_unitary_moving_to_selfDualSkewLattice D 𝔫 h𝔫 hcop d
  have hJ : W.Om 1 g' e0 = ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) •
      Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 := by
    rw [W.split 1 g' 1 x' (stdL D a) (skewLat D 𝔫 d) (suppSplit_one' D a) hg's
      (fun q hq hi => ⟨by simpa using zeroAt_zero' D q, hx'q q hq hi⟩) (by simp) hx'd (VacMove.moves_one D a) hg'm]
    rfl
  have hc0 : ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ) ≠ 0 := Units.ne_zero _
  have hJe : Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) a d) (La D (tor0 D ⊤ δ) (stdL D a) (skewLat D 𝔫 d)) e0 =
      ((W.chV.f x' ^ W.ep * W.chV'.f 1 ^ W.ep' : ℂˣ) : ℂ)⁻¹ • W.Om 1 g' e0 := by
    rw [hJ, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have e1 := W.mul r 1 1 g' e0 hT
  have e2 := W.mul 1 r g' 1 e0 hT
  rw [mul_one, one_mul] at e1
  rw [one_mul, mul_one, hrc, W.smul _ _ _ _ hT] at e2
  rw [hJe, W.smul _ _ _ _ (W.maps 1 g' e0 hT), ← e1, e2, smul_comm]

end GlobalTheory.FunObj.EigUnit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LeviOp

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

theorem map_inv_mul {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A⁻¹.map g * A.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem map_mul_inv {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A.map g * A⁻¹.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]

theorem hom_mulVec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (g : F →+* S) (g' : F →+* T)
    (hg : f.comp g = g') (M : Matrix κ κ F) (x : κ → S) (i : κ) :
    f ((M.map g *ᵥ x) i) = (M.map g' *ᵥ (fun j => f (x j))) i := by
  subst hg
  set_option synthInstance.maxHeartbeats 100000 in
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

theorem spAct_levi {R : Type} [CommRing R] [Algebra F R] (A : Matrix κ κ F) (w : (κ → R) × (κ → R)) :
    GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w =
      (A.map (algebraMap F R) *ᵥ w.1, (A⁻¹.map (algebraMap F R))ᵀ *ᵥ w.2) := by
  unfold GlobalTheory.SympChange.spAct GlobalTheory.SympChange.leviM
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  ext k <;> simp [Matrix.transpose_map]

theorem schr_levi {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    (fun x => schr ψ w φ (A⁻¹.map (algebraMap F R) *ᵥ x)) =
      schr ψ (GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w) (fun x => φ (A⁻¹.map (algebraMap F R) *ᵥ x)) := by
  rw [spAct_levi]
  funext x
  simp only [GlobalTheory.WeilM.schr]
  have h1 := map_inv_mul (algebraMap F R) A hA
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

def homeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S) (A : Matrix κ κ F)
    (hA : IsUnit A.det) : (κ → S) ≃ₜ (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem homeo_apply {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (x : κ → S) : homeo g A hA x = A⁻¹.map g *ᵥ x := rfl

def linEquiv {S : Type} [CommRing S] [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) : (κ → S) ≃L[ℝ] (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := Matrix.mulVec_smul _ c x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

theorem sb_comp {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {φ : X → ℂ} (hφ : φ ∈ SB X) : φ ∘ h ∈ SB X :=
  ⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩

variable [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

theorem mulVec_mem {v : Pl (F := F)} (M : Matrix κ κ F)
    (hM : ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F) (x : κ → Fv F v)
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) (i : κ) :
    (M.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)

theorem eventually_int (M : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  exact fun i j => (algebraMap F (Af F) (M i j)).2


open scoped Classical in
theorem hasOp_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  intro F _ _ ψ _ _ _ κ _ _ A hA
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L,
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    simp
  · have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
        LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
          pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
      intro f g
      funext x
      simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      congr 1
      · congr 1
        funext i
        exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
      · congr 1
        funext i
        exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
    have hle : schA F κ ≤ (schA F κ).comap
        (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, g, hg, rfl⟩
      show _ ∈ schA F κ
      rw [key]
      exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
    exact fun Φ hΦ => hle hΦ
  · intro w Φ _
    exact schr_levi ψ A hA w Φ
  · intro v
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => sb_comp (homeo _ A hA) hφ) ?_
    intro φ hφ
    refine ⟨φ ∘ (homeo (algebraMap F (Fv F v)) A hA).symm, sb_comp _ hφ, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, Function.comp_apply]
    exact congrArg φ ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x)
  · intro v φ _ h
    funext x
    have := congrFun h ((homeo (algebraMap F (Fv F v)) A hA).symm x)
    simp only [LinearMap.funLeft_apply, Pi.zero_apply] at this
    have hx : A⁻¹.map (algebraMap F (Fv F v)) *ᵥ (homeo (algebraMap F (Fv F v)) A hA).symm x = x :=
      (homeo (algebraMap F (Fv F v)) A hA).apply_symm_apply x
    rw [hx] at this
    exact this
  · intro v w φ _
    exact schr_levi (GlobalTheory.LatVac.psiAt ψ v) A hA w φ
  · filter_upwards [eventually_int A, eventually_int A⁻¹] with v hA1 hA2
    funext x
    have hiff : (∀ i, (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
      constructor
      · intro h i
        have e : x = A.map (algebraMap F (Fv F v)) *ᵥ (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) :=
          ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x).symm
        rw [e]
        exact mulVec_mem A hA1 _ h i
      · intro h i
        exact mulVec_mem A⁻¹ hA2 x h i
    show Set.indicator _ _ _ = Set.indicator _ _ _
    by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hiff.2 hx),
        Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from mt hiff.1 hx),
        Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
  · intro f φ _ _
    funext x
    simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · refine finprod_congr fun v => congrArg (φ v) ?_
      funext i
      exact hom_mulVec (evFin F v).toRingHom (algebraMap F (AF F)) (algebraMap F (Fv F v))
        (RingHom.ext fun c => (evFin F v).commutes c) A⁻¹ x i

end GlobalTheory.LeviOp
end
end

