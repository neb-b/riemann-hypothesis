module

public import Formalism.LocalToGlobal.Columns.ChainInst
public import Formalism.LocalToGlobal.Columns.ReducedMatrixExtensionEntry
public import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
public import Formalism.LocalToGlobal.Columns.OcbPhiFIdxFPos
public import Formalism.LocalToGlobal.Columns.FirstUnfoldingEqZeroOfNotIntegral
public import Formalism.LocalToGlobal.Columns.Bundle0033
public import Formalism.LocalToGlobal.Columns.HeckeSpCount
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant
public import Formalism.LocalToGlobal.Columns.Bundle0031

@[expose] public section

-- bundled from Formalism.LocalToGlobal.Columns.ChainLawLev
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Bridge

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {G : ChGlob X R.m} {m2 : ℕ}

theorem clL_base (hok : ChIdx.Ok Ch sel mu cst L G m2) (hX : X.Ok) (hPr : Pr.Ok) (hCh : Ch.Ok)
    (hs : cst.sharp = true) :
    OcbBase Ch sel mu cst m2 := by
  exact
    { hX := hX
      hPr := hPr
      hCh := hCh
      hm := hok.hm
      cst_ok := hok.cst_ok
      sharp := hs
      psi0 := hok.psi0
      depthG := hok.depthG }

end Bridge

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.ChainOneOkL
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section E1

variable {E K L : Type} [Field E] [NumberField E] [Field K] [CharZero K] [Field L] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}


variable (P) in
def ookRed {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    (Fin n' → 𝓞 E ⧸ P.asIdeal) →ₗ[𝓞 E ⧸ P.asIdeal] (Fin n → 𝓞 E ⧸ P.asIdeal) :=
  Matrix.toLin' (Matrix.of fun (l : Fin n) (s : Fin n') => redP P (Loc.atN (xj (Loc.eN E n' s.1)) l.1))

theorem ookRed_spec {n' n : ℕ} (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) : ocbXRed P xj (ookRed P xj) := by
  intro l s hl hs
  unfold ookRed
  rw [ocbS_atN_toLin' _ hl hs]
  rfl

theorem ookAtN_add {N : ℕ} (v w : Fin N → E) (l : ℕ) : Loc.atN (v + w) l = Loc.atN v l + Loc.atN w l := by
  unfold Loc.atN
  split_ifs
  · rfl
  · rw [add_zero]

theorem xInt_of_firstUnfolding_ne_zero {n' c' n c : ℕ} (hc' : c' = c + 1) (Ψ : Loc.SF E K (n' + c') (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (psi : E → K) (vals : Finset E) (wt : K) (xj : (Fin n' → E) →ₗ[E] (Fin n → E))
    (h : Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Ψ xj ≠ 0) : ocbXInt P xj := by
  by_contra hx
  exact h (firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi vals wt xj hx)

theorem firstUnfolding_reduction_independent (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B A' B' : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (hA' : c + 1 ≤ A') (hB' : 1 ≤ B') (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A' B') ((q : K) ^ B')⁻¹ Ψ xj =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  by_cases hx : ocbXInt P xj
  · apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA' hB' xj (ookRed P xj) hx (ookRed_spec xj),
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx]

theorem firstUnfolding_add_eq_self_of_intAt_div (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hu : ((q : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) (hp : q.Prime)
    (hcard : Nat.card (𝓞 E ⧸ P.asIdeal) = q) {n' c' n c : ℕ} (hc' : c' = c + 1) (σ : K →+* L)
    (Ψ : Loc.SF E K (n' + c') (n + c)) (Ψr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + (c + 1)) (n + c))
    (hsupp : ∀ y, Ψ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Ψ y) = Ψr ybar)
    (psi : E → K) (ψ₀ : 𝓞 E ⧸ P.asIdeal → L) (hpsi : ∀ a, IntAt P a → σ (psi (a / (q : E))) = ψ₀ (redP P a))
    {A B : ℕ} (hA : c + 1 ≤ A) (hB : 1 ≤ B) (xj z : (Fin n' → E) →ₗ[E] (Fin n → E))
    (hz : ∀ l s, l < n → s < n' → IntAt P (Loc.atN (z (Loc.eN E n' s)) l / (q : E))) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ (xj + z) =
      Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi (LocE.valsQ E q A B) ((q : K) ^ B)⁻¹ Ψ xj := by
  have hq0 : (q : E) ≠ 0 := ciQ_ne_zero hu
  have hD : ∀ l s, l < n → s < n' → Loc.atN ((xj + z) (Loc.eN E n' s)) l =
      Loc.atN (xj (Loc.eN E n' s)) l + (q : E) * (Loc.atN (z (Loc.eN E n' s)) l / (q : E)) := by
    intro l s _ _
    rw [LinearMap.add_apply, ookAtN_add, mul_div_cancel₀ _ hq0]
  have hint : ocbXInt P (xj + z) ↔ ocbXInt P xj := by
    constructor
    · intro h l s hl hs
      have h1 := h l s hl hs
      rw [hD l s hl hs] at h1
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).1 h1
    · intro h l s hl hs
      rw [hD l s hl hs]
      exact (ciIntAt_add_iff ((ciIntAt_q (q := q)).mul (hz l s hl hs))).2 (h l s hl hs)
  by_cases hx : ocbXInt P xj
  · have hred' : ocbXRed P (xj + z) (ookRed P xj) := by
      intro l s hl hs
      rw [ookRed_spec xj l s hl hs, hD l s hl hs, redP_add_natCast_mul hq (hz l s hl hs)]
    apply σ.injective
    rw [firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB (xj + z) (ookRed P xj) (hint.2 hx) hred',
      firstUnfolding_reduction_eq hq hu hp hcard hc' σ Ψ Ψr hsupp hred psi ψ₀ hpsi hA hB xj (ookRed P xj) hx (ookRed_spec xj)]
  · rw [firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ xj hx, firstUnfolding_eq_zero_of_not_integral hc' Ψ hsupp psi _ _ (xj + z) (fun h => hx (hint.1 h))]

end E1

section Cong

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ookLamGvS_congr (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K) (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ r t j a : ℕ} (M M' : ℕ → ℕ → E)
    (hkr : k₀ ≤ r) (hra : r ≤ a) (hja : r + j * t ≤ a)
    (h : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p')) :
    LocE.lamGvS ψ₀ χ k₀ r t j M' = LocE.lamGvS ψ₀ χ k₀ r t j M := by
  unfold LocE.lamGvS
  congr 1
  · congr 1
    have hb1 : ∀ i ∈ Finset.range (k₀ - 1), i < a ∧ i + 1 < a := fun i hi => by simp at hi; omega
    have hb2 : ∀ i ∈ Finset.range (r - k₀ - 1), k₀ + i < a ∧ k₀ + i + 1 < a := fun i hi => by simp at hi; omega
    rw [reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      reduction_add (ciIntAt_sum _ _ fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1)
        (ciIntAt_sum _ _ fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.1),
      redP_sum _ _ (fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).1),
      redP_sum _ _ (fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).1)]
    exact congrArg₂ (· + ·) (Finset.sum_congr rfl fun i hi => (h i (i + 1) (hb1 i hi).1 (hb1 i hi).2).2.2)
      (Finset.sum_congr rfl fun i hi => (h (k₀ + i) (k₀ + i + 1) (hb2 i hi).1 (hb2 i hi).2).2.2)
  · refine Finset.prod_congr rfl fun i hi => ?_
    have hi' : i < j := by simpa using hi
    have hb : ∀ s : Fin t, r + i * t + s.1 < a := fun s => by
      have h1 := s.2
      have h2 : (i + 1) * t ≤ j * t := Nat.mul_le_mul_right _ hi'
      nlinarith
    apply ciUnitV_congr
    rw [redP_det (Matrix.of fun s s' : Fin t => M' (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).2.1),
      redP_det (Matrix.of fun s s' : Fin t => M (r + i * t + s.1) (r + i * t + s'.1)) (fun s s' => (h _ _ (hb s) (hb s')).1)]
    congr 1
    ext s s'
    exact (h _ _ (hb s) (hb s')).2.2


open Classical in
theorem ookPhiGS_congr (hq : ((q : ℕ) : 𝓞 E) ∈ P.asIdeal) (hq0 : (q : E) ≠ 0) (ψ₀ : AddChar (𝓞 E ⧸ P.asIdeal) K)
    (χ : ℕ → (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {k₀ rS r t j c' n' c n : ℕ} (x x' : HomE E (n' + c') (n + c))
    (hkr : k₀ ≤ r) (han : r + (j - 1) * t ≤ n + c)
    (hD : ∀ p p', p < n + c → p' < r + (j - 1) * t → ∃ d, IntAt P d ∧
      LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' p p' =
        LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x p p' + q * d) :
    LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x' = LocE.PhiGS (P := P) q ψ₀ χ k₀ rS r t j c' n' c n x := by
  rw [phiGS_eq, phiGS_eq]
  set M := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x with hM
  set M' := LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) x' with hM'
  set a := r + (j - 1) * t with ha
  have hra : r ≤ a := Nat.le_add_right _ _
  have k1 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p') ↔ IntAt P (M p p')) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact ciIntAt_add_iff ((ciIntAt_q (q := q)).mul hd)
  have k2 : ∀ p p', p < n + c → p' < a → (IntAt P (M' p p' / q) ↔ IntAt P (M p p' / q)) := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he, add_div, mul_div_cancel_left₀ _ hq0]
    exact ciIntAt_add_iff hd
  have k3 : ∀ p p', p < n + c → p' < a → redP P (M' p p') = redP P (M p p') := by
    intro p p' hp hp'
    obtain ⟨d, hd, he⟩ := hD p p' hp hp'
    rw [he]
    exact redP_add_natCast_mul hq hd
  have hc : symPhiCond P q k₀ rS r t j c n M' ↔ symPhiCond P q k₀ rS r t j c n M := by
    unfold symPhiCond
    constructor
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').1 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').1 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [← k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [← k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [← k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
    · rintro ⟨h1, h2, h3, h4⟩
      refine ⟨fun p p' hp hp' => (k1 p p' hp hp').2 (h1 p p' hp hp'), fun p p' h0 hp hp' => (k2 p p' hp hp').2 (h2 p p' h0 hp hp'),
        fun p' hp' => ⟨?_, fun p hp hne hc => ?_⟩, fun p p' h0 hp' hp hpp => ?_⟩
      · rw [k3 p' p' (by omega) (by omega)]; exact (h3 p' hp').1
      · rw [k3 p p' (by omega) (by omega)]; exact (h3 p' hp').2 p hp hne hc
      · rw [k3 p p' (by omega) hp']; exact h4 p p' h0 hp' hp hpp
  by_cases hC : symPhiCond P q k₀ rS r t j c n M
  · rw [if_pos (hc.2 hC), if_pos hC]
    have htrip : ∀ p p', p < a → p' < a → IntAt P (M p p') ∧ IntAt P (M' p p') ∧ redP P (M' p p') = redP P (M p p') :=
      fun p p' hp hp' => ⟨hC.1 p p' (by omega) hp', (hc.2 hC).1 p p' (by omega) hp', k3 p p' (by omega) hp'⟩
    congr 1
    · exact ookLamGvS_congr ψ₀ χ M M' hkr hra (le_refl _) htrip
    · congr 1
      apply ciUnitV_congr
      rw [redP_det (Matrix.of fun s s' : Fin a => M' s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).2.1),
        redP_det (Matrix.of fun s s' : Fin a => M s.1 s'.1) (fun s s' => (htrip s.1 s'.1 s.2 s'.2).1)]
      congr 1
      ext s s'
      exact (htrip s.1 s'.1 s.2 s'.2).2.2
  · rw [if_neg (fun h => hC (hc.1 h)), if_neg hC]

theorem ookEntB_joinX (q : ℕ) {k₀ n' c' n c : ℕ} (hc' : c' = 1) (hc : c = 0) (hk : k₀ ≤ n') (x₀ : HomE E n' n) (y' : Sp E n)
    {p s : ℕ} (hp : p < n) (hs : s < n') :
    LocE.entB q k₀ c' n' c n (fun i => i + 1) (fun i => i + 1) (joinCol (c' := c') (c := c) x₀ y') p (LocE.fPos k₀ c' n' s) =
      x₀ (Pi.single ⟨s, hs⟩ 1) ⟨p, hp⟩ := by
  subst hc' hc
  have f1 : LocE.fIdx k₀ 1 n' (LocE.fPos k₀ 1 n' s) = s := ocbPhi_fIdx_fPos hk (by omega)
  have f2 : LocE.fIdx k₀ 0 n p = p := ciFIdx (Or.inl rfl) (by omega)
  unfold LocE.entB joinCol atNL
  rw [f1, f2, ciScE_lt _ hp, ciScE_lt _ hs, dite_eq_left (show n' < n' + 1 by omega)]
  simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.smulRight_apply, LinearMap.proj_apply]
  rw [ciAtN_inX hp]
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  have e1 : (LinearMap.funLeft E E (Fin.castAdd 1)) (Loc.eN E (n' + 1) s) = (Pi.single ⟨s, hs⟩ 1 : Fin n' → E) := by
    funext i
    show Loc.eN E (n' + 1) s (Fin.castAdd 1 i) = _
    unfold Loc.eN
    simp only [Fin.val_castAdd, Pi.single_apply, Fin.ext_iff]
  have e2 : Loc.eN E (n' + 1) s ⟨n', by omega⟩ = 0 := by
    unfold Loc.eN
    rw [if_neg (by simp; omega)]
  rw [e1, e2, zero_mul, add_zero, sub_zero, zpow_zero, mul_one]

theorem ookFIdx_lt {k₀ c' n' p' : ℕ} (hc' : c' = 1) (hk : k₀ ≤ n') (hp' : p' < n' + c') (hne : p' ≠ k₀) :
    LocE.fIdx k₀ c' n' p' < n' ∧ LocE.fPos k₀ c' n' (LocE.fIdx k₀ c' n' p') = p' := by
  subst hc'
  exact ⟨by unfold LocE.fIdx; split_ifs <;> omega, symFPos_fIdx hk hp'⟩

theorem ookPrX_le {k₀ rS r t n c : ℕ} :
    Loc.prX (Loc.Cbe (LocE.JGsym P q k₀ rS r t n c) 1) ≤ GLint E n P := by
  rintro g ⟨ρ, hr, hg⟩ x
  have hr' : ρ ∈ LocE.JGsym P q k₀ rS r t n c := by
    have := hr.2
    simpa [MulAut.conj_apply] using this
  rw [← ciMem_lamY (P := P) (q := q) (c := c) (fun i => i + 1) (g x), ← hg]
  exact (hr'.1 _).trans (ciMem_lamY _ _)

end Cong

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.OcbTIntOfStab
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Tr

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem ocbT_bEnt_comp (hq0 : (q : E) ≠ 0) {n' c' n c : ℕ} (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c))
    {l s : ℕ} (hl : l < n + c) (hs : s < n' + c') :
    ocbBEnt n' n q (g ∘ₗ y) l s = ∑ m : Fin (n + c), ocbBEnt n n q g l m.1 * ocbBEnt n' n q y m.1 s := by
  unfold ocbBEnt
  rw [ocbS_atN_comp g y hl hs, Finset.sum_mul]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  have hz : ((q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) l)) =
      (q : E) ^ (LocE.scE n (fun i => i + 1) m.1 - LocE.scE n (fun i => i + 1) l) *
        (q : E) ^ (LocE.scE n' (fun i => i + 1) s - LocE.scE n (fun i => i + 1) m.1) := by
    rw [← zpow_add₀ hq0]
    congr 1
    ring
  rw [hz]
  ring

private theorem intAt_apply_of_mem_stdAt {N : ℕ} {x : Sp E N} (hx : x ∈ stdAt E N P) (i : Fin N) : IntAt P (x i) := by
  obtain ⟨s, hs, hsx⟩ := hx
  rw [mem_stdLat] at hsx
  obtain ⟨r, hr⟩ := hsx i
  exact ⟨r, s, hs, by rw [hr]; simp [Algebra.smul_def]⟩

private theorem mem_sclLat_iff_scaled_mem_stdAt {N : ℕ} (e : ℕ → ℤ) (x : Sp E N) :
    x ∈ LocE.sclLat P q N e ↔ (fun l : Fin N => ((q : E) ^ e l)⁻¹ * x l) ∈ stdAt E N P := by
  unfold LocE.sclLat
  rw [Submodule.mem_comap]
  rfl

theorem ocbT_int_of_stab (hq0 : (q : E) ≠ 0) {n c : ℕ} {g : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hg : g ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1))) {l m : ℕ} (hl : l < n + c) (hm : m < n + c) :
    IntAt P (ocbBEnt n n q g.toLinearMap l m) := by
  set e := LocE.scE n (fun i => i + 1) with he
  let v : Sp E (n + c) := fun i => if (i : ℕ) = m then (q : E) ^ (e m) else 0
  have hv : v ∈ LocE.lamY P q n c (fun i => i + 1) := by
    unfold LocE.lamY
    rw [mem_sclLat_iff_scaled_mem_stdAt]
    refine ⟨1, one_mem _, ?_⟩
    rw [one_smul, mem_stdLat]
    intro i
    by_cases hi : (i : ℕ) = m
    · refine ⟨1, ?_⟩
      simp only [v, hi, if_true, map_one]
      rw [← he, inv_mul_cancel₀ (zpow_ne_zero _ hq0)]
    · exact ⟨0, by simp [v, hi]⟩
  have hg' : ∀ x, g x ∈ LocE.lamY P q n c (fun i => i + 1) ↔ x ∈ LocE.lamY P q n c (fun i => i + 1) := hg
  have hgv := (hg' v).2 hv
  unfold LocE.lamY at hgv
  rw [mem_sclLat_iff_scaled_mem_stdAt] at hgv
  have hint := intAt_apply_of_mem_stdAt hgv ⟨l, hl⟩
  have hv' : v = ((q : E) ^ (e m)) • Loc.eN E (n + c) m := by
    funext i
    by_cases hi : (i : ℕ) = m <;> simp [v, Loc.eN, hi]
  convert hint using 1
  unfold ocbBEnt
  rw [ocbS_atN_of_lt _ hl]
  simp only [LinearEquiv.coe_coe, hv', map_smul, Pi.smul_apply, smul_eq_mul]
  rw [← he, zpow_sub₀ hq0]
  ring

theorem ocbT_bEnt_id {n c l s : ℕ} (hl : l < n + c) :
    ocbBEnt n n q (LinearMap.id : Sp E (n + c) →ₗ[E] Sp E (n + c)) l s = if l = s then 1 else 0 := by
  unfold ocbBEnt
  rw [LinearMap.id_apply, ocbS_atN_of_lt _ hl]
  by_cases h : l = s
  · subst h
    simp [Loc.eN]
  · simp [Loc.eN, h]

theorem ocbT_red_symm (hq0 : (q : E) ≠ 0) {n c : ℕ} {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)}
    (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) {l s : ℕ} (hl : l < n + c) (hs : s < n + c) :
    Loc.atN (hbar.symm (Loc.eN _ (n + c) s)) l = redP P (ocbBEnt n n q h₀.symm.toLinearMap l s) := by
  classical
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hI1 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hh₀ hi hm
  have hI2 : ∀ i m : ℕ, i < n + c → m < n + c → IntAt P (ocbBEnt n n q h₀.symm.toLinearMap i m) :=
    fun i m hi hm => ocbT_int_of_stab hq0 hsymm hi hm
  have hDA : LinearMap.toMatrix' hbar.symm.toLinearMap * LinearMap.toMatrix' hbar.toLinearMap = 1 := by
    rw [← LinearMap.toMatrix'_comp, LinearEquiv.symm_comp, LinearMap.toMatrix'_id]
  have hAC : LinearMap.toMatrix' hbar.toLinearMap *
      (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) = 1 := by
    ext i j
    rw [Matrix.mul_apply]
    have hcomp := ocbT_bEnt_comp (n' := n) (c' := c) hq0 h₀.toLinearMap h₀.symm.toLinearMap i.2 j.2
    rw [LinearEquiv.comp_symm, ocbT_bEnt_id i.2] at hcomp
    have hsum : ∑ m : Fin (n + c), LinearMap.toMatrix' hbar.toLinearMap i m *
        (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) m j =
        redP P (∑ m : Fin (n + c),
          ocbBEnt n n q h₀.toLinearMap i m * ocbBEnt n n q h₀.symm.toLinearMap m j) := by
      rw [redP_sum _ _ (fun m _ => IntAt.mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2))]
      refine Finset.sum_congr rfl (fun m _ => ?_)
      rw [reduction_mul (hI1 _ _ i.2 m.2) (hI2 _ _ m.2 j.2), Matrix.of_apply, ocbS_atN_toMatrix']
      congr 1
      exact (hred₀ _ _ i.2 m.2).2
    rw [hsum, ← hcomp, Matrix.one_apply]
    by_cases hij : i = j
    · subst hij
      simp [redP_one]
    · have hij' : (i : ℕ) ≠ j := fun h => hij (Fin.ext h)
      simp [hij, hij', redP_zero]
  have hCD : (Matrix.of fun i j : Fin (n + c) => redP P (ocbBEnt n n q h₀.symm.toLinearMap i j)) =
      LinearMap.toMatrix' hbar.symm.toLinearMap := by
    rw [← Matrix.one_mul (Matrix.of _), ← hDA, Matrix.mul_assoc, hAC, Matrix.mul_one]
  have h1 := congrFun (congrFun hCD ⟨l, hl⟩) ⟨s, hs⟩
  rw [Matrix.of_apply, ocbS_atN_toMatrix'] at h1
  exact h1.symm

theorem ocbT_trans (hq0 : (q : E) ≠ 0) {K L : Type} [Field K] [Field L] (σ : K →+* L) {n' c' c'' n c : ℕ} (hcc : c' = c'')
    {h₀ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hh₀ : h₀ ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)))
    {hbar : (Fin (n + c) → 𝓞 E ⧸ P.asIdeal) ≃ₗ[𝓞 E ⧸ P.asIdeal] (Fin (n + c) → 𝓞 E ⧸ P.asIdeal)}
    (hred₀ : ocbIsRed P q n c h₀ hbar) (Φ : Loc.SF E K (n' + c') (n + c)) (Φr : Loc.SF (𝓞 E ⧸ P.asIdeal) L (n' + c'') (n + c))
    (hsupp : ∀ y, Φ y ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s))
    (hred : ∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) → σ (Φ y) = Φr ybar) :
    (∀ y, Φ (h₀.symm.toLinearMap ∘ₗ y) ≠ 0 → ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) ∧
    (∀ y ybar, (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      (∀ l s, l < n + c → s < n' + c' → Loc.atN (ybar (Loc.eN _ _ s)) l = redP P (ocbBEnt n' n q y l s)) →
        σ (Φ (h₀.symm.toLinearMap ∘ₗ y)) = Φr (hbar.symm.toLinearMap ∘ₗ ybar)) := by
  have hsymm : h₀.symm ∈ stabL E (n + c) (LocE.lamY P q n c (fun i => i + 1)) :=
    (stabL E (n + c) _).inv_mem hh₀
  have hcomp_int : ∀ (g : Sp E (n + c) →ₗ[E] Sp E (n + c)) (y : HomE E (n' + c') (n + c)),
      (∀ l m, l < n + c → m < n + c → IntAt P (ocbBEnt n n q g l m)) →
      (∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q y l s)) →
      ∀ l s, l < n + c → s < n' + c' → IntAt P (ocbBEnt n' n q (g ∘ₗ y) l s) := by
    intro g y hg hy l s hl hs
    rw [ocbT_bEnt_comp hq0 g y hl hs]
    exact ciIntAt_sum _ _ (fun m _ => IntAt.mul (hg _ _ hl m.2) (hy _ _ m.2 hs))
  refine ⟨fun y hy => ?_, fun y ybar hy hyb => ?_⟩
  · have h1 := hsupp _ hy
    have h2 := hcomp_int h₀.toLinearMap _ (fun l m hl hm => ocbT_int_of_stab hq0 hh₀ hl hm) h1
    have he : h₀.toLinearMap ∘ₗ (h₀.symm.toLinearMap ∘ₗ y) = y := by
      rw [← LinearMap.comp_assoc, LinearEquiv.comp_symm, LinearMap.id_comp]
    rwa [he] at h2
  · have hI := hcomp_int h₀.symm.toLinearMap y (fun l m hl hm => ocbT_int_of_stab hq0 hsymm hl hm) hy
    apply hred _ _ hI
    intro l s hl hs
    have hs' : s < n' + c'' := by omega
    rw [ocbS_atN_comp _ _ hl hs', ocbT_bEnt_comp hq0 _ _ hl hs,
      redP_sum _ _ (fun m _ => IntAt.mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs))]
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [reduction_mul (ocbT_int_of_stab hq0 hsymm hl m.2) (hy _ _ m.2 hs), hyb _ _ m.2 hs]
    congr 1
    exact ocbT_red_symm hq0 hh₀ hred₀ hl m.2

end Tr

end Formalism.L2.Col
end
end

-- bundled from Formalism.LocalToGlobal.Columns.StabilizerMapMaximalIndex
section
open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

def frameOfY {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs)) : Sp X.E n ≃ₗ[X.E] Sp X.E n :=
  Classical.choose (exists_frameD P (hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni))

theorem frameOfY_spec {n : ℕ} (P : HeightOneSpectrum (𝓞 X.E)) (d : DecoSet (E := X.E) (n := n) (ST := Pr.vT u) (SG := Pr.vGs)) :
    ∀ x, frameOfY u P d x ∈ localization₂ P.asIdeal d.1.N ↔ x ∈ stdAt X.E n P :=
  Classical.choose_spec (exists_frameD P (hcnt_isFullLattice_of_unimodular d.2.lat d.2.uni))

variable (hm : R.m = m2 + 2)

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm}

end Top

end Formalism.L2.Col
end
end

