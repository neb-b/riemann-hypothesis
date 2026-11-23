module

public import Formalism.LocalRingCardinality.Bundle0006
public import Formalism.SharpRestriction.SmoothDesignExistence.DGamSmooth
public import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0008
public import Formalism.SharpRestriction.Divisibility.Bundle0002
public import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
public import Formalism.SharpRestriction.Divisibility.Bundle0001
public import Formalism.SharpRestriction.GlobalSchurBounds.FlipTwoThree
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
public import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
public import Formalism.LocalRingCardinality.Lemmas
public import Formalism.SharpRestriction.AdmissibleParameterJoins.SumLogPrimeFactorsLe
public import Formalism.LocalRingCardinality.DataForced
public import Formalism.LocalRingCardinality.DataParams
public import Mathlib
public import Formalism.SharpRestriction.AdmissibleParameterJoins.Bundle0002
public import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
public import Formalism.SharpRestriction.CuspSpanNormBounds.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DGamMink
section
namespace Formalism.MainNotions.J

open Formalism.BasicNotions

private lemma prime_le_succ_of_dvd_minkM' {n p : ℕ} (hp : p.Prime) (h : p ∣ minkM n) : p ≤ n + 1 := by
  have h' : p ∣ ∏ q ∈ (Finset.range (n + 2)).filter Nat.Prime, q ^ Formalism.HermitianLatticeCounting.S6.minkowskiExp n q := h
  rcases (Prime.dvd_finsetProd_iff hp.prime _).1 h' with ⟨q, hq, hdvd⟩
  rw [Finset.mem_filter, Finset.mem_range] at hq
  have hpq := (Nat.prime_dvd_prime_iff_eq hp hq.2).1 (hp.dvd_of_dvd_pow hdvd)
  omega

theorem dGamSmooth_of_dvd {eps : ℝ} (Fm : FamP eps)
    (h : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (i : Fm.Ix x) u,
      ((Fm.D x i).mem u).C.DGam ∣ minkM (2 * (Fm.D x i).R.f * (Fm.D x i).R.N (Fm.D x i).R.m)) :
    Pk.DGamSmooth Fm := by
  obtain ⟨x0, hx0⟩ := h
  exact ⟨x0, fun x hx i u p hp hpd => prime_le_succ_of_dvd_minkM' hp (dvd_trans hpd (hx0 x hx i u))⟩

end Formalism.MainNotions.J
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLb
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.FrobeniusOrbits

def NumsL (D : D7) (L : SizeData₂ D) (Cn cL : ℝ) : Prop :=
  ∀ u, flipTwoThree.Nums D (flipTwoThree.Tu D u) (D.host.g 0) (D.host.g 1) Cn L.sc.x L.sc.b (cL * L.sc.L) L.sc.b' L.Sc
    L.etaSz

def WtsL (D : D7) (L : SizeData₂ D) (Cn : ℝ) : Prop :=
  ∀ u, flipTwoThree.Wts D u Cn L.sc.x L.sc.b L.sc.b' L.Sc L.etaSz

theorem tau1_mem_Psi (φ : Formalism.HC.Frame) (t : φ.A) : φ.tau1 t ∈ φ.Psi := by
  show φ.tau1 t ∈ φ.chD.ker
  rw [MonoidHom.mem_ker]
  rfl

theorem tau1_injective_alt (φ : Formalism.HC.Frame) : Function.Injective φ.tau1 := by
  intro a b h
  simpa [Formalism.HC.Frame.tau1, Formalism.HC.Frame.iota] using h

theorem sum_tops (D : D7) (g : D.what₂.Tau → ℝ) (h : D.host.TT → ℝ)
    (hg : ∀ τ (t : D.host.TT), (D.eTau τ : D.R.GG) = D.R.tau1 t → g τ = h t) :
    ∑ τ ∈ topsOf D.host D.eTau, g τ = ∑ t : D.host.TT, h t := by
  symm
  refine Finset.sum_bij
    (fun (t : D.host.TT) _ => D.eTau.symm ⟨D.R.tau1 (t : D.R.A), tau1_mem_Psi D.R.toFrame (t : D.R.A)⟩)
    ?_ ?_ ?_ ?_
  · intro t _
    simp only [topsOf, Finset.mem_filter, Finset.mem_univ, true_and, Equiv.apply_symm_apply,
      Subtype.coe_mk, Host.topPlaces, Finset.mem_image]
    exact ⟨(t : D.R.A), t.2, rfl⟩
  · intro a _ b _ hab
    have h1 := congrArg (fun x => ((D.eTau x : D.R.Psi) : D.R.GG)) hab
    simp only [Equiv.apply_symm_apply, Subtype.coe_mk] at h1
    exact Subtype.ext (tau1_injective_alt D.R.toFrame h1)
  · intro τ hτ
    simp only [topsOf, Finset.mem_filter, Finset.mem_univ, true_and, Host.topPlaces,
      Finset.mem_image] at hτ
    obtain ⟨a, ha, hat⟩ := hτ
    refine ⟨⟨a, ha⟩, Finset.mem_univ _, ?_⟩
    apply D.eTau.injective
    apply Subtype.ext
    simp only [Equiv.apply_symm_apply, Subtype.coe_mk]
    exact hat
  · intro t _
    symm
    apply hg
    simp only [Equiv.apply_symm_apply, Subtype.coe_mk]

theorem lamCol_top (D : D7) (L : SizeData₂ D) (u : D.what₂.Word) (τ : D.what₂.Tau) (t : D.host.TT)
    (h : (D.eTau τ : D.R.GG) = D.R.tau1 t) : flipTwoThree.aT D u τ = (L.aT t : ℝ) := by
  have hk : 0 < D.R.k := by have := D.R.m_add_three_le_k; omega
  obtain ⟨h1, -⟩ := L.top_u τ t hk h
  have e1 := D.hcW_first u τ hk
  have e2 : flipTwoThree.aT D u τ = (((D.hcW u τ).u ⟨0, hk⟩ : ℚ) : ℝ) - (((D.R.k : ℝ) - 1) / 2) := by
    simp only [flipTwoThree.aT, flipTwoThree.lamCol, dif_pos hk, hcToWeightQ, rhoVec, Fin.val_mk, Nat.cast_zero,
      sub_zero] <;> push_cast <;> ring
  rw [e2, e1, h1]
  ring

theorem scale_pos (s : Scale) : 0 < s.x ∧ 0 < s.L ∧ 0 < s.b ∧ 0 < s.a ∧ 0 < s.b' := by
  have hx : 0 < s.x := by linarith [s.one_lt_alt]
  have hL : 0 < s.L := Real.rpow_pos_of_pos hx _
  have hb : 0 < s.b := Real.exp_pos _
  have ha : 0 < s.a := mul_pos hx hb
  exact ⟨hx, hL, hb, ha, div_pos ha (Real.exp_pos _)⟩

theorem orderBound_of_fifth_sixth (D : D7) (L : SizeData₂ D) (Cn C5 C6 cL : ℝ)
    (h5 : flipTwoThree.Conclusion5 D Cn C5 L.sc.x) (h6 : flipTwoThree.Conclusion6 D Cn C6 L.sc.x)
    (hcL : 1 ≤ cL) (hrd : 1 ≤ D.host.rdE)
    (hN : NumsL D L Cn cL) (hW : WtsL D L Cn) (CV : ∀ u, flipTwoThree.ColVal D u) :
    LocalQuadraticParts.FrobeniusExpansionCongruence L (max (max C5 C6) 0 * cL) := by
  intro u
  have hM5 : C5 ≤ max (max C5 C6) 0 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM6 : C6 ≤ max (max C5 C6) 0 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hM0 : 0 ≤ max (max C5 C6) 0 := le_max_right _ _
  have hcL0 : 0 ≤ cL := by linarith
  have hMc := mul_le_mul_of_nonneg_left hcL hM0
  have hC5 : C5 ≤ max (max C5 C6) 0 * cL := by linarith
  have hC6 : C6 ≤ max (max C5 C6) 0 * cL := by linarith
  have h5' := h5 u _ _ _ _ _ (hN u) (hW u) (CV u)
  have h6' := h6 u _ _ _ _ _ (hN u) (hW u) (CV u)
  have hNu := hN u
  unfold flipTwoThree.Nums at hNu
  obtain ⟨-, -, -, -, -, -, hSc, heta, hmt, -, -, -, -, -, hv1, -⟩ := hNu
  have eT : flipTwoThree.Tu D u = (D.mem u).A.T := rfl
  rw [eT] at h5' h6'
  have hS : ∑ t ∈ flipTwoThree.tops D, flipTwoThree.aT D u t / (D.R.k : ℝ) * Real.log ((D.mem u).A.T : ℝ) =
      ∑ t : D.host.TT, ((L.aT t : ℝ) / D.R.k) * Real.log ((D.mem u).A.T : ℝ) :=
    sum_tops D _ _ (fun τ t h => by rw [lamCol_top D L u τ t h])
  rw [hS] at h5'
  have hk : 1 ≤ D.R.k := by have := D.R.m_add_three_le_k; omega
  have hk1 : (1 : ℝ) ≤ D.R.k := by exact_mod_cast hk
  have hlk : 0 ≤ Real.log (D.R.k : ℝ) := Real.log_nonneg hk1
  have hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
  have hlkv : 0 ≤ Real.log ((D.R.k : ℝ) * D.host.v) :=
    Real.log_nonneg (one_le_mul_of_one_le_of_one_le hk1 hv1)
  have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
  have hn : (0 : ℝ) ≤ (D.host.TT.card : ℝ) := Nat.cast_nonneg _
  have hsc := scale_pos L.sc
  have hx0 : 0 < L.sc.x := hsc.1
  have hxb : 0 ≤ L.sc.x * L.sc.b := (mul_pos hsc.1 hsc.2.2.1).le
  have hmt0 : (0 : ℝ) ≤ (D.R.m : ℝ) * D.R.t := mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  have hb'x : 0 < L.sc.b' / L.sc.x := by linarith
  have hb' : 0 ≤ L.sc.b' := by
    by_contra hneg
    push_neg at hneg
    have := div_neg_of_neg_of_pos hneg hx0
    linarith
  have hbS : 0 ≤ L.sc.b' + L.Sc := by linarith
  have hk0 : (0 : ℝ) ≤ D.R.k := by linarith
  have hfk2L : 0 ≤ (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * L.sc.L :=
    mul_nonneg (mul_nonneg hf (sq_nonneg _)) hsc.2.1.le
  rw [show LocalQuadraticParts.nTT D = (D.host.TT.card : ℝ) from rfl, show L.sc.a = L.sc.x * L.sc.b from rfl]
  constructor
  · have p1 := mul_nonneg (sub_nonneg.mpr hC5) (mul_nonneg (mul_nonneg hn hxb) hlk)
    have p2 := mul_nonneg (sub_nonneg.mpr hC5) (mul_nonneg (mul_nonneg (mul_nonneg hf hk0) hbS) hlk)
    have p3 := mul_nonneg (sub_nonneg.mpr hC5) (mul_nonneg (mul_nonneg hf (by linarith : (0 : ℝ) ≤ L.Sc)) hlT)
    have p4 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hM5) hcL0) hfk2L
    linarith
  · have q1 := mul_nonneg (sub_nonneg.mpr hC6) (mul_nonneg (mul_nonneg hn hxb) hlkv)
    have q2 := mul_nonneg (sub_nonneg.mpr hC6)
      (mul_nonneg (mul_nonneg hf hbS) (add_nonneg (mul_nonneg hk0 hlkv) hlT))
    have q3 := mul_nonneg (mul_nonneg (sub_nonneg.mpr hM6) hcL0) hfk2L
    linarith

theorem family_orderBound_of_fifth_sixth {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)
    (Cn cL : ℝ) (h5 : flipTwoThree.ConclusionF5 Fm) (h6 : flipTwoThree.ConclusionF6 Fm) (hcL : 1 ≤ cL)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      1 ≤ (Fm.D x i).host.rdE ∧ NumsL (Fm.D x i) (Fm.L x i) Cn cL ∧ WtsL (Fm.D x i) (Fm.L x i) Cn ∧
        ∀ u, Nonempty (flipTwoThree.ColVal (Fm.D x i) u)) :
    LocalQuadraticParts.SlopesFamily Fm := by
  obtain ⟨C5, xa, hC5⟩ := h5 Cn
  obtain ⟨C6, xb, hC6⟩ := h6 Cn
  obtain ⟨x0, hx0⟩ := hE
  unfold LocalQuadraticParts.SlopesFamily
  refine ⟨max (max C5 C6) 0 * cL, max (max x0 xa) (max xb (Fm.x1 + 1)), ?_⟩
  intro x hx i
  have hxa : xa ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0' : x0 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxb : xb ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx1 : Fm.x1 < x := by
    have : Fm.x1 + 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    linarith
  obtain ⟨hrd, hN, hW, hCV⟩ := hx0 x hx0' i
  have hxx := Fm.L_x x i hx1
  have p5 : flipTwoThree.Conclusion5 (Fm.D x i) Cn C5 (Fm.L x i).sc.x := by rw [hxx]; exact hC5 x hxa hx1 i
  have p6 : flipTwoThree.Conclusion6 (Fm.D x i) Cn C6 (Fm.L x i).sc.x := by rw [hxx]; exact hC6 x hxb hx1 i
  exact orderBound_of_fifth_sixth (Fm.D x i) (Fm.L x i) Cn C5 C6 cL p5 p6 hcL hrd hN hW (fun u => (hCV u).some)

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLd
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions

def LevelPrimeBasicClauses (D : D7) : Prop :=
  ∀ u,
    ((D.mem u).A.du : ℝ) = (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) ∧
    (LocalQuadraticParts.MuH D u).mu = ((D.fm u).lat 0).mu -
      (D.R.f : ℝ) * Real.log (((D.mem u).A.T : ℝ) - 1) / (((D.mem u).A.T : ℝ) - 2) ∧
    (LocalQuadraticParts.MuH D u).muMax ≤ ((D.fm u).lat 0).muMax

theorem levelPrimeClauses_of_second (D : D7) (h : ∀ u, product_first_zeroth_parts.Conclusion2 D u) : LevelPrimeBasicClauses D := by
  intro u
  obtain ⟨h1, h2, h3, -⟩ := h u
  obtain ⟨s1, s2, -⟩ := D.ram_slopes u
  refine ⟨?_, ?_, ?_⟩
  · have h1' := congrArg (fun q : ℚ => (q : ℝ)) h1
    push_cast at h1'
    rw [h1']
    ring
  · rw [show (LocalQuadraticParts.MuH D u).mu = (D.fm u).ramLat.mu from s1]
    exact h2
  · rw [show (LocalQuadraticParts.MuH D u).muMax = (D.fm u).ramLat.muMax from s2]
    exact h3

theorem sum_lwP_e_le (D : D7) (p : ℕ) (hp : p.Prime) (S : Finset D.what₂.places.Pl)
    (hS : ∀ w ∈ S, D.what₂.places.resChar w = p) :
    ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) ≤ Real.log p := by
  classical
  obtain ⟨T, hT⟩ := finite_places_over (K := D.what₂.LL) p hp
  have h1 : ∑ w ∈ S, SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ) =
      ∑ v ∈ S.map D.plEq.toEmbedding, lw D.what₂.LL v * (eWL D.what₂.LL v : ℝ) := by
    rw [Finset.sum_map]
    refine Finset.sum_congr rfl (fun w _ => ?_)
    rw [D.ram_eq w]; rfl
  have hsub : S.map D.plEq.toEmbedding ⊆ T := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_map.1 hv
    rw [hT]
    have := resChar_mem D w
    rw [hS w hw] at this
    exact this
  rw [h1, ← sum_lw_e p hp T hT]
  exact Finset.sum_le_sum_of_subset_of_nonneg hsub
    (fun v _ _ => mul_nonneg (lw_nonneg v) (Nat.cast_nonneg _))

def LenAtT (D : D7) (L : SizeData₂ D) : Prop :=
  ∀ u w, D.what₂.places.resChar w = (D.mem u).A.T →
    DV.lenLoc (D.plEq w) (L.NuLat u) (DV.MramL D u) =
      product_first_zeroth_parts.len D u w (product_first_zeroth_parts.Sram D u w) (product_first_zeroth_parts.Nlam D u w)

def LocSpan (D : D7) : Prop :=
  ∀ u w, ∀ y ∈ (D.fm u).S 0 w, InLoc (D.plEq w) ((D.fm u).lat 0).L y

def LevelPrimeSizeBounds (D : D7) (L : SizeData₂ D) (C1 : ℝ) : Prop :=
  ∀ u w, product_first_zeroth_parts.OverT D u w → ∑ v ∈ product_first_zeroth_parts.VV D u w,
      ((product_first_zeroth_parts.amax D u : ℝ) / D.R.k + 2 * product_first_zeroth_parts.Wt D u ((D.fm u).tauOf w v) + D.R.k +
        (D.fm u).bTop ((D.fm u).tauOf w v)) ≤
    C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b')

theorem levelPrime_summary_of_fifth (D : D7) (L : SizeData₂ D) (C C1 : ℝ) (h2 : ∀ u, product_first_zeroth_parts.Conclusion2 D u)
    (h5 : ∀ u, product_first_zeroth_parts.Conclusion5 D u C) (hNu : DV.NuDef D L) (hAtT : NuAtTDef D L) (hLoc : LocSpan D)
    (hLen : LenAtT D L) (hS : LevelPrimeSizeBounds D L C1)
    (hSet : ∀ u, product_first_zeroth_parts.HidaSetting D u) (hC1 : 0 ≤ C1) : LocalQuadraticParts.adm26 L (4 * C1) := by
  classical
  intro u
  obtain ⟨c1, c2, c3⟩ := levelPrimeClauses_of_second D h2 u
  refine ⟨c1, c2, c3, ?_, ?_⟩
  · intro w hw x hx
    have h1 : InLoc (D.plEq w) (L.NuLat u) x :=
      ⟨1, fun h => (D.plEq w).isPrime.ne_top ((Ideal.eq_top_iff_one _).mpr h), by rwa [one_smul]⟩
    have h2 : D.nuIn u x ∈ product_first_zeroth_parts.Nlam D u w := (hAtT u w hw x).mp h1
    have h3 : D.nuIn u x ∈ (D.fm u).S 0 w := ((h5 u w hw).1 h2).1
    obtain ⟨s, hs, hsx⟩ := hLoc u w _ h3
    refine ⟨s, hs, ?_⟩
    rw [pow_zero, Ideal.one_eq_top, Submodule.top_smul]
    show (D.nuIn u).restrictScalars (NumberField.RingOfIntegers D.what₂.LL) (s • x) ∈ ((D.fm u).lat 0).L
    rw [map_smul]
    exact hsx
  · intro F hFT
    have hx0 : 0 < L.sc.x := lt_trans zero_lt_one L.sc.one_lt_alt
    have ha : 0 < L.sc.a := mul_pos hx0 (Real.exp_pos _)
    have hb' : 0 < L.sc.b' := div_pos ha (Real.exp_pos _)
    have hk : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    have hm : (0 : ℝ) ≤ D.R.m := Nat.cast_nonneg _
    have hd : (0 : ℝ) ≤ D.duS u := Nat.cast_nonneg _
    have hTT : (0 : ℝ) ≤ LocalQuadraticParts.nTT D := Nat.cast_nonneg _
    have hlT : 0 ≤ Real.log ((D.mem u).A.T : ℝ) := Real.log_natCast_nonneg _
    set B : ℝ := C1 * LocalQuadraticParts.nTT D * (L.sc.a / D.R.k + L.sc.b') with hB
    have hB0 : 0 ≤ B := by positivity
    have hterm : ∀ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        (SizeData₂.lwP w * (D.what₂.places.ramIdx w : ℝ)) * (2 * (D.R.m * D.duS u * B)) := by
      intro w hw
      have hwT : D.what₂.places.resChar w = (D.mem u).A.T := hFT w hw
      obtain ⟨-, -, n, hn, hle⟩ := h5 u w hwT
      have hl := hNu.2.2 u w n (by rw [hLen u w hwT, hn])
      have hlw := logWeight_nonneg w
      have he : (0 : ℝ) ≤ D.what₂.places.ramIdx w := Nat.cast_nonneg _
      have hSw := hS u w hwT
      have h1 : (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B) :=
        le_trans hle (by gcongr)
      unfold SizeData₂.sz
      calc 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (L.lenMN u w : ℝ))
          = 2 * SizeData₂.lwP w * (n : ℝ) := by rw [hl]; ring
        _ ≤ 2 * SizeData₂.lwP w * ((D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * B)) := by gcongr
        _ = _ := by ring
    have hsum : ∑ w ∈ F, SizeData₂.sz w (L.lenMN u w) ≤
        Real.log ((D.mem u).A.T : ℝ) * (2 * (D.R.m * D.duS u * B)) := by
      refine le_trans (Finset.sum_le_sum hterm) ?_
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_right
        (sum_lwP_e_le D _ (D.mem u).A.T_prime F hFT) (by positivity)

    have hN1 : 1 ≤ D.R.N D.R.m := by have := D.R.m_add_three_le_k; unfold Ranks.N; omega
    have hTf : 2 * D.R.f + 1 < (D.mem u).A.T := by
      have h := (hSet u).1
      have : 2 * D.R.f ≤ 2 * D.R.f * D.R.N D.R.m := Nat.le_mul_of_pos_right _ hN1
      omega
    have hTfR : 2 * (D.R.f : ℝ) + 1 < (D.mem u).A.T := by exact_mod_cast hTf
    have hf : (0 : ℝ) ≤ D.R.f := Nat.cast_nonneg _
    have hT1 : 0 < ((D.mem u).A.T : ℝ) - 1 := by linarith
    have hT2 : (2 : ℝ) ≤ (D.mem u).A.T := by exact_mod_cast (D.mem u).A.T_prime.two_le
    have hr : (1 / 2 : ℝ) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f := by
      have hb := one_add_mul_le_pow (a := -(1 / (((D.mem u).A.T : ℝ) - 1))) (by
        have : 1 / (((D.mem u).A.T : ℝ) - 1) ≤ 1 := by
          rw [div_le_one hT1]; linarith
        linarith) D.R.f
      have h3 : (D.R.f : ℝ) * (1 / (((D.mem u).A.T : ℝ) - 1)) ≤ 1 / 2 := by
        rw [mul_one_div, div_le_iff₀ hT1]; linarith
      have h4 : (1 + -(1 / (((D.mem u).A.T : ℝ) - 1))) = 1 - 1 / (((D.mem u).A.T : ℝ) - 1) := by ring
      rw [h4] at hb
      linarith
    have hgoal : (4 * C1) * LocalQuadraticParts.nTT D * D.R.m * (L.sc.a / D.R.k + L.sc.b') *
        Real.log ((D.mem u).A.T : ℝ) = 4 * (D.R.m * B * Real.log ((D.mem u).A.T : ℝ)) := by
      rw [hB]; ring
    rw [hgoal]
    rcases eq_or_lt_of_le hd with h0 | h0
    · rw [c1, ← h0, mul_zero, div_zero]; positivity
    · have hdu : 0 < ((D.mem u).A.du : ℝ) := by rw [c1]; positivity
      rw [div_le_iff₀ hdu]
      refine le_trans hsum ?_
      rw [c1]
      have : (D.duS u : ℝ) * (1 / 2) ≤ (1 - 1 / (((D.mem u).A.T : ℝ) - 1)) ^ D.R.f * (D.duS u : ℝ) := by
        rw [mul_comm]; gcongr
      have hP : 0 ≤ D.R.m * B * Real.log ((D.mem u).A.T : ℝ) := by positivity
      nlinarith

theorem family_levelPrime_summary {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps) (C C1 : ℝ) (hC1 : 0 ≤ C1)
    (hE : ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x,
      (∀ u, product_first_zeroth_parts.Conclusion2 (Fm.D x i) u) ∧ (∀ u, product_first_zeroth_parts.Conclusion5 (Fm.D x i) u C) ∧ LocSpan (Fm.D x i) ∧
      LenAtT (Fm.D x i) (Fm.L x i) ∧
      LevelPrimeSizeBounds (Fm.D x i) (Fm.L x i) C1 ∧ ∀ u, product_first_zeroth_parts.HidaSetting (Fm.D x i) u) :
    LocalQuadraticParts.LevelTFamily Fm := by
  obtain ⟨x0, hx0⟩ := hE
  refine ⟨4 * C1, max x0 (Fm.x1 + 1), fun x hx i => ?_⟩
  have hxx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : Fm.x1 < x := by
    have := le_trans (le_max_right x0 (Fm.x1 + 1)) hx
    linarith
  obtain ⟨h2, h5, hLoc, hLen, hS, hSet⟩ := hx0 x hxx0 i
  exact levelPrime_summary_of_fifth (Fm.D x i) (Fm.L x i) C C1 h2 h5 (Fm.nuDef x hx1 i) (Fm.ex x hx1 i).lat.atT hLoc hLen hS
    hSet hC1

end Formalism.MainNotions.J
end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.DIVfromGLk
section
noncomputable section

namespace Formalism.MainNotions.J

open Formalism.BasicNotions Formalism.BasicNotions.DV NumberField

variable {D : D7} {L : SizeData₂ D}

theorem ETDef_of {X : ErrX D} {K : Formalism.MainNotions.G.Consts} {c : ErrC} (P : ParameterChoice' D L) (hF : L.FDef) (hE : L.EDef X K c)
    (hTg : ∀ u (i : Fin 2), D.host.g i ≠ (D.mem u).A.T) : ∀ u, Formalism.MainNotions.product_first_zeroth_parts.ETDef D u L := by
  intro u w hw
  have hw' : D.what₂.places.resChar w = (D.mem u).A.T := hw
  have hs : D.host.cls (D.what₂.places.resChar w) = PrimeClass.splitK := by
    rw [hw']; exact P.level_split _ (D.T_level u)
  obtain ⟨hg, ht, _⟩ := L.not_inert w (by rw [hs]; exact fun h => by cases h) (by rw [hs]; exact fun h => by cases h)
  refine ⟨ht, fun j hj => ⟨hg j, ?_, ?_⟩⟩
  · rw [hF j hj w]
    unfold Fval FvalP
    have h1 : D.what₂.places.resChar w ∉ L.gTypes := by
      rw [hw']
      simp only [SizeData₂.gTypes, Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hTg u 0 h.symm, fun h => hTg u 1 h.symm⟩
    have h2 : D.host.cls (D.what₂.places.resChar w) ≠ PrimeClass.ramD := by rw [hs]; exact fun h => by cases h
    have h3 : ¬ ((Formalism.MainNotions.G.IsResidueClassZero D (D.what₂.places.resChar w) ∨ Formalism.MainNotions.G.IsSg D (D.what₂.places.resChar w)) ∧
        (D.what₂.places.resChar w : ℝ) ≤ L.sc.X'' D.R.n) := by
      rintro ⟨h | h, _⟩
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
      · exact absurd (hs.symm.trans h) (fun h => by cases h)
    rw [if_neg h1, if_neg h2, if_neg h3]
  · rw [hE u j hj w]
    unfold Eval
    simp only [hw', if_true]

end Formalism.MainNotions.J

end
end

-- bundled from Formalism.SharpRestriction.AdmissibleParameterJoins.SfromGLe
section
noncomputable section

namespace Formalism.MainNotions.J

open NumberField Formalism.HermitianLatticesTheory Formalism.BasicNotions

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def IdxColTie (D : D7) : Prop := StandardLattice.idxPi D (D.host.g 0) (D.host.g 1) = S.gaG D

def IdxRowTie (D : D7) : Prop := StandardLattice.idxSig D (D.host.g 0) (D.host.g 1) = LocalBesselAndTopKernel.idxRows D

end Formalism.MainNotions.J

end
end

