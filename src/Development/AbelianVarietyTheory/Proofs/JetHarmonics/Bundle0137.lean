module

public import Mathlib
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumNatCastMemHeightOneSpectrumIff
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0033
public import Development.AbelianVarietyTheory.Definitions.Jets.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0134
public import Development.AbelianVarietyTheory.Definitions.Jets.DepthNumbersThresholdEq
public import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
public import Formalism.LocalToGlobal.LatticeGeometry.Bundle0001
public import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0127
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0123
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Formalism.SharpRestriction.Divisibility.AbelianOpenPart.OEOsInjective
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0027
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GramSpace
public import Formalism.SharpRestriction.Divisibility.WeightAlgebra
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0032
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0035
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0034
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroSplitOfLocalAndSum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.NusOfEqRamMulNuStarAt
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

noncomputable section

namespace GlobalTheory.RunDepthScale

open Formalism.MainNotions.ModuliIntegralCharts.H1 in
theorem nusOf_eq_nuN {D : D7} (B : WeightFamilies.Prov D) {j : ℕ} (w : WeightFamilies.Wt D j)
    (nu : HeightOneSpectrum (𝓞 B.KO) → ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : DepPage)
    (h1 : Q.g1 = D.host.g 0) (h2 : Q.g2 = D.host.g 1) (hq1 : Q.q1 = D.host.q) (hdd : Q.dd = D.host.d)
    (hsm : Q.sm = D.host.small) (hvd : Q.vd = vdOf D) :
    nusOf B w nu la = (ramOverZ la : ℝ) * Q.nuN (WeightAlgebra.DF w) (nu la) (resCharOf la) := by
  classical
  have hq : D.host.q.Prime := D.host.hyp.1
  have hd : D.host.d.Prime := D.host.hyp.2.1
  unfold nusOf DepPage.nuN
  rw [H1algLink.eWL_eq la, h1, h2]
  by_cases hc : ∃ i : Fin 2, ((D.host.g i : ℕ) : 𝓞 B.KO) ∈ la.asIdeal
  · rw [dite_eq_left hc]
    have hch := (H1algLink.prime_mem_iff la (D.host.g_prime _)).1 (Classical.choose_spec hc)
    rw [← hch, mul_div_assoc]
    congr 1
    by_cases e0 : resCharOf la = D.host.g 0
    · rw [if_pos e0, e0]
    · rw [if_neg e0]
      have e1 : resCharOf la = D.host.g 1 := by
        generalize Classical.choose hc = i at hch
        fin_cases i
        · exact absurd hch e0
        · exact hch
      rw [if_pos e1, e1]
  · rw [dite_eq_right hc]
    have e0 : ¬ resCharOf la = D.host.g 0 := fun e =>
      hc ⟨0, (H1algLink.prime_mem_iff la (D.host.g_prime 0)).2 e⟩
    have e1 : ¬ resCharOf la = D.host.g 1 := fun e =>
      hc ⟨1, (H1algLink.prime_mem_iff la (D.host.g_prime 1)).2 e⟩
    rw [if_neg e0, if_neg e1]
    congr 2
    unfold DepPage.cP DepPage.IsRam
    rw [hq1, hdd, hvd, hsm, show ringChar (𝓞 B.KO ⧸ la.asIdeal) = resCharOf la from rfl]
    have hS : ((D.host.QS : ℕ) : 𝓞 B.KO) ∈ la.asIdeal ↔ resCharOf la ∈ D.host.small :=
      (UpperTheory.cmDatum_natCast_mem_heightOneSpectrum_iff D.host.toHostRaw B.KO la).1
    simp only [hS, H1algLink.prime_mem_iff la hq, H1algLink.prime_mem_iff la hd]
    by_cases a2 : resCharOf la ∈ D.host.small
    · rw [if_pos a2, if_pos (Or.inl a2)]
      unfold c2 vdOf
      rw [if_pos a2, Int.ceil_toNat, ← Nat.cast_mul, Nat.ceil_natCast]
    · rw [if_neg a2]
      by_cases b : resCharOf la = D.host.q ∨ resCharOf la = D.host.d
      · rw [if_pos b, if_pos (Or.inr b)]
        unfold Formalism.MainNotions.DIV.Cons.cHalf vdOf
        rw [if_neg a2, Int.ceil_toNat]
        congr 2
        ring
      · rw [if_neg b, if_neg (fun h => h.elim a2 b)]
        simp

theorem nusOf_eq_ram_mul_nuStarAt : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (T : Top D) (h : LawsP T) (EX : ErrX D) (j : ℕ), InR D j → letI := T.Q.H.starRing; ∀ la : HeightOneSpectrum (𝓞 T.Q.c.F), nusOf (recB h.toLawsCore) (lR Tp hK j) (fun la' => (nuW (T.Q.Xo j) T.Q.c la' T.Q.l.M (wtA (lR Tp hK j)) Tp.nWn).toReal / (ramOverZ la' : ℝ)) la = (ramOverZ la : ℝ) * nuStarAt (Xo := T.Q.Xo j) (c := T.Q.c) (depOf T.toCore EX Tp hK) la j := by
  intro D L Pm Tp hK T h EX j hj la
  letI := T.Q.H.starRing
  refine (nusOf_eq_nuN (recB h.toLawsCore) (lR Tp hK j) _ la (depOf T.toCore EX Tp hK).Q rfl rfl rfl rfl rfl rfl).trans ?_
  rw [← GlobalTheory.WeightExponents.DF_wtA h.pins hj (lR Tp hK j)]
  rfl

end GlobalTheory.RunDepthScale
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.RealPlaceWeightRowGapMulBoundsSize
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.GoodDepth.Gap

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.FormalSeriesBounds GlobalTheory.GoodDepth GlobalTheory.RunDepth

variable {D : D7}

theorem emb_inj {t t' : D.what₂.Tau} (h : DV.tauEmb D t = DV.tauEmb D t') : t = t' :=
  D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem emb_ne_conj (t t' : D.what₂.Tau) :
    DV.tauEmb D t ≠ ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') := by
  intro h
  have h1 : ReciprocityTheory.ChartRestriction.G.Geo.Tor.conjEmb (DV.tauEmb D t') =
      D.host.emb (((D.eTau t' : D.R.Psi) : D.R.GG) * D.R.cc) := by
    rw [Formalism.L2.Geo.emb_mul_cc_comp]
    refine RingHom.ext fun x => ?_
    exact (Formalism.MainNotions.WeightFamilies.emb_conj D (DV.tauEmb D t') x).symm
  have h2 := (Formalism.L2.Geo.exists_tauEmb_iff D _).1 ⟨t, (h.trans h1).symm⟩
  exact (Formalism.L2.Geo.mem_Psi_iff_mul_cc_notMem _).1 (D.eTau t').2 h2

theorem wtA_emb {j : ℕ} (w : WeightFamilies.Wt D j) (t : D.what₂.Tau) (i : ℕ) :
    wtA w (DV.tauEmb D t, i) = ext0 (w.aP t) i := by
  classical
  unfold wtA
  rw [Finset.sum_eq_single t]
  · simp [emb_ne_conj]
  · intro t' _ ht'
    have : DV.tauEmb D t ≠ DV.tauEmb D t' := fun h => ht' (emb_inj h).symm
    simp [emb_ne_conj, this]
  · simp

theorem real_bounds {T Dd G y w η t S S' η' w2 x : ℝ} (hT : 40 * (Dd + 2) ≤ T) (hD : 0 ≤ Dd) (hG : 0 ≤ G)
    (h1 : (T + Dd + 2) * G ≤ y) (h2 : y < (T + Dd + 2) * (G + 1)) (hy1 : w - η ≤ y) (hy2 : y ≤ S + w + η + 1)
    (hTt : T ≤ t) (htη : t ≤ η) (h3 : t * η ≤ w2 / x) (hx : 1 < x) (hw : w2 ≤ w)
    (hS : S ≤ 2 * S') (hS' : 0 ≤ S') (hη : η ≤ 2 * η') :
    (1 - (Dd + 4) / T) * w ≤ T * G ∧ T * G ≤ w + 100 * (S' + η') := by
  have hT0 : 0 < T := by linarith
  have htη0 : 0 < t * η := mul_pos (by linarith) (by linarith)
  have h4 : t * η * x ≤ w2 := (le_div_iff₀ (by linarith)).1 h3
  have h5 : t * η ≤ w := by nlinarith
  constructor
  · have e : (1 - (Dd + 4) / T) * w = (T - Dd - 4) * w / T := by field_simp; ring
    rw [e, div_le_iff₀ hT0]
    have a1 : (T - Dd - 2) * (w - η - (T + Dd + 2)) ≤ (T - Dd - 2) * ((T + Dd + 2) * G) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have a2 : 0 ≤ (Dd + 2) ^ 2 * G := by positivity
    have a3 : T * η ≤ t * η := mul_le_mul_of_nonneg_right hTt (by linarith)
    have a4 : T * T ≤ t * η := mul_le_mul hTt (by linarith) hT0.le (by linarith)
    have a5 : 0 ≤ (Dd + 2) * η := mul_nonneg (by linarith) (by linarith)
    have a6 : 0 ≤ (Dd + 2) ^ 2 := by positivity
    nlinarith
  · have a1 : 0 ≤ (Dd + 2) * G := by positivity
    nlinarith

theorem le_two_floor {a : ℝ} (h : 1 ≤ a) : a ≤ 2 * (⌊a⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast (Nat.one_le_floor_iff a).2 h
  have h2 := Nat.lt_floor_add_one a
  linarith

variable {L : SizeData₂ D} {Pm : ParameterChoice' D L}

theorem gap_kappa (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (hj : InR D j) (τ : D.what₂.Tau)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hv : D.R.k - 2 < D.R.k - 1) (hm : 0 < D.R.m) :
    0 ≤ WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ ∧
    ((WeightAlgebra.gapZ ((kaR Tp hK j).aP τ) ⟨D.R.k - 2, h1⟩ : ℤ) : ℚ) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ + (D.hc τ).b ⟨0, hm⟩ - 1 := by
  unfold WeightAlgebra.gapZ
  rw [dite_eq_left h2]
  constructor
  · have := (kaR Tp hK j).aPlus_antitone τ (show (⟨D.R.k - 2, h1⟩ : Fin _) ≤ ⟨D.R.k - 2 + 1, h2⟩ from Nat.le_succ _)
    have h3 : (((kaR Tp hK j).aP τ ⟨D.R.k - 2 + 1, h2⟩ : ℕ) : ℤ) ≤ (kaR Tp hK j).aP τ ⟨D.R.k - 2, h1⟩ := by
      exact_mod_cast this
    exact sub_nonneg.2 h3
  · unfold kaR
    rw [kaWt_big D hK _ j hj.1 hj.2, kaWt_big D hK _ j hj.1 hj.2, Int.cast_sub, (hK j hj.1 hj.2 τ).1,
      (hK j hj.1 hj.2 τ).1, DV.aPlusQ_eq, DV.aPlusQ_eq]
    have e0 : D.R.k - 2 + 1 - (D.R.k - 1) = 0 := by omega
    have s1 : DV.sigPar D τ (D.R.k - 2) = (D.hc τ).v ⟨D.R.k - 2, hv⟩ := by
      unfold DV.sigPar; rw [dite_eq_left hv]
    have s2 : DV.sigPar D τ (D.R.k - 2 + 1) = -(D.hc τ).b ⟨0, hm⟩ := by
      unfold DV.sigPar
      rw [dite_eq_right (by omega), dite_eq_left (by omega)]
      congr 2
      exact Fin.ext e0
    simp only [s1, s2]
    push_cast
    ring

theorem gapW_eq (Tp : ParamsT D L Pm) (hK : DV.KapDef D) {j : ℕ} (z : RPl D.R)
    (h1 : D.R.k - 2 < (D.R.sigW j).1) (h2 : D.R.k - 2 + 1 < (D.R.sigW j).1) (hk : 2 ≤ D.R.k) :
    gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z =
      (Int.fdiv (WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ + 2) (WeightAlgebra.Tp D j Tp.TO)).toNat := by
  have e : D.R.k - 1 = D.R.k - 2 + 1 := by omega
  show wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 2) - wtA (lR Tp hK j) (DV.tauEmb D (plOf D z), D.R.k - 1) = _
  rw [wtA_emb, wtA_emb, e]
  unfold ext0
  rw [dite_eq_left h1, dite_eq_left h2]
  show ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2, h1⟩ -
    ofGaps (lGapP D (kaR Tp hK j) Tp.TO Tp.nWn (plOf D z)) ⟨D.R.k - 2 + 1, h2⟩ = _
  rw [ofGaps_succ _ ⟨D.R.k - 2, h1⟩ h2, Nat.add_sub_cancel]
  unfold lGapP
  rw [if_pos h2]

theorem TO_le_t (Tp : ParamsT D L Pm) : Tp.TO ≤ D.R.t := by
  have a1 := Tp.split
  have a2 := Tp.nP_eq
  have a4 := Tp.nW_40
  have hf : 1 ≤ D.R.f := by
    have h0 : 0 < D.R.toFrame.ord := D.R.toFrame.ord_pos
    have h1 : D.R.f = 2 * D.R.toFrame.ord := rfl
    omega
  have a5 : Tp.TO * 1 ≤ Tp.TO * Tp.nWn := Nat.mul_le_mul_left _ (by omega)
  have a6 : 1 * D.R.r ≤ 8 * D.R.f * D.R.r := Nat.mul_le_mul_right _ (by omega)
  omega

theorem gap_bounds : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (j : ℕ), InR D j → ∀ z : RPl D.R, L.sc.w'' D.R.n ≤ (numOf D L).w j z →
  (1 - ((Tp.Dp : ℝ) + 4) / Tp.TO) * (numOf D L).w j z ≤ (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ∧
  (Tp.TO : ℝ) * gapW (numOf D L) (fun z => DV.tauEmb D (plOf D z)) (wtA (lR Tp hK j)) z ≤ (numOf D L).w j z + 100 * ((numOf D L).Sc + (numOf D L).eta) := by
  intro D L Pm Tp hK j hj z hw
  have hj1 := hj.1
  have hj2 := hj.2
  have hk : 5 ≤ D.R.k := by have := D.R.m_add_three_le_k; have := D.R.two_le_m; omega
  have hs : (D.R.sigW j).1 = D.R.k + j - 1 := rfl
  have h1 : D.R.k - 2 < (D.R.sigW j).1 := by omega
  have h2 : D.R.k - 2 + 1 < (D.R.sigW j).1 := by omega
  have hv : D.R.k - 2 < D.R.k - 1 := by omega
  have hm : 0 < D.R.m := by omega
  have hjm : j - 1 < D.R.m := by omega
  rw [gapW_eq Tp hK z h1 h2 (by omega)]
  obtain ⟨g0, g1⟩ := gap_kappa Tp hK hj (plOf D z) h1 h2 hv hm
  generalize WeightAlgebra.gapZ ((kaR Tp hK j).aP (plOf D z)) ⟨D.R.k - 2, h1⟩ = c at g0 g1 ⊢
  have hT' : WeightAlgebra.Tp D j Tp.TO = Tp.TO + Tp.Dp + 2 := by
    unfold WeightAlgebra.Tp; rw [GlobalTheory.DepthBoundProbe.dimY_eq Tp hj]
  rw [hT', Int.fdiv_eq_ediv_of_nonneg _ (Nat.cast_nonneg _)]
  have hpos : (0 : ℤ) < ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := by positivity
  have q0 : 0 ≤ (c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ) := Int.ediv_nonneg (by omega) hpos.le
  have q1 := Int.mul_ediv_self_le (x := c + 2) hpos.ne'
  have q2 := Int.lt_mul_ediv_self_add (x := c + 2) hpos
  have q3 := Int.toNat_of_nonneg q0
  generalize ((c + 2) / ((Tp.TO + Tp.Dp + 2 : ℕ) : ℤ)).toNat = G at q3 ⊢
  rw [← q3] at q1 q2
  have r1 : ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) ≤ (c : ℝ) + 2 := by exact_mod_cast q1
  have r2 : (c : ℝ) + 2 < ((Tp.TO : ℝ) + Tp.Dp + 2) * (G : ℝ) + ((Tp.TO : ℝ) + Tp.Dp + 2) := by exact_mod_cast q2
  have g2 : (c : ℝ) = (((D.hc (plOf D z)).v ⟨D.R.k - 2, hv⟩ : ℚ) : ℝ) + (((D.hc (plOf D z)).b ⟨0, hm⟩ : ℚ) : ℝ) - 1 := by
    exact_mod_cast congrArg (fun q : ℚ => (q : ℝ)) g1
  have hwe : (numOf D L).w j z = (((D.hc (plOf D z)).e ⟨j - 1, hjm⟩ : ℚ) : ℝ) := by
    unfold NumDatum.w NumDatum.eQ
    congr 1
    split_ifs with h
    · rfl
    · exact absurd (by first | exact hjm | exact ⟨hj1, hj2⟩) h
  have c1 := L.cloud_v (plOf D z) ⟨D.R.k - 2, hv⟩
  have c2 := abs_le.1 (L.be_close (plOf D z) ⟨0, hm⟩ ⟨j - 1, hjm⟩)
  rw [Rat.cast_sub] at c2
  have hT40 : 40 * ((Tp.Dp : ℝ) + 2) ≤ Tp.TO := by exact_mod_cast Tp.TO_40
  have hD : (0 : ℝ) ≤ Tp.Dp := Nat.cast_nonneg _
  have hT2 : (1 : ℝ) ≤ (Tp.TO : ℝ) ^ 2 := one_le_pow₀ (by linarith)
  have hDel := le_two_floor (hT2.trans Tp.Del_TO)
  have hh0 : (1 : ℝ) ≤ LevelStarExponents.h0 L := by
    have := Tp.heightBound_ge_order_sq
    have : (0 : ℝ) ≤ D.R.t := Nat.cast_nonneg _
    linarith
  have hh := le_two_floor hh0
  have hmR : (0 : ℝ) < D.R.m := by exact_mod_cast hm
  refine real_bounds (y := (c : ℝ) + 2) (η := L.etaSz) (t := D.R.t) (S := L.Sc) hT40 hD (Nat.cast_nonneg _) r1
    (by linarith) (by rw [hwe]; linarith [c1.1, c2.1]) (by rw [hwe]; linarith [c1.2, c2.2])
    (by exact_mod_cast TO_le_t Tp) Pm.t_le_eta Pm.teta L.sc.one_lt_alt hw ?_ ?_ ?_
  · rw [L.Sc_eq]
    show _ ≤ 2 * ((D.R.k : ℝ) * (4 * ((⌊(D.s.Del : ℝ)⌋₊ : ℕ) : ℝ)))
    have : (0 : ℝ) ≤ D.R.k := Nat.cast_nonneg _
    nlinarith
  · unfold NumDatum.Sc; positivity
  · show _ ≤ 2 * ((D.R.m : ℝ) * ((⌊LevelStarExponents.h0 L⌋₊ : ℕ) : ℝ))
    have e : L.etaSz = D.R.m * LevelStarExponents.h0 L := by unfold LevelStarExponents.h0; field_simp
    rw [e]
    nlinarith

end GlobalTheory.GoodDepth.Gap
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.SizesBoundAtTwoFirstRowsWeights
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.DIV Formalism.L2.Pj Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.L2.Indef.Tree.DepthCond Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Datum Level Moduli Coeff)
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF (AvFSt HTFSt UpFSt)
open GlobalTheory.RunDepth GlobalTheory.CharDepth

namespace GlobalTheory.RunDepth

theorem vd2_nonneg_of_D7 (D : D7) : 0 ≤ vd2 D := by
  unfold vd2
  exact Real.logb_nonneg (by norm_num) (by exact_mod_cast D.host.QS_pos)

theorem sizes_two_arith (T f q m v A S C b Sc η : ℝ) (hf : 0 ≤ f) (hq : 0 ≤ q) (hqm : q ≤ m) (hv : 0 ≤ v)
    (hC : 1 ≤ C) (hb : 0 ≤ b) (hSc : 0 ≤ Sc) (hη : 0 ≤ η) (hA : T * A = 2 * b + Sc) (hS : T * S ≤ f * η) :
    T * (f * q * (1 + v / 2) * A + q * S) ≤ C * m * (2 + v) * (2 * f * b + f * (Sc + η)) := by
  have hm : 0 ≤ m := hq.trans hqm
  have e1 : T * (f * q * (1 + v / 2) * A + q * S) = q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) := by
    rw [← hA]; ring
  have h1 : f * (1 + v / 2) * (2 * b + Sc) + T * S ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by
    have p1 : 0 ≤ f * (1 + v / 2) * (2 * b + Sc) := by positivity
    have p2 : 0 ≤ (1 + v) * (f * η) := by positivity
    nlinarith
  have h0 : 0 ≤ (2 + v) * (2 * f * b + f * (Sc + η)) := by positivity
  rw [e1]
  calc q * (f * (1 + v / 2) * (2 * b + Sc) + T * S) ≤ q * ((2 + v) * (2 * f * b + f * (Sc + η))) :=
        mul_le_mul_of_nonneg_left h1 hq
    _ ≤ m * ((2 + v) * (2 * f * b + f * (Sc + η))) := mul_le_mul_of_nonneg_right hqm h0
    _ ≤ C * (m * ((2 + v) * (2 * f * b + f * (Sc + η)))) := le_mul_of_one_le_left (mul_nonneg hm h0) hC
    _ = _ := by ring

theorem sizes_bound_two : ∀ (D : D7) (L : SizeData₂ D) (Pm : ParameterChoice' D L) (Tp : ParamsT D L Pm) (hK : DV.KapDef D) (Q : Par D), Q.Pins → 3 ≤ L.sc.x → (D.R.k : ℝ) * L.sc.b' ≤ L.sc.b → ∀ C : ℝ, 1 ≤ C → ∀ j, InR D j → ∃ Ap : ℝ, 0 ≤ Ap ∧ (∀ τ, InPsi Q.H τ → (wtA (lR Tp hK j) (τ, 0) : ℝ) ≤ Ap) ∧ (open Classical in (Tp.TO : ℝ) * ((D.R.f : ℝ) * (Q.Dw j).q * (1 + vd2 D / 2) * Ap + (Q.Dw j).q * ∑ τ ∈ Finset.univ.filter (fun τ => ¬ InPsi Q.H τ), (wtA (lR Tp hK j) (τ, 0) : ℝ)) ≤ C * D.R.m * (2 + vd2 D) * (2 * (D.R.f : ℝ) * L.sc.b + (D.R.f : ℝ) * (L.Sc + L.etaSz))) := by
  classical
  intro D L Pm Tp hK Q hQ hx hkb C hC j hj
  obtain ⟨hSe, hw⟩ := _root_.GlobalTheory.RunDepth.sizes_le_two_mul D L Pm hx hkb
  obtain ⟨hw1, -, -⟩ := hw j hj
  obtain ⟨-, -, hP, hN, hwt⟩ := _root_.GlobalTheory.WeightExponents.weight_exponents D Q hQ j hj (lR Tp hK j)
  have hT : (0 : ℝ) < (Tp.TO : ℝ) := by exact_mod_cast TO_pos Tp
  have hb : 0 ≤ L.sc.b := (Real.exp_pos _).le
  have hSc := L.Sc_pos.le
  have hη := L.etaSz_pos.le
  have hplus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aP t) 0 : ℝ) ≤ 2 * L.sc.b + L.Sc := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aP t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aP t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (_root_.GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).1 ⟨0, h⟩
      obtain ⟨h2, h3, -⟩ := _root_.GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t
      rcases Nat.lt_or_ge 0 (D.R.k - 1) with hk | hk
      · have := h2 ⟨0, h⟩ hk
        have := (hw1 t).2
        linarith
      · have := h3 ⟨0, h⟩ hk
        linarith
    · simp only [Nat.cast_zero, mul_zero]; linarith
  have hminus : ∀ t, (Tp.TO : ℝ) * (ext0 ((lR Tp hK j).aM t) 0 : ℝ) ≤ L.etaSz := by
    intro t
    unfold Formalism.L2.Pj.ext0
    split_ifs with h
    · have h1 : (Tp.TO : ℝ) * ((lR Tp hK j).aM t ⟨0, h⟩ : ℝ) ≤ ((kaR Tp hK j).aM t ⟨0, h⟩ : ℝ) := by
        exact_mod_cast (_root_.GlobalTheory.RunDepth.mul_rows_lR_le_kaR D L Pm Tp hK j t).2.1 ⟨0, h⟩
      exact h1.trans ((_root_.GlobalTheory.WeightRows.kappa_entries_le D L Pm Tp hK j hj t).2.2 _)
    · simpa using hη
  refine ⟨(2 * L.sc.b + L.Sc) / Tp.TO, by positivity, ?_, ?_⟩
  · intro τ hτ
    obtain ⟨t, rfl⟩ := (hP τ).1 hτ
    rw [(hwt t 0).1, le_div_iff₀ hT, mul_comm]
    exact hplus t
  · have hq : (Q.Dw j).q ≤ D.R.m := by
      rw [(hQ.2.2.2 j hj).2.1]
      exact Nat.sub_le _ _
    refine sizes_two_arith _ _ _ _ _ _ _ _ _ _ _ (Nat.cast_nonneg _) (Nat.cast_nonneg _) (by exact_mod_cast hq)
      (vd2_nonneg_of_D7 D) hC hb hSc hη (by field_simp) ?_
    rw [Finset.mul_sum]
    have hcard : (Finset.univ.filter (fun τ => ¬ InPsi Q.H τ)).card ≤ D.R.f := by
      rw [← (_root_.GlobalTheory.RunDepth.plOf_bijective_card D).2, ← Finset.card_univ]
      refine le_trans (Finset.card_le_card ?_)
        (Finset.card_image_le (f := fun t => ComplexEmbedding.conjugate (DV.tauEmb D t)))
      intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      exact Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩
    refine (Finset.sum_le_card_nsmul _ _ L.etaSz ?_).trans ?_
    · intro τ hτ
      obtain ⟨t, rfl⟩ := (hN τ).1 (Finset.mem_filter.1 hτ).2
      rw [(hwt t 0).2]
      exact hminus t
    · rw [nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hη

end GlobalTheory.RunDepth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.WeightOnDatum
section
open AlgebraicGeometry CategoryTheory NumberField IsLocalRing IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps.EtaleWeightGaps
open GlobalTheory.PtTie

namespace GlobalTheory.WeightOnDatum

theorem weight_on_datum : ∀ (D : D7) (T : Core D), T.Q.Pins → ∀ (j : ℕ), InR D j → ∀ w : WeightFamilies.Wt D j, Formalism.L2.Pj.DF (T.Q.Dw j) (wtA w) = WeightAlgebra.DF w ∧ DomW (T.Q.Dw j) (wtA w) ∧ (w.LastPos → Formalism.L2.Pj.LastPos (T.Q.Dw j) (wtA w) ∧ 1 ≤ WeightAlgebra.DF w) ∧ (∀ τ, (T.Q.Dw j).mult τ ≤ D.R.r) ∧ Fintype.card (Lt1 (T.Q.Dw j)) ≤ 2 * D.R.f * D.R.r ∧ 1 ≤ D.R.f ∧ 1 ≤ D.R.r ∧ Module.finrank ℚ D.host.E = 2 * D.R.f := by
  intro D T hP j hj w
  obtain ⟨hDF, -, hPsi, hN, hwt⟩ := GlobalTheory.WeightExponents.weight_exponents D T.Q hP j hj w
  have hfr : Module.finrank ℚ D.host.E = 2 * D.R.f := by
    rw [D.host.finrank_cmField]
    unfold Ranks.f Ranks.n
    ring
  obtain ⟨hp, hq, -⟩ := hP.2.2.2 j hj
  have hm2 := D.R.two_le_m
  have hk5 := D.R.m_add_three_le_k
  have hj1 := hj.1
  have hj2 := hj.2
  have hr : (T.Q.Dw j).p + (T.Q.Dw j).q = D.R.r := by
    rw [hp, hq]
    simp only [Ranks.sigW, Ranks.r]; omega
  have hf : 1 ≤ D.R.f := by
    have := D.R.m_le_f
    unfold Ranks.f Ranks.n
    omega
  have hp0 : 0 < (D.R.sigW j).1 := by
    simp only [Ranks.sigW]; omega
  have hlast : w.LastPos → ∀ t, 1 ≤ w.aP t ⟨(D.R.sigW j).1 - 1, by omega⟩ := fun hw t =>
    hw t _ (by show (D.R.sigW j).1 - 1 + 1 = _; omega)
  refine ⟨hDF, ?_, fun hw => ⟨?_, ?_⟩, fun τ => ?_, ?_, hf, by omega, hfr⟩
  · intro τ i i' h
    exact (dom_wtA w).1 τ h
  · intro τ hτ _
    obtain ⟨t, rfl⟩ := (hPsi τ).1 hτ
    have hmult : (T.Q.Dw j).mult (DV.tauEmb D t) = (D.R.sigW j).1 := by
      unfold Datum.mult
      have hτ' : (DV.tauEmb D t) (T.Q.H.rt : D.host.E) = T.Q.H.rt0 := hτ
      rw [if_pos hτ', hp]
    rw [hmult, (hwt t _).1]
    unfold ext0
    rw [dite_eq_left (by omega)]
    exact hlast hw t
  · have ht : Nonempty D.what₂.Tau := by
      by_cases h : InPsi T.Q.H D.host.φ₀
      · obtain ⟨t, -⟩ := (hPsi _).1 h
        exact ⟨t⟩
      · obtain ⟨t, -⟩ := (hN _).1 h
        exact ⟨t⟩
    obtain ⟨t⟩ := ht
    unfold WeightAlgebra.DF WeightAlgebra.degP
    refine le_trans ?_ (Finset.single_le_sum (f := fun τ => (∑ i, w.aP τ i) + ∑ i, w.aM τ i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t))
    refine le_trans ?_ (Nat.le_add_right _ _)
    exact le_trans (hlast hw t) (Finset.single_le_sum (f := fun i => w.aP t i)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ _))
  · rw [← hr, Datum.mult]
    split_ifs <;> omega
  · refine card_Lt1_le_finrank_mul.trans ?_
    rw [hfr, hr]

end GlobalTheory.WeightOnDatum
end

