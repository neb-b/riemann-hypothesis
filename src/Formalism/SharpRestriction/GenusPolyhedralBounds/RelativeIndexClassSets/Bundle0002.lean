module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.PublishedIntClosHolds
public import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.Bundle0007
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionSheafQuotient
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0001

@[expose] public section

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FinitePtsOfCurve
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

theorem Kp_charZero (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : CharZero (Kp X la N) := by
  have := Kl_charZero X la
  exact charZero_of_injective_algebraMap (algebraMap (X.Kl la) (Kp X la N)).injective

theorem unif_irreducible (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) : Irreducible (unif X la) :=
  Classical.choose_spec (IsDiscreteValuationRing.exists_irreducible (X.Ol la))

theorem unifO_irreducible (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) : Irreducible (unifO X la N) :=
  Op.irreducible_map X la N (unif_irreducible X la)

variable {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

theorem isUnif_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) : IsUnif (OsK X la G.w) (unifO X la G.N) := by
  have := hC.1
  have : Algebra.IsIntegral (Kp X la G.N) (OsK X la G.w) := Algebra.IsIntegral.of_finite _ _
  exact isUnif_of_field (Kp X la G.N) (unifO_irreducible X la G.N)

theorem finite_As_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) :
    Module.Finite (Op X la G.N) ↥(As (Op X la G.N) (OsK X la G.w)) := by
  have := hC.1
  have := hC.2.1
  have := Kp_charZero X la G.N
  exact (integralClosure_dvr' (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).1

theorem isDVRAt_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) (ζ : PtsG G la) : IsDVRAt ζ := by
  have := hC.1
  have := hC.2.1
  have := Kp_charZero X la G.N
  exact (integralClosure_dvr' (Op X la G.N) (Kp X la G.N) (OsK X la G.w)).2 ζ

theorem finite_pts_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) :
    Finite (PtsG G la) ∧
      (∑ᶠ ζ : PtsG G la, ep (unifO X la G.N) ζ * fdeg ζ) = Module.finrank (Kp X la G.N) (OsK X la G.w) := by
  have := hC.1
  have := hC.2.1
  have : ∀ ζ : PtsG G la, IsDVRAt ζ := isDVRAt_of_curve Q hC
  exact _root_.ramificationDegreeSum (Op X la G.N) (Kp X la G.N) (OsK X la G.w) (unifO X la G.N) (unifO_irreducible X la G.N)
    (finite_As_of_curve Q hC)

theorem one_le_ep_of_curve (Q : LocalPointData G la) (hC : Q.InCurve) (ζ : PtsG G la) : 1 ≤ ep (unifO X la G.N) ζ := by
  have := isDVRAt_of_curve Q hC ζ
  exact ep_pos ζ (isUnif_of_curve Q hC)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.FirstLengthLePrimeBound
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def firstLength_le_prime_bound (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (T : ℕ) :
    Submodule (Op X la G.N) (WK X la G.w wF (a0 D j T)) :=
  Submodule.span (Op X la G.N) ((rhoK X la G.w wF (a0 D j T) T) ''
    {f : ↥(Vw X la G.N (addL wF wL T)) | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
      (f : Rp X la G.N) = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))})

def LenBase : Prop :=
  ∀ (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ i, G.th' i ∈ B.Mlat j wF) → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    Q.Ila ≠ ⊤ →
    Module.length (Op X la G.N) (↥(Q.AA T) ⧸ (firstLength_le_prime_bound G la T).comap (Q.AA T).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * Q.Ila.toNat : ℕ) : ℕ∞)

def LenPole : Prop :=
  ∀ (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (Q : LocalPointData G la) (S : Scal B) (CRm : ℝ) (T e : ℕ) (c : ℝ),
    Q.Ok S CRm T c → (∀ k, G.w k ∈ X.WWc S.sW wL) →
    Module.length (Op X la G.N) (↥(Q.AAp T (Q.mm S T e)) ⧸ (Q.AA T).comap (Q.AAp T (Q.mm S T e)).subtype) ≤
      ((Nat.choose (T - 1) (WeightFamilies.dimY D j) * ∑ᶠ ζ, Q.mm S T e ζ * fdeg ζ : ℕ) : ℕ∞)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.HeightsOfHtConcl
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module Formalism.MainNotions.Gaps.EtaleWeightGaps

namespace Formalism.MainNotions.Gaps.HeightData

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def toHtData (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ) : HtData where
  K := B.KO
  D := WeightFamilies.dimY D j
  δ := G.del
  i := G.iet
  g0 := (g0 D : ℝ)
  L := wL.size
  G := Gc
  PH := PH
  Prw := Prw
  Pet := Pet
  S k := WeightFamilies.meanLogSup B (G.th' k)
  etaPart := j < D.R.m
  Op la := Op X la G.N
  SectionSheafQuotient la := SectionSheafQuotient X la G.w wF
  A0 la := (Qf la).A0
  t la := tL G la
  Pts la := PtsG G la
  ep la ζ := ep (unifO X la G.N) ζ
  f _ ζ := fdeg ζ
  vEt la ζ := (X.vAt la ((Qf la).y ζ) (X.inc _ G.et)).toReal

theorem heights_of_htConcl (G : GlobalFamilyData X ka wL wF) (Qf : ∀ la, LocalPointData G la) (Gc PH Prw Pet : ℝ)
    (h : HtConcl (toHtData G Qf Gc PH Prw Pet)) : Heights Qf Gc PH Prw Pet := by
  exact h

end Formalism.MainNotions.Gaps.HeightData
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LenAtEqZeroOfSubsingleton
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D}

theorem rho_eq_zero_of_ge {j : ℕ} (hj : D.R.m ≤ j) : WeightFamilies.rho D j = 0 := by
  unfold WeightFamilies.rho Ranks.sigW
  exact Nat.sub_eq_zero_of_le hj

theorem not_killed_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (cu : B.Cu j)
    (χ : WeightFamilies.ExpoSet D (B.Xc j cu)) : ¬ WeightFamilies.Killed B CR T c cu χ := by
  rintro ⟨xi, -, hne, -⟩
  apply hne
  funext i
  exact absurd (hρ ▸ i.2 : i.1 < 0) (Nat.not_lt_zero _)

theorem MggK_eq_top_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    WeightFamilies.MggK B CR T c j ka = ⊤ := by
  unfold WeightFamilies.MggK
  simp only [iInf_eq_top]
  intro cu χ hk
  exact absurd hk (not_killed_of_rho hρ CR T c cu χ)

theorem MggIn_eq_top_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    WeightFamilies.MggIn B CR T c j ka = ⊤ := by
  unfold WeightFamilies.MggIn
  rw [MggK_eq_top_of_rho hρ]
  rfl

theorem Qm_subsingleton_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    Subsingleton (WeightFamilies.Qm B CR T c j ka) :=
  Submodule.Quotient.subsingleton_iff.2 (MggIn_eq_top_of_rho hρ CR T c ka)

theorem rhoP_eq_zero_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j) :
    WeightFamilies.rhoP B CR T c j ka = 0 := by
  have := Qm_subsingleton_of_rho (B := B) hρ CR T c ka
  unfold WeightFamilies.rhoP
  exact Module.finrank_zero_of_subsingleton

theorem lenAt_eq_zero_of_subsingleton (la : HeightOneSpectrum (𝓞 B.KO)) (N : Type) [AddCommGroup N] [Module (𝓞 B.KO) N]
    [Subsingleton N] : WeightFamilies.lenAt B la N = 0 := by
  unfold WeightFamilies.lenAt
  rw [Module.length_eq_zero_iff]
  infer_instance

theorem lenAt_Qm_eq_zero_of_rho {j : ℕ} (hρ : WeightFamilies.rho D j = 0) (CR T c : ℝ) (ka : WeightFamilies.Wt D j)
    (la : HeightOneSpectrum (𝓞 B.KO)) (N : Submodule (𝓞 B.KO) (WeightFamilies.Qm B CR T c j ka)) :
    WeightFamilies.lenAt B la (WeightFamilies.Qm B CR T c j ka ⧸ N) = 0 := by
  have := Qm_subsingleton_of_rho (B := B) hρ CR T c ka
  exact lenAt_eq_zero_of_subsingleton la _

def lenQ {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (CRm : ℝ) (T : ℕ) (c : ℝ)
    (la : HeightOneSpectrum (𝓞 B.KO)) : ℝ :=
  ((WeightFamilies.lenAt B la (WeightFamilies.Qm B CRm T c j ka ⧸ Submodule.span (𝓞 B.KO)
    (Set.range fun i : Fin G.rq => (Submodule.Quotient.mk (G.th i) : WeightFamilies.Qm B CRm T c j ka)))).toNat : ℝ)

theorem lenQ_of_ge {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (hj : D.R.m ≤ j) (CRm : ℝ)
    (T : ℕ) (c : ℝ) (la : HeightOneSpectrum (𝓞 B.KO)) : lenQ G CRm T c la = 0 := by
  unfold lenQ
  rw [lenAt_Qm_eq_zero_of_rho (rho_eq_zero_of_ge hj)]
  simp

theorem rLa_tsum_split {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF}
    (Qf : ∀ la, LocalPointData G la) (CRm : ℝ) (T : ℕ) (c : ℝ)
    (hI : Summable (fun la => ((Qf la).Ila.toNat : ℝ) * X.lN la))
    (hN : j < D.R.m → Summable (fun la => (Qf la).Net * X.lN la))
    (hC : Summable (fun la => (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la))
    (hQ : Summable (fun la => lenQ G CRm T c la * X.lN la)) :
    Summable (fun la => rLa (Qf la) CRm T c * X.lN la) ∧
    ∑' la, rLa (Qf la) CRm T c * X.lN la =
      (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((∑' la, ((Qf la).Ila.toNat : ℝ) * X.lN la) +
        (if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * ∑' la, (Qf la).Net * X.lN la else 0)) +
      (∑' la, (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la) +
      ∑' la, lenQ G CRm T c la * X.lN la := by
  by_cases hj : j < D.R.m
  · have e : (fun la => rLa (Qf la) CRm T c * X.lN la) = fun la =>
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * (((Qf la).Ila.toNat : ℝ) * X.lN la) +
          (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * ((T : ℝ) * (max 0 c / (2 * (G.iet : ℝ)))) *
            ((Qf la).Net * X.lN la) +
          (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la + lenQ G CRm T c la * X.lN la := by
      funext la
      unfold rLa lenQ
      rw [if_pos hj]
      ring
    have h := (((hI.hasSum.mul_left (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ)).add
      ((hN hj).hasSum.mul_left ((Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) *
        ((T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))))))).add hC.hasSum).add hQ.hasSum
    rw [e]
    refine ⟨h.summable, h.tsum_eq.trans ?_⟩
    rw [if_pos hj]
    ring
  · have e : (fun la => rLa (Qf la) CRm T c * X.lN la) = fun la =>
        (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * (((Qf la).Ila.toNat : ℝ) * X.lN la) +
          (Formalism.MainNotions.Gaps.SizeBoundsAlt.gaussC (B.Mlat j ka) G.zc la : ℝ) * X.lN la + lenQ G CRm T c la * X.lN la := by
      funext la
      unfold rLa lenQ
      rw [if_neg hj]
      ring
    have h := ((hI.hasSum.mul_left (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ)).add hC.hasSum).add hQ.hasSum
    rw [e]
    refine ⟨h.summable, h.tsum_eq.trans ?_⟩
    rw [if_neg hj]
    ring

theorem lenQ_tsum_of_ge {j : ℕ} {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData X ka wL wF) (hj : D.R.m ≤ j)
    (CRm : ℝ) (T : ℕ) (c : ℝ) :
    Summable (fun la => lenQ G CRm T c la * X.lN la) ∧ ∑' la, lenQ G CRm T c la * X.lN la = 0 := by
  have e : (fun la => lenQ G CRm T c la * X.lN la) = fun _ => (0 : ℝ) := by
    funext la
    rw [lenQ_of_ge G hj, zero_mul]
  rw [e]
  exact ⟨summable_zero, tsum_zero⟩

theorem ka_eq_addL {j : ℕ} {ka wL wF : WeightFamilies.Wt D j} {T nP nW : ℕ} (hF : IsF' ka wL wF T nP) (hn : wL.n = nW)
    (hk : ka.n = nP + T * nW) : ka = addL wF wL T := by
  obtain ⟨h1, h2, h3⟩ := hF
  apply Formalism.MainNotions.Gaps.SizeBoundsAlt.weight_ext
  · funext τ i
    have := h2 τ i
    simp only [addL, wadd, wsmul]
    zify
    linarith
  · funext τ i
    have := h3 τ i
    simp only [addL, wadd, wsmul]
    zify
    linarith
  · simp only [addL, wadd, wsmul]
    rw [h1, hn, hk]

theorem ka_eq_addL_of_setC {j : ℕ} {large₂ : SizeData₂ D} {X : PJ D B P j} {CK C1 A1 : ℝ} {ka wL wF : WeightFamilies.Wt D j}
    {T nP nW : ℕ} {h0 : ℝ} (hC : SetC large₂ X CK C1 A1 ka wL wF T nP nW h0) : ka = addL wF wL T := by
  obtain ⟨hk, -, -, -, -, -, -, -, -, -, -, -, -, hV, hIL, hIF, -⟩ := hC
  exact ka_eq_addL hIF hIL.1 (hk.trans hV)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.WeightedPrimeSumBound
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

def WeightedPrimeSumBoundAlt (large₂ : SizeData₂ D) (X : PJ D B P j) (wL : WeightFamilies.Wt D j) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  (∀ la, 0 ≤ nus la) ∧ (Function.support nus).Finite ∧ (∑ᶠ la, |nus la| * X.lN la) ≤ PN D large₂ * wL.size

def HypC (large₂ : SizeData₂ D) (X : PJ D B P j) (H : KHyp) (C2 A2 CR Bx CT : ℝ) (S : Scal B)
    (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ParA large₂ H.CA ∧ SetC large₂ X H.CK H.C1 H.A1 ka wL wF T nP nW h0 ∧ ScalB large₂ X H.C1 H.A1 S ka wL wF T ∧
    WeightedPrimeSumBoundAlt large₂ X wL nus ∧ H2 X S ka wL wF ∧ H3 large₂ H C2 A2 CR Bx wL T ∧ H4 large₂ X H C2 A2 CR ka wL wF T nW ∧
    (T : ℝ) ≤ large₂.sc.x ^ CT

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j}

def CombBound (G : GlobalFamilyData X ka wL wF) (S : Scal B) (c : ℝ) (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ) : Prop :=
  ∀ la (y : X.Pt la),
    (j < D.R.m → 0 ≤ X.vAt la y (X.inc _ G.et) ∧ (X.vAt la y (X.inc _ G.et) ≠ ⊤ →
      X.depth S.sW wL la y ≤ (((nus la : ℝ) + c / (2 * (G.iet : ℝ)) * (X.vAt la y (X.inc _ G.et)).toReal : ℝ) : EReal))) ∧
    (D.R.m ≤ j → X.depth S.sW wL la y ≤ ((nus la : ℝ) : EReal))

def LatAt (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) : Prop := Submodule.IsFullLattice B.KO (B.Mlat j ka)

def SupBoundByL2AtWeight (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CG AG : ℝ) : Prop :=
  ∀ (F : B.Cusp j ka) (σ : B.KO →+* ℂ),
    B.supN j ka σ F ^ 2 ≤ Real.exp (WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size)) * B.l2NormAlt j ka σ F ^ 2

def LAMwAt (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (C A : ℝ) : Prop :=
  ∀ F : B.Cusp j ka, F ∈ B.Mlat j ka → F ≠ 0 →
    -(WeightFamilies.PP0v D large₂ C A * (1 + Real.log ka.size) * ka.size) ≤ WeightFamilies.meanLogSup B F

def QAt (large₂ : SizeData₂ D) (B : WeightFamilies.Prov D) (j : ℕ) (ka : WeightFamilies.Wt D j) (CR Ck Ch Ah Cc Ac T c : ℝ) : Prop :=
  0 ≤ CR → WeightFamilies.Obound B large₂ Ch Ah → ka.n = D.R.nV → ka.LastPos →
    ka.size ≤ Ck * (D.R.k : ℝ) * (D.R.f : ℝ) * large₂.sc.b → 0 < T → 0 < c → T * c ≤ 1 →
  ∃ be : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ, (∀ la, 0 ≤ be la) ∧
    (be.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ WeightFamilies.PPv D large₂ Cc Ac * ka.size ∧
  ∀ th : Fin (WeightFamilies.rhoP B CR T c j ka) → B.Mlat j ka,
    Submodule.span B.KO (Set.range fun i => ((th i : B.Mlat j ka) : B.Cusp j ka)) ⊔ WeightFamilies.MggK B CR T c j ka = ⊤ →
    (∀ i, WeightFamilies.meanLogSup B ((th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) →
  ∃ nn : HeightOneSpectrum (𝓞 B.KO) →₀ ℝ,
    (∀ la, ∃ ℓ : ℕ,
      WeightFamilies.lenAt B la (WeightFamilies.Qm B CR T c j ka ⧸ Submodule.span (𝓞 B.KO)
        (Set.range fun i => (Submodule.Quotient.mk (th i) : WeightFamilies.Qm B CR T c j ka))) = ℓ ∧
      (ℓ : ℝ) ≤ nn la + (WeightFamilies.rhoP B CR T c j ka : ℝ) * be la) ∧
    (nn.sum fun la v => v * WeightFamilies.lnN B la) / WeightFamilies.degO B ≤ (WeightFamilies.rhoP B CR T c j ka : ℝ) * WeightFamilies.PPv D large₂ Cc Ac * ka.size

namespace GlobalFamilyData

variable (G : GlobalFamilyData X ka wL wF)

def TiedW (S : Scal B) (Gc Prw : ℝ) : Prop :=
  Submodule.span (𝓞 B.KO) (Set.range G.w) = X.WWc S.sW wL ∧ (∀ k, G.w k ∈ B.Mlat j wL) ∧
  Real.log G.N ≤ Prw * (wL.size - 1) ∧ (∀ σ k, Real.log (B.supN j wL σ (G.w k)) ≤ G.mx σ) ∧
  (∑ σ, G.mx σ) / (Fintype.card (B.KO →+* ℂ) : ℝ) ≤ Gc * wL.size

def TiedTh (S : Scal B) (Gc : ℝ) : Prop :=
  ∀ i, G.th' i ∈ X.Thc S.sF wF ∧ WeightFamilies.meanLogSup B (G.th' i) ≤ Gc * wF.size

def TiedZ (S : Scal B) (T : ℕ) (Gc : ℝ) : Prop :=
  (∀ k, G.th0 k ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ G.th0 k ∈ B.Mlat j (X.wF0 wL wF) ∧
    WeightFamilies.meanLogSup B (G.th0 k) ≤ Gc * (X.wF0 wL wF).size ∧ ∑ i, G.alz k i = a0 D j T) ∧
  (∀ k β, X.inc ka (G.zc k β) = (Formalism.MainNotions.Gaps.SizeBoundsAlt.zPoly X G.w (G.alz k) (G.th0 k)).coeff β) ∧
  (∃ φ : Fin G.rz → B.Cusp j ka →ₗ[B.KO] B.KO, Formalism.MainNotions.Gaps.SizeBoundsAlt.detPoly φ G.zc ≠ 0)

def TiedQ (large₂ : SizeData₂ D) (S : Scal B) (CRm : ℝ) (T : ℕ) (c Ch Ah : ℝ) : Prop :=
  G.rq = WeightFamilies.rhoP B CRm T c j ka ∧ (∀ i, ((G.th i : B.Mlat j ka) : B.Cusp j ka) ∈ X.Thc S.sK ka) ∧
  Submodule.span B.KO (Set.range fun i => ((G.th i : B.Mlat j ka) : B.Cusp j ka)) ⊔ WeightFamilies.MggK B CRm T c j ka = ⊤ ∧
  ∀ i, WeightFamilies.meanLogSup B ((G.th i : B.Mlat j ka) : B.Cusp j ka) ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size

def TiedEt (large₂ : SizeData₂ D) (Cf Af : ℝ) : Prop :=
  j < D.R.m → 0 < G.iet ∧ G.et ≠ 0 ∧ X.NonZeroComp _ G.et ∧
    ∀ σ, Real.log (B.supN j _ σ G.et) / G.iet ≤ WeightFamilies.PPv D large₂ Cf Af

end GlobalFamilyData

def DeepHerm (X : PJ D B P j) (ka : WeightFamilies.Wt D j) : Prop :=
  ∃ (dH : ℕ) (Hm : Formalism.MainNotions.Gaps.SizeBoundsAlt.Herm (fun σ => B.l2NormAlt j ka σ) dH), Hm.Conj

def DeepSubMul (X : PJ D B P j) : Prop := Formalism.MainNotions.Gaps.SizeBoundsAlt.SubMul X

def DeepLogD (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (Pd : ℝ) : Prop := Real.log (finrank B.KO (B.Cusp j ka) : ℝ) ≤ Pd

def PageGd (X : PJ D B P j) (ka : WeightFamilies.Wt D j) (large₂ : SizeData₂ D) (CG AG Pd : ℝ) : Prop :=
  WeightFamilies.PPv D large₂ CG AG * (1 + Real.log ka.size) ≤ Pd

def ShareRd (T del d : ℕ) : Prop := (Nat.choose (T - 1) (WeightFamilies.dimY D j) : ℝ) * del ≤ d

def ShareRho (T rz d : ℕ) : Prop := (rz : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def ShareRhoP (T rq d : ℕ) : Prop := (rq : ℝ) ≤ 22 * (WeightFamilies.dimY D j : ℝ) ^ 2 * d / T

def LocalPointData.InLift {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (T : ℕ) : Prop :=
  ∀ a ∈ Q.A0, ∃ x : ↥(HK X la G.w wF), toA0K X la G.w wF x = a ∧ toWK X la G.w wF (a0 D j T) x ∈ Q.AA T

def LocalPointData.InLiftC {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G la) (S : Scal B) (Gc Prw : ℝ) (T : ℕ) : Prop :=
  G.TiedW S Gc Prw → Q.InCurve → Q.InTie S → Q.InLift T

def InContainZ (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (S : Scal B) (T : ℕ) : Prop :=
  Submodule.span (Kp X la G.N)
      {v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (θ : B.Cusp j (X.wF0 wL wF)), ∑ i, al i = a0 D j T ∧
          θ ∈ X.Thc S.s0 (X.wF0 wL wF) ∧ v = secPow X la G.w al * emb X la G.N (X.inc _ θ)} ≤
    Submodule.span (Kp X la G.N) (Set.range (zK G la))

def InContainM (G : GlobalFamilyData X ka wL wF) (la : HeightOneSpectrum (𝓞 B.KO)) (CRm : ℝ) (T : ℕ) (c : ℝ) : Prop :=
  Submodule.span (Kp X la G.N) ((fun F => emb X la G.N (X.inc ka F)) '' (WeightFamilies.MggK B CRm T c j ka : Set (B.Cusp j ka))) ≤
    Submodule.span (Kp X la G.N)
      ({v | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
          v = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))} ∪
       Set.range (zK G la))

def Conclusion1OfComb : Prop :=
  ∀ (large₂ : SizeData₂ D) (X : Prov D B P) (K : KAdm) (H : KHyp) (Ch Ah Cq Aq C2 A2 CR CT : ℝ),
    ∀ j (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) (S : Scal B) (ka wL wF : WeightFamilies.Wt D j) (T nP nW : ℕ) (h0 : ℝ)
      (nus : HeightOneSpectrum (𝓞 B.KO) → ℝ),
    HypC large₂ (X j h1 h2) H C2 A2 CR 0 CT S ka wL wF T nP nW h0 nus →
    LatAt B j ka → SupBoundByL2AtWeight large₂ B j ka K.CG K.AG → LAMwAt large₂ B j ka K.CL K.AL →
    (j < D.R.m → QAt large₂ B j ka K.CRm H.CK Ch Ah Cq Aq T (cc D large₂ C2 A2 CR wL)) →
    ∀ (G : GlobalFamilyData (X j h1 h2) ka wL wF) (Gc PH Prw Pet Pd : ℝ) (Qf : ∀ la, LocalPointData G la),
    G.TiedW S Gc Prw → G.TiedTh S Gc → G.TiedZ S T Gc →
    G.TiedQ large₂ S K.CRm T (cc D large₂ C2 A2 CR wL) Ch Ah → G.TiedEt large₂ K.Cf K.Af →
    DeepHerm (X j h1 h2) ka → DeepSubMul (X j h1 h2) → DeepLogD (X j h1 h2) ka Pd →
    PageGd (X j h1 h2) ka large₂ K.CG K.AG Pd →
    ShareRd (D := D) (j := j) T G.del ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRho (D := D) (j := j) T G.rz ((X j h1 h2).rk ka (B.Mlat j ka)) →
    ShareRhoP (D := D) (j := j) T G.rq ((X j h1 h2).rk ka (B.Mlat j ka)) →
    PolyDom (j := j) D B large₂ K H C2 A2 CR Ch Ah Cq Aq Gc PH Prw Pet Pd ka →
    (∀ la, InBasis G la) → (∀ la, (Qf la).InCurve) → (∀ la, (Qf la).InTie S) → (∀ la, (Qf la).InLiftC S Gc Prw T) →
    (∀ la, InContainZ G la S T) → (∀ la, InContainM G la K.CRm T (cc D large₂ C2 A2 CR wL)) →
    CombBound G S (cc D large₂ C2 A2 CR wL) nus →
    Heights Qf Gc PH Prw Pet →
    Concl (X j h1 h2) S ka wL wF T nus
      ((X j h1 h2).rk ka (B.Mlat j ka) * D.R.f * D.R.m * large₂.sc.b * large₂.de2)

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

