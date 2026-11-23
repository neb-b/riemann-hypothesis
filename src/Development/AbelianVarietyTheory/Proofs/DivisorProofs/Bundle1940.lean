module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0536
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1855
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0779
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowEqSpan
public import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1876
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0027
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToricPeriodBlockIsSymm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1863
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalisedModelUniformisationBaseChange
public import Development.AbelianVarietyTheory.Definitions.ArchimedeanThetaValues.IsThetaL2NormSquared
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0007

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedLevelPointsOfLattice
section
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR

noncomputable section

namespace GlobalTheory.TraitArc

open GlobalTheory.TauTwist

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
  {T : CDVR} (D : DegData T.V (maximalIdeal T.V)) [Module (𝓞 E) D.toPre.X]
  (oD : letI := H.starRing; D.toPre.OAct (𝓞 E)) {ϖ : T.V} (hϖ : Irreducible ϖ)

def qv : D.toPre.X → ℤ := fun χ => (QForm.exists_QVal hϖ D χ).choose

theorem isQ_qv : QForm.IsQ D.toPre ϖ (qv D hϖ) := fun χ => (QForm.exists_QVal hϖ D χ).choose_spec

def beF : LinearMap.BilinForm ℤ D.toPre.X :=
  LinearMap.mk₂ ℤ (fun a b => QForm.bHom hϖ D (isQ_qv D hϖ) a b)
    (fun a a' b => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])
    (fun a b b' => by simp [map_add (f := _)]) (fun n a b => by simp [map_zsmul])

theorem beF_symm (a b : D.toPre.X) : beF D hϖ a b = beF D hϖ b a := QForm.bOf_comm D a b

theorem beF_self (a : D.toPre.X) : beF D hϖ a a = 2 * qv D hϖ a :=
  (QForm.two_Q_eq hϖ D (isQ_qv D hϖ) a).symm

theorem beF_pos {a : D.toPre.X} (ha : a ≠ 0) : 0 < beF D hϖ a a := by
  have := QForm.Q_pos hϖ D (isQ_qv D hϖ) ha
  rw [beF_self]; omega

include oD in
theorem beF_adj (x : 𝓞 E) (a b : D.toPre.X) : beF D hϖ (x • a) b = beF D hϖ a (H.bar x • b) :=
  letI := H.starRing
  QForm.bOf_balance hϖ D GlobalTheory.abelianSchemeLaws_all.1 oD (isQ_qv D hϖ) x a b

include oD in
theorem beF_w0 (a : D.toPre.X) : beF D hϖ a (H.w0 • a) = qv D hϖ a := by
  have h₁ := beF_adj D oD hϖ H.w0 a a
  have hb : H.bar H.w0 = 1 - H.w0 := by rw [HostModel.cmHost_bar_halfIntegerGenerator]
  rw [hb, sub_smul, one_smul, map_sub, beF_symm D hϖ (H.w0 • a) a] at h₁
  have h₂ := beF_self D hϖ a
  omega

def tF (a b : D.toPre.X) : (FractionRing T.V)ˣ := GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a b))

include oD in
theorem isScalarForm_tF : letI := H.starRing; IsScalarForm (𝓞 E) (tF D hϖ) := by
  letI := H.starRing
  refine ⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩
  · simp only [tF, map_add (f := _), neg_add, zpow_add]
  · rw [tF, tF, beF_symm]
  · rw [tF, tF, beF_adj D oD]; rfl

abbrev D0 : DegPre T.V := letI := H.starRing; GlobalTheory.TauTwist.twist D.toPre H.w0 (tF D hϖ)

def oa0 : letI := H.starRing; (D0 (H := H) D hϖ).OAct (𝓞 E) :=
  letI := H.starRing; twistAct (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) oD


include oD in
theorem gen0 (a : D.toPre.X) : PsiUnitOn (D0 (H := H) D hϖ) a Set.univ :=
  psiUnitOn_rescale_of_qVal T D.toPre ϖ hϖ a (qv D hϖ a) (isQ_qv D hϖ a) _ (by
    show ((GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a (H.w0 • a))) : (FractionRing T.V)ˣ) : FractionRing T.V) = _
    rw [beF_w0 D oD, Units.val_zpow_eq_zpow_val]; rfl)

def rF (k : ℕ) (a b : D.toPre.X) : (FractionRing T.V)ˣ := GlobalTheory.ArcBuild.piK hϖ ^ (-(beF D hϖ a b / k))

include oD in
theorem isRootForm_rF {k : ℕ} (hk : ∀ a b, (k : ℤ) ∣ beF D hϖ a b) :
    letI := H.starRing; IsRootForm (𝓞 E) k (tF D hϖ) (rF D hϖ k) := by
  letI := H.starRing
  refine ⟨⟨fun a b b' => ?_, fun a b => ?_, fun x a b => ?_⟩, fun a b => ?_⟩
  · simp only [rF, map_add (f := _)]
    rw [Int.add_ediv_of_dvd_left (hk a b), neg_add, zpow_add]
  · rw [rF, rF, beF_symm]
  · rw [rF, rF, beF_adj D oD]; rfl
  · rw [rF, tF, ← zpow_natCast, ← zpow_mul, neg_mul, Int.ediv_mul_cancel (hk a b)]
    ext; simp

theorem psiRel0 : letI := H.starRing; PsiRel D.toPre (D0 (H := H) D hϖ).psi fun y => tF D hϖ y (H.w0 • y) :=
  psiRel_rescale _ _

section ThetaShiftProofs

variable {Dm : Datum H} {l : Level H} {c : Coeff l} {O : Type} [CommRing O] (β : O →+* c.F) (b : O →+* T.V)

theorem dvd_of_dvd {k : ℕ} (hk : k ∣ l.M') (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (a a' : D.toPre.X) :
    (k : ℤ) ∣ beF D hϖ a a' :=
  (Int.natCast_dvd_natCast.2 hk).trans ((dvd_mul_left _ _).trans (hdiv a a'))

def twistedLevelPointsOfLattice (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (v : Dm.La) : QkPt (D0 (H := H) D hϖ) (FractionRing T.V) l.A :=
  letI := H.starRing
  qkScale (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) (psiRel0 D hϖ)
    (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (Nat.dvd_lcm_right l.M l.A) hdiv)) _ (pA v)

def eta0 (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M)
    (v : Dm.La) : QkPt (D0 (H := H) D hϖ) (FractionRing T.V) l.M :=
  letI := H.starRing
  qkScale (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) (psiRel0 D hϖ)
    (isRootForm_rF D oD hϖ (dvd_of_dvd D hϖ (Nat.dvd_lcm_left l.M l.A) hdiv)) _ (pM v)


open scoped Classical in
variable (Dm) in
def LieCl : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (r : O), ((β r : c.F) : ℂ) = H.rt0 →
    ∀ τ : 𝓞 E →+* F, ∃ n, LieMult (ofRingAct oD.onB.toRingAct)
      (spMap ((algebraMap (FractionRing T.V) F).comp (algebraMap T.V _))) τ n ∧
      n + Module.finrank (𝓞 E) D.toPre.X =
        if τ H.rt = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b r) then Dm.p else Dm.q


variable (Dm) in
def TateCl (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) : Prop :=
  letI := H.starRing
  ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing T.V) F] (z : O), ((β z : c.F) : ℂ) = zeta l.A →
    ∃ I : TateIsoQ Dm (D0 (H := H) D hϖ) (oa0 D oD hϖ) F,
      (I.ζ l.A : F) = (algebraMap (FractionRing T.V) F).comp (algebraMap T.V _) (b z) ∧
      (∀ a q, QkExt (algebraMap _ F) (twistedLevelPointsOfLattice D oD hϖ hdiv pA a) q → Out.QkPt.Equiv (D0 (H := H) D hϖ) F q (I.ev l.A a)) ∧
      ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) Dm.La), ∀ q,
        QkExt (algebraMap _ F) (eta0 D oD hϖ hdiv pM a) q → Out.QkPt.Equiv (D0 (H := H) D hϖ) F q (I.ev l.M a)

def arc (hX : Nontrivial D.toPre.X) (hw : letI := H.starRing; TraceFormTwistIso D.toPre oD H.w0)
    (hdiv : ∀ a a', (2 * l.M' : ℤ) ∣ beF D hϖ a a') (pA : Dm.La → QkPt D.toPre (FractionRing T.V) l.A)
    (pM : Dm.La → QkPt D.toPre (FractionRing T.V) l.M) (hLie : LieCl D oD Dm β b)
    (hTate : TateCl D oD hϖ Dm β b hdiv pA pM) : ArcIn Dm l β T.V b :=
  letI := H.starRing
  { D₀ := D0 D hϖ
    oa := oa0 D oD hϖ
    nontriv := hX
    even := psiEven_twist (isScalarForm_tF D oD hϖ) H.w0 D.psi_even
    bimult := tauBimult_twist (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) D.tau_bimult
    gen := gen0 D oD hϖ
    w0 := psi_weight_zero_twist (GlobalTheory.ArcBuild.cmIdempotent_add_star_eq_one (H := H)) (isScalarForm_tF D oD hϖ) hw
    be := beF D hϖ
    be_symm := beF_symm D hϖ
    be_pos := fun a ha => beF_pos D hϖ ha
    be_adj := beF_adj D oD hϖ
    be_dvd := hdiv
    eta := eta0 D oD hϖ hdiv pM
    etaA := twistedLevelPointsOfLattice D oD hϖ hdiv pA
    geom := fun F _ _ _ r z hr hz f hf => by
      subst hf
      obtain ⟨I, h₁, h₂, h₃⟩ := hTate F z hz
      exact ⟨hLie F r hr, I, h₁, h₂, h₃⟩ }

end ThetaShiftProofs

end GlobalTheory.TraitArc
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSplittingCharacterUnitOffPlaces
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR
open Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ConjTwist GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.OnTies GlobalTheory.OnCmp GlobalTheory.BaseCmp
open Formalism.IndefR.Fin Formalism.IndefR.Fin.LevelGroupLemmas
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.DilChi
open GlobalTheory.ChiUnit

theorem natCast_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (m : ℕ) :
    (m : 𝓞 E) ∈ (conjPl P).asIdeal ↔ (m : 𝓞 E) ∈ P.asIdeal := by
  show Formalism.L2.DIV.starOHom (m : 𝓞 E) ∈ P.asIdeal ↔ _
  rw [map_natCast]

theorem conjO_mem_conjPl {E : Type} [Field E] [NumberField E] [StarRing E] (P : Pl E) (a : 𝓞 E) :
    Formalism.L2.DIV.starO a ∈ (conjPl P).asIdeal ↔ a ∈ P.asIdeal := by
  show Formalism.L2.DIV.starO (Formalism.L2.DIV.starO a) ∈ P.asIdeal ↔ _
  rw [Formalism.L2.DIV.starO_starO]

theorem conjO_not_mem_sq {E : Type} [Field E] [NumberField E] [StarRing E] {P : Pl E} {a : 𝓞 E}
    (h : a ∉ P.asIdeal ^ 2) : Formalism.L2.DIV.starO a ∉ (conjPl P).asIdeal ^ 2 := by
  intro ha
  apply h
  have h1 : Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) ∈ Ideal.map Formalism.L2.DIV.starOHom ((conjPl P).asIdeal ^ 2) := Ideal.mem_map_of_mem _ ha
  rw [Ideal.map_pow] at h1
  have h2 : Ideal.map Formalism.L2.DIV.starOHom (conjPl P).asIdeal ≤ P.asIdeal := Ideal.map_comap_le
  have h3 := Ideal.pow_right_mono h2 2 h1
  rwa [show Formalism.L2.DIV.starOHom (Formalism.L2.DIV.starO a) = a from Formalism.L2.DIV.starO_starO a] at h3

theorem natCard_mem {E : Type} [Field E] [NumberField E] (P : Pl E) (h : Nat.card (kP P) ≠ 0) :
    ((Nat.card (kP P) : ℕ) : 𝓞 E) ∈ P.asIdeal := by
  haveI : Finite (kP P) := Nat.finite_of_card_ne_zero h
  letI := Fintype.ofFinite (kP P)
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, Nat.card_eq_fintype_card]
  exact Nat.cast_card_eq_zero (kP P)

theorem units_mul_relation_rearrange_commRing {Rg : Type*} [CommRing Rg] (c e i s : Rg) (n : ℕ) (hc2 : c * c = c) (hce : c * e = 0) :
    c * (e * i + c * s + (1 - e - c)) ^ n + (1 - c) = 1 + c * (s ^ n - 1) := by
  have hca : c * (e * i + c * s + (1 - e - c)) = c * s := by
    linear_combination (i - 1) * hce + (s - 1) * hc2
  have hpow : ∀ m : ℕ, c * (e * i + c * s + (1 - e - c)) ^ m = c * s ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      calc c * (e * i + c * s + (1 - e - c)) ^ (m + 1) = (c * (e * i + c * s + (1 - e - c)) ^ m) * (e * i + c * s + (1 - e - c)) := by ring
        _ = s ^ m * (c * (e * i + c * s + (1 - e - c))) := by rw [ih]; ring
        _ = c * s ^ (m + 1) := by rw [hca]; ring
  linear_combination hpow n

theorem detIdele_eq_locE (D : D7) (V : HSp D) (Q : Finset (Pl D.host.E)) (eQ : AE D) (heQ : IsIdemSum eQ Q)
    (ϖ : D.host.E) (z : GA D V)
    (hz : mt V z = Matrix.diagonal (fun _ => eQ * incA D ϖ⁻¹ + cA D eQ * cA D (incA D ϖ) + (1 - eQ - cA D eQ)))
    (x : (AE D)ˣ) (hx : IsDetAt (cA D eQ) V z x) :
    (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (star ϖ ^ V.rank) := by
  have he : eQ * eQ = eQ := by
    classical
    obtain ⟨es, hes, hsum, horth⟩ := Formalism.IndefR.Fin.idemSum_orth Q eQ heQ
    rw [hsum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.sum_eq_single i (fun j hj hji => (horth i hi j hj (Ne.symm hji)).1) (fun h => absurd hi h)]
    exact (hes i hi).1
  have hc2 : cA D eQ * cA D eQ = cA D eQ := by rw [← map_mul, he]
  have hce : cA D eQ * eQ = 0 := by rw [mul_comm]; exact heQ.2
  have hs : incA D (star ϖ) = cA D (incA D ϖ) := rfl
  rw [hx, hz, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  unfold Formalism.L2.JoinChr.locE
  rw [map_pow, hs]
  exact units_mul_relation_rearrange_commRing _ _ _ _ V.rank hc2 hce

theorem chi_unitOff : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.Hk3.Core R F → QGuard R → ∀ (i : Fin D.R.m), VStd D i → ∀ (ξ : Formalism.L2.Host.HChar D.host.E) (χ : (AE D)ˣ →* Circle) (ξR : ∀ PP : Pl D.host.E, (kP PP)ˣ →* ℂˣ) (Q : Finset (Pl D.host.E)) (ω : WeilRep D i) (φ : WO (Vc D i) (Wc D i) → ℂ), KerDat R i ξ χ ξR Q ω φ → (∃ t, Q ⊆ R.Q t) → ∀ N : ℕ, N ≠ 0 → (∀ PP ∈ Q, (N : 𝓞 D.host.E) ∈ PP.asIdeal) → ∀ eQ : AE D, IsIdemSum eQ Q → ∀ ϖ : 𝓞 D.host.E, (ϖ : D.host.E) ≠ 0 → (∀ PP ∈ Q, ϖ ∈ PP.asIdeal ∧ ϖ ∉ PP.asIdeal ^ 2) → ∀ z : GA D (Vc D i), mt (Vc D i) z = Matrix.diagonal (fun _ => eQ * incA D ((ϖ : D.host.E)⁻¹) + cA D eQ * cA D (incA D (ϖ : D.host.E)) + (1 - eQ - cA D eQ)) → ∀ x : (AE D)ˣ, IsDetAt (cA D eQ) (Vc D i) z x → UnitOff N ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ))⁻¹ := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R F hC hQG i hV ξ χ ξR Q ω φ hK hQt N hN hNQ eQ heQ ϖ hϖ0 hϖ z hz x hx
  show GlobalTheory.IndefiniteRowSideFullHecke.CentralInvolutionRing.UnitOff N _
  have hlev := hC.lev
  have hs0 : star ((ϖ : 𝓞 D.host.E) : D.host.E) ≠ 0 := by simpa using hϖ0
  set u : D.host.Eˣ := Units.mk0 _ hs0 with hu
  have hxl : (x : AE D) = Formalism.L2.JoinChr.locE D (cA D eQ) (((u ^ (Vc D i).rank : D.host.Eˣ)) : D.host.E) := by
    rw [detIdele_eq_locE D (Vc D i) Q eQ heQ _ z hz x hx, Units.val_pow_eq_pow_val]; rfl
  have hval : ∀ (c : (AE D)ˣ →* Circle) (ψ : Formalism.L2.Host.HChar D.host.E), ChrEq c ψ →
      ((c x : Circle) : ℂ) = ∏ P ∈ Q, (((ψ.locK (conjPl P) u : ℂˣ) : ℂ)) ^ (Vc D i).rank := by
    intro c ψ hc
    rw [_root_.GlobalTheory.IdemSumChar.char_eq_prod D Q eQ heQ (u ^ (Vc D i).rank) x hxl c ψ hc]
    refine Finset.prod_congr rfl fun P _ => ?_
    rw [map_pow, Units.val_pow_eq_pow_val]
  have e : ((((Lift.chrTh (Lift.tup R.mu0 χ) R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)) =
      (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ)) * (((χ x : Circle) : ℂ)) * (((R.eta x : Circle) : ℂ))⁻¹ := by
    simp only [Lift.chrTh, Lift.tup, MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]
  rw [e, hval _ _ (hlev.mu0 i), hval _ _ hK.chr, hval _ _ hlev.eta]
  have hb : ∀ P ∈ Q, Formalism.L2.DIV.starO ϖ ∈ (conjPl P).asIdeal ∧ Formalism.L2.DIV.starO ϖ ∉ (conjPl P).asIdeal ^ 2 := fun P hP =>
    ⟨(conjO_mem_conjPl P ϖ).2 (hϖ P hP).1, conjO_not_mem_sq (hϖ P hP).2⟩
  have hNc : ∀ P ∈ Q, (N : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := fun P hP => (natCast_mem_conjPl P N).2 (hNQ P hP)
  have hunr : ∀ P ∈ Q, (R.C.mu0 i).UnrAt (conjPl P) := fun P hP => by
    obtain ⟨⟨q, hq, hqc, -, hqg⟩, -⟩ := hK.pl P hP
    have hqm : (q : 𝓞 D.host.E) ∈ (conjPl P).asIdeal := by
      rw [natCast_mem_conjPl, ← hqc]; exact natCard_mem P (by rw [hqc]; exact hq.ne_zero)
    exact (R.C.isMu0 i).unr (conjPl P) fun k hk =>
      not_mem_of_prime_ne (conjPl P) (D.host.g_prime k) hq (hqg k) hqm hk
  have hcoe : (u : D.host.E) = ((Formalism.L2.DIV.starO ϖ : 𝓞 D.host.E) : D.host.E) := by rw [Formalism.L2.DIV.starO_coe]; rfl
  obtain ⟨nμ, -, hnμ⟩ := (R.C.isMu0 i).inf
  obtain ⟨n, hn, hnx⟩ := hK.fin
  refine unitOff_inv (unitOff_mul (unitOff_mul (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)
    (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)) (unitOff_inv (unitOff_prod _ _ fun P hP => unitOff_pow ?_ _)))
  · rw [locK_eq_val _ (hunr P hP) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ nμ (conjPl P) _ hnμ (finite_ramified_places_hecke_character _ (R.C.isMu0 i).unr)
      (R.C.isMu0 i).tame (hunr P hP) (hNc P hP)
  · refine unitOff_of_pow_eq_one _ hn ?_
    have h := LR ξ n hnx (conjPl P) u
    rw [← Units.val_pow_eq_pow_val, h, Units.val_one]
  · rw [locK_eq_val _ (R.C.isEta.unr (conjPl P)) u _ hcoe (hb P hP).1 (hb P hP).2]
    exact GlobalTheory.ValUnit.unitOff_val _ _ _ _ _ (conjPl P) _ R.C.isEta.inf
      (Set.Finite.subset Set.finite_empty fun w hw => hw (R.C.isEta.unr w)) (fun w y hy _ => R.C.isEta.unr w y hy)
      (R.C.isEta.unr (conjPl P)) (hNc P hP)

end GlobalTheory.DilChi
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValRPush
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open GlobalTheory GlobalTheory.LieHt GlobalTheory.Cartier GlobalTheory.ThetaOnto GlobalTheory.KeyCl GlobalTheory.Ex GlobalTheory.MBLow GlobalTheory.SecJet
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.MBLow.Cl Matrix

noncomputable section

namespace GlobalTheory.MBLow.Cl.DZero

theorem valR_push {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) {X : Scheme.{0}} (x : Sp A ⟶ X) (U : X.Opens)
    (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(X, U)) : valR (spMap φ ≫ x) U f = φ (valR x U f) := by
  have h' : ⊤ ≤ (spMap φ ≫ x) ⁻¹ᵁ U := fun p _ => h (Set.mem_univ _)
  rw [valR, valR, dite_eq_left h, dite_eq_left h']
  have e1 : (spMap φ ≫ x).appLE U ⊤ h' = x.appLE U ⊤ h ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    exact (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  rw [e1]
  exact congrArg (fun k => k.hom ((x.appLE U ⊤ h).hom f)) e2

theorem isD_zero : AllC fun {R} _ _ {D} _ {N} ν => ∀ (g : ℕ) (d : AB N.toNumB g), IsD ν d 0 (DegPre.zeroT D (TE R ℂ)) := by
  intro R _ _ _ _ D _ _ _ N ν g d U f hU
  have h0 : d.ex 0 = 1 := by
    have := d.ex_add 0 0
    rw [add_zero] at this
    exact left_eq_mul.1 this
  have e : (lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
      (DegPre.zeroT D (TE R ℂ))).left = spMap (algebraMap ℂ (DualNumber ℂ)) ≫ ptB ν d 0 := by
    have : lift (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ)
        (DegPre.zeroT D (TE R ℂ)) =
        (Over.homMk (spMap (algebraMap ℂ (DualNumber ℂ))) rfl : TE R ℂ ⟶ TF (R := R) ℂ) ≫
          lift (𝟙 (TF (R := R) ℂ)) (ν.eA (d.ex 0)) := by
      rw [comp_lift, Category.comp_id, h0, map_one, Hom.one_def, ← Category.assoc, comp_toUnit]
    rw [this, Over.comp_left]
    rfl
  rw [e, valR_push _ _ _ hU, map_zero, TrivSqZeroExt.inr_zero, add_zero]
  rfl

end GlobalTheory.MBLow.Cl.DZero

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationSubringDedekindOpenImmersion
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.CoeffValuation

theorem mem_of_forall_natCast {L : Type} [Field L] [NumberField L] (W : ValuationSubring L)
    (h : ∀ n : ℕ, n ≠ 0 → (n : L) ∉ W.nonunits) (x : L) : x ∈ W := by
  have halg : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ L).mpr (Algebra.IsAlgebraic.isAlgebraic x)
  obtain ⟨m, hm, hint⟩ := halg.exists_integral_multiple
  have h1 : m • x ∈ W := by
    have h : IsIntegral W (m • x) := hint.tower_top
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := W) (K := L)).mp h
    exact hy ▸ y.2
  have h2 : ((m.natAbs : ℕ) : L)⁻¹ ∈ W := by
    have := h m.natAbs (Int.natAbs_ne_zero.mpr hm)
    rw [ValuationSubring.mem_nonunits_iff_or] at this
    by_contra hc
    exact this (Or.inr hc)
  have hm' : (m : L) ≠ 0 := Int.cast_ne_zero.mpr hm
  have h3 : (m : L)⁻¹ ∈ W := by
    rcases Int.natAbs_eq m with e | e
    · rw [e, Int.cast_natCast]; exact h2
    · rw [e, Int.cast_neg, Int.cast_natCast, inv_neg]; exact W.neg_mem _ h2
  have : x = (m : L)⁻¹ * (m • x) := by
    rw [zsmul_eq_mul, inv_mul_cancel_left₀ hm']
  rw [this]
  exact W.mul_mem _ _ h3 h1

theorem dedekind_and_away {L : Type} [Field L] [NumberField L] (W : ValuationSubring L) :
    IsDedekindDomain W ∧ ∃ π : W, IsLocalization.Away π L := by
  by_cases h : ∃ n : ℕ, n ≠ 0 ∧ (n : L) ∈ W.nonunits
  · obtain ⟨n, hn, hW⟩ := h
    have := (GlobalTheory.isDiscreteValuationRing_and_finite_residueField_of_numberField W hn hW).1
    refine ⟨inferInstance, ?_⟩
    obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible W
    refine ⟨π, ?_⟩
    refine (isLocalization_iff _ _).mpr ⟨?_, ?_, ?_⟩
    · rintro ⟨_, k, rfl⟩
      exact IsUnit.mk0 _ ((map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr (pow_ne_zero k hπ.ne_zero))
    · intro z
      obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := W) z
      have hb0 : b ≠ 0 := nonZeroDivisors.ne_zero hb
      obtain ⟨k, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hb0 hπ
      refine ⟨⟨a * (u⁻¹ : Wˣ), ⟨π ^ k, k, rfl⟩⟩, ?_⟩
      have hb1 : algebraMap W L (u * π ^ k) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective W L)).mpr hb0
      rw [div_mul_eq_mul_div, div_eq_iff hb1, ← map_mul, ← map_mul]
      congr 1
      rw [mul_assoc, Units.inv_mul_cancel_left]
    · intro a b hab
      exact ⟨1, by rw [IsFractionRing.injective W L hab]⟩
  · have hall : ∀ x : L, x ∈ W := mem_of_forall_natCast W fun n hn hW => h ⟨n, hn, hW⟩
    have hbij : Function.Bijective (algebraMap W L) :=
      ⟨IsFractionRing.injective W L, fun x => ⟨⟨x, hall x⟩, rfl⟩⟩
    have hF : IsField W := (RingEquiv.ofBijective _ hbij).toMulEquiv.isField (Field.toIsField L)
    have : IsPrincipalIdealRing W := hF.isPrincipalIdealRing
    exact ⟨inferInstance, 1, IsLocalization.away_of_isUnit_of_bijective L isUnit_one hbij⟩

theorem isDedFrac_and_isOpenImmersion : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (l : Level H) (c : Coeff l) (W : ValuationSubring c.F), GlobalTheory.Models.IsDedFrac W.subtype ∧ IsOpenImmersion (spMap W.subtype) := by
  intro E _ _ _ H l c W
  have := c.fin
  have : NumberField c.F := NumberField.mk
  obtain ⟨hD, π, hπ⟩ := dedekind_and_away W
  exact ⟨⟨⟨inferInstance, hD⟩, inferInstance, (inferInstance : IsFractionRing W c.F)⟩,
    IsOpenImmersion.of_isLocalization (S := c.F) π⟩

end GlobalTheory.CoeffValuation
end

