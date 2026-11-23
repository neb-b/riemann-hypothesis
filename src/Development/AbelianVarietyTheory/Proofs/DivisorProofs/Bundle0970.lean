module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.AevalEqZeroOfMemConeIdeal
public import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsAlgebraicIndependentGenericPoint
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ProjPointIdealMemProjComponentsOfIsProjPureDim
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFormDegreeLeHilbertDegreeEvalNeZero
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LeadingCoeffNonnegOfEventuallyEvalNat
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0018
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0033
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0160
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0932
public import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupOfEventuallyPolynomial
section
set_option autoImplicit false

namespace GlobalTheory.CompHt

open Filter Topology
open scoped ENNReal

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma factorial_mul_div_pow_ennreal_eq_ofReal (D k m : ℕ) (hk : 1 ≤ k) :
    (D.factorial : ℝ≥0∞) * ((m : ℕ∞) : ℝ≥0∞) / (k : ℝ≥0∞) ^ D =
      ENNReal.ofReal ((D.factorial : ℝ) * (m : ℝ) / (k : ℝ) ^ D) := by
  have hk' : (0 : ℝ) < (k : ℝ) ^ D := by
    have : (0 : ℝ) < k := by exact_mod_cast hk
    positivity
  rw [ENNReal.ofReal_div_of_pos hk', ENNReal.ofReal_mul (by positivity),
    ENNReal.ofReal_pow (by positivity)]
  simp

set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
private lemma tendsto_eval_div_pow_atTop_coeff_of_degree_le (Q : Polynomial ℝ) (D : ℕ) (hQ : Q.degree ≤ D) :
    Tendsto (fun y : ℝ => Q.eval y / y ^ D) atTop (𝓝 (Q.coeff D)) := by
  have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
  rcases hQ.lt_or_eq with hlt | heq
  · have hc : Q.coeff D = 0 := Polynomial.coeff_eq_zero_of_degree_lt hlt
    rw [hc]
    simpa using Polynomial.div_tendsto_atTop_zero_of_degree_lt (P := Q) (Q := Polynomial.X ^ D) (by rw [hX]; exact hlt)
  · have hc : Q.leadingCoeff = Q.coeff D := by
      rw [Polynomial.leadingCoeff, Polynomial.natDegree_eq_of_degree_eq_some heq]
    have := Polynomial.div_tendsto_atTop_leadingCoeff_div_of_degree_eq (P := Q) (Q := Polynomial.X ^ D) (by rw [hX, heq])
    simpa [hc] using this


set_option autoImplicit false in
open Filter Topology in
open scoped ENNReal in
theorem _root_.GlobalTheory.CompHt.growth_of_eventually_eq_eval :
    ∀ (D a : ℕ) (h : ℕ → ℕ) (H : Polynomial ℚ), 1 ≤ a → (∀ᶠ n : ℕ in atTop, (h n : ℚ) = H.eval (n : ℚ)) →
      (H.degree ≤ D → ∀ δ : ℕ, (δ : ℚ) = (D.factorial : ℚ) * H.coeff D →
        _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = (a : ℝ≥0∞) ^ D * δ) ∧
      ((D : WithBot ℕ) < H.degree → _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = ⊤) := by
  intro D a h H ha hev
  set Q : Polynomial ℝ := H.map (algebraMap ℚ ℝ) with hQdef
  have hQdeg : Q.degree = H.degree := Polynomial.degree_map _ _

  have hak : Tendsto (fun k : ℕ => a * k) atTop atTop :=
    tendsto_atTop_mono (fun k => Nat.le_mul_of_pos_left k ha) tendsto_id
  have hakR : Tendsto (fun k : ℕ => ((a * k : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hak

  have hval : ∀ᶠ k : ℕ in atTop, (h (a * k) : ℝ) = Q.eval ((a * k : ℕ) : ℝ) := by
    filter_upwards [hak.eventually hev] with k hk
    have hcast : ((a * k : ℕ) : ℝ) = algebraMap ℚ ℝ ((a * k : ℕ) : ℚ) := by simp
    rw [hQdef, Polynomial.eval_map, hcast, Polynomial.eval₂_at_apply, ← hk]
    simp

  set g : ℕ → ℝ := fun k => (D.factorial : ℝ) * (h (a * k) : ℝ) / (k : ℝ) ^ D with hg
  have hg_eq : ∀ᶠ k : ℕ in atTop, g k = (D.factorial : ℝ) * (a : ℝ) ^ D *
      (Q.eval ((a * k : ℕ) : ℝ) / ((a * k : ℕ) : ℝ) ^ D) := by
    filter_upwards [hval, eventually_ge_atTop 1] with k hk hk1
    have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
    have ha0 : (a : ℝ) ≠ 0 := by exact_mod_cast (show a ≠ 0 by omega)
    simp only [hg]
    rw [hk]
    push_cast
    field_simp
    ring
  have hlim : _root_.GlobalTheory.CompHt.growth D (fun k => (h (a * k) : ℕ∞)) = limsup (fun k => ENNReal.ofReal (g k)) atTop := by
    unfold _root_.GlobalTheory.CompHt.growth
    refine limsup_congr ?_
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact factorial_mul_div_pow_ennreal_eq_ofReal D k (h (a * k)) hk
  refine ⟨fun hdeg δ hδ => ?_, fun hdeg => ?_⟩
  · have hT : Tendsto g atTop (𝓝 ((D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D)) := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      exact ((tendsto_eval_div_pow_atTop_coeff_of_degree_le Q D (hQdeg ▸ hdeg)).comp hakR).const_mul _
    rw [hlim, (ENNReal.tendsto_ofReal hT).limsup_eq]
    have hc : (D.factorial : ℝ) * (a : ℝ) ^ D * Q.coeff D = ((a ^ D * δ : ℕ) : ℝ) := by
      rw [hQdef, Polynomial.coeff_map]
      have : ((δ : ℚ) : ℝ) = ((D.factorial : ℚ) * H.coeff D : ℚ) := by rw [hδ]
      push_cast at this ⊢
      rw [this]
      simp only [eq_ratCast]
      ring
    rw [hc, ENNReal.ofReal_natCast]
    push_cast
    rfl
  · have hQdeg' : (D : WithBot ℕ) < Q.degree := hQdeg ▸ hdeg
    have hX : (Polynomial.X ^ D : Polynomial ℝ).degree = D := by simp
    have hlc : 0 < Q.leadingCoeff := by
      by_contra hneg
      push_neg at hneg
      have hpos : 0 < Q.degree := lt_of_le_of_lt (by exact_mod_cast Nat.zero_le D) hQdeg'
      have hbot := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos hpos hneg).comp hakR
      have hneg' := hbot.eventually (eventually_lt_atBot (0 : ℝ))
      obtain ⟨k, hk1, hk2⟩ := (hneg'.and hval).exists
      simp only [Function.comp_apply] at hk1
      rw [← hk2] at hk1
      exact absurd hk1 (not_lt.2 (Nat.cast_nonneg _))
    have hT : Tendsto g atTop atTop := by
      refine Tendsto.congr' (EventuallyEq.symm hg_eq) ?_
      refine Tendsto.const_mul_atTop (by positivity) ?_
      refine (Polynomial.div_tendsto_atTop_of_degree_gt (P := Q) (Q := Polynomial.X ^ D) (by rw [hX]; exact hQdeg')
        (by simp) ?_).comp hakR |>.congr fun k => by simp
      simpa using hlc.le
    rw [hlim]
    exact (ENNReal.tendsto_ofReal_atTop.comp hT).limsup_eq

end GlobalTheory.CompHt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankGrowthLimsupShiftLe
section
set_option autoImplicit false

open MvPolynomial GlobalTheory.ChowHt GlobalTheory.CompHt Filter
open scoped ENNReal Topology

namespace GlobalTheory.GrowthShift

theorem eventually_mul_inv_pow_le (D e : ℕ) {a : ℝ≥0∞} (ha : a < 1) :
    ∀ᶠ k : ℕ in atTop, a * ((k : ℝ≥0∞) ^ D)⁻¹ ≤ (((k + e : ℕ) : ℝ≥0∞) ^ D)⁻¹ := by
  lift a to NNReal using ha.ne_top
  have ha' : (a : ℝ) < 1 := by exact_mod_cast ha
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) / (k + (e : ℝ))) ^ D) atTop (𝓝 1) := by
    simpa using (tendsto_natCast_div_add_atTop (e : ℝ)).pow D
  filter_upwards [h1.eventually (lt_mem_nhds ha'), eventually_gt_atTop 0] with k hk hk0
  have hkR : (0 : ℝ) < k := Nat.cast_pos.2 hk0
  have hke : (0 : ℝ) < ((k : ℝ) + e) ^ D := by positivity
  rw [div_pow, lt_div_iff₀ hke] at hk
  have h2 : (a : ℝ≥0∞) * ((k + e : ℕ) : ℝ≥0∞) ^ D ≤ (k : ℝ≥0∞) ^ D := by
    have h3 : a * ((k + e : ℕ) : NNReal) ^ D ≤ (k : NNReal) ^ D := by
      rw [← NNReal.coe_le_coe]
      push_cast
      exact hk.le
    exact_mod_cast h3
  have n0 : (k : ℝ≥0∞) ^ D ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 hk0.ne')
  have nt : (k : ℝ≥0∞) ^ D ≠ ⊤ := ENNReal.pow_ne_top (ENNReal.natCast_ne_top k)
  rw [ENNReal.le_inv_iff_mul_le, mul_right_comm, ← div_eq_mul_inv, ENNReal.div_le_iff n0 nt, one_mul]
  exact h2

theorem growth_shift_le : ∀ (D e : ℕ) (r : ℕ → ℕ∞), growth D (fun k => r (k + e)) ≤ growth D r := by
  intro D e r
  refine ENNReal.le_of_forall_lt_one_mul_le fun a ha => ?_
  rw [growth, growth, ← ENNReal.limsup_const_mul_of_ne_top ha.ne_top,
    ← Filter.limsup_nat_add (fun τ : ℕ => (D.factorial : ℝ≥0∞) * (r τ : ℝ≥0∞) / (τ : ℝ≥0∞) ^ D) e]
  refine limsup_le_limsup ((eventually_mul_inv_pow_le D e ha).mono fun k hk => ?_)
  simp only [div_eq_mul_inv]
  rw [mul_left_comm]
  exact mul_le_mul_right hk _

end GlobalTheory.GrowthShift
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
section
noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace

namespace GlobalTheory.GalLift

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

section Datum

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m)
  (σ : D.what₂.LL →+* ℂ)

abbrev Comparison₂ (gramR : Matrix (Fin D.sp.X'.rank) (Fin D.sp.X'.rank) D.host.E)
    (c0R : VV D.what₂.LL (fun τ => Bridge.lamRdef (Ptw D) τ) →ₛₗ[D.what₂.embLL] R.cX.coef.W)
    (c0L : ∀ i : Fin D.R.m, VsV D i D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV i).W) : Prop :=
  Bridge.FamTie R.B R.pl (R.Sb : Set (Pl D.host.E)) R.Q (labLL D) (fun τ => Bridge.lamRdef (Ptw D) τ)
    (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L

abbrev ptAt (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) (f : WO (Vc D i) (Wc D i) → ℂ) :
    PolF D (Wc D i).rank (Vc D i).rank → (WO (Vc D i) (Wc D i) → ℂ) :=
  pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.BV i) B f

structure VecData (f₀ f : WO (Vc D i) (Wc D i) → ℂ)
    (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ) : Prop where
  vec : IsThPVecOf R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i σ)) (R.ΛV i) (R.ΛW i) (R.βV i) (R.βW i)
      R.Pg ∅ (fun _ => 1) f₀ f
  onb : ∀ ρ, IsONBasis (gramAt D (Wc D i) ρ) (cart (R.MW i σ) ρ) (B ρ) (pW D i ρ)
  theta : ∀ P, IsThetaFunO R.ψ (Vc D i) (Wc D i) (ptAt R i σ B f P)

def LiftData (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (ω : GA D (Vc D i) × GA D (Wc D i) →* Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ))
    (f₀ f : WO (Vc D i) (Wc D i) → ℂ) (B : D.what₂.Tau → Matrix (Fin (Wc D i).rank) (Fin (Wc D i).rank) ℂ)
    (io : LowT (R.MW i σ) →ₗ[ℂ] c.W →ₗ[ℂ] PolF D (Wc D i).rank (Vc D i).rank)
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ))) : Prop :=
  IsWeilDatumO R.ψ (Vc D i) (Wc D i) μ' (μ' * η'⁻¹) ω ∧ VecData R i σ f₀ f B ∧
    IsIoW R.θ (R.MW i σ) c ω (ptAt R i σ B f) (deltaConj i σ) io ∧
    Lift.IsThetaP (R.νV i A.μ0) (R.fdV i A.μ0) (fun g h φ => thetaKO ω h g φ) (ptAt R i σ B f) io
      (LinearMap.range (c.ext ∘ₗ H.e)) thP

def IsProjOf {c : CoefA (Vc D i)} {H : HMod (Bridge.Gf (Vc D i) → c.W)}
    (thP : LinearMap.range (c.ext ∘ₗ H.e) →ₗ[ℂ] (LowT (R.MW i σ) →ₗ[ℂ] (GA D (Wc D i) → ℂ)))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) : Prop :=
  ∀ (x : H.H) (v : ∀ ρ, lowT (R.MW i σ) ρ),
    (R.HW i σ).e (th x) (fun ρ => v ρ) = R.eWf i σ (thP ((c.ext ∘ₗ H.e).rangeRestrict x) (PiTensorProduct.tprod ℂ v))

theorem isConjLift_iff (μ' η' : (AE D)ˣ →* Circle) (c : CoefA (Vc D i)) (H : HMod (Bridge.Gf (Vc D i) → c.W))
    (th : H.H →ₗ[ℂ] (R.HW i σ).H) :
    IsConjLift R i σ μ' η' c H th ↔ ∃ ω f₀ f B io thP, LiftData R i σ μ' η' c H ω f₀ f B io thP ∧ IsProjOf R i σ thP th := by
  constructor
  · rintro ⟨ω, f₀, f, B, io, thP, h1, h2, h3, h4, h5, h6, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, ⟨h1, ⟨h2, h3, h4⟩, h5, h6⟩, h7⟩
  · rintro ⟨ω, f₀, f, B, io, thP, h, h7⟩
    exact ⟨ω, f₀, f, B, io, thP, h.1, h.2.1.vec, h.2.1.onb, h.2.1.theta, h.2.2.1, h.2.2.2, h7⟩

structure CoefAt (c : CoefA (Vc D i)) (c₁ : VsV D i D.what₂.LL →ₛₗ[σ] c.W) : Prop where
  coef : c.Is
  act : ∀ (γ : GQ (Vc D i)) (γE : GL (Fin (Vc D i).rank) D.host.E), Bridge.IsRatMat (Vc D i) γ γE →
    ∀ v, c₁ (rhoVr (labLL D) (lamV D i) γE v) = c.ρ (γ : GA D (Vc D i)) (c₁ v)
  indep : LinearIndependent ℂ fun a => c₁ (bVV D.what₂.LL (lamV D i) a)
  span : Submodule.span ℂ (Set.range fun a => c₁ (bVV D.what₂.LL (lamV D i) a)) = ⊤
  pair : ∀ a b, inner ℂ (c₁ (bVV D.what₂.LL (lamV D i) a)) (c₁ (bVV D.what₂.LL (lamV D i) b)) =
    σ (pairVr (labLL D) (lamV D i) (gramV D i) (bVV D.what₂.LL (lamV D i) a) (bVV D.what₂.LL (lamV D i) b))

def PhaseFun (u : GA D (Wc D i) → ℂ) : Prop :=
  (∀ h, ‖u h‖ = 1) ∧ (∀ γ ∈ GQ (Wc D i), ∀ h, u (γ * h) = u h) ∧ (∀ g ∈ GinfC (Wc D i), ∀ h, u (h * g) = u h) ∧
    ∀ k ∈ levW R i, ∀ h, u (h * k) = u h

abbrev IsLiftW (g : G) (k : GA D (Wc D i)) : Prop := Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) (R.eG g) k

def EtaVals : Prop :=
  ∀ (P : Pl D.host.E) (e : AE D), Formalism.L2.JoinChr.IsPlIdem D e P → ∀ x : (AE D)ˣ,
    (x : AE D) = Formalism.L2.JoinChr.locE D e (Formalism.L2.Host.unif P : D.host.Eˣ) →
      ∃ y : D.what₂.LL, D.what₂.embLL y = ((R.eta x : Circle) : ℂ) * (((Real.sqrt (Nat.card (kP P) : ℝ))⁻¹ : ℝ) : ℂ)

end Datum

section Geo

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {i : Fin D.R.m}
  (O : OMDat T.toCore R i Unit (fun _ => A.μ0))

def RepsAt (v₀ : (R.MW i (sg0 D A)).Vec) (h : O.Cl' () → GA D (Vc D i)) : Prop :=
  ∃ J' : Subgroup (Bridge.Gf (Vc D i)), RepsR R i A.μ0 h (O.bad ()) J' (O.Lh ()) (O.gam ()) (O.vol ()) ∧
    PlaceEx R i A.μ0 h O.c0' ∧ ThAdIs R i A.μ0 h O.c0' v₀ (O.thAd ()) ∧
      ∀ x, O.Plc () x ↔ ∃ x₀, Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x

abbrev actG (g : G) : T.R ((i : ℕ) + 1) →ₗ[T.Q.c.F] T.R ((i : ℕ) + 1) := actLev T.Q.c O.lev2 g

variable (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1))

def IsClassSum (h : O.Cl' () → GA D (Vc D i)) (x₀ : A.fam.amb.FL i A.μ0) {n : ℕ} (a : Fin n → D.what₂.LL)
    (f : Fin n → Cu T κ i) : Prop :=
  ∃ (x : O.Cl' () → VsV D i O.c'.F) (f' : Rul (T.Q.Xo ((i : ℕ) + 1)) O.c'),
    Place R i A.μ0 h O.c0' (jVx R i A.μ0 x₀) x ∧ f' ∈ sec (T.Q.Xo ((i : ℕ) + 1)) O.c' (wtA (κ i)) (Vc D i).rank ∧
    IsThClsD (T.Q.Xo ((i : ℕ) + 1)) O.c' (O.dδ ()) (O.w ()) (O.La ()) (O.Nc ()) (O.gam ()) (O.vol ()) (O.ep ()) O.io x f' ∧
    IsBC O.hle f' (fun k => O.jL (a k)) (fun k => (f k : T.R ((i : ℕ) + 1)))

def EquivBy (σ : D.what₂.LL →+* ℂ) (hV : T.V ((i : ℕ) + 1) (res T σ) = Wc D i) (u : GA D (Wc D i) → ℂ) : Prop :=
  ∀ g k, IsLiftW R i g k → ∀ (f : Cu T κ i) (h : GA D (Wc D i)),
    u h * phiC T hV (wtA (κ i)) (actG O g (f : T.R ((i : ℕ) + 1))) h =
      σ (((R.FW i).chi g : D.what₂.LLˣ) : D.what₂.LL) * (u (h * k) * phiC T hV (wtA (κ i)) (f : T.R ((i : ℕ) + 1)) (h * k))

end Geo

end GlobalTheory.GalLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularRepresentationOfFinitePair
section
noncomputable section

open MeasureTheory Filter Set
open scoped ENNReal symmDiff Topology Pointwise

namespace GlobalTheory.QuotRegular

section General

variable {G : Type} [Group G] (Γ : Subgroup G)

abbrev cl (g : G) : Quotient (QuotientGroup.rightRel Γ) := Quotient.mk _ g

theorem cl_mul (γ : Γ) (x : G) : cl Γ ((γ : G) * x) = cl Γ x := by
  refine Quotient.sound (QuotientGroup.rightRel_apply.2 ?_)
  simp

def tr (g : G) : Quotient (QuotientGroup.rightRel Γ) → Quotient (QuotientGroup.rightRel Γ) :=
  Quotient.map' (fun x => x * g) fun a b h => by
    rw [QuotientGroup.rightRel_apply] at h ⊢
    simpa [mul_assoc] using h

theorem tr_cl (g x : G) : tr Γ g (cl Γ x) = cl Γ (x * g) := rfl

theorem tr_one : tr Γ 1 = id := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_one x)

theorem tr_mul (g h : G) : tr Γ (g * h) = tr Γ h ∘ tr Γ g := by
  funext q
  induction q using Quotient.inductionOn with
  | h x => exact congrArg (cl Γ) (mul_assoc x g h).symm

variable [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G]

omit [TopologicalSpace G] [IsTopologicalGroup G] [BorelSpace G] in
theorem measurable_cl : Measurable (cl Γ) := measurable_quotient_mk''

theorem measurable_tr (g : G) : Measurable (tr Γ g) := by
  rw [measurable_from_quotient]
  exact (measurable_cl Γ).comp (measurable_mul_const g)

variable {Γ} {μ : Measure G} [μ.IsMulLeftInvariant] [Countable Γ] {𝓕 : Set G}

theorem ae_of_ae_quot (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {p : Quotient (QuotientGroup.rightRel Γ) → Prop}
    (hp : ∀ᵐ q ∂((μ.restrict 𝓕).map (cl Γ)), p q) : ∀ᵐ x ∂μ, p (cl Γ x) := by
  have h1 := ae_of_ae_map (measurable_cl Γ).aemeasurable hp
  rw [ae_restrict_iff'₀ h𝓕.nullMeasurableSet] at h1
  have h2 : ∀ᵐ y ∂μ, ∀ γ : Γ, (γ : G) * y ∈ 𝓕 → p (cl Γ ((γ : G) * y)) :=
    ae_all_iff.2 fun γ => (measurePreserving_mul_left μ (γ : G)).quasiMeasurePreserving.ae h1
  filter_upwards [h2, h𝓕.ae_covers] with y hy hc
  obtain ⟨γ, hγ⟩ := hc
  simpa only [cl_mul] using hy γ hγ

variable [μ.IsMulRightInvariant]

theorem measurePreserving_tr (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) :
    MeasurePreserving (tr Γ g) ((μ.restrict 𝓕).map (cl Γ)) ((μ.restrict 𝓕).map (cl Γ)) := by
  refine ⟨measurable_tr Γ g, Measure.ext fun A hA => ?_⟩
  have hA' : MeasurableSet (cl Γ ⁻¹' A) := measurable_cl Γ hA
  rw [Measure.map_apply (measurable_tr Γ g) hA, Measure.map_apply (measurable_cl Γ) hA,
    Measure.map_apply (measurable_cl Γ) (measurable_tr Γ g hA), Measure.restrict_apply hA',
    Measure.restrict_apply (measurable_cl Γ (measurable_tr Γ g hA))]
  have hD' : IsFundamentalDomain Γ ((fun x => x * g⁻¹) ⁻¹' 𝓕) μ :=
    h𝓕.preimage_of_equiv (measurePreserving_mul_right μ g⁻¹).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => by
        change ((γ : G) * x) * g⁻¹ = (γ : G) * (x * g⁻¹)
        rw [mul_assoc]
  have hinv : ∀ γ : Γ, (fun x => γ • x) ⁻¹' (cl Γ ⁻¹' A) = cl Γ ⁻¹' A := by
    intro γ
    ext x
    change cl Γ ((γ : G) * x) ∈ A ↔ cl Γ x ∈ A
    rw [cl_mul]
  rw [← hD'.measure_set_eq h𝓕 hA' hinv, ← measure_preimage_mul_right μ g (_ ∩ (fun x => x * g⁻¹) ⁻¹' 𝓕)]
  congr 1
  ext x
  simp only [mem_inter_iff, mem_preimage, tr_cl, mul_inv_cancel_right]

theorem measure_symmDiff_le (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) {A : Set (Quotient (QuotientGroup.rightRel Γ))}
    (hA : MeasurableSet A) (g g₀ : G) :
    ((μ.restrict 𝓕).map (cl Γ)) ((tr Γ g ⁻¹' A) ∆ (tr Γ g₀ ⁻¹' A)) ≤
      μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕))) := by
  set S := ((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆ ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) with hS
  have hU : μ.restrict 𝓕 (⋃ γ : Γ, γ • S) ≤ μ S := by
    rw [h𝓕.measure_eq_tsum S]
    refine (measure_iUnion_le _).trans (le_of_eq (tsum_congr fun γ => ?_))
    rw [Measure.restrict_apply₀' h𝓕.nullMeasurableSet]
  rw [Measure.map_apply (measurable_cl Γ) ((measurable_tr Γ g hA).symmDiff (measurable_tr Γ g₀ hA))]
  refine le_trans (measure_mono_ae ?_) hU
  have key : ∀ a b x : G, (∃ γ : Γ, γ • (x * a) ∈ 𝓕) → cl Γ (x * a) ∈ A → cl Γ (x * b) ∉ A →
      ∃ γ : Γ, (γ : G) * x * a ∈ cl Γ ⁻¹' A ∩ 𝓕 ∧ (γ : G) * x * b ∉ cl Γ ⁻¹' A ∩ 𝓕 := by
    rintro a b x ⟨γ, hγ⟩ h2 h3
    refine ⟨γ, ?_, fun h => h3 ?_⟩
    · rw [mul_assoc]
      exact ⟨by rw [mem_preimage, cl_mul]; exact h2, hγ⟩
    · have := h.1
      rwa [mem_preimage, mul_assoc, cl_mul] at this
  filter_upwards [ae_restrict_of_ae ((measurePreserving_mul_right μ g).quasiMeasurePreserving.ae h𝓕.ae_covers),
    ae_restrict_of_ae ((measurePreserving_mul_right μ g₀).quasiMeasurePreserving.ae h𝓕.ae_covers)] with x e1 e2 hx
  rcases hx with ⟨a, b⟩ | ⟨a, b⟩
  · obtain ⟨γ, k1, k2⟩ := key g g₀ x e1 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inl ⟨k1, k2⟩)⟩
  · obtain ⟨γ, k1, k2⟩ := key g₀ g x e2 a b
    exact mem_iUnion.2 ⟨γ⁻¹, mem_inv_smul_set_iff.2 (Or.inr ⟨k1, k2⟩)⟩

def reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) :
    G →* (Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ)) →L[ℂ] Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) where
  toFun g := (Lp.compMeasurePreservingₗᵢ ℂ (tr Γ g) (measurePreserving_tr h𝓕 g)).toContinuousLinearMap
  map_one' := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 1)).trans ?_
    rw [tr_one]
    rfl
  map_mul' g h := by
    refine ContinuousLinearMap.ext fun F => Lp.ext ?_
    refine (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 (g * h))).trans ?_
    refine EventuallyEq.trans ?_ (Lp.coeFn_compMeasurePreserving
      (Lp.compMeasurePreserving (tr Γ h) (measurePreserving_tr h𝓕 h) F) (measurePreserving_tr h𝓕 g)).symm
    rw [tr_mul]
    exact ((measurePreserving_tr h𝓕 g).quasiMeasurePreserving.ae_eq_comp
      (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 h))).symm

theorem reg_apply (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    reg h𝓕 g F = Lp.compMeasurePreserving (tr Γ g) (measurePreserving_tr h𝓕 g) F := rfl

theorem reg_val (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ∀ᵐ x ∂μ, reg h𝓕 g F (cl Γ x) = F (cl Γ (x * g)) :=
  ae_of_ae_quot h𝓕 (p := fun q => reg h𝓕 g F q = F (tr Γ g q))
    (Lp.coeFn_compMeasurePreserving F (measurePreserving_tr h𝓕 g))

theorem norm_reg (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (g : G) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    ‖reg h𝓕 g F‖ = ‖F‖ := Lp.norm_compMeasurePreserving F (measurePreserving_tr h𝓕 g)

theorem continuous_reg [LocallyCompactSpace G] [SecondCountableTopology G] [IsFiniteMeasureOnCompacts μ]
    (h𝓕 : IsFundamentalDomain Γ 𝓕 μ) (F : Lp ℂ 2 ((μ.restrict 𝓕).map (cl Γ))) :
    Continuous fun g => reg h𝓕 g F := by
  refine Lp.induction (p := 2) ENNReal.ofNat_ne_top (fun F => Continuous fun g => reg h𝓕 g F)
    ?_ ?_ ?_ F
  · intro c A hA hμA
    rw [Lp.simpleFunc.coe_indicatorConst]
    simp only [reg_apply, Lp.indicatorConstLp_compMeasurePreserving]
    refine continuous_indicatorConstLp_set ENNReal.ofNat_ne_top fun g₀ => ?_
    let m : C(G, C(G, G)) := ContinuousMap.curry ⟨fun p : G × G => p.2 * p.1, by fun_prop⟩
    have ht : Tendsto (fun g => μ (((fun x => x * g) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)) ∆
        ((fun x => x * g₀) ⁻¹' (cl Γ ⁻¹' A ∩ 𝓕)))) (𝓝 g₀) (𝓝 0) :=
      tendsto_measure_symmDiff_preimage_nhds_zero (μ := μ) (ν := μ) (f := m) (g := m g₀)
        (m.continuous.tendsto g₀) (Eventually.of_forall fun g => measurePreserving_mul_right μ g)
        (measurePreserving_mul_right μ g₀)
        ((measurable_cl Γ hA).nullMeasurableSet.inter h𝓕.nullMeasurableSet)
        (by
          rw [Measure.map_apply (measurable_cl Γ) hA, Measure.restrict_apply (measurable_cl Γ hA)] at hμA
          exact hμA.ne)
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => zero_le)
      fun g => measure_symmDiff_le h𝓕 hA g g₀
  · intro f g hf hg _ h1 h2
    simp only [map_add (f := _)]
    exact h1.add h2
  · refine isClosed_of_closure_subset fun F hF => ?_
    refine TendstoUniformly.continuous (F := fun F' g => reg h𝓕 g F') (p := 𝓝 F) ?_
      (mem_closure_iff_frequently.1 hF)
    refine Metric.tendstoUniformly_iff.2 fun ε hε => ?_
    filter_upwards [Metric.ball_mem_nhds F hε] with F' h g
    rw [dist_eq_norm, ← map_sub, norm_reg, ← dist_eq_norm, dist_comm]
    exact h

end General

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.HolDict

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem exists_isReg : ∀ (D : D7) (V : HSp D) (μ : Measure (GA D V)) (𝓕 : Set (GA D V)),
    FinPair V μ 𝓕 → ∃ ρ, IsReg V μ 𝓕 ρ := by
  intro D V μ 𝓕 h
  obtain ⟨h1, h2, -, h4, h5, -, h7⟩ := GlobalTheory.Mem.AdelicGroupTop.adelic_unitary_topology D V
  have := h.haar
  have := h.right
  exact ⟨reg h.fd, reg_val h.fd, norm_reg h.fd, continuous_reg h.fd⟩

end GlobalTheory.QuotRegular
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimilitudeFactorFormGroupBoundedOfTestSupportStatement
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.similitudeFactor_formGroup_bounded_of_test_support : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (L : G.Level) (f : G.GAf → ℂ), IsTest (MonoidHom.id _) L.K.toSubgroup L.K.toSubgroup f → ∀ (K' : Subgroup (Gr G 1)) (f' : Gr G 1 → ℂ), IsTest (sigG G 1) (KHT p G.m G.n 1 G.Fw) K' f' → ∀ (β : G.Cˣ) (x : (AfP p ⊗[ℚ] G.C)ˣ) (t : (AfP p)ˣ) (hx : Triv G (AfP p) β x t), ∃ S : ℝ, ∀ (y : grp G β) (h₁ : G.GAf) (h₂ : Gr G 1), f (h₁⁻¹ * toAfF G β x t hx y * h₁) ≠ 0 → f' (h₂⁻¹ * toP1 G β y * h₂) ≠ 0 → (((y : G.Cˣ × ℚˣ).2 : ℚ) : ℝ) ≤ S := by
  first | (exact @GlobalTheory.SimBound.main) | (exact GlobalTheory.SimBound.main) | (intros; apply GlobalTheory.SimBound.main  <;> assumption)
end

