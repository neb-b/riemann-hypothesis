module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0235
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0274
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0263
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0254
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0251
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0279
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0226
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0239
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0270
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0238
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0284
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0278

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaTranslatePowerSeriesPowBoundedCoeffsOfTorsi
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section
namespace GlobalTheory.ThetaTransl
open GlobalTheory.EvenTheta

variable {p : ℕ} [Fact p.Prime]

def GoodAt (g : GL3Theta.G1 p) (k : ℕ) (F : ℂ → ℂ) : Prop :=
  AlgEnt F ∧ ∃ B : PowerSeries ℂ_[p], BddSer B ∧ g.atU F = ePhi1 g.lam g.abelian₂ g.C g.wq ^ k * B

theorem bdd_mul {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f * h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.2

theorem bdd_add {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f + h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).1

theorem bdd_sub {f h : PowerSeries ℂ_[p]} (hf : BddSer f) (hh : BddSer h) : BddSer (f - h) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.1 f h hf hh).2.1

theorem bdd_C (c : ℂ_[p]) : BddSer (PowerSeries.C c) :=
  ((GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.1 c).1

theorem bdd_X : BddSer (PowerSeries.X : PowerSeries ℂ_[p]) :=
  ⟨1, (GlobalTheory.EvenTheta.SerRing.series_ring_laws p).2.2.2.1⟩

theorem bdd_sum {ι : Type*} (s : Finset ι) (f : ι → PowerSeries ℂ_[p]) (h : ∀ i ∈ s, BddSer (f i)) :
    BddSer (∑ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, fun n => by simp⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact bdd_add (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

theorem lamC_one (lam : Qbar →+* ℂ_[p]) : lamC lam 1 = 1 := by
  have h : (1 : ℂ) ∈ Qbar := one_mem _
  rw [lamC, dite_eq_left h]
  exact map_one lam

theorem good_mul {g : GL3Theta.G1 p} {k l : ℕ} {F G : ℂ → ℂ} (hF : GoodAt g k F) (hG : GoodAt g l G) :
    GoodAt g (k + l) (fun z => F z * G z) := by
  obtain ⟨hFa, B, hB, hFe⟩ := hF
  obtain ⟨hGa, B', hB', hGe⟩ := hG
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 F G hFa hGa).1
  refine ⟨ha, B * B', bdd_mul hB hB', ?_⟩
  rw [he, hFe, hGe, pow_add]
  ring

theorem good_one (g : GL3Theta.G1 p) : GoodAt g 0 (fun _ => (1 : ℂ)) := by
  obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
  refine ⟨ha, 1, ?_, ?_⟩
  · simpa using bdd_C (p := p) 1
  · rw [he, lamC_one, map_one, pow_zero, one_mul]

theorem good_pow {g : GL3Theta.G1 p} {k : ℕ} {F : ℂ → ℂ} (hF : GoodAt g k F) (n : ℕ) :
    GoodAt g (k * n) (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using good_one g
  | succ n ih =>
    have := good_mul ih hF
    simp only [← pow_succ] at this
    rwa [show k * n + k = k * (n + 1) by ring] at this

theorem good_congr {g : GL3Theta.G1 p} {k l : ℕ} {F : ℂ → ℂ} (h : GoodAt g k F) (e : k = l) : GoodAt g l F :=
  e ▸ h

theorem atU_mul_pow {g : GL3Theta.G1 p} {F G : ℂ → ℂ} (hF : AlgEnt F) (hG : AlgEnt G) (m n : ℕ) :
    AlgEnt (fun z => F z ^ m * G z ^ n) ∧ g.atU (fun z => F z ^ m * G z ^ n) = g.atU F ^ m * g.atU G ^ n := by
  have hpow : ∀ {H : ℂ → ℂ}, AlgEnt H → ∀ k : ℕ, AlgEnt (fun z => H z ^ k) ∧
      g.atU (fun z => H z ^ k) = g.atU H ^ k := by
    intro H hH k
    induction k with
    | zero =>
      obtain ⟨ha, he⟩ := (GlobalTheory.SerTransport.transport p g).2.1 1 (one_mem _)
      simp only [pow_zero]
      exact ⟨ha, by rw [he, lamC_one, map_one]⟩
    | succ k ih =>
      obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ H ih.1 hH).1
      simp only [pow_succ]
      exact ⟨ha, by rw [he, ih.2]⟩
  obtain ⟨h1, e1⟩ := hpow hF m
  obtain ⟨h2, e2⟩ := hpow hG n
  obtain ⟨ha, he⟩ := ((GlobalTheory.SerTransport.transport p g).1 _ _ h1 h2).1
  exact ⟨ha, by rw [he, e1, e2]⟩


set_option maxHeartbeats 800000 in
theorem tau_pow_bdd : ∀ (D : D7) (p : ℕ) [Fact p.Prime] (cc : Ideal (𝓞 D.host.K)) (δ : ℂ) (g : GL3Theta.G1 p),
    GL3Theta.At D cc δ g → ∀ t : ℂ, GL3Theta.Tors1 p g.abelian₂ t → ∀ N : ℕ, 0 < N → (N : ℂ) * t ∈ g.abelian₂ →
      GlobalTheory.EvenTheta.BddSer (GlobalTheory.ThetaTransl.tau g t ^ N) := by
  intro D p _ cc δ g hg t ht N hN hNt
  obtain ⟨hcc, -, hδ, hΛ, hok⟩ := hg
  have hcrv : Crv D cc δ := ⟨hcc, hδ⟩
  have hG := (GlobalTheory.InducedType.induced_type D).1
  obtain ⟨hlat, -, hdisc, -, -⟩ := GlobalTheory.CurveLattice.lattice_of_curve D hG cc δ hcrv
  obtain ⟨⟨-, h2, h3⟩, hwp⟩ := (GlobalTheory.CurveAlgebraic.integral_j_and_algebraic_data D hG).2 cc δ hcrv
  have huse := (GlobalTheory.ThetaConj.cmTheta_taylorCoeff_algebraic_and_conjugate D cc δ hcrv).1
  simp only [tor0] at h2 h3
  rw [← hΛ] at hlat hdisc h2 h3 hwp huse
  have hlat' : IsLat g.abelian₂ := hlat
  have halg : ∀ x, InRationalLattice g.abelian₂ x → AlgEnt (U1 g.abelian₂ x (sgStar g.abelian₂)) := fun x hx => ⟨by
    have := hlat'.differentiable
    unfold U1
    fun_prop, huse x hx⟩
  have hU0 : U1 g.abelian₂ 0 (sgStar g.abelian₂) = sgStar g.abelian₂ := by
    funext z; simp [U1]
  have hsg : AlgEnt (sgStar g.abelian₂) := hU0 ▸ halg 0 ⟨1, one_pos, by simp⟩
  have htq : InRationalLattice g.abelian₂ t := ⟨N, hN, hNt⟩
  have hP := halg t htq
  have htn := ht.1
  have hwt : wpF g.abelian₂ t ∈ Qbar := (hwp t htq htn).1
  obtain ⟨hu1, hwq1, -, he0, hsgU⟩ := GlobalTheory.EvenTheta.DatumBasic.datum_basic p g hok hlat' h2 h3 hdisc
  set e := ePhi1 g.lam g.abelian₂ g.C g.wq with he_def
  set ε : ℂ_[p] := ((g.C.u⁻¹ : ℂ_[p]ˣ) : ℂ_[p]) with hε_def
  have he : e ≠ 0 := fun h => by rw [h, map_zero] at he0; exact zero_ne_one he0
  have gσ : GoodAt g 1 (sgStar g.abelian₂) :=
    ⟨hsg, PowerSeries.C ε * PowerSeries.X, bdd_mul (bdd_C ε) bdd_X, by rw [hsgU]; ring⟩
  obtain ⟨hSa, hSe⟩ := GlobalTheory.EvenTheta.Param.sqTh_atU p g hok.2.1 hlat' h2 h3 hsg t htn hwt
  have gS : GoodAt g 2 (sqTh g.abelian₂ t) := ⟨hSa, lineSer g.wq⁻¹ (xAt g t),
    bdd_sub ⟨1, hwq1⟩ (bdd_mul (bdd_C _) (by rw [sq]; exact bdd_mul (bdd_X (p := p)) (bdd_X (p := p)))), hSe⟩
  obtain ⟨hTa, w, hw, hTe⟩ := _root_.GlobalTheory.ThetaTransl.CubeSer.sqThD_atU p g hok hlat' h2 h3 hdisc hsg t htn hwt
  have gT : GoodAt g 3 (sqThD g.abelian₂ t) := ⟨hTa, w, hw, hTe⟩
  obtain ⟨I, a, b, hle, hid⟩ := GlobalTheory.T.exists_sigmaStar_translate_pow_decomposition g.abelian₂ hlat' t N hN hNt t htn
  let φ : Fin (I + 1) ⊕ Fin (I + 1) → ℂ → ℂ := Sum.elim
    (fun i z => sgStar g.abelian₂ z ^ (2 * (I - (i : ℕ)) + 3) * sqTh g.abelian₂ t z ^ (i : ℕ))
    (fun j z => sgStar g.abelian₂ z ^ (2 * (I - (j : ℕ))) * sqTh g.abelian₂ t z ^ (j : ℕ) * sqThD g.abelian₂ t z)
  let c : Fin (I + 1) ⊕ Fin (I + 1) → ℂ := Sum.elim (fun i => a i) (fun j => b j)
  have gφ : ∀ k, GoodAt g (2 * I + 3) (φ k) := by
    rintro (i | j)
    · have hi := i.isLt
      exact good_congr (good_mul (good_pow gσ (2 * (I - (i : ℕ)) + 3)) (good_pow gS (i : ℕ))) (by omega)
    · have hj := j.isLt
      exact good_congr (good_mul (good_mul (good_pow gσ (2 * (I - (j : ℕ)))) (good_pow gS (j : ℕ))) gT)
        (by omega)
  obtain ⟨hEa, hEe⟩ := atU_mul_pow (g := g) hsg hP (2 * I + 3 - N) N
  have hEq : ∀ z, sgStar g.abelian₂ z ^ (2 * I + 3 - N) * U1 g.abelian₂ t (sgStar g.abelian₂) z ^ N = ∑ k, c k * φ k z := by
    intro z
    rw [hid z, Fintype.sum_sum_type]
    congr 1
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
    · rw [← Fin.sum_univ_eq_sum_range]; rfl
  obtain ⟨a', -, hlin⟩ := _root_.GlobalTheory.TranslLin.transl_lin p g _ φ c _ hEa (fun k => (gφ k).1) hEq
  choose B hB hBe using fun k => (gφ k).2
  have hS : BddSer (∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k) :=
    bdd_sum _ _ fun k _ => bdd_mul (bdd_C _) (hB k)
  rw [hEe, hsgU] at hlin
  simp only [hBe] at hlin
  have hPe : g.atU (U1 g.abelian₂ t (sgStar g.abelian₂)) = e * tau g t := by
    rw [tau, ← mul_assoc, PowerSeries.mul_inv_cancel _ (by rw [he0]; exact one_ne_zero), one_mul]
  rw [hPe] at hlin
  set K := 2 * I + 3 - N with hKd
  have hK : K + N = 2 * I + 3 := Nat.sub_add_cancel hle
  have hsum : ∑ k, PowerSeries.C (lamC g.lam (a' k)) * (e ^ (2 * I + 3) * B k) =
      e ^ (2 * I + 3) * ∑ k, PowerSeries.C (lamC g.lam (a' k)) * B k := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun k _ => by ring
  have hleft : (PowerSeries.C ε * PowerSeries.X * e) ^ K * (e * tau g t) ^ N =
      e ^ (2 * I + 3) * (PowerSeries.C (ε ^ K) * (PowerSeries.X ^ K * tau g t ^ N)) := by
    rw [← hK, pow_add, map_pow]; ring
  have key := hleft.symm.trans (hlin.trans hsum)
  have key2 := mul_left_cancel₀ (pow_ne_zero _ he) key
  obtain ⟨C0, hC0⟩ := hS
  refine ⟨C0, fun n => ?_⟩
  have h1 := congrArg (PowerSeries.coeff (n + K)) key2
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', if_pos (by omega), Nat.add_sub_cancel] at h1
  have h2 := hC0 (n + K)
  rw [← h1, norm_mul, norm_pow, hu1, one_pow, one_mul] at h2
  exact h2

end GlobalTheory.ThetaTransl
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TranslateModifiedSigmaTwoMulAtZero
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.SigmaDuplication

open Filter Topology

theorem sgStar_two_mul {Λ : AddSubgroup ℂ} (hΛ : GlobalTheory.EvenTheta.IsLat Λ) {P : ℂ} (hP : P ∉ Λ) :
    sgStar Λ (2 * P) = -(wpD Λ P) * sgStar Λ P ^ 4 := by
  obtain ⟨⟨hdiff, hd0, -, -⟩, hzero, -, hwp, -⟩ := GlobalTheory.OddTheta.sgStar_laws Λ hΛ
  obtain ⟨L, hL⟩ := GlobalTheory.OddTheta.exists_periodPair Λ hΛ
  have h0 : sgStar Λ 0 = 0 := (hzero 0).2 (zero_mem Λ)
  have hPL : P ∉ L.lattice := fun hm => hP ((hL P).2 hm)
  have hwpfun : wpF Λ = L.weierstrassP := funext (GlobalTheory.OddTheta.wpF_eq L Λ hL)
  have hwpd : HasDerivAt (wpF Λ) (wpD Λ P) P := by
    rw [hwpfun, GlobalTheory.LatticeInvariants.wpD_eq hL P, ← congrFun L.deriv_weierstrassP P]
    exact ((L.differentiableOn_weierstrassP P hPL).differentiableAt
      (L.isClosed_lattice.isOpen_compl.mem_nhds hPL)).hasDerivAt
  have hA : HasDerivAt (fun v => sgStar Λ (P + v)) (deriv (sgStar Λ) (P + P) * 1) P :=
    (hdiff (P + P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_add P)
  have hB : HasDerivAt (fun v => sgStar Λ (P - v)) (deriv (sgStar Λ) (P - P) * -1) P :=
    (hdiff (P - P)).hasDerivAt.comp P ((hasDerivAt_id' P).const_sub P)
  have hS := (hdiff P).hasDerivAt.pow 2
  have hG := (hwpd.sub_const (wpF Λ P)).mul (hS.const_mul (sgStar Λ P ^ 2))
  have hev : (fun v => sgStar Λ (P + v) * sgStar Λ (P - v)) =ᶠ[𝓝 P]
      (fun v => (wpF Λ v - wpF Λ P) * (sgStar Λ P ^ 2 * sgStar Λ v ^ 2)) := by
    have hne : sgStar Λ P ≠ 0 := fun h => hP ((hzero P).1 h)
    filter_upwards [(hdiff.continuous.continuousAt (x := P)).eventually_ne hne] with v hv
    have hvΛ : v ∉ Λ := fun hm => hv ((hzero v).2 hm)
    linear_combination hwp P v hP hvΛ
  have huniq := (hA.mul hB).unique (hG.congr_of_eventuallyEq hev)
  simp only [sub_self, h0, hd0, Pi.pow_apply] at huniq
  rw [two_mul]
  linear_combination -huniq

theorem U1_two_mul_at_zero_eq_neg_wpD_mul_pow_four : ∀ (Λ : AddSubgroup ℂ), GlobalTheory.EvenTheta.IsLat Λ → ∀ P : ℂ, P ∉ Λ →
    U1 Λ (2 * P) (sgStar Λ) 0 = -(wpD Λ P) * U1 Λ P (sgStar Λ) 0 ^ 4 := by
  intro Λ hΛ P hP
  show sgStar Λ (0 + 2 * P) * Complex.exp _ = -(wpD Λ P) * (sgStar Λ (0 + P) * Complex.exp _) ^ 4
  rw [zero_add, zero_add, sgStar_two_mul hΛ hP, mul_pow, ← Complex.exp_nat_mul, mul_assoc]
  congr 2
  simp only [map_mul, map_ofNat]
  push_cast
  ring_nf

end GlobalTheory.SigmaDuplication
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeilRepresentationCommHeisenbergIntertwiner
section
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.InertSign
open scoped BigOperators

noncomputable section

namespace GlobalTheory.WeilInter

variable {D : D7} {N N' : ℕ}

theorem sd_of_moves {g : GA D N} {L : Lat D N} (h : Moves D (g : GL (Fin N) (AE D)) L) : SD D L := by
  obtain ⟨Lt, h1, -⟩ := exists_lattice_of_adelic_point D N
  have : L = Lt g := by
    ext x; rw [h x, (h1 g).1 x]
  rw [this]; exact (h1 g).2

theorem klat (T : Tor D) {g : GA D N} {g' : GA D N'} {L : Lat D N} {L' : Lat D N'}
    (h : Moves D (g : GL (Fin N) (AE D)) L) (h' : Moves D (g' : GL (Fin N') (AE D)) L') :
    KLat D T (La D T L L') := Or.inr ⟨_, _, sd_of_moves h, sd_of_moves h', rfl⟩

theorem quot_bijective {V : Type} [AddCommGroup V] (A₁ A₂ B₁ B₂ : AddSubgroup V) (f : B₁ → B₂)
    (h1 : ∀ x y : B₁, (x : V) - (y : V) ∈ A₁ ↔ (f x : V) - (f y : V) ∈ A₂)
    (h2 : ∀ y : B₂, ∃ x : B₁, (f x : V) - (y : V) ∈ A₂) :
    Function.Bijective (fun q : B₁ ⧸ A₁.addSubgroupOf B₁ =>
      (QuotientAddGroup.mk (f (Quotient.out q)) : B₂ ⧸ A₂.addSubgroupOf B₂)) := by
  have e1 : ∀ x y : B₁, (QuotientAddGroup.mk x : B₁ ⧸ A₁.addSubgroupOf B₁) = QuotientAddGroup.mk y ↔
      (x : V) - (y : V) ∈ A₁ := fun x y => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  have e2 : ∀ x y : B₂, (QuotientAddGroup.mk x : B₂ ⧸ A₂.addSubgroupOf B₂) = QuotientAddGroup.mk y ↔
      (x : V) - (y : V) ∈ A₂ := fun x y => by
    rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf]; rfl
  constructor
  · intro q q' hq
    have := (e1 _ _).2 ((h1 _ _).2 ((e2 _ _).1 hq))
    rwa [QuotientAddGroup.out_eq', QuotientAddGroup.out_eq'] at this
  · intro r
    obtain ⟨y, rfl⟩ := QuotientAddGroup.mk_surjective r
    obtain ⟨x, hx⟩ := h2 y
    refine ⟨QuotientAddGroup.mk x, ?_⟩
    have h3 := (h1 _ _).1 ((e1 (Quotient.out (QuotientAddGroup.mk x : B₁ ⧸ A₁.addSubgroupOf B₁)) x).1
      (QuotientAddGroup.out_eq' _))
    refine (e2 _ _).2 ?_
    have := A₂.add_mem h3 hx
    rwa [sub_add_sub_cancel] at this

theorem wd_congr {T : Tor D} {A B : AddSubgroup (VC D N N')} (hA : Nice D T A) (hB : Nice D T B)
    {G : VC D N N' → ℂ} (hG : G ∈ ThSp D T A) {u v : VC D N N'} (hu : u ∈ B) (hv : v ∈ B) (h : u - v ∈ A) :
    Wd D T u G = Wd D T v G := by
  have h1 := Wd_Wd D T v (u - v) G
  rw [((hA.mem_ThSp G).1 hG).2 _ h, hB.2.1 v hv _ (B.sub_mem hu hv), one_smul, add_sub_cancel] at h1
  exact h1.symm

theorem iop_sum {T : Tor D} (A : AddSubgroup (VC D N N')) {B : AddSubgroup (VC D N N')} (hB : Nice D T B)
    [Fintype (B ⧸ A.addSubgroupOf B)] (F : VC D N N' → ℂ) :
    Iop D T A B F = ((Real.sqrt ((A.addSubgroupOf B).index : ℝ))⁻¹ : ℂ) •
      ∑ q : B ⧸ A.addSubgroupOf B, Wd D T ((Quotient.out q : B) : VC D N N') F := by
  rw [hB.Iop_eq]
  funext z
  rw [finsum_eq_sum_of_fintype, Pi.smul_apply, Finset.sum_apply, smul_eq_mul]

theorem zero_mem_TT (T : Tor D) : (0 : VC D N N' → ℂ) ∈ TT D T N N' := by
  refine ⟨differentiable_const _, 1, Nat.one_pos, fun x _ => ?_⟩
  have := Wd_smul D T (1 • x) 0 (0 : VC D N N' → ℂ)
  rwa [zero_smul, zero_smul] at this

theorem om_sum {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {e0 : VC D N N' → ℂ} (W : WeilO D cc δ N N' e0)
    (hadd : ∀ F ∈ TT D (tor0 D cc δ) N N', ∀ G ∈ TT D (tor0 D cc δ) N N', F + G ∈ TT D (tor0 D cc δ) N N')
    (g : GA D N) (g' : GA D N') {ι : Type} (s : Finset ι) (φ : ι → VC D N N' → ℂ)
    (hφ : ∀ i, φ i ∈ TT D (tor0 D cc δ) N N') :
    ∑ i ∈ s, φ i ∈ TT D (tor0 D cc δ) N N' ∧ W.Om g g' (∑ i ∈ s, φ i) = ∑ i ∈ s, W.Om g g' (φ i) := by
  induction s using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty, Finset.sum_empty]
    refine ⟨zero_mem_TT _, ?_⟩
    have := W.smul g g' 0 0 (zero_mem_TT _)
    rwa [zero_smul, zero_smul] at this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact ⟨hadd _ (hφ a) _ ih.1, by rw [W.add g g' _ (hφ a) _ ih.1, ih.2]⟩

theorem om_iop : ∀ (D : D7) (cc : Ideal (𝓞 D.host.K)) (δ : ℂ), Crv D cc δ → δ ≠ 0 → ∀ (N N' : ℕ) (e0 : VC D N N' → ℂ) (W : WeilO D cc δ N N' e0) (g h k : GA D N) (g' h' k' : GA D N') (L₁ L₂ M₁ M₂ : Lat D N) (L₁' L₂' M₁' M₂' : Lat D N'), Moves D (h : GL (Fin N) (AE D)) L₁ → Moves D (h' : GL (Fin N') (AE D)) L₁' → Moves D ((g * h : GA D N) : GL (Fin N) (AE D)) L₂ → Moves D ((g' * h' : GA D N') : GL (Fin N') (AE D)) L₂' → Moves D (k : GL (Fin N) (AE D)) M₁ → Moves D (k' : GL (Fin N') (AE D)) M₁' → Moves D ((g * k : GA D N) : GL (Fin N) (AE D)) M₂ → Moves D ((g' * k' : GA D N') : GL (Fin N') (AE D)) M₂' → ∀ F ∈ Th D (tor0 D cc δ) L₁ L₁', W.Om g g' (Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₁ L₁') (La D (tor0 D cc δ) M₁ M₁') F) = Iop D (tor0 D cc δ) (La D (tor0 D cc δ) L₂ L₂') (La D (tor0 D cc δ) M₂ M₂') (W.Om g g' F) := by
  intro D cc δ hc hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂' a1 a1' a2 a2' b1 b1' b2 b2' F hF
  obtain ⟨t1, t2, t3, -⟩ := _root_.GlobalTheory.ThetaLevels.levels_closed D cc δ hc N N'
  have hFT := t1 _ _ (sd_of_moves a1) (sd_of_moves a1') F hF
  have hG := _root_.GlobalTheory.WeilTheta.om_mem_Th_moved D cc δ hc N N' e0 W g h g' h' L₁ L₂ L₁' L₂' a1 a1' a2 a2' F hF
  obtain ⟨f, f1, f2, f3⟩ := _root_.GlobalTheory.WeilCorr.exists_corr D cc δ hc hδ N N' e0 W g h k g' h' k' L₁ L₂ M₁ M₂ L₁' L₂' M₁' M₂'
    a1 a1' a2 a2' b1 b1' b2 b2' F hFT
  have kA1 := klat (tor0 D cc δ) a1 a1'
  have kA2 := klat (tor0 D cc δ) a2 a2'
  have kB1 := klat (tor0 D cc δ) b1 b1'
  have kB2 := klat (tor0 D cc δ) b2 b2'
  have nA2 := GlobalTheory.ThetaTriple.nice_of_klat hc kA2
  have nB1 := GlobalTheory.ThetaTriple.nice_of_klat hc kB1
  have nB2 := GlobalTheory.ThetaTriple.nice_of_klat hc kB2
  haveI i1 := AddSubgroup.fintypeOfIndexNeZero (GlobalTheory.ThetaTriple.index_ne_zero hc kA1 kB1)
  haveI i2 := AddSubgroup.fintypeOfIndexNeZero (GlobalTheory.ThetaTriple.index_ne_zero hc kA2 kB2)
  have hb := quot_bijective _ _ _ _ f f2 f3
  have hi : ((La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) M₁ M₁')).index =
      ((La D (tor0 D cc δ) L₂ L₂').addSubgroupOf (La D (tor0 D cc δ) M₂ M₂')).index :=
    Nat.card_congr (Equiv.ofBijective _ hb)
  have hW : ∀ x : La D (tor0 D cc δ) M₁ M₁', Wd D (tor0 D cc δ) (x : VC D N N') F ∈ TT D (tor0 D cc δ) N N' := by
    intro x
    obtain ⟨z, hz, -⟩ := exists_pt_of_mem_La_moved D (GlobalTheory.InducedType.induced_type D).1 cc δ hc.1.1 N N' k k'
      M₁ M₁' b1 b1' x x.2
    rw [hz]
    exact t2 z F hFT
  obtain ⟨s1, s2⟩ := om_sum W t3 g g' Finset.univ
    (fun q : La D (tor0 D cc δ) M₁ M₁' ⧸ (La D (tor0 D cc δ) L₁ L₁').addSubgroupOf (La D (tor0 D cc δ) M₁ M₁') =>
      Wd D (tor0 D cc δ) ((Quotient.out q : La D (tor0 D cc δ) M₁ M₁') : VC D N N') F) (fun q => hW _)
  rw [iop_sum _ nB1, iop_sum _ nB2, W.smul g g' _ _ s1, s2, hi]
  congr 1
  refine Fintype.sum_bijective _ hb _ _ fun q => ?_
  rw [f1]
  refine wd_congr nA2 nB2 hG (f _).2 (Subtype.property _) ?_
  have := (QuotientAddGroup.out_eq' (QuotientAddGroup.mk (f (Quotient.out q)) : La D (tor0 D cc δ) M₂ M₂' ⧸
    (La D (tor0 D cc δ) L₂ L₂').addSubgroupOf (La D (tor0 D cc δ) M₂ M₂'))).symm
  rw [QuotientAddGroup.eq_iff_sub_mem, AddSubgroup.mem_addSubgroupOf] at this
  exact this

end GlobalTheory.WeilInter
end
end

