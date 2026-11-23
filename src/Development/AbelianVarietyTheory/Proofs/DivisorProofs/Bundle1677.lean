module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DefiniteThetaPairTermsNormsIndependentRepresenta
public import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
public import Formalism.PairingDivisors.StatementH
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0330
public import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ValBasic
public import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.Bundle0002
public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1615
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
public import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1645
public import Development.AbelianVarietyTheory.Definitions.Foundations.OfInfProjInfMulOfFinProjFin
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1659
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1288
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1487
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1502
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1617

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationProportionalityRatioLeBottomPairs
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.NormSum.LemmaC

open GlobalTheory.NormVal

theorem integralOver_cast {D : D7} {p m n : ℕ} (e : n = m) (h : GA D n) (hi : IntegralOver D p h) :
    IntegralOver D p (e ▸ h : GA D m) := by
  subst e; exact hi

theorem exists_cast_eq {D : D7} {p m n : ℕ} (e : n = m) (h' : GA D m) :
    ∃ h : GA D n, (e ▸ h : GA D m) = h' ∧ (IntegralOver D p h' → IntegralOver D p h) := by
  subst e; exact ⟨h', rfl, id⟩

theorem bd_intCast (p : ℕ) [Fact p.Prime] (n : ℤ) : Bd p 1 ((n : ℤ) : ℂ) := by
  have hm : ((n : ℤ) : ℂ) ∈ Qbar := intCast_mem _ n
  refine ⟨hm, fun lam => ?_⟩
  rw [lamC_of_mem lam hm]
  have e1 : (⟨(n : ℂ), hm⟩ : Qbar) = (n : Qbar) := Subtype.ext (by simp)
  rw [e1, map_intCast]
  exact IsUltrametricDist.norm_intCast_le_one _ n


set_option maxHeartbeats 1000000 in
theorem vw_le_of_bottom_pairs : ∀ (D : D7) (N : ℕ) (B : ℝ) (Q : ℕ) (S : Finset ℕ) (del_vp : ℕ → ℝ) (b : ℝ), GlobalTheory.NormSum.Inp D →
    GlobalTheory.NormSum.Exponents S del_vp b → GlobalTheory.NormSum.CoordInt D N B Q del_vp →
    ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (σ : K →+* ℂ) (w : Formalism.PairingDivisionLocalBalance.Pl K) (p : ℕ) [Fact p.Prime],
    (p : 𝓞 K) ∈ w.asIdeal → ∀ (δ t0 : ℂ) (Q₁ Q₂ : ℕ), padicValNat p Q₁ ≤ padicValNat p Q →
    padicValNat p Q₂ ≤ padicValNat p Q →
    ∀ (P₁ P₁' : Pair D ⊤ δ t0 Q₁) (P₂ P₂' : Pair D ⊤ δ t0 Q₂), P₁.Small N B → P₁'.Small N B → P₂.Small N B →
    P₂'.Small N B → ∀ (hd₁ : P₁'.d = P₁.d) (hd₂ : P₂'.d = P₂.d) (b₁ b₂ v : ℂ)
    (M₁ : Tup D P₁.a P₁.d P₁.n → Tup D P₁'.a P₁'.d P₁'.n → ℤ) (M₂ : Tup D P₂'.a P₂'.d P₂'.n → Tup D P₂.a P₂.d P₂.n → ℤ),
    (∀ (h : GA D P₁.d) T, starRingEnd ℂ (P₁.coord h T) = b₁ * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁ ▸ h) T') →
    (∀ (h : GA D P₂.d) T', P₂'.coord (hd₂ ▸ h) T' * b₂ = ∑ T, (M₂ T' T : ℂ) * starRingEnd ℂ (P₂.coord h T)) →
    b₂ ≠ 0 → v ∈ Qbar → (∀ lam : Qbar →+* ℂ_[p], ‖lamC lam v‖ = 1) →
    ∀ (γ z z' : K), b₁ = σ γ * b₂ * v → σ z = (P₁.norm : ℂ) → σ z' = (P₂'.norm : ℂ) → z ≠ 0 → z' ≠ 0 →
    (vw w γ : ℝ) ≤ vw w z + vw w z' + 6 * Formalism.PairingDivisionLocalBalance.wt S del_vp w := by
  intro D N B Q S del_vp b hI hE hC K _ _ _ σ w p _ hw δ t0 Q₁ Q₂ hQ₁ hQ₂ P₁ P₁' P₂ P₂' hs₁ hs₁' hs₂ hs₂' hd₁ hd₂ b₁ b₂ v M₁ M₂ hr₁ hr₂ hb₂ hv hv1 γ z z' hγ hz hz' hz0 hz0'
  have hp : p.Prime := Fact.out
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
  have hp0 : (0 : ℝ) < p := by linarith
  set e : ℝ := del_vp p with he
  set r : ℝ := (p : ℝ) ^ e with hr
  have hr0 : 0 ≤ r := by positivity

  have hgam : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, Bd p r ((gam D P.J g : ℂ)⁻¹) := fun P hQ' hS g => by
    obtain ⟨-, h2, -⟩ := hC δ t0 p _ hQ' P hS
    exact (Bd.inv_nat (h2 g).1 dvd_rfl).mono (Real.rpow_le_rpow_of_exponent_le hp1 (h2 g).2)

  have hco : ∀ {Q' : ℕ} (P : Pair D ⊤ δ t0 Q'), padicValNat p Q' ≤ padicValNat p Q → P.Small N B →
      ∀ g, IntegralOver D p g → ∀ T, Bd p r (P.coord g T) := fun P hQ' hS g hg T =>
    (hC δ t0 p _ hQ' P hS).2.2 g hg T

  have hb₁ : b₁ ≠ 0 := by
    rintro rfl
    have h0 : P₁.norm = 0 := by
      unfold Pair.norm
      refine finsum_eq_zero_of_forall_eq_zero fun q => ?_
      have : P₁.sq q.out = 0 := by
        unfold Pair.sq
        refine Finset.sum_eq_zero fun T _ => ?_
        have := hr₁ q.out T
        rw [zero_mul, map_eq_zero] at this
        rw [this, norm_zero]; norm_num
      rw [this, mul_zero]
    apply hz0
    apply σ.injective
    rw [hz, h0, map_zero, Complex.ofReal_zero]
  have hγ0 : γ ≠ 0 := by
    rintro rfl
    rw [map_zero, zero_mul, zero_mul] at hγ
    exact hb₁ hγ
  have hv0 : v ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hγ
    exact hb₁ hγ

  have hA : Bd p (r * (r * (1 * r))) ((P₁.norm : ℂ) * b₁⁻¹) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₁ hQ₁ P₁ hs₁
    choose s hs1 hs2 using h1
    rw [(_root_.GlobalTheory.NormSum.RepInv.rep_indep D hI ⊤ δ t0 Q₁ P₁.crv P₁.pt0 P₁ P₁.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₁⁻¹)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₁ hQ₁ hs₁ _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      have e1 : ((‖P₁.coord (s q) T‖ ^ 2 : ℝ) : ℂ) * b₁⁻¹ =
          P₁.coord (s q) T * ∑ T', (M₁ T T' : ℂ) * P₁'.coord (hd₁.symm ▸ s q) T' := by
        rw [Complex.ofReal_pow, ← Complex.mul_conj', hr₁]
        field_simp
      rw [e1]
      refine (hco P₁ hQ₁ hs₁ _ (hs2 q) T).mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      exact (bd_intCast p _).mul (hco P₁' hQ₁ hs₁' _ (integralOver_cast hd₁.symm _ (hs2 q)) T')

  have hB : Bd p (r * (r * (1 * r))) ((P₂'.norm : ℂ) * b₂) := by
    obtain ⟨h1, -, -⟩ := hC δ t0 p Q₂ hQ₂ P₂' hs₂'
    choose s hs1 hs2 using h1
    rw [(_root_.GlobalTheory.NormSum.RepInv.rep_indep D hI ⊤ δ t0 Q₂ P₂'.crv P₂'.pt0 P₂' P₂'.level_pos).2.2.2.1 s hs1]
    refine finsum_induction (fun x : ℝ => Bd p (r * (r * (1 * r))) ((x : ℂ) * b₂)) ?_
      (fun x y hx hy => ?_) (fun q => ?_)
    · beta_reduce; rw [Complex.ofReal_zero, zero_mul]; exact Bd.zero (by positivity)
    · beta_reduce at hx hy ⊢; rw [Complex.ofReal_add, add_mul]; exact hx.add hy
    · beta_reduce; rw [Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast, mul_assoc]
      refine Bd.mul (hgam P₂' hQ₂ hs₂' _) ?_
      unfold Pair.sq
      rw [Complex.ofReal_sum, Finset.sum_mul]
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T' _ => ?_)
      obtain ⟨h, hh, hi⟩ := exists_cast_eq (p := p) hd₂.symm (s q)
      have e1 : ((‖P₂'.coord (s q) T'‖ ^ 2 : ℝ) : ℂ) * b₂ =
          (starRingEnd ℂ) (P₂'.coord (s q) T') * ∑ T, (M₂ T' T : ℂ) * (starRingEnd ℂ) (P₂.coord h T) := by
        rw [← hr₂ h T', hh, Complex.ofReal_pow, ← Complex.mul_conj']
        ring
      rw [e1]
      refine (hco P₂' hQ₂ hs₂' _ (hs2 q) T').conj.mul ?_
      refine Finset.sum_induction _ _ (fun x y => Bd.add) (Bd.zero (by positivity)) (fun T _ => ?_)
      exact (bd_intCast p _).mul (hco P₂ hQ₂ hs₂ _ (hi (hs2 q)) T).conj

  set x : K := z * z' * γ⁻¹ with hx
  have hx0 : x ≠ 0 := mul_ne_zero (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0)
  have hσx : σ x = ((P₁.norm : ℂ) * b₁⁻¹) * ((P₂'.norm : ℂ) * b₂) * v := by
    have hσγ : σ γ ≠ 0 := (map_ne_zero σ).2 hγ0
    rw [hx, map_mul, map_mul, map_inv₀, hz, hz', hγ]
    field_simp
  have hX : Bd p (r * (r * (1 * r)) * (r * (r * (1 * r))) * 1) (σ x) := by
    rw [hσx]
    exact (hA.mul hB).mul ⟨hv, fun lam => (hv1 lam).le⟩
  have hpow : r * (r * (1 * r)) * (r * (r * (1 * r))) * 1 = (p : ℝ) ^ (6 * e) := by
    rw [mul_comm 6 e, Real.rpow_mul hp0.le, hr]
    norm_num
    ring
  have key := GlobalTheory.PadicPlaceBound.neg_mul_vw_le_vw K σ x p w (6 * e) hx0 hw fun lam =>
    (hX.2 lam).trans (le_of_eq hpow)
  have hvx : (Formalism.DivisionValues.vw w x : ℝ) = Formalism.DivisionValues.vw w z + Formalism.DivisionValues.vw w z' - Formalism.DivisionValues.vw w γ := by
    rw [hx, Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ (mul_ne_zero hz0 hz0') (inv_ne_zero hγ0),
      Formalism.DivisionValues.ValuationRepresentative.vw_mul w _ _ hz0 hz0', Formalism.DivisionValues.ValuationRepresentative.vw_inv]
    push_cast; ring
  rw [hE.wt_eq hp w hw]
  rw [hvx] at key
  linarith

end GlobalTheory.NormSum.LemmaC
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilActionIntegralPointCosetVectorEq
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead.Move

open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

variable {D : D7}


set_option maxHeartbeats 1000000 in
theorem eig_of_prop {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) (hT : P.e0 ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    {g' : Formalism.MainNotions.StandardLatticesGL3.GA D P.d}
    {H : VC D P.a P.d → ℂ} {c : ℂ} (hc' : P.W.Om 1 g' P.e0 = c • H) (hH : H ∈ TT D (tor0 D ⊤ δ) P.a P.d)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) : P.W.Om k 1 H = s • H := by
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply P.W.nz
    have h0 : P.W.Om 1 g' P.e0 = 0 := by rw [hc', zero_smul]
    have e := P.W.mul 1 1 g'⁻¹ g' P.e0 hT
    have e1 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * 1 = 1 := mul_one 1
    have e2 : g'⁻¹ * g' = 1 := inv_mul_cancel g'
    rw [e1, e2, P.W.one _ hT, h0] at e
    have z := P.W.smul 1 g'⁻¹ (0 : ℂ) (0 : VC D P.a P.d → ℂ) (NormUniq.tt_zero _)
    have z0 : (0 : ℂ) • (0 : VC D P.a P.d → ℂ) = 0 := zero_smul ℂ _
    rw [z0] at z
    rw [e, z]
    exact zero_smul ℂ _
  have e1 := P.W.mul k 1 1 g' P.e0 hT
  have e2 := P.W.mul 1 k g' 1 P.e0 hT
  have f1 : k * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) = k := mul_one k
  have f2 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) * g' = g' := one_mul g'
  have f3 : (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) * k = k := one_mul k
  have f4 : g' * (1 : Formalism.MainNotions.StandardLatticesGL3.GA D P.d) = g' := mul_one g'
  rw [f1, f2] at e1
  rw [f3, f4] at e2
  have e3 : P.W.Om k 1 (P.W.Om 1 g' P.e0) = s • P.W.Om 1 g' P.e0 := by
    rw [← e1, e2, he, P.W.smul _ _ _ _ hT]
  rw [hc', P.W.smul _ _ _ _ hH, smul_comm s c H] at e3
  exact smul_right_injective _ hc0 e3

theorem iop_eig (hI : Inp D) {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)} (h𝔪 : 𝔪 ≠ ⊥)
    (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a) (s : ℂ) (he : P.W.Om k 1 P.e0 = s • P.e0) :
    P.W.Om k 1 (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d)
        (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0) =
      s • Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0 := by
  obtain ⟨g', hg'⟩ := GlobalTheory.TrueTheta.exists_moves_of_selfDual D P.d _ (GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d)
  obtain ⟨c, hc⟩ := VacMove.exists_scalar hI P.crv P.vac.1 P.W 1 g' (VacMove.moves_one D P.a) hg'
  exact eig_of_prop P (VacMove.vac_TT hI.g1 P.crv P.vac.1) (c := c) (by rw [hc]; funext z; rfl)
    (GlobalTheory.FunObj.CosetFix.iop_facts hI P h𝔪).1 k s he

theorem exists_close {𝔪 : Ideal (𝓞 D.host.E)} (o : ℕ) {a d : ℕ} (k : Formalism.MainNotions.StandardLatticesGL3.GA D a)
    (z : Matrix (Fin d) (Fin a) D.host.E) (hz : Approx 𝔪 o k z) (m : ℕ) (hm : 0 < m) :
    ∃ w : Matrix (Fin d) (Fin a) D.host.E, (∀ i j, ∃ b ∈ 𝔪, w i j = (b : D.host.E)) ∧
      CloseTo D ⊤ m (k : GL (Fin a) (Formalism.MainNotions.StandardLatticesGL3.AE D)) ((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D))
        (unitBlock D o a d) (z + w) := by
  choose b hb y hy hby using fun i j => GlobalTheory.CongApprox.exists_mem_approx D 𝔪 m hm _ (neg_mem (hz i j))
  refine ⟨Matrix.of fun i j => (b i j : D.host.E), fun i j => ⟨b i j, hb i j, rfl⟩, ?_⟩
  have e1 : (((1 : Formalism.MainNotions.StandardLatticesGL3.GA D d) : GL (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) : Matrix (Fin d) (Fin d) (Formalism.MainNotions.StandardLatticesGL3.AE D)) = 1 := by
    simp
  unfold CloseTo
  refine fun i j => ⟨y i j, hy i j, Eq.trans ?_ (hby i j)⟩
  rw [e1, Matrix.one_mul, Matrix.map_add _ (map_add (inc D))]
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.map_apply, Matrix.of_apply]
  ring

theorem wd_smul (δ : ℂ) {a d : ℕ} (x : VC D a d) (c : ℂ) (F : VC D a d → ℂ) :
    Wd D (tor0 D ⊤ δ) x (c • F) = c • Wd D (tor0 D ⊤ δ) x F := by
  funext y
  simp only [Wd, Formalism.MainNotions.TaylorLogMetric.U, Pi.smul_apply, smul_eq_mul]
  ring

theorem om_cosetVec : ∀ {D : D7}, GlobalTheory.NormSum.Inp D → ∀ {δ t0 : ℂ} {Q : ℕ} (P : Pair D ⊤ δ t0 Q) {𝔪 : Ideal (𝓞 D.host.E)}, 𝔪 ≠ ⊥ →
  ∀ (o : ℕ) (k : Formalism.MainNotions.StandardLatticesGL3.GA D P.a), k ∈ intG D P.a → ∀ c : ℂ, P.W.Om k 1 P.e0 = c • P.e0 →
  ∀ z : Matrix (Fin P.d) (Fin P.a) D.host.E, IsIntE z → Approx 𝔪 o k z →
  P.W.Om k 1 (cosetVec P 𝔪 o) = c • cosV δ 𝔪 z P.e0 := by
  intro D hD δ t0 Q P 𝔪 h𝔪 o k hk c hc z hzi hz
  have h1 := hD.g1
  have he := P.vac.1
  have hIT := (GlobalTheory.FunObj.CosetFix.iop_facts hD P h𝔪).1
  have hfix := iop_eig hD P h𝔪 k c hc
  have k0 : KLat D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) :=
    VacMove.klat _ (VacMove.moves_one D P.a) (VacMove.moves_one D P.d)
  have kB : KLat D (tor0 D ⊤ δ) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) :=
    Or.inr ⟨_, _, VacMove.sd_of_moves (VacMove.moves_one D P.a), GlobalTheory.SkewLatSelfDual.skewLat_SD h𝔪 P.d, rfl⟩
  have hHB := (hD.uni ⊤ δ P.crv P.a P.d _ _ k0 kB P.e0 he).2.1
  obtain ⟨m, hm, hl⟩ := P.W.lift k 1 (unitBlock D o P.a P.d) _ hIT
  obtain ⟨w, hw, hclose⟩ := exists_close o k z hz m hm
  have hmain := hl _ hclose
  rw [hfix, wd_smul] at hmain
  obtain ⟨hw0, hwB⟩ := GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ 𝔪 w hw
  have hx0 := (GlobalTheory.FunObj.SqNum.pt_mem_of_entries_mem D δ ⊤ z
    (fun i j => (hzi i j).imp fun b hb => ⟨Submodule.mem_top, hb⟩)).1
  obtain ⟨φ, hφ⟩ := VacMove.wd_wd D (tor0 D ⊤ δ) (pt D (tor0 D ⊤ δ) δ z) (pt D (tor0 D ⊤ δ) δ w)
  have hφ1 : φ = 1 := by
    have h2 := hφ P.e0
    rw [VacMove.wd_fix h1 P.crv k0 he hw0, VacMove.wd_fix h1 P.crv k0 he hx0,
      VacMove.wd_fix h1 P.crv k0 he (add_mem hx0 hw0)] at h2
    by_contra hne
    apply P.W.nz
    have : (φ - 1) • P.e0 = 0 := by rw [sub_smul, one_smul, ← h2, sub_self]
    exact (smul_eq_zero.1 this).resolve_left (sub_ne_zero.2 hne)
  have h3 := hφ (Iop D (tor0 D ⊤ δ) (La0 D (tor0 D ⊤ δ) P.a P.d) (La D (tor0 D ⊤ δ) (stdL D P.a) (skewLat D 𝔪 P.d)) P.e0)
  rw [VacMove.wd_fix h1 P.crv kB hHB hwB, hφ1, one_smul, ← VacMove.pt_add] at h3
  have hWT := GlobalTheory.FunObj.NormUniq.wd_rat_mem_TT P.crv one_pos (by rw [one_smul]; exact pt_unitBlock_mem δ o P.a P.d) hIT
  unfold cosetVec cosV
  rw [P.W.smul _ _ _ _ hWT, hmain, ← h3, smul_comm]

end GlobalTheory.StdRead.Move
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilEigenInjectiveExtends
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.EvInj

theorem finprod_ne_zero' {ι : Type} {g : ι → ℂ} (h : ∀ i, g i ≠ 0) : ∏ᶠ i, g i ≠ 0 := by
  classical
  rw [finprod_def]
  split_ifs
  · exact Finset.prod_ne_zero_iff.2 fun i _ => h i
  · exact one_ne_zero

theorem eq_zero_of_pure_eq_zero {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f : SInf F κ)
    (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ) (hne : ∀ v, φ v ≠ 0)
    (hstd : ∀ᶠ v in Filter.cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1)
    (h0 : pure f φ = 0) : f = 0 := by
  classical
  have hS := Filter.eventually_cofinite.1 hstd
  set S := hS.toFinset
  have hpt : ∀ v, ∃ y : κ → Fv F v, φ v y ≠ 0 := fun v => by
    by_contra hc
    push_neg at hc
    exact hne v (funext hc)
  choose pt hpt using hpt
  let yf : κ → Af F := fun i => ∑ v ∈ S, GlobalTheory.AdelicU.singleFin v (pt v i)
  have hyf : ∀ w i, evalV F w (yf i) = if w ∈ S then pt w i else 0 := by
    intro w i
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [yf, map_sum]
    split_ifs with hw
    · rw [Finset.sum_eq_single w]
      · exact GlobalTheory.AdelicU.evalV_singleFin_self w _
      · intro b _ hb; exact GlobalTheory.AdelicU.evalV_singleFin_ne (Ne.symm hb) _
      · intro h; exact absurd hw h
    · refine Finset.sum_eq_zero fun b hb => ?_
      exact GlobalTheory.AdelicU.evalV_singleFin_ne (by rintro rfl; exact hw hb) _
  ext a
  let x : κ → AF F := fun i => ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i), yf i)
  have hI : (fun i => evI F (x i)) = a := by
    funext i
    show InfiniteAdeleRing.ringEquiv_mixedSpace F ((InfiniteAdeleRing.ringEquiv_mixedSpace F).symm (a i)) = a i
    exact RingEquiv.apply_symm_apply _ _
  have hF : ∀ w, (fun i => GlobalTheory.AdelicU.evFin F w (x i)) = fun i => if w ∈ S then pt w i else 0 := by
    intro w; funext i; exact hyf w i
  have hc : ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) ≠ 0 := by
    refine finprod_ne_zero' fun v => ?_
    rw [hF v]
    by_cases hv : v ∈ S
    · simp only [hv, if_true]; exact hpt v
    · simp only [hv, if_false]
      have : φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1 := by
        by_contra hc'; exact hv (hS.mem_toFinset.2 hc')
      rw [this, Set.indicator_of_mem (by intro i; exact zero_mem _)]
      exact one_ne_zero
  have e := congrFun h0 x
  change f (fun i => evI F (x i)) * ∏ᶠ v, φ v (fun i => GlobalTheory.AdelicU.evFin F v (x i)) = 0 at e
  rw [hI] at e
  simpa using (mul_eq_zero.1 e).resolve_right hc

theorem ei_injective : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E) (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M M₁ : Model σ X W), M.IsGood B.ψ → ∀ e : Fn F n d →ₗ[ℂ] Fn F n d, Set.InjOn e (schA F (Fin n × Fin d) : Set _) → ∀ (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d)) (ev : ∀ v : Pl (F := F), ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ), (∀ v, ev v (M.vac v) = M₁.vac v) → (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in Filter.cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) → Function.Injective ei := by
  intro F E _ _ _ _ _ σ B n d X W M M₁ hM e hinj ei ev _ hev
  refine (injective_iff_map_eq_zero ei).2 fun f hf => ?_
  have hSB : ∀ v, M.vac v ∈ SB (Fin n × Fin d → Fv F v) := fun v => (hM.vac v).1
  have hmem : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac ∈ schA F (Fin n × Fin d) :=
    GlobalTheory.TensUniq.pure_mem_schA f M.vac hSB hM.std
  have h1 : e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac) = e 0 := by
    rw [hev f M.vac hSB (Filter.Eventually.of_forall fun _ => rfl), hf, map_zero]
    funext x
    simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  have h2 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f M.vac = 0 :=
    hinj hmem (schA F (Fin n × Fin d)).zero_mem h1
  exact eq_zero_of_pure_eq_zero f M.vac (fun v => (hM.vac v).2.1) hM.std h2

end GlobalTheory.EvInj
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorHaarNormProportionalStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK MeasureTheory GlobalTheory.DoublingEv
open scoped Matrix ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_operator_haar_norm_proportional : ∀ (F : Type) [Field F] [NumberField F] (κ κ' : Type) [Fintype κ] [Fintype κ']
    (A : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ)), IsTame F A →
    (∀ μ : @Measure (κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ φ ∈ schA F κ, ∫⁻ x, ‖A φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖φ x‖ₑ ^ 2 ∂μ) →
    (∀ μ : @Measure (κ ⊕ κ' → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ ⊕ κ'), ∫⁻ x, ‖partL (κ' := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) ∧
    (∀ μ : @Measure (κ' ⊕ κ → AF F) (borel _), @Measure.IsAddHaarMeasure _ _ _ (borel _) μ →
      ∃ c : ℝ≥0∞, ∀ Φ ∈ schA F (κ' ⊕ κ), ∫⁻ x, ‖partR (κ := κ') A Φ x‖ₑ ^ 2 ∂μ = c * ∫⁻ x, ‖Φ x‖ₑ ^ 2 ∂μ) := by
  first | exact @GlobalTheory.DoublingEvaluationL2.main | exact GlobalTheory.DoublingEvaluationL2.main | (intros; apply GlobalTheory.DoublingEvaluationL2.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartzStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open scoped TensorProduct
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open ValuativeRel

open scoped GlobalTheory.VacAny
open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.weil_representation_preserves_schwartz : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n} {Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d} (M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y)
    (ψ : AddChar (AF F) ℂ), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsStd ψ →
    ∀ (γ : Matrix (Fin n) (Fin d) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.AE (F := F) (E := E))), ∀ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d),
      M.co.rho ψ γ Φ ∈ GlobalTheory.WeilM.schA F (Fin n × Fin d) := by
  first | exact @GlobalTheory.HeisSchA.rho_mem_schA | exact GlobalTheory.HeisSchA.rho_mem_schA | (intros; apply GlobalTheory.HeisSchA.rho_mem_schA <;> assumption)
end

