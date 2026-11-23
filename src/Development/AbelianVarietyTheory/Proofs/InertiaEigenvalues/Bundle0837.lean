module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0808
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DifferentiableIntegralMulCpow
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0025
public import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
public import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.SqNormIntegralFundamentalDomainEqL2NormSq
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockVectorsOverVacuaDenseThetaFunctions
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0362
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1016
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0142
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0119
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsHeisenbergCombinationProjectsOntoVacuum
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0715

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SummableNonzeroRationalVectorLeShortestVector
section
noncomputable section

open NumberField Matrix MeasureTheory GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.ThetaPoisson GroundTheory.Global
  GroundTheory.Global.IdeleGroup
open scoped ComplexConjugate nonZeroDivisors ContDiff

namespace GlobalTheory.RSTheta

theorem summable_tsum_norm_le_of_le_shortest (E : Type) [Field E] [NumberField E] [_root_.NumberField.IsTotallyComplex E] (a : ℕ)
    (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ) (N : ℕ) (hN : Module.finrank ℝ (Fin a → Cinf E) ≤ N) :
    ∃ (M : ℕ) (C : ℝ), ∀ (h : GA E a) (A : ℝ) (c : (Fin a → E) → ℂ), 0 ≤ A →
      (∀ ξ : Fin a → E, (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)) ∉ latt a J →
        c ξ = 0) →
      (∀ ξ ξ' : Fin a → E, ξ' ≠ 0 →
        (fun i => pFin E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)) ∈ latt a J →
        ‖c ξ‖ * (1 + ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ j)) ᵥ* h.val) i)‖) ^ M ≤
          A * ‖fun i => pInf E (((fun j => algebraMap E (Ad E) (ξ' j)) ᵥ* h.val) i)‖ ^ N) →
      Summable (fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∧
        ∑' ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ ≤ C * A := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · haveI : IsEmpty {ξ : Fin 0 → E // ξ ≠ 0} := ⟨fun ξ => ξ.2 (Subsingleton.elim _ _)⟩
    exact ⟨0, 0, fun _ _ _ _ _ _ => ⟨summable_empty, by simp⟩⟩
  set D := Module.finrank ℝ (Fin a → Cinf E) with hD
  have hD1 : 1 ≤ D := by rw [hD, finrank_pi_Cinf]; exact Nat.mul_pos ha Module.finrank_pos
  have hND : (D : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨K, hK, hlat⟩ := GlobalTheory.LatticeCount.tsum_one_add_norm_rpow_neg_le_regimes (V := Fin a → Cinf E)
    hD1 (M := ((N + D + 1 : ℕ) : ℝ)) (by push_cast; linarith)
  rw [← hD] at hlat
  refine ⟨N + D + 1, 2 ^ N * K, fun g A c hA hsupp hdec => ?_⟩
  let T : (Fin a → E) →+ (Fin a → Ad E) :=
    { toFun := fun ξ => (fun j => algebraMap E (Ad E) (ξ j)) ᵥ* g.val
      map_zero' := by simp only [Pi.zero_apply, map_zero]; exact zero_vecMul _
      map_add' := fun x y => by simp only [Pi.add_apply, map_add (f := _)]; exact add_vecMul _ _ _ }
  let TI : (Fin a → E) →+ (Fin a → Cinf E) := ((pInf E).toAddMonoidHom.compLeft (Fin a)).comp T
  let TF : (Fin a → E) →+ (Fin a → Af E) := ((pFin E).toAddMonoidHom.compLeft (Fin a)).comp T
  let P : AddSubgroup (Fin a → E) := (AddSubgroup.pi Set.univ fun _ => idealFiniteAdeles J).comap TF
  have hP : ∀ ξ, ξ ∈ P ↔ TF ξ ∈ latt a J := fun ξ => ⟨fun h i => h i trivial, fun h i _ => h i⟩
  obtain ⟨δ, hδ, hδle⟩ := exists_le_norm g (isCompact_latt J)
  replace hδle : ∀ ξ ∈ P, ξ ≠ 0 → δ ≤ ‖TI ξ‖ := fun ξ h h0 => hδle ξ h0 ((hP ξ).1 h)
  have hsP : ∀ ξ, c ξ ≠ 0 → ξ ∈ P := fun ξ h => (hP ξ).2 (by_contra fun h' => h (hsupp ξ h'))
  set S : Set ℝ := (fun ξ => ‖TI ξ‖) '' {ξ | ξ ∈ P ∧ ξ ≠ 0} with hS
  rcases S.eq_empty_or_nonempty with hS0 | hS0
  · have : ∀ ξ : {ξ : Fin a → E // ξ ≠ 0}, ‖c ξ‖ = 0 := fun ξ => by
      by_contra h
      exact Set.eq_empty_iff_forall_notMem.1 hS0 _ ⟨ξ.1, ⟨hsP _ (norm_ne_zero_iff.1 h), ξ.2⟩, rfl⟩
    simp only [this, tsum_zero]
    exact ⟨summable_zero, by positivity⟩
  have hr : 0 < sInf S := hδ.trans_le (le_csInf hS0 (by rintro _ ⟨ξ, hξ, rfl⟩; exact hδle ξ hξ.1 hξ.2))
  have hrle : ∀ ξ ∈ P, ξ ≠ 0 → sInf S ≤ ‖TI ξ‖ := fun ξ h h0 =>
    csInf_le ⟨0, by rintro _ ⟨ξ, -, rfl⟩; exact norm_nonneg _⟩ ⟨ξ, ⟨h, h0⟩, rfl⟩
  obtain ⟨_, ⟨ξ₀, hξ₀, rfl⟩, hlt⟩ := exists_lt_of_csInf_lt hS0 (show sInf S < 2 * sInf S by linarith)
  generalize sInf S = r at hr hrle hlt
  obtain ⟨hsum, hlo, hhi⟩ := hlat (P.map TI) r hr (by
    rintro _ ⟨ξ, hξ, rfl⟩ h0
    exact hrle ξ hξ fun e => h0 (by rw [e, map_zero]))
  set B : ℝ := A * (2 * r) ^ N with hB
  have hB0 : 0 ≤ B := by positivity
  have hterm : ∀ ξ, ‖c ξ‖ ≤ B * (1 + ‖TI ξ‖) ^ (-(((N + D + 1 : ℕ)) : ℝ)) := fun ξ => by
    have h1 := hdec ξ ξ₀ hξ₀.2 ((hP _).1 hξ₀.1)
    have hpos : 0 < (1 + ‖TI ξ‖) ^ (N + D + 1) := by positivity
    rw [Real.rpow_neg (by positivity), Real.rpow_natCast, ← div_eq_mul_inv, le_div_iff₀ hpos]
    refine h1.trans (mul_le_mul_of_nonneg_left ?_ hA)
    exact pow_le_pow_left₀ (norm_nonneg _) hlt.le _
  let j : {ξ // ξ ∈ P ∧ ξ ≠ 0} → {ξ : Fin a → E // ξ ≠ 0} := fun ξ => ⟨ξ.1, ξ.2.2⟩
  have hj : Function.Injective j := fun x y h => Subtype.ext (congrArg (fun z : {ξ : Fin a → E // ξ ≠ 0} => z.1) h)
  have hjs : ∀ ξ ∉ Set.range j, ‖c ξ‖ = 0 := fun ξ h => by
    by_contra h'
    exact h ⟨⟨ξ.1, hsP _ (norm_ne_zero_iff.1 h'), ξ.2⟩, rfl⟩
  let ι : {ξ // ξ ∈ P ∧ ξ ≠ 0} → ((P.map TI : Set (Fin a → Cinf E)) \ {0} : Set (Fin a → Cinf E)) := fun ξ =>
    ⟨TI ξ.1, ⟨ξ.1, ξ.2.1, rfl⟩, norm_pos_iff.1 (hr.trans_le (hrle _ ξ.2.1 ξ.2.2))⟩
  have hι : Function.Injective ι := fun x y h => Subtype.ext (by
    by_contra hne
    have h1 := hrle _ (P.sub_mem x.2.1 y.2.1) (sub_ne_zero.2 hne)
    rw [map_sub, show TI x.1 = TI y.1 from congrArg Subtype.val h, sub_self, norm_zero] at h1
    exact h1.not_gt hr)
  have hs1 := (hsum.mul_left B).comp_injective hι
  have hs2 : Summable ((fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) ∘ j) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun ξ => hterm ξ.1) hs1
  refine ⟨(hj.summable_iff hjs).1 hs2, ?_⟩
  rw [← hj.tsum_eq (f := fun ξ : {ξ : Fin a → E // ξ ≠ 0} => ‖c ξ‖) fun ξ h => by_contra fun h' => h (hjs ξ h')]
  refine (Summable.tsum_le_tsum_of_inj ι hι (fun _ _ => by positivity) (fun ξ => hterm ξ.1) hs2
    (hsum.mul_left B)).trans ?_
  rw [tsum_mul_left]
  have key : ∀ e : ℝ, r ^ ((N : ℝ) + e) ≤ 1 → B * (K * r ^ e) ≤ 2 ^ N * K * A := by
    intro e he
    calc B * (K * r ^ e) = 2 ^ N * K * A * r ^ ((N : ℝ) + e) := by
          rw [hB, Real.rpow_add hr, Real.rpow_natCast, mul_pow]; ring
      _ ≤ _ := mul_le_of_le_one_right (by positivity) he
  rcases le_total r 1 with h1 | h1
  · exact (mul_le_mul_of_nonneg_left (hlo h1) hB0).trans (key _ (Real.rpow_le_one hr.le h1 (by linarith)))
  · exact (mul_le_mul_of_nonneg_left (hhi h1) hB0).trans
      (key _ (Real.rpow_le_one_of_one_le_of_nonpos h1 (by push_cast; linarith)))

end GlobalTheory.RSTheta
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaFunctionFixedFinitePartSobolevLimitFockVect
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift

namespace GlobalTheory.FinLikeClosure

open GlobalTheory.ChainFr GlobalTheory.Size

theorem fix_of_finLike {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} {i : Fin D.R.m} {t : T}
    {f : WO (Vc D i) (Wc D i) → ℂ} (hf : FinLike R i t f) (c : WO (Vc D i) (Wc D i) →₀ ℂ)
    (hc : ∀ u ∈ c.support, u.map (infPart D) = 0)
    (hv : (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u (R.vP i t)) = R.vP i t) :
    (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u f) = f := by
  have key : ∀ g : WO (Vc D i) (Wc D i) → ℂ, ((c - Finsupp.single 0 1).sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u g) =
      (c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u g) - g := fun g => by
    rw [Finsupp.sum_sub_index (fun _ _ _ => sub_smul _ _ _), Finsupp.sum_single_index (by rw [zero_smul]), one_smul,
      GlobalTheory.OrientedHeis.heisO_zero]
  classical
  have hs : ∀ u ∈ (c - Finsupp.single 0 1).support, u.map (infPart D) = 0 := fun u hu => by
    rcases Finset.mem_union.1 (Finsupp.support_sub hu) with h | h
    · exact hc u h
    · rw [Finset.mem_singleton.1 (Finsupp.support_single_subset h)]
      exact Matrix.map_zero _ (map_zero _)
  have := hf.2 _ hs (by rw [key, hv, sub_self])
  rwa [key, sub_eq_zero] at this

theorem closure : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T : Type) (A : FamIn D.what₂.LL G Pl0 T D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), GlobalTheory.LiftRows.Given R F → R.FullP → ∀ (i : Fin D.R.m) (t : T) (μ : Measure (WO (Vc D i) (Wc D i))) (𝓕 : Set (WO (Vc D i) (Wc D i))), IsCovolOne (ratL (Wc D i) (Vc D i)) μ 𝓕 → ∀ f, FinLike R i t f → ∀ (d : ℕ) (δ : ENNReal), 0 < δ → ∃ P, GlobalTheory.Size.sobO R.ψ R.θ μ 𝓕 d (f - R.ptP i t P) < δ := by
  intro D G _ _ Pl0 T A Ks _ _ _ R F hG _ i t μ 𝓕 hμ f hf d δ hδ
  have hC := hG.core
  have hθ : IsInfFam R.θ := hC.models.inf
  have hψ : IsStdChar D R.ψ (-1) := (hC.thP.ωP i t).std
  let AV := GlobalTheory.WeilReal.frOf (Vc D i) (fun _ => 1) (R.BV i) (fun _ => (Vc D i).rank) (hC.models.BV i)
  let BW := Fr.ofModel (R.MW i (sg0 D A))
  have cAV : AV.cart = fun _ => 1 := GlobalTheory.WeilReal.frOf_cart (hC.models.BV i)
  have oAV : AV.onb = R.BV i := GlobalTheory.WeilReal.frOf_onb (hC.models.BV i)
  have hpt : ∀ x, ptF R.ψ R.θ AV BW x =
      pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) x :=
    fun x => by rw [ptF, cAV, oAV]; rfl
  have hvθ : IsThetaFunO R.ψ (Vc D i) (Wc D i) (R.vP i t) := by
    have := hC.thP.pt_theta i t 1
    unfold RealDat.ptP pureTensorO at this
    rwa [GlobalTheory.AdTh.VecFock.pureTensorL_one] at this
  have hvv : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) (R.vP i t) :=
    GlobalTheory.DatumFock.isFockVacAt_thPVec _ _ _ _ (fun _ => 1) _ _ _ _ _ _ _ _ _ _ (hC.thP.vP i t) hvθ
  have cS : ∀ τ, IsCartanInv (gramAt D (Vc D i) τ) 1 := fun τ => by
    have := Model.isCartanInv_cart AV τ
    rwa [cAV] at this
  have cT : ∀ τ, IsCartanInv (gramAt D (Wc D i) τ) (cart (R.MW i (sg0 D A)) τ) := fun τ => Model.isCartanInv_cart BW τ
  obtain ⟨U, hU, hfU, hdense⟩ := GlobalTheory.FockDensity.fockDense D _ _ AV BW R.θ R.ψ hψ hθ μ 𝓕 hμ f hf.1
  obtain ⟨c, hc0, hcv, hcx⟩ := _root_.GlobalTheory.VacDensity.proj D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ (fun _ => 1) (cart (R.MW i (sg0 D A))) cS cT
    (R.vP i t) hvθ hvv U hU
  let Pf : Module.End ℂ (WO (Vc D i) (Wc D i) → ℂ) :=
    c.sum fun u z => z • GlobalTheory.Hk3.FiniteHeis.heisLin R.ψ (Vc D i) (Wc D i) u
  have hPf : ∀ h, Pf h = c.sum fun u z => z • heisO R.ψ (Vc D i) (Wc D i) u h := fun h =>
    LinearMap.finsupp_sum_apply _ _ _
  have hfix : Pf f = f := (hPf f).trans (fix_of_finLike hf c hc0 hcv)
  let Lp := pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i)
    (onb (R.MW i (sg0 D A))) (R.vP i t)
  have hLp : ∀ P, R.ptP i t P = Lp P := fun _ => rfl

  have himg : ∀ g ∈ fockSpan R.ψ R.θ AV BW U, Pf g ∈ LinearMap.range Lp := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem g hg =>
      obtain ⟨f₀, P, h1, h2, rfl⟩ := hg
      have hv0 : ∀ τ, IsFockVacAt (heisO R.ψ (Vc D i) (Wc D i)) R.θ τ (cplxO 1 (cart (R.MW i (sg0 D A)) τ)) f₀ :=
        fun τ => by
          have := h1.2 τ
          rwa [cAV] at this
      obtain ⟨a, ha⟩ := hcx f₀ h2 hv0
      refine ⟨a • P, ?_⟩
      rw [hPf, hpt, GlobalTheory.FiniteHeisComb.sum_heisO_pureTensorO D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ _ _ _ _ c hc0 f₀ h1.1 P, ha,
        GlobalTheory.FiniteFock.pureTensorO_smul, map_smul]
    | zero => rw [map_zero]; exact zero_mem _
    | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
    | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ a hx
  set C : ENNReal := ∑ u ∈ c.support, ‖c u‖ₑ with hCdef
  have hCt : C ≠ ⊤ := ENNReal.sum_ne_top.2 fun _ _ => eNorm_ne_top
  rcases eq_or_ne C 0 with hC0 | hC0
  · obtain ⟨g, hg, hgU, -⟩ := hdense d 1 one_pos
    obtain ⟨P, hP⟩ := himg g hg
    refine ⟨P, lt_of_le_of_lt ?_ hδ⟩
    have hb := GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ μ 𝓕 hμ c hc0 (f - g) (sub_mem hfU hgU).1 d
    rw [← hCdef, hC0, zero_mul, ← hPf, map_sub, hfix, ← hP, ← hLp] at hb
    exact hb
  · obtain ⟨g, hg, hgU, hgd⟩ := hdense d (δ / C) (ENNReal.div_pos hδ.ne' hCt)
    obtain ⟨P, hP⟩ := himg g hg
    refine ⟨P, ?_⟩
    have hb := GlobalTheory.HeisTranslateBound.sobO_finsupp_sum_le D R.ψ R.θ (Vc D i) (Wc D i) hψ hθ μ 𝓕 hμ c hc0 (f - g) (sub_mem hfU hgU).1 d
    rw [← hCdef, ← hPf, map_sub, hfix, ← hP, ← hLp] at hb
    refine lt_of_le_of_lt hb ?_
    calc C * sobO R.ψ R.θ μ 𝓕 d (f - g) < C * (δ / C) := by simpa only [mul_comm C] using ENNReal.mul_lt_mul_left hC0 hCt hgd
      _ = δ := ENNReal.mul_div_cancel hC0 hCt

end GlobalTheory.FinLikeClosure
end

