module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0521
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegerExponentSectionEqZeroOfIncreasingFlag
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsProbabilityMeasureMuPart
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1308
public import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0184
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1725
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0211
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1800
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1860
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1758
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0793
public import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0012
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1345
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1480
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1351
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1450
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1488
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1719
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1473
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContDiffThetaTransformArchimedeanCm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1801
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1859
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0776
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0056
public import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0045

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousOnReadingIntegerExponentSection
section
set_option autoImplicit false

noncomputable section

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_succ_mem_secZ {e : Ix Dw → ℤ} {g : Rul Xo c} (hg : g ∈ secZ Xo c e) (m : ℕ) :
    g ^ (m + 1) ∈ secZ Xo c ((m + 1) • e) := by
  induction m with
  | zero => simpa using hg
  | succ m ih =>
    rw [pow_succ, succ_nsmul]
    exact mul_mem_secZ ih hg

theorem differentiableOn_rdU_of_antitone {σ : c.F →+* ℂ} {r : ℕ} {U : Unf Xo c σ r} (hU : IsUnf U)
    (hpq : 1 ≤ Dw.p + Dw.q) {e : Ix Dw → ℤ} (he0 : e none = 0)
    (hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩))
    {f : Rul Xo c} (hf : f ∈ secZ Xo c e) (k : U.Comp) : DifferentiableOn ℂ (rdU U f k) (U.X k).dom := by
  intro x hx
  have ho : IsOpen (U.X k).dom := FourierCoefficientDomain.isOpen_dom _
  obtain ⟨n, hn, g, hg, hg0⟩ := GlobalTheory.TrueCx.FlatConst.exists_sec_four hpq (U.un k ⟨x, hx⟩)
  set M : ℕ := ∑ i : Ix Dw, (e i).natAbs with hMdef
  have hM : ∀ i, -(4 * ((M + 1 : ℕ) : ℤ)) ≤ e i := fun i => by
    have h1 : (e i).natAbs ≤ M := Finset.single_le_sum (f := fun i => (e i).natAbs) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ i)
    have h2 : -((e i).natAbs : ℤ) ≤ e i := by
      have := Int.natAbs_abs (e i); rw [← Int.abs_eq_natAbs]; exact neg_abs_le _
    have h3 : ((e i).natAbs : ℤ) ≤ M := by exact_mod_cast h1
    push_cast; linarith
  let a : (E →+* ℂ) × ℕ → ℕ := fun p =>
    if h : p.2 < Dw.mult p.1 then (4 * ((M + 1 : ℕ) : ℤ) + e (some ⟨p.1, ⟨p.2, h⟩⟩)).toNat else 0
  have hdom : Dom a ((M + 1) * n) := by
    refine ⟨fun τ i j hij => ?_, hn.mul_left _⟩
    show a (τ, j) ≤ a (τ, i)
    simp only [a]
    by_cases hj : j < Dw.mult τ
    · have hi : i < Dw.mult τ := lt_of_le_of_lt hij hj
      rw [dif_pos hj, dif_pos hi]
      exact Int.toNat_le_toNat (by linarith [hanti τ ⟨i, hi⟩ ⟨j, hj⟩ hij])
    · rw [dite_eq_right hj]; exact Nat.zero_le _
  have hgp := pow_succ_mem_secZ (Xo := Xo) (c := c) (by rw [secZ_nat]; exact hg) M
  have hgf : g ^ (M + 1) * f ∈ sec Xo c a ((M + 1) * n) := by
    rw [← secZ_nat]
    convert mul_mem_secZ hgp hf using 2
    funext i
    rcases i with _ | ⟨τ, i⟩
    · simp [ex, he0]
    · have hi := i.2
      rw [Pi.add_apply, Pi.smul_apply]
      simp only [ex, a, dif_pos hi, nsmul_eq_mul]
      rw [Int.toNat_of_nonneg (by linarith [hM (some ⟨τ, i⟩)])]
      push_cast
      ring
  have d1 := (hU.2.2.2.2.1 _ n ⟨fun _ _ _ _ => le_rfl, hn⟩ g hg k).1
  have d2 := (hU.2.2.2.2.1 _ _ hdom _ hgf k).1
  have hx0 : rdU U g k x ≠ 0 := by
    have : rdU U g k x = toC (evR Xo c g (U.un k ⟨x, hx⟩)) := dif_pos hx
    rwa [this]
  have a1 := d1.differentiableAt (ho.mem_nhds hx)
  have a2 := d2.differentiableAt (ho.mem_nhds hx)
  refine ((a2.mul ((a1.pow (M + 1)).inv (pow_ne_zero _ hx0))).congr_of_eventuallyEq ?_).differentiableWithinAt
  filter_upwards [a1.continuousAt.eventually_ne hx0] with y hy0
  have e1 : rdU U (g ^ (M + 1) * f) k y = rdU U g k y ^ (M + 1) * rdU U f k y := by
    rw [rdU_mul]
    have : ∀ m : ℕ, rdU U (g ^ (m + 1)) = rdU U g ^ (m + 1) := fun m => by
      induction m with
      | zero => simp
      | succ m ih => rw [pow_succ g (m + 1), rdU_mul, ih, ← pow_succ]
    rw [this]; rfl
  rw [Pi.mul_apply, Pi.inv_apply, e1, Pi.pow_apply, mul_right_comm, mul_inv_cancel₀ (pow_ne_zero _ hy0), one_mul]

end GlobalTheory.ReadCont

namespace GlobalTheory.ReadCont

open NumberField IsDedekindDomain Module Formalism.BasicNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt
  GlobalTheory.FlatLine GlobalTheory.CompHt GlobalTheory.FlatCore

theorem continuousOn_rdU : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (x : ℝ), Laws U x → ∀ (e : Ix Dw → ℤ), e none = 0 → ∀ s ∈ secZ Xo c e, ∀ σ, GoodEmb c σ → ∀ k, ContinuousOn (rdU (U σ) s k) ((U σ).X k).dom := by
  intro E _ _ _ H Dw l Xo c r U x hL e he0 s hs σ hσ k
  by_cases hanti : ∀ τ (i j : Fin (Dw.mult τ)), i ≤ j → e (some ⟨τ, j⟩) ≤ e (some ⟨τ, i⟩)
  · exact (differentiableOn_rdU_of_antitone (hL.unf σ hσ) hL.pos he0 hanti hs k).continuousOn
  · push_neg at hanti
    obtain ⟨τ, i, j, hij, hlt⟩ := hanti
    have hij' : i < j := lt_of_le_of_ne hij (by rintro rfl; exact lt_irrefl _ hlt)
    rw [_root_.GlobalTheory.IncrZero.secZ_eq_zero_of_lt E H Dw l Xo c e τ i j hij' hlt s hs, map_zero]
    exact continuousOn_const

end GlobalTheory.ReadCont
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousTransportedWeilOperatorGroupVariable
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

namespace GlobalTheory.WeilCont

theorem continuous_transport_apply : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ), IsStdChar D ψ (-1) →
    ∀ (S T : HSp D) (χS χT : (AE D)ˣ →* Circle), IsHeckeChar D χS → IsHeckeChar D χT →
      ResEta D χS S.rank → ResEta D χT T.rank →
      ∀ (JA : Matrix (Fin T.rank) (Fin T.rank) D.host.E) (JB : Matrix (Fin S.rank) (Fin S.rank) D.host.E)
        (ξ : AF D.host.F ⊗[D.host.F] D.host.E), JA = T.gramᵀ →
        ξ • incM D.host.F JB = incM D.host.F (D.host.xi0 • S.gram⁻¹) →
        ∀ (κ : Type) [Fintype κ]
          (co : GlobalTheory.WeilM.Darboux (GlobalTheory.WeilM.symp (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) ξ (incM D.host.F JA) (incM D.host.F JB)) κ),
          (∀ x : Matrix (Fin T.rank) (Fin S.rank) D.host.E, ∃ y z : κ → D.host.F,
            co.e (incM D.host.F x) = (fun i => algebraMap D.host.F (AF D.host.F) (y i), fun i => algebraMap D.host.F (AF D.host.F) (z i))) →
          ∀ ω : GA D S × GA D T →* Module.End ℂ (Formalism.IndefR.Datum.WO S T → ℂ),
            Formalism.IndefR.Datum.IsWeilDatumO ψ S T χS χT ω →
 ∀ om : GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JA) ×
      GlobalTheory.WeilM.UG (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.cA D.sp.cm.sig) (incM D.host.F JB) →* Module.End ℂ ((κ → AF D.host.F) → ℂ),
                       GlobalTheory.WeilSchrodinger.IsTransport ψ co ω om →
  ∀ Φ ∈ GlobalTheory.WeilM.schA D.host.F κ, ∀ z : κ → AF D.host.F, Continuous fun p => om p Φ z := by
  intro D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ _ co hco ω hω om htr Φ hΦ z
  have hth := _root_.GlobalTheory.ThetaTransportCont.thetaTr_om_continuous D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    _root_.GlobalTheory.WeilCont.exists_local_finite_parts D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace D.host.F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, GlobalTheory.WeilM.pureA D.host.F (f p i) (g i) := fun p hp => by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin D.host.F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      _root_.GlobalTheory.WeilCont.slice_bounds D ψ hψ S T χS χT hS hT rS rT JA JB ξ hJA hJB κ co hco ω hω om htr Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := _root_.GlobalTheory.SchwartzMajorant.exists_summable_majorant D.host.F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → D.host.F) → AddChar (κ → AF D.host.F) ℂ := fun a =>
    ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = ψ ((fun i => algebraMap D.host.F (AF D.host.F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) =
      ψ (⅟(2 : AF D.host.F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j) := by
    intro p y'
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → D.host.F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.1.2.2.2
    refine ⟨Pi.single i (algebraMap D.host.F (AF D.host.F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF D.host.F, ψ (-t) * ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, ψ (-(⅟(2 : AF D.host.F) * (z ⬝ᵥ y'))) *
          GlobalTheory.WeilSchrodinger.thetaTr D.host.F co ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap D.host.F (AF D.host.F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := _root_.GlobalTheory.continuousAt_charSeries_coef_zero e (fun a y => hψ.1.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL

end GlobalTheory.WeilCont
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousWeilDatumTransportCmApply
section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped Classical

namespace GlobalTheory.WeilContF

open Formalism.IndefR.DatumF

theorem continuous_transportF_apply : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E),
    B.IsGood σ → ∀ (nS nT : ℕ) (JS : Matrix (Fin nS) (Fin nS) E) (JT : Matrix (Fin nT) (Fin nT) E),
      IsHermND σ JS → IsHermND σ JT → ∀ ξ₀ : E, ξ₀ ≠ 0 → σ ξ₀ = -ξ₀ →
      ∀ (χS χT : (AF F ⊗[F] E)ˣ →* Circle), Formalism.IndefR.DatumF.IsHeckeCharF χS → Formalism.IndefR.DatumF.IsHeckeCharF χT →
        Formalism.IndefR.DatumF.ResEtaF χS nS → Formalism.IndefR.DatumF.ResEtaF χT nT →
        ∀ ω : Formalism.IndefR.DatumF.GAF σ JS × Formalism.IndefR.DatumF.GAF σ JT →* Module.End ℂ (Formalism.IndefR.DatumF.WOF F E nS nT → ℂ),
        Formalism.IndefR.DatumF.IsWeilDatumOF σ JS JT (fun w : InfinitePlace F => (B.emb w).1) ξ₀ B.ψ χS χT ω →
        ∀ (JA : Matrix (Fin nT) (Fin nT) E) (JB : Matrix (Fin nS) (Fin nS) E) (ξ : AF F ⊗[F] E), JA = JTᵀ →
          ξ • incM F JB = incM F (ξ₀ • JS⁻¹) →
          ∀ (κ : Type) [Fintype κ] (co : Darboux (symp (cA σ) ξ (incM F JA) (incM F JB)) κ),
            (∀ x : Matrix (Fin nT) (Fin nS) E, ∃ y z : κ → F,
              co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
            ∀ om : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB) →* Module.End ℂ ((κ → AF F) → ℂ),
              GlobalTheory.WeilSchrodinger.IsTransportF σ B.ψ co ω om → ∀ Φ ∈ schA F κ, ∀ z : κ → AF F, Continuous fun p => om p Φ z := by
  intro F E _ _ _ _ _ σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ _ co hco om htr
    Φ hΦ z
  have hstd := hω.std
  have hψ := hstd.1

  have hth : ∀ w, Continuous fun p => GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w := by
    intro w
    have hex : ∀ p : UG (cA σ) (incM F JA) × UG (cA σ) (incM F JB),
        ∃ (g : GAF σ JS) (h : GAF σ JT),
          mtF σ JT h = p.1.1.1 ∧ mtF σ JS g = (p.2⁻¹).1.1ᵀ := fun p =>
      _root_.GlobalTheory.WeilPairPartnerF.pair_partnerF F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB p.1 p.2
    choose g h hh hg using hex
    have hθ : IsThetaFunOF σ JS JT ξ₀ B.ψ (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) :=
      ⟨_root_.GlobalTheory.ThetaQuasiRatF.thetaTr_ratWF_add F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        GlobalTheory.T.thetaTransform_adelicSchwartz_hasFiniteLevel_CM F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        _root_.GlobalTheory.ThetaTrContF.continuous_thetaTrF F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ,
        _root_.GlobalTheory.ThetaSmoothF.contDiff_thetaTr_realF F E σ B hB hstd nS nT JS JT hJS hJT ξ₀ hξ0 hσξ JA JB ξ hJA hJB κ co hco Φ hΦ⟩
    have hhU : ∀ p, matHomF σ JT (h p) = p.1.1 := fun p => Units.ext (hh p)
    have hgU : ∀ p, (matHomF σ JS (g p))⁻¹.1 = p.2.1.1ᵀ := by
      intro p
      apply Units.inv_eq_of_mul_eq_one_right
      change mtF σ JS (g p) * _ = 1
      rw [hg p, ← Matrix.transpose_mul, Subgroup.coe_inv, Units.mul_inv, Matrix.transpose_one]
    have hcH' : Continuous fun p => matHomF σ JT (h p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JT (h p)) = fun p => p.1.1.1 := funext fun p => hh p
        rw [e]
        exact Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
      · have e : (fun p => (matHomF σ JT (h p))⁻¹.1) = fun p => (p.1.1)⁻¹.1 := funext fun p => by rw [hhU p]
        rw [e]
        exact Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_fst)
    have hcG' : Continuous fun p => matHomF σ JS (g p) := by
      refine Units.continuous_iff.2 ⟨?_, ?_⟩
      · have e : (Units.val ∘ fun p => matHomF σ JS (g p)) = fun p => ((p.2.1)⁻¹).1ᵀ := funext fun p => hg p
        rw [e]
        exact (Units.continuous_coe_inv.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
      · have e : (fun p => (matHomF σ JS (g p))⁻¹.1) = fun p => p.2.1.1ᵀ := funext hgU
        rw [e]
        exact (Units.continuous_val.comp (continuous_subtype_val.comp continuous_snd)).matrix_transpose
    have hcH : Continuous h := continuous_induced_rng.2 hcH'
    have hcG : Continuous g := continuous_induced_rng.2 hcG'
    have heq : ∀ p, GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) w =
        ω (g p, h p) (GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ Φ) w := fun p =>
      congrFun (htr p.1 p.2 (g p) (h p) (hh p) (hg p) Φ hΦ).2 w
    exact ((hω.om_cont _ hθ w).comp (hcG.prodMk hcH)).congr fun p => (heq p).symm
  refine continuous_iff_continuousAt.2 fun p0 => ?_
  obtain ⟨N, hN, m, g, y, hg, hy, hf⟩ :=
    _root_.GlobalTheory.WeilContF.exists_local_finite_parts_F F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr Φ hΦ p0
  let f : _ → Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ :=
    fun p => if h : p ∈ N then Classical.choose (hf p h) else 0
  have hfe : ∀ p ∈ N, om p Φ = ∑ i, pureA F (f p i) (g i) := fun p hp => by
    simp only [f, dif_pos hp]
    exact Classical.choose_spec (hf p hp)
  have hslice : ∀ p ∈ N, ∀ i v, f p i v = om p Φ (GlobalTheory.WeilCont.adeleJoin F v (y i)) := by
    intro p hp i v
    rw [hfe p hp, Finset.sum_apply, Finset.sum_eq_single i]
    · rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_pos rfl, mul_one]
    · intro j _ hji
      rw [GlobalTheory.WeilCont.pureA_adeleJoin, hy, if_neg hji, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hbd : ∀ k : ℕ, ∃ C : ℝ, ∀ᶠ p in nhds p0, ∀ i v, ‖v‖ ^ k * ‖f p i v‖ ≤ C := by
    intro k
    choose C hC using fun i =>
      _root_.GlobalTheory.WeilContF.slice_bounds F E σ B hB nS nT JS JT hJS hJT ξ₀ hξ0 hσξ χS χT hS hT rS rT ω hω JA JB ξ hJA hJB κ co hco om htr
        Φ hΦ (y i) p0 k 0
    refine ⟨∑ i, |C i|, ?_⟩
    filter_upwards [Filter.eventually_all.2 hC, hN] with p hp hpN i v
    have h1 := hp i v
    rw [norm_iteratedFDeriv_zero] at h1
    rw [hslice p hpN i v]
    exact h1.trans ((le_abs_self _).trans
      (Finset.single_le_sum (f := fun i => |C i|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)))
  obtain ⟨M, hM, hMb⟩ := GlobalTheory.SchwartzMajorant.exists_summable_majorant F κ (fun p => om p Φ) p0 m g f hg
    (Filter.eventually_of_mem hN fun p hp => hfe p hp) hbd z
  let e : (κ → F) → AddChar (κ → AF F) ℂ := fun a =>
    B.ψ.compAddMonoidHom (AddMonoidHom.mk' (fun y => (fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y)
      (fun y y' => dotProduct_add _ y y'))
  have he : ∀ a y, e a y = B.ψ ((fun i => algebraMap F (AF F) (a i)) ⬝ᵥ y) := fun a y => rfl
  have hform : ∀ p y', GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
      B.ψ (⅟(2 : AF F) * (z ⬝ᵥ y')) * ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
    intro p y'
    simp only [GlobalTheory.WeilSchrodinger.thetaTr, GlobalTheory.WeilM.thetaSum, GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr,
      LinearEquiv.apply_symm_apply, he]
    rw [← tsum_mul_left]
    refine tsum_congr fun a => ?_
    simp only [AddChar.map_add_eq_mul, Pi.add_def]
    ring
  have h0 : ∀ y, e 0 y = 1 := fun y => by
    rw [he]
    simp
  have hne : ∀ a : κ → F, a ≠ 0 → ∃ y, e a y ≠ 1 := by
    intro a ha
    obtain ⟨i, hi⟩ := Function.ne_iff.1 ha
    obtain ⟨x0, hx0⟩ := hψ.2.2.2
    refine ⟨Pi.single i (algebraMap F (AF F) (a i)⁻¹ * x0), ?_⟩
    rw [he, dotProduct_single, ← mul_assoc, ← map_mul, mul_inv_cancel₀ hi, map_one, one_mul]
    exact hx0
  have hψinv : ∀ t : AF F, B.ψ (-t) * B.ψ t = 1 := fun t => by
    simpa using (AddChar.map_add_eq_mul B.ψ (-t) t).symm
  have hc : ∀ y', ContinuousAt (fun p => ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j)) p0 := by
    intro y'
    have h2 : ∀ p, B.ψ (-(⅟(2 : AF F) * (z ⬝ᵥ y'))) *
          GlobalTheory.WeilSchrodinger.thetaTr F co B.ψ (om p Φ) (co.e.symm (z, y')) =
        ∑' a, e a y' * om p Φ (fun j => algebraMap F (AF F) (a j) + z j) := by
      intro p
      simp only [hform, ← mul_assoc, hψinv, one_mul]
    exact ((continuous_const.mul (hth _)).continuousAt).congr (Filter.Eventually.of_forall h2)
  have hL := GlobalTheory.continuousAt_charSeries_coef_zero e (fun a y => hψ.2.1 _) h0 hne _ p0 M hM hMb hc
  simpa using hL

end GlobalTheory.WeilContF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeFromGramAndBounds
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.AllWt GlobalTheory.BigTop Filter Topology

namespace GlobalTheory.CovTop.Assembly

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem tendsto_exp_mul_rpow {c : ℝ} (hc : 0 < c) (A : ℝ) :
    Tendsto (fun x : ℝ => Real.exp (-(x ^ c)) * x ^ A) atTop (𝓝 0) := by
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (A / c) 1 one_pos).comp (tendsto_rpow_atTop hc)
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with x hx
  simp only [Function.comp]
  rw [← Real.rpow_mul hx, mul_div_cancel₀ _ hc.ne', mul_comm, neg_mul, one_mul]

theorem exists_loss_le {c : ℝ} (hc : 0 < c) (A B C : ℝ) :
    ∃ x0 : ℝ, ∀ x, x0 ≤ x → 12 * Real.exp (-(x ^ c)) * (x ^ A + x ^ B + C) ≤ 1 := by
  have h := ((((tendsto_exp_mul_rpow hc A).add (tendsto_exp_mul_rpow hc B)).add
    ((tendsto_exp_mul_rpow hc 0).mul_const C)).const_mul 12)
  have h1 : (12 : ℝ) * (0 + 0 + 0 * C) < 1 := by norm_num
  obtain ⟨x0, hx0⟩ := eventually_atTop.1 (h.eventually (gt_mem_nhds h1))
  refine ⟨x0, fun x hx => ?_⟩
  have := hx0 x hx
  simp only [Real.rpow_zero] at this
  nlinarith

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y0 : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y0 cX} {Csz : ℝ} (p : PtAt ex Csz) (i : Fin D.R.m)

theorem lcv_le {A B PP C1 C2 : ℝ} (hx : 0 < L.sc.x) (h1 : 0 ≤ C1) (h2 : 0 ≤ C2)
    (hs : 12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * (L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) ≤ 1)
    (hG : GramAt p i) (hR : RecAt p i) (hC : CutAt p i) (hB : BadAt p i) (hL : LamAt p i A) (hS : SizeAt p i PP B)
    (hK : CoreAt p i C1) (hW : LowAt p i C2) :
    Formalism.DivisionValues.lcv ((p.S false).XW i) ((p.S false).M i) / ((p.S false).D : ℝ) ≤ mainT p i + (C1 + C2 + 1) * unitE p := by
  haveI : IsTotallyComplex D.what₂.LL := D.tcLL
  obtain ⟨g1, g2, g3, -⟩ := hG
  obtain ⟨c1, c2, c3, c4⟩ := hC
  obtain ⟨s1, s2, -, s4, -⟩ := hS
  unfold RecAt at hR
  unfold LamAt at hL
  unfold CoreAt at hK
  unfold LowAt at hW
  have hA := Real.rpow_pos_of_pos hx A
  have hB' := Real.rpow_pos_of_pos hx B
  have hδ := Real.exp_pos (-(L.sc.x ^ (L.sc.ez / 7)))
  have hm := (abs_le.1 s4).2
  have key := GlobalTheory.CutNum.slope_good_ge D.what₂.LL _ (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i)
    (latAll p.R.toRealDat i) (eGood p.R.toRealDat i) (Fintype.card p.P.Gp) (Real.exp (-(L.sc.x ^ (L.sc.ez / 7))))
    ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) g1 g2 inf_le_left
    (fun h => g3 (le_bot_iff.1 (h ▸ latGood_le p.R.toRealDat p.F.lv2 i))) c1 c2 Fintype.card_pos c3 hδ.le
  have key' : slope_sq (nrmR p.R.toRealDat i) (latType p.R.toRealDat p.F.lv2 i) -
      12 * Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) * ((L.sc.x ^ A + L.sc.x ^ B + (C1 + C2 + 1)) * unitE p) ≤
      slope_sq (nrmR p.R.toRealDat i) (latGood p.R.toRealDat p.F.lv2 i) := by
    refine key ?_ hB ?_ ?_ ?_
    all_goals
      clear key hR
      generalize Real.exp (-(L.sc.x ^ (L.sc.ez / 7))) = δ at *
      generalize L.sc.x ^ A = a at *
      generalize L.sc.x ^ B = b at *
      generalize unitE p = E at *
      have hE : 0 ≤ E := by linarith
      have ea := mul_le_mul_of_nonneg_left s2 hA.le
      have eb := mul_le_mul_of_nonneg_left s2 hB'.le
      have e1 := mul_nonneg h1 hE
      have e2 := mul_nonneg h2 hE
      have e3 := mul_nonneg hA.le hE
      have e4 := mul_nonneg hB'.le hE
    · nlinarith [mul_nonneg hδ.le hA.le, mul_nonneg hδ.le hB'.le, mul_nonneg hδ.le h1, mul_nonneg hδ.le h2]
    · linarith
    · linarith
    · linarith
  have hE : 0 ≤ unitE p := by linarith
  have := mul_le_mul_of_nonneg_right hs hE
  rw [mul_assoc] at this
  linarith

end GlobalTheory.CovTop.Assembly

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComponentIntegralFramedPointLiesOn
section
open GlobalTheory.IndefiniteRowSideFullHecke.DifferentConjugateDefects NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AllWt GlobalTheory.FlatLine GlobalTheory.FlatTw GlobalTheory.SlopeRec GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.RefSum

namespace GlobalTheory.IntFrComp

open AlgebraicGeometry

theorem exists_liesOn : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io), ∃ Z : Comp Xo c, (letI := io.toAlgebra; LiesOn Z y.1) := by
  intro E _ _ _ H Dw l Xo c T io y
  letI := io.toAlgebra
  let s₀ : Sp T.Fr := (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum T.Fr)
  refine ⟨⟨irreducibleComponent (GlobalTheory.AllWt.ptF y.1 s₀), irreducibleComponent_mem_irreducibleComponents _⟩,
    fun s => ?_⟩
  obtain rfl : s = s₀ := Subsingleton.elim (α := PrimeSpectrum T.Fr) s s₀
  exact mem_irreducibleComponent

end GlobalTheory.IntFrComp
end

