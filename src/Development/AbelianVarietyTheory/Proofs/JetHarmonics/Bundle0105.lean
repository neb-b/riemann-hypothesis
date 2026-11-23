module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0011
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0098
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UwEllipticFlow
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0103
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MultiplicativeShiftEqTranslateBySmallPoint
public import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.VRatioGt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FirstCohomology.LevelFrameOfLaws
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ProdSumReindex
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGenOfTop
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0075
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0102
public import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
public import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0101
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0074
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0014
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGap

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.CpTransportedTaylorSeriesShiftEqTranslate
section
open PowerSeries GlobalTheory.MomOne
open scoped ComplexConjugate BigOperators Topology

noncomputable section
namespace GlobalTheory.MomOne.Transfer
variable {q : ℕ} [Fact q.Prime]

def Tr (ι : ℂ ≃+* ℂ_[q]) (ℓ : ℂ_[q]⟦X⟧) (ζ : ℂ_[q]) (p : ℂ) (F : ℂ → ℂ) : Prop :=
  AnalyticAt ℂ F 0 ∧ AnalyticAt ℂ (fun z => F (z + p)) 0 ∧ Bdd (hat ι ℓ F) ∧
    hat ι ℓ (fun z => F (z + p)) = shiftS ζ (hat ι ℓ F)

lemma bdd_add {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f + g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).1⟩

lemma bdd_mul {f g : ℂ_[q]⟦X⟧} (hf : Bdd f) (hg : Bdd g) : Bdd (f * g) := by
  obtain ⟨A, hf⟩ := hf
  obtain ⟨B, hg⟩ := hg
  exact ⟨_, ((sup_norm_laws q).1 f g A B hf hg).2⟩

section
variable {ι : ℂ ≃+* ℂ_[q]} {ℓ : ℂ_[q]⟦X⟧} {ζ : ℂ_[q]} {p : ℂ}

lemma Tr.const (h0 : constantCoeff ℓ = 0) (c : ℂ) : Tr ι ℓ ζ p (fun _ => c) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).2.1 c
  refine ⟨analyticAt_const, analyticAt_const, ⟨‖ι c‖, fun n => ?_⟩, ?_⟩
  · rw [h, coeff_C]
    split_ifs <;> simp
  · rw [h, Shift.shiftS_C]

lemma Tr.add (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z + G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.add g1, f2.add g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).1]; exact bdd_add f3 g3
  · rw [(h _ _ f1 g1).1, (h _ _ f2 g2).1, f4, g4, Shift.shiftS_add hζ f3 g3]

lemma Tr.mul (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F G : ℂ → ℂ} (hF : Tr ι ℓ ζ p F)
    (hG : Tr ι ℓ ζ p G) : Tr ι ℓ ζ p (fun z => F z * G z) := by
  have h := (TaylorRead.hat_laws q ι ℓ h0).1
  obtain ⟨f1, f2, f3, f4⟩ := hF
  obtain ⟨g1, g2, g3, g4⟩ := hG
  refine ⟨f1.mul g1, f2.mul g2, ?_, ?_⟩
  · rw [(h _ _ f1 g1).2.1]; exact bdd_mul f3 g3
  · rw [(h _ _ f1 g1).2.1, (h _ _ f2 g2).2.1, f4, g4, Shift.shiftS_mul hζ f3 g3]

lemma Tr.pow (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {F : ℂ → ℂ} (hF : Tr ι ℓ ζ p F) (n : ℕ) :
    Tr ι ℓ ζ p (fun z => F z ^ n) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 1
  | succ n ih => simpa only [pow_succ] using Tr.mul h0 hζ ih hF

lemma Tr.sum (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) (F : ℕ → ℂ → ℂ) (hF : ∀ i, Tr ι ℓ ζ p (F i))
    (n : ℕ) : Tr ι ℓ ζ p (fun z => ∑ i ∈ Finset.range n, F i z) := by
  induction n with
  | zero => simpa using Tr.const (ι := ι) (ζ := ζ) (p := p) h0 0
  | succ n ih => simpa only [Finset.sum_range_succ] using Tr.add h0 hζ ih (hF n)

lemma exists_homog (h0 : constantCoeff ℓ = 0) (hζ : ‖ζ - 1‖ < 1) {u w : ℂ → ℂ} (hu : Tr ι ℓ ζ p u)
    (hw : Tr ι ℓ ζ p w) (A : Polynomial ℂ) :
    ∃ (k : ℕ) (F : ℂ → ℂ), Tr ι ℓ ζ p F ∧ ∀ z x : ℂ, x * w z = u z → F z = A.eval x * w z ^ k := by
  refine ⟨A.natDegree, fun z => ∑ i ∈ Finset.range (A.natDegree + 1),
    A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)), ?_, fun z x hx => ?_⟩
  · exact Tr.sum h0 hζ (fun i z => A.coeff i * (u z ^ i * w z ^ (A.natDegree - i)))
      (fun i => Tr.mul h0 hζ (Tr.const h0 _) (Tr.mul h0 hζ (hu.pow h0 hζ i) (hw.pow h0 hζ _))) _
  · rw [Polynomial.eval_eq_sum_range, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i hi => ?_
    have hi' : i ≤ A.natDegree := Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)
    obtain ⟨j, hj⟩ := Nat.exists_eq_add_of_le hi'
    rw [← hx, hj, Nat.add_sub_cancel_left]
    ring

lemma exists_quot (h0 : constantCoeff ℓ = 0) (h1 : coeff 1 ℓ ≠ 0) {f D N : ℂ → ℂ} (S : ℂ_[q]⟦X⟧)
    (hf : MeromorphicAt f 0) (hD : AnalyticAt ℂ D 0) (hN : AnalyticAt ℂ N 0)
    (hD0 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), D z ≠ 0) (he : ∀ᶠ z in 𝓝[≠] (0 : ℂ), f z * D z = N z)
    (hS : S * hat ι ℓ D = hat ι ℓ N) :
    ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
  obtain ⟨h, hc, hid, hcc, -⟩ := TaylorRead.hat_laws q ι ℓ h0
  have hDne : hat ι ℓ D ≠ 0 := by
    intro hz
    have e : hat ι ℓ D = hat ι ℓ (fun _ => 0) := by rw [hz, hc]; simp
    have e2 := (h _ _ hD analyticAt_const).2.2.2 h1 e
    obtain ⟨z, hz1, hz2⟩ := (hD0.and (e2.filter_mono nhdsWithin_le_nhds)).exists
    exact hz1 hz2
  have hpow : ∀ n : ℕ, hat ι ℓ (fun z => z ^ n) = ℓ ^ n := by
    intro n
    induction n with
    | zero => simpa using hc 1
    | succ n ih =>
      simp only [pow_succ]
      rw [(h (fun z => z ^ n) (fun z => z) (by fun_prop) (by fun_prop)).2.1, ih, hid]
  have key : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      hat ι ℓ g = ℓ ^ n * S := by
    intro n g hg hge
    apply mul_right_cancel₀ hDne
    rw [mul_assoc, hS, ← hpow, ← (h _ _ hg hD).2.1, ← (h (fun z => z ^ n) N (by fun_prop) hN).2.1]
    refine (h _ _ (hg.mul hD) (AnalyticAt.mul (by fun_prop) hN)).2.2.1 ?_
    filter_upwards [hge, he] with z a b
    show g z * D z = z ^ n * N z
    rw [a, ← b, mul_assoc]
  have main : ∀ (n : ℕ) (g : ℂ → ℂ), AnalyticAt ℂ g 0 → (∀ᶠ z in 𝓝[≠] (0 : ℂ), g z = z ^ n * f z) →
      ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = f z) ∧ hat ι ℓ ψ = S := by
    intro n
    induction n with
    | zero =>
      intro g hg hge
      exact ⟨g, hg, by simpa using hge, by simpa using key 0 g hg hge⟩
    | succ n ih =>
      intro g hg hge
      have hg0 : g 0 = 0 := by
        have := congrArg constantCoeff (key _ g hg hge)
        rw [hcc] at this
        simpa [h0] using this
      obtain ⟨s, hs⟩ := hg
      refine ih (dslope g 0) ⟨_, hs.has_fpower_series_dslope_fslope⟩ ?_
      filter_upwards [hge, self_mem_nhdsWithin] with z a hz
      have hz' : z ≠ 0 := hz
      rw [dslope_of_ne _ hz', slope_def_field, hg0, a]
      field_simp
      ring
  obtain ⟨n, hn⟩ := hf
  exact main n _ hn (Filter.Eventually.of_forall fun z => by simp)
end

lemma x_ne (M : Mdl q) (hM : M.Ok) (c z₀ : ℂ) : ∀ᶠ z in 𝓝[≠] z₀, M.x z - c ≠ 0 := by
  obtain ⟨-, -, hx, -, u0, w0, du, -, hs⟩ := uw_elliptic_flow q M hM
  have hm : Meromorphic (fun z => M.x z - c) := fun z => (hx.1 z).sub (MeromorphicAt.const c z)
  have h0 : meromorphicOrderAt (fun z => M.x z - c) 0 ≠ ⊤ := by
    intro ht
    rw [meromorphicOrderAt_eq_top_iff] at ht
    obtain ⟨au, aw, -, -, e1, e2⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
    have dw : deriv M.w 0 = 0 := by
      have := e2.self_of_nhds.2.2
      simpa [u0, w0] using this
    have e3 : ∀ᶠ z in 𝓝[≠] (0 : ℂ), M.u z = c * M.w z := by
      filter_upwards [ht, e1] with z a b
      rw [← b.2.2.1, sub_eq_zero.mp a]
    have e4 : M.u =ᶠ[𝓝 0] fun z => c * M.w z := by
      rw [eventually_nhdsWithin_iff] at e3
      filter_upwards [e3] with z a
      by_cases hz : z = 0
      · simp [hz, u0, w0]
      · exact a hz
    have := e4.deriv_eq
    rw [du, deriv_const_mul _ aw.differentiableAt, dw, mul_zero] at this
    exact hM.1 this
  have h1 := hm.exists_meromorphicOrderAt_ne_top_iff_forall.1 ⟨0, h0⟩ z₀
  rcases (hm z₀).eventually_eq_zero_or_eventually_ne_zero with h | h
  · exact absurd (meromorphicOrderAt_eq_top_iff.2 h) h1
  · exact h

lemma tendsto_add_punct (p : ℂ) : Filter.Tendsto (fun z : ℂ => z + p) (𝓝[≠] 0) (𝓝[≠] p) := by
  refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
  · have : Filter.Tendsto (fun z : ℂ => z + p) (𝓝 0) (𝓝 (0 + p)) :=
      (continuous_id.add continuous_const).tendsto 0
    rw [zero_add] at this
    exact this.mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with z hz
    simpa using hz

theorem shift_eq_hat_translate : ∀ (q : ℕ) [Fact q.Prime] (M : Mdl q) (ω ζ : ℂ_[q]) (p : ℂ) (φ : ℂ → ℂ), M.MChart ω → M.At ω ζ p → Ell M.L φ → AnalyticAt ℂ φ 0 → Bdd (hat M.ι (C ω * logS) φ) → ∃ ψ : ℂ → ℂ, AnalyticAt ℂ ψ 0 ∧ (∀ᶠ z in 𝓝[≠] (0 : ℂ), ψ z = φ (z + p)) ∧ hat M.ι (C ω * logS) ψ = shiftS ζ (hat M.ι (C ω * logS) φ) := by
  intro q _ M ω ζ p φ hch hat' hφ hφ0 hφb
  have hM : M.Ok := hch.1
  have h0 : constantCoeff (C ω * logS : ℂ_[q]⟦X⟧) = 0 := hch.2.1
  have hζ : ‖ζ - 1‖ < 1 := hat'.2.1
  obtain ⟨h1, v, xs, ys, -, -, bys, -, -, cys, -, hwy, -⟩ := _root_.GlobalTheory.MomOne.ChartXY.chart_xy q M _ hch
  obtain ⟨tu, tw⟩ := _root_.GlobalTheory.MomOne.SmallTranslate.shift_eq_translate q M ω ζ p hch hat'
  obtain ⟨m, P, A, B, -, hAB⟩ := GlobalTheory.T.exists_ellipticFunction_mul_prod_eq_xy q M φ hM hφ
  obtain ⟨-, -, -, -, -, -, -, -, hs⟩ := uw_elliptic_flow q M hM
  obtain ⟨au0, aw0, -, -, e0, -⟩ := hs 0 (Or.inl M.L.lattice.zero_mem)
  obtain ⟨aup, awp, -, -, ep, -⟩ := hs p hat'.1
  have htr : AnalyticAt ℂ (fun z : ℂ => z + p) 0 := by fun_prop
  have hu : Tr M.ι (C ω * logS) ζ p M.u :=
    ⟨au0, aup.comp_of_eq htr (zero_add p), ⟨1, hch.2.2.1⟩, tu⟩
  have hw : Tr M.ι (C ω * logS) ζ p M.w := by
    refine ⟨aw0, awp.comp_of_eq htr (zero_add p), ⟨1, ?_⟩, tw⟩
    refine (sup_norm_laws q).2.2.2.2.2 _ ys 0 1 bys cys ?_
    rw [pow_zero, one_mul, mul_comm, hwy]
    intro n
    rw [map_neg, norm_neg, coeff_X_pow]
    split_ifs <;> simp
  set Q : Polynomial ℂ := ∏ i, (Polynomial.X - Polynomial.C (M.x (P i))) with hQ
  obtain ⟨a, FQ, tQ, eQ⟩ := exists_homog h0 hζ hu hw Q
  obtain ⟨b, FA, tA, eA⟩ := exists_homog h0 hζ hu hw A
  obtain ⟨c, FB, tB, eB⟩ := exists_homog h0 hζ hu hw B
  have tD : Tr M.ι (C ω * logS) ζ p (fun z => FQ z * M.w z ^ (b + c + 1)) :=
    tQ.mul h0 hζ (hw.pow h0 hζ _)
  have tN : Tr M.ι (C ω * logS) ζ p
      (fun z => M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b))) :=
    (hw.pow h0 hζ _).mul h0 hζ ((tA.mul h0 hζ (hw.pow h0 hζ _)).add h0 hζ
      ((Tr.const h0 (-1)).mul h0 hζ (tB.mul h0 hζ (hw.pow h0 hζ _))))
  have hid : ∀ z, (z ∉ M.L.lattice ∧ M.y z ≠ 0 ∧ M.x z * M.w z = M.u z ∧ M.y z * M.w z = -1) →
      φ z * Q.eval (M.x z) = A.eval (M.x z) + B.eval (M.x z) * M.y z →
      φ z * (FQ z * M.w z ^ (b + c + 1)) =
        M.w z ^ a * (FA z * M.w z ^ (c + 1) + (-1) * (FB z * M.w z ^ b)) := by
    intro z e1 e2
    rw [eQ z _ e1.2.2.1, eA z _ e1.2.2.1, eB z _ e1.2.2.1, ← e1.2.2.2]
    linear_combination M.w z ^ (a + b + c + 1) * e2
  have h := (TaylorRead.hat_laws q M.ι _ h0).1
  refine exists_quot h0 h1 _ ?_ tD.2.1 tN.2.1 ?_ ?_ ?_
  · exact MeromorphicAt.comp_analyticAt (f := φ) (g := fun z => z + p) (hφ.1 _) htr
  · have hQ0 : ∀ᶠ z in 𝓝[≠] p, ∀ i, M.x z - M.x (P i) ≠ 0 :=
      Filter.eventually_all.2 fun i => x_ne M hM _ p
    refine (tendsto_add_punct p).eventually (p := fun z => FQ z * M.w z ^ (b + c + 1) ≠ 0) ?_
    filter_upwards [hQ0, ep] with z a1 a2
    have hw0 : M.w z ≠ 0 := by
      intro hz
      have := a2.2.2.2
      rw [hz] at this
      simp at this
    rw [eQ z _ a2.2.2.1]
    refine mul_ne_zero (mul_ne_zero ?_ (pow_ne_zero _ hw0)) (pow_ne_zero _ hw0)
    rw [hQ, Polynomial.eval_prod]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by simpa using a1 i
  · exact (tendsto_add_punct p).eventually ((ep.and (hAB p)).mono fun z hz => hid z hz.1 hz.2)
  · rw [tD.2.2.2, tN.2.2.2, ← Shift.shiftS_mul hζ hφb tD.2.2.1, ← (h _ _ hφ0 tD.1).2.1]
    congr 1
    exact (h _ _ (hφ0.mul tD.1) tN.1).2.2.1 ((e0.and (hAB 0)).mono fun z hz => hid z hz.1 hz.2)

end GlobalTheory.MomOne.Transfer
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsPowFrame
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.UnifJets

theorem exists_pow_frame {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) {A B : Type} [CommRing A] [CommRing B]
    (ψ : A →+* B) (ψ' : B →+* A) (hψ : ψ.comp ψ' = RingHom.id B) (hψ' : ψ'.comp ψ = RingHom.id A)
    (p : Sp A ⟶ X) (z : Sp B ⟶ X) (hz : z = spMap ψ ≫ p) (q : ℕ)
    (t : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => z) (fun _ => (1 : ℤ)))) (ht : t.IsGen) :
    ∃ τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => (q : ℤ))), τ.IsGen ∧
      ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp B) (y : Z) (J), Good L y J → val τ (r ≫ spMap ψ) y J = val t r y J ^ q := by
  have e₁ : spMap ψ ≫ spMap ψ' = 𝟙 _ := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ]; exact Spec.map_id _
  have e₂ : spMap ψ' ≫ spMap ψ = 𝟙 _ := by
    rw [spMap, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp, hψ']; exact Spec.map_id _
  obtain ⟨τ, hτ, hv⟩ := exists_gen hL (φ' := fun _ : Fin 1 => p ≫ 𝟙 X) (ε' := fun _ => (q : ℤ)) (fun U _ h => by
      simp only [hz, ← Category.assoc, e₂, Category.id_comp, Category.comp_id, _root_.mul_one])
    (LB.pullGen L _ _ (GeneratorPullback.powGen L _ _ t q) (spMap ψ'))
    (pullGen_isGen _ _ _ _ (SectionScalarValuation.powGen_isGen' L _ _ t ht q) _)
  refine ⟨τ, hτ, fun Z r y J hJ => ?_⟩
  rw [hv _ _ y J hJ, val_pull hJ, TWM.val_powGen, Category.assoc, e₁, Category.comp_id]

theorem sval_comp {X Y : Scheme.{0}} {L : LB X} (hL : L.IsLB) {q : ℕ} (σ : H0 L q) (p : Y ⟶ X)
    (τ : LB.Gen (LB.LinComb L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => (q : ℤ)))) (a : Γ(Y, ⊤))
    (h : ∀ (y : Y) (J), Good L y J → sval σ p y J = gs (𝟙 _) y ⊤ a * (val τ (𝟙 _) y J).val)
    {Z : Scheme.{0}} (r : Z ⟶ Y) (z : Z) (J) (hJ : Good L z J) :
    sval σ (r ≫ p) z J = gs r z ⊤ a * (val τ r z J).val := by
  have hj : p (r z) ∈ L.U (J (r ≫ p ≫ 𝟙 X)) := hJ (r ≫ p ≫ 𝟙 X)
  obtain ⟨J', hJ', e⟩ := exists_good L hL (r z) (K := Unit) (fun _ => p ≫ 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X))
    (fun _ _ _ => rfl) (fun _ => hj)
  have h₁ := h (r z) J' hJ'
  rw [sval_of σ p _ J' (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => e ()),
    val_of τ _ _ J' (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => by rw [Category.id_comp]; exact e ())] at h₁
  rw [sval_of σ _ _ J (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => by rw [Category.assoc]),
    val_of τ _ _ J (fun _ => J (r ≫ p ≫ 𝟙 X)) (fun _ => rfl)]
  have m₁ : p (r z) ∈ LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X)) :=
    Set.mem_iInter.2 fun _ => hj
  have m₂ : r z ∈ LB.wchart L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X)) :=
    Set.mem_iInter.2 fun _ => hj
  have s₁ : ∀ f, gs (r ≫ p) z (LB.wchart L (K := Fin 1) (fun _ => 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X))) f =
      (r.stalkMap z).hom (gs p (r z) _ f) := fun f =>
    (gs_pull r p z _ m₁ f).symm.trans ((gs_stalkMap r z _ m₁ _).trans (congrArg (r.stalkMap z).hom
      ((gs_pull (𝟙 Y) p (r z) _ m₁ f).trans (congrArg (fun w => gs w (r z) _ f) (Category.id_comp p)))))
  have s₂ : ∀ u, (r.stalkMap z).hom (gm (𝟙 Y) (r z)
      (LB.wchart L (K := Fin 1) (fun _ => p ≫ 𝟙 X) (fun _ => J (r ≫ p ≫ 𝟙 X))) u).val = (gm r z _ u).val := fun u =>
    (congrArg (r.stalkMap z).hom (gs_unit (𝟙 Y) (r z) _ m₂ u).symm).trans
      ((gs_stalkMap r z _ m₂ _).symm.trans (gs_unit r z _ m₂ u))
  exact (s₁ _).trans ((congrArg (r.stalkMap z).hom h₁).trans ((map_mul _ _ _).trans
    (congrArg₂ (· * ·) (gs_stalkMap r z ⊤ trivial a).symm (s₂ _))))

theorem cst_spMap {A C : Type} [CommRing A] [CommRing C] {Z : Scheme.{0}} (q : Z ⟶ Sp C) (φ : A →+* C) (z : Z) (a : A) :
    cst (q ≫ spMap φ) z a = cst q z (φ a) := by
  rw [← H1.cst_stalkMap, H1.gs_spec, H1.cst_stalkMap, Category.comp_id]

theorem cst_sum {A : Type} [CommRing A] {Z : Scheme.{0}} (q : Z ⟶ Sp A) (z : Z) {n : ℕ} (a : Fin n → A) :
    cst q z (∑ i, a i) = ∑ i, cst q z (a i) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [cst, gs_eq q z ⊤ trivial, map_sum]

theorem coeff_of_jet {V F κ : Type} [CommRing V] [CommRing F] [Fintype κ] [DecidableEq κ] (φ : V →+* F) (m : ℕ)
    (f : MvPowerSeries κ V) (g : MvPowerSeries κ F) (c : F)
    (h : psJet m g = algebraMap F _ c * jetCoef φ κ m (psJet m f)) (e : κ →₀ ℕ) (he : e.degree ≤ m) :
    MvPowerSeries.coeff e g = c * φ (MvPowerSeries.coeff e f) := by
  have h' : Ideal.Quotient.mk (orig F κ ^ (m + 1)) (psTrunc m g) =
      Ideal.Quotient.mk (orig F κ ^ (m + 1)) (MvPolynomial.C c * MvPolynomial.map φ (psTrunc m f)) := h
  have h2 := GermFun.coeff_eq_zero_of_mem (Ideal.Quotient.eq.1 h') (Nat.lt_succ_of_le he)
  rwa [MvPolynomial.coeff_sub, GermFun.coeff_psTrunc _ _ _ he, MvPolynomial.coeff_C_mul, MvPolynomial.coeff_map,
    GermFun.coeff_psTrunc _ _ _ he, sub_eq_zero] at h2

theorem jetCoef_smul {V F κ : Type} [CommRing V] [CommRing F] (φ : V →+* F) (m : ℕ) (c : V) (a : Jet V κ m) :
    jetCoef φ κ m (c • a) = algebraMap F _ (φ c) * jetCoef φ κ m a := by
  rw [Algebra.smul_def, map_mul]
  exact congrArg (· * _) (congrArg (Ideal.Quotient.mk _) (MvPolynomial.map_C φ c))

theorem jets : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → AJetSt := by
  intro hL _ _ hT V _ _ _ _ ϖ hϖ D A G _ _ U κ _ _ z hz τ hτ hτT Q hQ Φ M0 r b hΦ0 hM0 hb hbw F _ _ _ _ _ v hv q n hq hn f
  have hLB := U.LG.isLB
  obtain ⟨x, hx, hM⟩ := _root_.GlobalTheory.PowGerm.univConv V G κ z hz _ (Fintype.equivFin κ).symm
  obtain ⟨ψ, -, hψ⟩ := hM n
  obtain ⟨τ', hτ', hvτ⟩ := exists_pow_frame hLB (ψ : Chart.JetR V (Fin (Fintype.card κ)) n →+* Jet V κ n)
    (ψ.symm : Jet V κ n →+* Chart.JetR V (Fin (Fintype.card κ)) n) (RingHom.ext fun a => ψ.apply_symm_apply a)
    (RingHom.ext fun a => ψ.symm_apply_apply a) (x n).left (z n).left hψ q (τ n) (hτ n)
  obtain ⟨l, σ, fa, χ, a, hexp, hΦ, hχ, hsupp, hval, hspan⟩ :=
    SmallJets.small_characters_span_jets hL (twistBCSpan_of hT) V ϖ hϖ D A G U Q hQ r b Φ M0 hΦ0 hM0 hb hbw
      q n hq hn _ x hx τ' hτ'
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun V).1
    (show ψ.symm (psJet n f) ∈ Submodule.span V (Set.range a) by rw [hspan]; trivial)
  have hθ := fun i => (hΦ i).elim fun Φ hΦ' =>
    FamBaseChange.main hL.globalFns V (maximalIdeal V) D q Φ (fa i) hΦ' F
  choose θ hθ using hθ
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  obtain ⟨gm, h0, hle, hge⟩ : ∃ gm : ℚ, 0 ≤ gm ∧ (gm : ℝ) ≤ (n : ℝ) ^ 2 * Φ / q ∧
      ∀ i, (Q (χ i) : ℚ) / q ≤ gm := by
    refine ⟨(⌊(n : ℝ) ^ 2 * Φ⌋ : ℤ) / q, ?_, ?_, fun i => ?_⟩
    · have : 0 ≤ ⌊(n : ℝ) ^ 2 * Φ⌋ := Int.floor_nonneg.2 (mul_nonneg (sq_nonneg _) hΦ0)
      positivity
    · push_cast
      exact div_le_div_of_nonneg_right (Int.floor_le _) hq0.le
    · exact div_le_div_of_nonneg_right (by exact_mod_cast Int.le_floor.2 (hχ i)) (Nat.cast_nonneg q)
  obtain ⟨lam, hlam0, hlam⟩ : ∃ lam : F, lam ≠ 0 ∧ v lam = (gm : WithTop ℚ) := by
    rcases h0.eq_or_lt with h | h
    · exact ⟨1, one_ne_zero, by rw [← h]; simp⟩
    · exact exists_val_eq hv h
  obtain ⟨σ', hσ'⟩ := BoxExpansion.exists_secLin (φ := fun _ : Fin 1 => 𝟙 G.left) (ε := fun _ => (q : ℤ)) hLB
    (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (UnifPre.gFK (R := V) (G := G) F)
    (fun _ => UnifPre.gFK (R := V) (G := G) F) (fun _ => (Category.comp_id _).symm) σ
    (fun i => lam * algebraMap V F (c i))
  obtain ⟨g, hg⟩ := (_root_.GlobalTheory.GermBasic.main V D A G U κ z hz τ hτ F q).2.2 hτT σ'
  refine ⟨∑ i, (lam * algebraMap V F (c i)) • θ i, σ', g, lam, GermJets.nuGe_sum _ _ _ fun i _ => ?_,
    ⟨l, _, σ, fa, hexp, hσ', GermJets.secLin_comb _ hθ⟩, hg, hlam0, ⟨gm, hlam, hle⟩, ?_⟩
  · have hci : (0 : WithTop ℚ) ≤ v (algebraMap V F (c i)) := by
      rw [IsScalarTower.algebraMap_apply V (FractionRing V) F]
      exact (TWO.v_of_V v hϖ hv (c i)).1
    have h2 := NuGe.smul Q (q := gm) (ζ := lam * algebraMap V F (c i))
      (by rw [AddValuation.map_mul, hlam]; exact le_add_of_nonneg_right hci) ((isSmul_iff _ _ _).2 rfl)
      (GermJets.nuGe_of_class hϖ hQ hv (by omega) (hθ i) (χ i) (hsupp i))
    exact NuGe.mono Q h2 (by have := hge i; linarith)
  · refine coeff_of_jet (algebraMap V F) n f g lam ?_
    obtain ⟨zF, e₁, e₂, hzF⟩ := hg n
    refine H1.cst_ext fun y => ?_
    obtain ⟨J, hJ, -⟩ := exists_good U.LG.L hLB y (K := PEmpty) (fun k => k.elim) (fun k => k.elim)
      (fun k => k.elim) (fun k => k.elim)
    have h₁ := (hzF y J hJ).symm.trans (BoxExpansion.secLin_val hσ' zF y hJ)
    have h₂ : ∀ i, gs zF y ⊤ (Out.scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left
          (lam * algebraMap V F (c i))) * sval (σ i) (zF ≫ UnifPre.gFK (R := V) (G := G) F) y J =
        cst (𝟙 _) y (algebraMap F (Jet F κ n) lam * jetCoef (algebraMap V F) κ n (ψ (c i • a i))) *
          (val (τ n) (spMap (jetCoef (algebraMap V F) κ n)) y J ^ q).val := fun i => by
      have k₁ : gs zF y ⊤ (Out.scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left
          (lam * algebraMap V F (c i))) = cst (𝟙 _) y (algebraMap F (Jet F κ n) (lam * algebraMap V F (c i))) :=
        (gs_pull zF _ y ⊤ trivial _).trans ((congrArg (fun w => cst w y (lam * algebraMap V F (c i))) e₁).trans
          (H1.gs_spec _ y _))
      have k₂ := sval_comp hLB (σ i) (x n).left τ' _ (hval i)
        (spMap (jetCoef (algebraMap V F) κ n) ≫ spMap (ψ : Chart.JetR V (Fin (Fintype.card κ)) n →+* Jet V κ n)) y J hJ
      rw [hvτ _ _ y J hJ] at k₂
      have k₃ : sval (σ i) (zF ≫ UnifPre.gFK (R := V) (G := G) F) y J =
          cst (𝟙 _) y (jetCoef (algebraMap V F) κ n (ψ (a i))) *
            (val (τ n) (spMap (jetCoef (algebraMap V F) κ n)) y J ^ q).val :=
        (congrArg (fun w => sval (σ i) w y J) (e₂.trans ((congrArg (_ ≫ ·) hψ).trans (Category.assoc _ _ _).symm))).trans
          (k₂.trans (congrArg (· * _) ((cst_spMap _ _ y _).trans (H1.gs_spec _ y _))))
      rw [k₁, k₃, map_smul, jetCoef_smul, ← _root_.mul_assoc, ← H1.cst_mul, map_mul, _root_.mul_assoc (algebraMap F (Jet F κ n) lam)]
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.sum_congr rfl fun i _ => h₂ i, ← Finset.sum_mul, ← cst_sum, ← Finset.mul_sum, ← map_sum, ← map_sum, hc,
      ψ.apply_symm_apply] at h₁
    exact (Units.mul_left_inj _).1 h₁

end GlobalTheory.UnifJets
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.FamilySetupCayleyMomentStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.family_setup_cayley_moment : Hyps → ∀ (k r : ℕ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (lam : Fin (2 * r + k + 1) → ℝ) (u : ℕ → ℝ) (b bv ga h : ℝ) (q0 : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (R : (Fin (2 * r + k + 1) → ℤ) → Rep k r) (l : ∀ ν, (R ν).H → Wp) (dg : (Fin (2 * r + k + 1) → ℤ) → ℝ) (Q : Mx k r) (E : ∀ ν, Fin (2 * r + k + 1) → Fin (2 * r + k + 1) → Module.End ℂ (R ν).smSub), Setup lam u b bv ga h q0 z π μW μN μG νq R l dg → PI.UpqRep.IsCayleyU k r (PI.BesselPeriodGGP.eps48 k r) Q → (∀ ν, n1 ν ≤ q0 → (R ν).IsE Q (E ν) ∧ Formalism.REAL.GlRel (E ν)) → ∀ ν, n1 ν + 1 ≤ q0 → ∀ (j q : ℕ) (MM : ℝ), j ≤ 4 * (2 * r + k + 1) ^ 2 → 0 ≤ MM → (∀ (s : Fin (2 * r + k + 1)) (y : (R (ν - Pi.single s 1)).smSub), Lev (PI.BesselPeriodGGP.eps48 k r) (E (ν - Pi.single s 1)) (fun a => lam a + (((ν - Pi.single s 1) : Fin (2 * r + k + 1) → ℤ) a : ℝ)) (j + 2) y → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * q) * (dg (ν - Pi.single s 1) * ‖l (ν - Pi.single s 1) ((R (ν - Pi.single s 1)).σ (Matrix.of x) y)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal (MM * ‖y‖ ^ 2)) → ∀ w : (R ν).smSub, Lev (PI.BesselPeriodGGP.eps48 k r) (E ν) (fun a => lam a + ((ν : Fin (2 * r + k + 1) → ℤ) a : ℝ)) j w → ∫⁻ x, ENNReal.ofReal (lenA k r z (Matrix.of x) 0 ^ (2 * (q + 1)) * (dg ν * ‖l ν ((R ν).σ (Matrix.of x) w)‖ ^ 2)) ∂νq ≤ ENNReal.ofReal ((((2 * r + k + 1) : ℝ) ^ 2 * (Formalism.QuantumDeterminants.Tz k r z * b ^ 4) * (6 * bv) ^ (2 * (2 * r + 2))) * MM * ‖w‖ ^ 2) := by
  first | exact @GlobalTheory.MomentStep.moment_step | exact GlobalTheory.MomentStep.moment_step | (intros; apply GlobalTheory.MomentStep.moment_step <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.GermOfFamHolds
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PowGerm

theorem germOfFam_holds : Laws → Laws2 → Laws4 → TwistBaseChangeStatement → GermOfFamT := by
  intro hL hL2 hL4 hT E _ _ _ H Dw l Xo c inst hstar
  obtain rfl := starSt E H inst hstar
  let := H.starRing
  intro T io y C htr P ϖ hϖ Q hQ n _ D' A' G' _ _ pD pA pG U' PU F _ _ _ _ v hv q hq
  have hu := _root_.GlobalTheory.PowGerm.univPow T.V C.I.G.G G' n _ pG C.xT (_root_.GlobalTheory.PowGerm.univSt_holds E H Dw l Xo c T io y C)
  obtain ⟨τ, hτ, ht, hiff⟩ := frameNSt_holds E H T.V C.I.G P _ C.FT C.actT C.ph1T C.ph2T C.syT C.adT C.tgT C.xT C.eT C.wPT
    C.chartT C.frameT C.primT n D' A' G' pD pA pG U' PU
  refine ⟨fun σ' => ?_, fun s σ' hE hs g hg => ?_⟩
  · obtain ⟨f, hf⟩ := (GlobalTheory.GermBasic.main T.V D' A' G' U' _ _ hu τ hτ F q).2.2 (ht htr) σ'
    exact ⟨f, (hiff F q σ' f).2 hf⟩
  · exact GlobalTheory.IntegralGerm.main hL hL2 hL4 hT T.V ϖ hϖ D' A' G' U' _ _ hu τ hτ F v hv q hq σ' s g hE
      ((hiff F q σ' g).1 hg)
      (n1e T.V ϖ hϖ D' _ (GlobalTheory.QBox.main T.V ϖ hϖ n P.D D' pD Q hQ) F v q s hs)

end GlobalTheory.PowGerm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorMomentWeightedStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_moment_weighted : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (z : Fin (2 * r + k + 1) → ℂ) (π : Mx k r → (Wp →L[ℂ] Wp)) (u : ℕ → ℝ) (μW μN μG νq : Measure (Formalism.QuantumDeterminants.Mt k r)) (om : ι → ℂ) (Bm : R.H → Wp) (BI : ∀ I, (RI I).H → Wp) (β : κ → ℂ), R.IsDS ε mu → (∀ I, (RI I).IsDS ε (muI I)) → Function.Injective muI → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → SideG k r z π u μW μN μG νq → IsIsoB R z π νq Bm → (∀ I, IsIsoB (RI I) z π νq (BI I) ∨ β I = 0) → (∀ I, ∀ y ∈ (RI I).sm, Bm (ev Γ R om (fun c => io I c y)) = β I • BI I y) → ∀ I, IsIsoB (RI I) z π νq (BI I) → ∀ y ∈ (RI I).sm, ENNReal.ofReal (‖β I‖ ^ 2 * ‖y‖ ^ 2) ≤ ∫⁻ x, ENNReal.ofReal ((∑ i, ‖(ρ (Matrix.of x)⁻¹ *ᵥ om) i‖ ^ 2) * ‖BI I ((RI I).σ (Matrix.of x) y)‖ ^ 2) ∂νq := by
  first | exact @GlobalTheory.MomLem8.moment_lemma_pieri | exact GlobalTheory.MomLem8.moment_lemma_pieri | (intros; apply GlobalTheory.MomLem8.moment_lemma_pieri <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.JetHarmonics.TensorWeightedBesselGapStatement
section
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.tensor_weighted_bessel_gap : Hyps → ∀ (k r : ℕ) (ι κ : Type) [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ] (ρ : Mx k r → Matrix ι ι ℂ) (Γ : Matrix ι ι ℂ) (d : ℕ) (R : Rep k r) (RI : κ → Rep k r) (io : ∀ I, ι → (RI I).H → R.H) (pr : ∀ I, ι → R.H → (RI I).H) (ep : κ → ℝ) (ε : Fin (2 * r + k + 1) → Bool) (mu : Fin (2 * r + k + 1) → ℝ) (muI : κ → Fin (2 * r + k + 1) → ℝ) (h : ℝ) (Wp : Type) [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [CompleteSpace Wp] [FiniteDimensional ℂ Wp] (Wq : Type) [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [CompleteSpace Wq] [FiniteDimensional ℂ Wq] (D : B.RealPlaceData k r Wp Wq) (om om' : ι → ℂ) (l : R.H → Wp) (l' : R.H → Wq) (lI : ∀ I, (RI I).H → Wp) (lI' : ∀ I, (RI I).H → Wq) (F : Mx k r → (Wq →L[ℂ] Wp)) (s : ℂ) (FI : κ → Mx k r → (Wq →L[ℂ] Wp)) (sI τ : κ → ℂ), R.IsDS ε mu → Formalism.QuantumDeterminants.GapAtLeast ε mu h → (∀ I, (RI I).IsDS ε (muI I) ∧ Formalism.QuantumDeterminants.GapAtLeast ε (muI I) h) → GapOK k r h → IsFRep ρ Γ d → TensH ρ Γ R RI io pr ep → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z, ρ g *ᵥ om = om) → (∀ g ∈ Formalism.QuantumDeterminants.Sset k r D.z', ρ g *ᵥ om' = om') → (∀ I, IsBeL (RI I) D.z D.π D.μW D.μN (lI I) ∧ IsBeL (RI I) D.z' D.π' D.μW' D.μN (lI' I)) → IsCoef R l l' F s → (∀ I, ((¬ NzOn (RI I) (lI I) ∨ ¬ NzOn (RI I) (lI' I)) ∧ τ I = 0) ∨ (IsCoef (RI I) (lI I) (lI' I) (FI I) (sI I) ∧ sI I ≠ 0 ∧ ∃ κ₀ κ₁ : ℂ, (∀ v ∈ R.sm, lI I (∑ c, pr I c (tm R om v c)) = κ₀ • l v) ∧ (∀ v ∈ R.sm, lI' I (∑ c, pr I c (tm R om' v c)) = κ₁ • l' v) ∧ τ I = (ep I : ℂ) * κ₁ * star κ₀ * s / sI I)) → ∀ γ ∈ JF.Om k r D.z D.z', Formalism.QuantumDeterminants.herm Γ (ρ γ *ᵥ om') om • B.JF D F γ = ∑ I, τ I • B.JF D (FI I) γ := by
  first | exact @GlobalTheory.BesselPieri.pieri_bessel | exact GlobalTheory.BesselPieri.pieri_bessel | (intros; apply GlobalTheory.BesselPieri.pieri_bessel <;> assumption)
end

