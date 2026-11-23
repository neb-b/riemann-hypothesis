module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.TorusSections.IsTorusOf
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.CuspStatementPf
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.PointwiseNormInvarianceHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.ArakelovInstances.FirstMinimumInvariantContinuousPos
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0015
public import Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormProdSumThetaLeExp
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.GCauchyHolds

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.AppellHumbertSectionEntireWithFactor
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem isHolTo_snd_slice {V W : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W]
    [NormedSpace ℂ W] {X : Scheme.{0}} {e : W → (Sp ℂ ⟶ X)}
    (he : IsHolTo ((Set.univ : Set V) ×ˢ (Set.univ : Set W)) (fun bz => e bz.2)) : IsHolTo Set.univ e := by
  intro U f
  have h := he U f
  have hd : Differentiable ℂ (fun z : W => ((0 : V), z)) := (differentiable_const _).prodMk differentiable_id
  refine ⟨?_, ?_⟩
  · have hs : {b ∈ (Set.univ : Set W) | ⊤ ≤ e b ⁻¹ᵁ U} = (fun z : W => ((0 : V), z)) ⁻¹'
        {b ∈ (Set.univ : Set V) ×ˢ (Set.univ : Set W) | ⊤ ≤ e b.2 ⁻¹ᵁ U} :=
      Set.ext fun z => ⟨fun hz => ⟨⟨trivial, trivial⟩, hz.2⟩, fun hz => ⟨trivial, hz.2⟩⟩
    rw [hs]
    exact h.1.preimage hd.continuous
  · exact h.2.comp (f := fun z : W => ((0 : V), z)) hd.differentiableOn
      (fun z hz => ⟨⟨trivial, trivial⟩, hz.2⟩)

theorem isHolTo_ex_of_isPeriod {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H}
    {l : Level H} {Xo : Moduli Dw l} {σ : KA l →+* ℂ} {g : ℕ} {ty : Fin g → (E →+* ℂ)} (Fu : FamilyUnif Xo σ ty)
    (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (hP : IsPeriod (Fu.Di i) ty Pm) :
    IsHolTo Set.univ (fun z => (Fu.ex i Pm z).left) := by
  exact isHolTo_snd_slice (e := fun z => (Fu.ex i Pm z).left)
    (Fu.hol i 0 Set.univ (fun _ => Pm) isOpen_univ ⟨fun _ _ => hP, fun _ => differentiableOn_const _⟩).2

theorem isFnOf_entire_factor :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (σ : KA l →+* ℂ) (g : ℕ) (ty : Fin g → (E →+* ℂ)) (Fu : FamilyUnif Xo σ ty) (i : Fin Fu.n) (Pm : (Fu.Di i).La →+ (Fin g → ℂ)) (Hm : Matrix (Fin g) (Fin g) ℂ) (χl : (Fin g → ℂ) → ℂ) (fr : Xo.univ.t.PP.L.ι → (Fin g → ℂ) → ℂ), IsPeriod (Fu.Di i) ty Pm → AHFrame Fu i Pm Hm χl fr → ∀ (s : LB.Sec (PPx (Fu.u i Pm))) (θ : (Fin g → ℂ) → ℂ), IsFnOf Fu i Pm fr (Fu.u i Pm) s θ → Differentiable ℂ θ ∧ ∀ a z, θ (z + Pm a) = χl (Pm a) * Complex.exp (Real.pi * hermForm Hm z (Pm a) + Real.pi / 2 * hermForm Hm (Pm a) (Pm a)) * θ z := by
  intro E _ _ _ H Dw l Xo σ g ty Fu i Pm Hm χl fr hP hF s θ hθ
  obtain ⟨-, -, -, hdf, hne, -, -, hfac⟩ := hF
  let pt : (Fin g → ℂ) → (Sp ℂ ⟶ Gx (Fu.u i Pm)) := fun z =>
    (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z)).left
  have h1 : ∀ z, pt z ≫ gxFst (Fu.u i Pm) = (Fu.ex i Pm z).left := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ snd _ _).left = (Fu.ex i Pm z).left := by
      rw [Out.ptSecT, lift_snd]
    exact this
  have h2 : ∀ z, pt z ≫ gxSnd (Fu.u i Pm) = 𝟙 (Sp ℂ) := fun z => by
    have : (Out.ptSecT Xo.univ.t.G (Fu.ex i Pm z) ≫ fst _ _).left = 𝟙 (Sp ℂ) := by
      rw [Out.ptSecT, lift_fst]; rfl
    exact this
  have hex := isHolTo_ex_of_isPeriod Fu i Pm hP
  have hpt : IsHolTo Set.univ pt := by
    refine GlobalTheory.HolFibre.isHolTo_of_isPullback (p := gxSnd (Fu.u i Pm)) (q := gxFst (Fu.u i Pm))
      (IsPullback.of_hasPullback (Fu.u i Pm) Xo.univ.t.G.hom) ?_ ?_
    · simp only [h2]
      exact GlobalTheory.HolFibre.isHolTo_const isOpen_univ _
    · simp only [h1]
      exact hex
  have hch : ∀ z, ∃ j, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j := fun z => by
    have hm : (Fu.ex i Pm z).left (default : PrimeSpectrum ℂ) ∈ ⨆ j, Xo.univ.t.PP.L.U j := by
      rw [Xo.univ.t.PP.isLB.cover]; trivial
    obtain ⟨j, hj⟩ := TopologicalSpace.Opens.mem_iSup.1 hm
    exact ⟨j, (top_le_preimage_iff_mem _ _).2 hj⟩
  have hU : ∀ j z, ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j →
      ⊤ ≤ pt z ⁻¹ᵁ (PPx (Fu.u i Pm)).U (fun _ => j) := fun j z h y hy => by
    have h3 := h hy
    rw [← h1] at h3
    exact Set.mem_iInter.2 fun _ => h3
  refine ⟨fun z₀ => ?_, fun a z => ?_⟩
  · obtain ⟨j, hj⟩ := hch z₀
    have ho : IsOpen {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      have h0 := (hex (Xo.univ.t.PP.L.U j) 0).1
      simp only [Set.mem_univ, true_and] at h0
      exact h0
    have hv : DifferentiableOn ℂ (fun z => valAt' (pt z) ((PPx (Fu.u i Pm)).U fun _ => j) (s.f fun _ => j))
        {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} :=
      (hpt _ (s.f (fun _ => j))).2.mono (fun z hz => ⟨trivial, hU j z hz⟩)
    have hq : DifferentiableOn ℂ θ {z | ⊤ ≤ (Fu.ex i Pm z).left ⁻¹ᵁ Xo.univ.t.PP.L.U j} := by
      refine (hv.mul ((hdf j).inv (fun z hz => hne j z hz))).congr fun z hz => ?_
      rw [Pi.mul_apply, Pi.inv_apply, hθ j z (pt z) (h1 z) (h2 z) hz, mul_inv_cancel_right₀ (hne j z hz)]
    exact hq.differentiableAt (ho.mem_nhds hj)
  · obtain ⟨j, hj⟩ := hch z
    have he : Fu.ex i Pm (z + Pm a) = Fu.ex i Pm z := by
      rw [Fu.ex_add i Pm hP, (Fu.ex_ker i Pm hP (Pm a)).2 ⟨a, rfl⟩, _root_.mul_one]
    have e1 := hθ j z (pt z) (h1 z) (h2 z) hj
    have e2 := hθ j (z + Pm a) (pt z) (by rw [he]; exact h1 z) (h2 z) (by rw [he]; exact hj)
    have e3 := (hfac a j z).2 hj
    have n2 := hne j (z + Pm a) (by rw [he]; exact hj)
    apply mul_right_cancel₀ n2
    rw [← e2, e1, e3]
    ring

end GlobalTheory.EtaAn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ArchimedeanBoundTotalConstantSize
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn


open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
attribute [local instance] Over.cartesianMonoidalCategory in
theorem _root_.GlobalTheory.EtaAn.archimedeanBoundTotalConstant_size : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r q m Nc : ℕ) (L : ℝ), 2 ≤ L → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E → 1 ≤ r → 1 ≤ m → m ≤ r → 1 ≤ q → 1 ≤ _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E) ≤ 2 * L → Real.log (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E) ≤ 2 * L → Real.log r ≤ L → Real.log q ≤ 70 * L → Real.log Nc ≤ 41 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 → 0 ≤ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ∧ _root_.GlobalTheory.EtaAn.p16 E r q m 5 (max 1 Nc * 5 ^ (8 * _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r ^ 2)) ≤ 200000 * (_root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E * r * L) ^ 2 := by
  intro E _ _ _ r q m Nc L hL hf hr hm hmr hq hrd hlrd hlf hlr hlq hlN
  unfold _root_.GlobalTheory.EtaAn.p16 _root_.GlobalTheory.EtaAn.p3 _root_.ReciprocityTheory.ChartRestriction.G.I2.dstar _root_.ReciprocityTheory.ChartRestriction.G.I2.RR
  push_cast
  set f := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.f E with hfdef
  set D := _root_.ReciprocityTheory.ChartRestriction.G.I2.PT.rd E with hDdef
  have hF : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hM : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hMR : (m : ℝ) ≤ r := by exact_mod_cast hmr
  have hQ : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlM : Real.log m ≤ L := (Real.log_le_log (by positivity) hMR).trans hlr
  have hlFnn : 0 ≤ Real.log f := Real.log_nonneg hF
  have hlRnn : 0 ≤ Real.log r := Real.log_nonneg hR
  have hlMnn : 0 ≤ Real.log m := Real.log_nonneg hM
  have hlQnn : 0 ≤ Real.log q := Real.log_nonneg hQ
  have hlDnn : 0 ≤ Real.log D := Real.log_nonneg hrd
  have heOne := Real.exp_one_gt_d9
  have heTwo : (7.3 : ℝ) ≤ Real.exp 2 := by
    rw [show (2 : ℝ) = 1 + 1 by norm_num, Real.exp_add]; nlinarith
  have hlTwo : Real.log 2 ≤ 1 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlFive : Real.log 5 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSix : Real.log 6 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlSeven : Real.log 7 ≤ 2 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]; linarith
  have hlTenThousand : Real.log 10000 ≤ 10 := by
    rw [Real.log_le_iff_le_exp (by norm_num), show (10 : ℝ) = 2 * 5 by norm_num, Real.exp_mul]
    have : (7.3 : ℝ) ^ 5 ≤ Real.exp 2 ^ 5 := pow_le_pow_left₀ (by norm_num) heTwo 5
    rw [← Real.rpow_natCast] at this
    norm_num at this ⊢
    linarith
  have hlTwoNonneg : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlFiveNonneg : 0 ≤ Real.log 5 := Real.log_nonneg (by norm_num)

  have hy : (1 : ℝ) ≤ f * r * q :=
    one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hF hR) hQ
  have hsqrt : 1 ≤ √((f : ℝ) * r * q) := Real.one_le_sqrt.mpr hy
  have hlogSqrt : Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ 2 + 37 * L := by
    calc Real.log (1 + 6 * √((f : ℝ) * r * q)) ≤ Real.log (7 * √((f : ℝ) * r * q)) :=
          Real.log_le_log (by positivity) (by linarith)
      _ = Real.log 7 + (Real.log f + Real.log r + Real.log q) / 2 := by
          rw [Real.log_mul (by norm_num) (by positivity), Real.log_sqrt (by positivity),
            Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity)]
      _ ≤ 2 + 37 * L := by linarith
  have hlogSqrtNonneg : 0 ≤ Real.log (1 + 6 * √((f : ℝ) * r * q)) :=
    Real.log_nonneg (by have := Real.sqrt_nonneg ((f : ℝ) * r * q); linarith)

  have hg : Real.log (3 * (2 * (f : ℝ) * m)) = Real.log 6 + Real.log f + Real.log m := by
    rw [show 3 * (2 * (f : ℝ) * m) = 6 * f * m by ring, Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity)]
  have hlogFact : Real.log (2 * (3 * (2 * (f : ℝ) * m)) ^ (2 * f * m)) =
      Real.log 2 + 2 * f * m * Real.log (3 * (2 * (f : ℝ) * m)) := by
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow]
    push_cast
    ring
  have hgUpper : Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 + 3 * L := by rw [hg]; linarith
  have hgNonneg : 0 ≤ Real.log (3 * (2 * (f : ℝ) * m)) := by rw [hg]; linarith [Real.log_nonneg (show (1:ℝ) ≤ 6 by norm_num)]

  have hmaxOne : (1 : ℝ) ≤ max 1 (Nc : ℝ) := le_max_left _ _
  have hlogBig : Real.log (max 1 (Nc : ℝ) * 5 ^ (8 * f * r ^ 2)) =
      Real.log (max 1 (Nc : ℝ)) + 8 * f * r ^ 2 * Real.log 5 := by
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow]
    push_cast
    ring
  have hXnn : 0 ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by positivity
  have hlogMax : Real.log (max 1 (Nc : ℝ)) ≤ 41 * ((f : ℝ) * r * L) ^ 2 := by
    rcases le_total (Nc : ℝ) 1 with h | h
    · rw [max_eq_left h, Real.log_one]; exact hXnn
    · rw [max_eq_right h]; exact hlN
  have hlogMaxNonneg : 0 ≤ Real.log (max 1 (Nc : ℝ)) := Real.log_nonneg hmaxOne

  have hlogLast : Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
      ≤ 10 + 24 * L := by
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    have hD : (0 : ℝ) < D := by linarith
    rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
      Real.log_pow, Real.log_pow, Real.log_pow]
    push_cast
    linarith
  have hlogLastNonneg : 0 ≤ Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    apply Real.log_nonneg
    rw [show 5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2) =
        10000 * r * f ^ 3 * m ^ 3 * D ^ 7 by ring]
    exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le
      (one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le (by norm_num) hR)
        (one_le_pow₀ hF)) (one_le_pow₀ hM)) (one_le_pow₀ hrd)
  rw [hlogFact, hlogBig]

  have hFL : 2 ≤ (f : ℝ) * L := le_trans hL (le_mul_of_one_le_left (by linarith) hF)
  have hFRsq : 4 * ((f : ℝ) * r ^ 2) ≤ ((f : ℝ) * r * L) ^ 2 := by
    have hFLsq : 4 ≤ (f : ℝ) * L ^ 2 := by
      calc (4 : ℝ) = 1 * (2 * 2) := by ring
        _ ≤ f * (L * L) := mul_le_mul hF (mul_le_mul hL hL (by norm_num) (by linarith))
            (by norm_num) (by positivity)
        _ = f * L ^ 2 := by ring
    calc 4 * ((f : ℝ) * r ^ 2) ≤ (f * L ^ 2) * ((f : ℝ) * r ^ 2) :=
          mul_le_mul_of_nonneg_right hFLsq (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hFRsqL : 2 * ((f : ℝ) * r ^ 2 * L) ≤ ((f : ℝ) * r * L) ^ 2 := by
    calc 2 * ((f : ℝ) * r ^ 2 * L) ≤ (f * L) * ((f : ℝ) * r ^ 2 * L) :=
          mul_le_mul_of_nonneg_right hFL (by positivity)
      _ = ((f : ℝ) * r * L) ^ 2 := by ring
  have hRle : (r : ℝ) ≤ f * r ^ 2 := by
    calc (r : ℝ) = 1 * 1 * r := by ring
      _ ≤ f * r * r := mul_le_mul (mul_le_mul hF hR zero_le_one (by positivity)) le_rfl
          (by positivity) (by positivity)
      _ = f * r ^ 2 := by ring
  have hprodSqrt : (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) ≤
      r * (f * r * (2 + 37 * L)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hlogSqrt (by positivity)) (by positivity)
  have hprodFact : (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) ≤ r * (2 * f * r * (2 + 3 * L)) := by
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc 2 * (f : ℝ) * m * Real.log (3 * (2 * (f : ℝ) * m)) ≤ 2 * f * m * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_left hgUpper (by positivity)
      _ ≤ 2 * f * r * (2 + 3 * L) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hMR (by positivity)) (by linarith)
  have hprodRFM : (r : ℝ) * (2 * f * m) ≤ 2 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hMR (by positivity : (0 : ℝ) ≤ 2 * f * r)
    linarith
  have hprodLast : (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) ≤
      625 * (f * r ^ 2) * (10 + 24 * L) := by
    calc (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
          Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2))
        ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_left hlogLast (by positivity)
      _ ≤ 625 * (f * r ^ 2) * (10 + 24 * L) :=
          mul_le_mul_of_nonneg_right (by linarith [hprodRFM]) (by linarith)
  have hprodFiveA : 8 * (f : ℝ) * r ^ 2 * Real.log 5 ≤ 16 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlFive (by positivity : (0 : ℝ) ≤ f * r ^ 2)
    linarith
  have hprodFiveB : 2 * (f : ℝ) * r ^ 2 * Real.log 5 ≤ 4 * (f * r ^ 2) := by
    have := mul_le_mul_of_nonneg_left hlFive (by positivity : (0 : ℝ) ≤ f * r ^ 2)
    linarith
  have hnnSqrt : 0 ≤ (r : ℝ) * (f * r * Real.log (1 + 6 * √((f : ℝ) * r * q))) := by positivity
  have hnnFact : 0 ≤ (r : ℝ) * (2 * f * m * Real.log (3 * (2 * (f : ℝ) * m))) := by positivity
  have hnnLast : 0 ≤ (5 : ℝ) ^ 4 * r * (2 * f * m) / 2 *
      Real.log (5 ^ 4 * (r : ℝ) * (2 * (f : ℝ) * m) / 2 * (4 * D ^ 7 * (2 * (f : ℝ) * m) ^ 2)) := by
    positivity
  have hnnFive : 0 ≤ (f : ℝ) * r ^ 2 * Real.log 5 := by positivity
  have hnnTwo : 0 ≤ (r : ℝ) * Real.log 2 := by positivity
  have hRlogTwo : (r : ℝ) * Real.log 2 ≤ r := mul_le_of_le_one_right (by positivity) hlTwo
  have hrfm_nonneg : 0 ≤ (r : ℝ) * (2 * f * m) := by positivity
  have hRnn : (0 : ℝ) ≤ r := by positivity
  constructor
  · linarith
  · linarith

end GlobalTheory.EtaAn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ConjEqNegOfSqEqNegNat
section
namespace GlobalTheory.ImaginarySqrtEmbedding

open NumberField

theorem conj_eq_neg_of_sq_eq_neg_nat (z : ℂ) (d : ℕ) (h : z ^ 2 = -(d : ℂ)) :
    starRingEnd ℂ z = -z := by
  have hre : z.re * z.re - z.im * z.im = -(d : ℝ) := by
    have := congrArg Complex.re h
    simpa [pow_two] using this
  have him : z.re * z.im + z.im * z.re = 0 := by
    have := congrArg Complex.im h
    simpa [pow_two] using this
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h0 : z.re = 0 := by
    by_contra hne
    have him0 : z.im = 0 := by
      have h2 : z.re * z.im = 0 := by linarith
      exact (mul_eq_zero.mp h2).resolve_left hne
    have hpos : 0 < z.re * z.re := mul_self_pos.mpr hne
    rw [him0] at hre
    linarith
  apply Complex.ext <;> simp [h0]

theorem embedding_sqrt_sq_and_conj {E : Type} [Field E] [NumberField E] [IsCMField E]
    {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (τ : E →+* ℂ) :
    τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) ^ (2 : ℕ)
        = -(↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.d H) : ℂ) ∧
      starRingEnd ℂ (τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E))
        = -τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) := by
  have h1 : τ (↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.rt H) : E) ^ (2 : ℕ)
      = -(↑(ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host.d H) : ℂ) := by
    have h := congrArg (fun a : 𝓞 E => τ (algebraMap (𝓞 E) E a)) H.rt_sq
    simp only [map_pow, map_neg, map_natCast] at h
    exact h
  exact ⟨h1, conj_eq_neg_of_sq_eq_neg_nat _ _ h1⟩

end GlobalTheory.ImaginarySqrtEmbedding
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.CuspAndSupCLeOfBounded
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.BoundedCusp

theorem mem_SS_of_definite {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (X : Data E r)
    (la : FD.Wt X.Ψ r) (τ0 : X.Ψ) (h : X.p0 = 0 ∨ X.p0 = r) (P : Frame X.Ψ r → ℂ) (hP : X.IsBddSec la P) :
    P ∈ X.SS la := by
  refine ⟨hP, fun ξ hξ x hx => ?_⟩
  exfalso
  have hiso : X.IsIsoV (X.embV ξ) := fun τ =>
    ⟨by rw [show X.embV ξ τ = Data.emb τ.1 ξ from rfl, hermC_emb, hξ.2.1, map_zero],
      emb_ne_zero τ.1 hξ.2.2⟩
  have hmpos := PositiveMinorUnits.mN_pos (MajorantFamilyNorms.hG_of X τ0) X.p0 X.p0_le (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1 (hiso τ0).2
  have htop := PositiveMinorUnits.mN_top (MajorantFamilyNorms.hG_of X τ0) X.p0 (mat x τ0) (hx τ0).1
    (MajorantFamilyNorms.hsg_of X hx τ0) (X.embV ξ τ0) (hiso τ0).1
  rcases h with h | h
  · rw [h, PositiveMinorUnits.mN_zero] at hmpos
    exact lt_irrefl _ hmpos
  · rw [h, htop] at hmpos
    exact lt_irrefl _ hmpos

end GlobalTheory.BoundedCusp

namespace GlobalTheory

theorem cusp_and_supC_le_of_bounded : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (r : ℕ) (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (n : ℕ) (f : Rul Xo c) (C : ℝ), 2 ≤ n → Even n → (∀ σ, GoodEmb c σ → IsUnf (U σ)) → f ∈ sec Xo c 0 n → (∀ σ, GoodEmb c σ → ∀ k, ∀ x ∈ ((U σ).X k).dom, ((U σ).X k).pnorm (laU (U σ) 0 n k) (rdU (U σ) f k) x ≤ C) → 0 ≤ C → f ∈ cusp Xo c U 0 n ∧ ∀ σ (xi : ℝ), GoodEmb c σ → supC Xo c U xi σ 0 n f ≤ C := by
  intro E _ _ _ H Dw l Xo c r U n f C hn hev hU hf hb hC
  refine ⟨?_, fun σ xi hσ => ?_⟩
  · rw [mem_cusp]
    refine ⟨hf, fun σ hσ => holCusp_mem_holSub _ _ fun j => ?_⟩
    obtain ⟨-, -, -, -, hsec, -⟩ := hU σ hσ
    have hD : Dom (0 : (E →+* ℂ) × ℕ → ℕ) n := ⟨fun τ i i' _ => le_rfl, hev⟩
    obtain ⟨τ0⟩ : Nonempty ((U σ).X j).Ψ := by
      obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
      by_cases h : τ ∈ ((U σ).X j).Ψ
      · exact ⟨⟨τ, h⟩⟩
      · exact ⟨⟨_, not_not.mp (fun h' => h ((((U σ).X j).cmType τ).mpr h'))⟩⟩
    have hbd : ((U σ).X j).IsBddSec (laU (U σ) 0 n j) (rdU (U σ) f j) :=
      ⟨hsec _ _ hD f hf j, C, hb σ hσ j⟩
    have hle := ((U σ).X j).p0_le
    by_cases h0 : ((U σ).X j).p0 = 0 ∨ ((U σ).X j).p0 = r
    · exact BoundedCusp.mem_SS_of_definite _ _ τ0 h0 _ hbd
    · refine AR.Up.cuspStatement_holds r _ _ τ0 (by omega) (by omega) ?_ ?_ _ hbd
      · intro i i' h1 h2
        unfold laU
        by_cases h3 : ((U σ).X j).p0 ≤ (i : ℕ)
        · rw [if_pos h3, if_pos (by omega)]
          simp
        · rw [if_neg h3, if_neg (by omega)]
          simp
      · intro i i' h1 h2
        unfold laU
        rw [if_neg (by omega), if_pos (by omega)]
        omega
  · have h1 : lieFac Dw xi (0 : (E →+* ℂ) × ℕ → ℕ) = 1 := by simp [lieFac]
    unfold supC supN
    rw [h1, _root_.one_mul]
    refine ENNReal.toReal_le_of_le_ofReal hC ?_
    exact iSup_le fun p => ENNReal.ofReal_le_ofReal (hb σ hσ p.1 p.2 p.2.2)

end GlobalTheory
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.ExistsBorelOrthonormalFlagFrame
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.EtaAn

theorem exists_unit_frame : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r), ∀ x ∈ X.dom, ∃ b ∈ Bor X.Ψ r, rmul x b ∈ X.dom ∧ (∀ τ i, ‖dmin X.Gm (rmul x b) τ i‖ = 1) ∧ X.la1 (rmul x b) = X.la1 x ∧ (∀ th, I2.phiFD X th (rmul x b) = I2.phiFD X th x) ∧ ∀ (la : Wt X.Ψ r) (P : Frame X.Ψ r → ℂ), X.IsSec la P → X.pnorm la P x = ‖P (rmul x b)‖ := by
  intro E _ _ _ r X x hx
  have hb := FrameDegreeData.bOf_mem X hx
  have ho := FrameDegreeData.ortho_bOf X hx
  have hd : ∀ τ i, ‖dmin X.Gm (rmul x (FrameDegreeData.bOf X x)) τ i‖ = 1 := by
    intro τ i
    unfold dmin
    rw [ho τ, FrameDegreeData.lminor_diagonal, norm_prod]
    refine Finset.prod_eq_one fun j _ => ?_
    rw [Complex.norm_real]
    rcases FrameDegreeData.sgn_sq X.p0 (Fin.castLE (Nat.le_of_lt_succ i.isLt) j : Fin r) with h | h <;>
      rw [h] <;> simp
  have hl : X.la1 (rmul x (FrameDegreeData.bOf X x)) = X.la1 x := by
    unfold Data.la1
    rw [ReciprocityTheory.ChartRestriction.G.AR.Inst.firstMinimumSq_rightBorel X hx hb]
  refine ⟨_, hb, OrthogonalFrameDomain.rmul_mem_dom X hx hb, hd, hl, fun th => ?_, fun la P hP => ?_⟩
  · unfold I2.phiFD
    rw [hl]
  · rw [← FrameDegreeData.pnorm_rmul X la P hP.2.1 x hx _ hb]
    unfold Data.pnorm
    simp only [norm_div, hd, div_one, Real.one_rpow, Finset.prod_const_one, _root_.mul_one]

end GlobalTheory.EtaAn
end

-- bundled from Development.AbelianVarietyTheory.Proofs.TorusSplitting.NormProdSumThetaLeExpTorus
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.L2.PjFree GlobalTheory.EtaForm GlobalTheory.EtaAn GlobalTheory.ArcQ
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

theorem norm_prod_sum_theta_le_exp_of_card :
    ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (T : I2.PT E) (DF : ℕ) (P : I2.Par T DF) (R i N : ℕ), 2 ≤ R → 1 ≤ N → ∀ s ∈ T.Sec 1 1, T.l2 1 s = 1 → ∀ (G J : Type) [Fintype G] [Fintype J], Fintype.card G = 2 * R ^ 4 * i → Fintype.card J ≤ R ^ (2 * I2.PT.f E * T.r ^ 2) → ∀ (cf : J → ℤ) (w : G → J → Fin T.r → ℂ) (a : G → J → Fin T.r → I2.Vsp T.dim), (∀ j, |cf j| ≤ N) → (∀ g j b, ((R : ℂ) ^ 2) • a g j b ∈ T.L) → (∀ g j, ∀ x ∈ T.L, ∃ c : Fin T.r → 𝓞 E, ∃ y ∈ T.L, x = ∑ b, I2.act (c b) (((R : ℂ) ^ 2) • a g j b) + (R : ℂ) • y) → (∀ g j b, ‖w g j b‖ = Real.sqrt (T.ptN2 1 s fun _ => a g j b)) → ‖∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b‖ ≤ Real.exp (-(i : ℝ) * (T.ph (I2.th (E := E) P.q P.R0) - p16 E T.r P.q P.m R N)) := by
  intro E _ _ _ T DF P R i N hR hN s hs hl G J _ _ hG hJ cf w a hcf ha hsp hw
  have hs0 : s ≠ 0 := by
    rintro rfl
    simp [I2.PT.l2, I2.PT.ptN2] at hl
  let eG : Fin (2 * R ^ 4 * i) ≃ G := (Fintype.equivFinOfCardEq hG).symm
  let eJ : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  have key := GlobalTheory.norm_prod_sum_theta_le_exp I2.T_holds E T DF P R hR s hs hs0 i N
    (Fintype.card J) hN hJ (fun _ t => (cf (eJ t) : ℂ)) (fun k t => ∏ b, w (eG k) (eJ t) b)
    (fun k t => a (eG k) (eJ t))
    (fun _ t => by
      rw [Complex.norm_intCast]
      exact_mod_cast hcf (eJ t))
    (fun k t => ⟨ha _ _, hsp _ _⟩)
    (fun k t => by
      rw [norm_prod]
      simp [hw, hl])
  have h1 : ∏ g, ∑ j, (cf j : ℂ) * ∏ b, w g j b =
      ∏ k, ∑ t, (cf (eJ t) : ℂ) * ∏ b, w (eG k) (eJ t) b := by
    rw [← eG.prod_comp]
    exact Finset.prod_congr rfl fun k _ => (eJ.sum_comp _).symm
  rw [h1, neg_mul]
  exact key

end GlobalTheory
end

