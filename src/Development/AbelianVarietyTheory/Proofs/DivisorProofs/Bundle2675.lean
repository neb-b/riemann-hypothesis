module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0069
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0037
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0658
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1164
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1213
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2623
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1092
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1132
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1094
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2480
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0036
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2515
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2510
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2625
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2626
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2624
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2630
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2466
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.Bundle0010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2441
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2566
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0980
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2536

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotients
section
open Filter Topology MvPolynomial GlobalTheory.HSAmp

set_option autoImplicit false

namespace GlobalTheory.HSAmp.TrBasis

variable {K : Type} [Field K]

theorem isAlgebraic_div_of_mem {s : Set K} {a b : K} (ha : a ∈ Algebra.adjoin ℤ s)
    (hb : b ∈ Algebra.adjoin ℤ s) (hb0 : b ≠ 0) : IsAlgebraic (Algebra.adjoin ℤ s) (a / b) := by
  refine ⟨Polynomial.C (⟨b, hb⟩ : Algebra.adjoin ℤ s) * Polynomial.X - Polynomial.C ⟨a, ha⟩, ?_, ?_⟩
  · intro h
    have h1 := congrArg (fun p : Polynomial (Algebra.adjoin ℤ s) => p.coeff 1) h
    simp at h1
    exact hb0 (congrArg Subtype.val h1)
  · simp [mul_div_cancel₀ _ hb0]

theorem isAlgebraic_trans [CharZero K] {s t : Set K}
    (ht : Algebra.IsAlgebraic (Algebra.adjoin ℤ t) K)
    (hts : ∀ w ∈ t, IsAlgebraic (Algebra.adjoin ℤ s) w) :
    Algebra.IsAlgebraic (Algebra.adjoin ℤ s) K := by
  rw [← AlgebraicIndependent.matroid_spanning_iff] at ht ⊢
  rw [Matroid.spanning_iff_closure_eq] at ht ⊢
  refine Set.eq_univ_of_univ_subset ?_
  rw [AlgebraicIndependent.matroid_e] at ht
  rw [← ht]
  refine Matroid.closure_subset_closure_of_subset_closure ?_
  intro w hw
  rw [AlgebraicIndependent.matroid_closure_eq]
  exact (Subalgebra.mem_algebraicClosure _ _).2 (hts w hw)

theorem trBasis_of_integral_ratR (K : Type) [Field K] [CharZero K] (D : ℕ) (x : Fin (D + 1) → K) (l : Fin (D + 1))
    (A : Subring K) (htr : Algebra.trdeg ℤ K = D) (hl : x l ≠ 0) (hA : Algebra.FiniteType ℤ A)
    (hint : ∀ w ∈ A, IsIntegral (ratR x l) w)
    (hfr : ∀ w : K, ∃ a ∈ A, ∃ b ∈ A, b ≠ 0 ∧ w = a / b) :
    (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧
      FiniteDimensional (ratF x) K := by
  haveI : FaithfulSMul ℤ K := (faithfulSMul_iff_algebraMap_injective ℤ K).mpr Int.cast_injective
  set y : Fin (D + 1) → K := fun j => x j / x l with hy
  have hle : ratR x l ≤ (Algebra.adjoin ℤ (Set.range y)).toSubring :=
    Subring.closure_le.2 Algebra.subset_adjoin
  let φ : ratR x l →+* Algebra.adjoin ℤ (Set.range y) :=
    { toFun := fun v => ⟨v, hle v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hAlgA : ∀ w ∈ (A : Set K), IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) w := fun w hw =>
    (IsIntegral.map_of_comp_eq φ (RingHom.id K) (by ext; rfl) (hint w hw)).isAlgebraic
  have hAlgY : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range y)) K := by
    refine isAlgebraic_trans (t := (A : Set K)) ⟨fun w => ?_⟩ hAlgA
    obtain ⟨a, ha, b, hb, hb0, rfl⟩ := hfr w
    exact isAlgebraic_div_of_mem (Algebra.subset_adjoin ha) (Algebra.subset_adjoin hb) hb0
  set z : Fin D → K := fun j => x (l.succAbove j) / x l with hz
  have hAlgZ : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range z)) K := by
    refine isAlgebraic_trans hAlgY ?_
    rintro _ ⟨j, rfl⟩
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · subst h
      simp only [hy, div_self hl]
      exact isAlgebraic_one
    · exact isAlgebraic_algebraMap (⟨z j', Algebra.subset_adjoin ⟨j', rfl⟩⟩ :
        Algebra.adjoin ℤ (Set.range z))
  have hZ : IsTranscendenceBasis ℤ z :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ z (by rw [htr]; simp)
  have hx : ∀ j, x j ≠ 0 := by
    intro j
    rcases Fin.eq_self_or_eq_succAbove l j with h | ⟨j', rfl⟩
    · exact h ▸ hl
    · intro h0
      exact hZ.1.ne_zero j' (by simp [hz, h0])
  set u : Fin D → K := fun j => x j.succ / x 0 with hu
  have hv : ∀ k, x k / x 0 ∈ Algebra.adjoin ℤ (Set.range u) := by
    intro k
    refine Fin.cases ?_ (fun j => ?_) k
    · rw [div_self (hx 0)]; exact Subalgebra.one_mem _
    · exact Algebra.subset_adjoin ⟨j, rfl⟩
  have hAlgU : Algebra.IsAlgebraic (Algebra.adjoin ℤ (Set.range u)) K := by
    refine isAlgebraic_trans hAlgZ ?_
    rintro _ ⟨j, rfl⟩
    have e : z j = (x (l.succAbove j) / x 0) / (x l / x 0) := by
      simp only [hz]; field_simp [hx 0, hl]
    rw [e]
    exact isAlgebraic_div_of_mem (hv _) (hv _) (div_ne_zero hl (hx 0))
  have hU : IsTranscendenceBasis ℤ u :=
    Algebra.IsAlgebraic.isTranscendenceBasis_of_le_trdeg_of_finite ℤ u (by rw [htr]; simp)
  refine ⟨hx, hU.1, ?_⟩

  have hleF : ∀ {v : K}, v ∈ Algebra.adjoin ℤ (Set.range u) → v ∈ ratF x := fun hv =>
    Algebra.adjoin_le (S := subalgebraOfSubring (ratF x).toSubring) Subfield.subset_closure hv
  let ψ : Algebra.adjoin ℤ (Set.range u) →+* ratF x :=
    { toFun := fun v => ⟨v, hleF v.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hψ : Function.Injective ψ := fun a b h => by
    have h' := congrArg Subtype.val h
    exact Subtype.ext h'
  have hAlgF : Algebra.IsAlgebraic (ratF x) K :=
    ⟨fun w => (hAlgU.isAlgebraic w).ringHom_of_comp_eq ψ (RingHom.id K) hψ (by ext; rfl)⟩
  obtain ⟨t, ht⟩ := hA.out
  let T : Set K := (Subtype.val : A → K) '' (t : Set A)
  haveI : Finite T := (t.finite_toSet.image _).to_subtype
  have hfd : FiniteDimensional (ratF x) (IntermediateField.adjoin (ratF x) T) :=
    IntermediateField.finiteDimensional_adjoin fun w _ => (hAlgF.isAlgebraic w).isIntegral
  have hmemA : ∀ a : A, (a : K) ∈ IntermediateField.adjoin (ratF x) T := by
    intro a
    have ha : a ∈ Algebra.adjoin ℤ (t : Set A) := ht ▸ Algebra.mem_top
    induction ha using Algebra.adjoin_induction with
    | mem c hc => exact IntermediateField.subset_adjoin _ _ ⟨c, hc, rfl⟩
    | algebraMap n => simpa using IntermediateField.intCast_mem _ n
    | add a b _ _ ha hb => simpa using add_mem ha hb
    | mul a b _ _ ha hb => simpa using mul_mem ha hb
  have htop : IntermediateField.adjoin (ratF x) T = ⊤ := by
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨a, ha, b, hb, _, rfl⟩ := hfr w
    exact div_mem (hmemA ⟨a, ha⟩) (hmemA ⟨b, hb⟩)
  rw [htop] at hfd
  exact IntermediateField.topEquiv.toLinearEquiv.finiteDimensional

end GlobalTheory.HSAmp.TrBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransgressionDensityHolomorphicChartEtale
section
open MeasureTheory Filter Topology GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.GoodTop
open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff Matrix

namespace GlobalTheory.GoodTop

theorem corrTop_holoChart_trans : ∀ {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {m : ℕ} (E : Fr (ratOf X) (fun _ : Unit => m) 0) (O : X.X.Opens) (H H₀ : Mat (fun _ : Unit => m) X.Fn → CxPts X.str σ → Mat (fun _ : Unit => m) ℂ), IsMetricOn E O H → IsMetricOn E ⊤ H₀ → ∀ {ρ : CxPts X.str σ → ℝ}, (∀ y, CInfAt ρ y) → ∀ {e : OpenPartialHomeomorph (CxPts X.str σ) (V X.dim)}, IsHoloChart e → ∀ (c : AlgChart X.str σ X.dim) {y : CxPts X.str σ}, y ∈ ptsIn X.str σ O → y ∈ e.source → y ∈ c.e.source → ∀ {A : Mat (fun _ : Unit => m) X.Fn}, A ∈ E.S (under y) → corrTop (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) = ‖transDet e c.e y‖ ^ 2 * corrDens E H₀ H ρ c y := by
  intro F _ σ X m E O H H₀ hM hM₀ ρ hρ e he c y hy hey hcy A hA
  set A' := (E.nonempty (under y)).choose with hA'def
  have hA' : A' ∈ E.S (under y) := (E.nonempty (under y)).choose_spec
  have hy₀ : y ∈ ptsIn X.str σ (⊤ : X.X.Opens) := GlobalTheory.CxPts.mem_ptsIn_top

  set φ : V X.dim → V X.dim := c.e ∘ e.symm with hφ
  have ho := isOpen_over e c.e.open_source
  have hm := mem_over e hey hcy
  have e₂ : φ (e y) = c.e y := congrArg c.e (e.left_inv hey)
  have hφa : AnalyticAt ℂ φ (e y) :=
    GlobalTheory.SCV.analyticAt_of_differentiableOn (GlobalTheory.T.differentiableOn_holomorphicChart_trans_etaleChart he c) (ho.mem_nhds hm)

  set ρc : V X.dim → ℝ := fun v => ρ (c.e.symm v)
  set G₀ : Mat (fun _ : Unit => m) X.Fn → V X.dim → Matrix (Fin m) (Fin m) ℂ := fun B v => H₀ B (c.e.symm v) ()
  set G₁ : Mat (fun _ : Unit => m) X.Fn → V X.dim → Matrix (Fin m) (Fin m) ℂ := fun B v => H B (c.e.symm v) ()
  have hback : ∀ w ∈ e.target ∩ e.symm ⁻¹' c.e.source, c.e.symm (φ w) = e.symm w := fun w hw =>
    c.e.left_inv hw.2

  have step1 : corrC (fun v => ρ (e.symm v)) (fun v => H₀ A (e.symm v) ()) (fun v => H A (e.symm v) ()) (e y) =
      corrC (fun v => ρc (φ v)) (fun v => G₀ A (φ v)) (fun v => G₁ A (φ v)) (e y) := by
    apply GlobalTheory.T.transgressionTopCoeffComplex_germ_congr
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [ρc, hback w hw]
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [G₀, hback w hw]
    · filter_upwards [ho.mem_nhds hm] with w hw
      simp only [G₁, hback w hw]

  have hρc : ContDiffAt ℝ ∞ ρc (c.e y) := _root_.GlobalTheory.GoodTop.contDiffAt_holoChart c.holo hcy (hρ y)
  have hG₀ := hM₀.mContDiffAt_chart hy₀ c hcy hA ()
  have hG₀u := hM₀.isUnit_det_chart hy₀ c hcy hA ()
  have hG₁ := hM.mContDiffAt_chart hy c hcy hA ()
  have hG₁u := hM.isUnit_det_chart hy c hcy hA ()
  have step2 : corrC (fun v => ρc (φ v)) (fun v => G₀ A (φ v)) (fun v => G₁ A (φ v)) (e y) =
      ((‖(fderiv ℂ φ (e y)).det‖ ^ 2 : ℝ) : ℂ) * corrC ρc (G₀ A) (G₁ A) (φ (e y)) := by
    apply GlobalTheory.T.transgressionTopCoeff_comp_holomorphic_jacobian_sq (hφa.contDiffAt)
    · rw [e₂]; exact hρc.differentiableAt (by simp)
    · rw [e₂]; exact hG₀
    · rw [e₂]; exact hG₀u
    · rw [e₂]; exact hG₁
    · rw [e₂]; exact hG₁u

  obtain ⟨hQ, hQu, hQh⟩ := _root_.GlobalTheory.GoodTop.changeFrame_holoChart E (e := c.e) c.holo hcy hA hA'
  have step3 : corrC ρc (G₀ A) (G₁ A) (c.e y) = corrC ρc (G₀ A') (G₁ A') (c.e y) := by
    rw [← GlobalTheory.T.transgressionTopCoeff_holomorphic_frame_change ρc hG₀ hG₀u hG₁ hG₁u hQ hQu hQh]
    have hO : ∀ᶠ z in 𝓝 y, z ∈ ptsIn X.str σ O := (isOpen_ptsIn O).mem_nhds hy
    have hev := (c.e.tendsto_symm hcy).eventually
      (hO.and ((GlobalTheory.FrameLift.eventually_mem hA).and (GlobalTheory.FrameLift.eventually_mem hA')))
    apply GlobalTheory.T.transgressionTopCoeffComplex_germ_congr
    · exact Filter.EventuallyEq.rfl
    · filter_upwards [hev] with w hw
      simp only [G₀, Matrix.transpose_transpose]
      rw [hM₀.trans _ GlobalTheory.CxPts.mem_ptsIn_top A hw.2.1 A' hw.2.2 ()]
      congr 1
    · filter_upwards [hev] with w hw
      simp only [G₁, Matrix.transpose_transpose]
      rw [hM.trans _ hw.1 A hw.2.1 A' hw.2.2 ()]
      congr 1
  simp only [corrTop, corrDens]
  rw [← hA'def]
  rw [step1, step2, e₂, step3, Complex.re_ofReal_mul]
  have hT : transDet e c.e y = (fderiv ℂ φ (e y)).det := rfl
  rw [hT]
  ring

end GlobalTheory.GoodTop
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransportSymmetricLiftsThetaGroupTrait
section
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.ThetaMove

theorem GlobalTheory.ThetaMove.ptSec_transl' {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (p x : T ⟶ A) :
    (ptSecT A p).left ≫ (translT A x).left = (ptSecT A (x * p)).left := by
  rw [← Over.comp_left]
  congr 1
  rw [ptSecT, translT, comp_lift, lift_fst, ptSecT, translPt_eq, MonObj.comp_mul, lift_fst_assoc, Category.id_comp,
    lift_snd]

theorem GlobalTheory.ThetaMove.translT_inv {S : Scheme.{0}} {A : Over S} [GrpObj A] {T : Over S} (x : T ⟶ A) :
    (translT A x).left ≫ (translT A x⁻¹).left = 𝟙 _ ∧ (translT A x⁻¹).left ≫ (translT A x).left = 𝟙 _ := by
  constructor
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, inv_mul_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]
  · rw [← Over.comp_left, GlobalTheory.PullMove.translT_mul, mul_inv_cancel, GlobalTheory.PullMove.translT_one, Over.id_left]

theorem GlobalTheory.ThetaMove.transport_symLift : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], Base R → ∀ (D : DegData R (maximalIdeal R)) (C : LabCover D) (j : ℕ) (wA : LB.Iso C.A.L (C.P.L.L.pull C.α)), wA.IsGen → ∀ (W : Type) [CommRing W] [IsDomain W] [IsLocalRing W] (T : Trait C W) (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] [Algebra (FractionRing W) F], (∀ r, algebraMap (FractionRing R) F (algebraMap R _ r) = algebraMap (FractionRing W) F (algebraMap W _ (T.φ r))) → ∀ f : (TFK (R := W) F ⊗ T.A.A).left ⟶ (TFK (R := R) F ⊗ C.A.A).left, IsIso f → f ≫ (fst (TFK (R := R) F) C.A.A).left = (fst (TFK (R := W) F) T.A.A).left → f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α = (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β → ∀ w₀ : LB.Iso (T.A.L.pull T.U.gen.hom.left) (T.U.LG.L.pull (pullback.fst T.G.hom (jK W))), w₀.IsGen → ∀ (x' : TFK (R := W) F ⟶ T.A.A) (x : TFK (R := R) F ⟶ C.A.A), (ptSecT T.A.A x').left ≫ f = (ptSecT C.A.A x).left → x' ^ (C.n ^ j) = 1 → ((∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ') → ∃ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ) ∧ ∀ θ : ThetaGrp C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := R) F), SymLift C.A.A C.A.L (C.n ^ j : ℕ) (C.n ^ j) x θ → ∃ θ' : ThetaGrp T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) (TFK (R := W) F), SymLift T.A.A T.A.L (C.n ^ j : ℕ) (C.n ^ j) x' θ' ∧ ∀ (σ σ' : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j)) (τ τ' : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) → (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ' p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ' q z Jt) → IsActOf T.A.A T.A.L ((C.n ^ j : ℕ) : ℤ) θ' σ σ' → IsActOf C.A.A C.A.L ((C.n ^ j : ℕ) : ℤ) θ τ τ' := by
  intro R _ _ _ hR D C j wA hwA W _ _ _ T F _ _ _ _ hφ f hf hf1 hf2 w₀ hw₀ x' x hx hx'
  have hPL := C.P.L.isLB
  have hAL := C.A.isLB
  have hGL := T.U.LG.isLB
  have hTL := T.A.isLB
  have hgi : T.U.gen.inv.left ≫ T.U.gen.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, Iso.inv_hom_id, Over.id_left]
  obtain ⟨w, hw, hgw⟩ := _root_.GlobalTheory.IsoRes.exists_iso_restrict hGL hTL hgi w₀ hw₀
  have h₁ : f ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α =
      (snd (TFK (R := W) F) T.A.A).left ≫ (T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.β := by
    rw [Category.assoc]; exact hf2
  have hT1 := GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 x' x hx
  have hneg := GlobalTheory.T.traitFibreIso_comm_neg C T F f hf1 hf2
  have hinv : f ≫ (translT C.A.A x⁻¹).left = (translT T.A.A x'⁻¹).left ≫ f := by
    calc f ≫ (translT C.A.A x⁻¹).left
        = ((translT T.A.A x'⁻¹).left ≫ (translT T.A.A x').left) ≫ f ≫ (translT C.A.A x⁻¹).left := by
          rw [(translT_inv x').2, Category.id_comp]
      _ = (translT T.A.A x'⁻¹).left ≫ (f ≫ (translT C.A.A x).left) ≫ (translT C.A.A x⁻¹).left := by
          rw [hT1]; simp only [Category.assoc]
      _ = (translT T.A.A x'⁻¹).left ≫ f := by
          rw [Category.assoc, (translT_inv x).1, Category.comp_id]
  have hpt : ∀ i : ℕ, (ptSecT T.A.A (x' ^ i)).left ≫ f = (ptSecT C.A.A (x ^ i)).left := by
    intro i
    induction i with
    | zero =>
      rw [pow_zero, pow_zero, ← inv_mul_cancel x', ← inv_mul_cancel x, ← ptSec_transl', ← ptSec_transl',
        Category.assoc, ← hinv, ← Category.assoc, hx]
    | succ i ih =>
      rw [pow_succ', pow_succ', ← ptSec_transl', ← ptSec_transl', Category.assoc, ← hT1, ← Category.assoc, ih]
  have hpow : ∀ i : ℕ, f ≫ (translT C.A.A (x ^ i)).left = (translT T.A.A (x' ^ i)).left ≫ f :=
    fun i => GlobalTheory.T.traitFibreIso_comm_translation C T F f hf1 hf2 _ _ (hpt i)
  have hG0 : ((snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) ≫ T.G.hom =
      (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
    have e1 : T.U.gen.inv.left ≫ pullback.snd T.G.hom (jK W) = T.A.A.hom := Over.w T.U.gen.inv
    have e2 : (snd (TFK (R := W) F) T.A.A).left ≫ T.A.A.hom = (fst (TFK (R := W) F) T.A.A).left ≫ jFK (R := W) F :=
      (Over.w (snd (TFK (R := W) F) T.A.A)).trans (Over.w (fst (TFK (R := W) F) T.A.A)).symm
    have e3 : jFK (R := W) F ≫ jK W = spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) := by
      unfold jFK jK spMap
      rw [← Spec.map_comp]
      rfl
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc T.U.gen.inv.left, e1, ← Category.assoc,
      e2, Category.assoc, e3]
  let JPc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ C.G.left) → C.P.L.L.ι := fun z ψ => (exists_chart hPL (ψ z)).choose
  have gJP : ∀ {Z : Scheme.{0}} (z : Z), Good C.P.L.L z (JPc z) := fun z ψ => (exists_chart hPL (ψ z)).choose_spec
  let JGc : ∀ {Z : Scheme.{0}} (z : Z), (Z ⟶ T.G.left) → T.U.LG.L.ι := fun z ψ => (exists_chart hGL (ψ z)).choose
  have gJG : ∀ {Z : Scheme.{0}} (z : Z), Good T.U.LG.L z (JGc z) := fun z ψ => (exists_chart hGL (ψ z)).choose_spec
  let Ψ : ∀ {Z : Scheme.{0}}, (Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) → ∀ z : Z, ((Z ⟶ C.A.A.left) → C.A.L.ι) →
      ((Z ⟶ T.A.A.left) → T.A.L.ι) → (Z.presheaf.stalk z)ˣ := fun q z JA Jt =>
    tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left q z (JPc z) JA (JGc z) Jt
  have conv : ∀ (σ : SecK T.A.L (snd (TFK (R := W) F) T.A.A).left (C.n ^ j))
      (τ : SecK C.A.L (snd (TFK (R := R) F) C.A.A).left (C.n ^ j)), (∀ (Z : Scheme.{0}) (p : Z ⟶ T.G.left) (p' : Z ⟶ (TFK (R := R) F ⊗ C.A.A).left) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left), q ≫ f = p' → p ≫ T.β = p' ≫ (snd (TFK (R := R) F) C.A.A).left ≫ C.α → p ≫ T.G.hom = q ≫ (fst (TFK (R := W) F) T.A.A).left ≫ spMap ((algebraMap (FractionRing W) F).comp (algebraMap W _)) → ∀ z JP JA JG Jt, Good C.P.L.L z JP → Good C.A.L z JA → Good T.U.LG.L z JG → Good T.A.L z Jt → (gw wA (p' ≫ (snd (TFK (R := R) F) C.A.A).left) z (JP (p ≫ T.β)) (JA (p' ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ p' z JA = (gw T.ℓ p z (JP (p ≫ T.β)) (JG p) ^ (C.n ^ j)).val * (gw w₀ (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left) z (JG (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W))) (fun _ => Jt (q ≫ (snd (TFK (R := W) F) T.A.A).left)) ^ (C.n ^ j)).val * sval σ q z Jt) →
      ∀ (Z : Scheme.{0}) (q : Z ⟶ (TFK (R := W) F ⊗ T.A.A).left) (z : Z) JA Jt, Good C.A.L z JA → Good T.A.L z Jt →
        sval τ (q ≫ f) z JA = (Ψ q z JA Jt ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt := by
    intro σ τ hr Z q z JA Jt hJA hJt
    have e := hr Z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W)) (q ≫ f) q
      rfl (by simp only [Category.assoc]; rw [hf2]) (by rw [Category.assoc, hG0]) z (JPc z) JA (JGc z) Jt (gJP z) hJA
      (gJG z) hJt
    simp only [Category.assoc] at e
    show sval τ (q ≫ f) z JA = ((tf wA T.ℓ w f (snd (TFK (R := R) F) C.A.A).left (snd (TFK (R := W) F) T.A.A).left
      q z (JPc z) JA (JGc z) Jt) ^ ((C.n ^ j : ℕ) : ℤ)).val * sval σ q z Jt
    simp only [tf, hgw, Category.assoc]
    rw [zpow_natCast, mul_pow, mul_pow, inv_pow, Units.val_mul, Units.val_mul]
    calc sval τ (q ≫ f) z JA
        = (((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left))) ^ (C.n ^ j))⁻¹).val *
          ((gw wA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left) z
            (JPc z (q ≫ (snd (TFK (R := W) F) T.A.A).left ≫ T.U.gen.inv.left ≫ pullback.fst T.G.hom (jK W) ≫ T.β))
            (JA (q ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left)) ^ (C.n ^ j)).val * sval τ (q ≫ f) z JA) := by
          rw [← _root_.mul_assoc, ← Units.val_mul, _root_.inv_mul_cancel, Units.val_one, _root_.one_mul]
      _ = _ := by rw [e]; ring
  have hs₂ : ∀ p : TFK (R := W) F ⟶ T.A.A, (translT T.A.A p).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (translPt T.A.A p).left := fun p => by rw [← Over.comp_left, translT, lift_snd]
  have hn₂ : (negT T.A.A (TFK (R := W) F)).left ≫ (snd (TFK (R := W) F) T.A.A).left =
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left := by rw [← Over.comp_left, negT, lift_snd]
  have hn₃ : (negT T.A.A (TFK (R := W) F)).left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left =
      f ≫ (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left := by
    rw [← Category.assoc, ← hneg, Category.assoc, ← Over.comp_left, negT, lift_snd]
  have hs₃ : (translT T.A.A x').left ≫ f ≫ (snd (TFK (R := R) F) C.A.A).left = f ≫ (translPt C.A.A x).left := by
    rw [← Category.assoc, ← hT1, Category.assoc, ← Over.comp_left, translT, lift_snd]
  refine ⟨?_, ?_⟩
  · rintro ⟨⟨pt', φ', hφ'⟩, hs'⟩
    have e0 : pt' = x' := hs'.pt_eq
    subst e0
    obtain ⟨u, hu, hvu⟩ := _root_.GlobalTheory.ThetaMove.exists_gen_up hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A x).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A pt').left (translT T.A.A pt').left h₁
      (hs₂ pt') hs₃ ((C.n ^ j : ℕ) : ℤ) φ' hφ'
    obtain ⟨ν', hν', hsym'⟩ := hs'.sym
    obtain ⟨ν, hν, hvν⟩ := _root_.GlobalTheory.ThetaMove.exists_gen_up hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν' hν'
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x, u, hu⟩, ⟨rfl, corr_of_val hAL fun y J hJ => ?_, ν, hν, corr_of_val hAL fun y J hJ => ?_⟩⟩
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ Ψ hpow hx' Hu _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hs'.pow_eq (inv f), val_one, val_one]
    · have hJt : Good T.A.L y (fun ψ => (exists_chart hTL (ψ y)).choose) := fun ψ => (exists_chart hTL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨x, u, hu⟩ ⟨pt', φ', hφ'⟩ ν ν' Ψ hinv hneg Hu Hν _ (inv f) y J _ hJ hJt
      rw [IsIso.inv_hom_id] at e
      rw [e, val_corr hJt hsym' (inv f), val_one, val_one]
  · rintro ⟨pt, φ, hφ⟩ hs
    have e0 : pt = x := hs.pt_eq
    subst e0
    obtain ⟨u', hu', hvu'⟩ := _root_.GlobalTheory.ThetaMove.exists_down_three hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (translPt C.A.A pt).left (snd (TFK (R := W) F) T.A.A).left (translPt T.A.A x').left (translT T.A.A x').left h₁
      (hs₂ x') hs₃ ((C.n ^ j : ℕ) : ℤ) φ hφ
    obtain ⟨ν, hν, hsym⟩ := hs.sym
    obtain ⟨ν', hν', hvν'⟩ := _root_.GlobalTheory.ThetaMove.exists_down_three hAL hPL hGL hTL wA hwA T.ℓ T.ℓ_gen w hw f (snd (TFK (R := R) F) C.A.A).left
      (snd (TFK (R := R) F) C.A.A ≫ (GrpObj.inv : C.A.A ⟶ C.A.A)).left (snd (TFK (R := W) F) T.A.A).left
      (snd (TFK (R := W) F) T.A.A ≫ (GrpObj.inv : T.A.A ⟶ T.A.A)).left (negT T.A.A (TFK (R := W) F)).left h₁ hn₂ hn₃
      ((C.n ^ j : ℕ) : ℤ) ν hν
    have Hu := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvu' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    have Hν := fun Z q z J J' (hJ : Good C.A.L z J) (hJ' : Good T.A.L z J') =>
      hvν' Z q z (JPc z) J (JGc z) J' (gJP z) hJ (gJG z) hJ'
    refine ⟨⟨x', u', hu'⟩, ⟨rfl, corr_of_val hTL fun y J' hJ' => ?_, ν', hν', corr_of_val hTL fun y J' hJ' => ?_⟩, ?_⟩
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_powValue_eq_of_conjugate_torsion f _ (C.n ^ j) ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hpow hx' Hu _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hs.pow_eq, val_one, val_one]
    · have hJA : Good C.A.L y (fun ψ => (exists_chart hAL (ψ y)).choose) := fun ψ => (exists_chart hAL (ψ y)).choose_spec
      have e := GlobalTheory.T.thetaGroup_symmetryValue_eq_of_conjugate f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ ν ν' Ψ hinv hneg Hu Hν _ (𝟙 _) y _ J' hJA hJ'
      rw [← e, val_corr hJA hsym, val_one, val_one]
    · intro σ σ' τ τ' hr hr' hact
      exact GlobalTheory.T.thetaGroupAction_compat_fibreIso hAL hTL f _ ⟨pt, φ, hφ⟩ ⟨x', u', hu'⟩ Ψ hT1 Hu σ σ' τ τ' (conv σ τ hr) (conv σ' τ' hr') hact
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedSectionRelatedAtZeroShift
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum GlobalTheory.TwFam

namespace GlobalTheory.TwFac

theorem formEq_empty_dε {X Y : Scheme.{0}} (φ φ' : Fin 5 → (Y ⟶ X)) (e : φ' = φ) (n j : ℤ) :
    FormEq (K := PEmpty) PEmpty.elim PEmpty.elim (Sum.elim φ φ') (dε n j) := by
  subst e
  intro U _ h
  simp only [dε, Fintype.prod_sum_type, Sum.elim_inl, Sum.elim_inr, zpow_neg, Finset.prod_inv_distrib,
    mul_inv_cancel, Finset.univ_eq_empty, Finset.prod_empty]

theorem val_tau_psi_zero {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} (hB : D.TauBimult)
    (z : (TF (R := R) (FractionRing R)).left) (J) (hJ : Good D.P.L z J) :
    val (D.tau 0 0) (jFK (R := R) (FractionRing R)) z J = 1 ∧
      val (D.psi 0) (jFK (R := R) (FractionRing R)) z J * val D.rigK (jFK (R := R) (FractionRing R)) z J = 1 := by
  have C : IsCub (DVR.th D (T := TF (R := R) (FractionRing R)) z J) := isCub_cubV D.cub hJ
  have z0 : (0 : D.X) + 0 = 0 := add_zero 0
  have hτ := DVR.tau_mul (𝟙 (TF (R := R) (FractionRing R))) hJ hB 0 0 0
  have hψ := DVR.UUA.psi_add (𝟙 (TF (R := R) (FractionRing R))) hJ (0 : D.X) 0
  have hpt : ∀ a b c : D.X, a = b → ∀ (r : (TF (R := R) (FractionRing R)).left ⟶ _),
      val (D.tau a c) r z J = val (D.tau b c) r z J := by rintro a b c rfl r; rfl
  have hpp : ∀ a b : D.X, a = b → ∀ (r : (TF (R := R) (FractionRing R)).left ⟶ _),
      val (D.psi a) r z J = val (D.psi b) r z J := by rintro a b rfl r; rfl
  rw [hpt _ _ _ z0, cPoint_zero, C.face] at hτ
  have t00 := (mul_left_cancel hτ).symm
  rw [hpp _ _ z0, t00, _root_.one_mul] at hψ
  rw [Over.id_left, Category.id_comp] at t00 hψ
  refine ⟨t00, mul_left_cancel (a := val (D.psi 0) (jFK (R := R) (FractionRing R)) z J) ?_⟩
  rw [_root_.mul_one, ← _root_.mul_assoc]
  exact hψ.symm

theorem trel_zero : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], AdmBase R (maximalIdeal R) → ∀ (D : DegData R (maximalIdeal R)), ∀ (a a' : D.toPre.P.A ⟶ D.toPre.P.A) (h h' : D.toPre.X →+ D.toPre.X), EndData D.toPre a a' h h' → ∀ N : ℕ, 1 ≤ N → ∀ (s₀ : SecT D.toPre a N (-1) 0) (s' : SecT D.toPre a N (-1) (shift h h' N (-1) 0)), (∀ (Z : Scheme.{0}) (x : Z ⟶ D.toPre.P.A.left) (z : Z) (J), Good D.toPre.P.L z J → sval s' x z J = sval s₀ x z J) → TRel h 0 s₀ s' := by
  intro R _ _ _ hR D a a' h h' hE N _ s₀
  have hs : shift h h' N (-1) 0 = 0 := by simp [shift]
  generalize shift h h' N (-1) 0 = β' at hs
  subst hs
  intro s' hv u hu Z x z J hJ
  have hL := D.toPre.P.isLB
  have htr : (DegPre.trF D.toPre (FractionRing R) 0).left = 𝟙 _ := by rw [DVR.UUA.trF_zero, Over.id_left]
  have hc0 : D.toPre.c 0 = 1 := by
    have h := D.toPre.c_add 0 0
    rw [add_zero] at h
    exact mul_eq_left.1 h.symm
  have hp : padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0) = 𝟙 _ := by
    rw [hc0, MonObj.comp_one]
    exact _root_.mul_one (𝟙 D.toPre.P.A)
  obtain ⟨u₀, hu₀, -⟩ := exists_gen hL (formEq_empty_dε (tφ D.toPre a 0)
    (fun k => (padd D.toPre.P.A (𝟙 _) (toUnit _ ≫ D.toPre.c 0)).left ≫ tφ D.toPre a 0 k)
    (funext fun k => by rw [hp, Over.id_left, Category.id_comp]) (N : ℤ) (-1)) (LB.oneGen D.toPre.P.L)
    (LB.isGen_oneGen D.toPre.P.L)
  obtain ⟨u', hu', hv'⟩ := exists_gen hL (φ' := dφ D.toPre a 0 0 0) (formEq_empty_dε _ _
    (funext fun k => by rw [htr, Category.id_comp]) (N : ℤ) (-1)) (LB.oneGen D.toPre.P.L)
    (LB.isGen_oneGen D.toPre.P.L)
  have hf : IsFac D.toPre a h N (-1) 0 0 0 u' := by
    refine ⟨hu', fun y I hI => ?_⟩
    obtain ⟨t0, p0⟩ := val_tau_psi_zero D.tau_bimult y I hI
    have hh : val (D.toPre.psi (h 0)) (jFK (R := R) (FractionRing R)) y I =
        val (D.toPre.psi 0) (jFK (R := R) (FractionRing R)) y I :=
      congrArg (fun w => val (D.toPre.psi w) (jFK (R := R) (FractionRing R)) y I) (map_zero h)
    rw [hv' _ _ y I hI, val_one, hh, t0, _root_.mul_one, ← zpow_add, ← mul_zpow, p0, one_zpow]
  have key := (GlobalTheory.T.twistedFactor_exists_unique_const_mul_integralGenerator R hR D a h hE.1 hE.2.2.2.1 N (-1) 0 0 0 u₀ hu₀).2.1 u u' hu hf Z x z J hJ
  rw [key, hv' _ _ z J hJ, val_one, htr, Category.id_comp, Units.val_one, _root_.mul_one]
  exact hv Z _ z J hJ

end GlobalTheory.TwFac
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisationSectionsExtendingPointsMultiplyStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR
open GlobalTheory.Poinc.Sep

open GlobalTheory.Poinc.Tors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.uniformisation_sections_extending_points_multiply : ∀ (V : Type) [CommRing V] [IsDomain V] [IsLocalRing V], IsCN V → ∀ (D : DegData V (maximalIdeal V)) (A : PolAV (Sp (FractionRing V))) (G : Over (Sp V)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (U : Unif (maximalIdeal V) D A G), ∀ (x x' : TFK (R := V) (FractionRing V) ⟶ A.A) (h h' h'' : (𝟙_ (Over (Sp V))) ⟶ G), IntTerm.Ext U.toUnifPre x h → IntTerm.Ext U.toUnifPre x' h' → IntTerm.Ext U.toUnifPre (x * x') h'' → h'' = h * h' := by
  first | exact @GlobalTheory.Poinc.Tors.ext_mul | exact GlobalTheory.Poinc.Tors.ext_mul | (intros; apply GlobalTheory.Poinc.Tors.ext_mul <;> assumption)
end

