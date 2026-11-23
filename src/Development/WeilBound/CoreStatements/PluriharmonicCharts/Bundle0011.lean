module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0032
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.Pull1
public import Development.AutomorphicSpectrum.Definitions.MetricPeriods.IsPeriodOn
public import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.Bundle0013
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.Bundle0004
public import GroundTheory.HeightsAndTheta.Heights.Intersections.Bundle0003
public import Development.AutomorphicSpectrum.Statements.MetricStatements.AgreementIffGuarded
public import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.Bundle0007
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.Bundle0012
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.IntersectionFamilyDefectFormula
public import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphic
public import ReciprocityTheory.AnalyticForms.PotentialTheory.Bundle0003
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0016
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridge
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.Bundle0010

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.ExistsIsDerivAt0Loc
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

noncomputable section

namespace PositivityTheory.Xgp.c_bm_exists_period

open GlobalTheory GlobalTheory.FibreDeriv GlobalTheory.VerticalDeriv

theorem exists_isDerivAt0_loc {g : ℕ} {Z : Scheme.{0}} {B : Set (Fin g → ℂ)} {e : (Fin g → ℂ) → (Sp ℂ ⟶ Z)}
    (hol : IsHolTo B e) (hB : 0 ∈ B) (w : Fin g → ℂ) :
    ∃ v : Sp (DualNumber ℂ) ⟶ Z, IsDerivAt0 e w v := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := Z) (U := ⊤)
    (x := e 0 (default : PrimeSpectrum ℂ)) trivial
  have h0 : ⊤ ≤ e 0 ⁻¹ᵁ U := (top_le_preimage_iff_mem _ U).2 hxU
  have hd := LocalLift.hol_differentiableAt hol hB h0
  let J : Γ(Z, U) →+* DualNumber ℂ :=
    { toFun := fun f => jet w (fun z => valAt' (e z) U f)
      map_one' := by
        have : (fun z => valAt' (e z) U 1) =ᶠ[nhds 0] fun _ => 1 := by
          filter_upwards [LocalLift.hol_eventually_mem hol hB h0] with z hz
          exact valAt'_one _ hz.2
        rw [jet_congr w this, jet_const, map_one]
      map_zero' := by
        simp only [valAt'_zero]
        rw [jet_const, map_zero]
      map_add' := fun f f' => by
        simp only [valAt'_add]
        exact jet_add w (hd f) (hd f')
      map_mul' := fun f f' => by
        simp only [valAt'_mul]
        exact jet_mul w (hd f) (hd f') }
  obtain ⟨v, hv, hve⟩ := TangentOrigin.exists_evalPt_eq hU J
  refine ⟨v, isDerivAt0_of_affine ?_ hU hv fun a => ⟨hd a, DFunLike.congr_fun hve a⟩⟩
  refine TangentOrigin.ext_evalPt hU ((TangentOrigin.top_le_preimage_iff v U).1 hv) h0 (RingHom.ext fun f => ?_)
  refine (TangentOrigin.evalPt_spMap_comp TangentOrigin.fstC v U hv _ f).trans ?_
  rw [hve, ← TangentOrigin.valAt'_eq_evalPt]
  exact fst_jet w (fun z => valAt' (e z) U f)

end PositivityTheory.Xgp.c_bm_exists_period
end
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XCFlArith
section
open MvPolynomial MeasureTheory Filter Topology Matrix ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped ComplexOrder Classical

theorem PositivityTheory.Xgp.t_c_fl_arith : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) := by
  intro Ψ _ _ _ N hN
  have h := FlagArithVar.proof Ψ N hN
  rwa [dimFl, ← Nat.choose_two_right] at h
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.XFlArith
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

noncomputable section

namespace PositivityTheory.Xgp.fl_arith

open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter GroundTheory.Heights₂.Heights.CoordinateConeArithVar FlagArithVar

theorem arith_of_trdeg {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω] [CharZero Ω]
    (hK : Nonempty K) (y : (Σ k, ι k) → Ω) (c : ∀ k, ι k) (hc : ∀ k, y ⟨k, c k⟩ ≠ 0) (d : ℕ)
    (hd : Algebra.trdeg ℤ (Subfield.closure (coneRatios y c)) = (d : Cardinal)) :
    IsArithVar (mCoordIdeal y) (d + 1) := by
  have hhor : IsHorizontal (mCoordIdeal y) := horizontal y
  refine ⟨hK, ⟨RingHom.ker_isPrime _, isMultiHomogIdeal y, relevant y _ hc⟩, hhor, ?_⟩
  have htr := ConeTrdeg.full _ ι (ratioField y c) (ratioPtL y c) (birational y _ hc)
    (fun k ↦ ⟨c k, fun h0 ↦ by
      have h1 := congrArg Subtype.val h0
      simp [ratioPtL, ratioPt, hc] at h1⟩)
    (by rw [mCoordIdeal_ratioPtL y _ hc]; exact hhor)
  have hL : Algebra.trdeg ℤ (ratioField y c) = ((d : ℕ) : Cardinal) := by
    rw [CoordinateConeArithVar.ratioField, trdeg_int_adjoin]
    exact hd
  rw [mCoordIdeal_ratioPtL y _ hc, hL] at htr
  have : (mCoordIdeal y).IsPrime := RingHom.ker_isPrime _
  have hA := IntDomainDim.full (MRing ι ⧸ mCoordIdeal y) (algebraMap_injective _ hhor)
  rw [hA, htr, ← Nat.cast_add, Cardinal.toENat_nat]
  push_cast
  ring

theorem trdeg_lt {Ω : Type} [Field Ω] [CharZero Ω] (L' L : Subfield Ω) (h : L' ≤ L) (t : Ω) (ht : t ∈ L)
    (σ : ℕ → Ω →+* Ω) (hσ : ∀ n, ∀ x ∈ L', σ n x = x) (hinj : Function.Injective fun n => σ n t) (D : ℕ)
    (hD : Algebra.trdeg ℤ L = (D : Cardinal)) : ∃ d < D, Algebra.trdeg ℤ L' = (d : Cardinal) := by
  letI : Algebra L' L := (Subfield.inclusion h).toAlgebra
  haveI : IsScalarTower ℤ L' L := IsScalarTower.of_algebraMap_eq' (RingHom.ext_int _ _)
  haveI : FaithfulSMul ℤ L' := (faithfulSMul_iff_algebraMap_injective ℤ L').mpr Int.cast_injective
  haveI : FaithfulSMul L' L := (faithfulSMul_iff_algebraMap_injective L' L).mpr (algebraMap L' L).injective
  haveI : Algebra.Transcendental L' L := by
    refine ⟨⟨t, ht⟩, ?_⟩
    rintro ⟨p, hp0, hp⟩
    have h1 : Polynomial.eval₂ L'.subtype t p = 0 := by
      have := congrArg L.subtype hp
      rw [Polynomial.aeval_def, Polynomial.hom_eval₂, map_zero] at this
      exact this
    have h2 : ∀ n, (p.map L'.subtype).IsRoot (σ n t) := fun n => by
      have := congrArg (σ n) h1
      rw [Polynomial.hom_eval₂, map_zero] at this
      have e : (σ n).comp L'.subtype = L'.subtype := RingHom.ext fun x => hσ n x x.2
      rw [e] at this
      rw [Polynomial.IsRoot, Polynomial.eval_map]
      exact this
    refine Polynomial.map_ne_zero (f := L'.subtype) hp0 (Polynomial.eq_zero_of_infinite_isRoot _ ?_)
    exact Set.infinite_of_injective_forall_mem hinj h2
  have hadd := trdeg_add_eq ℤ L' (A := L)
  have hpos := trdeg_pos L' L
  rw [hD] at hadd
  have hfin : Algebra.trdeg ℤ L' < Cardinal.aleph0 :=
    (le_self_add.trans hadd.le).trans_lt (Cardinal.natCast_lt_aleph0)
  have hfin2 : Algebra.trdeg L' L < Cardinal.aleph0 :=
    (le_add_self.trans hadd.le).trans_lt (Cardinal.natCast_lt_aleph0)
  obtain ⟨d, hd⟩ := Cardinal.lt_aleph0.1 hfin
  obtain ⟨e, he⟩ := Cardinal.lt_aleph0.1 hfin2
  rw [he] at hpos
  rw [hd, he] at hadd
  refine ⟨d, ?_, hd⟩
  have a1 : d + e = D := by exact_mod_cast hadd
  have a2 : 0 < e := by exact_mod_cast hpos
  omega

variable {Ψ : Type} [DecidableEq Ψ] {N : ℕ}

def r0 (q₀ : FlBlock Ψ N) : Fin N := ⟨q₀.2, by have := q₀.2.2; omega⟩

def r1 (q₀ : FlBlock Ψ N) : Fin N := ⟨q₀.2 + 1, by have := q₀.2.2; omega⟩

def sub (q₀ : FlBlock Ψ N) (c : ℚ) : MvPolynomial (Ψ × Fin N × Fin N) ℚ →ₐ[ℚ] MvPolynomial (Ψ × Fin N × Fin N) ℚ :=
  aeval fun x => X x + if x.1 = q₀.1 ∧ x.2.1 = r0 q₀ then C c * X (x.1, r1 q₀, x.2.2) else 0

theorem flag_row_one_ne_zero (q₀ : FlBlock Ψ N) : r1 q₀ ≠ r0 q₀ := fun h => by
  have := congrArg Fin.val h
  simp [r0, r1] at this

theorem sub_sub (q₀ : FlBlock Ψ N) (c : ℚ) (p) : sub q₀ (-c) (sub q₀ c p) = p := by
  have : (sub q₀ (-c)).comp (sub q₀ c) = AlgHom.id ℚ _ := by
    refine MvPolynomial.algHom_ext fun x => ?_
    by_cases h : x.1 = q₀.1 ∧ x.2.1 = r0 q₀
    · simp [sub, h, flag_row_one_ne_zero]
    · simp [sub, h]
  exact congrArg (fun φ => φ p) this

theorem sub_inj (q₀ : FlBlock Ψ N) (c : ℚ) : Function.Injective (sub q₀ c) :=
  Function.LeftInverse.injective (sub_sub q₀ c)

def subF (q₀ : FlBlock Ψ N) (c : ℚ) : ΩFl Ψ N →+* ΩFl Ψ N :=
  IsFractionRing.lift (g := (algebraMap _ (ΩFl Ψ N)).comp (sub q₀ c).toRingHom)
    ((IsFractionRing.injective _ _).comp (sub_inj q₀ c))

theorem subF_alg (q₀ : FlBlock Ψ N) (c : ℚ) (p) :
    subF q₀ c (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) _ p) = algebraMap _ _ (sub q₀ c p) :=
  IsFractionRing.lift_algebraMap _ _

def yP (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) : MvPolynomial (Ψ × Fin N × Fin N) ℚ :=
  Matrix.det (Matrix.of fun a b : Fin ((p.1.2 : ℕ) + 1) => X (p.1.1, Fin.castLE (step_le p.1.2) a, p.2.1 b))

theorem sub_yP (q₀ : FlBlock Ψ N) (c : ℚ) (p : Σ q : FlBlock Ψ N, FlIdx Ψ N q) (hp : p.1 ≠ q₀) :
    sub q₀ c (yP p) = yP p := by
  obtain ⟨⟨τ, i⟩, A⟩ := p
  rw [yP, AlgHom.map_det]
  by_cases h : τ = q₀.1 ∧ (q₀.2 : ℕ) < i
  · obtain ⟨h1, h2⟩ := h
    let a0 : Fin ((i : ℕ) + 1) := ⟨q₀.2, by omega⟩
    let a1 : Fin ((i : ℕ) + 1) := ⟨q₀.2 + 1, by omega⟩
    have hne : a0 ≠ a1 := fun e => by have := congrArg Fin.val e; simp [a0, a1] at this
    refine Eq.trans ?_ (Matrix.det_updateRow_add_smul_self _ hne (C c))
    congr 1
    ext1 a b
    by_cases ha : a = a0
    · subst ha
      have e0 : Fin.castLE (step_le i) a0 = r0 q₀ := rfl
      have e1 : Fin.castLE (step_le i) a1 = r1 q₀ := rfl
      simp [sub, e0, e1, h1]
    · have e0 : Fin.castLE (step_le i) a ≠ r0 q₀ := fun e => ha (Fin.ext (congrArg (fun x : Fin N => (x : ℕ)) e))
      simp [sub, e0, Matrix.updateRow_ne ha]
  · congr 1
    ext1 a b
    have e0 : ¬ (τ = q₀.1 ∧ Fin.castLE (step_le i) a = r0 q₀) := by
      rintro ⟨h1, e⟩
      have e' : (a : ℕ) = q₀.2 := congrArg (fun x : Fin N => (x : ℕ)) e
      have h5 : (a : ℕ) < i + 1 := a.2
      refine hp (Prod.ext h1 (Fin.ext ?_))
      have : ¬ (q₀.2 : ℕ) < i := fun h2 => h ⟨h1, h2⟩
      show (i : ℕ) = q₀.2
      omega
    simp [sub, e0]

def nextIdx (q₀ : FlBlock Ψ N) : FlIdx Ψ N q₀ :=
  ⟨fun b => if (b : ℕ) = q₀.2 then r1 q₀ else Fin.castLE (step_le q₀.2) b, fun a b hab => by
    have h1 := a.2
    have h2 := b.2
    rw [Fin.lt_def] at hab ⊢
    dsimp only
    split_ifs <;> simp [r1] <;> omega⟩

def ev1 : MvPolynomial (Ψ × Fin N × Fin N) ℚ →+* ℚ := eval fun x => if x.2.1 = x.2.2 then 1 else 0

theorem ev_lead (q₀ : FlBlock Ψ N) (c : ℚ) : ev1 (sub q₀ c (yP ⟨q₀, leadIdx Ψ N q₀⟩)) = 1 := by
  rw [yP, AlgHom.map_det, RingHom.map_det, ← Matrix.det_one (n := Fin ((q₀.2 : ℕ) + 1))]
  congr 1
  ext a b
  have h2 : (b : ℕ) < q₀.2 + 1 := b.2
  have : r1 q₀ ≠ Fin.castLE (step_le q₀.2) b := fun e => by
    have : (q₀.2 : ℕ) + 1 = b := congrArg (fun x : Fin N => (x : ℕ)) e
    omega
  simp [sub, ev1, leadIdx, Matrix.one_apply, apply_ite (eval _), this]

theorem ev_next (q₀ : FlBlock Ψ N) (c : ℚ) : ev1 (sub q₀ c (yP ⟨q₀, nextIdx q₀⟩)) = c := by
  rw [yP, AlgHom.map_det, RingHom.map_det]
  have : (ev1.mapMatrix ((sub q₀ c).mapMatrix (Matrix.of fun a b : Fin ((q₀.2 : ℕ) + 1) =>
      (X (q₀.1, Fin.castLE (step_le q₀.2) a, (nextIdx q₀).1 b) : MvPolynomial (Ψ × Fin N × Fin N) ℚ)))) =
      Matrix.diagonal fun a => if a = Fin.last _ then c else 1 := by
    ext a b
    have h1 := a.2
    have h2 := b.2
    simp only [sub, ev1, nextIdx, RingHom.mapMatrix_apply, AlgHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply,
      aeval_X, map_add, eval_X, apply_ite (eval _), map_mul, eval_C, map_zero, true_and, Matrix.diagonal_apply,
      Fin.ext_iff, r0, r1, Fin.val_castLE, Fin.val_last, apply_ite Fin.val]
    split_ifs <;> first | omega | simp
  rw [this, Matrix.det_diagonal]
  simp

end PositivityTheory.Xgp.fl_arith

end

open PositivityTheory.Xgp.fl_arith FlagArithVar in
theorem PositivityTheory.Xgp.t_fl_arith : ∀ (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] [Nonempty Ψ] (N : ℕ), 2 ≤ N → IsArithVar (PFl Ψ N) (antisymDegree Ψ N + 1) ∧ ∀ q₀ : FlBlock Ψ N, Nonempty {q : FlBlock Ψ N // q ≠ q₀} → ∃ d₀ < antisymDegree Ψ N + 1, IsArithVar (imageZ (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) (PFl Ψ N)) d₀ := by
  intro Ψ _ _ _ N hN
  have hD : antisymDegree Ψ N = dimFl Ψ N := by rw [dimFl, ← Nat.choose_two_right]; rfl
  rw [hD]
  refine ⟨FlagArithVar.proof Ψ N hN, fun q₀ hK => ?_⟩
  have hc : ∀ q, yFl Ψ N ⟨q, leadIdx Ψ N q⟩ ≠ 0 := fun q => by
    rw [yFl_lead]; exact GenLeadMinorNeZero.full ℚ Ψ N q.1 q.2
  set v := (fun p : Σ q : {q : FlBlock Ψ N // q ≠ q₀}, FlIdx Ψ N q.1 => (⟨p.1.1, p.2⟩ : Σ q, FlIdx Ψ N q)) with hv
  have himg : imageZ v (PFl Ψ N) = mCoordIdeal (yFl Ψ N ∘ v) := by
    ext F
    simp only [PFl, imageZ, mCoordIdeal, Ideal.mem_comap, RingHom.mem_ker, AlgHom.toRingHom_eq_coe,
      RingHom.coe_coe, GroundTheory.Heights₂.Heights.Targets.ImageCoord.mConeMap_rename
        (Subtype.val : {q : FlBlock Ψ N // q ≠ q₀} → FlBlock Ψ N) v (fun _ => rfl) (yFl Ψ N) F]
    exact ⟨fun h => rename_injective _ Subtype.val_injective (by rw [h, map_zero]), fun h => by rw [h, map_zero]⟩
  have hL : Algebra.trdeg ℤ (Subfield.closure (coneRatios (yFl Ψ N) (leadIdx Ψ N))) =
      ((dimFl Ψ N : ℕ) : Cardinal) := by
    have h := trdeg_closure_of_rat _ (FlagRatioTrdeg.full ℚ Ψ N)
    rw [coneRatios_eq]
    exact h
  have hy : ∀ p, yFl Ψ N p = algebraMap _ _ (yP p) := fun _ => rfl
  obtain ⟨d, hd, hd'⟩ := trdeg_lt (Subfield.closure (coneRatios (yFl Ψ N ∘ v) fun q => leadIdx Ψ N q.1)) _
    (Subfield.closure_mono (t := coneRatios (yFl Ψ N) (leadIdx Ψ N)) (by rintro _ ⟨p, rfl⟩; exact ⟨v p, rfl⟩))
    (yFl Ψ N ⟨q₀, nextIdx q₀⟩ / yFl Ψ N ⟨q₀, leadIdx Ψ N q₀⟩)
    (Subfield.subset_closure ⟨⟨q₀, nextIdx q₀⟩, rfl⟩) (fun n => subF q₀ n) (fun n x hx => by
      refine (Subfield.closure_le (t := (subF q₀ n).eqLocusField (RingHom.id _))).2 ?_ hx
      rintro _ ⟨p, rfl⟩
      show subF q₀ n (yFl Ψ N (v p) / yFl Ψ N (v ⟨p.1, _⟩)) = yFl Ψ N (v p) / yFl Ψ N (v ⟨p.1, _⟩)
      rw [map_div₀, hy, hy, subF_alg, subF_alg, sub_yP q₀ _ _ p.1.2, sub_yP q₀ _ _ p.1.2])
    (fun n m hnm => by
      have hne : ∀ n : ℕ, subF q₀ n (yFl Ψ N ⟨q₀, leadIdx Ψ N q₀⟩) ≠ 0 := fun n =>
        (map_ne_zero _).2 (hc q₀)
      simp only [map_div₀] at hnm
      rw [div_eq_div_iff (hne n) (hne m)] at hnm
      simp only [hy, subF_alg, ← map_mul] at hnm
      have := congrArg ev1 (IsFractionRing.injective _ _ hnm)
      simp only [map_mul, ev_lead, ev_next, mul_one] at this
      exact_mod_cast this) _ hL
  refine ⟨d + 1, by omega, ?_⟩
  rw [himg]
  exact arith_of_trdeg hK _ (fun q => leadIdx Ψ N q.1) (fun q => hc q.1) d hd'
end

-- bundled from Development.WeilBound.CoreStatements.PluriharmonicCharts.X_vert_deg
section
open MvPolynomial MeasureTheory Filter Topology ReciprocityTheory.AnForm ReciprocityTheory.AnForm.M ReciprocityTheory.AnForm.P ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.AI ReciprocityTheory.ChartRestriction.G.AI.I1 ReciprocityTheory.ChartRestriction.G.AI.I2 ReciprocityTheory.ChartRestriction.G.AI.I4 GlobalTheory.CompanionTheory.Ar.PB GroundTheory.Heights₂.Heights GroundTheory.Heights₂.Heights.LowerBoundFree

namespace PositivityTheory.Xgp.vert_deg

theorem isC2At_of_isPotential {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {Q : LocPot X}
    (h : IsPotential A Q) (x : X) : IsTwiceDifferentiableAt A Q x := by
  intro j hj
  refine potSmoothAt A Q h x j ⟨(A.chart j).map_source hj, ?_⟩
  show (A.chart j).symm (A.chart j x) ∈ Q.U x
  rw [(A.chart j).left_inv hj]
  exact Q.mem_U x

theorem isNull_zeros {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {s : MRing ι} {a : K → ℕ} (hs : IsMultiHomog s a)
    (hsP : s ∉ P) : IsNull R.A {x | eval (R.lift x x) (map (Int.castRingHom ℂ) s) = 0} := by
  obtain ⟨Ψ, hΨ⟩ := goodProjExists K ι P D hP
  exact fun j => GlobalTheory.CompanionTheory.Ar.Cmp.OneSlot.zeros_null R Ψ hP hΨ hs hsP j

theorem exists_log {e : ℕ} {X : Type} [TopologicalSpace X] (A : FinHolAtlas e X) {U : Set X} (hU : IsOpen U)
    {F : X → ℂ} (hF : A.HoloOn U F) {x : X} (hx : x ∈ U) (h0 : F x ≠ 0) :
    ∃ V : Set X, IsOpen V ∧ x ∈ V ∧ V ⊆ U ∧ ∃ G : X → ℂ, A.HoloOn V G ∧
      ∀ y ∈ V, F y ≠ 0 ∧ Real.log ‖F y‖ = (G y).re := by
  refine ⟨{y | y ∈ U ∧ F y / F x ∈ Complex.slitPlane}, ?_, ⟨hx, ?_⟩, fun y hy => hy.1,
    fun y => Complex.log (F y / F x) + ((Real.log ‖F x‖ : ℝ) : ℂ), fun j y hy => ?_, fun y hy => ?_⟩
  · refine isOpen_iff_mem_nhds.mpr fun z hz => ?_
    have hc := GlobalTheory.CompanionTheory.Ar.PB.Proj.continuousAt_of_holoOn A hF hz.1
    filter_upwards [hU.mem_nhds hz.1, (hc.div_const (F x)).eventually_mem
      (Complex.isOpen_slitPlane.mem_nhds hz.2)] with w h1 h2
    exact ⟨h1, h2⟩
  · rw [div_self h0]
    exact Complex.one_mem_slitPlane
  · have h1 : AnalyticAt ℂ (fun y' => F ((A.chart j).symm y') / F x) y :=
      (hF j y ⟨hy.1, hy.2.1⟩).div analyticAt_const h0
    exact (h1.clog hy.2.2).add analyticAt_const
  · have hq : F y / F x ≠ 0 := Complex.slitPlane_ne_zero hy.2
    have hy0 : F y ≠ 0 := fun h => hq (by rw [h, zero_div])
    refine ⟨hy0, ?_⟩
    rw [Complex.add_re, Complex.log_re, Complex.ofReal_re, norm_div,
      Real.log_div (norm_ne_zero_iff.2 hy0) (norm_ne_zero_iff.2 h0)]
    ring

theorem exists_samePot {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {P J : Ideal (MRing ι)} {D : ℕ}
    (R : AnLogRes P J D) (hP : IsArithVar P (D + 1)) {T : Finset ℕ} {α : ℕ → ℝ} {A B : HermLine ι}
    (h : A = B ∨ VertClose P T α A B) :
    ∃ N : Set R.X, IsNull R.A N ∧ SamePot R.A Nᶜ (potOf R A) (potOf R B) := by
  rcases h with rfl | ⟨f, g, df, dg, hf, hg, hfP, hgP, -, hn, -, -⟩
  · refine ⟨∅, fun j => by simp, fun x _ => ⟨Set.univ, isOpen_univ, Set.mem_univ x, fun _ => 0,
      fun j => analyticOnNhd_const, fun y _ => by simp⟩⟩
  · refine ⟨{x | eval (R.lift x x) (map (Int.castRingHom ℂ) f) = 0} ∪
      {x | eval (R.lift x x) (map (Int.castRingHom ℂ) g) = 0}, fun j => ?_, fun x hx => ?_⟩
    · rw [Set.preimage_union, Set.inter_union_distrib_left]
      exact measure_union_null (isNull_zeros R hP hf hfP j) (isNull_zeros R hP hg hgP j)
    · simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_setOf_eq, not_or] at hx
      obtain ⟨V, hV, hxV, hVU, G, hG, hGe⟩ :=
        exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x f) (R.mem_U x) hx.1
      obtain ⟨V', hV', hxV', -, G', hG', hGe'⟩ :=
        exists_log R.A (R.isOpen_U x) (holoOn_eval_lift R x g) (R.mem_U x) hx.2
      refine ⟨V ∩ V', hV.inter hV', ⟨hxV, hxV'⟩, fun y => G y - G' y, fun j y hy => ?_, fun y hy => ?_⟩
      · exact (hG j y ⟨hy.1, hy.2.1⟩).sub (hG' j y ⟨hy.1, hy.2.2⟩)
      · have hz := R.mem x y (hVU hy.1)
        have e := congrArg Real.log (hn _ hz)
        rw [Real.log_mul (norm_ne_zero_iff.2 (hGe y hy.1).1) (B.pos _ hz.1).ne',
          Real.log_mul (norm_ne_zero_iff.2 (hGe' y hy.2).1) (A.pos _ hz.1).ne',
          (hGe y hy.1).2, (hGe' y hy.2).2] at e
        show Real.log (A.h (R.lift x y)) - Real.log (B.h (R.lift x y)) = (G y - G' y).re
        rw [Complex.sub_re]
        linarith

end PositivityTheory.Xgp.vert_deg

theorem PositivityTheory.Xgp.t_vert_deg : ResExistsStatement → ∀ (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] (P : Ideal (MRing ι)) (D : ℕ) (L L' : Fin D → HermLine ι) (T : Finset ℕ) (α : ℕ → ℝ), IsArithVar P (D + 1) → (∀ j, IsSmoothHerm (L j)) → (∀ j, IsSmoothHerm (L' j)) → (∀ j, L j = L' j ∨ VertClose P T α (L j) (L' j)) → ∀ (Am : HermLine ι) (s : MRing ι), IsSmoothHerm Am → IsSectionOn P Am s → ptsIntegral P (pot L) (logNorm Am s) = ptsIntegral P (pot L') (logNorm Am s) := by
  intro hE K _ ι _ P D L L' T α hP hL hL' hV Am s hAm hs
  obtain ⟨J, ⟨R⟩⟩ := exists_anLogRes hE hP
  choose N hN hS using fun j => PositivityTheory.Xgp.vert_deg.exists_samePot R hP (hV j)
  rw [ptsIntegral_eq_mInt' hE resBridge R hP hL hAm hs, ptsIntegral_eq_mInt' hE resBridge R hP hL' hAm hs]
  refine (mInt_congr_samePot D R.X R.A (⋃ j, N j)ᶜ _ _ _ _ (fun j => ?_) (fun j x hx => hS j x ?_)
    (fun j x _ => PositivityTheory.Xgp.vert_deg.isC2At_of_isPotential _ (isPotential_potOf R (hL' j)) x)
    (fun _ _ => rfl)).1
  · rw [compl_compl, Set.preimage_iUnion, Set.inter_iUnion]
    exact measure_iUnion_null fun i => hN i j
  · exact fun h => hx (Set.mem_iUnion.2 ⟨j, h⟩)
end

