module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
public import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.Bundle0035
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans
public import Development.AutomorphicArithmetic.CMTraceForms.CmDatumDiscriminantDepthBounds
public import Development.AbelianVarietyTheory.Statements.ShortVectorBound.ScaledLatticesInSupLattices
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0033

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MaximalIdealFormalPointsFormModule
section
set_option autoImplicit false
noncomputable section
open IsLocalRing ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB.WickVanishing

namespace GlobalTheory.PlaceInt.FormalPts

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {d : ℕ}

def SmallPt {n : ℕ} (x : Pt V n d) : Prop := ∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V

def subPt {m n : ℕ} (a : Fin m → Pt V n d) (p : Pt V m d) : Pt V n d := fun i => evV a (p i)

theorem small_one {n : ℕ} {x : Pt V n d} (hx : SmallPt x) : ∀ j, SmallPt (![x] j) := by
  intro j
  fin_cases j
  simpa using hx

theorem small_two {n : ℕ} {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : ∀ j, SmallPt (![x, y] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy

theorem small_three {n : ℕ} {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    ∀ j, SmallPt (![x, y, z] j) := by
  intro j
  fin_cases j
  · simpa using hx
  · simpa using hy
  · simpa using hz

variable [IsAdicComplete (maximalIdeal V) V] [CharZero V]

theorem small_evV {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (f : PS V m d)
    (hf : MvPowerSeries.constantCoeff f = 0) : MvPowerSeries.constantCoeff (evV a f) ∈ maximalIdeal V := by
  have S := evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  exact S.2.1 f (by rw [hf]; exact zero_mem _)

theorem evV_ev {l m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (b : Fin l → Pt V m d)
    (hb : ∀ j, GP (b j)) (f : PS V l d) : evV a (ev b f) = evV (fun j => subPt a (b j)) f := by
  have hb' : ∀ p : Fin l × Fin d, MvPowerSeries.constantCoeff (b p.1 p.2) ∈ maximalIdeal V := fun p => by
    rw [hb p.1 p.2]
    exact zero_mem _
  have S := evC_spec V (Fin l × Fin d) (Fin m × Fin d) (Fin n × Fin d) (fun p => b p.1 p.2) hb'
  have e1 : ev b f = evC (fun p : Fin l × Fin d => b p.1 p.2) f := (S.2.2.1 (fun p => hb p.1 p.2) f).symm
  rw [e1]
  exact S.2.2.2 (fun p => a p.1 p.2) (fun p => ha p.1 p.2) f

theorem subPt_pt {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (j : Fin m) :
    subPt a (pt V d j) = a j := by
  funext i
  obtain ⟨⟨ψ, hX, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) (MvPowerSeries.X (j, i)) = a j i
  rw [hψ, hX]

theorem subPt_zero {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) :
    subPt a (0 : Pt V m d) = 0 := by
  funext i
  obtain ⟨⟨ψ, -, hψ⟩, -⟩ :=
    evC_spec V (Fin m × Fin d) (Fin n × Fin d) (Fin n × Fin d) (fun p => a p.1 p.2) (fun p => ha p.1 p.2)
  show evC (fun p : Fin m × Fin d => a p.1 p.2) 0 = 0
  rw [hψ, map_zero]

theorem subPt_addOf {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (F : Fin d → PS V 2 d)
    (p q : Pt V m d) (hp : GP p) (hq : GP q) :
    subPt a (addOf F p q) = addV F (subPt a p) (subPt a q) := by
  funext i
  show evV a (ev ![p, q] (F i)) = evV ![subPt a p, subPt a q] (F i)
  rw [evV_ev a ha ![p, q] (pair_points_zero_constant hp hq) (F i)]
  congr 1
  funext j
  fin_cases j <;> rfl

theorem subPt_comp1 {m n : ℕ} (a : Fin m → Pt V n d) (ha : ∀ j, SmallPt (a j)) (φ : Pt V 1 d)
    (p : Pt V m d) (hp : GP p) : subPt a (comp1 φ p) = compV φ (subPt a p) := by
  funext i
  show evV a (ev ![p] (φ i)) = evV ![subPt a p] (φ i)
  rw [evV_ev a ha ![p] (single_point_zero_constant hp) (φ i)]
  congr 1
  funext j
  fin_cases j
  rfl

variable (G : FGLaw V d) {n : ℕ}

theorem addV_comm {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) : addV G.F x y = addV G.F y x := by
  funext i
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have key := congrArg (evV ![x, y]) (G.comm i)
  rw [evV_ev _ h2 _ (pair_points_zero_constant g1 g0)] at key
  refine key.symm.trans ?_
  show evV (fun j => subPt ![x, y] (![pt V (n := 2) d 1, pt V (n := 2) d 0] j)) (G.F i) = evV ![y, x] (G.F i)
  congr 1
  funext j
  fin_cases j
  · exact subPt_pt _ h2 1
  · exact subPt_pt _ h2 0

theorem addV_assoc {x y z : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) (hz : SmallPt z) :
    addV G.F (addV G.F x y) z = addV G.F x (addV G.F y z) := by
  funext i
  have h3 := small_three hx hy hz
  have g0 : GP (pt V (n := 3) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 3) d 1) := gp_pt 1
  have g2 : GP (pt V (n := 3) d 2) := gp_pt 2
  have e0 : subPt ![x, y, z] (pt V (n := 3) d 0) = x := subPt_pt _ h3 0
  have e1 : subPt ![x, y, z] (pt V (n := 3) d 1) = y := subPt_pt _ h3 1
  have e2 : subPt ![x, y, z] (pt V (n := 3) d 2) = z := subPt_pt _ h3 2
  have key := congrArg (evV ![x, y, z]) (G.assoc i)
  have hl : evV ![x, y, z] (ev ![addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1), pt V (n := 3) d 2] (G.F i)) =
      addV G.F (addV G.F x y) z i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant (gp_addOf G.F G.const _ _ g0 g1) g2)]
    show evV _ (G.F i) = evV ![addV G.F x y, z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 0) (pt V (n := 3) d 1)) = addV G.F x y
      rw [subPt_addOf _ h3 _ _ _ g0 g1, e0, e1]
    · exact e2
  have hr : evV ![x, y, z] (ev ![pt V (n := 3) d 0, addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)] (G.F i)) =
      addV G.F x (addV G.F y z) i := by
    rw [evV_ev _ h3 _ (pair_points_zero_constant g0 (gp_addOf G.F G.const _ _ g1 g2))]
    show evV _ (G.F i) = evV ![x, addV G.F y z] (G.F i)
    congr 1
    funext j
    fin_cases j
    · exact e0
    · show subPt ![x, y, z] (addOf G.F (pt V (n := 3) d 1) (pt V (n := 3) d 2)) = addV G.F y z
      rw [subPt_addOf _ h3 _ _ _ g1 g2, e1, e2]
  exact hl.symm.trans (key.trans hr)

theorem zero_addV {x : Pt V n d} (hx : SmallPt x) : addV G.F 0 x = x := by
  funext i
  have h1 := small_one hx
  have g0 : GP (pt V (n := 1) d 0) := gp_pt 0
  have e : subPt ![x] (pt V (n := 1) d 0) = x := subPt_pt _ h1 0
  have key := congrArg (evV ![x]) (G.unit i)
  rw [evV_ev _ h1 _ (pair_points_zero_constant gp_zero₂ g0)] at key
  refine Eq.trans ?_ (key.trans (congrFun e i))
  show evV ![0, x] (G.F i) = _
  congr 1
  funext j
  fin_cases j
  · exact (subPt_zero _ h1).symm
  · exact e.symm

theorem addV_zero {x : Pt V n d} (hx : SmallPt x) : addV G.F x 0 = x := by
  have h0 : SmallPt (0 : Pt V n d) := fun i => by
    show MvPowerSeries.constantCoeff (0 : PS V n d) ∈ maximalIdeal V
    rw [map_zero]
    exact zero_mem _
  rw [addV_comm G hx h0]
  exact zero_addV G hx

variable {O : Type} [CommRing O] {G} (A : OAct O G)

theorem act_addV (a : O) {x y : Pt V n d} (hx : SmallPt x) (hy : SmallPt y) :
    compV (A.act a) (addV G.F x y) = addV G.F (compV (A.act a) x) (compV (A.act a) y) := by
  have h2 := small_two hx hy
  have g0 : GP (pt V (n := 2) d 0) := gp_pt 0
  have g1 : GP (pt V (n := 2) d 1) := gp_pt 1
  have e0 : subPt ![x, y] (pt V (n := 2) d 0) = x := subPt_pt _ h2 0
  have e1 : subPt ![x, y] (pt V (n := 2) d 1) = y := subPt_pt _ h2 1
  have hφ : GP (A.act a) := A.const a
  have key := congrArg (subPt ![x, y]) (A.hom a)
  unfold FGLaw.add at key
  rw [subPt_comp1 _ h2 _ _ (gp_addOf _ G.const _ _ g0 g1), subPt_addOf _ h2 _ _ _ g0 g1,
    subPt_addOf _ h2 _ _ _ (gp_comp1 _ _ hφ g0) (gp_comp1 _ _ hφ g1), subPt_comp1 _ h2 _ _ g0,
    subPt_comp1 _ h2 _ _ g1, e0, e1] at key
  exact key

theorem add_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a + b)) x = addV G.F (compV (A.act a) x) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a + b)) = addV G.F (subPt ![x] (A.act a)) (subPt ![x] (A.act b))
  rw [A.add_act a b]
  unfold FGLaw.add
  exact subPt_addOf _ (small_one hx) _ _ _ (A.const a) (A.const b)

theorem mul_actV (a b : O) {x : Pt V n d} (hx : SmallPt x) :
    compV (A.act (a * b)) x = compV (A.act a) (compV (A.act b) x) := by
  show subPt ![x] (A.act (a * b)) = compV (A.act a) (subPt ![x] (A.act b))
  rw [A.mul_act a b]
  exact subPt_comp1 _ (small_one hx) _ _ (A.const b)

theorem one_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 1) x = x := by
  show subPt ![x] (A.act 1) = x
  rw [A.one_act]
  exact subPt_pt _ (small_one hx) 0

theorem zero_actV {x : Pt V n d} (hx : SmallPt x) : compV (A.act 0) x = 0 := by
  show subPt ![x] (A.act 0) = 0
  rw [GlobalTheory.FourierChainCompare.act_zero A]
  exact subPt_zero _ (small_one hx)

theorem addV_neg_actV {x : Pt V n d} (hx : SmallPt x) : addV G.F x (compV (A.act (-1)) x) = 0 := by
  have h := add_actV A 1 (-1) hx
  rw [one_actV A hx, add_neg_cancel, zero_actV A hx] at h
  exact h.symm

end GlobalTheory.PlaceInt.FormalPts

namespace GlobalTheory.PlaceInt
open FormalPts

theorem smallPts_module : ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V] [CharZero V] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB V d O) (n : ℕ) (x y z : Pt V n d), (∀ i, MvPowerSeries.constantCoeff (x i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (y i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (z i) ∈ maximalIdeal V) → (∀ i, MvPowerSeries.constantCoeff (addV B.G.F x y i) ∈ maximalIdeal V) ∧ addV B.G.F x y = addV B.G.F y x ∧ addV B.G.F (addV B.G.F x y) z = addV B.G.F x (addV B.G.F y z) ∧ addV B.G.F x 0 = x ∧ addV B.G.F x (compV (B.A.act (-1)) x) = 0 ∧ compV (B.A.act 1) x = x ∧ compV (B.A.act 0) x = 0 ∧ ∀ a b : O, (∀ i, MvPowerSeries.constantCoeff (compV (B.A.act a) x i) ∈ maximalIdeal V) ∧ compV (B.A.act a) (addV B.G.F x y) = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act a) y) ∧ compV (B.A.act (a + b)) x = addV B.G.F (compV (B.A.act a) x) (compV (B.A.act b) x) ∧ compV (B.A.act (a * b)) x = compV (B.A.act a) (compV (B.A.act b) x) := by
  intro V _ _ _ _ _ d O _ _ B n x y z hx hy hz
  refine ⟨fun i => small_evV ![x, y] (small_two hx hy) (B.G.F i) (B.G.const i), addV_comm B.G hx hy,
    addV_assoc B.G hx hy hz, addV_zero B.G hx, addV_neg_actV B.A hx, one_actV B.A hx, zero_actV B.A hx,
    fun a b => ⟨fun i => small_evV ![x] (small_one hx) (B.A.act a i) (B.A.const a i), act_addV B.A a hx hy,
      add_actV B.A a b hx, mul_actV B.A a b hx⟩⟩

end GlobalTheory.PlaceInt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RamifiedPrimeLossLeValuationPrimePower
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceTop
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie

theorem ramLoss_le_vLa_pPow (D : D7) (K : Type) [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) (j : ℕ)
    (w : WeightFamilies.Wt D j) (a b : ℕ) (ha : c2 D w ≤ a) (hb : Formalism.MainNotions.DIV.Cons.cHalf w ≤ b) :
    ramLoss D la w ≤ ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) := by
  have hqp : D.host.q.Prime := D.host.hyp.1
  have hdp : D.host.d.Prime := D.host.hyp.2.1
  obtain ⟨hs, hq, hd, -, -⟩ := UpperTheory.cmDatum_discriminantDepth_bounds D.host.toHostAx
  have hN : pPow D a b b ≠ 0 := by
    unfold pPow
    exact mul_ne_zero (mul_ne_zero (pow_ne_zero _ D.host.QS_pos.ne') (pow_ne_zero _ hqp.ne_zero)) (pow_ne_zero _ hdp.ne_zero)
  have hl := Crude.resCharOf_prime la
  haveI : Fact (resCharOf la).Prime := ⟨hl⟩
  have ha' : (DF w : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (DF w : ℝ) / 2 ≤ b := Nat.ceil_le.1 hb
  have hD : (0 : ℝ) ≤ (DF w : ℝ) := Nat.cast_nonneg _
  have he : (0 : ℝ) ≤ (ramOverZ la : ℝ) := Nat.cast_nonneg _
  have hR : ((vLa la ((pPow D a b b : ℕ) : K) : ℤ) : ℝ) = (padicValNat (resCharOf la) (pPow D a b b) : ℝ) * ramOverZ la := by
    rw [Crude.crv_vLa_natCast la hN, Int.cast_natCast, Nat.cast_mul]
  have hz : ∀ p ∈ D.host.condN.primeFactors, p ≠ resCharOf la →
      ((vLa la (p : K) : ℤ) : ℝ) * D.host.vdH p * (DF w : ℝ) / 2 = 0 := fun p hp hne => by
    have hpp := Nat.prime_of_mem_primeFactors hp
    haveI : Fact p.Prime := ⟨hpp⟩
    rw [Crude.crv_vLa_natCast la hpp.ne_zero, Nat.padicValNat_def, multiplicity_primes hne.symm]; simp
  rw [ramLoss, hR]
  by_cases hm : resCharOf la ∈ D.host.condN.primeFactors
  · rw [Finset.sum_eq_single_of_mem _ hm hz, Crude.crv_vLa_natCast la hl.ne_zero, Nat.padicValNat_def, Nat.Prime.multiplicity_self]
    have key : D.host.vdH (resCharOf la) * (DF w : ℝ) / 2 ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) := by
      have hv0 := D.host.vdH_nonneg (resCharOf la)
      have hle : ∀ k : ℕ, resCharOf la ^ k ∣ pPow D a b b → (k : ℝ) ≤ (padicValNat (resCharOf la) (pPow D a b b) : ℝ) :=
        fun k hk => by exact_mod_cast ((by simpa only [_root_.Nat.padicValNat_def] using @_root_.multiplicity_dvd_iff_le : ∀ {p : _root_.Nat} [hp : _root_.Fact (_root_.Nat.Prime p)] {a n : _root_.Nat} (ha : a ≠ 0), p ^ n ∣ a ↔ n ≤ _root_.padicValNat p a) hN).1 hk
      rcases (D.host.dvd_condN_iff_small hl).1 (Nat.dvd_of_mem_primeFactors hm) with h | h | h
      · have h1 := hle (padicValNat (resCharOf la) D.host.QS * a) (by
          rw [pow_mul]; exact ((pow_dvd_pow_of_dvd (_root_.Dvd.intro_left _ (_root_.Nat.divMaxPow_mul_pow_padicValNat _ _)) a).mul_right _).mul_right _)
        have h2 := (hs _ h).1
        push_cast at h1
        nlinarith [mul_le_mul h2 ha' hD (Nat.cast_nonneg _), mul_nonneg hv0 hD]
      · have h1 := hle b (by rw [h]; exact (Dvd.intro_left _ rfl).mul_right _)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hq hD]
      · have h1 := hle b (by rw [h]; exact Dvd.intro_left _ rfl)
        rw [h] at hv0 ⊢; rw [h] at h1
        nlinarith [mul_le_mul_of_nonneg_right hd hD]
    push_cast
    nlinarith [mul_le_mul_of_nonneg_right key he]
  · rw [Finset.sum_eq_zero fun p hp => hz p hp fun h => hm (h ▸ hp)]
    positivity

end GlobalTheory.PlaceTop
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.WeightNormalizerAndExponentsOfWeightSum
section
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.PlaceScalar
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.L2.Pj GlobalTheory.PtTie GlobalTheory.PlaceTop

theorem ceil_mul_add_le (x y : ℝ) (k : ℕ) : ⌈(k : ℝ) * x + y⌉₊ ≤ k * ⌈x⌉₊ + ⌈y⌉₊ := by
  rw [Nat.ceil_le]
  push_cast
  have h1 := Nat.le_ceil x
  have h2 := Nat.le_ceil y
  have h3 : (k : ℝ) * x ≤ k * (⌈x⌉₊ : ℝ) := mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg k)
  linarith

theorem weight_normalizer_and_exponents_of_weight_sum :
    ∀ (D : D7) (B : WeightFamilies.Prov D) (hinj : Function.Injective D.what₂.OtoLL) (EX : ErrX D) (j : ℕ) (wL wF w : WeightFamilies.Wt D j) (k : ℕ), (∀ τ i, w.aP τ i = wF.aP τ i + k * wL.aP τ i) → (∀ τ i, w.aM τ i = wF.aM τ i + k * wL.aM τ i) → nnW B hinj EX w = nnW B hinj EX wL ^ k * nnW B hinj EX wF ∧ c2 D w ≤ k * c2 D wL + c2 D wF ∧ Formalism.MainNotions.DIV.Cons.cHalf w ≤ k * Formalism.MainNotions.DIV.Cons.cHalf wL + Formalism.MainNotions.DIV.Cons.cHalf wF := by
  intro D B hinj EX j wL wF w k hP hM
  have hp : Formalism.MainNotions.DIV.Cons.Dplus w = k * Formalism.MainNotions.DIV.Cons.Dplus wL + Formalism.MainNotions.DIV.Cons.Dplus wF := by
    simp only [Formalism.MainNotions.DIV.Cons.Dplus, hP, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hm : Formalism.MainNotions.DIV.Cons.Dminus w = k * Formalism.MainNotions.DIV.Cons.Dminus wL + Formalism.MainNotions.DIV.Cons.Dminus wF := by
    simp only [Formalism.MainNotions.DIV.Cons.Dminus, hM, Finset.sum_add_distrib, Finset.mul_sum]
    ring
  have hs : ∀ u : WeightFamilies.Wt D j, WeightAlgebra.DF u = Formalism.MainNotions.DIV.Cons.Dplus u + Formalism.MainNotions.DIV.Cons.Dminus u := by
    intro u
    simp only [WeightAlgebra.DF, WeightAlgebra.degP, Formalism.MainNotions.DIV.Cons.Dplus, Formalism.MainNotions.DIV.Cons.Dminus, Finset.sum_add_distrib]
  have hf : (WeightAlgebra.DF w : ℝ) = k * (WeightAlgebra.DF wL : ℝ) + (WeightAlgebra.DF wF : ℝ) := by
    rw [hs, hs, hs, hp, hm]
    push_cast
    ring
  refine ⟨?_, ?_, ?_⟩
  · simp only [nnW, hp, hm]
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    ring
  · unfold c2
    exact le_of_eq (by exact_mod_cast hf)
  · unfold Formalism.MainNotions.DIV.Cons.cHalf
    have : (WeightAlgebra.DF w : ℝ) / 2 = k * ((WeightAlgebra.DF wL : ℝ) / 2) + (WeightAlgebra.DF wF : ℝ) / 2 := by
      rw [hf]; ring
    rw [this]
    exact ceil_mul_add_le _ _ _

end GlobalTheory.PlaceScalar
end
end

