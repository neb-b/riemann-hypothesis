module

public import Mathlib
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ExistsCombComb

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CentEq
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private def sc {R : Type} [CommRing R] (n : ℕ) : GL (Fin 1) R →* GL (Fin n) R :=
  (GeneralLinearGroup.scalar (Fin n)).comp GeneralLinearGroup.det

private theorem sc_val {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (i j : Fin n) :
    (sc n x).val i j = if i = j then x.val 0 0 else 0 := by
  change Matrix.scalar (Fin n) (Matrix.det x.val) i j = _
  rw [Matrix.det_fin_one]
  by_cases e : i = j <;> simp [e]

private theorem sc_scalar {R : Type} [CommRing R] (n : ℕ) (z : Rˣ) :
    sc n (GeneralLinearGroup.scalar (Fin 1) z) = GeneralLinearGroup.scalar (Fin n) z := by
  ext i j
  rw [sc_val]
  change (if i = j then Matrix.scalar (Fin 1) z.val 0 0 else 0) = Matrix.scalar (Fin n) z.val i j
  by_cases e : i = j <;> simp [e]

private theorem sc_comm {R : Type} [CommRing R] (n : ℕ) (x : GL (Fin 1) R) (g : GL (Fin n) R) :
    sc n x * g = g * sc n x :=
  Units.ext (Matrix.scalar_commute (Matrix.det x.val) (fun _ => Commute.all _ _) g.val).eq

private theorem map_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (p : R →+* S) (x : GL (Fin 1) R) :
    GeneralLinearGroup.map p (sc n x) = sc n (GeneralLinearGroup.map p x) := by
  ext i j
  change p ((sc n x).val i j) = _
  rw [sc_val, sc_val]
  split_ifs
  · rfl
  · exact map_zero p

private theorem corner_sc {R S : Type} [CommRing R] [CommRing S] (n : ℕ) (s : R →ₙ+* S) (x : GL (Fin 1) R) :
    GlobalTheory.CuspRep.cornerGL n s (sc n x) = sc n (GlobalTheory.CuspRep.cornerGL 1 s x) := by
  ext i j
  rw [sc_val]
  change (1 : Matrix (Fin n) (Fin n) S) i j - s ((1 : Matrix (Fin n) (Fin n) R) i j) + s ((sc n x).val i j) =
    if i = j then (1 : Matrix (Fin 1) (Fin 1) S) 0 0 - s ((1 : Matrix (Fin 1) (Fin 1) R) 0 0) + s (x.val 0 0) else 0
  rw [sc_val]
  by_cases e : i = j <;> simp [Matrix.one_apply, e]

private theorem continuous_sc {R : Type} [CommRing R] [TopologicalSpace R] (n : ℕ) :
    Continuous (sc n : GL (Fin 1) R → GL (Fin n) R) := by
  have h : Continuous fun x : GL (Fin 1) R => (sc n x).val := by
    refine continuous_matrix fun i j => ?_
    simp only [sc_val]
    split_ifs
    · exact Units.continuous_val.matrix_elem 0 0
    · exact continuous_const
  refine Units.continuous_iff.2 ⟨h, ?_⟩
  simp only [← map_inv]
  refine continuous_matrix fun i j => ?_
  simp only [sc_val]
  split_ifs
  · exact Units.continuous_coe_inv.matrix_elem 0 0
  · exact continuous_const

private theorem sc_mem {K : Type} [Field K] (n : ℕ) (O : Subring K) (x : GL (Fin 1) K)
    (h : x ∈ Formalism.UG.GLint (Fin 1) O) : sc n x ∈ Formalism.UG.GLint (Fin n) O := by
  rw [GlobalTheory.AdelicU.mem_GLint_iff] at h ⊢
  rw [← map_inv]
  constructor <;> intro i j <;> rw [sc_val] <;> split_ifs
  · exact h.1 0 0
  · exact zero_mem _
  · exact h.2 0 0
  · exact zero_mem _

theorem UpperTheory.V.Af.Smo.centEq :
    UpperTheory.V.Af.Smo.CentLoc → UpperTheory.V.Af.Smo.AwayInd → UpperTheory.V.Af.Smo.DenseAway → UpperTheory.V.Af.Smo.CentEq := by
  intro hL hA hD E _ _ n S B f f' hc hc' hl hl' hE hK hK' z g g'
  have h1 : ∀ k : GL (Fin 1) (Af E), Away S k → ∀ g g' : GA E n,
      f (g * finGL E n (sc n k)) * f' g' = f g * f' (g' * finGL E n (sc n k)) := by
    refine hA E 1 S _ (fun k hk g g' => ?_) (fun w hw k _ _ hP y g g' => ?_)
    · have hk' : InKS S (sc n k) := by
        refine ⟨fun w hw => ?_, fun w => ?_⟩
        · rw [map_sc, hk.1 w hw, map_one]
        · rw [map_sc]; exact sc_mem n _ _ (hk.2 w)
      rw [hK g _ hk', hK' g' _ hk']
    · obtain ⟨c, hcc⟩ := hL E n w (B w) (GeneralLinearGroup.det y)
      have e : sc n (locGL E 1 w y) = locGL E n w (1 * GeneralLinearGroup.scalar (Fin n) (GeneralLinearGroup.det y)) := by
        rw [one_mul]; exact (corner_sc n (sLoc E w) y).symm
      have a := hcc _ ((hE w hw).1 (g * finGL E n (sc n k))) 1
      have b := hcc _ ((hE w hw).2 (g' * finGL E n (sc n k))) 1
      simp only [map_one, mul_one] at a b
      rw [map_mul, map_mul, ← mul_assoc, ← mul_assoc, e, a, b, mul_assoc, hP]
      ring
  have h2 : ∀ x : GA E 1, f (g * sc n x) * f' g' = f g * f' (g' * sc n x) := by
    refine isClosed_property (hD E 1 S).denseRange_val (isClosed_eq ?_ ?_) ?_
    · exact (hc.comp (continuous_const.mul (continuous_sc n))).mul continuous_const
    · exact continuous_const.mul (hc'.comp (continuous_const.mul (continuous_sc n)))
    · rintro ⟨_, γ, k, hk, rfl⟩
      have e : ∀ u : GA E n, u * sc n (ratGL E 1 γ * finGL E 1 k) = ratGL E n (sc n γ) * (u * finGL E n (sc n k)) := by
        intro u
        rw [map_mul, ← mul_assoc, ← sc_comm n (ratGL E 1 γ) u, mul_assoc]
        congr 1
        · exact (map_sc n _ γ).symm
        · exact congrArg _ (corner_sc n (sFin E) k).symm
      change f (g * sc n (ratGL E 1 γ * finGL E 1 k)) * _ = _ * f' (g' * sc n (ratGL E 1 γ * finGL E 1 k))
      rw [e, e]
      have a : ∀ u, f (ratGL E n (sc n γ) * u) = f u := hl _
      have b : ∀ u, f' (ratGL E n (sc n γ) * u) = f' u := hl' _
      rw [a, b]
      exact h1 k hk g g'
  rw [← sc_scalar]
  exact h2 _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.CentLoc
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem scalar_comm' {K : Type} [Field K] {n : ℕ} (y : Kˣ) (g : GL (Fin n) K) :
    GeneralLinearGroup.scalar (Fin n) y * g = g * GeneralLinearGroup.scalar (Fin n) y :=
  Units.ext (Matrix.scalar_commute (y : K) (fun _ => Commute.all _ _) g.val).eq

private theorem finsum_top {K : Type} [Field K] {n : ℕ} (O : Subring K) (ϖ : Kˣ) (W : GL (Fin n) K → ℂ)
    (hW : ∀ g, ∀ k ∈ Formalism.UG.GLint (Fin n) O, W (g * k) = W g) (g : GL (Fin n) K) :
    ∑ᶠ c : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O, Formalism.UG.Tj ℂ n O (ϖ : K) n c.out * W (g * c.out) =
      W (g * GeneralLinearGroup.scalar (Fin n) ϖ) := by
  set z : GL (Fin n) K := GeneralLinearGroup.scalar (Fin n) ϖ with hz
  have hd : Formalism.UG.diagJ n (ϖ : K) n = z.val := by
    simp [Formalism.UG.diagJ, hz]
  rw [finsum_eq_single _ (z : GL (Fin n) K ⧸ Formalism.UG.GLint (Fin n) O)]
  · obtain ⟨k, hk⟩ := QuotientGroup.mk_out_eq_mul (Formalism.UG.GLint (Fin n) O) z
    rw [hk, ← mul_assoc, hW _ _ k.2, Formalism.UG.Tj, Set.indicator_of_mem, Pi.one_apply, one_mul]
    exact ⟨1, one_mem _, k, k.2, by simp [hd]⟩
  · intro c hc
    rw [Formalism.UG.Tj, Set.indicator_of_notMem, zero_mul]
    rintro ⟨a, ha, b, hb, e⟩
    refine hc ?_
    have e' : c.out = z * (a * b) := by
      rw [← mul_assoc, hz, scalar_comm', ← hz]
      exact Units.ext (by rw [e, hd]; rfl)
    rw [← QuotientGroup.out_eq' c, e']
    exact QuotientGroup.mk_mul_of_mem _ (mul_mem ha hb)

private theorem scalar_mem {K : Type} [Field K] {n : ℕ} (O : Subring K) (u : Kˣ) (h : (u : K) ∈ O)
    (h' : ((u⁻¹ : Kˣ) : K) ∈ O) : GeneralLinearGroup.scalar (Fin n) u ∈ Formalism.UG.GLint (Fin n) O := by
  have key : ∀ x : Kˣ, (x : K) ∈ O → ∀ i j, (GeneralLinearGroup.scalar (Fin n) x).val i j ∈ O := fun x hx i j => by
    change Matrix.diagonal (fun _ => (x : K)) i j ∈ O
    rw [Matrix.diagonal_apply]
    split_ifs
    · exact hx
    · exact zero_mem _
  refine GlobalTheory.AdelicU.mem_GLint_iff.2 ⟨key u h, ?_⟩
  rw [← map_inv]
  exact key _ h'

theorem UpperTheory.V.Af.Smo.centLoc :
    UpperTheory.V.Af.Smo.CentLoc := by
  intro E _ _ n w B y
  by_cases hB : B.card = n
  swap
  · exact ⟨0, fun W hW => absurd hW.card hB⟩
  let H : Subgroup (w.adicCompletion E)ˣ :=
    { carrier := {y | ∃ c : ℂ, c ≠ 0 ∧ ∀ W : GL (Fin n) (w.adicCompletion E) → ℂ, Eig w B W →
        ∀ g, W (g * GeneralLinearGroup.scalar (Fin n) y) = c * W g}
      one_mem' := ⟨1, one_ne_zero, fun W _ g => by simp⟩
      mul_mem' := by
        rintro a b ⟨c, hc, h⟩ ⟨d, hd, h'⟩
        exact ⟨d * c, mul_ne_zero hd hc, fun W hW g => by rw [map_mul, ← mul_assoc, h' W hW, h W hW, mul_assoc]⟩
      inv_mem' := by
        rintro a ⟨c, hc, h⟩
        refine ⟨c⁻¹, inv_ne_zero hc, fun W hW g => ?_⟩
        have := h W hW (g * GeneralLinearGroup.scalar (Fin n) a⁻¹)
        rw [mul_assoc, ← map_mul, inv_mul_cancel, map_one, mul_one] at this
        rw [this, inv_mul_cancel_left₀ hc] }
  suffices hy : y ∈ H from hy.imp fun _ h => h.2
  obtain ⟨p, hp⟩ : ∃ p, Formalism.UG.IsUnifV E w p := w.valuedAdicCompletion_surjective E _
  have hp0 : p ≠ 0 := fun h0 => by simp [Formalism.UG.IsUnifV, h0] at hp
  have hne : GlobalTheory.LFun.satEig (Formalism.UG.qV E w) n B n ≠ 0 := by
    have hq := Multiset.powersetCard_self (B.map fun b : ℂˣ => (b : ℂ))
    rw [Multiset.card_map, hB] at hq
    simp [GlobalTheory.LFun.satEig, Multiset.esymm, hq]
  have hpH : Units.mk0 p hp0 ∈ H := ⟨_, hne, fun W hW g =>
    (finsum_top (Formalism.UG.Ov E w) (Units.mk0 p hp0) W hW.inv g).symm.trans (hW.eig p hp n le_rfl g)⟩
  have hu : ∀ u : (w.adicCompletion E)ˣ, Valued.v (u : w.adicCompletion E) = 1 → u ∈ H := fun u h =>
    ⟨1, one_ne_zero, fun W hW g => by
      rw [one_mul]
      refine hW.inv g _ (scalar_mem (Formalism.UG.Ov E w) u h.le ?_)
      change Valued.v ((u⁻¹ : (w.adicCompletion E)ˣ) : w.adicCompletion E) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, h, inv_one]⟩
  have hy0 : Valued.v (y : w.adicCompletion E) ≠ 0 := by simp
  have := hu (y * Units.mk0 p hp0 ^ WithZero.log (Valued.v (y : w.adicCompletion E))) (by
    have hp' : Valued.v p = WithZero.exp (-1 : ℤ) := hp
    rw [Units.val_mul, Units.val_zpow_eq_zpow_val, map_mul, map_zpow₀, Units.val_mk0, hp', ← WithZero.exp_zsmul]
    simp only [zsmul_neg, zsmul_one, Int.cast_id]
    rw [WithZero.exp_neg, WithZero.exp_log hy0, mul_inv_cancel₀ hy0])
  exact (H.mul_mem_cancel_right (H.zpow_mem hpH _)).1 this
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ChartCont
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem cc_infGL (F : Type) [Field F] [NumberField F] [IsTotallyReal F] (a : ℕ) :
    Continuous (infGL F a) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf F : Rinf F → Ad F) := (TR.continuous_infEq F).prodMk continuous_const
  exact continuous_const.sub continuous_const |>.add (continuous_id.matrix_map hs)

private theorem cc_unit (E : Type) [Field E] [NumberField E] (n : ℕ) {X : Type} [TopologicalSpace X]
    (u : X → GL (Fin n) (Rinf E)) (hu : Continuous fun x => (u x).val) : Continuous u := by
  refine Units.continuous_iff.2 ⟨hu, ?_⟩
  have e : (fun x => ((u x)⁻¹).val) = fun x => ((u x).val)⁻¹ := funext fun x => Matrix.coe_units_inv _
  rw [e]
  refine continuous_iff_continuousAt.2 fun x => ?_
  have hd : IsUnit ((u x).val).det := (Matrix.isUnit_iff_isUnit_det _).1 (u x).isUnit
  obtain ⟨d, hd⟩ := hd
  refine ContinuousAt.comp (f := fun x => (u x).val) (continuousAt_matrix_inv _ ?_) hu.continuousAt
  rw [← hd]
  exact NormedRing.inverse_continuousAt d

theorem UpperTheory.V.Af.Smo.chartCont :
    UpperTheory.V.Af.Smo.ChartCont := by
  intro E _ _ _ n f hf
  have h1 : ContinuousOn (fun z : GA E n × Lie E n => chart f z.1 z.2) (Set.univ ×ˢ invSet E n) := by
    rw [continuousOn_iff_continuous_restrict]
    let u : ↥((Set.univ : Set (GA E n)) ×ˢ invSet E n) → GL (Fin n) (Rinf E) :=
      fun z => (show IsUnit (Matrix.of z.1.2) from z.2.2).unit
    have hu : Continuous u := cc_unit E n u (continuous_snd.comp continuous_subtype_val)
    have e : ((Set.univ : Set (GA E n)) ×ˢ invSet E n).domRestrict (fun z : GA E n × Lie E n => chart f z.1 z.2) =
        fun z => f (z.1.1 * infGL E n (u z)) := by
      funext z
      have h : IsUnit (Matrix.of z.1.2) := z.2.2
      change chart f z.1.1 z.1.2 = _
      rw [chart, dite_eq_left h]
    rw [e]
    exact hf.comp ((continuous_fst.comp continuous_subtype_val).mul ((cc_infGL E n).comp hu))
  refine ⟨h1, fun g => ?_⟩
  classical
  have h2 : ContinuousOn (chart f g) (invSet E n) :=
    h1.comp (f := fun x => (g, x)) (continuous_const.prodMk continuous_id).continuousOn
      fun x hx => ⟨Set.mem_univ _, hx⟩
  have h3 := h2.measurable_piecewise (g := fun _ => (0 : ℂ)) continuousOn_const TR.isOpen_invSet.measurableSet
  convert h3 using 1
  funext x
  by_cases hx : x ∈ invSet E n
  · rw [Set.piecewise_eq_of_mem _ _ _ hx]
  · rw [Set.piecewise_eq_of_notMem _ _ _ hx, chart, dite_eq_right (show ¬ IsUnit (Matrix.of x) from hx)]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ChartSmul
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem isY_map {R R' : Type} [CommRing R] [CommRing R'] {n m : ℕ} (f : R →+* R') (p : GL (Fin n) R)
    (hp : IsY m p.val) : IsY m (GeneralLinearGroup.map f p).val := by
  intro i hi
  obtain ⟨h1, h2⟩ := hp i hi
  refine ⟨?_, fun j hj => ?_⟩
  · change f (p.val i i) = 1
    rw [h1, map_one]
  · change f (p.val i j) = 0
    rw [h2 j hj, map_zero]

private theorem chart_smul {E : Type} [Field E] [NumberField E] [IsTotallyReal E] {n : ℕ} (f f' : GA E n → ℂ)
    (g g' : GA E n) (a : ℂ) (h : ∀ y, f (g * infGL E n y) = a * f' (g' * infGL E n y)) (x : Lie E n) :
    chart f g x = a * chart f' g' x := by
  unfold chart
  split_ifs with hx
  · exact h _
  · simp

theorem UpperTheory.V.Af.Smo.killP :
    UpperTheory.V.Af.Smo.ArchKir → UpperTheory.V.Af.Smo.FinKir → UpperTheory.V.Af.Smo.EmbY → UpperTheory.V.Af.Smo.PsiInf → UpperTheory.V.Af.Smo.ChartCont → UpperTheory.V.Af.Smo.KillP := by
  intro hA hF hE hP hC E _ _ _ n hn S U
  obtain ⟨c, Hf, hf1, hc, hf⟩ := hF E n hn S U
  obtain ⟨Hi, hi1, hi⟩ := hA E n (n - 1) (by omega)
  refine ⟨c, fun p => Hi (GeneralLinearGroup.map (pInf E) p) * Hf (GeneralLinearGroup.map (pFin E) p),
    by simp [hi1, hf1], hc, fun α => ?_⟩
  obtain ⟨β, hβ⟩ := hi α
  refine ⟨β, fun W hW hb hWh hU p hp => ?_⟩
  obtain ⟨C, hb⟩ := hb
  have hpi := isY_map (pInf E) p hp.1
  have hpf := isY_map (pFin E) p hp.1
  have hS := hp.2
  beta_reduce
  have e : p = finGL E n (GeneralLinearGroup.map (pFin E) p) * infGL E n (GeneralLinearGroup.map (pInf E) p) := by
    rw [← TR.infGL_comm, TR.infGL_mul_finGL]
  generalize GeneralLinearGroup.map (pInf E) p = a at *
  generalize GeneralLinearGroup.map (pFin E) p = b at *
  have h1 : ∀ x, chart (fop c W) (finGL E n b) x = Hf b * chart W 1 x := by
    refine chart_smul _ _ _ _ _ fun y => ?_
    have := hf (fun k => W (finGL E n k * infGL E n y)) (fun ν _ hν g _ => ?_) (fun g _ u hu _ => ?_) b hS hpf
    · simp only [map_one] at this
      rw [← this]
      unfold fop comb
      refine Finsupp.sum_congr fun x _ => ?_
      beta_reduce
      rw [map_mul, mul_assoc, mul_assoc, TR.infGL_comm]
    · obtain ⟨k1, k2⟩ := (hE E n 0).2.1 ν hν
      rw [map_mul, mul_assoc, hWh _ k1, k2]
      rfl
    · rw [map_mul, mul_assoc, ← TR.infGL_comm, ← mul_assoc, hU _ u hu]
  have h2 := hβ (chart W 1) ((hC E n W hW).2 1) ⟨max C 0, fun x => ?_⟩ (fun ν hν x => ?_) a hpi
  · unfold conv
    rw [e, TR.chart_mul]
    simp only [Function.comp_apply, h1, mul_assoc]
    rw [integral_const_mul, h2]
    ring
  · unfold chart
    split_ifs
    · exact (hb _).trans (le_max_left _ _)
    · simp
  · obtain ⟨k1, k2⟩ := (hE E n 0).2.2.1 ν hν
    have := congrFun (TR.chart_mul W 1 ν) x
    rw [Function.comp_apply] at this
    rw [← this]
    refine chart_smul _ _ _ _ _ (fun y => ?_) x
    rw [one_mul, one_mul, hWh _ k1, k2, hP]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.ColConj
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

private theorem inv_row {R : Type} [CommRing R] {n : ℕ} (m : ℕ) (k : Fin n) (hk : k.val = m + 1) (p : GL (Fin n) R)
    (hp : IsY (m + 1) p.val) : (∀ j, j < k → (p⁻¹).val k j = 0) ∧ (p⁻¹).val k k = 1 := by
  have h1 : ∀ j, j < k → (p⁻¹).val k j = 0 := by
    have hb : p.val.BlockTriangular (fun i : Fin n => if i.val ≤ m then 0 else i.val) := by
      intro i j hij
      dsimp only at hij
      have hi : m + 1 ≤ i.val := by split_ifs at hij <;> omega
      refine (hp i hi).2 j ?_
      rw [Fin.lt_def]
      split_ifs at hij <;> omega
    haveI : Invertible p.val := p.invertible
    have hq := Matrix.blockTriangular_inv_of_blockTriangular hb
    intro j hj
    rw [Matrix.coe_units_inv]
    refine hq ?_
    rw [Fin.lt_def] at hj
    dsimp only
    split_ifs <;> omega
  refine ⟨h1, ?_⟩
  have h2 : ((p⁻¹).val * p.val) k k = 1 := by rw [Units.inv_mul, Matrix.one_apply_eq]
  rw [Matrix.mul_apply, Finset.sum_eq_single k, (hp k hk.ge).1, mul_one] at h2
  · exact h2
  · intro j _ hj
    rcases lt_or_gt_of_ne hj with h | h
    · rw [h1 j h, zero_mul]
    · rw [(hp j (by rw [Fin.lt_def] at h; omega)).2 k h, mul_zero]
  · simp

theorem UpperTheory.V.Af.Smo.colConj :
    UpperTheory.V.Af.Smo.ColConj := by
  intro R _ n m hm p hp u
  set k : Fin n := ⟨m.val + 1, hm⟩ with hkdef
  have hk : k.val = m.val + 1 := rfl
  obtain ⟨hb0, hb1⟩ := inv_row m.val k hk p hp
  set c : Fin n → R := fun i => if i ≤ m then u i else 0 with hc
  set a : Fin n → R := p.val *ᵥ c with ha
  set b : Fin n → R := (p⁻¹).val k with hb
  have ha0 : ∀ i, m < i → a i = 0 := by
    intro i hi
    change ∑ j, p.val i j * c j = 0
    refine Finset.sum_eq_zero fun j _ => ?_
    by_cases hj : j ≤ m
    · rw [(hp i hi).2 j (lt_of_le_of_lt hj hi), zero_mul]
    · simp [hc, hj]
  have hab : ∀ i j, j ≤ i → a i * b j = 0 := by
    intro i j hij
    by_cases hi : m < i
    · rw [ha0 i hi, zero_mul]
    · rw [hb0 j (by rw [Fin.lt_def] at hi ⊢; rw [Fin.le_def] at hij; omega), mul_zero]
  have hdot : b ⬝ᵥ a = 0 := Finset.sum_eq_zero fun i _ => by rw [mul_comm]; exact hab i i le_rfl
  have hsq : vecMulVec a b * vecMulVec a b = 0 := by
    rw [vecMulVec_mul_vecMulVec, hdot, zero_smul, vecMulVec_zero]
  refine ⟨⟨1 + vecMulVec a b, 1 - vecMulVec a b, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [add_mul, mul_sub, mul_sub, hsq]; simp
  · rw [sub_mul, mul_add, mul_add, hsq]; simp
  · intro i _
    refine ⟨?_, fun j hj => ?_⟩
    · simp [vecMulVec_apply, hab i i le_rfl]
    · simp [vecMulVec_apply, hab i j hj.le, Matrix.one_apply_ne hj.ne']
  · have : dotLe m (p.val m) u = a m := by
      refine Finset.sum_congr rfl fun j _ => ?_
      simp [hc]
    rw [this]
    unfold supN
    rw [Finset.sum_eq_single m, Finset.sum_eq_single k]
    · have : m ≠ k := fun h => by have := congrArg Fin.val h; omega
      simp [hk, vecMulVec_apply, hb1, Matrix.one_apply_ne this]
    · intro j _ hj
      rw [if_neg fun h => hj (Fin.ext (by omega))]
    · simp
    · intro i _ hi
      refine Finset.sum_eq_zero fun j _ => ?_
      split_ifs with h
      · have hne : i ≠ j := fun e => by have := congrArg Fin.val e; omega
        have : a i * b j = 0 := by
          rcases lt_or_gt_of_ne hi with h' | h'
          · rw [hb0 j (by rw [Fin.lt_def] at h' ⊢; omega), mul_zero]
          · rw [ha0 i h', zero_mul]
        simp [vecMulVec_apply, this, Matrix.one_apply_ne hne]
      · rfl
    · simp
  · have h1 : colM m u = 1 + vecMulVec c (Pi.single k 1) := by
      unfold colM
      congr 1
      ext i j
      by_cases hj : j = k
      · subst hj
        simp [vecMulVec_apply, hc, hk]
      · have : j.val ≠ m.val + 1 := fun h => hj (Fin.ext h)
        simp [vecMulVec_apply, hj, this]
    have h2 : b ᵥ* p.val = Pi.single k 1 := by
      ext j
      have : ((p⁻¹).val * p.val) k j = (1 : Matrix (Fin n) (Fin n) R) k j := by rw [Units.inv_mul]
      rw [Matrix.one_apply] at this
      rw [Pi.single_apply, ← if_congr eq_comm rfl rfl, ← this]
      rfl
    change p.val * colM m u = (1 + vecMulVec a b) * p.val
    rw [h1, mul_add, add_mul, mul_one, one_mul, mul_vecMulVec, vecMulVec_mul, h2]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.SmoothRepresentationsGL.EigOfSat
section
open NumberField IsDedekindDomain MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.FourierWhittaker (whittaker)
open GlobalTheory.CuspRep (GA Af Ad ratGL finGL locGL pFin pLoc sFin sLoc)
open UpperTheory.V UpperTheory.V.Af.Smo
open UpperTheory.V.TR (Rinf Lie chart infGL pInf sInf toL lmul oneL invSet CuspSub)
open scoped SchwartzMap FourierTransform RealInnerProductSpace ContDiff Topology

theorem UpperTheory.V.Af.Smo.eigOfSat :
    UpperTheory.V.Af.Smo.EigOfSat := by
  intro E _ _ _ n π w B hB φ hφ hK g
  refine ⟨hB.card, fun y k hk => ?_, fun ϖ hϖ j hj y => ?_⟩
  · rw [map_mul, map_mul, ← mul_assoc, hK _ k hk]
  · by_cases h0 : φ = 0
    · subst h0
      simp
    have he := (hB.2 (⟨φ, hφ⟩ : π.V)
      (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (Subtype.ext (funext fun x => hK x k hk))) fun h => h0 (congrArg Subtype.val h)).2.2.2 ϖ hϖ j hj
    let ev : π.V →+ ℂ :=
      { toFun := fun ψ => ψ.1.1 (g * finGL E n (locGL E n w y))
        map_zero' := rfl
        map_add' := fun _ _ => rfl }
    have hs := ev.map_finsum (GlobalTheory.LFun.finite_heckeVec (Formalism.UG.Final.GLintComm E w n)
      (GlobalTheory.LFun.Tj_mem_hecke hϖ j) (π.locRep w) ⟨φ, hφ⟩)
    refine Eq.trans (finsum_congr fun c => ?_) (hs.symm.trans (congrArg ev he))
    rw [map_mul, map_mul, ← mul_assoc]
    rfl
end

