module

public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0023
public import Mathlib
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0006
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0016
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0017
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0020
public import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.Bundle0011
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0001
public import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ExistsUnitFormLocalizationEtaleNbhd
public import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.Bundle0002
public import Development.WeilBound.CoreStatements.HodgeTatePoints.Bundle0005
public import Development.WeilBound.CoreStatements.HodgeTatePoints.TwhopfSec

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.CcBase
section
noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.CompanionTheory.Ar.Crv GlobalTheory.CompanionTheory.Ar.Conj

namespace PositivityTheory.HtPt.Cc

variable {R : Type} [CommRing R] {d : ℕ}

def Z {n : ℕ} (a : Pt R n d) : Prop := ∀ i, constantCoeff (a i) = 0

def ZZ {m n : ℕ} (b : Fin m → Pt R n d) : Prop := ∀ j i, constantCoeff (b j i) = 0

def evP {m n : ℕ} (b : Fin m → Pt R n d) (a : Pt R m d) : Pt R n d := fun i => ev b (a i)

def evV {l m n : ℕ} (b : Fin m → Pt R n d) (a : Fin l → Pt R m d) : Fin l → Pt R n d := fun j => evP b (a j)

theorem ZZ_nil {n : ℕ} : ZZ (![] : Fin 0 → Pt R n d) := fun j => j.elim0

theorem ZZ_cons {m n : ℕ} {p : Pt R n d} {u : Fin m → Pt R n d} (hp : Z p) (hu : ZZ u) :
    ZZ (Matrix.vecCons p u) := fun j => Fin.cases hp (fun j => hu j) j

theorem Z_pt {n : ℕ} (j : Fin n) : Z (pt R d j) := fun i => by simp [pt]

theorem Z_zero {n : ℕ} : Z (0 : Pt R n d) := fun i => by simp

theorem cc_ev {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) {f : PS R m d}
    (hf : constantCoeff f = 0) : constantCoeff (ev b f) = 0 :=
  constantCoeff_subst_eq_zero (a := fun p : Fin m × Fin d => b p.1 p.2) (hasSubst_ev b hb)
    (fun p => hb p.1 p.2) hf

theorem Z_comp1 {n : ℕ} {φ : Pt R 1 d} {a : Pt R n d} (hφ : Z φ) (ha : Z a) : Z (comp1 φ a) :=
  fun i => cc_ev (ZZ_cons ha ZZ_nil) (hφ i)

theorem Z_add {n : ℕ} (G : FGLaw R d) {a b : Pt R n d} (ha : Z a) (hb : Z b) : Z (addOf G.F a b) :=
  fun i => cc_ev (ZZ_cons ha (ZZ_cons hb ZZ_nil)) (G.const i)

theorem Z_act {O : Type} [CommRing O] {G : FGLaw R d} (A : OAct O G) (a : O) : Z (A.act a) := A.const a

theorem ev_ev {l m n : ℕ} {b : Fin m → Pt R n d} {a : Fin l → Pt R m d} (hb : ZZ b) (ha : ZZ a)
    (f : PS R l d) : ev b (ev a f) = ev (evV b a) f :=
  subst_comp_subst_apply (hasSubst_ev a ha) (hasSubst_ev b hb) f

theorem evV_cons {l m n : ℕ} (b : Fin m → Pt R n d) (p : Pt R m d) (u : Fin l → Pt R m d) :
    evV b (Matrix.vecCons p u) = Matrix.vecCons (evP b p) (evV b u) :=
  funext fun j => Fin.cases rfl (fun _ => rfl) j

theorem evV_nil {m n : ℕ} (b : Fin m → Pt R n d) : evV b (![] : Fin 0 → Pt R m d) = ![] :=
  funext fun j => j.elim0

theorem evalPoints_coordinatePoint {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (j : Fin m) : evP b (pt R d j) = b j :=
  funext fun i => ev_X b hb j i

theorem ev_mul' {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (f g : PS R m d) :
    ev b (f * g) = ev b f * ev b g := ev_mul b hb f g

theorem ev_zero' {m n : ℕ} (b : Fin m → Pt R n d) : ev b (0 : PS R m d) = 0 := by
  simpa using ev_C b (0 : R)

theorem evalPoints_zero {m n : ℕ} (b : Fin m → Pt R n d) : evP b (0 : Pt R m d) = 0 :=
  funext fun _ => ev_zero' b

theorem evalPoints_comp {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (φ : Pt R 1 d) {a : Pt R m d} (ha : Z a) :
    evP b (comp1 φ a) = comp1 φ (evP b a) := by
  funext i
  change ev b (ev ![a] (φ i)) = ev ![evP b a] (φ i)
  rw [ev_ev hb (ZZ_cons ha ZZ_nil), evV_cons, evV_nil]

theorem evalPoints_add {m n : ℕ} {b : Fin m → Pt R n d} (hb : ZZ b) (F : Fin d → PS R 2 d) {x y : Pt R m d}
    (hx : Z x) (hy : Z y) : evP b (addOf F x y) = addOf F (evP b x) (evP b y) := by
  funext i
  change ev b (ev ![x, y] (F i)) = ev ![evP b x, evP b y] (F i)
  rw [ev_ev hb (ZZ_cons hx (ZZ_cons hy ZZ_nil)), evV_cons, evV_cons, evV_nil]

theorem comp1_eq_evalPoint {n : ℕ} (φ : Pt R 1 d) (x : Pt R n d) : comp1 φ x = evP ![x] φ := rfl

theorem germComp1_germComp1_eq_substitute {n : ℕ} (φ : Pt R 1 d) {ψ : Pt R 1 d} (hψ : Z ψ) {x : Pt R n d} (hx : Z x) :
    comp1 (comp1 φ ψ) x = comp1 φ (comp1 ψ x) :=
  evalPoints_comp (ZZ_cons hx ZZ_nil) φ hψ

theorem eval_identity_two (f : PS R 2 d) : ev (n := 2) ![pt R d 0, pt R d 1] f = f :=
  ev_pt_self _ (fun j => by fin_cases j <;> rfl) f

section Laws

variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O) {n : ℕ}

theorem act_zero_at (x : Pt R n d) : comp1 (B.A.act ((0 : ℕ) : O)) x = 0 := by
  have ha : B.A.act 0 = 0 := by
    have hc := B.A.const 0
    have h1 : B.A.act 0 = B.G.add (B.A.act 0) (B.A.act 0) := by rw [← B.A.add_act, add_zero]
    have h2 : B.A.act 0 = comp1 (B.A.act 0) (B.A.act 0) := by rw [← B.A.mul_act, mul_zero]
    have h3 : ReciprocityTheory.ChartRestriction.G.TB.dLin (B.A.act 0) = 0 := by
      have := GlobalTheory.FormalMulN.dLin_add B.G hc hc
      rw [← h1] at this
      exact left_eq_add.mp this
    have h4 : ∀ i, 2 ≤ (B.A.act 0 i).order := fun i =>
      GlobalTheory.FormalSeries.two_le_order_iff.mpr ⟨hc i, fun j => by
        obtain ⟨j0, j⟩ := j
        obtain rfl : j0 = 0 := Subsingleton.elim _ _
        exact congrFun (congrFun h3 i) j⟩
    have h5 : ∀ (k : ℕ) i, (k : ℕ∞) ≤ (B.A.act 0 i).order := by
      intro k
      induction k with
      | zero => simp
      | succ k ih =>
        intro i
        have := GlobalTheory.FormalSeries.le_order_subst_sub_subst
          (a := fun p : Fin 1 × Fin d => (![B.A.act 0] : Fin 1 → Pt R 1 d) p.1 p.2) (b := 0) (k := k)
          (fun p => GlobalTheory.GaugeAdjoint.const_one hc p.1 p.2) (by simp)
          (fun p => by simpa using ih p.2) (h4 i)
        rw [subst_zero_of_constantCoeff_zero (hc i), sub_zero] at this
        rw [congrFun h2 i]
        exact this
    funext i
    exact GlobalTheory.FormalSeries.eq_of_forall_le_order_sub fun k => by simpa using h5 k i
  rw [Nat.cast_zero, ha, comp1_eq_evalPoint]
  exact evalPoints_zero _

theorem act_succ_at (k : ℕ) {x : Pt R n d} (hx : Z x) :
    comp1 (B.A.act ((k + 1 : ℕ) : O)) x = addOf B.G.F (comp1 (B.A.act (k : O)) x) x := by
  rw [Nat.cast_succ, B.A.add_act, B.A.one_act, comp1_eq_evalPoint, comp1_eq_evalPoint,
    evalPoints_add (ZZ_cons hx ZZ_nil) _ (Z_act _ _) (Z_pt _), evalPoints_coordinatePoint (ZZ_cons hx ZZ_nil)]
  rfl

theorem first_power_succ_at (k : ℕ) {x z : Pt R n d} (hx : Z x) (hz : Z z) :
    ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k) * ev ![comp1 (B.A.act (k : O)) x, x, z] B.ph1 := by
  have h : ev ![x, z] (pow1 B (k + 1)) = ev ![x, z] (pow1 B k *
      ev (n := 2) ![comp1 (B.A.act (k : O)) (pt R d 0), pt R d 0, pt R d 1] B.ph1) := by
    rw [pow1, Finset.prod_range_succ, pow1]
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem second_power_succ_at (k : ℕ) {x z : Pt R n d} (hx : Z x) (hz : Z z) :
    ev ![x, z] (pow2 B (k + 1)) = ev ![x, z] (pow2 B k) * ev ![x, comp1 (B.A.act (k : O)) z, z] B.ph2 := by
  have h : ev ![x, z] (pow2 B (k + 1)) = ev ![x, z] (pow2 B k *
      ev (n := 2) ![pt R d 0, comp1 (B.A.act (k : O)) (pt R d 1), pt R d 1] B.ph2) := by
    rw [pow2, Finset.prod_range_succ, pow2]
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem first_power_zero : pow1 B 0 = 1 := by simp [pow1]

theorem second_power_zero : pow2 B 0 = 1 := by simp [pow2]

theorem sy_law_at {x z w : Pt R n d} (hx : Z x) (hz : Z z) (hw : Z w) :
    ev ![x, z, w] B.ph2 * ev ![x, z] B.sy * ev ![x, w] B.sy =
      ev ![x, addOf B.G.F z w] B.sy * ev ![z, w, x] B.ph1 := by
  have h := congrArg (ev ![x, z, w]) B.sy_law
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem symmetric_zero_right_at {x : Pt R n d} (hx : Z x) : ev ![x, 0] B.sy = 1 := by
  have h := congrArg (ev ![x]) B.symmetry_zero_snd
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem second_form_zero_left_at {x z : Pt R n d} (hx : Z x) (hz : Z z) : ev ![0, x, z] B.ph2 = 1 := by
  have h := congrArg (ev ![x, z]) B.cocycleRight_zero_fst
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem first_form_zero_right_at {x z : Pt R n d} (hx : Z x) (hz : Z z) : ev ![x, z, 0] B.ph1 = 1 := by
  have h := congrArg (ev ![x, z]) B.cocycleLeft_zero_thd
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

theorem interchange_at {x y z w : Pt R n d} (hx : Z x) (hy : Z y) (hz : Z z) (hw : Z w) :
    ev ![x, y, z] B.ph1 * ev ![x, y, w] B.ph1 * ev ![addOf B.G.F x y, z, w] B.ph2 =
      ev ![x, z, w] B.ph2 * ev ![y, z, w] B.ph2 * ev ![x, y, addOf B.G.F z w] B.ph1 := by
  have h := congrArg (ev ![x, y, z, w]) B.interchange
  simp (discharger := (repeat first | assumption | exact ZZ_nil | apply ZZ_cons | exact Z_pt _ | exact Z_zero | exact Z_comp1 (Z_act _ _) (Z_pt _) | exact Z_add _ (Z_pt _) (Z_pt _))) only
    [ev_mul', ev_ev, evV_cons, evV_nil, evalPoints_coordinatePoint,
     evalPoints_zero, evalPoints_comp, evalPoints_add, ev_one] at h
  exact h

end Laws

end PositivityTheory.HtPt.Cc
end
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.DegLeOfEquiv
section
open GlobalTheory.CompanionTheory.Ar.Crv

namespace PositivityTheory.HtPt.Ch

section SlopeTestRemainingChoices

variable {K : Type} [Field K] {C : ACurve K} {V : Type} [AddCommGroup V] [Module K V]

theorem basis_mem {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) (q : Fin n) : b q ∈ L := by
  refine (h _).2 fun r => ?_
  by_cases e : q = r <;> simp [e, Finsupp.single_apply]

theorem smul_mem_lat {i : C.I} {n : ℕ} {b : Module.Basis (Fin n) K V} {L : AddSubgroup V}
    (h : IsLatOf C i b L) {a : K} (ha : C.v i a ≤ 1) {x : V} (hx : x ∈ L) : a • x ∈ L := by
  refine (h _).2 fun r => ?_
  rw [map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  exact mul_le_one' ha ((h _).1 hx r)

theorem v_det_le {i : C.I} {n : ℕ} {b b' : Module.Basis (Fin n) K V} {L L' : AddSubgroup V}
    (h : IsLatOf C i b L) (h' : IsLatOf C i b' L') (hle : L ≤ L') : C.v i (b'.det b) ≤ 1 := by
  rw [Module.Basis.det_apply, Matrix.det_apply']
  refine (C.v i).map_sum_le fun σ _ => ?_
  rw [map_mul, map_prod]
  refine mul_le_one' ?_ (Finset.prod_le_one' fun q _ => (h' _).1 (hle (basis_mem h q)) _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with e | e <;> simp [e]

theorem deg_triv [FiniteDimensional K V] {n : ℕ} (b : Module.Basis (Fin n) K V)
    {L : C.I → AddSubgroup V} (h : ∀ i, IsLatOf C i b (L i)) : IsBun C L ∧ deg C L = 0 := by
  have hb : IsBun C L := Inhab.isBun_of_basis C b L h
  refine ⟨hb, ?_⟩
  rw [(_root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V L n b (fun _ => b) hb h).2]
  simp [Module.Basis.det_self]

end SlopeTestRemainingChoices

theorem deg_mono : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (L L' : C.I → AddSubgroup V), IsBun C L → IsBun C L' → (∀ i, L i ≤ L' i) → deg C L ≤ deg C L' := by
  intro K _ C V _ _ _ L L' hL hL' hle
  choose b hb using hL.1
  choose b' hb' using hL'.1
  obtain ⟨hf, e⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V L _ (Module.finBasis K V) b hL hb
  obtain ⟨hf', e'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegFormula.deg_formula K C V L' _ (Module.finBasis K V) b' hL' hb'
  rw [e, e']
  refine finsum_le_finsum' (hf.subset fun i hi h1 => hi (by simp [h1]))
    (hf'.subset fun i hi h1 => hi (by simp [h1])) fun i => ?_
  refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg _)
  have n1 : C.v i ((Module.finBasis K V).det (b i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b i)).ne_zero
  have n2 : C.v i ((Module.finBasis K V).det (b' i)) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 ((Module.finBasis K V).isUnit_det (b' i)).ne_zero
  rw [WithZero.log_le_log n1 n2, ← Module.Basis.det_mul_det _ (b' i) (b i), map_mul]
  exact mul_le_of_le_one_right' (v_det_le (hb i) (hb' i) (hle i))

theorem deg_le_of_equiv {K : Type} [Field K] {C : ACurve K} {V V' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} (e : V ≃ₗ[K] V') (hL : IsBun C L)
    (hL' : IsBun C L') (h : ∀ i, ∀ x ∈ L i, e x ∈ L' i) : deg C L ≤ deg C L' := by
  obtain ⟨hM, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegEquiv.deg_equiv K C V V' L
    (fun i => (L i).comap e.symm.toLinearMap.toAddMonoidHom) e hL (fun i x => by simp)
  rw [← hd]
  refine deg_mono K C V' _ _ hM hL' fun i y hy => ?_
  simpa using h i (e.symm y) hy

theorem deg_inj : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (f : V →ₗ[K] V') (W : Submodule K V), IsBun C L → IsBun C L' → Function.Injective f → IsHom C L L' f → subDeg C L W ≤ subDeg C L' (W.map f) := by
  intro K _ C V _ _ _ V' _ _ _ L L' f W hL hL' hf hh
  exact deg_le_of_equiv (Submodule.equivMapOfInjective f hf W) (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V L W hL).1
    (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V' L' _ hL').1 fun i x hx => hh i x hx

theorem subdeg_trivial : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (n : ℕ) (b : Module.Basis (Fin n) K V) (L : C.I → AddSubgroup V) (W : Submodule K V), (∀ i, IsLatOf C i b (L i)) → subDeg C L W ≤ 0 := by
  intro K _ C V _ _ _ n b L W h
  obtain ⟨hL, h0⟩ := deg_triv b h
  have hs := _root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot K C V L W hL
  obtain ⟨κ, a, ha, hsp, hli⟩ := exists_linearIndependent' K (fun q => W.mkQ (b q))
  have : Finite κ := Finite.of_injective a ha
  have : Fintype κ := Fintype.ofFinite κ
  have htop : ⊤ ≤ Submodule.span K (Set.range ((fun q => W.mkQ (b q)) ∘ a)) := by
    rw [hsp, show (Set.range fun q => W.mkQ (b q)) = W.mkQ '' Set.range b from
      Set.range_comp _ _, Submodule.span_image, b.span_eq, Submodule.map_top, Submodule.range_mkQ]
  let c := (Module.Basis.mk hli htop).reindex (Fintype.equivFin κ)
  have hc : ∀ q, c q = W.mkQ (b (a ((Fintype.equivFin κ).symm q))) := fun q => by simp [c]
  obtain ⟨hM, hM0⟩ := deg_triv (C := C) c (fun i => Inhab.isLatOf_latOf C i c)
  have := deg_mono K C _ _ _ hM (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V L W hL).2 fun i y hy => by
    rw [← c.sum_repr y]
    refine sum_mem fun q _ => ⟨c.repr y q • b (a ((Fintype.equivFin κ).symm q)),
      smul_mem_lat (h i) (hy q) (basis_mem (h i) _), ?_⟩
    rw [hc]; simp
  omega

theorem ses_restrict {K : Type} [Field K] {C : ACurve K} {V V' V'' : Type} [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [AddCommGroup V'] [Module K V'] [FiniteDimensional K V']
    [AddCommGroup V''] [Module K V''] [FiniteDimensional K V'']
    {L : C.I → AddSubgroup V} {L' : C.I → AddSubgroup V'} {L'' : C.I → AddSubgroup V''}
    {f : V →ₗ[K] V'} {g : V' →ₗ[K] V''} (hL' : IsBun C L') (h : ShortExact C L L' L'' f g)
    (A : Submodule K V) (X : Submodule K V') (B : Submodule K V'')
    (hA : ∀ x, x ∈ A ↔ f x ∈ X) (hB : ∀ z, z ∈ B ↔ ∃ y ∈ X, g y = z) :
    ∃ I : C.I → AddSubgroup B, IsBun C I ∧ subDeg C L' X = subDeg C L A + deg C I ∧
      ∀ i z, z ∈ I i ↔ ∃ y ∈ L' i, y ∈ X ∧ g y = z := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  let f' : A →ₗ[K] X := f.restrict fun x hx => (hA x).1 hx
  let g' : X →ₗ[K] B := g.restrict fun y hy => (hB _).2 ⟨y, hy, rfl⟩
  have hse : ShortExact C (sub C L A) (sub C L' X)
      (fun i => (sub C L' X i).map g'.toAddMonoidHom) f' g' := by
    refine ⟨fun x y e => Subtype.ext (h1 (congrArg Subtype.val e)), fun y => ⟨fun hy => ?_, ?_⟩,
      fun z => ?_, fun i x => h4 i x, fun i z => Iff.rfl⟩
    · obtain ⟨x, hx⟩ := (h2 y).1 (congrArg Subtype.val hy)
      exact ⟨⟨x, (hA x).2 (hx ▸ y.2)⟩, Subtype.ext hx⟩
    · rintro ⟨x, rfl⟩
      exact Subtype.ext (h2.apply_apply_eq_zero x)
    · obtain ⟨y, hy, e⟩ := (hB z).1 z.2
      exact ⟨⟨y, hy⟩, Subtype.ext e⟩
  obtain ⟨-, hI, hd⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact K C _ _ _ _ _ _ f' g' (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V' L' X hL').1 hse
  refine ⟨_, hI, hd, fun i z => ⟨?_, ?_⟩⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, y.2, rfl⟩
  · rintro ⟨y, hy, hX, e⟩
    exact ⟨⟨y, hX⟩, hy, Subtype.ext e⟩

theorem subdeg_ses : ∀ (K : Type) [Field K] (C : ACurve K) (V : Type) [AddCommGroup V] [Module K V] [FiniteDimensional K V] (V' : Type) [AddCommGroup V'] [Module K V'] [FiniteDimensional K V'] (V'' : Type) [AddCommGroup V''] [Module K V''] [FiniteDimensional K V''] (L : C.I → AddSubgroup V) (L' : C.I → AddSubgroup V') (L'' : C.I → AddSubgroup V'') (f : V →ₗ[K] V') (g : V' →ₗ[K] V'') (X : Submodule K V'), IsBun C L' → ShortExact C L L' L'' f g → subDeg C L' X ≤ subDeg C L (X.comap f) + subDeg C L'' (X.map g) := by
  intro K _ C V _ _ _ V' _ _ _ V'' _ _ _ L L' L'' f g X hL' h
  obtain ⟨I, hI, hd, hm⟩ := ses_restrict hL' h (X.comap f) X (X.map g) (fun _ => Iff.rfl)
    (fun _ => Iff.rfl)
  have hL'' := (_root_.GlobalTheory.CompanionTheory.Ar.Crv.deg_shortExact K C _ _ _ _ _ _ f g hL' h).2.1
  have : deg C I ≤ subDeg C L'' (X.map g) :=
    deg_mono K C _ _ _ hI (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C V'' L'' _ hL'').1 fun i z hz => by
      obtain ⟨y, hy, -, e⟩ := (hm i z).1 hz
      exact (h.2.2.2.2 i z).2 ⟨y, hy, e⟩
  omega

theorem exists_dot {K : Type} [Field K] {d : ℕ} (ψ : Module.Dual K (Fin d → K)) :
    ∃ u : Fin d → K, ∀ x, u ⬝ᵥ x = ψ x := by
  refine ⟨fun j => ψ (Pi.single j 1), fun x => ?_⟩
  set_option synthInstance.maxHeartbeats 100000 in
    conv_rhs => rw [pi_eq_sum_univ' x, map_sum]
  simp [dotProduct, mul_comm]

theorem subdeg_orth : ∀ (K : Type) [Field K] (C : ACurve K) (d : ℕ) (L : C.I → AddSubgroup (Fin d → K)) (W X : Submodule K (Fin d → K)), IsBun C L → (∀ u, u ∈ W ↔ ∀ φ ∈ X, u ⬝ᵥ φ = 0) → subDeg C (dotDual C L) X = deg C (dotDual C L) + subDeg C L W := by
  intro K _ C d L W X hL hW
  have hbij : Function.Bijective (dotProductBilin K K : (Fin d → K) →ₗ[K] (Fin d → K) →ₗ[K] K) := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun u hu => funext fun j => ?_, fun ψ => ?_⟩
    · simpa using LinearMap.congr_fun hu (Pi.single j 1)
    · obtain ⟨u, hu⟩ := exists_dot ψ
      exact ⟨u, LinearMap.ext hu⟩
  obtain ⟨hD, -, hbi⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual K C _ _ L _ hL hbij
  let B₀ : (Fin d → K) →ₗ[K] W →ₗ[K] K := ((dotProductBilin K K).comp W.subtype).flip
  have hB₀ : ∀ φ (w : W), B₀ φ w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  let B : ((Fin d → K) ⧸ X) →ₗ[K] W →ₗ[K] K :=
    X.liftQ B₀ fun φ hφ => LinearMap.ext fun w => (hW w).1 w.2 φ hφ
  have hB : ∀ φ (w : W), B (X.mkQ φ) w = (w : Fin d → K) ⬝ᵥ φ := fun _ _ => rfl
  have hBb : Function.Bijective B := by
    refine ⟨(injective_iff_map_eq_zero _).2 fun y hy => ?_, fun ψ => ?_⟩
    · obtain ⟨φ, rfl⟩ := X.mkQ_surjective y
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
        ← Subspace.forall_mem_dualAnnihilator_apply_eq_zero_iff]
      intro ψ hψ
      obtain ⟨u, hu⟩ := exists_dot ψ
      have hu' : u ∈ W := (hW u).2 fun x hx => by
        rw [hu]; exact (Submodule.mem_dualAnnihilator ψ).1 hψ x hx
      rw [← hu, ← hB φ ⟨u, hu'⟩, hy]; rfl
    · obtain ⟨ψ', rfl⟩ := LinearMap.dualMap_surjective_of_injective W.injective_subtype ψ
      obtain ⟨u, hu⟩ := exists_dot ψ'
      refine ⟨X.mkQ u, LinearMap.ext fun w => ?_⟩
      rw [hB, dotProduct_comm, hu]; rfl
  obtain ⟨-, hq, -⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Crv.DegDual.deg_dual K C _ _ _ B (_root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuot.isBun_sub_quot K C _ _ X hD).2 hBb
  have he : dualLat C (quot C (dualLat C L (dotProductBilin K K)) X) B = sub C L W := by
    funext i; ext w
    have : (w : Fin d → K) ∈ L i ↔ (w : Fin d → K) ∈
        dualLat C (dualLat C L (dotProductBilin K K)) (dotProductBilin K K).flip i := by rw [hbi]
    refine Iff.trans ?_ this.symm
    constructor
    · intro H φ hφ
      exact H _ ⟨φ, hφ, rfl⟩
    · rintro H _ ⟨φ, hφ, rfl⟩
      exact H φ hφ
  have hs := _root_.GlobalTheory.CompanionTheory.Ar.Crv.SubQuotDeg.deg_eq_subDeg_add_deg_quot K C _ _ X hD
  rw [he] at hq
  unfold dotDual
  unfold subDeg at hs ⊢
  omega

end PositivityTheory.HtPt.Ch
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.GcDescend
section
open Module NumberField GlobalTheory.CompanionTheory.Ar.HT TensorProduct

namespace PositivityTheory.HtPt.Gc

theorem test_descend : ∀ (A K : Type) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsIntegrallyClosed A] [Field K] [Algebra A K] [IsFractionRing A K] (C : Type) [Field C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] (hv : v.Integers O) [Algebra A O] (𝔮 : Ideal A) (M : Type) [AddCommGroup M] [Module A M] (L : Submodule A M) (x : M), 𝔮.IsPrime → 𝔮.height = 1 → Function.Injective (algebraMap A O) → (∀ a, a ∈ 𝔮 ↔ v (algebraMap O C (algebraMap A O a)) < 1) → (1 : O) ⊗ₜ[A] x ∈ Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) → ∃ s : A, s ∉ 𝔮 ∧ s • x ∈ L := by
  intro A K _ _ _ _ _ _ _ C _ v O _ _ hv _ q M _ _ L x hq h1 hinj hcen hx
  haveI : IsDomain O := hv.hom_inj.isDomain
  haveI : ValuationRing O := ValuationRing.of_integers _ hv
  haveI := dvr_of_height_one q h1
  have hu : ∀ s : q.primeCompl, IsUnit (algebraMap A O s) := fun s => by
    rw [hv.isUnit_iff_valuation_eq_one]
    exact le_antisymm (hv.map_le_one _) (not_lt.1 fun h => s.2 ((hcen s).2 h))
  let R := Localization.AtPrime q
  letI : Algebra R O := (IsLocalization.lift (M := q.primeCompl) hu).toAlgebra
  have hcomp : ∀ a : A, algebraMap R O (algebraMap A R a) = algebraMap A O a := fun a =>
    IsLocalization.lift_eq hu a
  haveI : IsScalarTower A R O := IsScalarTower.of_algebraMap_eq fun a => (hcomp a).symm
  have hinjR : Function.Injective (algebraMap R O) := by
    set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in rw [injective_iff_map_eq_zero]
    intro r hr
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    have h2 : algebraMap A O a = 0 := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul]
      simp only at hr
      rw [hr, zero_mul]
    have : a = 0 := hinj (by simpa using h2)
    simp [this]
  haveI : IsLocalHom (algebraMap R O) := ⟨fun r hr => by
    obtain ⟨⟨a, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl r
    simp only at hr ⊢
    rw [IsLocalization.AtPrime.isUnit_mk'_iff R q]
    have h2 : IsUnit (algebraMap A O a) := by
      rw [← hcomp, ← IsLocalization.mk'_spec R a s, map_mul, hcomp]
      exact hr.mul (hu s)
    rw [hv.isUnit_iff_valuation_eq_one] at h2
    intro ha
    exact ((hcen a).1 ha).ne h2⟩
  haveI : FaithfulSMul R O := (faithfulSMul_iff_algebraMap_injective R O).2 hinjR
  haveI : Module.Flat R O := by
    rw [IsDedekindDomain.flat_iff_torsion_eq_bot, ← Submodule.isTorsionFree_iff_torsion_eq_bot]
    infer_instance
  haveI : Module.FaithfullyFlat R O := Module.FaithfullyFlat.of_flat_of_isLocalHom
  have h0 : (1 : O) ⊗ₜ[A] (L.mkQ x) = 0 := by
    have : Submodule.span O ((fun y : M => (1 : O) ⊗ₜ[A] y) '' (L : Set M)) ≤
        LinearMap.ker (L.mkQ.baseChange O) := by
      rw [Submodule.span_le]
      rintro _ ⟨y, hy, rfl⟩
      simp [(Submodule.Quotient.mk_eq_zero L).2 hy]
    simpa using this hx
  have h2 : (1 : O) ⊗ₜ[R] ((1 : R) ⊗ₜ[A] (L.mkQ x)) = 0 := by
    apply (AlgebraTensorModule.cancelBaseChange A R O O (M ⧸ L)).injective
    simpa using h0
  rw [Module.FaithfullyFlat.one_tmul_eq_zero_iff] at h2
  obtain ⟨s, hs⟩ := (IsLocalizedModule.eq_zero_iff q.primeCompl
    (TensorProduct.mk A R (M ⧸ L) 1)).1 h2
  refine ⟨s, s.2, ?_⟩
  rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_smul]
  exact hs

end PositivityTheory.HtPt.Gc
end

-- bundled from Development.WeilBound.CoreStatements.HodgeTatePoints.HtatHopfSub
section
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT

theorem PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub :
    ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) := by
  intro R _ _ _ T _ _ Γ U hU
  obtain ⟨H, A, hH, hA, hAf⟩ := PositivityTheory.HtPt.Twhopf.sub_order R T Γ U hU
  have key : Γ.btOrder U = indOrder H.subtype A := by
    ext f
    rw [PositivityTheory.HtPt.Twhopf.mem_order R T Γ U f]
    constructor
    · intro hf t
      obtain ⟨s, hs⟩ := (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).1 (hf t)
      exact (hAf _).2 ⟨s, fun t' h => hs t' h⟩
    · intro hf t
      refine (PositivityTheory.HtPt.Twhopf.reg_iff R T Γ U _).2 ?_
      obtain ⟨s, hs⟩ := (hAf _).1 (hf t)
      exact ⟨s, fun t' h => hs ⟨t', (hH t').2 h⟩ h⟩
  rw [key]
  exact PositivityTheory.HtPt.Twhopf.ind_hopf R T H H.subtype H.subtype_injective A hA

theorem PositivityTheory.HtPt.Htat.bt_sub_hopf : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (U : Γ.G.left.Opens), Γ.IsFinOpenSub U → IsHopfOrder (Γ.btOrder U) :=
  @PositivityTheory.HtPt.Htat.SubgroupHopfOrder.btOrder_isHopfOrder_of_finOpenSub
end

