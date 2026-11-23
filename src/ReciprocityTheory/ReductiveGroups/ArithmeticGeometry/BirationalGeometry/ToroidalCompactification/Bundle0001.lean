module

public import Mathlib

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AnChart
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open MvPolynomial

theorem hasFDerivAt_eval {I : Type} [Fintype I] [DecidableEq I] (p : MvPolynomial I ℂ) (x : I → ℂ) :
    HasFDerivAt (fun x => eval x p) (∑ i, eval x (pderiv i p) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i) x := by
  induction p using MvPolynomial.induction_on with
  | C a => simpa using hasFDerivAt_const a x
  | add p q hp hq =>
    refine ((hp.add hq).congr_fderiv ?_).congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => map_add _ _ _)
    simp [add_smul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    refine ((hp.mul (hasFDerivAt_apply (𝕜 := ℂ) j x)).congr_fderiv (ContinuousLinearMap.ext fun v => ?_)).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun y => by simp)
    simp [pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib, Finset.mul_sum, mul_comm, mul_left_comm, apply_ite, add_comm]

theorem anChart_alg {k A : Type} [Field k] [CommRing A] [Algebra k A] (D : ℕ) [h : Algebra.IsStandardSmoothOfRelativeDimension D k A]
    (σ : k →+* ℂ) (ψ₀ : A →+* ℂ) (h₀ : ψ₀.comp (algebraMap k A) = σ) :
    ∃ (N : ℕ) (g : Fin N → A) (f : Fin D → A) (B : Set (Fin D → ℂ)) (ε : ℝ) (Ψ : (Fin D → ℂ) → (A →+* ℂ)),
      0 < ε ∧ IsOpen B ∧ (∀ b ∈ B, (Ψ b).comp (algebraMap k A) = σ ∧ ∀ i, Ψ b (f i) = b i) ∧
      (∀ a, DifferentiableOn ℂ (fun b => Ψ b a) B) ∧
      ∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → (∀ j, ‖ψ (g j) - ψ₀ (g j)‖ < ε) →
        (fun i => ψ (f i)) ∈ B ∧ Ψ (fun i => ψ (f i)) = ψ := by
  classical
  obtain ⟨I, J, _, _, P, hd⟩ := h.out
  have := Fintype.ofFinite I
  have := Fintype.ofFinite J
  have e : Fin D ≃ {i : I // i ∉ Set.range P.map} := (Fintype.equivFinOfCardEq (by
    rw [Fintype.card_subtype_compl, ← hd, Algebra.Presentation.dimension, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card,
      Set.card_range_of_injective P.map_inj])).symm
  let ev := fun (x : I → ℂ) => eval₂Hom σ x
  have pt : ∀ ψ : A →+* ℂ, ψ.comp (algebraMap k A) = σ → ∀ p, ψ (algebraMap P.Ring A p) = ev (fun i => ψ (P.val i)) p := fun ψ hψ p => by
    rw [P.algebraMap_apply, aeval_def, ← coe_eval₂Hom, map_eval₂Hom, hψ]
  let q : I → MvPolynomial I k := fun i => if h : i ∈ Set.range P.map then P.relation h.choose else X i
  have q₁ : ∀ j, q (P.map j) = P.relation j := fun j => (dif_pos ⟨j, rfl⟩).trans
    (congrArg _ (P.map_inj (⟨j, rfl⟩ : P.map j ∈ Set.range P.map).choose_spec))
  have q₂ : ∀ i : {i : I // i ∉ Set.range P.map}, q i = X i.1 := fun i => dif_neg i.2
  let Φ : (I → ℂ) → I → ℂ := fun x i => eval x (map σ (q i))
  have Φe : ∀ x i, Φ x i = ev x (q i) := fun x i => eval_map _ _ _
  let x₀ : I → ℂ := fun i => ψ₀ (P.val i)
  let F : (I → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    ∑ i', eval x₀ (pderiv i' (map σ (q i))) • ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : I => ℂ) i'
  have hF : HasFDerivAt Φ F x₀ := hasFDerivAt_pi.2 fun i => hasFDerivAt_eval _ _
  have Fv : ∀ v i, F v i = ∑ i', ev x₀ (pderiv i' (q i)) * v i' := fun v i => by
    simp [F, ev, pderiv_map, eval_map]
  have inj : Function.Injective F := (injective_iff_map_eq_zero F).2 fun v hv => by
    have z₁ : ∀ i, i ∉ Set.range P.map → v i = 0 := fun i hi => by
      have := congrFun hv i
      rw [Fv, q₂ ⟨i, hi⟩] at this
      simpa [pderiv_X, Pi.single_apply, apply_ite] using this
    have dt : ((ev x₀).mapMatrix P.jacobiMatrix).det ≠ 0 := by
      rw [← RingHom.map_det, ← pt ψ₀ h₀, ← P.jacobian_eq_jacobiMatrix_det]
      exact (P.jacobian_isUnit.map ψ₀).ne_zero
    have z₂ : (fun j => v (P.map j)) = 0 := Matrix.eq_zero_of_vecMul_eq_zero dt (funext fun j => by
      have := congrFun hv (P.map j)
      rw [Fv, q₁, ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image P.map)) (fun i _ hi => by
        rw [z₁ i (by simpa using hi), mul_zero]), Finset.sum_image fun a _ b _ h => P.map_inj h] at this
      simpa [Matrix.vecMul, dotProduct, P.jacobiMatrix_apply, mul_comm] using this)
    funext i
    by_cases hi : i ∈ Set.range P.map
    · obtain ⟨j, rfl⟩ := hi; exact congrFun z₂ j
    · exact z₁ i hi
  let F' : (I → ℂ) ≃L[ℂ] (I → ℂ) := (LinearEquiv.ofInjectiveEndo F.toLinearMap inj).toContinuousLinearEquiv
  have cd : ContDiffAt ℂ 1 Φ x₀ := contDiffAt_pi.2 fun i =>
    (AnalyticOnNhd.eval_mvPolynomial (map σ (q i)) x₀ trivial).contDiffAt
  let T := cd.toOpenPartialHomeomorph Φ (f' := F') hF one_ne_zero
  let O := T.target ∩ interior {w | ContDiffAt ℂ 1 T.symm w}
  have oO : IsOpen O := T.open_target.inter isOpen_interior
  have mO : Φ x₀ ∈ O := ⟨cd.image_mem_toOpenPartialHomeomorph_target (f' := F') hF one_ne_zero,
    mem_interior_iff_mem_nhds.2 ((cd.to_localInverse (f' := F') hF one_ne_zero).eventually (by simp))⟩
  let em : (Fin D → ℂ) →L[ℂ] (I → ℂ) := ContinuousLinearMap.pi fun i =>
    if h : i ∈ Set.range P.map then 0 else ContinuousLinearMap.proj (e.symm ⟨i, h⟩)
  have m₁ : ∀ b j, em b (P.map j) = 0 := fun b j => by simp [em]
  have m₂ : ∀ b i, em b (e i) = b i := fun b i => by simp only [em, ContinuousLinearMap.pi_apply, dif_neg (e i).2]; simp
  have lf : ∀ x : I → ℂ, (∀ j, ev x (P.relation j) = 0) → ∃ ψ : A →+* ℂ, ∀ p, ψ (algebraMap P.Ring A p) = ev x p := fun x hx =>
    ⟨(algebraMap P.Ring A).liftOfSurjective P.algebraMap_surjective ⟨ev x, by
      show P.ker ≤ _
      rw [← P.span_range_relation_eq_ker, Ideal.span_le]
      rintro _ ⟨j, rfl⟩; exact hx j⟩, fun p => RingHom.liftOfRightInverse_comp_apply _ _ _ _ p⟩
  choose Ψ hΨ using lf
  have rel : ∀ b, em b ∈ O → ∀ j, ev (T.symm (em b)) (P.relation j) = 0 := fun b hb j => by
    rw [← q₁, ← Φe, show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₁]
  obtain ⟨ε, ε0, hε⟩ := Metric.mem_nhds_iff.1 (Filter.inter_mem (T.open_source.mem_nhds
    (cd.mem_toOpenPartialHomeomorph_source (f' := F') hF one_ne_zero)) (hF.continuousAt.preimage_mem_nhds (oO.mem_nhds mO)))
  let n := Fintype.equivFin I
  refine ⟨_, fun j => P.val (n.symm j), fun i => P.val (e i), em ⁻¹' O, ε, fun b => if h : em b ∈ O then Ψ _ (rel b h) else ψ₀, ε0,
    oO.preimage em.continuous, fun b hb => ?_, fun a => ?_, fun ψ hψ hg => ?_⟩
  · simp only [dif_pos (show em b ∈ O from hb)]
    refine ⟨RingHom.ext fun r => ?_, fun i => ?_⟩
    · rw [RingHom.comp_apply, IsScalarTower.algebraMap_apply k P.Ring A, hΨ]; exact eval₂Hom_C _ _ _
    · rw [show P.val (e i) = algebraMap P.Ring A (X (e i).1) by simp, hΨ, ← q₂, ← Φe,
        show Φ (T.symm (em b)) = em b from T.right_inv hb.1, m₂]
  · obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    refine DifferentiableOn.congr (f := fun b => eval (T.symm (em b)) (map σ p)) (fun b hb => ?_) fun b hb => ?_
    · have c₁ : ContDiffAt ℂ 1 T.symm (em b) := interior_subset hb.2
      have c₂ : DifferentiableAt ℂ (fun x : I → ℂ => eval x (map σ p)) (T.symm (em b)) := (hasFDerivAt_eval _ _).differentiableAt
      exact (c₂.comp b ((c₁.differentiableAt one_ne_zero).comp b em.differentiableAt)).differentiableWithinAt
    · simp only [dif_pos (show em b ∈ O from hb)]; rw [hΨ, eval_map]; rfl
  · have hx := hε (show (fun i => ψ (P.val i)) ∈ Metric.ball x₀ ε from (dist_pi_lt_iff ε0).2 fun i => by
      simpa [dist_eq_norm] using hg (n i))
    have e₁ : em (fun i => ψ (P.val (e i))) = Φ fun i => ψ (P.val i) := funext fun i => by
      by_cases hi : i ∈ Set.range P.map
      · obtain ⟨j, rfl⟩ := hi
        rw [m₁, Φe, q₁, ← pt ψ hψ, P.algebraMap_apply, P.aeval_val_relation, map_zero]
      · obtain ⟨j, hj⟩ := e.surjective ⟨i, hi⟩
        obtain rfl : (e j).1 = i := congrArg Subtype.val hj
        rw [m₂, Φe, q₂]
        simp only [ev, eval₂Hom_X']
    have mB : em (fun i => ψ (P.val (e i))) ∈ O := by rw [e₁]; exact hx.2
    refine ⟨mB, (dif_pos mB).trans (RingHom.ext fun a => ?_)⟩
    obtain ⟨p, rfl⟩ := P.algebraMap_surjective a
    rw [hΨ, pt ψ hψ, e₁, show T.symm (Φ fun i => ψ (P.val i)) = _ from T.left_inv hx.1]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd
section
set_option autoImplicit false

noncomputable section

open MvPowerSeries

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

abbrev PS (R : Type) [CommRing R] (n d : ℕ) : Type := MvPowerSeries (Fin n × Fin d) R

abbrev Pt (R : Type) [CommRing R] (n d : ℕ) : Type := Fin d → PS R n d

variable {R : Type} [CommRing R] {d : ℕ}

def pt (R : Type) [CommRing R] {n : ℕ} (d : ℕ) (j : Fin n) : Pt R n d := fun i => X (j, i)

def ev {m n : ℕ} (a : Fin m → Pt R n d) (f : PS R m d) : PS R n d :=
  MvPowerSeries.subst (fun p : Fin m × Fin d => a p.1 p.2) f

def comp1 {n : ℕ} (φ : Pt R 1 d) (a : Pt R n d) : Pt R n d := fun i => ev ![a] (φ i)

def addOf {n : ℕ} (F : Fin d → PS R 2 d) (a b : Pt R n d) : Pt R n d := fun i => ev ![a, b] (F i)

def Dof (F : Fin d → PS R 2 d) (u : Fin d → R) (f : PS R 1 d) : PS R 1 d :=
  ∑ j : Fin d, (∑ i : Fin d, C (u i) * ev (n := 1) ![pt R d 0, 0] (pderiv (R := R) ((1 : Fin 2), i) (F j))) *
    pderiv (R := R) ((0 : Fin 1), j) f

def DmonOf (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → R) (m : ι →₀ ℕ)
    (f : PS R 1 d) : PS R 1 d :=
  (Finset.univ : Finset ι).toList.foldr (fun l g => (Dof F (u l))^[m l] g) f

def DpolyOf (F : Fin d → PS R 2 d) {ι : Type} [Fintype ι] (u : ι → Fin d → R)
    (P : MvPolynomial ι R) (f : PS R 1 d) : PS R 1 d :=
  ∑ m ∈ P.support, C (P.coeff m) * DmonOf F u m f

@[simp] lemma ev_one {m n : ℕ} (a : Fin m → Pt R n d) : ev a (1 : PS R m d) = 1 := by
  have H : ∃ p : MvPolynomial (Fin m × Fin d) R, (p : MvPowerSeries (Fin m × Fin d) R) = 1 :=
    ⟨1, MvPolynomial.coe_one⟩
  have hc : Classical.choose H = 1 := by
    have h := (Classical.choose_spec H).trans MvPolynomial.coe_one.symm
    first
    | exact MvPolynomial.coe_inj.mp h
    | exact MvPolynomial.coe_injective _ _ h
    | exact MvPolynomial.coe_injective _ h
  first
  | (simp [ev]; done)
  | (simp only [ev, MvPowerSeries.subst, MvPowerSeries.eval₂];
      rw [dif_pos H, hc];
      exact MvPolynomial.eval₂_one _ _)
  | (unfold ev MvPowerSeries.subst MvPowerSeries.eval₂;
      rw [dif_pos H, hc];
      exact MvPolynomial.eval₂_one _ _)
  | (simp only [ev, MvPowerSeries.subst, MvPowerSeries.eval₂, dif_pos H, hc, MvPolynomial.eval₂_one])

structure FGLaw (R : Type) [CommRing R] (d : ℕ) where
  F : Fin d → PS R 2 d
  const : ∀ i, constantCoeff (F i) = 0
  unit : ∀ i, ev (n := 1) ![0, pt R d 0] (F i) = (X ((0 : Fin 1), i) : PS R 1 d)
  comm : ∀ i, ev (n := 2) ![pt R d 1, pt R d 0] (F i) = F i
  assoc : ∀ i,
    ev (n := 3) ![fun l => ev (n := 3) ![pt R d 0, pt R d 1] (F l), pt R d 2] (F i) =
      ev (n := 3) ![pt R d 0, fun l => ev (n := 3) ![pt R d 1, pt R d 2] (F l)] (F i)

namespace FGLaw

variable (G : FGLaw R d)

abbrev add {n : ℕ} (a b : Pt R n d) : Pt R n d := addOf G.F a b

def mapF {S : Type} [CommRing S] (φ : R →+* S) : Fin d → PS S 2 d :=
  fun i => MvPowerSeries.map φ (G.F i)

end FGLaw

structure OAct (O : Type) [CommRing O] (G : FGLaw R d) where
  act : O → Pt R 1 d
  const : ∀ a i, constantCoeff (act a i) = 0
  hom : ∀ a, comp1 (act a) (G.add (pt R (n := 2) d 0) (pt R (n := 2) d 1)) =
    G.add (comp1 (act a) (pt R (n := 2) d 0)) (comp1 (act a) (pt R (n := 2) d 1))
  add_act : ∀ a b, act (a + b) = G.add (act a) (act b)
  mul_act : ∀ a b, act (a * b) = comp1 (act a) (act b)
  one_act : act 1 = pt R d 0

structure FB (R : Type) [CommRing R] (d : ℕ) (O : Type) [CommRing O] [StarRing O] where
  G : FGLaw R d
  A : OAct O G
  ph1 : PS R 3 d
  ph2 : PS R 3 d
  sy : PS R 2 d
  ad : O → PS R 2 d
  cocycleLeft_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph1 = 1
  cocycleLeft_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph1 = 1
  cocycleRight_zero_fst : ev (n := 2) ![0, pt R d 0, pt R d 1] ph2 = 1
  cocycleRight_zero_snd : ev (n := 2) ![pt R d 0, 0, pt R d 1] ph2 = 1
  cocycleRight_zero_thd : ev (n := 2) ![pt R d 0, pt R d 1, 0] ph2 = 1
  symmetry_zero_fst : ev (n := 1) ![0, pt R d 0] sy = 1
  symmetry_zero_snd : ev (n := 1) ![pt R d 0, 0] sy = 1
  adjoint_zero_fst : ∀ a, ev (n := 1) ![0, pt R d 0] (ad a) = 1
  adjoint_zero_snd : ∀ a, ev (n := 1) ![pt R d 0, 0] (ad a) = 1

  cocycleLeft_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph1 =
      ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph1 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph1

  cocycleLeft_comm : ev (n := 3) ![pt R d 1, pt R d 0, pt R d 2] ph1 = ph1

  cocycleRight_assoc :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph2 *
        ev (n := 4) ![pt R d 0, G.add (pt R d 1) (pt R d 2), pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph2

  cocycleRight_comm : ev (n := 3) ![pt R d 0, pt R d 2, pt R d 1] ph2 = ph2

  interchange :
    ev (n := 4) ![pt R d 0, pt R d 1, pt R d 2] ph1 * ev (n := 4) ![pt R d 0, pt R d 1, pt R d 3] ph1 *
        ev (n := 4) ![G.add (pt R d 0) (pt R d 1), pt R d 2, pt R d 3] ph2 =
      ev (n := 4) ![pt R d 0, pt R d 2, pt R d 3] ph2 * ev (n := 4) ![pt R d 1, pt R d 2, pt R d 3] ph2 *
        ev (n := 4) ![pt R d 0, pt R d 1, G.add (pt R d 2) (pt R d 3)] ph1

  sy_inv : sy * ev (n := 2) ![pt R d 1, pt R d 0] sy = 1

  sy_law :
    ph2 * ev (n := 3) ![pt R d 0, pt R d 1] sy * ev (n := 3) ![pt R d 0, pt R d 2] sy =
      ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] sy * ev (n := 3) ![pt R d 1, pt R d 2, pt R d 0] ph1

  adjoint_compat_left : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), comp1 (A.act a) (pt R d 1), pt R d 2] ph1 *
        ev (n := 3) ![G.add (pt R d 0) (pt R d 1), pt R d 2] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 2] (ad a) * ev (n := 3) ![pt R d 1, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, pt R d 1, comp1 (A.act (star a)) (pt R d 2)] ph1

  adjoint_compat_right : ∀ a : O,
    ev (n := 3) ![comp1 (A.act a) (pt R d 0), pt R d 1, pt R d 2] ph2 *
        ev (n := 3) ![pt R d 0, G.add (pt R d 1) (pt R d 2)] (ad a) =
      ev (n := 3) ![pt R d 0, pt R d 1] (ad a) * ev (n := 3) ![pt R d 0, pt R d 2] (ad a) *
        ev (n := 3) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1),
          comp1 (A.act (star a)) (pt R d 2)] ph2
  ad_one : ad 1 = 1

  ad_mul : ∀ a b : O, ad (a * b) =
    ev (n := 2) ![comp1 (A.act b) (pt R d 0), pt R d 1] (ad a) *
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] (ad b)

  ad_add : ∀ a b : O,
    ev (n := 2) ![comp1 (A.act a) (pt R d 0), comp1 (A.act b) (pt R d 0), pt R d 1] ph1 * ad (a + b) =
      ad a * ad b *
        ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1), comp1 (A.act (star b)) (pt R d 1)] ph2

  ad_sy : ∀ a : O,
    ad a * ev (n := 2) ![pt R d 1, pt R d 0] (ad (star a)) *
        ev (n := 2) ![comp1 (A.act a) (pt R d 0), pt R d 1] sy =
      ev (n := 2) ![pt R d 0, comp1 (A.act (star a)) (pt R d 1)] sy

namespace FB

variable {O : Type} [CommRing O] [StarRing O] (B : FB R d O)

variable (k : Type) [CommRing k] [Algebra ℚ k] [Algebra R k]

abbrev toK {n : ℕ} (f : PS R n d) : PS k n d := MvPowerSeries.map (algebraMap R k) f

def expS {n : ℕ} (f : PS k n d) : PS k n d := PowerSeries.subst f (PowerSeries.exp k)

def actK (a : O) : Pt k 1 d := fun i => MvPowerSeries.map (algebraMap R k) (B.A.act a i)

def FK : Fin d → PS k 2 d := B.G.mapF (algebraMap R k)

structure IsCanonGauge (h : PS k 2 d) : Prop where
  ax0 : ev (n := 1) ![0, pt k d 0] h = 0
  ax1 : ev (n := 1) ![pt k d 0, 0] h = 0
  ph1 : toK k B.ph1 = expS k (ev (n := 3) ![pt k d 0, pt k d 2] h + ev (n := 3) ![pt k d 1, pt k d 2] h -
    ev (n := 3) ![addOf (B.FK k) (pt k d 0) (pt k d 1), pt k d 2] h)
  ph2 : toK k B.ph2 = expS k (ev (n := 3) ![pt k d 0, pt k d 1] h + ev (n := 3) ![pt k d 0, pt k d 2] h -
    ev (n := 3) ![pt k d 0, addOf (B.FK k) (pt k d 1) (pt k d 2)] h)
  sy : toK k B.sy = expS k (ev (n := 2) ![pt k d 1, pt k d 0] h - h)
  ad : ∀ a : O, toK k (B.ad a) = expS k (ev (n := 2) ![comp1 (B.actK k a) (pt k d 0), pt k d 1] h -
    ev (n := 2) ![pt k d 0, comp1 (B.actK k (star a)) (pt k d 1)] h)

def hL (h : PS k 2 d) (w0 : O) : PS k 1 d := ev (n := 1) ![pt k d 0, comp1 (B.actK k w0) (pt k d 0)] h

def nabVal (h : PS k 2 d) (w0 : O) (m : ℕ) (f : PS k 1 d) {ι : Type} [Fintype ι]
    (u : ι → Fin d → k) (P : MvPolynomial ι k) : k :=
  constantCoeff (DpolyOf (B.FK k) u P (f * expS k ((m : k) • B.hL k h w0)))

end FB

def FB.triv {O : Type} [CommRing O] [StarRing O] (G : FGLaw R d) (A : OAct O G) : FB R d O where
  G := G
  A := A
  ph1 := 1
  ph2 := 1
  sy := 1
  ad := fun _ => 1
  cocycleLeft_zero_fst := by simp
  cocycleLeft_zero_snd := by simp
  cocycleLeft_zero_thd := by simp
  cocycleRight_zero_fst := by simp
  cocycleRight_zero_snd := by simp
  cocycleRight_zero_thd := by simp
  symmetry_zero_fst := by simp
  symmetry_zero_snd := by simp
  adjoint_zero_fst := by simp
  adjoint_zero_snd := by simp
  cocycleLeft_assoc := by simp
  cocycleLeft_comm := by simp
  cocycleRight_assoc := by simp
  cocycleRight_comm := by simp
  interchange := by simp
  sy_inv := by simp
  sy_law := by simp
  adjoint_compat_left := by simp
  adjoint_compat_right := by simp
  ad_one := by simp
  ad_mul := by simp
  ad_add := by simp
  ad_sy := by simp

end ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
section
noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory

attribute [local instance] MvPolynomial.gradedAlgebra

abbrev Sp (R : Type) [CommRing R] : Scheme.{0} := Spec (CommRingCat.of R)

abbrev spMap {R R' : Type} [CommRing R] [CommRing R'] (f : R →+* R') : Sp R' ⟶ Sp R :=
  Spec.map (CommRingCat.ofHom f)

abbrev PSpace (R : Type) [CommRing R] (N : ℕ) : Scheme.{0} :=
  Proj (MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R)

def PSpace.str (R : Type) [CommRing R] (N : ℕ) : PSpace R N ⟶ Sp R :=
  Proj.toSpecZero _ ≫ spMap (algebraMap R ↥(MvPolynomial.homogeneousSubmodule (Fin (N + 1)) R 0))

def IsProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsClosedImmersion i ∧ i ≫ PSpace.str R N = f

def IsQProjOver {R : Type} [CommRing R] {X : Scheme.{0}} (f : X ⟶ Sp R) : Prop :=
  ∃ (N : ℕ) (i : X ⟶ PSpace R N), IsImmersion i ∧ QuasiCompact i ∧ i ≫ PSpace.str R N = f

def IsNormalScheme (X : Scheme.{0}) : Prop :=
  ∀ x : X, IsDomain (X.presheaf.stalk x) ∧ IsIntegrallyClosed (X.presheaf.stalk x)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
end
end

