module

public import Formalism.LocalToGlobal.ProjectiveLattices.SectionOfLineBundleOne
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0015
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0010

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ArcPtX
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

lemma arcι_X_isUnit (Dw : Datum H) (K₁ : Type) [Field K₁] : IsUnit (arcι Dw K₁ PowerSeries.X) := by
  have h : IsUnit (HahnSeries.ofPowerSeries ℤ K₁ PowerSeries.X) := by
    rw [isUnit_iff_ne_zero]
    first
      | (rw [HahnSeries.ofPowerSeries_X]; exact HahnSeries.single_ne_zero one_ne_zero)
      | (intro h0
         exact PowerSeries.X_ne_zero ((map_eq_zero_iff _ HahnSeries.ofPowerSeries_injective).mp h0))
      | (simp; done)
  exact (h.map (MvPolynomial.C (σ := ArcLt Dw))).map
    (algebraMap (MvPolynomial (ArcLt Dw) (LaurentSeries K₁)) (ArcS Dw K₁))

lemma arc_pt_X (Dw : Datum H) (K₁ : Type) [Field K₁] (q : Sp (ArcS Dw K₁)) :
    PowerSeries.X ∉ ((spMap (arcι Dw K₁)) q).asIdeal := by
  intro hX
  have h1 : arcι Dw K₁ PowerSeries.X ∈ q.asIdeal := by
    first
      | exact hX
      | (simpa using hX)
  exact q.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ h1 (arcι_X_isUnit Dw K₁))

theorem arcPt_point (Y : Model Xo c β) {K₁ : Type} [Field K₁] (b : O →+* K₁) [Algebra c.F (ArcS Dw K₁)]
    (hcomp : (algebraMap c.F (ArcS Dw K₁)).comp β = (arcι Dw K₁).comp ((PowerSeries.C (R := K₁)).comp b))
    (χ : Sp (PowerSeries K₁) ⟶ Y.X) (hχs : χ ≫ Y.s = spMap (PowerSeries.C (R := K₁)) ≫ spMap b)
    (hj : ∀ x : Sp (PowerSeries K₁), PowerSeries.X ∉ x.asIdeal → χ x ∈ Set.range Y.j) :
    ∃ z : Sp (ArcS Dw K₁) ⟶ Xo.XF c, z ≫ Y.j = spMap (arcι Dw K₁) ≫ χ ∧
      z ≫ Y.jQ ≫ pullback.snd _ _ = spMap (algebraMap c.F (ArcS Dw K₁)) := by
  haveI := Y.jQ_open
  have hw : (spMap (arcι Dw K₁) ≫ χ) ≫ Y.s = spMap (algebraMap c.F (ArcS Dw K₁)) ≫ spMap β := by
    rw [Category.assoc, hχs, ← spMap_comp, ← spMap_comp, ← spMap_comp, hcomp]
  let g : Sp (ArcS Dw K₁) ⟶ pullback Y.s (spMap β) :=
    pullback.lift (spMap (arcι Dw K₁) ≫ χ) (spMap (algebraMap c.F (ArcS Dw K₁))) hw
  have hg : Set.range g ⊆ Set.range Y.jQ := by
    rintro _ ⟨q, rfl⟩
    rw [← Y.ab_gen]
    have e1 : (pullback.fst Y.s (spMap β)) (g q) = χ ((spMap (arcι Dw K₁)) q) := by
      have := congrArg (fun f : Sp (ArcS Dw K₁) ⟶ Y.X => f q) (pullback.lift_fst _ _ hw)
      first
        | exact this
        | (simpa using this)
    show (pullback.fst Y.s (spMap β)) (g q) ∈ abLocus Y.t.G
    rw [e1]
    obtain ⟨p, hp⟩ := hj _ (arc_pt_X Dw K₁ q)
    rw [← hp]
    have h2 : Y.jQ p ∈ (pullback.fst Y.s (spMap β)) ⁻¹' abLocus Y.t.G := by
      rw [Y.ab_gen]
      exact ⟨p, rfl⟩
    exact h2
  refine ⟨IsOpenImmersion.lift Y.jQ g hg, ?_, ?_⟩
  · show IsOpenImmersion.lift Y.jQ g hg ≫ Y.jQ ≫ pullback.fst _ _ = _
    rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_fst]
  · rw [← Category.assoc, IsOpenImmersion.lift_fac, pullback.lift_snd]

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.CrudeDiv
section
set_option autoImplicit false

noncomputable section

namespace Formalism.L2.Pj.Crude

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

variable {k : Type} [CommRing k] {d n : ℕ}

theorem div_Lin_add (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f + g) = Lin b v f + Lin b v g := by
  simp only [Lin, map_add (f := _), mul_add, Finset.sum_add_distrib]

theorem div_Lin_mul (b : Fin n) (v : Fin d → k) (f g : PS k n d) :
    Lin b v (f * g) = Lin b v f * g + f * Lin b v g := by
  simp only [Lin, Derivation.leibniz, smul_eq_mul, mul_add, Finset.sum_add_distrib, Finset.sum_mul,
    Finset.mul_sum]
  rw [add_comm]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => ?_ <;> ring

theorem div_Lin_C (b : Fin n) (v : Fin d → k) (c : k) : Lin b v (C c : PS k n d) = 0 := by
  simp [Lin, MvPowerSeries.pderiv_C]

theorem Lin_linForm (b b' : Fin n) (v w : Fin d → k) :
    Lin b v (∑ j : Fin d, C (w j) * (X (b', j) : PS k n d)) =
      C (if b = b' then ∑ j : Fin d, v j * w j else 0) := by
  unfold Lin
  by_cases h : b = b'
  · subst h
    set_option synthInstance.maxHeartbeats 100000 in
      simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Finset.mul_sum,
      map_sum, Pi.single_apply, Prod.ext_iff]
  · simp [MvPowerSeries.pderiv_X, MvPowerSeries.pderiv_C, Derivation.leibniz, Pi.single_apply,
      Prod.ext_iff, h]

theorem div_Lin_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (Q : MvPolynomial ι k) :
    Lin (cp l) (u l) (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ (MvPolynomial.pderiv l Q) := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
    rw [MvPolynomial.aeval_C, MvPolynomial.pderiv_C, map_zero, MvPowerSeries.algebraMap_apply]
    simpa using div_Lin_C (cp l) (u l) a
  | add p q hp hq => rw [map_add (f := _), div_Lin_add, hp, hq, map_add (f := _), map_add (f := _)]
  | mul_X p i hp =>
    rw [map_mul, div_Lin_mul, hp, MvPolynomial.aeval_X, hl, Derivation.leibniz, MvPolynomial.pderiv_X]
    by_cases h : l = i
    · subst h
      simp
      ring
    · simp [h, Pi.single_apply]
      ring

theorem div_Lin_iter_aeval {ι : Type} [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k) (φ : ι → PS k n d)
    (l : ι) (hl : ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0)) (t : ℕ) (Q : MvPolynomial ι k) :
    (Lin (cp l) (u l))^[t] (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ ((MvPolynomial.pderiv l)^[t] Q) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, div_Lin_aeval cp u φ l hl]

theorem div_LinMon_aeval {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) (Q : MvPolynomial ι k) :
    LinMon cp u a (MvPolynomial.aeval φ Q) = MvPolynomial.aeval φ
      ((Finset.univ : Finset ι).toList.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) Q) := by
  unfold LinMon
  generalize (Finset.univ : Finset ι).toList = L
  induction L with
  | nil => rfl
  | cons l L ih =>
    simp only [List.foldr_cons]
    rw [ih]
    by_cases h0 : a l = 0
    · rw [h0]
      rfl
    · exact div_Lin_iter_aeval cp u φ l (hdual l (ha l h0)) (a l) _

theorem div_constCoeff_aeval {ι : Type} (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0)
    (Q : MvPolynomial ι k) : constantCoeff (MvPolynomial.aeval φ Q) = MvPolynomial.constantCoeff Q := by
  induction Q using MvPolynomial.induction_on with
  | C a => simp [MvPowerSeries.algebraMap_apply]
  | add p q hp hq => simp only [map_add (f := _), hp, hq]
  | mul_X p i hp => simp [hp, hφ0]

theorem div_iter_pderiv_monomial {ι : Type} [DecidableEq ι] (i : ι) (t : ℕ) (s : ι →₀ ℕ) (c : k) :
    (MvPolynomial.pderiv i)^[t] (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - Finsupp.single i t) (c * ((s i).descFactorial t : k)) := by
  induction t with
  | zero => simp
  | succ t ih =>
    have h1 : s - Finsupp.single i t - Finsupp.single i 1 = s - Finsupp.single i (t + 1) := by
      ext j
      first
        | (simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp only [Finsupp.tsub_apply, Finsupp.single_apply]; split_ifs <;> omega)
        | (simp [Finsupp.single_apply]; split_ifs <;> omega)
    have h2 : (s - Finsupp.single i t) i = s i - t := by
      first
        | simp only [Finsupp.coe_tsub, Pi.sub_apply, Finsupp.single_eq_same]
        | simp
    rw [Function.iterate_succ_apply', ih, MvPolynomial.pderiv_monomial, h1, h2,
      Nat.descFactorial_succ]
    congr 1
    push_cast
    ring

theorem div_listSum_apply_of_notMem {ι : Type} (a : ι →₀ ℕ) (L : List ι) (l : ι) (hl : l ∉ L) :
    (L.map fun l' => Finsupp.single l' (a l')).sum l = 0 := by
  induction L with
  | nil => simp
  | cons x L ih =>
    simp only [List.mem_cons, not_or] at hl
    simp [Finsupp.single_apply, Ne.symm hl.1, ih hl.2]

theorem div_fold_monomial {ι : Type} [DecidableEq ι] (a : ι →₀ ℕ) (L : List ι) (hL : L.Nodup) (s : ι →₀ ℕ)
    (c : k) :
    L.foldr (fun l g => (MvPolynomial.pderiv l)^[a l] g) (MvPolynomial.monomial s c) =
      MvPolynomial.monomial (s - (L.map fun l => Finsupp.single l (a l)).sum)
        (c * (L.map fun l => ((s l).descFactorial (a l) : k)).prod) := by
  induction L with
  | nil => simp
  | cons x L ih =>
    rw [List.nodup_cons] at hL
    rw [List.foldr_cons, ih hL.2, div_iter_pderiv_monomial]
    have hx : (s - (L.map fun l => Finsupp.single l (a l)).sum) x = s x := by
      rw [Finsupp.tsub_apply, div_listSum_apply_of_notMem a L x hL.1, Nat.sub_zero]
    simp only [List.map_cons, List.sum_cons, List.prod_cons, hx]
    congr 1
    · rw [tsub_tsub, add_comm]
    · ring

theorem linMon_aeval_monomial {ι : Type} [Fintype ι] [DecidableEq ι] (cp : ι → Fin n) (u : ι → Fin d → k)
    (φ : ι → PS k n d) (hφ0 : ∀ i, constantCoeff (φ i) = 0) (Good : Set ι)
    (hdual : ∀ l ∈ Good, ∀ l', Lin (cp l) (u l) (φ l') = C (if l = l' then 1 else 0))
    (a α : ι →₀ ℕ) (ha : ∀ l, a l ≠ 0 → l ∈ Good) :
    constantCoeff (LinMon cp u a (MvPolynomial.aeval φ (MvPolynomial.monomial α (1 : k)))) =
      if a = α then ((α.prod fun _ e => e.factorial : ℕ) : k) else 0 := by
  classical
  rw [div_LinMon_aeval cp u φ Good hdual a ha, div_fold_monomial a _ (Finset.nodup_toList _),
    div_constCoeff_aeval φ hφ0, MvPolynomial.constantCoeff_monomial]
  have hLs : ∀ (M : Type) [AddCommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).sum = ∑ l, f l := fun M _ f => by
    rw [← Multiset.sum_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hLp : ∀ (M : Type) [CommMonoid M] (f : ι → M),
      ((Finset.univ : Finset ι).toList.map f).prod = ∏ l, f l := fun M _ f => by
    rw [← Multiset.prod_coe, ← Multiset.map_coe, Finset.coe_toList]
    rfl
  have hS : ((Finset.univ : Finset ι).toList.map fun l => Finsupp.single l (a l)).sum = a := by
    rw [hLs]
    ext j
    simp [Finsupp.finsetSum_apply, Finsupp.single_apply]
  have hP : ((Finset.univ : Finset ι).toList.map fun l => ((α l).descFactorial (a l) : k)).prod =
      ∏ l, ((α l).descFactorial (a l) : k) := hLp k _
  rw [hS, hP, one_mul]
  by_cases hEq : a = α
  · subst hEq
    rw [tsub_self, if_pos rfl, if_pos rfl, Finsupp.prod_fintype _ _ (fun _ => Nat.factorial_zero)]
    push_cast
    exact Finset.prod_congr rfl fun l _ => by rw [Nat.descFactorial_self]
  · rw [if_neg hEq]
    split_ifs with h0
    · have hle : α ≤ a := tsub_eq_zero_iff_le.mp h0
      obtain ⟨l, hl⟩ : ∃ l, α l < a l := by
        by_contra hcon
        push_neg at hcon
        exact hEq (le_antisymm (Finsupp.le_def.mpr hcon) hle)
      exact Finset.prod_eq_zero (Finset.mem_univ l)
        (by rw [Nat.descFactorial_eq_zero_iff_lt.mpr hl, Nat.cast_zero])
    · rfl

end Formalism.L2.Pj.Crude
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ExtPtUnique
section
noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}

theorem extPt (Y : Model Xo c β) (T : CDVR) (b : O →+* T.V) (x : Sp T.Fr ⟶ Xo.XF c)
    (hx : x ≫ Y.j ≫ Y.s = Out.jK T.V ≫ spMap b) :
    ∃ yt : Sp T.V ⟶ Y.X, Out.jK T.V ≫ yt = x ≫ Y.j ∧ yt ≫ Y.s = spMap b := by
  haveI : IsProper Y.s := projProper _ _ _ Y.proj
  have hE : ValuativeCriterion.Existence Y.s := by
    have h1 : UniversallyClosed Y.s := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h1
    exact h1.1
  let S : ValuativeCommSq Y.s :=
    { R := T.V, K := FractionRing T.V, i₁ := x ≫ Y.j, i₂ := spMap b,
      commSq := ⟨by rw [Category.assoc]; exact hx⟩ }
  obtain ⟨⟨⟨l, hl1, hl2⟩⟩⟩ := hE S
  exact ⟨l, hl1, hl2⟩

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
section
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace Formalism.L2.Pj

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable (Xo : Moduli Dw l) (c : Coeff l)

def IntFramesSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    (letI := io.toAlgebra; ∀ y₀ : FrPt Xo c T.Fr, y₀.x = z ≫ pullback.fst _ _ →
      ∃ (y : IntFr Xo c T io) (t : Ix Dw → T.Frˣ), FrBor t y₀ y.1)

def GenFibreSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β)
    (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt),
      ∃ (t' : SAB H (Sp T.Fr)) (_m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _))
        (_m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))), True

def LieFreeSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (G : SAB H (Sp T.V)) (t' : SAB H (Sp T.Fr)) (x : Sp T.Fr ⟶ Xo.X)
    (m1 : SABMap t' Xo.univ.t x) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
    (letI := io.toAlgebra; x ≫ Xo.s = sOf c T.Fr) →
    letI := io.toAlgebra
    ∀ u₀ : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left),
    (∀ τ i, IsTanAt x (u₀ τ i)) → (∀ τ i, IsEigAt c τ (u₀ τ i)) →
    (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u₀ τ) a w) →
    ∃ (ub : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (epsOver T.V T.V ⟶ G.G))
      (u : ∀ τ : E →+* ℂ, Fin (Dw.mult τ) → (Sp (DualNumber T.Fr) ⟶ Xo.univ.t.G.left)),
      ((∀ τ i, IsTan (ub τ i)) ∧ (∀ τ i, IsEigV c io G τ (ub τ i)) ∧
        (∀ τ (w : epsOver T.V T.V ⟶ G.G), IsTan w → IsEigV c io G τ w →
          ∃! a : Fin (Dw.mult τ) → T.V, IsComb (ub τ) a w) ∧
        ∀ τ i, ∃ u' : Sp (DualNumber T.Fr) ⟶ t'.G.left, u' ≫ m1.φ = u τ i ∧
          u' ≫ m2.φ = spMap (dualMap (algebraMap T.V T.Fr)) ≫ (ub τ i).left) ∧
      (∀ τ i, IsTanAt x (u τ i)) ∧ (∀ τ i, IsEigAt c τ (u τ i)) ∧
      (∀ τ w, IsTanAt x w → IsEigAt c τ w → ∃! a : Fin (Dw.mult τ) → T.Fr, IsCombAt x (u τ) a w) ∧
      ∀ τ i, ∃ cf : Fin (Dw.mult τ) → T.Fr, IsUnit (cf i) ∧ (∀ j, i < j → cf j = 0) ∧ IsCombAt x (u₀ τ) cf (u τ i)

def ThetaFrameSt : Prop :=
  ∀ (T : CDVR) (io : c.F →+* T.Fr) (O : Type) [CommRing O] (β : O →+* c.F) (Y : Model Xo c β),
    PushInvertible Y.t.G Y.t.PP.L → ∀ (yt : Sp T.V ⟶ Y.X) (z : Sp T.Fr ⟶ Xo.XF c),
    z ≫ Y.j = spMap (algebraMap T.V T.Fr) ≫ yt → z ≫ pullback.snd _ _ = spMap io →
    ∀ (G : SAB H (Sp T.V)) (_m : SABMap G Y.t yt) (t' : SAB H (Sp T.Fr))
      (m1 : SABMap t' Xo.univ.t (z ≫ pullback.fst _ _)) (m2 : SABMap t' G (spMap (algebraMap T.V T.Fr))),
      letI := io.toAlgebra
      ∀ s₀ : LB.Sec (PPx (z ≫ pullback.fst _ _)),
      (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i, s'.f i = scal (z ≫ pullback.fst _ _) a i * s₀.f i) →
      ∃ (θ : LB.Sec G.PP.L) (s : LB.Sec (PPx (z ≫ pullback.fst _ _))),
        (∀ σ : LB.Sec G.PP.L, ∃! a : T.V, ∀ i,
          σ.f i = resG G.G.left le_top ((G.G.hom).appTop.hom (toΓ T.V a)) * θ.f i) ∧
        (∃ (w1 : LB.Iso t'.PP.L (Xo.univ.t.PP.L.pull m1.φ)) (w2 : LB.Iso t'.PP.L (G.PP.L.pull m2.φ))
          (σ : LB.Sec t'.PP.L) (s1 : LB.Sec (Xo.univ.t.PP.L.pull m1.φ)) (θ2 : LB.Sec (G.PP.L.pull m2.φ)),
          RigIso m1 w1 ∧ RigIso m2 w2 ∧ IsoMaps w1 σ s1 ∧ IsoMaps w2 σ θ2 ∧ PullSec m2.φ θ θ2 ∧
          ∀ g : t'.G.left ⟶ Gx (z ≫ pullback.fst _ _),
            g ≫ (snd (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = m1.φ →
            g ≫ (fst (Over.mk (z ≫ pullback.fst _ _)) Xo.univ.t.G).left = t'.G.hom →
            ∀ j (h : (Xo.univ.t.PP.L.pull m1.φ).U j ≤ g ⁻¹ᵁ (PPx (z ≫ pullback.fst _ _)).U (fun _ => j PUnit.unit)),
              s1.f j = (g.appLE _ _ h).hom (s.f (fun _ => j PUnit.unit))) ∧
        (∀ s' : LB.Sec (PPx (z ≫ pullback.fst _ _)), ∃! a : T.Fr, ∀ i,
          s'.f i = scal (z ≫ pullback.fst _ _) a i * s.f i) ∧
        ∃ a : T.Frˣ, ∀ i, s.f i = scal (z ≫ pullback.fst _ _) (a : T.Fr) i * s₀.f i

def SpreadSt : Prop :=
  ∀ (S : Type) [Field S] [Algebra c.F S] (y : FrPt Xo c S),
    FromTest (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) y

theorem genFibre (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) : GenFibreSt Xo c := by
  intro T io O _ β Y yt z h1 h2 G m
  obtain ⟨PP', cub, sym, adj, prim, m2, -⟩ := sabPull hC (spMap (algebraMap T.V T.Fr)) G
  obtain ⟨n, -⟩ := sabComp pullCubComp E H _ _ _ Y.t G _ yt _ m m2
  rw [← h1] at n
  have n' : SABMap _ Y.t (z ≫ (Y.jQ ≫ pullback.fst _ _)) := n
  obtain ⟨m1, -⟩ := sabCancel pullCubCancel E H _ _ _ Y.t Y.oF.t _ _ z Y.m n'
  obtain ⟨n2, -⟩ := sabComp pullCubComp E H _ _ _ Xo.univ.t Y.oF.t _ _ z Y.m0.toSABMap m1
  exact ⟨_, n2, m2, trivial⟩


set_option maxHeartbeats 1000000 in
theorem intFrames_of (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hG : GenFibreSt Xo c) (hL : LieFreeSt Xo c)
    (hT : ThetaFrameSt Xo c) (hS : SpreadSt Xo c) : IntFramesSt Xo c := by

  have e : ∀ (X : Scheme.{0}) (U : X.Opens) (h : U ≤ (𝟙 X) ⁻¹ᵁ U) (v : Γ(X, U)),
      (Scheme.Hom.appLE (𝟙 X) U U h).hom v = v := by
    intro X U h v
    simp [Scheme.Hom.appLE]
    first
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; rfl)
      | (erw [Category.id_comp, CategoryTheory.Functor.map_id]; simp; done)
      | (erw [CategoryTheory.Functor.map_id]; simp; done)
  have key : ∀ {S : Type} [CommRing S] (x : Sp S ⟶ Xo.X) (s s0 : LB.Sec (PPx x)) (a : S),
      (∀ i, s.f i = scal x a i * s0.f i) → ∀ (i : Fin 1 → Xo.univ.t.PP.L.ι)
        (h : (PPx x).U i ≤ (𝟙 (Gx x)) ⁻¹ᵁ (PPx x).U i),
        (Scheme.Hom.appLE (𝟙 (Gx x)) _ _ h).hom (scal x a i * s0.f i) = s.f i := by
    intro S _ x s s0 a ha i h
    rw [ha i]
    exact e _ _ _ _
  intro T io O _ β Y hP yt z h1 h2
  letI := io.toAlgebra
  intro y₀ hy₀
  obtain ⟨x0, hx0, u0, tan0, eig0, basis0, s0, gen0⟩ := y₀
  dsimp only at hy₀
  subst hy₀
  obtain ⟨PP', cub, sym, adj, prim, mG, -⟩ := sabPull hC yt Y.t
  obtain ⟨t', m1, m2, -⟩ := hG T io O β Y yt z h1 h2 _ mG
  obtain ⟨ub, u, ⟨hub1, hub2, hub3, hub4⟩, hu1, hu2, hu3, hu4⟩ :=
    hL T io _ t' _ m1 m2 hx0 u0 tan0 eig0 basis0
  obtain ⟨θ, s, hθ1, hθ2, hs, a, ha⟩ := hT T io O β Y hP yt z h1 h2 _ mG t' m1 m2 s0 gen0
  choose cf hcf1 hcf2 hcf3 using hu4
  let y : FrPt Xo c T.Fr :=
    { x := _, x_over := hx0, u := u, tan := hu1, eig := hu2, basis := hu3, s := s, gen := hs }
  refine ⟨⟨y, hS T.Fr y, _, t', m1, m2, ⟨ub, hub1, hub2, hub3, hub4⟩, θ, hθ1, hθ2⟩,
    fun k => match k with | none => a | some p => (hcf1 p.1 p.2).unit, rfl, ?_, 𝟙 _, ?_, ?_, ?_⟩
  · intro τ i
    exact ⟨cf τ i, (hcf1 τ i).unit_spec.symm, hcf2 τ i, hcf3 τ i⟩
  · exact Category.id_comp _
  · exact Category.id_comp _
  · exact key _ s s0 _ ha

theorem intFrames (hC : ReciprocityTheory.ChartRestriction.G.Out.CubePullSt) (hL : LieFreeSt Xo c) (hT : ThetaFrameSt Xo c)
    (hS : SpreadSt Xo c) : IntFramesSt Xo c :=
  intFrames_of Xo c hC (genFibre Xo c hC) hL hT hS

end Formalism.L2.Pj
end
end

