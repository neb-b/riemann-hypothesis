module

public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0008
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0007
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpOfPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActPf
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0010
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Bundle0001
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006

@[expose] public section

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartJetTrA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj

attribute [local instance] Over.cartesianMonoidalCategory

section Ring

variable {V K : Type} [CommRing V] [CommRing K] (f : V →+* K)

theorem jetCoef_mk (κ : Type) (m : ℕ) (p : MvPolynomial κ V) :
    jetCoef f κ m (Ideal.Quotient.mk _ p) = Ideal.Quotient.mk _ (MvPolynomial.map f p) := rfl

theorem psTrunc_map {σ : Type} [Fintype σ] [DecidableEq σ] (m : ℕ) (F : MvPowerSeries σ V) :
    psTrunc m (MvPowerSeries.map f F) = MvPolynomial.map f (psTrunc m F) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [psTrunc, map_sum, MvPolynomial.map_monomial, MvPowerSeries.coeff_map]

theorem jetCoef_alg (κ : Type) (m : ℕ) :
    (jetCoef f κ m).comp (algebraMap V (Jet V κ m)) = (algebraMap K (Jet K κ m)).comp f := by
  refine RingHom.ext fun v => ?_
  first
  | (show jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C v)) = Ideal.Quotient.mk _ (MvPolynomial.C (f v))
     rw [jetCoef_mk, MvPolynomial.map_C])
  | (simp only [RingHom.comp_apply]
     rw [← Ideal.Quotient.mk_algebraMap, ← Ideal.Quotient.mk_algebraMap, MvPolynomial.algebraMap_eq,
       MvPolynomial.algebraMap_eq, jetCoef_mk, MvPolynomial.map_C])

theorem jetCoef_aug (κ : Type) (m : ℕ) :
    ((jetAug : Jet K κ m →ₐ[K] K) : Jet K κ m →+* K).comp (jetCoef f κ m) =
      f.comp ((jetAug : Jet V κ m →ₐ[V] V) : Jet V κ m →+* V) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.C a))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.C a)))
    rw [jetCoef_mk, MvPolynomial.map_C]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.C (f a)) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.C a))
    simp
  · show (jetAug : Jet K κ m →ₐ[K] K) (jetCoef f κ m (Ideal.Quotient.mk _ (MvPolynomial.X i))) =
      f ((jetAug : Jet V κ m →ₐ[V] V) (Ideal.Quotient.mk _ (MvPolynomial.X i)))
    rw [jetCoef_mk, MvPolynomial.map_X]
    show (MvPolynomial.aeval fun _ => (0 : K)) (MvPolynomial.X i) =
      f ((MvPolynomial.aeval fun _ => (0 : V)) (MvPolynomial.X i))
    simp

theorem jetCoef_trunc (κ : Type) (m : ℕ) :
    ((jetTrunc : Jet K κ (m + 1) →ₐ[K] Jet K κ m) : Jet K κ (m + 1) →+* Jet K κ m).comp (jetCoef f κ (m + 1)) =
      (jetCoef f κ m).comp ((jetTrunc : Jet V κ (m + 1) →ₐ[V] Jet V κ m) : Jet V κ (m + 1) →+* Jet V κ m) := by
  refine Ideal.Quotient.ringHom_ext (RingHom.ext fun p => ?_)
  first
  | rfl
  | simp [jetCoef_mk, jetTrunc]

theorem jetCoef_map {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' V) (hφ : ∀ i, φ i ∈ orig V κ')
    (hφ' : ∀ i, MvPolynomial.map f (φ i) ∈ orig K κ') :
    (jetCoef f κ' m).comp ((jetMap φ hφ : Jet V κ m →ₐ[V] Jet V κ' m) : Jet V κ m →+* Jet V κ' m) =
      ((jetMap (fun i => MvPolynomial.map f (φ i)) hφ' : Jet K κ m →ₐ[K] Jet K κ' m) : Jet K κ m →+* Jet K κ' m).comp
        (jetCoef f κ m) := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_))
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.C a))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.C a)))
    rw [jetCoef_mk]
    simp
  · show jetCoef f κ' m (Ideal.Quotient.mk _ ((MvPolynomial.aeval φ) (MvPolynomial.X i))) =
      Ideal.Quotient.mk _ ((MvPolynomial.aeval fun i => MvPolynomial.map f (φ i))
        (MvPolynomial.map f (MvPolynomial.X i)))
    rw [jetCoef_mk]
    simp

end Ring

end Formalism.MainNotions.ModuliIntegralCharts.H1.JetTr
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpActOf
section
set_option autoImplicit false

namespace Formalism.MainNotions.ModuliIntegralCharts.H1

theorem expActOf_of (hE : LinEigSt) : ExpActOfSt := expActOf_of_eig hE

end Formalism.MainNotions.ModuliIntegralCharts.H1
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.ExpChartJetA
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA

open Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD

variable {R : Type} [CommRing R]

theorem ker_fst_sq : RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ (0 + 1 + 1) = ⊥ := by
  show RingHom.ker (TrivSqZeroExt.fstHom R R R) ^ 2 = ⊥
  rw [sq, eq_bot_iff, Ideal.mul_le]
  intro x hx y hy
  have hx' : x.fst = 0 := by simpa using hx
  have hy' : y.fst = 0 := by simpa using hy
  rw [Ideal.mem_bot]
  ext <;> simp [TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, hx', hy']

def tp {κ : Type} (g : κ → R) : Jet R κ (0 + 1) →ₐ[R] DualNumber R :=
  liftJet (MvPolynomial.aeval fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (by
    apply le_bot_iff.1
    refine (Ideal.pow_right_mono (Ideal.span_le.2 ?_) _).trans (le_of_eq ker_fst_sq)
    rintro _ ⟨q, rfl⟩
    simp)

theorem tp_mk {κ : Type} (g : κ → R) (q : κ) :
    tp g (Ideal.Quotient.mk _ (MvPolynomial.X q)) = TrivSqZeroExt.inr (g q) := by
  show MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (MvPolynomial.X q) = _
  rw [MvPolynomial.aeval_X]

theorem zero_ne_single {κ : Type} (q : κ) : (0 : κ →₀ ℕ) ≠ Finsupp.single q 1 :=
  (Finsupp.single_ne_zero.mpr one_ne_zero).symm

theorem aeval_inr {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (P : MvPolynomial κ R) :
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) P =
      TrivSqZeroExt.inl (AddMonoidAlgebra.coeff P 0) +
        TrivSqZeroExt.inr (∑ q, g q * AddMonoidAlgebra.coeff P (Finsupp.single q 1)) := by
  induction P using MvPolynomial.induction_on with
  | C a => simp [MvPolynomial.coeff_C, zero_ne_single, TrivSqZeroExt.algebraMap_eq_inl]
  | add p q hp hq =>
    rw [map_add (f := _), hp, hq]
    simp only [MvPolynomial.coeff_add, mul_add, Finset.sum_add_distrib, TrivSqZeroExt.inl_add,
      TrivSqZeroExt.inr_add]
    abel
  | mul_X p n hp =>
    have hc : ∀ q, AddMonoidAlgebra.coeff (p * MvPolynomial.X n) (Finsupp.single q 1) =
        if q = n then AddMonoidAlgebra.coeff p 0 else 0 := by
      intro q
      rw [MvPolynomial.coeff_mul_X']
      by_cases h : q = n
      · subst h
        simp
      · rw [if_neg h, if_neg]
        rw [Finsupp.support_single_ne_zero _ one_ne_zero, Finset.mem_singleton]
        exact fun h' => h h'.symm
    have h0 : AddMonoidAlgebra.coeff (p * MvPolynomial.X n) 0 = 0 := by
      rw [MvPolynomial.coeff_mul_X']
      simp
    rw [map_mul, hp, MvPolynomial.aeval_X, h0]
    ext <;> simp [hc, TrivSqZeroExt.fst_mul, TrivSqZeroExt.snd_mul, mul_comm]

private lemma coeff_psTrunc_lemma {κ : Type} [Fintype κ] [DecidableEq κ] (f : MvPowerSeries κ R)
    (e : κ →₀ ℕ) (he : e.degree < 0 + 1 + 1) :
    AddMonoidAlgebra.coeff (psTrunc (0 + 1) f) e = MvPowerSeries.coeff e f := by
  rw [psTrunc_eq, MvPowerSeries.coeff_truncTotal _ he]

theorem tp_psJet {κ : Type} [Fintype κ] [DecidableEq κ] (g : κ → R) (f : MvPowerSeries κ R) :
    tp g (psJet (0 + 1) f) = TrivSqZeroExt.inl (MvPowerSeries.constantCoeff f) +
      TrivSqZeroExt.inr (∑ q, g q * MvPowerSeries.coeff (Finsupp.single q 1) f) := by
  have h1 : tp g (psJet (0 + 1) f) =
      MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (g q) : DualNumber R)) (psTrunc (0 + 1) f) := rfl
  rw [h1, aeval_inr, coeff_psTrunc_lemma f 0 (by simp [Finsupp.degree]),
    MvPowerSeries.coeff_zero_eq_constantCoeff_apply]
  congr 2
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [coeff_psTrunc_lemma f _ (by simp [Finsupp.degree_single])]

theorem jetTan_eq_tp {κ : Type} [DecidableEq κ] (ℓ : κ) :
    (jetTan ℓ : Jet R κ (0 + 1) →ₐ[R] DualNumber R) = tp (fun q => if q = ℓ then 1 else 0) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro i
  show MvPolynomial.aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber R) else 0)
      (MvPolynomial.X i) =
    MvPolynomial.aeval (fun q => (TrivSqZeroExt.inr (if q = ℓ then 1 else 0) : DualNumber R))
      (MvPolynomial.X i)
  rw [MvPolynomial.aeval_X, MvPolynomial.aeval_X]
  by_cases h : i = ℓ
  · (simp only [if_pos h]) <;> rfl
  · simp only [if_neg h, TrivSqZeroExt.inr_zero]

theorem tp_comp_jetMap {κ κ' : Type} [Fintype κ'] [DecidableEq κ'] (h : κ' → R) (a : κ → MvPowerSeries κ' R)
    (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) :
    (tp h).comp (jetMap (m := 0 + 1) (fun p => psTrunc (0 + 1) (a p)) (fun p => psTrunc_mem_orig (0 + 1) (a p) (ha p))) =
      tp (fun p => ∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro p
  have h1 : (jetMap (m := 0 + 1) (fun p => psTrunc (0 + 1) (a p))
      (fun p => psTrunc_mem_orig (0 + 1) (a p) (ha p))) (Ideal.Quotient.mk _ (MvPolynomial.X p)) =
        psJet (0 + 1) (a p) := by
    show (Ideal.Quotient.mk (orig R κ' ^ (0 + 1 + 1)))
      (MvPolynomial.aeval (fun p => psTrunc (0 + 1) (a p)) (MvPolynomial.X p)) = _
    rw [MvPolynomial.aeval_X] <;> rfl
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [h1, tp_psJet, ha p, tp_mk]
  simp

theorem snd_tp_psJet_subst {κ κ' : Type} [Fintype κ] [DecidableEq κ] [Fintype κ'] [DecidableEq κ'] (h : κ' → R)
    (a : κ → MvPowerSeries κ' R) (ha : ∀ p, MvPowerSeries.constantCoeff (a p) = 0) (f : MvPowerSeries κ R) :
    (tp h (psJet (0 + 1) (MvPowerSeries.subst a f))).snd =
      ∑ p, (∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (a p)) *
        MvPowerSeries.coeff (Finsupp.single p 1) f := by
  rw [psJet_subst (0 + 1) a ha f, ← AlgHom.comp_apply, tp_comp_jetMap h a ha, tp_psJet]
  simp

theorem sum_coeff_X {κ : Type} [Fintype κ] [DecidableEq κ] (h : κ → R) (s : κ) :
    ∑ q, h q * MvPowerSeries.coeff (Finsupp.single q 1) (MvPowerSeries.X s : MvPowerSeries κ R) = h s := by
  simp [MvPowerSeries.coeff_X, Finsupp.single_left_inj]

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

theorem lin_unit {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((1 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst (fun q : Fin 1 × Fin d => u q.2)
    (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2) ha (G.F k)
  have hu : MvPowerSeries.subst (fun p : Fin 2 × Fin d => (![0, pt R d 0] : Fin 2 → Pt R 1 d) p.1 p.2)
      (G.F k) = MvPowerSeries.X ((0 : Fin 1), k) := G.unit k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 0 i) = 0 := by
    intro i
    simp
  have inner1 : ∀ i : Fin d, ∑ q : Fin 1 × Fin d, u q.2 *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![0, pt R d 0] : Fin 2 → Pt R 1 d) 1 i) = u i :=
    fun i => sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), i)
  rw [hu, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, zero_mul, Finset.sum_const_zero, zero_add] at key
  rw [← key, tp_psJet]
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add]
  exact sum_coeff_X (fun q : Fin 1 × Fin d => u q.2) ((0 : Fin 1), k)

theorem lin_comm {d : ℕ} (G : FGLaw R d) (u : Fin d → R) (k : Fin d) :
    ∑ j, u j * MvPowerSeries.coeff (Finsupp.single ((0 : Fin 2), j) 1) (G.F k) = u k := by
  classical
  set h : Fin 2 × Fin d → R := fun q => if q.1 = 0 then u q.2 else 0 with hh
  have h_0 : ∀ j, h ((0 : Fin 2), j) = u j := fun j => by simp [hh]
  have h_1 : ∀ j, h ((1 : Fin 2), j) = 0 := fun j => by simp [hh]
  have ha : ∀ p : Fin 2 × Fin d,
      MvPowerSeries.constantCoeff ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) = 0 := by
    rintro ⟨i, j⟩
    fin_cases i <;> simp [pt]
  have key := snd_tp_psJet_subst h
    (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) ha (G.F k)
  have hc : MvPowerSeries.subst
      (fun p : Fin 2 × Fin d => (![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) p.1 p.2) (G.F k) = G.F k :=
    G.comm k
  have inner0 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 0 i) = 0 :=
    fun i => (sum_coeff_X h ((1 : Fin 2), i)).trans (h_1 i)
  have inner1 : ∀ i : Fin d, ∑ q : Fin 2 × Fin d, h q *
      MvPowerSeries.coeff (Finsupp.single q 1) ((![pt R d 1, pt R d 0] : Fin 2 → Pt R 2 d) 1 i) = u i :=
    fun i => (sum_coeff_X h ((0 : Fin 2), i)).trans (h_0 i)
  rw [hc, tp_psJet] at key
  simp only [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inr, zero_add] at key
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fintype.sum_prod_type, Fin.sum_univ_two] at key
  simp only [inner0, inner1, h_0, h_1, zero_mul, Finset.sum_const_zero, zero_add, add_zero] at key
  rw [key]
  exact lin_unit G u k

theorem lin_F {d : ℕ} (G : FGLaw R d) (v w : Fin d → R) (k : Fin d) :
    ∑ p : Fin 2 × Fin d, (![v, w] : Fin 2 → Fin d → R) p.1 p.2 *
      MvPowerSeries.coeff (Finsupp.single p 1) (G.F k) = v k + w k := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons]
  rw [lin_comm G v k, lin_unit G w k]

end Formalism.MainNotions.ModuliIntegralCharts.H1.ExpChartJetA
end
end

-- bundled from Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdSy
section
set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj NumberField
open Formalism.MainNotions.ModuliIntegralCharts.H1.GermFun Formalism.MainNotions.ModuliIntegralCharts.H1.GermD Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ (PS Pt ev pt)

section Alg

variable {S : Type} [CommRing S] (d : ℕ)

abbrev swJ (m : ℕ) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 2 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (![fun j => X ((1 : Fin 2), j), fun j => X ((0 : Fin 2), j)] : Fin 2 → Fin d → MvPolynomial (Fin 2 × Fin d) S)
      p.1 p.2

private theorem jetSubstP_apply_mk {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S)
    (p : MvPolynomial κ S) :
    jetSubstP m φ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) =
      Ideal.Quotient.mk _ (aeval (fun i => φ i - C (MvPolynomial.constantCoeff (φ i))) p) := by
  rfl

private theorem degree_eq_sum_lemma_2 {τ : Type} (e : τ →₀ ℕ) : e.degree = ∑ i ∈ e.support, e i := by
  first
  | rfl
  | simp [Finsupp.degree, Finsupp.sum]

private theorem le_degree_lemma_4 {τ : Type} (e : τ →₀ ℕ) (i : τ) : e i ≤ e.degree := by
  by_cases h : e i = 0
  · rw [h]; exact Nat.zero_le _
  · rw [degree_eq_sum_lemma_2]
    exact Finset.single_le_sum (f := fun j => e j) (fun _ _ => Nat.zero_le _)
      (Finsupp.mem_support_iff.2 h)

private theorem mem_degLE_lemma_6 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (e : τ →₀ ℕ) :
    e ∈ degLE m ↔ e.degree ≤ m := by
  unfold degLE
  rw [Finset.mem_filter, Finset.mem_image]
  constructor
  · rintro ⟨_, h⟩
    rw [degree_eq_sum_lemma_2]
    exact h
  · intro h
    refine ⟨⟨fun i => ⟨e i, by have := le_degree_lemma_4 e i; omega⟩, Finset.mem_univ _, ?_⟩, ?_⟩
    · ext i
      simp
    · rw [degree_eq_sum_lemma_2] at h
      exact h

private theorem coeff_psTrunc_lemma_7 {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ)
    (f : MvPowerSeries τ S) (e : τ →₀ ℕ) :
    AddMonoidAlgebra.coeff (psTrunc m f) e = if e.degree ≤ m then MvPowerSeries.coeff e f else 0 := by
  rw [psTrunc, coeff_sum]
  simp only [coeff_monomial, Finset.sum_ite_eq', mem_degLE_lemma_6]

theorem mk_psTrunc_X {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) (q : τ) :
    (Ideal.Quotient.mk (orig S τ ^ (m + 1)) (psTrunc m (MvPowerSeries.X q))) = Ideal.Quotient.mk _ (X q) := by
  have hdeg : (Finsupp.single q 1).degree = 1 := by
    rw [degree_eq_sum_lemma_2, Finsupp.support_single_ne_zero _ one_ne_zero, Finset.sum_singleton,
      Finsupp.single_eq_same]
  have hs : psTrunc m (MvPowerSeries.X q : MvPowerSeries τ S) = if 1 ≤ m then X q else 0 := by
    ext e
    rw [coeff_psTrunc_lemma_7, MvPowerSeries.coeff_X]
    by_cases h2 : e = Finsupp.single q 1
    · subst h2
      rw [hdeg]
      by_cases h3 : 1 ≤ m
      · simp [h3, MvPolynomial.coeff_X]
      · simp [h3]
    · have h4 : AddMonoidAlgebra.coeff (X q : MvPolynomial τ S) e = 0 := by
        rw [MvPolynomial.coeff_X']
        exact if_neg (Ne.symm h2)
      split_ifs <;> simp [h4, h2]
  rw [Ideal.Quotient.eq, hs]
  split_ifs with h
  · rw [sub_self]
    exact Ideal.zero_mem _
  · have hm : m = 0 := by omega
    subst hm
    rw [zero_sub, zero_add, pow_one]
    exact Ideal.neg_mem_iff _ |>.2 (Ideal.subset_span ⟨q, rfl⟩)

private theorem jetMap_mk_lemma_13 {κ κ' : Type} (m : ℕ) (φ : κ → MvPolynomial κ' S) (hφ : ∀ i, φ i ∈ orig S κ')
    (p : MvPolynomial κ S) :
    jetMap (m := m) φ hφ (Ideal.Quotient.mk (orig S κ ^ (m + 1)) p) = Ideal.Quotient.mk _ (aeval φ p) := by
  rfl

end Alg

section Axes

variable {S : Type} [CommRing S] (d : ℕ)

abbrev axJ (m : ℕ) (b : Bool) : Jet S (Fin 2 × Fin d) m →ₐ[S] Jet S (Fin 1 × Fin d) m :=
  jetSubstP m fun p : Fin 2 × Fin d =>
    (if b then ![fun _ => 0, fun j => X ((0 : Fin 1), j)] else ![fun j => X ((0 : Fin 1), j), fun _ => 0] :
      Fin 2 → Fin d → MvPolynomial (Fin 1 × Fin d) S) p.1 p.2

def axV (b : Bool) (k : Fin 2) (j : Fin d) : MvPolynomial (Fin 1 × Fin d) S :=
  if (k = 1) = b then X ((0 : Fin 1), j) else 0

theorem axJ_X (m : ℕ) (b : Bool) (k : Fin 2) (j : Fin d) :
    axJ (S := S) d m b (Ideal.Quotient.mk _ (X (k, j))) = Ideal.Quotient.mk _ (axV d b k j) := by
  rw [jetSubstP_apply_mk, aeval_X]
  cases b <;> fin_cases k <;> simp [axV]

theorem psTrunc_zero {τ : Type} [Fintype τ] [DecidableEq τ] (m : ℕ) :
    psTrunc m (0 : MvPowerSeries τ S) = 0 := by
  simp [psTrunc]

theorem psJet_ev_ax (m : ℕ) (f : PS S 2 d) (b : Bool) :
    psJet m (ev (n := 1) (if b then ![0, pt S d 0] else ![pt S d 0, 0]) f) = axJ d m b (psJet m f) := by
  have ha : ∀ p : Fin 2 × Fin d, MvPowerSeries.constantCoeff
      ((fun p : Fin 2 × Fin d => ((if b then ![0, pt S d 0] else ![pt S d 0, 0]) : Fin 2 → Pt S 1 d) p.1 p.2) p) = 0 := by
    rintro ⟨i, j⟩
    cases b <;> fin_cases i <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt]
  unfold ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.ev
  rw [psJet_subst m _ ha f]
  refine DFunLike.congr_fun ?_ (psJet m f)
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  rintro ⟨k, j⟩
  simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
  rw [axJ_X, jetMap_mk_lemma_13, aeval_X]
  cases b <;> fin_cases k <;> simp [ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ.pt, mk_psTrunc_X, axV, psTrunc_zero]

end Axes

section Frame

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {X0 : Scheme.{0}} (t : SAB H X0)
variable {S : Type} [CommRing S] (x0 : Sp S ⟶ X0) (d : ℕ) (x : ∀ m, jOG x0 d m 1 ⟶ t.G)

theorem scaleGenG_scaleGenG {Y : Scheme.{0}} {K : Type} [Fintype K] (φ : K → (Y ⟶ t.G.left)) (ε : K → ℤ)
    (v w : Γ(Y, ⊤)ˣ) (g : LB.Gen (LB.LinComb t.PP.L φ ε)) :
    scaleGenG t φ ε v (scaleGenG t φ ε w g) = scaleGenG t φ ε (v * w) g := by
  simp only [scaleGenG, Units.val_mul, map_mul, mul_assoc]

theorem unitΓ_mul {A : Type} [CommRing A] (a b : Aˣ) : unitΓ (a * b) = unitΓ a * unitΓ b := by
  exact map_mul (Units.map (toΓ A).toMonoidHom) a b

theorem unitΓ_one {A : Type} [CommRing A] : unitΓ (1 : Aˣ) = 1 := by
  exact map_one (Units.map (toΓ A).toMonoidHom)

end Frame

end Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdSy
end
end

