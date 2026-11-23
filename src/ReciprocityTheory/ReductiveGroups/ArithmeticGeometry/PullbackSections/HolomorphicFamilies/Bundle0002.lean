module

public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetA
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.Bundle0002
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ValAtLem
public import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FBIdJet
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.Bundle0001

@[expose] public section

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.HolJetB
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections

open AlgebraicGeometry CategoryTheory Opposite Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.TB.ValAt
open scoped ContDiff

section JetOf

variable {g : ℕ}

def jetOf (m : ℕ) (θ : (Fin g → ℂ) → ℂ) : Jet ℂ (Fin 1 × Fin g) m := psJet m (tay θ 0)

theorem psJet_add' {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f h : MvPowerSeries ι ℂ) :
    psJet m (f + h) = psJet m f + psJet m h := by
  simp only [psJet, psTrunc, map_add (f := _), Finset.sum_add_distrib]

theorem jetOf_mul (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) :
    jetOf m (f * h) = jetOf m f * jetOf m h := by
  rw [jetOf, (TM.taylor_multiplication.1 g f h hf hh).1, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psJet_mul]
  rfl

theorem jetOf_add (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hf : ContDiffAt ℂ ω f 0) (hh : ContDiffAt ℂ ω h 0) :
    jetOf m (f + h) = jetOf m f + jetOf m h := by
  rw [jetOf, (TM.taylor_multiplication.1 g f h hf hh).2, psJet_add']
  rfl

theorem jetOf_const (m : ℕ) (c : ℂ) :
    jetOf m (fun _ : Fin g → ℂ => c) = algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m) c := by
  rw [jetOf, TM.taylor_multiplication.2.1 g c]
  have h : (MvPowerSeries.C c : MvPowerSeries (Fin 1 × Fin g) ℂ) =
      ((MvPolynomial.C c : MvPolynomial (Fin 1 × Fin g) ℂ) : MvPowerSeries (Fin 1 × Fin g) ℂ) := by simp
  rw [h, psJet, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.mk_trunc_coe, ← MvPolynomial.algebraMap_eq]
  rfl

theorem jetOf_congr (m : ℕ) {f h : (Fin g → ℂ) → ℂ} (hfh : f =ᶠ[nhds 0] h) : jetOf m f = jetOf m h := by
  rw [jetOf, jetOf, TM.taylor_multiplication.2.2 g f h hfh]

theorem jetAug_psJet {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι ℂ) :
    (jetAug : Jet ℂ ι m →ₐ[ℂ] ℂ) (psJet m f) = MvPowerSeries.constantCoeff f := by
  rw [psJet, Formalism.MainNotions.ModuliIntegralCharts.H1.FBIdJet.psTrunc_eq]
  show MvPolynomial.aeval (fun _ => (0 : ℂ)) _ = _
  rw [MvPolynomial.aeval_zero', Algebra.algebraMap_self, RingHom.id_apply, MvPolynomial.constantCoeff_eq,
    MvPowerSeries.coeff_truncTotal _ (by simp), MvPowerSeries.coeff_zero_eq_constantCoeff_apply]

theorem jetAug_jetOf (m : ℕ) (θ : (Fin g → ℂ) → ℂ) : (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ) (jetOf m θ) = θ 0 := by
  rw [jetOf, jetAug_psJet, constantCoeff_tay]
  show lD θ 0 (Multiset.toList 0) = θ 0
  rw [Multiset.toList_zero]
  exact iteratedFDeriv_zero_apply _

theorem jetTrunc_psJet {ι : Type} [Fintype ι] [DecidableEq ι] (m : ℕ) (f : MvPowerSeries ι ℂ) :
    (jetTrunc : Jet ℂ ι (m + 1) →ₐ[ℂ] Jet ℂ ι m) (psJet (m + 1) f) = psJet m f := by
  rw [psJet, psJet]
  show Ideal.Quotient.mk _ (psTrunc (m + 1) f) = Ideal.Quotient.mk _ (psTrunc m f)
  rw [Ideal.Quotient.eq]
  exact Formalism.MainNotions.ModuliIntegralCharts.H1.GermD.psTrunc_succ_sub f

theorem jetTrunc_jetOf (m : ℕ) (θ : (Fin g → ℂ) → ℂ) :
    (jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) (jetOf (m + 1) θ) = jetOf m θ :=
  jetTrunc_psJet m _

theorem ne_zero_of_isUnit_jetOf (m : ℕ) {θ : (Fin g → ℂ) → ℂ} (h : IsUnit (jetOf m θ)) : θ 0 ≠ 0 := by
  have := h.map (jetAug : Jet ℂ (Fin 1 × Fin g) m →ₐ[ℂ] ℂ)
  rw [jetAug_jetOf] at this
  exact this.ne_zero

end JetOf

section HolJet

variable {g : ℕ} {Y : Scheme.{0}}

abbrev cpt : Sp ℂ := IsLocalRing.closedPoint (CommRingCat.of ℂ)

def IsHolFam (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) : Prop :=
  ∀ (U : Y.Opens) (f : Γ(Y, U)), IsOpen {z | ⊤ ≤ e z ⁻¹ᵁ U} ∧
    DifferentiableOn ℂ (fun z => valAt' (e z) U f) {z | ⊤ ≤ e z ⁻¹ᵁ U}

variable (e : (Fin g → ℂ) → (Sp ℂ ⟶ Y)) (hol : IsHolFam e)

set_option backward.isDefEq.respectTransparency false in
theorem top_le_of_mem {x : Sp ℂ ⟶ Y} {U : Y.Opens} (h : x cpt ∈ U) : ⊤ ≤ x ⁻¹ᵁ U :=
  (Scheme.preimage_eq_top_of_closedPoint_mem x h).ge

include hol in
theorem eventually_mem {U : Y.Opens} (hU : e 0 cpt ∈ U) : ∀ᶠ z in nhds 0, ⊤ ≤ e z ⁻¹ᵁ U :=
  (hol U 0).1.mem_nhds (top_le_of_mem hU)

include hol in
theorem contDiffAt_val {U : Y.Opens} (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) :
    ContDiffAt ℂ ω (fun z => valAt' (e z) U f) 0 :=
  (analyticAt_val e hol U f 0 (top_le_of_mem hU)).contDiffAt

def jetRingHom (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) : Γ(Y, U) →+* Jet ℂ (Fin 1 × Fin g) m where
  toFun f := jetOf m (fun z => valAt' (e z) U f)
  map_one' := by
    rw [← map_one (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)), ← jetOf_const]
    refine jetOf_congr m ((eventually_mem e hol hU).mono fun z hz => ?_)
    exact valAt'_one _ _ hz
  map_mul' f h := by
    rw [← jetOf_mul m (contDiffAt_val e hol hU f) (contDiffAt_val e hol hU h)]
    congr 1
    funext z
    exact valAt'_mul _ _ f h
  map_zero' := by
    rw [← map_zero (algebraMap ℂ (Jet ℂ (Fin 1 × Fin g) m)), ← jetOf_const]
    congr 1
    funext z
    have := valAt'_sub (e z) U 0 0
    rw [sub_self, sub_self] at this
    exact this
  map_add' f h := by
    rw [← jetOf_add m (contDiffAt_val e hol hU f) (contDiffAt_val e hol hU h)]
    congr 1
    funext z
    exact valAt'_add _ _ f h

def jetψ (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) :
    Γ(Y, U) ⟶ CommRingCat.of (Jet ℂ (Fin 1 × Fin g) m) :=
  CommRingCat.ofHom (jetRingHom e hol m U hU)

theorem jetψ_apply (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) :
    jetψ e hol m U hU f = jetOf m (fun z => valAt' (e z) U f) := rfl

theorem jetψ_res (m : ℕ) (U V : Y.Opens) (hU : e 0 cpt ∈ U) (hV : e 0 cpt ∈ V) (h : V ≤ U) :
    Y.presheaf.map (homOfLE h).op ≫ jetψ e hol m V hV = jetψ e hol m U hU := by
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  refine jetOf_congr m ((eventually_mem e hol hV).mono fun z hz => ?_)
  exact valAt'_res _ h hz f

theorem jetψ_loc (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (f : Γ(Y, U)) (hf : IsUnit (jetψ e hol m U hU f)) :
    e 0 cpt ∈ Y.basicOpen f := by
  rw [jetψ_apply] at hf
  exact (valAt'_ne_zero_iff (e 0) U (top_le_of_mem hU) f cpt).mp (ne_zero_of_isUnit_jetOf m hf)

def jetPt (m : ℕ) : Sp (Jet ℂ (Fin 1 × Fin g) m) ⟶ Y :=
  nbhdPt (y₀ := e 0 cpt) (jetψ e hol m) (jetψ_res e hol m)

theorem jetPt_closedPoint (m : ℕ) : jetPt e hol m (IsLocalRing.closedPoint _) = e 0 cpt :=
  nbhdPt_closedPoint _ _ (jetψ_loc e hol m)

theorem jetPt_appLE (m : ℕ) (U : Y.Opens) (hU : e 0 cpt ∈ U) (h : ⊤ ≤ jetPt e hol m ⁻¹ᵁ U) :
    (jetPt e hol m).appLE U ⊤ h = jetψ e hol m U hU ≫ (Scheme.ΓSpecIso _).inv :=
  nbhdPt_appLE _ _ (jetψ_loc e hol m) U hU h

theorem jetPt_trunc (m : ℕ) :
    spMap ((jetTrunc : Jet ℂ (Fin 1 × Fin g) (m + 1) →ₐ[ℂ] Jet ℂ (Fin 1 × Fin g) m) : _ →+* _) ≫
      jetPt e hol (m + 1) = jetPt e hol m := by
  unfold jetPt
  rw [spMap, spec_comp_nbhdPt]
  refine nbhdPt_congr _ _ fun U hU => ?_
  ext f
  rw [CommRingCat.comp_apply, jetψ_apply, jetψ_apply]
  exact jetTrunc_jetOf m _

end HolJet

end ReciprocityTheory.ChartRestriction.G.PullbackSections
end
end

-- bundled from ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.SubstTanSnd
section
set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD

open MvPolynomial CategoryTheory Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G

attribute [local instance] Over.cartesianMonoidalCategory

variable {V : Type} [CommRing V] {d : ℕ}

abbrev zk (k : Fin d) : Jet V (Fin 1 × Fin d) 1 := Ideal.Quotient.mk _ (X ((0 : Fin 1), k))

theorem fst_jetTan (k : Fin d) (w : Jet V (Fin 1 × Fin d) 1) :
    (jetTan (R := V) (m := 0) ((0 : Fin 1), k) w).fst = jetAug w :=
  DFunLike.congr_fun (Formalism.L2.Pj.SaturatedCharts.fst_comp_jetTan (V := V) ((0 : Fin 1), k)) w

theorem jetTan_mk {ι : Type} [DecidableEq ι] (ℓ : ι) (q : MvPolynomial ι V) :
    jetTan (R := V) (m := 0) ℓ (Ideal.Quotient.mk _ q) =
      aeval (fun i => if i = ℓ then (DualNumber.eps : DualNumber V) else 0) q := rfl

theorem jetAug_mk {ι : Type} (q : MvPolynomial ι V) :
    jetAug (R := V) (m := 1) (Ideal.Quotient.mk _ q) = constantCoeff q := by
  show aeval (fun _ => (0 : V)) q = constantCoeff q
  exact RingHom.congr_fun MvPolynomial.eval_zero' q

private lemma snd_tan_lemma (c x : V) : (algebraMap V (DualNumber V) c + x • DualNumber.eps).snd = x := by
  rw [TrivSqZeroExt.snd_add, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, mul_one]
  have h0 : (algebraMap V (DualNumber V) c).snd = 0 := by
    first | rfl | simp [TrivSqZeroExt.algebraMap_eq_inl] | exact TrivSqZeroExt.snd_inl _ _
  rw [h0, zero_add]

theorem snd_lin (φ : Jet V (Fin 1 × Fin d) 1 →ₐ[V] DualNumber V) (hφ : ∀ w, (φ w).fst = jetAug w)
    (w : Jet V (Fin 1 × Fin d) 1) :
    (φ w).snd = ∑ k, (φ (zk k)).snd * (jetTan (R := V) (m := 0) ((0 : Fin 1), k) w).snd := by
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w
  induction q using MvPolynomial.induction_on
  next a =>
    have h1 : (Ideal.Quotient.mk _ (C a) : Jet V (Fin 1 × Fin d) 1) = algebraMap V _ a := rfl
    have h2 : (φ (Ideal.Quotient.mk _ (C a))).snd = 0 := by
      rw [h1, AlgHom.commutes]
      first | rfl | simp [TrivSqZeroExt.algebraMap_eq_inl] | exact TrivSqZeroExt.snd_inl _ _
    rw [h2]
    have hne : ∀ c : Fin d, (0 : Fin 1 × Fin d →₀ ℕ) ≠ Finsupp.single ((0 : Fin 1), c) 1 :=
      fun c => (Finsupp.single_ne_zero.2 one_ne_zero).symm
    symm
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [jetTan_mk, aeval_tan, snd_tan_lemma, MvPolynomial.coeff_C, if_neg (hne c), mul_zero]
  next p q hp hq =>
    simp only [map_add (f := _), TrivSqZeroExt.snd_add, hp, hq, mul_add, Finset.sum_add_distrib]
  next p n _ =>
    obtain ⟨a, b⟩ := n
    obtain rfl : a = 0 := Subsingleton.elim _ _
    have hz : ∀ c : Fin d, (φ (zk c)).fst = 0 := fun c => by
      rw [hφ, zk, jetAug_mk, MvPolynomial.constantCoeff_X]
    have hp : (φ (Ideal.Quotient.mk _ p)).fst = constantCoeff p := by rw [hφ, jetAug_mk]
    have hT : ∀ c : Fin d, (jetTan (R := V) (m := 0) ((0 : Fin 1), c)
        (Ideal.Quotient.mk _ (p * X ((0 : Fin 1), b)))).snd = if b = c then constantCoeff p else 0 := by
      intro c
      have hf : (jetTan (R := V) (m := 0) ((0 : Fin 1), c) (Ideal.Quotient.mk _ p)).fst = constantCoeff p := by
        rw [fst_jetTan, jetAug_mk]
      rw [map_mul, map_mul, TrivSqZeroExt.snd_mul, hf, jetTan_mk (ℓ := ((0 : Fin 1), c)) (X _), aeval_X]
      by_cases h : b = c
      · subst h; simp
      · have h' : ((0 : Fin 1), b) ≠ ((0 : Fin 1), c) := fun e => h (congrArg Prod.snd e)
        simp [h, h']
    have hm : (Ideal.Quotient.mk _ (p * X ((0 : Fin 1), b)) : Jet V (Fin 1 × Fin d) 1) =
        Ideal.Quotient.mk _ p * zk b := map_mul _ _ _
    rw [hm, map_mul, TrivSqZeroExt.snd_mul, hp, hz, ← hm]
    simp only [hT, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp [smul_eq_mul, mul_comm]

theorem substTan_fst (f : Fin d → MvPowerSeries (Fin 1 × Fin d) V) (j : Fin d) (w : Jet V (Fin 1 × Fin d) 1) :
    ((jetTan (R := V) (m := 0) ((0 : Fin 1), j)).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) w).fst = jetAug w := by
  rw [AlgHom.comp_apply, fst_jetTan]
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective w
  have h : (jetAug : Jet V (Fin 1 × Fin d) 1 →ₐ[V] V).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) = jetAug := by
    apply Ideal.Quotient.algHom_ext
    apply MvPolynomial.algHom_ext
    intro i
    simp only [AlgHom.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    show jetAug (Ideal.Quotient.mk _ (aeval _ (X i))) = _
    rw [aeval_X, jetAug_mk, jetAug_mk]
    simp
  exact (AlgHom.comp_apply _ _ _).symm.trans (DFunLike.congr_fun h _)

theorem substTan_snd (f : Fin d → MvPowerSeries (Fin 1 × Fin d) V) (j m : Fin d) :
    ((jetTan (R := V) (m := 0) ((0 : Fin 1), j)).comp
      (jetSubstP 1 fun p : Fin 1 × Fin d => psTrunc 1 (f p.2)) (zk m)).snd =
      MvPowerSeries.coeff (Finsupp.single ((0 : Fin 1), j) 1) (f m) := by
  rw [AlgHom.comp_apply]
  show (jetTan (R := V) (m := 0) ((0 : Fin 1), j) (Ideal.Quotient.mk _ (aeval _ (X ((0 : Fin 1), m))))).snd = _
  rw [aeval_X, jetTan_mk, aeval_tan]
  have hne : Finsupp.single ((0 : Fin 1), j) 1 ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  simp [MvPolynomial.coeff_C, hne.symm, coeff_psTrunc 1 _ _ (single_mem_degLE _)]

end ReciprocityTheory.ChartRestriction.G.PullbackSections.Pf.EigD
end
end

