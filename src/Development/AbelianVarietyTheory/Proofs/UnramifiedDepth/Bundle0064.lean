module

public import Mathlib
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
public import ReciprocityTheory.DualLattices.Bundle0028
public import ReciprocityTheory.DualLattices.Bundle0014
public import ReciprocityTheory.DualLattices.Bundle0035
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.LePreimageOfNil
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.Clauses
public import ReciprocityTheory.DualLattices.Bundle0031
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.Biextensions.GenericFiberCubeInclusion
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.Bundle0002
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.IsEigBasisIff
public import ReciprocityTheory.DualLattices.Bundle0020
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0063
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0015
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0012
public import Formalism.LocalToGlobal.CharacterGerms.Bundle0011
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartF
public import Development.AbelianVarietyTheory.Definitions.TeichmullerDepth.HasTeich
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0044
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0052
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsPureTypicalCurveWithIntegralTangent
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0057
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0060
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0047
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0042
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0056
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0058
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0061
public import Formalism.LocalToGlobal.ProjectiveLattices.PlaceBelow
public import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.Bundle0032

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.AbelianPartCokernelLengthLe
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem place_mul_bar {p : ℕ} [Fact p.Prime] {OE : Type} [CommRing OE] [StarRing OE] (w : Place p OE)
    (hinv : ∀ x, sig p OE (sig p OE x) = x) : w.e * w.bar = 0 := by
  have hb : w.bar * w.bar = w.bar := by
    unfold Place.bar
    rw [← map_mul, w.idem]
  rcases w.prim (w.e * w.bar) (by rw [_root_.mul_mul_mul_comm, w.idem, hb])
    (by rw [mul_right_comm, w.idem]) with h | h
  · exact h
  · exfalso
    apply w.split
    have h2 := congrArg (sig p OE) h
    unfold Place.bar at h h2
    rw [map_mul, hinv, mul_comm, h] at h2
    exact h2.symm

theorem abelian_coker_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp), H.P = 0 → H.PL = 0 → ∀ (w : Place p OE) (t : Fin w.n ≃ Emb (O := O) w.e) (rm : ℕ), (∀ τ ∈ Emb (O := O) w.bar, eigDim C (fun a : OE => H.ρL (1 ⊗ₜ[ℤ] a)) ((algebraMap O C).comp τ) ≤ rm) → ∃ cw : NNReal, HasLen v O (htCoker H w.e w.bar) cw ∧ (v (algebraMap O C (p : O)) : ℝ) ^ (((w.n : ℝ) * rm) / ((p : ℝ) - 1)) ≤ cw := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H hP hPL w t rm hrm
  obtain ⟨-, -, hstar⟩ := GlobalTheory.ChF.embeddings_idempotents_conjugation p C v O hv OE
  have hsig : ∀ x, sig p OE x = sigE p OE x := fun x => by
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul a b => rfl
    | add a b ha hb => rw [map_add (f := _), map_add (f := _), ha, hb]
  have hinv : ∀ x, sig p OE (sig p OE x) = x := fun x => by rw [hsig, hsig, hS.invol]
  have h0 : w.e * w.bar = 0 := place_mul_bar w hinv
  have he := w.idem
  have hbar : sigE p OE w.e = w.bar := (hsig _).symm
  have hbar' : sigE p OE w.bar = w.e := by rw [← hbar, hS.invol]
  have hb : w.bar * w.bar = w.bar := by rw [← hbar, ← map_mul, w.idem]
  let c : OE →+* OE := ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom
  have hcc : ∀ τ : OE →+* O, (τ.comp c).comp c = τ := fun τ => by
    ext a
    simp [c]
  let s : Emb (O := O) w.e ≃ Emb (O := O) w.bar :=
    { toFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.bar).1, hbar', this]⟩
      invFun := fun τ => ⟨τ.1.comp c, by
        have := τ.2
        simp only [Emb, Set.mem_setOf_eq] at this ⊢
        rw [(hstar τ.1 w.e).1, hbar, this]⟩
      left_inv := fun τ => Subtype.ext (hcc τ.1)
      right_inv := fun τ => Subtype.ext (hcc τ.1) }
  have hd := GlobalTheory.T.range_idempotent_rank_sum_eigenspaceDim p C v O hv OE g H.ρL w.bar hb w.n (t.trans s)
  obtain ⟨cw, hcw⟩ : ∃ x, HasLen v O (htCoker H w.e w.bar) x :=
    lenEx C v O hv g H.Ht (H.ρL w.e) ((H.ρ w.bar).map (algebraMap ℤ_[p] O))
  refine ⟨cw, hcw, ?_⟩
  have hav := lengthDegree_abelianVariety p g C v O _ _ cp hS H 3 ![w.e, w.bar, 1 - w.e - w.bar] (Equiv.swap 0 1)
    (by
      intro i j
      fin_cases i <;> fin_cases j <;> simp <;>
        first
        | exact he
        | exact hb
        | linear_combination h0
        | linear_combination -he - h0
        | linear_combination -hb - h0
        | linear_combination he + hb + 2 * h0)
    (by
      intro i
      fin_cases i
      · simpa using hbar
      · simpa using hbar'
      · have : (Equiv.swap (0 : Fin 3) 1) 2 = 2 := by decide
        simp only [Fin.reduceFinMk, this, Matrix.cons_val, map_sub, map_one, hbar, hbar']
        ring)
    (by simp [Fin.sum_univ_three, hP]) (by simp [hP])
    (by simp [Fin.sum_univ_three, hPL]) (by simp [hPL])
    0 (by decide) _ hd cw hcw
  refine le_trans ?_ hav
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (Fact.out : p.Prime).one_lt
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · refine div_le_div_of_nonneg_right ?_ (by linarith)
    have := Finset.sum_le_card_nsmul Finset.univ _ rm (fun j _ => hrm _ ((t.trans s) j).2)
    simp only [Finset.card_univ, Fintype.card_fin, smul_eq_mul] at this
    exact_mod_cast this

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.CartHypOfIntegralGaugedFormalGroupLaw
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem cartHyp_of_rlaw : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (I : Fin 2 → Type) [∀ g, Fintype (I g)] (κ : Type) [Fintype κ] (X : RawChart C d I κ), RLaw X V → HasProj X V → (∀ g, HasTeich X V g) → ∀ g, X.CartHyp V g := by
  intro C _ V d _ I _ κ _ X hL hP hT g
  have hlg0 : ∀ i, MvPowerSeries.constantCoeff (X.lg i) = 0 := fun i => by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hL.lin i 0 (by simp),
      MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.constantCoeff_X]
  have hh := hL.axes 0
  refine
    { zero := X.zero_mem hlg0 hh V g
      add := X.add_mem V g (GlobalTheory.T.addCurveStable_of_integralGaugedFormalGroupLaw C V d I κ X hL) hL.uint
      neg := X.neg_mem V g hL.odd
      teich := X.teich_mem V g
      Vm := X.V_mem V g
      Fm := _root_.GlobalTheory.RowLaw.FrobCurve.frob_mem_tySet C V d I κ X hL g
      sumV := _root_.GlobalTheory.RowLaw.ShiftSum.sumV_mem_tySet C V d I κ X hL g
      t2 := X.val_nonneg_leading_coeff_of_mem_tySet V g hL.lin hh ?_ (GlobalTheory.T.integral_gaugeBilinearTerm_of_type_ne C V d I κ X hL g (hT g))
      t3 := X.const_mem_type_set_of_nonneg hlg0 hh V g
      t4 := _root_.GlobalTheory.RowLaw.exists_pure_typical C V d I κ X hL hP g (hT g) }
  obtain ⟨w, hw, huw⟩ := hL.sat g
  refine ⟨w, hw, fun c c' => ?_⟩
  split_ifs with h
  · exact (huw c c').1 h
  · exact (huw c c').2 h

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsIsChOfTors
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem apply_eq_zero_of_killed {R : Type} [CommRing R] {d : ℕ} {F : Fin d → PS R 2 d} {N : ℕ}
    {φ : PS R 1 d →ₐ[R] R} (h : Killed F N φ) {f : PS R 1 d}
    (hf : f ∈ Ideal.span (Set.range (mulF F N))) : φ f = 0 := by
  have hle : Ideal.span (Set.range (mulF F N)) ≤ RingHom.ker φ := by
    rw [Ideal.span_le]
    rintro _ ⟨j, rfl⟩
    exact h j
  exact hle hf

private theorem killed_pow_mono {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) (p : ℕ) {m n : ℕ}
    (hmn : m ≤ n) {φ : PS R 1 d →ₐ[R] R} (h : Killed F.F (p ^ m) φ) : Killed F.F (p ^ n) φ := by
  intro j
  apply apply_eq_zero_of_killed h
  have hn : p ^ n = p ^ (n - m) * p ^ m := by rw [← pow_add, Nat.sub_add_cancel hmn]
  rw [hn]
  exact (_root_.GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow R d F).2.2.1 _ _ (Ideal.subset_span ⟨j, rfl⟩)

private theorem addOf_pt {R : Type} [CommRing R] {d : ℕ} (F : Fin d → PS R 2 d) :
    addOf F (pt R (n := 2) d 0) (pt R (n := 2) d 1) = F := by
  funext i
  unfold addOf ev
  have h : (fun q : Fin 2 × Fin d => (![pt R (n := 2) d 0, pt R (n := 2) d 1] : Fin 2 → Pt R 2 d) q.1 q.2)
      = MvPowerSeries.X := by
    funext ⟨a, b⟩
    fin_cases a <;> rfl
  rw [h, MvPowerSeries.subst_self]
  rfl

private theorem hasSubst_law {R : Type} [CommRing R] {d : ℕ} (F : FGLaw R d) :
    MvPowerSeries.HasSubst (fun q : Fin 1 × Fin d => (![F.F] : Fin 1 → Pt R 2 d) q.1 q.2) := by
  apply MvPowerSeries.hasSubst_of_constantCoeff_zero
  rintro ⟨a, b⟩
  fin_cases a
  exact F.const b

theorem exists_isCh_of_tors : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] (d : ℕ) (F : FGLaw O d), FH p F.F → ∀ (κ : (PS O 1 d →ₐ[O] O) → C), (∀ φ φ' ψ, Tors p F.F φ → Tors p F.F φ' → IsSum F.F φ φ' ψ → κ ψ = κ φ * κ φ') → (∀ φ, (∀ f, φ f = MvPowerSeries.constantCoeff f) → κ φ = 1) → ∃ u : PS O 1 d, IsCh F.F u ∧ ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
  intro p _ C _ _ _ v O _ _ hv _ _ d F hFH κ hmul hone
  have hinj : Function.Injective (algebraMap O C) := hv.hom_inj
  choose w hw using fun k : ℕ => _root_.GlobalTheory.character_on_torsion_points_eq_series p C v O hv d F hFH k κ
    (fun φ φ' ψ h h' hs => hmul φ φ' ψ ⟨k, h⟩ ⟨k, h'⟩ hs) hone
  obtain ⟨hsep, hsepT⟩ := _root_.GlobalTheory.ChF.mem_span_mulF_of_killed_and_eq_zero_of_tors p C v O hv d F hFH
  have hsame : ∀ {m n : ℕ}, m ≤ n → ∀ φ, Killed F.F (p ^ m) φ → φ (w m) = φ (w n) := by
    intro m n hmn φ h
    apply hinj
    rw [hw m φ h, hw n φ (killed_pow_mono F p hmn h)]
  set J : Ideal (PS O 1 d) := (Ideal.span {(p : O)}).map (MvPowerSeries.C : O →+* PS O 1 d) ⊔
    Ideal.span (Set.range (MvPowerSeries.X : Fin 1 × Fin d → PS O 1 d)) with hJ
  have hcomp : IsAdicComplete J (PS O 1 d) :=
    (mem_sup_span_X_pow_iff_and_isAdicComplete O (Ideal.span {(p : O)}) (Fin 1 × Fin d)).2 inferInstance
  have hcauchy : ∀ {m n : ℕ}, m ≤ n → w m ≡ w n [SMOD (J ^ m • ⊤ : Submodule (PS O 1 d) (PS O 1 d))] := by
    intro m n hmn
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top]
    have h1 := hsep m (w m - w n) (fun φ h => by rw [map_sub, hsame hmn φ h, sub_self])
    have h2 : Ideal.span (Set.range (mulF F.F (p ^ m))) ≤ J ^ (m + 1) := by
      rw [Ideal.span_le]
      rintro _ ⟨j, rfl⟩
      exact (_root_.GlobalTheory.ChF.lin_mulF_and_comp_and_span_le_and_mem_pow O d F).2.2.2 p m j
    exact Ideal.pow_le_pow_right (Nat.le_succ m) (h2 h1)
  obtain ⟨u, hu⟩ := hcomp.toIsPrecomplete.prec hcauchy
  have hval : ∀ φ, Tors p F.F φ → algebraMap O C (φ u) = κ φ := by
    rintro φ ⟨k, hk⟩
    rw [← hw k φ hk]
    congr 1
    have hH : IsHausdorff (Ideal.span {(p : O)}) O := inferInstance
    rw [← sub_eq_zero]
    apply hH.haus
    intro n
    rw [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow]
    obtain ⟨N, hN⟩ := (_root_.GlobalTheory.ChF.formalDisc_points_integers p C v O hv (Fin 1 × Fin d)).2.2 φ n
    have h1 := hu (max N k)
    rw [SModEq.sub_mem, smul_eq_mul, Ideal.mul_top] at h1
    have h2 := hN _ (Ideal.pow_le_pow_right (le_max_left N k) h1)
    rw [map_sub, ← hsame (le_max_right N k) φ hk] at h2
    rw [← neg_sub]
    exact neg_mem h2
  obtain ⟨inst, hinst⟩ := GlobalTheory.T.exists_addCommMonoid_algHom_powerSeries_fgLaw p C v O hv d F
  letI := inst
  obtain ⟨hsum, hzero, hkill⟩ := hinst
  refine ⟨u, ⟨?_, ?_⟩, hval⟩
  · apply hinj
    rw [← hzero u, hval _ ⟨0, (hkill _ _).1 (smul_zero _)⟩, hone _ hzero, map_one]
  · rw [addOf_pt, ← sub_eq_zero]
    apply GlobalTheory.T.eq_zero_of_forall_pair_points_valuationIntegers p C v O hv d (Tors p F.F) hsepT
    intro Φ φ φ' h0 h1 hφ hφ'
    let ψ : PS O 1 d →ₐ[O] O := Φ.comp (MvPowerSeries.substAlgHom (hasSubst_law F))
    have hψ : ∀ f, Φ (ev (n := 2) ![F.F] f) = ψ f := by
      intro f
      simp only [ψ, AlgHom.comp_apply, MvPowerSeries.coe_substAlgHom]
      rfl
    have hs : IsSum F.F φ φ' ψ := ⟨Φ, h0, h1, hψ⟩
    have hT : Tors p F.F ψ := by
      obtain ⟨k, hk⟩ := hφ
      obtain ⟨k', hk'⟩ := hφ'
      refine ⟨max k k', (hkill _ _).1 ?_⟩
      rw [(hsum _ _ _).1 hs, smul_add, (hkill _ _).2 (killed_pow_mono F p (le_max_left k k') hk),
        (hkill _ _).2 (killed_pow_mono F p (le_max_right k k') hk'), add_zero]
    apply hinj
    rw [map_sub, map_mul, hψ, h0, h1, map_sub, map_mul, hval _ hT, hval _ hφ, hval _ hφ',
      hmul _ _ _ hφ hφ' hs, sub_self, map_zero]

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.GermsDerivKernelOfFormal
section
open scoped BigOperators
open NumberField Formalism.IncomingBounds Formalism.L2.FormalSeriesBounds Formalism.L2.Pj GlobalTheory.RowLaw ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowLaw

theorem germs_deriv_kernel_of_formal : IntegralGermIndependentAllCharts ∧ CEqFBSt ∧ IndependenceBoundAllCharts :=
  ⟨fun C _ _ V O _ _ dd Y d _ I _ p H =>
      _root_.GlobalTheory.RowLaw.intGerm_indep_of_rlaw C V d I (Fin dd) (Y.raw p) (_root_.GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p _ H =>
      GlobalTheory.T.gaugeDeriv_eq_pairing_of_integralGaugedLaw C V d I (Fin dd) (Y.raw p) (_root_.GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) H,
    fun C _ _ V O _ _ dd Y d _ I _ p hr H h2 =>
      _root_.GlobalTheory.RowKernel.independenceBoundCondition_of_rankMaximalCondition C V d I (Fin dd) (Y.raw p) (_root_.GlobalTheory.RowLawPair.rLaw_pairData C V O dd Y d I p) hr H h2⟩

end GlobalTheory.RowLaw
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.LinearDataUnramifiedLengthBound
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry TensorProduct Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open ReciprocityTheory.PGsh ReciprocityTheory.PGsh.Up ReciprocityTheory.PGsh.Be2 GlobalTheory.ChF
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.ChF

private theorem ofNat_succ_fin (n : ℕ) [NeZero n] (k : ℕ) :
    Fin.ofNat n (k + 1) = Fin.ofNat n k + 1 := by
  ext
  simp [Fin.add_def, Fin.ofNat]

private theorem exp_bound (p : ℕ) [Fact p.Prime] (h : ℕ) (a b c : ℕ → ℕ) (D : ℕ)
    (hab : ∀ n, a n + b n = h) (hbc : ∀ n, b n ≤ c n) (hD : ∀ n, c n ≤ D) :
    (h : ℝ) / (p - 1) - ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (a n : ℝ) ≤
      ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (c n : ℝ) := by
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg _
  have sa := summable_geom_p (p := p) (fun n => (a n : ℝ)) (fun _ => Nat.cast_nonneg _) h
    (fun n => by exact_mod_cast (hab n ▸ Nat.le_add_right _ _ : a n ≤ h))
  have sc := summable_geom_p (p := p) (fun n => (c n : ℝ)) (fun _ => Nat.cast_nonneg _) D
    (fun n => by exact_mod_cast hD n)
  have sh := summable_geom_p (p := p) (fun _ => (h : ℝ)) (fun _ => Nat.cast_nonneg _) h
    (fun _ => le_rfl)
  have e : (h : ℝ) / (p - 1) = ∑' n : ℕ, (p : ℝ) ^ (-((n : ℝ) + 1)) * (h : ℝ) := by
    rw [tsum_mul_right, tsum_geom_p]; ring
  rw [e, ← Summable.tsum_sub sh sa]
  refine Summable.tsum_le_tsum (fun n => ?_) (sh.sub sa) sc
  rw [← mul_sub]
  refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hp0 _)
  have h1 : (a n : ℝ) + b n = h := by exact_mod_cast hab n
  have h2 : (b n : ℝ) ≤ c n := by exact_mod_cast hbc n
  linarith

private theorem eigDim_le (C : Type) [Field C] {O OE : Type} [CommRing O] [Algebra O C] [CommRing OE]
    {d : ℕ} (ρ : OE → Matrix (Fin d) (Fin d) O) (τ : OE →+* C) : eigDim C ρ τ ≤ d := by
  unfold eigDim
  simpa using Submodule.finrank_le (⨅ a : OE, Module.End.eigenspace
    (Matrix.toLin' ((ρ a).map (algebraMap O C))) (τ a))

theorem linDat_unram_bound : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C], v.Integers O → ∀ [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [Algebra ℤ_[p] O] (OE : Type) [CommRing OE] [IsDedekindDomain OE] [CharZero OE] [Module.Free ℤ OE] [Module.Finite ℤ OE] [StarRing OE] (cp : O), HodgeTateSetting p v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp → ∀ (g : ℕ) (H : HodgeTateDatum p g v O (ℤ_[p] ⊗[ℤ] OE) (sigE p OE) cp) (d r m : ℕ) (A : Matrix (Fin d) (Fin r) O) (B : Matrix (Fin g) (Fin d) O) (ρG : OE →+* Matrix (Fin d) (Fin d) O) (N : OE →+* Matrix (Fin r) (Fin r) ℤ) (s : Fin m → Fin d → O), LinDat H A B ρG N s → ∀ [IsLocalRing O], p ≠ 2 → ¬ ((p : ℤ) ∣ Algebra.discr ℤ (Module.Free.chooseBasis ℤ OE)) → ∀ (w : PlaceU p OE) [NeZero w.n] (t : Fin w.n ≃ Emb (O := O) w.e), (∀ (j : Fin w.n) (a : OE), ((t (j + 1) : Emb (O := O) w.e) : OE →+* O) a - (((t j : Emb (O := O) w.e) : OE →+* O) a) ^ p ∈ IsLocalRing.maximalIdeal O) → ∀ (rk : (OE →+* O) → ℕ) (W : ∀ τ : OE →+* O, Fin (rk τ) → Fin d → O), (∀ τ, EigB ρG τ (W τ)) → ∀ j : Fin w.n, ∃ xs : NNReal, HasLen v O ((Fin (rk ((t j : Emb (O := O) w.e) : OE →+* O)) → O) ⧸ Submodule.span O (Set.range fun k => Pdiv.ChartF.res (W ((t j : Emb (O := O) w.e) : OE →+* O)) (s k))) xs ∧ v (algebraMap O C (p : O)) ^ (∑' n : ℕ, ((p : ℝ) ^ (-((n : ℝ) + 1))) * (rk (((t (j + Fin.ofNat w.n (n + 1)) : Emb (O := O) w.e) : OE →+* O).comp ((starRingAut : RingAut OE) : OE ≃+* OE).toRingHom) : ℝ)) ≤ xs := by
  intro p _ C _ _ _ v O _ _ hv _ _ _ OE _ _ _ _ _ _ cp hS g H d r m A B ρG N s hL _ hp2 hdisc w _ t ht
    rk W hW j
  obtain ⟨U, τ, ε, hsg, hr, -, -, hcj, hφ⟩ :=
    GlobalTheory.ChF.exists_unramData p C v O hv OE cp hS g H hL.noPad.1 hL.noPad.2 hdisc
  obtain ⟨hex, hmono, -⟩ := GlobalTheory.ChF.hasLen_exists_mono_fp C v O hv
  set ix : Fin w.n → Fin U.m := fun k => τ.symm ((t k : Emb (O := O) w.e) : OE →+* O) with hix
  have hτ : ∀ k, τ (ix k) = ((t k : Emb (O := O) w.e) : OE →+* O) := fun k => τ.apply_symm_apply _
  have hφ1 : ∀ k, U.φ (ix k) = ix (k + 1) := fun k => hφ _ _ (fun a => by rw [hτ, hτ]; exact ht k a)
  have hφn : ∀ n : ℕ, (U.φ ^ n) (ix j) = ix (j + Fin.ofNat w.n n) := by
    intro n
    induction n with
    | zero => simp
    | succ n ih => rw [pow_succ', Equiv.Perm.mul_apply, ih, hφ1, ofNat_succ_fin, add_assoc]

  obtain ⟨-, -, α, b, -⟩ := GlobalTheory.PlaceMono.place_monogenic p OE w
  obtain ⟨h, y, hy1, hy2⟩ := GlobalTheory.LocalFactorFree.exists_free_generators p OE w b (Ix g) H.ρ
  have hh : ∀ k, U.r (ix k) + U.r (U.cj (ix k)) = h := by
    intro k
    have e1 := GlobalTheory.ChF.eigDim_eq_of_basis p C v O hv OE w b (Ix g) H.ρ h y hy1 hy2 _ (t k).2
    have e2 := GlobalTheory.ChF.eigDim_tate p C v O hv OE cp hS g H
      ((algebraMap O C).comp ((t k : Emb (O := O) w.e) : OE →+* O))
    rw [hr, hr, hcj, hτ, ← e1, e2, RingHom.comp_assoc]

  have hrk : ∀ σ : OE →+* O, eigDim C ρG ((algebraMap O C).comp σ) = rk σ := fun σ =>
    (GlobalTheory.ChF.eigB_res_surjective C v O hv OE d (rk σ) ρG σ (W σ) (hW σ)).2.2
  have hle : ∀ i, U.r i ≤ rk (τ i) := by
    intro i
    have e := (GlobalTheory.EigAdd.eigDim_add_transpose C O OE d r g A B hL.exact ρG
      ((Int.castRingHom O).mapMatrix.comp N)
      (H.ρL.comp (Algebra.TensorProduct.includeRight (R := ℤ) (A := ℤ_[p]) (B := OE)).toRingHom)
      hL.eqB hL.eqA ((algebraMap O C).comp (τ i))).1
    rw [hr, ← hrk, e]
    exact Nat.le_add_left _ _
  have hD : ∀ σ, rk σ ≤ d := fun σ => hrk σ ▸ eigDim_le C _ _

  obtain ⟨V1, hV1⟩ := lenEx C v O hv g H.Ht (U.εL (ix j)) (U.εT (U.cj (ix j)))
  obtain ⟨f, hf⟩ := GlobalTheory.ChF.cokE_surj_res_quot p C v O hv OE cp hS g H d r m A B ρG N s hL U (ix j)
    ((t j : Emb (O := O) w.e) : OE →+* O) (fun x => by rw [hsg, hτ]) _ _ (hW _)
  obtain ⟨xs, hxs⟩ := hex ((Fin (rk ((t j : Emb (O := O) w.e) : OE →+* O)) → O) ⧸ Submodule.span O
      (Set.range fun k => Pdiv.ChartF.res (W ((t j : Emb (O := O) w.e) : OE →+* O)) (s k)))
    (Module.finitePresentation_of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
      (by rw [Submodule.ker_mkQ]; exact Submodule.fg_span (Set.finite_range _)))
  refine ⟨xs, hxs, ?_⟩
  have h1 := hmono _ _ f V1 xs hf hV1 hxs
  have h2 := up_full u7 p g C v O _ _ cp hp2 hS H U (ix j) _ (LinearEquiv.refl _ _) V1 hV1
  refine le_trans ?_ h1
  rw [← NNReal.coe_le_coe, NNReal.coe_rpow]
  refine le_trans ?_ h2
  refine Real.rpow_le_rpow_of_exponent_ge ?_ ?_ ?_
  · exact_mod_cast pos_iff_ne_zero.2 hS.p_ne
  · exact_mod_cast hS.p_lt.le
  · have e : ((U.r (ix j) : ℝ) + U.r (U.cj (ix j))) = h := by exact_mod_cast hh j
    rw [e]
    unfold frobSum
    refine exp_bound p h (fun n => U.r ((U.φ ^ (n + 1)) (ix j)))
      (fun n => U.r (U.cj (ix (j + Fin.ofNat w.n (n + 1))))) _ d (fun n => ?_) (fun n => ?_)
      (fun n => hD _)
    · rw [hφn]; exact hh _
    · have := hle (U.cj (ix (j + Fin.ofNat w.n (n + 1))))
      rwa [hcj, hτ] at this

end GlobalTheory.ChF
end

-- bundled from Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.NabValNEqSumCoeff
section
open scoped BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ Formalism.L2.Pj NumberField

namespace GlobalTheory

theorem functional_eq_sum_coeff_of_vanish {σ K : Type} [CommRing K] [Finite σ]
    (F : MvPowerSeries σ K → K) (N : ℕ)
    (hadd : ∀ f g, F (f + g) = F f + F g) (hsmul : ∀ (t : K) f, F (t • f) = t * F f)
    (hvan : ∀ f, (∀ μ : σ →₀ ℕ, μ.degree ≤ N → MvPowerSeries.coeff μ f = 0) → F f = 0) :
    ∃ S : Finset (σ →₀ ℕ), ∀ f, F f =
      ∑ μ ∈ S, MvPowerSeries.coeff μ f * F (MvPowerSeries.monomial μ (1 : K)) := by
  classical
  let L : MvPowerSeries σ K →ₗ[K] K :=
    { toFun := F, map_add' := hadd, map_smul' := fun t f => by simpa using hsmul t f }
  have hL : ∀ f, L f = F f := fun _ => rfl
  refine ⟨(Finsupp.finite_of_degree_le (σ := σ) N).toFinset, fun f => ?_⟩
  set S := (Finsupp.finite_of_degree_le (σ := σ) N).toFinset with hS
  have hg : F (f - ∑ μ ∈ S, MvPowerSeries.coeff μ f • MvPowerSeries.monomial μ (1 : K)) = 0 := by
    apply hvan
    intro ν hν
    have hνS : ν ∈ S := by simpa [hS] using hν
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sub, map_sum, Finset.sum_eq_single_of_mem ν hνS]
    · simp
    · intro μ _ hne
      rw [map_smul, MvPowerSeries.coeff_monomial_ne (Ne.symm hne)]
      simp
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← hL, map_sub, map_sum, sub_eq_zero] at hg
  rw [← hL, hg]
  refine Finset.sum_congr rfl fun μ _ => ?_
  rw [map_smul, hL, smul_eq_mul]

theorem nabValN_eq_sum_coeff : ∀ (K : Type) [CommRing K] [Algebra ℚ K] (d : ℕ) (O : Type) [CommRing O] [StarRing O] (B : FB K d O) (h : PS K 2 d) (w0 : O) (m n : ℕ) (ι : Type) [Fintype ι] (cp : ι → Fin n) (u : ι → Fin d → K), ∀ (P : MvPolynomial ι K), ∃ S : Finset (Fin n × Fin d →₀ ℕ), ∀ f : PS K n d, nabValN B K h w0 m f cp u P = ∑ μ ∈ S, MvPowerSeries.coeff μ f * nabValN B K h w0 m (MvPowerSeries.monomial μ (1 : K)) cp u P := by
  intro K _ _ d O _ _ B h w0 m n ι _ cp u P
  obtain ⟨h1, h2, -, -⟩ := _root_.GlobalTheory.nabValN_bilinear K d O B h w0 m n ι cp u
  exact functional_eq_sum_coeff_of_vanish (fun f => nabValN B K h w0 m f cp u P) P.totalDegree
    (fun f g => h1 f g P) (fun t f => h2 t f P)
    (fun f hf => _root_.GlobalTheory.PowGerm.nabValN_eq_zero_of_coeff_eq_zero K d O B h w0 m n ι cp u f P hf)

end GlobalTheory
end

