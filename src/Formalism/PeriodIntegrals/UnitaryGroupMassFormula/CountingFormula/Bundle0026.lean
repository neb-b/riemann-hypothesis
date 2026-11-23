module

public import Mathlib
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0025
public import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.Bundle0022
public import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.Bundle0009

@[expose] public section

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountLeOfIntegral
section
open NumberField Module IsDedekindDomain Formalism.HermitianLattices.Ext.L3 Formalism.L2.SG.Pf.Cnt

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

section Counts

variable {K : Type} [Field K] [NumberField K]

theorem count_span_mul (P : HeightOneSpectrum (𝓞 K)) {y z : K} (hy : y ≠ 0) (hz : z ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (y * z)) =
      FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y) +
        FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) z) := by
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have hz' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) z ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hz
  rw [← FractionalIdeal.spanSingleton_mul_spanSingleton, FractionalIdeal.count_mul K P hy' hz']

theorem count_span_inv (P : HeightOneSpectrum (𝓞 K)) (y : K) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y⁻¹) =
      - FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y) := by
  by_cases hy : y = 0
  · simp [hy, FractionalIdeal.count_zero]
  have hy' : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have hyi : FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) y⁻¹ ≠ 0 := by
    simpa [FractionalIdeal.spanSingleton_eq_zero_iff] using hy
  have h := FractionalIdeal.count_mul K P hyi hy'
  rw [FractionalIdeal.spanSingleton_mul_spanSingleton, inv_mul_cancel₀ hy,
    FractionalIdeal.spanSingleton_one, FractionalIdeal.count_one] at h
  omega

theorem count_span_prod {ι : Type} (P : HeightOneSpectrum (𝓞 K)) (s : Finset ι) (z : ι → K)
    (hz : ∀ i, z i ≠ 0) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (∏ i ∈ s, z i)) =
      ∑ i ∈ s, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (z i)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [FractionalIdeal.count_one]
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha, count_span_mul P (hz a)
      (Finset.prod_ne_zero_iff.mpr fun i _ => hz i), ih]

theorem count_le_of_integral {ι : Type} [Fintype ι] (P : HeightOneSpectrum (𝓞 K)) (c : K) (s : 𝓞 K)
    (z : ι → K) (hc : c ≠ 0) (hs : s ∉ P.asIdeal) (hz : ∀ i, z i ≠ 0)
    (hw : c⁻¹ * (s : K) * ∏ i, z i ∈ (1 : FractionalIdeal (nonZeroDivisors (𝓞 K)) K)) :
    FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) c) ≤
      ∑ i, FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (z i)) := by
  have hs0 : (s : K) ≠ 0 := by
    intro h
    apply hs
    have : s = 0 := by exact_mod_cast h
    rw [this]; exact P.asIdeal.zero_mem
  have hprod : ∏ i, z i ≠ 0 := Finset.prod_ne_zero_iff.mpr fun i _ => hz i
  have hw0 : c⁻¹ * (s : K) * ∏ i, z i ≠ 0 :=
    mul_ne_zero (mul_ne_zero (inv_ne_zero hc) hs0) hprod
  have h1 := count_le_of_mem (K := K) P hw hw0
  rw [FractionalIdeal.count_one, count_span_mul P (mul_ne_zero (inv_ne_zero hc) hs0) hprod,
    count_span_mul P (inv_ne_zero hc) hs0, count_span_inv, count_span_prod P _ _ hz] at h1
  have h2 : FractionalIdeal.count K P (FractionalIdeal.spanSingleton (nonZeroDivisors (𝓞 K)) (s : K)) = 0 :=
    count_span_unit (K := K) P s hs
  rw [h2] at h1
  linarith

end Counts

end PI.UnitaryGroupMassFormula.CntFormula.R6
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.LatticeFlagExists
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Flag

variable {D : D7} {T : D.host.E} {F0 : FlagG (VS D) D.R.rS T} {f : Fin D.R.rS → (VS D).V}
  {M : Submodule (𝓞 D.host.E) (WbQ D F0)}

theorem rs_mem_lamC_perp {v : (VS D).V} (hv : v ∈ perpS (VS D) F0.X) :
    v ∈ lamC D F0 f M ↔ (Submodule.Quotient.mk (⟨v, hv⟩ : perpS (VS D) F0.X) : WbQ D F0) ∈ M ∧
      ∀ a, (VS D).hT (f a) v ∈ aaI D a := by
  have h0 : ∀ a, (VS D).hT (F0.e a) v = 0 := fun a => hv _ (Submodule.subset_span ⟨a, rfl⟩)
  have hvPr : vPr D F0 f v = v := by simp [vPr, h0]
  constructor
  · rintro ⟨-, ⟨w, hw, hwM⟩, h3⟩
    have hwv : w = ⟨v, hv⟩ := Subtype.ext (hw.trans hvPr)
    subst hwv
    exact ⟨hwM, fun a => by rw [← hvPr]; exact h3 a⟩
  · rintro ⟨hM, h3⟩
    refine ⟨fun a => ?_, ⟨⟨v, hv⟩, hvPr.symm, hM⟩, fun a => ?_⟩
    · simp only [h0, star_zero]
      exact fi_zero D _
    · rw [hvPr]
      exact h3 a

theorem rs_orth_perp {y : (VS D).V} (hy : y ∈ orth (VS D) F0.X) : y ∈ perpS (VS D) F0.X := by
  simp only [orth, Submodule.mem_iInf, LinearMap.mem_ker] at hy
  exact fun x hx => hy x hx

theorem rs_z_mem (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) :
    F0.z ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (z_mem_perp D F0)]
  refine ⟨hM.2.2.1, fun a => ?_⟩
  rw [hf.2.2 a]
  exact fi_zero D _

theorem rs_smul_e_mem (hf : PartnerOK D F0 f) {a : Fin D.R.rS} {x : D.host.E} (hx : x ∈ aaI D a) :
    x • F0.e a ∈ lamC D F0 f M := by
  have hXe : ∀ y ∈ F0.X, ∀ b, (VS D).hT y (F0.e b) = 0 := by
    intro y hy b
    have hy' : y ∈ Submodule.span D.host.E (Set.range F0.e) := hy
    clear hy
    induction hy' using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨c, rfl⟩ := hz
      exact F0.e_iso c b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  have hperp : x • F0.e a ∈ perpS (VS D) F0.X := by
    intro y hy
    rw [map_smul, hXe y hy a, smul_zero]
  rw [rs_mem_lamC_perp hperp]
  refine ⟨?_, fun b => ?_⟩
  · have hmem : x • F0.e a ∈ F0.X := Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    have h0 : (Submodule.Quotient.mk (⟨x • F0.e a, hperp⟩ : perpS (VS D) F0.X) : WbQ D F0) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr hmem
    rw [h0]
    exact zero_mem _
  · have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [map_smul, ← hs, hf.1 a b, smul_eq_mul]
    split_ifs with hab
    · subst hab
      simpa using hx
    · simp only [map_zero, mul_zero]
      exact FractionalIdeal.zero_mem _

theorem rs_xlam (hf : PartnerOK D F0 f) : XLam (lamC D F0 f M) (lf D F0) = XS D F0 := by
  apply le_antisymm
  · rintro v ⟨hvΛ, hvX⟩
    have hvX' : v ∈ F0.X := hvX
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun D.host.E).1 hvX'
    have hα := ((rs_mem_lamC_perp (rs_X_le_perp D F0 hvX')).1 hvΛ).2
    have hca : ∀ a, c a ∈ aaI D a := by
      intro a
      have h := hα a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← hc, map_sum] at h
      simp only [map_smul, rs_hT_f_e hf, smul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true] at h
      exact h
    rw [← hc]
    refine Submodule.sum_mem _ fun a _ => Submodule.subset_span ⟨a, c a, hca a, rfl⟩
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨a, x, hx, rfl⟩
    exact ⟨rs_smul_e_mem hf hx, Submodule.smul_mem _ x (rs_e_mem_X D F0 a)⟩

theorem rs_prim (hf : PartnerOK D F0 f) (hM : IsGlueLat (hWb D F0) (zbar D F0) M) (c : D.host.E)
    (hc : c • F0.z ∈ Lsub (lamC D F0 f M) (lf D F0)) : ∃ o : 𝓞 D.host.E, (o : D.host.E) = c := by
  obtain ⟨y, hy, x, hx, hyx⟩ := Submodule.mem_sup.1 hc.1
  have hyΛ : y ∈ lamC D F0 f M := hy.1
  have hyp : y ∈ perpS (VS D) F0.X := rs_orth_perp hy.2
  have hxX : x ∈ F0.X := hx
  have hxp : x ∈ perpS (VS D) F0.X := rs_X_le_perp D F0 hxX
  have hyM := ((rs_mem_lamC_perp hyp).1 hyΛ).1
  apply hM.2.2.2 c
  have hsum : c • (⟨F0.z, z_mem_perp D F0⟩ : perpS (VS D) F0.X) = ⟨y, hyp⟩ + ⟨x, hxp⟩ := by
    apply Subtype.ext
    simp only [Submodule.coe_smul, Submodule.coe_add]
    exact hyx.symm
  rw [zbar, ← Submodule.Quotient.mk_smul, hsum, Submodule.Quotient.mk_add, rs_mk_X_zero D F0 hxX, add_zero]
  exact hyM

def rsLift (w : perpS (VS D) F0.X) : (VS D).V := (w : (VS D).V) - ∑ a, (VS D).hT (f a) w • F0.e a

theorem rs_lift_perp (w : perpS (VS D) F0.X) : rsLift (f := f) w ∈ perpS (VS D) F0.X := by
  show ∀ x ∈ F0.X, (VS D).hT x (rsLift (f := f) w) = 0
  intro x hx
  have hxe : ∀ b, (VS D).hT x (F0.e b) = 0 := by
    intro b
    have hx' : x ∈ Submodule.span D.host.E (Set.range F0.e) := hx
    clear hx
    induction hx' using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨a, rfl⟩ := hy
      exact F0.e_iso a b
    | zero => rw [map_zero, LinearMap.zero_apply]
    | add y z _ _ hy hz => rw [map_add (f := _), LinearMap.add_apply, hy, hz, add_zero]
    | smul c y _ hy => rw [LinearMap.map_smulₛₗ, LinearMap.smul_apply, hy, smul_zero]
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rsLift, map_sub, map_sum, map_smul, hxe, smul_zero, Finset.sum_const_zero, sub_zero]
  exact w.2 x hx

theorem rs_lift_mk (w : perpS (VS D) F0.X) :
    (Submodule.Quotient.mk (⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) : WbQ D F0) =
      Submodule.Quotient.mk w := by
  apply (Submodule.Quotient.eq _).mpr
  show (((⟨rsLift (f := f) w, rs_lift_perp w⟩ : perpS (VS D) F0.X) - w : perpS (VS D) F0.X) : (VS D).V) ∈ F0.X
  simp only [Submodule.coe_sub, rsLift, sub_sub_cancel_left]
  exact neg_mem (sum_mem fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩))

theorem rs_hT_f_lift (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X) (b : Fin D.R.rS) :
    (VS D).hT (f b) (rsLift (f := f) w) = 0 := by
  have hfe : ∀ a, (VS D).hT (f b) (F0.e a) = if a = b then 1 else 0 := by
    intro a
    have hs : starRingEnd D.host.E ((VS D).hT (F0.e a) (f b)) = (VS D).hT (f b) (F0.e a) := by
      first
        | exact (VS D).herm (F0.e a) (f b)
        | exact (VS D).herm.eq (F0.e a) (f b)
    rw [← hs, hf.1 a b]
    split_ifs <;> simp
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [rsLift, map_sub, map_sum, map_smul, hfe, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true, sub_self]

theorem rs_lift_mem (hf : PartnerOK D F0 f) (w : perpS (VS D) F0.X)
    (hw : (Submodule.Quotient.mk w : WbQ D F0) ∈ M) : rsLift (f := f) w ∈ lamC D F0 f M := by
  rw [rs_mem_lamC_perp (rs_lift_perp w)]
  refine ⟨?_, fun a => ?_⟩
  · rw [rs_lift_mk]
    exact hw
  · rw [rs_hT_f_lift hf w a]
    exact FractionalIdeal.zero_mem _

theorem rs_mof (hf : PartnerOK D F0 f) : Mof D F0 (lamC D F0 f M) = M := by
  apply le_antisymm
  · rintro _ ⟨w, hw, rfl⟩
    have hw' : (w : (VS D).V) ∈ lamC D F0 f M := hw
    exact ((rs_mem_lamC_perp w.2).1 hw').1
  · intro m hm
    obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ m
    refine ⟨⟨rsLift (f := f) w, rs_lift_perp w⟩, rs_lift_mem hf w hm, ?_⟩
    exact rs_lift_mk w

end Flag

theorem lattice_flag_exists : LamFlag := by
  intro D u F0 f M hf hM
  exact ⟨rs_z_mem hf hM, rs_xlam hf, rs_prim hf hM, rs_mof hf⟩

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.RowUnitCondition
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

open PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

theorem star_int {K : Type} [Field K] [NumberField K] [StarRing K] (o : 𝓞 K) :
    ∃ o' : 𝓞 K, (o' : K) = star (o : K) := by
  have h1 : IsIntegral ℤ (star (o : K)) :=
    (NumberField.RingOfIntegers.isIntegral_coe o).map (starRingEnd K).toIntAlgHom
  exact ⟨⟨star (o : K), h1⟩, rfl⟩

theorem exists_one {K : Type} [Field K] [NumberField K] [StarRing K]
    {W : Type} [AddCommGroup W] [Module K W] [Module (𝓞 K) W] [IsScalarTower (𝓞 K) K W]
    (h : W →ₗ⋆[K] W →ₗ[K] K) (M : Submodule (𝓞 K) W)
    (hU : Formalism.HermitianLatticesTheory.IsUnimodular h M) {z : W} (hz : z ∈ M)
    (hprim : ∀ c : K, c • z ∈ M → ∃ o : 𝓞 K, (o : K) = c) : ∃ m ∈ M, h m z = 1 := by
  classical

  have memM : ∀ x : W, x ∈ M ↔ ∀ m ∈ M, ∃ y : 𝓞 K, algebraMap (𝓞 K) K y = h m x := by
    intro x
    conv_lhs => rw [← hU]
    simp only [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
      LinearMap.restrictScalars_apply, Submodule.mem_one]

  let I : Ideal (𝓞 K) :=
    { carrier := {o | ∃ m ∈ M, h m z = star (o : K)}
      add_mem' := by
        rintro a b ⟨m₁, hm₁, e₁⟩ ⟨m₂, hm₂, e₂⟩
        refine ⟨m₁ + m₂, M.add_mem hm₁ hm₂, ?_⟩
        rw [map_add (f := _), LinearMap.add_apply, e₁, e₂]
        show star (algebraMap (𝓞 K) K a) + star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a + b))
        rw [map_add (f := _), star_add]
      zero_mem' := ⟨0, M.zero_mem, by
        rw [map_zero, LinearMap.zero_apply]
        show (0 : K) = star (algebraMap (𝓞 K) K 0)
        rw [map_zero, star_zero]⟩
      smul_mem' := by
        rintro a b ⟨m, hm, e⟩
        refine ⟨a • m, M.smul_mem a hm, ?_⟩
        have ha : (a • m : W) = (algebraMap (𝓞 K) K a) • m := (algebraMap_smul K a m).symm
        rw [ha, LinearMap.map_smulₛₗ, LinearMap.smul_apply, e]
        simp only [smul_eq_mul, starRingEnd_apply]
        show star (algebraMap (𝓞 K) K a) * star (algebraMap (𝓞 K) K b) =
          star (algebraMap (𝓞 K) K (a * b))
        rw [map_mul, star_mul'] }
  have memI : ∀ o : 𝓞 K, o ∈ I ↔ ∃ m ∈ M, h m z = star (o : K) := fun o => Iff.rfl
  by_contra hne
  push_neg at hne
  have hI : I ≠ ⊤ := by
    intro htop
    have h1 : (1 : 𝓞 K) ∈ I := by rw [htop]; exact Submodule.mem_top
    obtain ⟨m, hm, e⟩ := (memI 1).1 h1
    exact hne m hm (by rw [e]; show star (algebraMap (𝓞 K) K 1) = 1; rw [map_one, star_one])
  obtain ⟨P, hPmax, hIP⟩ := Ideal.exists_le_maximal I hI
  have hP0 : P ≠ ⊥ :=
    Ring.ne_bot_of_isMaximal_of_not_isField hPmax (NumberField.RingOfIntegers.not_isField K)
  obtain ⟨c, hc, hc1⟩ :=
    FractionalIdeal.exists_notMem_one_of_ne_bot (K := K) hP0 hPmax.ne_top
  have hPne : (P : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) ≠ 0 := by
    rwa [ne_eq, FractionalIdeal.coeIdeal_eq_zero]
  rw [FractionalIdeal.mem_inv_iff hPne] at hc

  have hcz : (star c) • z ∈ M := by
    rw [memM]
    intro m hm
    obtain ⟨t, ht⟩ := (memM z).1 hz m hm
    obtain ⟨t', ht'⟩ := star_int t
    have e1 : h m z = star (t' : K) := by rw [ht', star_star]; exact ht.symm
    have ht'I : t' ∈ I := (memI t').2 ⟨m, hm, e1⟩
    have hcy := hc _ (by rw [FractionalIdeal.mem_coeIdeal]; exact ⟨t', hIP ht'I, rfl⟩)
    rw [FractionalIdeal.mem_one_iff] at hcy
    obtain ⟨s, hs⟩ := hcy
    obtain ⟨s', hs'⟩ := star_int s
    refine ⟨s', ?_⟩
    rw [map_smul, smul_eq_mul, e1, ← star_mul']
    change (s' : K) = _
    rw [hs']
    congr 1
  obtain ⟨o, ho⟩ := hprim _ hcz
  obtain ⟨o', ho'⟩ := star_int o
  apply hc1
  rw [FractionalIdeal.mem_one_iff]
  exact ⟨o', by change (o' : K) = c; rw [ho', ho, star_star]⟩

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem row_unit_condition : RowZUnit := by
  intro D u F0 Λ hrow
  obtain ⟨_, hMU, hzM, hprim⟩ := row_lattice_mass_holds D u F0 Λ hrow
  obtain ⟨m, hm, hm1⟩ := exists_one (hWb D F0) (Mof D F0 Λ) hMU hzM hprim
  obtain ⟨a, haΛ, rfl⟩ := (RowMPf.mem_Mof D F0 Λ m).1 hm
  refine ⟨a, haΛ, a.2, ?_⟩
  rw [zbar, hWb_mk] at hm1
  exact hm1

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf

theorem PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.row_unit_condition : PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnit := PI.UnitaryGroupMassFormula.CntFormula.RowsMassW.RowZUnitPf.row_unit_condition
end
end

-- bundled from Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.TraceOneUnramified
section
open NumberField Module Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.BasicNotions Formalism.L2.SG.CntLocal
open Classical

noncomputable section

namespace PI.UnitaryGroupMassFormula.CntFormula.RowsMassW

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem trace_one_unramified : TraceOne := fun D =>
  Formalism.MainNotions.BridgeLemma.l_theta D.host.E D.sp.cm.cmUnram

section Dual

variable {D : D7} {T : D.host.E} (F0 : FlagG (VS D) D.R.rS T)

theorem exists_dual0 : ∃ g0 : Fin D.R.rS → (VS D).V, IsDual0 F0 g0 := by
  let Φ : (VS D).V →ₗ[D.host.E] (Fin D.R.rS → D.host.E) := LinearMap.pi (fun a => (VS D).hT (F0.e a))
  have hsurj : LinearMap.range Φ = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hle⟩ := Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.2 hne)
    set μ : Fin D.R.rS → D.host.E := fun a => f (fun j => if a = j then 1 else 0) with hμdef
    have hv : ∀ v, ∑ a, (VS D).hT (F0.e a) v * μ a = 0 := by
      intro v
      have h1 : f (Φ v) = 0 := hle (LinearMap.mem_range_self Φ v)
      rw [LinearMap.pi_apply_eq_sum_univ f (Φ v)] at h1
      simpa [Φ, LinearMap.pi_apply, smul_eq_mul, μ] using h1
    have hx : ∑ a, star (μ a) • F0.e a = 0 := by
      apply (VS D).nondeg.1
      intro v
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum, LinearMap.sum_apply]
      simp only [map_smulₛₗ, LinearMap.smul_apply, starRingEnd_apply, star_star, smul_eq_mul]
      rw [← hv v]
      exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
    have hμ : ∀ a, μ a = 0 := by
      intro a
      have := Fintype.linearIndependent_iff.1 F0.e_indep (fun a => star (μ a)) hx a
      simpa using this
    apply hf0
    apply LinearMap.ext
    intro u
    rw [LinearMap.pi_apply_eq_sum_univ f u]
    simp only [LinearMap.zero_apply]
    apply Finset.sum_eq_zero
    intro a _
    have : f (fun j => if a = j then 1 else 0) = 0 := hμ a
    rw [this, smul_zero]
  refine ⟨fun b => Classical.choose (LinearMap.range_eq_top.1 hsurj (Pi.single b 1)), ?_⟩
  intro a b
  have h := Classical.choose_spec (LinearMap.range_eq_top.1 hsurj (Pi.single b 1))
  have h2 := congrFun h a
  simp only [Φ, LinearMap.pi_apply] at h2
  rw [h2, Pi.single_apply]

end Dual

theorem row_dual_frame : RowDualFrame := by
  intro D u F0 Λ hΛ
  obtain ⟨g0, hg0⟩ := exists_dual0 F0
  have hlat : Submodule.IsLattice D.host.E Λ := hΛ.2.1.1
  have hu : Formalism.HermitianLatticesTheory.IsUnimodular (VS D).hT Λ := hΛ.2.1.2.1
  have hiso : ∀ x ∈ F0.X, ∀ y ∈ F0.X, (VS D).hT x y = 0 := fun x hx y hy => hX_X F0 hx hy
  obtain ⟨P, P', hadj, hid, hX, _, hint', _⟩ :=
    Formalism.MainNotions.BridgeLemma.l_iso Formalism.MainNotions.BridgeLemma.l_adj Formalism.MainNotions.BridgeLemma.l_retr Formalism.MainNotions.BridgeLemma.l_theta
      D.host.E (VS D) Λ F0.X D.sp.cm.cmUnram hlat hu hiso

  have hker : ∀ w ∈ perpS (VS D) F0.X, P' w = 0 := by
    intro w hw
    apply (VS D).nondeg.2
    intro x
    rw [← hadj x w]
    exact hw _ (hX x)
  refine ⟨fun b => P' (g0 b), ?_, ?_⟩
  · intro a b
    show (VS D).hT (F0.e a) (P' (g0 b)) = _
    rw [← hadj, hid _ (e_mem_X F0 a), hg0 a b]
  · intro v hv
    have hg0' : ∀ a b, (VS D).hT (F0.e a) (g0 b) = if a = b then 1 else 0 := hg0
    have hyc : ycL F0 (fun b => P' (g0 b)) v = P' (ycL F0 g0 v) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [ycL_apply, ycL_apply, map_sum]
      exact Finset.sum_congr rfl (fun b _ => by rw [map_smul])
    have hperp : v - ycL F0 g0 v ∈ perpS (VS D) F0.X := by
      apply mem_perp_of F0
      intro a
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sub, ycL_apply, map_sum]
      simp [hg0']
    have h1 : P' (ycL F0 g0 v) = P' v := by
      have := hker _ hperp
      rw [map_sub, sub_eq_zero] at this
      exact this.symm
    rw [hyc, h1]
    exact hint' v hv

theorem rowClass_of_zunit (h : RowZUnit) : RowClass :=
  rowClass_of_three row_dual_frame h trace_one_unramified

end PI.UnitaryGroupMassFormula.CntFormula.RowsMassW
end
end

