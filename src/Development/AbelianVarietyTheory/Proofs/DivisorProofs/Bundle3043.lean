module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasDivPlace
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2108
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2698
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2710
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2697
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3025
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2692
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2814
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0920
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3011
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2944
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3034
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasTraitsOnOfHasTraitsP
public import ReciprocityTheory.AnalyticForms.RegularLocalRings.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3027
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2056
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0187
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.UnitThetaConstantsGenerateIntegralTorsion
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0196
public import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.Bundle0193
public import Development.AbelianVarietyTheory.Proofs.ModuliProofs.Bundle0214
public import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.Bundle0029
public import Development.AbelianVarietyTheory.Definitions.Degenerations.NormNatCastPadicAlgClOfCoprime
public import Development.AbelianVarietyTheory.Definitions.Divisors.ToRingActOpOfRingAct
public import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyHomFixRepTrivial
public import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3016
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3010
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle3026

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoprimeNsmulEndomorphismPreservesCompletio
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LKGeo.DenEnd

variable {p : ℕ} [Fact p.Prime]

theorem inAf_mem (D : Datum p) (x : D.La) : inAf D x ∈ LaHat D :=
  AddSubgroup.subset_closure ⟨1, x, fun v => by rw [map_one]; exact one_mem _, rfl⟩

theorem smul_mem (D : Datum p) {a : AfP p} (ha : IsIntAf a) {v : AfP p ⊗[ℚ] VQ D} (hv : v ∈ LaHat D) :
    a • v ∈ LaHat D := by
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨c, x, hc, rfl⟩ := hz
    refine AddSubgroup.subset_closure ⟨a * c, x, fun w => ?_, ?_⟩
    · rw [map_mul]; exact mul_mem (ha w) (hc w)
    · rw [TensorProduct.smul_tmul', smul_eq_mul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [smul_neg]; exact neg_mem hx

theorem exists_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) : ∃ d : ℕ, 0 < d ∧ d • v ∈ LaHat D := by
  have hadd : ∀ u w : AfP p ⊗[ℚ] VQ D, (∃ d : ℕ, 0 < d ∧ d • u ∈ LaHat D) → (∃ d : ℕ, 0 < d ∧ d • w ∈ LaHat D) →
      ∃ d : ℕ, 0 < d ∧ d • (u + w) ∈ LaHat D := by
    rintro u w ⟨d, hd, hu⟩ ⟨e, he, hw⟩
    refine ⟨d * e, Nat.mul_pos hd he, ?_⟩
    have : (d * e) • (u + w) = e • (d • u) + d • (e • w) := by
      rw [smul_add, smul_smul, smul_smul, mul_comm e d]
    rw [this]
    exact add_mem (nsmul_mem hu _) (nsmul_mem hw _)
  induction v using TensorProduct.induction_on with
  | zero => exact ⟨1, one_pos, by rw [smul_zero]; exact zero_mem _⟩
  | add u w hu hw => exact hadd u w hu hw
  | tmul a w =>
    induction w using TensorProduct.induction_on with
    | zero => exact ⟨1, one_pos, by rw [TensorProduct.tmul_zero, smul_zero]; exact zero_mem _⟩
    | add u w hu hw => rw [TensorProduct.tmul_add]; exact hadd _ _ hu hw
    | tmul q x =>
      obtain ⟨d, hd, h⟩ := GlobalTheory.DenAway.exists_nat_adele (q • a)
      refine ⟨d, hd, AddSubgroup.subset_closure ⟨(d : AfP p) * (q • a), x, h, ?_⟩⟩
      have e : q ⊗ₜ[ℤ] x = q • ((1 : ℚ) ⊗ₜ[ℤ] x) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
      rw [e, ← TensorProduct.smul_tmul, TensorProduct.smul_tmul', nsmul_eq_mul]

theorem isIntAf_inv : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹) := by
  intro v
  rw [AlgHom.commutes, IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have h1 : v.1.valuation ℚ (algebraMap ℤ ℚ (p : ℤ)) = 1 := by
    refine le_antisymm (v.1.valuation_le_one _) (not_lt.1 fun h => v.2 ?_)
    rw [IsDedekindDomain.HeightOneSpectrum.valuation_lt_one_iff_mem] at h
    have hm : (Ideal.span {(p : ℤ)}).IsMaximal :=
      PrincipalIdealRing.isMaximal_of_irreducible (Nat.prime_iff_prime_int.mp Fact.out).irreducible
    exact (hm.eq_of_le v.1.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 h)).symm
  have h2 : Valued.v (algebraMap ℚ (v.1.adicCompletion ℚ) (p : ℚ)⁻¹) = v.1.valuation ℚ (p : ℚ)⁻¹ :=
    IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v.1 _
  rw [h2, map_inv₀]
  simp only [eq_intCast, Int.cast_natCast] at h1
  rw [h1, inv_one]

theorem exists_coprime_nsmul_mem (D : Datum p) (v : AfP p ⊗[ℚ] VQ D) :
    ∃ t : ℕ, 0 < t ∧ t.Coprime p ∧ t • v ∈ LaHat D := by
  obtain ⟨d, hd, h⟩ := exists_nsmul_mem D v
  obtain ⟨k, t, ht, hdt⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd.ne' p (Fact.out : p.Prime).ne_one
  have ht0 : 0 < t := Nat.pos_of_ne_zero fun h => ht (h ▸ dvd_zero p)
  refine ⟨t, ht0, ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 ht).symm, ?_⟩
  have hint : IsIntAf (algebraMap ℚ (AfP p) (p : ℚ)⁻¹ ^ k) := fun u => by
    rw [map_pow]; exact pow_mem (isIntAf_inv u) k
  have hm := smul_mem D hint h
  have hp : (p : ℚ) ≠ 0 := by exact_mod_cast (Fact.out : p.Prime).ne_zero
  convert hm using 1
  rw [hdt, ← map_pow, algebraMap_smul, ← Nat.cast_smul_eq_nsmul ℚ, ← Nat.cast_smul_eq_nsmul ℚ, smul_smul]
  congr 1
  push_cast
  rw [inv_pow, ← _root_.mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hp), _root_.one_mul]

theorem exists_coprime_nsmul_map_mem : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p)
    (A : Module.End (AfP p) (AfP p ⊗[ℚ] VQ D)), ∃ j : ℕ, 0 < j ∧ j.Coprime p ∧ ∀ v ∈ LaHat D, j • A v ∈ LaHat D := by
  intro p _ D A
  have := D.freeLa
  have := D.finLa
  let b := Module.Free.chooseBasis ℤ D.La
  choose t ht0 htc ht using fun i => exists_coprime_nsmul_mem D (A (inAf D (b i)))
  refine ⟨∏ i, t i, Finset.prod_pos fun i _ => ht0 i, Nat.Coprime.prod_left fun i _ => htc i, ?_⟩
  have hbase : ∀ x : D.La, (∏ i, t i) • A (inAf D x) ∈ LaHat D := by
    intro x
    have hx : x ∈ Submodule.span ℤ (Set.range b) := by rw [b.span_eq]; trivial
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      obtain ⟨k, hk⟩ := Finset.dvd_prod_of_mem t (Finset.mem_univ i)
      rw [hk, mul_comm, mul_smul]
      exact nsmul_mem (ht i) k
    | zero =>
      have : inAf D 0 = 0 := by simp [inAf]
      rw [this, map_zero, smul_zero]; exact zero_mem _
    | add y z _ _ hy hz =>
      have : inAf D (y + z) = inAf D y + inAf D z := by simp only [inAf, TensorProduct.tmul_add]
      rw [this, map_add (f := _), smul_add]; exact add_mem hy hz
    | smul c y _ hy =>
      have : inAf D (c • y) = c • inAf D y := by
        simp only [inAf, TensorProduct.tmul_smul]
      rw [this, map_zsmul, smul_comm]; exact zsmul_mem hy c
  intro v hv
  induction hv using AddSubgroup.closure_induction with
  | mem z hz =>
    obtain ⟨a, x, ha, rfl⟩ := hz
    have e : a ⊗ₜ[ℚ] ((1 : ℚ) ⊗ₜ[ℤ] x) = a • inAf D x := by
      rw [inAf, TensorProduct.smul_tmul', smul_eq_mul, _root_.mul_one]
    rw [e, map_smul, smul_comm]
    exact smul_mem D ha (hbase x)
  | zero => rw [map_zero, smul_zero]; exact zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _), smul_add]; exact add_mem hx hy
  | neg x _ hx => rw [map_neg, smul_neg]; exact neg_mem hx

end GlobalTheory.LKGeo.DenEnd
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegeneratingMonomialFamilyAlgClosedResidue
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.UChartGeo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H}
  {Xo : Moduli Dw l} {c : Coeff l} {φ : InvFun (𝓞 E)}

theorem nontrivial_of_not_mem_range {V : Type} [CommRing V] [IsDomain V] [IsLocalRing V] (hV : GlobalTheory.Mum.Base V)
    (C : MonoFam Xo c φ V) {S T : Scheme.{0}} (s : S ⟶ T) [IsSeparated s] (j : Xo.XF c ⟶ S) (ξV : Sp V ⟶ S)
    (hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ s = g ≫ s)
    (hy : C.y ≫ j = jK V ≫ ξV) (hx : ξV (closedPoint V) ∉ Set.range j) : Nontrivial C.P.D.toPre.X := by
  by_contra hX
  rw [not_nontrivial_iff_subsingleton] at hX
  haveI : IsEmpty (Fin C.m) := ⟨fun i =>
    C.cone.linearIndependent.ne_zero i (LinearMap.ext₂ fun a b => by
      rw [Subsingleton.elim a 0]; simp)⟩
  have hprod : ∏ i, C.s i = 1 := by simp [Finset.univ_eq_empty]
  obtain ⟨yo, -, -, -, hg⟩ := _root_.GlobalTheory.UCanon.OpenPart.openCls Xo c φ V hV C
  let A := Localization.Away (∏ i, C.s i)
  let e : V ≃ₐ[V] A := IsLocalization.atUnit V A (∏ i, C.s i) (by rw [hprod]; exact isUnit_one)
  let h : A →+* V := e.symm.toRingEquiv.toRingHom
  have hcomp : h.comp (algebraMap V A) = RingHom.id V := by
    ext r
    show e.symm (algebraMap V A r) = r
    exact e.symm.commutes r
  have hid : spMap h ≫ spMap (algebraMap V A) = 𝟙 _ := by
    show Spec.map _ ≫ Spec.map _ = _
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, hcomp]
    exact Spec.map_id _
  have hψ : jK V ≫ spMap h ≫ yo = C.y := by
    rw [← Category.assoc]
    exact hg _ (by rw [Category.assoc, hid, Category.comp_id])
  have hgen : jK V ≫ (spMap h ≫ yo) ≫ j = jK V ≫ ξV := by
    rw [← Category.assoc, hψ, hy]
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have heq : (spMap h ≫ yo) ≫ j = ξV :=
    ext_of_isDominant_of_isSeparated s (hs _ _ hgen) (jK V) hgen
  exact hx ⟨(spMap h ≫ yo) (closedPoint V), by
    show ((spMap h ≫ yo) ≫ j) (closedPoint V) = _
    rw [heq]⟩

end GlobalTheory.UChartGeo

namespace GlobalTheory.UChartGeo


set_option maxHeartbeats 1000000 in
theorem exists_monoFam_algClosed : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Geo.Tor.Level H} (Xo : Moduli Dw l) (c : Coeff l) (φ : InvFun (𝓞 E)), 1 ≤ Dw.p + Dw.q → IsPolFan H.bar (min Dw.p Dw.q) φ → NoSelfInt H.bar (min Dw.p Dw.q) φ → ∀ {Z : Scheme.{0}} (zs : Z ⟶ Sp c.F) (i : Xo.XF c ⟶ Z) (OZ : LB Z) (N d : ℕ) (J : Z.IdealSheafData) {S : Scheme.{0}} (π : S ⟶ Z) (j : Xo.XF c ⟶ S) [IsOpenImmersion j] (BD : GlobalTheory.EffCartierData S), GlobalTheory.UPoinc.UPoinOnX Xo c φ zs i OZ N d J π j BD → SepB Xo c φ j → ∀ x : S, x ∉ Set.range j → ∃ (V : Type) (_ : CommRing V) (_ : IsDomain V) (_ : IsLocalRing V) (C : MonoFam Xo c φ V) (ξV : Sp V ⟶ S), GlobalTheory.Mum.Base V ∧ IsAlgClosed (ResidueField V) ∧ Nontrivial C.P.D.toPre.X ∧ C.y ≫ j = jK V ≫ ξV ∧ ξV (closedPoint V) = x := by
  intro E _ _ _ H Dw l Xo c φ hpq hpf hns Z zs i OZ N d J S π j _ BD hU hS x hx
  obtain ⟨V, _, _, _, C, ξV, hV, hy, hxV⟩ :=
    GlobalTheory.UChartTrait.exists_monoFam_through Xo c φ hpq hpf hns zs i OZ N d J π j BD hU hS x hx
  obtain ⟨Nn, ιP, hci, hι⟩ := hU.2.2.2.2.1.2.1
  haveI : IsSeparated (π ≫ zs) := by rw [← hι]; infer_instance
  haveI : IsDominant (jK V) := (GlobalTheory.Mum.Modif.self V).dominant
  have hs : ∀ f g : Sp V ⟶ S, jK V ≫ f = jK V ≫ g → f ≫ π ≫ zs = g ≫ π ≫ zs := fun f g hfg =>
    ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) (jK V) (by
      rw [← Category.assoc, hfg, Category.assoc])
  have hX : Nontrivial C.P.D.toPre.X :=
    nontrivial_of_not_mem_range hV C (π ≫ zs) j ξV hs hy (hxV ▸ hx)
  obtain ⟨y0, hy0⟩ := exists_ne (0 : C.P.D.toPre.X)
  obtain ⟨i0, -⟩ := C.mono.exists_pos (maximalIdeal.isMaximal _).ne_top hy0
  have hnf : ¬ IsField V := by
    intro hf
    have hm := C.s_mem i0
    rw [(IsLocalRing.isField_iff_maximalIdeal_eq).1 hf, Ideal.mem_bot] at hm
    exact C.s_ne_zero i0 hm
  haveI : IsNoetherianRing V := hV.1.1
  haveI : CharZero V := hV.2
  obtain ⟨W, _, _, _, ρ, hcomp, hac, hinj, hloc⟩ := _root_.GlobalTheory.CompleteClosedDvr.exists_complete_dvr_isAlgClosed V hnf ⟨C.b.comp (algebraMap ℚ c.F)⟩
  haveI : CharZero W := charZero_of_injective_ringHom hinj
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible W
  have hne : ∀ k, ρ (C.s k) ≠ 0 := fun k h0 => C.s_ne_zero k (hinj (h0.trans (map_zero ρ).symm))
  choose w u hwu using fun k => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible (hne k) hϖ
  have hW : GlobalTheory.UU.CDVR W := ⟨inferInstance, hcomp, inferInstance⟩
  obtain ⟨t, P, e, be, -, htK, hbe, -, hmono, -⟩ := trait_pull C hV W hW ϖ ρ hinj hloc w u hwu
  have hinj' : Function.Injective ((algebraMap W (FractionRing W)).comp ρ) :=
    (IsFractionRing.injective W (FractionRing W)).comp hinj
  obtain ⟨gam, hgam⟩ : ∃ gam : FractionRing V →+* FractionRing W,
      gam.comp (algebraMap V (FractionRing V)) = (algebraMap W (FractionRing W)).comp ρ :=
    ⟨IsFractionRing.lift hinj', RingHom.ext fun r => by
      rw [RingHom.comp_apply, RingHom.comp_apply]; exact IsFractionRing.lift_algebraMap hinj' r⟩
  have hκ : spMap gam ≫ jK V = jK W ≫ spMap ρ := by
    show Spec.map _ ≫ Spec.map _ = Spec.map _ ≫ Spec.map _
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp, hgam]
  obtain ⟨tK, h1, h2⟩ := htK (spMap gam) hκ
  have hover : (spMap gam ≫ C.y) ≫ pullback.snd _ _ = jK W ≫ spMap (ρ.comp C.b) := by
    rw [Category.assoc, C.y_over, ← Category.assoc, hκ, Category.assoc]
    congr 1
    exact (Spec.map_comp (CommRingCat.ofHom C.b) (CommRingCat.ofHom ρ)).symm
  let F : Fam Xo c W := ⟨ρ.comp C.b, t, P, spMap gam ≫ C.y, hover, ⟨tK, h1, h2⟩⟩
  let β : LinearMap.BilinForm ℤ P.D.toPre.X := ∑ k, (w k : ℤ) • pull e.toLinearMap (C.δ k)
  have hβ : β ∈ balForms H.bar P.D.toPre.X :=
    Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (pull_mem _ (C.cone.mem k))
  have hbeq : be = (l.M' : ℤ) • β := by
    rw [hbe, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ext a b
    simp only [LinearMap.smul_apply, pull_apply, smul_eq_mul]
    ring
  have hmono' : IsMonomial F.P.D.toPre ![ϖ] ![(l.M' : ℤ) • β] := hbeq ▸ hmono
  have hϖm : ϖ ∈ maximalIdeal W := (mem_maximalIdeal _).2 hϖ.not_isUnit
  obtain ⟨C', hC'⟩ := F.exists_monoFam hpf hϖm hβ hmono'
  have hyC : C'.toFam.y = spMap gam ≫ C.y := by rw [hC']
  refine ⟨W, inferInstance, inferInstance, inferInstance, C', spMap ρ ≫ ξV,
    ⟨⟨inferInstance, inferInstance, inferInstance, hcomp⟩, inferInstance⟩, hac, ?_, ?_, ?_⟩
  · rw [hC']
    exact e.symm.injective.nontrivial
  · show C'.toFam.y ≫ j = _
    rw [hyC, Category.assoc, hy, ← Category.assoc, hκ, Category.assoc]
  · show ξV (spMap ρ (closedPoint W)) = x
    have hcl : spMap ρ (closedPoint W) = closedPoint V := IsLocalRing.comap_closedPoint ρ
    rw [hcl, hxV]

end GlobalTheory.UChartGeo
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivTorsion
section
noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

namespace GlobalTheory.GSep

theorem exists_div_torsion : ∀ (X₁ : GlobalTheory.GSep.GSet) (z : X₁.M.Z) (k : ℕ), 2 ≤ k → k ∣ X₁.S.r * X₁.S.N →
    ∃ a : X₁.S.Gam, k • a = 0 ∧ X₁.M.Div X₁.S.th a z := by
  intro X z₀ k hk hd
  haveI := X.M.qc
  haveI : CompactSpace X.M.Z := QuasiCompact.compactSpace_of_compactSpace X.M.s
  obtain ⟨z, hz', hcl⟩ := (isClosed_closure (s := {z₀})).exists_closed_singleton ⟨z₀, subset_closure rfl⟩
  have hsp : z₀ ⤳ z := specializes_iff_mem_closure.2 hz'
  obtain ⟨U, hne, hU⟩ := _root_.GlobalTheory.GSep.exists_opens_R_le_O X
  obtain ⟨p, _, y, hy, hyU⟩ := exists_cen_main _ _ X.M z hcl U hne
  obtain ⟨hL, hL2⟩ := GlobalTheory.abelianSchemeLaws_all
  obtain ⟨hTU, hUT⟩ := GlobalTheory.ZH.thmU_and_uTors
  have hle : X.S.R ≤ X.M.O ((gPt p ≫ y) (closedPoint (PadicAlgCl p))) := hU _ (hyU ⟨_, rfl⟩)
  have hsw : ∀ w, (gPt p ≫ y) w ⤳ (gPt p ≫ y) (closedPoint (PadicAlgCl p)) := fun w => by
    rw [Subsingleton.elim w (closedPoint (PadicAlgCl p))]
  let y₀ : X.S.R →+* PadicAlgCl p :=
    (RatModel.valHomOf (gPt p ≫ y) _ hsw).comp (Subalgebra.inclusion hle).toRingHom
  have hy₀ : ∀ a : X.S.R, y₀ a = X.M.val (gPt p ≫ y) a := fun _ => rfl
  have hint : ∀ a : X.o₁, ‖y₀ (algebraMap X.o₁ X.S.R a)‖ ≤ 1 := fun a => by
    rw [hy₀]
    exact RatModel.norm_val_le_one hy ((X.M.O z).algebraMap_mem a)
  obtain ⟨u, l, τ, hτ, -⟩ :=
    (hasTests_of_real GlobalTheory.SS.semistableReductionSt hTU hL hL2 hUT X.o₁ X.Ω₁ X.S X.ρ).2 p y₀ ∅ hint
  have hq : ∀ w, 0 ≤ l.q w := fun w => by
    obtain ⟨e, he, -⟩ := hτ
    have h := τ.q_nonneg (e.symm w)
    rwa [he, AddEquiv.apply_symm_apply] at h
  obtain ⟨sc, h0, h₁, -, h₃⟩ := TestVal.exists_scale hL hL2 u l hint
  have hδ := (GlobalTheory.UnitTheta.closure_unit_theta hL hL2 hUT _ _ _ X.ρ p y₀ u l hint).1
  have hle' : ∀ a, ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ ≤ sc := fun a => by
    obtain ⟨w, -, hw⟩ := h₁ a
    exact hw.trans (mul_le_of_le_one_right h0 (Real.exp_le_one_iff.2 (neg_nonpos.2 (div_nonneg (hq w) (by positivity)))))
  have hsc : 0 < sc := hδ.trans_le (Real.iSup_le hle' h0)
  obtain ⟨a, -, ha, hn⟩ := h₃ k hk hd 0 (zero_mem _)
  refine ⟨a, by simpa using ha, RatModel.Div.of_specializes ?_ hsp⟩
  obtain ⟨d, hdv⟩ := X.div z
  refine (hdv.div_iff_isUnit a).2 ((RatModel.norm_val_eq_one_iff hy (hdv.2 a)).1 ?_)
  have hs := RatModel.gPt_specializes hy
  have e : ‖y₀ ⟨X.S.th a, X.S.th_mem a⟩‖ =
      ‖y₀ ⟨X.S.th d, X.S.th_mem d⟩‖ * ‖X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)‖ := by
    rw [hy₀, hy₀, ← norm_mul, ← RatModel.val_mul hsw (hle (X.S.th_mem d))
      (RatModel.O_le_of_specializes (hs _) (hdv.2 a))]
    congr 2
    have := hdv.1
    field_simp
  have b₁ := RatModel.norm_val_le_one hy (hdv.2 a)
  have b₂ := hle' d
  refine le_antisymm b₁ (not_lt.1 fun hlt => ?_)
  have := mul_le_mul_of_nonneg_right b₂ (norm_nonneg (X.M.val (gPt p ≫ y) (X.S.th a / X.S.th d)))
  nlinarith

end GlobalTheory.GSep
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDivisorMulIntegralUnitFiniteAdelesAwayP
section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.AV GlobalTheory.AV.AbVar GlobalTheory.PDivGroup GlobalTheory.Dieu GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKMid GlobalTheory.LKGeo GlobalTheory.LKRes
open ReciprocityTheory.DiscreteGroups.LocalClassField
open scoped TensorProduct

namespace GlobalTheory.AfUnitSplit

theorem isInt_add' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a + b) := fun v => by
  rw [map_add]; exact add_mem (ha v) (hb v)

theorem isInt_sub' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a - b) := fun v => by
  rw [map_sub]; exact sub_mem (ha v) (hb v)

theorem isInt_mul' {p : ℕ} {a b : AfP p} (ha : IsIntAf a) (hb : IsIntAf b) : IsIntAf (a * b) := fun v => by
  rw [map_mul]; exact mul_mem (ha v) (hb v)

theorem isInt_intCast' {p : ℕ} (k : ℤ) : IsIntAf (k : AfP p) := fun v => by
  rw [map_intCast]; exact intCast_mem _ k

theorem exists_dvd_mul_unit : ∀ (p : ℕ) [Fact p.Prime] (a b : AfP p) (K : ℕ), 0 < K → K.Coprime p → IsIntAf a →
    IsIntAf b → a * b = (K : AfP p) → ∃ (c : ℕ) (ε ε' : AfP p), c.Coprime p ∧ c ∣ K ∧ IsIntAf ε ∧ IsIntAf ε' ∧
      ε * ε' = 1 ∧ a = (c : AfP p) * ε := by
  intro p _ a b K hK hKp ha hb hab
  obtain ⟨m₀, β, hβ, e⟩ := LaHatMod.exists_int_add_mul K hK hKp a ha
  have hgpos : 0 < Int.gcd m₀ (K : ℤ) := Int.gcd_pos_of_ne_zero_right _ (by exact_mod_cast hK.ne')
  obtain ⟨g, a₀, K₀, hg, hcop, hm, hKe⟩ := Int.exists_gcd_one' hgpos
  have hgK : g ∣ K := by
    have : (g : ℤ) ∣ (K : ℤ) := ⟨K₀, by rw [hKe]; ring⟩
    exact_mod_cast this
  have hgp : g.Coprime p := Nat.Coprime.coprime_dvd_left hgK hKp
  have hbez : (1 : ℤ) = a₀ * Int.gcdA a₀ K₀ + K₀ * Int.gcdB a₀ K₀ := by
    rw [← Int.gcd_eq_gcd_ab, hcop]; rfl
  set s := Int.gcdA a₀ K₀
  set t := Int.gcdB a₀ K₀
  have hbez' : (1 : AfP p) = (a₀ : AfP p) * s + (K₀ : AfP p) * t := by
    have := congrArg (Int.cast : ℤ → AfP p) hbez; push_cast at this; exact this
  have hKc : (K : AfP p) = (K₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hKe; push_cast at this; exact this
  have hmc : (m₀ : AfP p) = (a₀ : AfP p) * (g : AfP p) := by
    have := congrArg (Int.cast : ℤ → AfP p) hm; push_cast at this; exact this
  have hgq : (g : ℚ) ≠ 0 := by exact_mod_cast hg.ne'
  set u := algebraMap ℚ (AfP p) (g : ℚ)⁻¹
  have hu : (g : AfP p) * u = 1 := by
    rw [← map_natCast (algebraMap ℚ (AfP p)), ← map_mul, mul_inv_cancel₀ hgq, map_one]
  have ha' : a = (g : AfP p) * ((a₀ : AfP p) + (K₀ : AfP p) * β) := by
    rw [e, hmc, hKc]; ring
  have hεb : ((a₀ : AfP p) + (K₀ : AfP p) * β) * b = (K₀ : AfP p) := by
    linear_combination (-(((a₀ : AfP p) + (K₀ : AfP p) * β) * b - (K₀ : AfP p))) * hu + u * hab
      - u * b * ha' + u * hKc
  refine ⟨g, (a₀ : AfP p) + (K₀ : AfP p) * β, (s : AfP p) - b * ((s : AfP p) * β - t), hgp, hgK,
    isInt_add' (isInt_intCast' _) (isInt_mul' (isInt_intCast' _) hβ),
    isInt_sub' (isInt_intCast' _) (isInt_mul' hb (isInt_sub' (isInt_mul' (isInt_intCast' _) hβ) (isInt_intCast' _))),
    ?_, ha'⟩
  linear_combination (-((s : AfP p) * β - t)) * hεb - hbez'

end GlobalTheory.AfUnitSplit
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFiniteUnramifiedRepresentingPolarizedHomsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_finite_unramified_representing_polarizedHoms : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (A B : Over S) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → Out.Rigidified A L → Out.Rigidified B M → Out.RelAmple A L → Out.RelAmple B M → ∃ R : HomFixRep A B L M, IsFinite R.π ∧ FormallyUnramified R.π := by
  first | (exact @GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified) | (exact GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified) | (intros; apply GlobalTheory.EndLoc.HomFixFinite.exists_finite_unramified  <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsometryKernelCoisotropicMod
section
noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.LowDat GlobalTheory.LowFilt

theorem GlobalTheory.LowFilt.exists_isometry_kerIs : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} (D : Datum H) {X : Type} [AddCommGroup X] [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X]
    (y : D.La →ₗ[𝓞 E] X) (n N : ℕ), 0 < n → N ∣ n → Cois D y n → ∀ Z Z' : Submodule (𝓞 E) D.La, IsOpp D Z Z' →
    Module.finrank (𝓞 E) Z = Module.finrank (𝓞 E) X →
    (∀ a, (∃ e, y a = N • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + N • e) →
    (∀ x, ∃ b ∈ Z', ∃ e, y b = x + n • e) →
    ∃ g : D.La ≃ₗ[𝓞 E] D.La, (∀ a b, D.EF (g a) (g b) = D.EF a b) ∧ (∀ a, ∃ e, g a = a + N • e) ∧
      ∀ a, (∃ e, y (g a) = n • e) ↔ ∃ b ∈ perp D Z, ∃ e, a = b + n • e := by
  intro E _ _ _ H D X _ _ _ _ y n N hn hNn hC Z Z' h hrk hN hon
  have hN0 : 0 < N := Nat.pos_of_dvd_of_pos hNn hn
  have hinj := _root_.GlobalTheory.LowFilt.inj_mod_of_surj_mod D y n hn Z Z' h hrk hon
  obtain ⟨σ, hσZ', hσid, hσy, hσN⟩ := _root_.GlobalTheory.LowFilt.exists_cell_section D y n N hn hNn Z Z' h hN hon
  obtain ⟨w, hw⟩ := exists_adjoint D σ
  obtain ⟨t, ht, hiso, hdvd⟩ := _root_.GlobalTheory.LowFilt.exists_shear_of_adjoint D y n N hn hNn hC Z Z' h σ w hσZ' hσid hσy hσN hw hinj
  have ht' : ∀ z : Z, t z - z ∈ perp D Z' := fun z => by
    obtain ⟨e, he, hze⟩ := ht z
    rw [hze, add_sub_cancel_left]
    exact (perp D Z').nsmul_mem he N
  have hker := _root_.GlobalTheory.LowFilt.ker_mod_eq_perp_range_add D y n hn Z Z' h hon t ht' hiso hdvd
  obtain ⟨g, hg, hgN, hgt⟩ := GlobalTheory.T.exists_isometry_extending_isotropic_shear D N hN0 Z Z' h t ht hiso
  refine ⟨equivOfIsometry D g hg, hg, hgN, fun a => ?_⟩
  simp only [equivOfIsometry_apply]
  rw [hker (g a)]
  constructor
  · rintro ⟨b, hb, e, he⟩
    set G := equivOfIsometry D g hg
    have hG : ∀ x, G x = g x := fun x => rfl
    refine ⟨G.symm b, fun z hz => ?_, G.symm e, ?_⟩
    · have := hb (t ⟨z, hz⟩) ⟨⟨z, hz⟩, rfl⟩
      rw [← hgt ⟨z, hz⟩, ← G.apply_symm_apply b, hG, hg] at this
      exact this
    · apply G.injective
      rw [map_add (f := _), map_nsmul, G.apply_symm_apply, G.apply_symm_apply, hG, he]
  · rintro ⟨b, hb, e, rfl⟩
    refine ⟨g b, ?_, g e, by rw [map_add (f := _), map_nsmul]⟩
    rintro _ ⟨z, rfl⟩
    rw [← hgt z, hg]
    exact hb z z.2
end
end

