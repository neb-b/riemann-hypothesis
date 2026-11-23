module

public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TrivIsCr
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0229
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AcrisTorsionFreeComplete
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NilpotentOfNotIsUnit
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0334
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0343
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0340
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0337
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0350
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0336
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisTorsionFreeCompleteFrobeniusProperties
section
attribute [local irreducible] Formalism.Per.σC Formalism.Per.σO Formalism.Per.φA Formalism.Per.zA Formalism.Per.AinfP Formalism.Per.zP Formalism.Per.toC Formalism.Per.θP Formalism.Per.kerP Formalism.Per.ev Formalism.Per.FilP Formalism.Per.θD Formalism.Per.pD Formalism.Per.zD Formalism.Per.FilD Formalism.Per.Acris0 Formalism.Per.Acris Formalism.Per.Bcris Formalism.Per.aB Formalism.Per.a0B Formalism.Per.zB Formalism.Per.φB Formalism.Per.σF Formalism.Per.σA Formalism.Per.extP Formalism.Per.σDp Formalism.Per.σD Formalism.Per.σB Formalism.Per.IsLog

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

noncomputable section

namespace GlobalTheory.AcrisFrobE

open scoped Nat

theorem pow_mul_factorial_dvd (l : ℕ) (hl : 0 < l) : ∀ n : ℕ, l ^ n * n ! ∣ (l * n)!
  | 0 => by simp
  | n + 1 => by
    have ih := pow_mul_factorial_dvd l hl n
    have e : l * (n + 1) = (l * n + (l - 1)) + 1 := by rw [Nat.mul_succ]; omega
    have h2 : (l * n)! ∣ (l * n + (l - 1))! := Nat.factorial_dvd_factorial (by omega)
    have e2 : l ^ (n + 1) * (n + 1)! = (l * n + (l - 1) + 1) * (l ^ n * n !) := by
      rw [← e, Nat.factorial_succ, pow_succ]; ring
    rw [e2, e, Nat.factorial_succ]
    exact Nat.mul_dvd_mul_left _ (ih.trans h2)

theorem pow_succ_dvd_factorial (l : ℕ) (hl : 0 < l) : l ^ (l + 1) ∣ (l * l)! := by
  refine dvd_trans ?_ (pow_mul_factorial_dvd l hl l)
  rw [pow_succ]
  exact Nat.mul_dvd_mul_left _ (Nat.dvd_factorial hl le_rfl)

variable (l : ℕ) [Fact l.Prime]

theorem isUnit_natCast_ainfP (n : ℕ) (hn : n ≠ 0) : IsUnit (n : Formalism.Per.AinfP l) :=
  GlobalTheory.AcrisDiscExt.isUnit_natCast_of (l := l) ((algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l)).comp (Formalism.Per.zA l))
    (by
      have := IsLocalization.Away.algebraMap_isUnit (S := Formalism.Per.AinfP l) (l : Formalism.Per.Ainf l)
      simpa using this) n hn

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE
open scoped Nat
variable (l : ℕ) [Fact l.Prime]

theorem coe_natCast0 (k : ℕ) : ((k : Formalism.Per.Acris0 l) : Formalism.Per.AinfP l) = k :=
  map_natCast (Formalism.Per.Acris0 l).val k

theorem exists_dpow (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) (n : ℕ) :
    ∃ d : Formalism.Per.Acris0 l, ((n ! : ℕ) : Formalism.Per.AinfP l) * (d : Formalism.Per.AinfP l) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
  obtain ⟨u, hu⟩ := isUnit_natCast_ainfP l (n !) (Nat.factorial_ne_zero n)
  have key : ((n ! : ℕ) : Formalism.Per.AinfP l) *
      (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n * ((u⁻¹ : (Formalism.Per.AinfP l)ˣ) : Formalism.Per.AinfP l)) =
      algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x ^ n := by
    rw [← hu, mul_comm, mul_assoc, Units.inv_mul, mul_one]
  exact ⟨⟨_, GlobalTheory.RingIface.dividedPower_mem_Acris0 l x n _ hx key⟩, key⟩

theorem exists_div_l (x : Formalism.Per.Ainf l) (hx : Formalism.Per.θ l x = 0) :
    ∃ y w : Formalism.Per.Acris0 l, (l : Formalism.Per.Acris0 l) * y = algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) x ^ l ∧
      y ^ l = (l : Formalism.Per.Acris0 l) * w := by
  have hl0 : 0 < l := (Fact.out : l.Prime).pos
  set X := algebraMap (Formalism.Per.Ainf l) (Formalism.Per.AinfP l) x with hX
  obtain ⟨g, hg⟩ := exists_dpow l x hx l
  obtain ⟨d, hd⟩ := exists_dpow l x hx (l * l)
  obtain ⟨m, hm⟩ := pow_succ_dvd_factorial l hl0
  have e : l * (l - 1)! = l ! := Nat.mul_factorial_pred hl0.ne'
  refine ⟨(((l - 1)! : ℕ) : Formalism.Per.Acris0 l) * g, (m : Formalism.Per.Acris0 l) * d, ?_, ?_⟩
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_algebraMap, coe_natCast0,
      coe_natCast0, ← hX, ← hg, ← mul_assoc, ← Nat.cast_mul, e]
  · apply Subtype.ext
    rw [Subalgebra.coe_mul, Subalgebra.coe_mul, Subalgebra.coe_pow, Subalgebra.coe_mul, coe_natCast0,
      coe_natCast0, coe_natCast0]
    refine ((isUnit_natCast_ainfP l (l ^ l) (pow_ne_zero _ hl0.ne')).mul_right_inj).1 ?_
    have h1 : ((l ^ l : ℕ) : Formalism.Per.AinfP l) * ((((l - 1)! : ℕ) : Formalism.Per.AinfP l) * (g : Formalism.Per.AinfP l)) ^ l =
        X ^ (l * l) := by
      rw [pow_mul, ← hg, ← e, Nat.cast_mul, Nat.cast_pow, ← mul_pow]; ring
    rw [h1, ← hd, hm]
    push_cast; ring

end GlobalTheory.AcrisFrobE

namespace GlobalTheory.AcrisFrobE

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ x : Per.Acris l, (l : Per.Acris l) * x = 0 → x = 0) ∧ IsAdicComplete (Ideal.span {(l : Per.Acris l)}) (Per.Acris l) ∧ (∃ v : (Per.Acris l)ˣ, ((algebraMap (Ainf l) (Per.Acris l)).comp bk.ev) (frobS l bk.a bk.E) = (l : Per.Acris l) * v) ∧ (∀ a : Ainf l, phiA l ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (WittVector.frobenius a)) ∧ ∀ (g : GQ l) (a : Ainf l), sigA g ((algebraMap (Ainf l) (Per.Acris l)) a) = (algebraMap (Ainf l) (Per.Acris l)) (Per.σA g a) := by
  intro l _ K bk
  obtain ⟨htor, hcomp, -, -⟩ := GlobalTheory.Per.acris_basic l
  haveI := hcomp
  refine ⟨htor, hcomp, ?_, ?_, ?_⟩
  · obtain ⟨u, hu⟩ := bk.isUnit_δ
    have hφ : frobS l bk.a bk.E = bk.E ^ l + (l : bk.S) * (u : bk.S) := by
      rw [hu]; exact (deltaS l bk.a).φ_eq bk.E
    have hx : Formalism.Per.θ l (bk.ev bk.E) = 0 := by
      have h : bk.ev bk.E ∈ RingHom.ker (Formalism.Per.θ l) := bk.span_ev ▸ Ideal.mem_span_singleton_self _
      exact h
    obtain ⟨y, w, hy, hw⟩ := exists_div_l l _ hx
    set j := algebraMap (Formalism.Per.Acris0 l) (Formalism.Per.Acris l) with hj
    set a := algebraMap (Ainf l) (Formalism.Per.Acris l) with ha_def
    have ha : ∀ t, a t = j (algebraMap (Formalism.Per.Ainf l) (Formalism.Per.Acris0 l) t) :=
      fun t => GlobalTheory.RingIface.tower l t
    set A : Formalism.Per.Acris l := a (bk.ev (u : bk.S)) with hA
    have hAu : IsUnit A := (u.isUnit.map bk.ev).map a
    obtain ⟨U, hU⟩ := hAu
    set Y := j y with hY
    set z := ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) * Y with hz_def
    have hz : z ^ l ∈ Ideal.span {(l : Formalism.Per.Acris l)} := by
      rw [hz_def, mul_pow, show Y ^ l = (l : Formalism.Per.Acris l) * j w by rw [hY, ← map_pow, hw, map_mul, map_natCast]]
      exact Ideal.mul_mem_left _ _ (Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self _))
    have hJ : (-z) ^ l ∈ (⊥ : Ideal (Formalism.Per.Acris l)).jacobson := by
      refine IsAdicComplete.le_jacobson_bot (Ideal.span {(l : Formalism.Per.Acris l)}) ?_
      rw [neg_pow]; exact Ideal.mul_mem_left _ _ hz
    have h1 : IsUnit (1 - (-z) ^ l) := by
      have := Ideal.mem_jacobson_bot.1 hJ (-1)
      rwa [mul_neg_one, neg_add_eq_sub] at this
    have h2 : IsUnit (1 + z) := by
      rw [← mul_neg_geom_sum, sub_neg_eq_add] at h1
      exact isUnit_of_mul_isUnit_left h1
    obtain ⟨V, hV⟩ := h2
    refine ⟨U * V, ?_⟩
    have hUU : (U : Formalism.Per.Acris l) * ((U⁻¹ : (Formalism.Per.Acris l)ˣ) : Formalism.Per.Acris l) = 1 := U.mul_inv
    have hxl : a (bk.ev bk.E) ^ l = (l : Formalism.Per.Acris l) * Y := by
      rw [ha, ← map_pow, ← hy, map_mul, map_natCast]
    rw [RingHom.comp_apply, hφ, map_add (f := _), map_mul, map_pow, map_natCast, map_add (f := _), map_pow, map_mul, map_natCast, hxl,
      Units.val_mul, hV, hU, hz_def]
    rw [← hA]
    rw [hU] at hUU
    linear_combination (-(l : Formalism.Per.Acris l) * Y) * hUU
  · intro a
    rw [(GlobalTheory.CrisMaps.phiA_extends l).alg]
    congr 1
    ext n
    rw [GlobalTheory.RingIface.phiA_coeff l a n, WittVector.coeff_frobenius_charP]
  · intro g a
    rw [(GlobalTheory.CrisMaps.sigA_extends g).alg]

end GlobalTheory.AcrisFrobE
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdicTopologicalBasisBasisModPow
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

private theorem TopBasis.c_mem_of_mem_map_pow {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}
    (tb : TopBasis s I ι) (m : ℕ) (j : ι) {y : A} (hy : y ∈ (I ^ m).map s) : tb.c j y ∈ I ^ m := by
  suffices h : ∀ r : A, tb.c j (r * y) ∈ I ^ m by simpa using h 1
  refine Submodule.span_induction (p := fun y _ => ∀ r : A, tb.c j (r * y) ∈ I ^ m) ?_ ?_ ?_ ?_ hy
  · rintro _ ⟨a, ha, rfl⟩ r
    rw [mul_comm, tb.c_mul]
    exact Ideal.mul_mem_right _ _ ha
  · intro r; simp
  · intro x y _ _ hx hy r
    rw [mul_add, map_add (f := _)]
    exact Ideal.add_mem _ (hx r) (hy r)
  · intro a x _ hx r
    rw [smul_eq_mul, ← mul_assoc]
    exact hx (r * a)

theorem TopBasis.basis_mod_pow : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type)
    (tb : TopBasis s I ι) (m : ℕ), letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra;
    ∃ b : Module.Basis ι (S ⧸ I ^ m) (A ⧸ (I ^ m).map s), ∀ i, b i = Ideal.Quotient.mk _ (tb.b i) := by
  intro S A _ _ s I ι tb m
  letI := (Ideal.quotientMap ((I ^ m).map s) s Ideal.le_comap_map).toAlgebra
  have hsmul : ∀ (a : S) (x : A), (Ideal.Quotient.mk (I ^ m) a) • (Ideal.Quotient.mk ((I ^ m).map s) x)
      = Ideal.Quotient.mk ((I ^ m).map s) (s a * x) := by
    intro a x
    rw [Algebra.smul_def, RingHom.algebraMap_toAlgebra, Ideal.quotientMap_mk, map_mul]
  have hli : LinearIndependent (S ⧸ I ^ m) (fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rw [linearIndependent_iff']
    intro F g hg j hj
    choose h hh using fun i => Ideal.Quotient.mk_surjective (I := I ^ m) (g i)
    have hsum : (∑ i ∈ F, s (h i) * tb.b i) ∈ (I ^ m).map s := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [← Ideal.Quotient.eq_zero_iff_mem, map_sum, ← hg]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [← hh i, hsmul]
    have hc := tb.c_mem_of_mem_map_pow m j hsum
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum, Finset.sum_eq_single j] at hc
    · rw [tb.c_mul, tb.c_self, mul_one] at hc
      rw [← hh j]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr hc
    · intro i _ hij
      rw [tb.c_mul, tb.c_ne j i (Ne.symm hij), mul_zero]
    · intro h'; exact (h' hj).elim
  have hsp : ⊤ ≤ Submodule.span (S ⧸ I ^ m) (Set.range fun i => Ideal.Quotient.mk ((I ^ m).map s) (tb.b i)) := by
    rintro x -
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hF : ∀ i, i ∉ (tb.fin y m).toFinset → tb.c i y ∈ I ^ m := by
      intro i hi
      simpa using hi
    have hx := tb.approx y m (tb.fin y m).toFinset hF
    have : Ideal.Quotient.mk ((I ^ m).map s) y = ∑ i ∈ (tb.fin y m).toFinset,
        (Ideal.Quotient.mk (I ^ m) (tb.c i y)) • Ideal.Quotient.mk ((I ^ m).map s) (tb.b i) := by
      set_option synthInstance.maxHeartbeats 100000 in
        simp_rw [hsmul, ← map_sum]
      exact Ideal.Quotient.eq.mpr hx
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  exact ⟨Module.Basis.mk hli hsp, fun i => by simp⟩

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfAdicTopologicalBasisOverBreuilKisin
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.AinfTopBasis

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K),
    ∃ ι : Type, Nonempty (TopBasis bk.ev bk.J ι) := by
  intro l _ K bk
  obtain ⟨h0, hu, -, hJ⟩ := _root_.GlobalTheory.BSP.flat_disc l K bk
  obtain ⟨ι, b, i₀, hb, hspan, hind⟩ := _root_.GlobalTheory.BSP.BK.exists_residue_basis l K bk
  have he := bk.deg_pos
  have hstrict := _root_.GlobalTheory.BSP.strict_indep_pow bk.S (Ainf l) bk.ev (l : bk.S) X ι b
    (fun x hx => by
      rw [map_natCast, mul_comm] at hx
      exact WittVector.eq_zero_of_p_mul_eq_zero x hx)
    (fun x hx => by
      rw [map_natCast, ← Ideal.mem_span_singleton, ← WittVector.ker_constantCoeff, RingHom.mem_ker] at hx ⊢
      rw [map_mul, bk.ev_X, WittVector.constantCoeff_apply (x := WittVector.teichmuller l _),
        WittVector.teichmuller_coeff_zero] at hx
      exact (mul_eq_zero.1 hx).resolve_left h0) hind
  have hS : IsAdicComplete (Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}) bk.S := by
    have h := ReciprocityTheory.P1.isAdicComplete_comap_constantCoeff (Ideal.span {(l : Wq l bk.a)})
    rwa [← ReciprocityTheory.P1.map_C_sup_span_X, Ideal.map_span, Set.image_singleton, map_natCast] at h
  have hA : IsAdicComplete ((Ideal.span {(l : bk.S)} ⊔ Ideal.span {(X : bk.S)}).map bk.ev) (Ainf l) := by
    rw [← Ideal.span_insert, Ideal.map_span, Set.image_pair, map_natCast]
    refine (GlobalTheory.Per.AinfComplete.main l _ fun h => hu ?_).1
    have h2 := h.map (WittVector.constantCoeff (p := l) (R := OCb l))
    rwa [bk.ev_X, WittVector.constantCoeff_apply, WittVector.teichmuller_coeff_zero] at h2
  obtain ⟨TB, -⟩ := _root_.GlobalTheory.BSP.exists_topBasis_of_span_of_strict bk.S (Ainf l) bk.ev _ ι b i₀ hb
    (Submodule.FG.sup (Submodule.fg_span_singleton _) (Submodule.fg_span_singleton _)) hS hA hspan hstrict
  obtain ⟨TB', -⟩ := _root_.GlobalTheory.BSP.TopBasis.exists_of_pow_le_of_pow_le bk.S (Ainf l) bk.ev _ ι TB bk.J (1 + bk.Ep.natDegree) 1
    hS.toIsHausdorff (by omega) one_pos
    (by
      rw [← hJ]
      refine Ideal.sup_pow_add_le_pow_sup_pow.trans ?_
      rw [pow_one, Ideal.span_singleton_pow])
    (by
      rw [pow_one, ← hJ]
      refine sup_le_sup_left ?_ _
      rw [Ideal.span_singleton_le_span_singleton]
      exact dvd_pow_self _ he.ne')
  exact ⟨ι, ⟨TB'⟩⟩

end GlobalTheory.BSP.AinfTopBasis
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfEnvelopeModPrimeProperties
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem TopBasis.dvd_iff_dvd_coeff {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (p : S)
    (hp : ∀ (n : ℕ) (y : S), p * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n) (x : A) :
    s p ∣ x ↔ ∀ i, p ∣ tb.c i x := by
  obtain ⟨h0, -, h2⟩ := _root_.GlobalTheory.BSP.TopBasis.coeff_facts S A ι s I tb
  refine ⟨?_, fun h => ?_⟩
  · rintro ⟨y, rfl⟩ i
    exact ⟨_, tb.c_mul i p y⟩
  · choose a ha using h
    obtain ⟨y, hy⟩ := h2 hI a fun n => (tb.fin x (2 * n + 2)).subset fun i hi hi' =>
      hi (hp n _ (ha i ▸ hi'))
    refine ⟨y, sub_eq_zero.1 (h0 _ fun i => ?_)⟩
    rw [map_sub, tb.c_mul, hy, ha, sub_self]

theorem TopBasis.mod_props {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}
    (tb : TopBasis s I ι) (hI : IsHausdorff I S) (l : ℕ) (u : S)
    (hp : ∀ (n : ℕ) (y : S), (l : S) * y ∈ I ^ (2 * n + 2) → y ∈ I ^ n)
    (h1 : ∀ y : S, (l : S) * y = 0 → y = 0) (h2 : ∀ y : S, (l : S) ∣ u * y → (l : S) ∣ y)
    (h3 : ∀ y : S, (∀ m : ℕ, ∃ z, (l : S) ∣ y - u ^ m * z) → (l : S) ∣ y) :
    (∀ x : A, (l : A) * x = 0 → x = 0) ∧ (∀ x : A, (l : A) ∣ s u * x → (l : A) ∣ x) ∧
      ∀ x : A, (∀ m : ℕ, ∃ z, (l : A) ∣ x - s u ^ m * z) → (l : A) ∣ x := by
  have key := tb.dvd_iff_dvd_coeff hI (l : S) hp
  rw [← map_natCast s l]
  refine ⟨fun x hx => (_root_.GlobalTheory.BSP.TopBasis.coeff_facts S A ι s I tb).1 x fun i => h1 _ ?_, fun x hx => (key x).2 fun i => h2 _ ?_,
    fun x hx => (key x).2 fun i => h3 _ fun m => ?_⟩
  · rw [← tb.c_mul, hx, map_zero]
  · rw [← tb.c_mul]
    exact (key _).1 hx i
  · obtain ⟨z, hz⟩ := hx m
    refine ⟨tb.c i z, ?_⟩
    rw [← tb.c_mul, ← map_sub, map_pow]
    exact (key _).1 hz i

theorem env_ainf_mod : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (En : Env bk (ainfObj K) (bk.ev bk.E) (bk.ev X)), (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) * x = 0 → x = 0) ∧ (∀ x : En.Q.A, ((l : ℕ) : En.Q.A) ∣ En.inl.f (bk.ev X) * x → ((l : ℕ) : En.Q.A) ∣ x) ∧ ∀ x : En.Q.A, (∀ m : ℕ, ∃ z, ((l : ℕ) : En.Q.A) ∣ x - En.inl.f (bk.ev X) ^ m * z) → ((l : ℕ) : En.Q.A) ∣ x := by
  intro l _ K bk En
  obtain ⟨hp, h2, h3, -⟩ := _root_.GlobalTheory.BSP.AinfDiv.main l K bk
  exact En.tb.mod_props (ainfObj K).complete.toIsHausdorff l (bk.ev X) hp ainf_torsionFree h2 h3

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AinfPrincipalIdealSaturatedClosed
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory.AinfSat

section Coeff

variable {p : ℕ} [hp : Fact p.Prime] {R : Type*} [CommRing R] [CharP R p]

theorem coeff_pow_mul_add (r : ℕ) (w : WittVector p R) (i : ℕ) :
    (((p : WittVector p R) ^ r * w).coeff (i + r)) = (w.coeff i) ^ (p ^ r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    have h : (p : WittVector p R) ^ (r + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ r * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h, show i + (r + 1) = (i + r).succ by omega, WittVector.verschiebung_coeff_succ,
      WittVector.coeff_frobenius_charP, ih, ← pow_mul, pow_succ]

theorem coeff_pow_mul_lt (n : ℕ) (w : WittVector p R) :
    ∀ j, j < n → ((p : WittVector p R) ^ n * w).coeff j = 0 := by
  induction n with
  | zero => intro j hj; omega
  | succ n ih =>
    intro j hj
    have h : (p : WittVector p R) ^ (n + 1) * w
        = WittVector.verschiebung (WittVector.frobenius ((p : WittVector p R) ^ n * w)) := by
      rw [WittVector.verschiebung_frobenius]; ring
    rw [h]
    cases j with
    | zero => exact WittVector.verschiebung_coeff_zero _
    | succ j =>
      rw [WittVector.verschiebung_coeff_succ, WittVector.coeff_frobenius_charP, ih j (by omega),
        zero_pow hp.out.ne_zero]

theorem coeff_eq_of_dvd {n : ℕ} {u v : WittVector p R} (h : (p : WittVector p R) ^ n ∣ u - v)
    (j : ℕ) (hj : j < n) : u.coeff j = v.coeff j := by
  obtain ⟨w, hw⟩ := h
  have hz : WittVector.truncate n (u - v) = 0 := by
    ext k
    rw [WittVector.coeff_truncate, hw, coeff_pow_mul_lt n w k k.2]
    simp
  have ht : WittVector.truncate n u = WittVector.truncate n v := by
    rw [map_sub, sub_eq_zero] at hz; exact hz
  have := congrArg (TruncatedWittVector.coeff (⟨j, hj⟩ : Fin n)) ht
  simpa [WittVector.coeff_truncate] using this

end Coeff

variable (l : ℕ) [Fact l.Prime]

theorem exists_of_pow_eq (r : ℕ) (d : Cb l) (b : OCb l)
    (h : d ^ (l ^ r) = algebraMap (OCb l) (Cb l) b) : ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = d := by
  refine ⟨(iterateFrobeniusEquiv (OCb l) l r).symm b, ?_⟩
  apply iterateFrobenius_inj (Cb l) l r
  rw [iterateFrobenius_def, iterateFrobenius_def, h, ← map_pow]
  congr 1
  have := (iterateFrobeniusEquiv (OCb l) l r).apply_symm_apply b
  rwa [iterateFrobeniusEquiv_apply, iterateFrobenius_def] at this

theorem mem_range_of_pow_mul (r : ℕ) (y : WCb l)
    (hy : ∀ n : ℕ, ∃ a : Ainf l, (l : WCb l) ^ n ∣ (l : WCb l) ^ r * y - inclW l a) :
    ∃ a : Ainf l, y = inclW l a := by
  have hc : ∀ i, ∃ c : OCb l, algebraMap (OCb l) (Cb l) c = y.coeff i := by
    intro i
    obtain ⟨a, ha⟩ := hy (i + r + 1)
    have he := coeff_eq_of_dvd ha (i + r) (by omega)
    rw [coeff_pow_mul_add] at he
    exact exists_of_pow_eq l r _ _ (by rw [he]; exact WittVector.map_coeff _ _ _)
  choose c hc using hc
  refine ⟨WittVector.mk l c, ?_⟩
  ext i
  rw [show inclW l (WittVector.mk l c) = WittVector.map (algebraMap (OCb l) (Cb l)) (WittVector.mk l c)
    from rfl, WittVector.map_coeff]
  exact (hc i).symm

theorem mem_ideal_of_saturated : ∀ (l : ℕ) [Fact l.Prime] (ι : Ainf l), IsUnit (inclW l ι) →
    ∀ (r : ℕ) (x : WCb l), (∀ n : ℕ, ∃ a : Ainf l,
      (l : WCb l) ^ n ∣ (l : WCb l) ^ r * x - inclW l (ι * a)) →
    ∃ a : Ainf l, x = inclW l (ι * a) := by
  intro l _ ι hu r x hx
  obtain ⟨u, hu⟩ := hu
  obtain ⟨a, ha⟩ := mem_range_of_pow_mul l r (↑u⁻¹ * x) (by
    intro n
    obtain ⟨a, w, hw⟩ := hx n
    refine ⟨a, ↑u⁻¹ * w, ?_⟩
    have : (l : WCb l) ^ r * (↑u⁻¹ * x) - inclW l a
        = ↑u⁻¹ * ((l : WCb l) ^ r * x - inclW l (ι * a)) := by
      rw [map_mul, ← hu, mul_sub]
      rw [← mul_assoc (↑u⁻¹ : WCb l) (↑u) _, Units.inv_mul, one_mul]
      ring
    rw [this, hw]; ring)
  refine ⟨a, ?_⟩
  rw [map_mul, ← ha, ← hu, ← mul_assoc, Units.mul_inv, one_mul]

end GlobalTheory.AinfSat
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ApproxBdRPlusFilMatrixMul
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP GlobalTheory.MemLoc GlobalTheory.Pst GlobalTheory.BKLim GlobalTheory.Cong Matrix
open scoped Formalism.Per NNReal

namespace GlobalTheory

theorem use₁₀ : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (n d : ℕ) (X Z : Matrix (Fin d) (Fin d) (Per.BdRp l)), (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * X i j ∈ Per.FilP l n) → (∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * Z i j ∈ Per.FilP l n) → ∃ (k : ℕ) (s : Matrix (Fin d) (Fin d) bk.S), ∀ i j, aDp l (bk.ev (s i j)) - (l : Per.BdRp l) ^ k * (X * Z) i j ∈ Per.FilP l n := by
  intro l _ K bk n d X Z ⟨k₁, s₁, h₁⟩ ⟨k₂, s₂, h₂⟩
  refine ⟨k₁ + k₂, s₁ * s₂, fun i j => ?_⟩
  have e : aDp l (bk.ev ((s₁ * s₂) i j)) - (l : Per.BdRp l) ^ (k₁ + k₂) * (X * Z) i j
      = ∑ m, (aDp l (bk.ev (s₁ i m)) * (aDp l (bk.ev (s₂ m j)) - (l : Per.BdRp l) ^ k₂ * Z m j)
        + (aDp l (bk.ev (s₁ i m)) - (l : Per.BdRp l) ^ k₁ * X i m) * ((l : Per.BdRp l) ^ k₂ * Z m j)) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Matrix.mul_apply, Matrix.mul_apply, map_sum, map_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, map_mul, pow_add]
    ring
  rw [e]
  exact Ideal.sum_mem _ fun m _ => Ideal.add_mem _ (Ideal.mul_mem_left _ _ (h₂ m j)) (Ideal.mul_mem_right _ _ (h₁ i m))

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularSurjectionsOfFontaineTheoremStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.bcris_regular_surjections_of_fontaine_theorem : GlobalTheory.Published.FontaineBcris → ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → (∀ (K : FinExt l) (b : P.R.B), b ≠ 0 → (∀ g ∈ GK K, ∃ x : ℚ_[l], P.actQ g b = x • b) → IsUnit b) ∧ (∀ u : P.R.B, ∃ x, x - P.φB x = u) ∧ ∀ (K : FinExt l) (w : P.R.BdR), ∃ x : P.R.B, P.φB x = x ∧ P.ιB x - w ∈ (P.PD K).Fil 0 := by
  first | exact @GlobalTheory.MemLoc.TiedRegular.regular_onto | exact GlobalTheory.MemLoc.TiedRegular.regular_onto | (intros; apply GlobalTheory.MemLoc.TiedRegular.regular_onto <;> assumption)
end

