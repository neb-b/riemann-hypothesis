module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0331
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0418
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0388
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0263
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0014
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0426
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0387
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0379
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0007
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0004
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0188
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0159
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0246
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0325
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0372
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0213
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0424
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0061
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0197

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinOEStabilityProperties
section
noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.OEStable

variable {l : ℕ} [hl : Fact l.Prime]

theorem perfect_Cb : PerfectRing (Cb l) l := by
  refine PerfectRing.ofSurjective _ _ fun x => ?_
  obtain ⟨a, b, hb, rfl⟩ := IsFractionRing.div_surjective (A := OCb l) x
  refine ⟨algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm a) /
    algebraMap _ _ ((frobeniusEquiv (OCb l) l).symm b), ?_⟩
  rw [frobenius_def, div_pow, ← map_pow (algebraMap (OCb l) (Cb l)),
    ← map_pow (algebraMap (OCb l) (Cb l)), frobeniusEquiv_symm_pow_p,
    frobeniusEquiv_symm_pow_p]

theorem eq_zero_of_forall_dvd (z : WCb l) (h : ∀ n, ((l : ℕ) : WCb l) ^ n ∣ z) : z = 0 := by
  ext m
  obtain ⟨y, hy⟩ := h (m + 1)
  rw [hy, mul_comm, WittVector.mul_pow_charP_coeff_zero _ (Nat.lt_succ_self m)]
  simp

private theorem sigmaA_eq_map_pt (g : GQ l) (a : Ainf l) : Per.σA g a = WittVector.map (Per.σF g) a := by
  apply GlobalTheory.Prism.inclW_injective
  rw [← galW_inclW]
  exact WittVector.ext fun n => autCb_alg l (galTilt l g) (a.coeff n)

variable {K : FinExt l} (bk : BK K)

theorem sat (w : WCb l) (hw : ((l : ℕ) : WCb l) * w ∈ bk.OE) : w ∈ bk.OE := by
  haveI := perfect_Cb (l := l)
  obtain ⟨ek, pr, hek, hinj, -, -⟩ := GlobalTheory.T.exists_residueTilt_injective_retract l K bk
  intro n
  obtain ⟨m, s, y, h⟩ := hw (n + 1)
  have h0 : (bk.evW s).coeff 0 = 0 := by
    have e : bk.evW s = (bk.evW X ^ m * w - ((l : ℕ) : WCb l) ^ n * y) * ((l : ℕ) : WCb l) := by
      linear_combination -h
    rw [e, WittVector.mul_charP_coeff_zero]
  have h1 : (bk.ev s).coeff 0 = 0 := by
    have e : (bk.evW s).coeff 0 = algebraMap (OCb l) (Cb l) ((bk.ev s).coeff 0) := WittVector.map_coeff _ _ _
    rw [e] at h0
    exact IsFractionRing.injective (OCb l) (Cb l) (h0.trans (map_zero _).symm)
  have h2 : PowerSeries.map (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) s = 0 :=
    hinj (by rw [hek, h1, map_zero])
  have h3 : ∀ i, ∃ c : Wq l bk.a, coeff i s = ((l : ℕ) : Wq l bk.a) * c := fun i => by
    have h4 := congrArg (coeff i) h2
    rw [coeff_map, map_zero] at h4
    have h5 : coeff i s ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Fq l bk.a)) := h4
    rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h5
    exact h5
  choose c hc using h3
  have h5 : s = ((l : ℕ) : bk.S) * PowerSeries.mk c := by
    ext i
    rw [hc, ← map_natCast (C (R := Wq l bk.a)) l, coeff_C_mul, coeff_mk]
  refine ⟨m, PowerSeries.mk c, y, ?_⟩
  apply sub_eq_zero.1
  apply WittVector.eq_zero_of_p_mul_eq_zero
  rw [h5, map_mul, map_natCast] at h
  linear_combination h

theorem closed (w : WCb l) (h : ∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) : w ∈ bk.OE := by
  intro n
  obtain ⟨v, hv, z, hz⟩ := h n
  obtain ⟨m, s, y, hy⟩ := hv n
  exact ⟨m, s, y + bk.evW X ^ m * z, by linear_combination hy + bk.evW X ^ m * hz⟩

theorem frob (w : WCb l) (hw : w ∈ bk.OE) : frobW l w ∈ bk.OE := by
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have key : ∀ t : bk.S, frobW l (bk.evW t) = bk.evW (frobS l bk.a t) := fun t => by
    rw [BK.evW, RingHom.comp_apply, RingHom.comp_apply, frobW_inclW, bk.ev_frob]
  refine ⟨l * m, frobS l bk.a s, frobW l y, ?_⟩
  have h' := congrArg (frobW l) h
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, key, frobS_X] at h'
  rw [pow_mul]
  linear_combination h'

theorem gal (g : ↥(GK K)) (hg : bk.FixFlat g) (w : WCb l) (hw : w ∈ bk.OE) : galW l (g : GQ l) w = w := by
  obtain ⟨-, -, -, hflat, -, hcomp, -⟩ := _root_.GlobalTheory.BSP.AinfDiv.main l K bk
  haveI := (_root_.GlobalTheory.WittTeichComplete.main l (OCb l) bk.flat hflat hcomp).1
  have hteich : Per.σA (g : GQ l) (WittVector.teichmuller l bk.flat) = WittVector.teichmuller l bk.flat := by
    rw [sigmaA_eq_map_pt, WittVector.map_teichmuller]
    exact congrArg _ hg
  have hfix : (Per.σA (g : GQ l)).comp bk.ev = bk.ev := by
    refine ringHom_ext_of_sep _ _ (fun r => ?_) ?_ ?_
    · rw [RingHom.comp_apply, bk.ev_C, bk.gal_w]
    · rw [RingHom.comp_apply, bk.ev_X, hteich]
    · intro x hx
      rw [RingHom.comp_apply, bk.ev_X, hteich] at hx
      refine IsHausdorff.haus' (I := Ideal.span {WittVector.teichmuller l bk.flat}) x fun n => ?_
      simp only [SModEq.zero, smul_eq_mul, Ideal.mul_top, Ideal.span_singleton_pow, Ideal.mem_span_singleton]
      exact hx n
  have hW : ∀ t : bk.S, galW l (g : GQ l) (bk.evW t) = bk.evW t := fun t => by
    change galW l _ (inclW l (bk.ev t)) = inclW l (bk.ev t)
    rw [galW_inclW, ← RingHom.comp_apply (Per.σA _) bk.ev, hfix]
  obtain ⟨-, -, hu, -, -⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  apply sub_eq_zero.1
  apply eq_zero_of_forall_dvd
  intro n
  obtain ⟨m, s, y, h⟩ := hw n
  have h' := congrArg (galW l (g : GQ l)) h
  simp only [map_mul, map_add (f := _), map_pow, map_natCast, hW] at h'
  obtain ⟨u, hu'⟩ := hu.pow m
  have e : (u : WCb l) * (galW l (g : GQ l) w - w) =
      ((l : ℕ) : WCb l) ^ n * (galW l (g : GQ l) y - y) := by
    rw [hu']; linear_combination h' - h
  refine ⟨(↑u⁻¹ : WCb l) * (galW l (g : GQ l) y - y), ?_⟩
  calc galW l (g : GQ l) w - w = (↑u⁻¹ : WCb l) * ((u : WCb l) * (galW l (g : GQ l) w - w)) := by
        rw [← mul_assoc, Units.inv_mul, one_mul]
    _ = _ := by rw [e]; ring

theorem inv (w : WCb l) (hw : w ∈ bk.OE) (hu : IsUnit w) : ∃ w' ∈ bk.OE, w * w' = 1 := by
  haveI := perfect_Cb (l := l)
  obtain ⟨-, -, -, -, hinv⟩ := GlobalTheory.T.breuilKisin_OE_mod_prime_laurent_field l K bk
  obtain ⟨u, rfl⟩ := hu
  have hy : WittVector.constantCoeff (p := l) (R := Cb l) u ∈
      bk.OE.map (WittVector.constantCoeff (p := l) (R := Cb l)) := Subring.mem_map.2 ⟨u, hw, rfl⟩
  obtain ⟨v, hv, hvy⟩ := Subring.mem_map.1 (hinv _ hy)
  have hne : WittVector.constantCoeff (p := l) (R := Cb l) u ≠ 0 := by
    intro h0
    have h1 := congrArg (WittVector.constantCoeff (p := l) (R := Cb l)) u.mul_inv
    rw [map_mul, h0, zero_mul, map_one] at h1
    exact zero_ne_one h1
  have h1 : (u : WCb l) * v - 1 ∈ RingHom.ker (WittVector.constantCoeff (p := l) (R := Cb l)) := by
    rw [RingHom.mem_ker, RingHom.map_sub, map_mul, hvy, map_one, mul_inv_cancel₀ hne, sub_self]
  rw [WittVector.ker_constantCoeff, Ideal.mem_span_singleton] at h1
  obtain ⟨z, hz⟩ := h1
  have hz' : z ∈ bk.OE := sat bk z (by
    rw [← hz]; exact sub_mem (mul_mem hw hv) (one_mem _))
  have huv : (u : WCb l) * v = 1 - (-((l : ℕ) : WCb l) * z) := by linear_combination hz
  have hi : (↑u⁻¹ : WCb l) * u = 1 := Units.inv_mul u
  refine ⟨↑u⁻¹, closed bk _ fun n => ⟨v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i,
    mul_mem hv (sum_mem fun i _ => pow_mem (mul_mem (neg_mem (natCast_mem _ l)) hz') i),
    ⟨(↑u⁻¹ : WCb l) * (-z) ^ n, ?_⟩⟩, u.mul_inv⟩
  have hgeom := geom_sum_mul_neg (-((l : ℕ) : WCb l) * z) n
  have hq : (-((l : ℕ) : WCb l) * z) ^ n = ((l : ℕ) : WCb l) ^ n * (-z) ^ n := by
    rw [neg_mul, ← mul_neg, mul_pow]
  linear_combination (-(↑u⁻¹ : WCb l)) * hgeom - ((↑u⁻¹ : WCb l) * ∑ i ∈ Finset.range n,
    (-((l : ℕ) : WCb l) * z) ^ i) * huv + (v * ∑ i ∈ Finset.range n, (-((l : ℕ) : WCb l) * z) ^ i) * hi
    - (↑u⁻¹ : WCb l) * hq

theorem main : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K), (∀ w : WCb l, ((l : ℕ) : WCb l) * w ∈ bk.OE → w ∈ bk.OE) ∧ (∀ w : WCb l, (∀ n : ℕ, ∃ v ∈ bk.OE, ((l : ℕ) : WCb l) ^ n ∣ w - v) → w ∈ bk.OE) ∧ (∀ w ∈ bk.OE, frobW l w ∈ bk.OE) ∧ (∀ g : ↥(GK K), bk.FixFlat g → ∀ w ∈ bk.OE, galW l (g : GQ l) w = w) ∧ ∀ w ∈ bk.OE, IsUnit w → ∃ w' ∈ bk.OE, w * w' = 1 := by
  intro l _ K bk
  exact ⟨sat bk, closed bk, frob bk, fun g hg w hw => gal bk g hg w hw, inv bk⟩

end GlobalTheory.OEStable
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductFaithfullyFlatModAdicPo
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.EnvFF

theorem adI_map {l : ℕ} [Fact l.Prime] {R : Type} [CommRing R] {B B' : Obj l R} (f : Hom B B') (m : ℕ) :
    (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast,
    GlobalTheory.T.prism_hom_map_ideal_eq l R B B' f]

theorem ff_of_basis {R S : Type} [CommRing R] [CommRing S] (g : R →+* S) (ι : Type) [Nonempty ι]
    (h : letI := g.toAlgebra; Nonempty (Module.Basis ι R S)) : g.FaithfullyFlat := by
  letI := g.toAlgebra
  obtain ⟨b⟩ := h
  exact Module.FaithfullyFlat.of_linearEquiv _ _ b.repr

end GlobalTheory.BSP.EnvFF

open GlobalTheory.BSP.EnvFF

theorem GlobalTheory.BSP.envFF : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B : Obj l ↥(OL K)) (t p : B.A)
    (En : Env bk B t p) (m : ℕ), (qmap En.inl m).FaithfullyFlat := by
  intro l _ K bk B t p En m
  have hJ : (adI B ^ m).map En.inl.f = adI En.Q ^ m := adI_map En.inl m
  have e : qmap En.inl m = (Ideal.quotEquivOfEq hJ).toRingHom.comp
      (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map) := by
    refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    rfl
  have h2 : (Ideal.quotEquivOfEq hJ).toRingHom.FaithfullyFlat :=
    RingHom.FaithfullyFlat.of_bijective (Ideal.quotEquivOfEq hJ).bijective
  have h1 : (Ideal.quotientMap ((adI B ^ m).map En.inl.f) En.inl.f Ideal.le_comap_map).FaithfullyFlat := by
    haveI : Nonempty (Digits l) := ⟨⟨0, fun _ => (Fact.out : l.Prime).pos⟩⟩
    obtain ⟨b, -⟩ := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
    exact ff_of_basis _ (Digits l) ⟨b⟩
  rw [e]
  exact RingHom.FaithfullyFlat.stableUnderComposition _ _ h1 h2
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismCoproductIsPushoutBaseChange
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP

theorem isPushout_of_bases {R S R' S' : Type} [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    (f : R →+* S) (g : R →+* R') (g' : S →+* S') (f' : R' →+* S') (hc : g'.comp f = f'.comp g) {ι : Type} :
    letI := f.toAlgebra; letI := f'.toAlgebra
    ∀ (b : Module.Basis ι R S) (b' : Module.Basis ι R' S'), (∀ i, g' (b i) = b' i) →
      CategoryTheory.IsPushout (CommRingCat.ofHom f) (CommRingCat.ofHom g) (CommRingCat.ofHom g')
        (CommRingCat.ofHom f') := by
  letI := f.toAlgebra; letI := g.toAlgebra; letI := g'.toAlgebra; letI := f'.toAlgebra
  letI : Algebra R S' := (f'.comp g).toAlgebra
  intro b b' hb
  haveI : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun _ => rfl
  haveI : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq fun x => (RingHom.congr_fun hc x).symm
  have hbc : IsBaseChange R' (IsScalarTower.toAlgHom R S S').toLinearMap := by
    refine IsBaseChange.of_equiv ((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)) fun m => ?_
    have : (((Algebra.TensorProduct.basis R' b).equiv b' (Equiv.refl _)).toLinearMap.restrictScalars R ∘ₗ
        TensorProduct.mk R R' S 1) = (IsScalarTower.toAlgHom R S S').toLinearMap := b.ext fun i => by
      simp only [LinearMap.coe_comp, Function.comp_apply, TensorProduct.mk_apply,
        LinearMap.coe_restrictScalars, LinearEquiv.coe_coe, AlgHom.toLinearMap_apply,
        IsScalarTower.coe_toAlgHom']
      rw [← Algebra.TensorProduct.basis_apply, Module.Basis.equiv_apply, Equiv.refl_apply]
      exact (hb i).symm
    exact LinearMap.congr_fun this m
  haveI : Algebra.IsPushout R R' S S' := ⟨hbc⟩
  haveI : Algebra.IsPushout R S R' S' := Algebra.IsPushout.symm inferInstance
  exact CommRingCat.isPushout_of_isPushout R S R' S'

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem exists_basis_quot_of_map_eq {S A : Type} [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (J : Ideal A)
    (hJ : I.map s = J) (hle : I ≤ J.comap s) {ι : Type} (b₀ : ι → A)
    (h : letI := (Ideal.quotientMap (I.map s) s Ideal.le_comap_map).toAlgebra
      ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ I.map s), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i)) :
    letI := (Ideal.quotientMap J s hle).toAlgebra
    ∃ b : Module.Basis ι (S ⧸ I) (A ⧸ J), ∀ i, b i = Ideal.Quotient.mk _ (b₀ i) := by
  subst hJ
  exact h

theorem map_adI_pow {R : Type} [CommRing R] {l : ℕ} {B B' : Obj l R} (f : Hom B B') (hI : B.I.map f.f = B'.I)
    (m : ℕ) : (adI B ^ m).map f.f = adI B' ^ m := by
  rw [Ideal.map_pow, adI, adI, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

end GlobalTheory.BSP

namespace GlobalTheory.BSP

variable {l : ℕ} [hl : Fact l.Prime] {K : FinExt l}

theorem env_map_tb_b {bk : BK K} {B B' : Obj l ↥(OL K)} {t p : B.A} {k : Hom B B'} {En : Env bk B t p}
    {En' : Env bk B' (k.f t) (k.f p)} (k' : Hom En.Q En'.Q) (h1 : k'.comp En.inl = En'.inl.comp k)
    (h2 : k'.comp En.inr = En'.inr) (α : Digits l) : k'.f (En.tb.b α) = En'.tb.b α := by
  have hreg : En'.inl.f (k.f t) ∈ nonZeroDivisors En'.Q.A :=
    by
    haveI := En'.Q.inv
    exact mem_nonZeroDivisors_of_invertible_span_singleton _ _ (Module.Invertible.congr (LinearEquiv.ofEq _ _ En'.I_eq))
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  have e2 : k'.f (BK.hf En.inr X) = BK.hf En'.inr X := by
    have := congrArg (fun h => Hom.f h X) h2
    exact this
  have hw : k'.f En.w = En'.w := by
    have a1 := congrArg k'.f En.w_eq
    have a2 := En'.w_eq
    have a3 : k'.f (En.inl.f p + En.inl.f t * En.w) = En'.inl.f (k.f p) + En'.inl.f (k.f t) * k'.f En.w := by
      simp only [map_add (f := _), map_mul, e1]
    have : En'.inl.f (k.f t) * (k'.f En.w - En'.w) = 0 := by linear_combination -a3 - a1 + e2 + a2
    exact sub_eq_zero.1 ((mem_nonZeroDivisors_iff.1 hreg).2 _ (by rw [mul_comm]; exact this))
  have hδ : ∀ i : ℕ, k'.f (En.Q.D.δ^[i] En.w) = En'.Q.D.δ^[i] En'.w := fun i =>
    (Function.Semiconj.iterate_right (f := k'.f) k'.f_δ i En.w).trans (congrArg (En'.Q.D.δ^[i]) hw)
  calc k'.f (En.tb.b α) = k'.f (α.1.prod fun i n => (En.Q.D.δ^[i] En.w) ^ n) := congrArg k'.f (En.tb_b α)
    _ = α.1.prod fun i n => k'.f ((En.Q.D.δ^[i] En.w) ^ n) := map_finsuppProd k'.f _ _
    _ = α.1.prod fun i n => (En'.Q.D.δ^[i] En'.w) ^ n :=
      Finsupp.prod_congr fun i _ => (map_pow _ _ _).trans (congrArg (· ^ α.1 i) (hδ i))
    _ = En'.tb.b α := (En'.tb_b α).symm

end GlobalTheory.BSP

namespace GlobalTheory.BSP

theorem env_isPO : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (B B' : Obj l ↥(OL K)) (t p : B.A)
    (k : Hom B B') (En : Env bk B t p) (En' : Env bk B' (k.f t) (k.f p)),
    ∃ k' : Hom En.Q En'.Q, IsPO En.inl k k' En'.inl := by
  intro l _ K bk B B' t p k En En'
  obtain ⟨k', ⟨h1, h2⟩, -⟩ := En.univ En'.Q (En'.inl.comp k) En'.inr
  have e1 : ∀ a, k'.f (En.inl.f a) = En'.inl.f (k.f a) := fun a => by
    have := congrArg (fun h => Hom.f h a) h1
    exact this
  refine ⟨k', ⟨h1, fun m => ?_⟩⟩
  have q1 := map_adI_pow En.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B En.Q En.inl) m
  have q2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B.A En.Q.A En.inl.f (adI B) (Digits l) En.tb m
  have q3 := exists_basis_quot_of_map_eq En.inl.f (adI B ^ m) (adI En.Q ^ m) q1 (adI_pow_le En.inl m) En.tb.b q2
  obtain ⟨b, hb⟩ := q3
  have r1 := map_adI_pow En'.inl (GlobalTheory.T.prism_hom_map_ideal_eq l _ B' En'.Q En'.inl) m
  have r2 := GlobalTheory.T.adicTopologicalBasis_basis_mod_pow B'.A En'.Q.A En'.inl.f (adI B') (Digits l) En'.tb m
  have r3 := exists_basis_quot_of_map_eq En'.inl.f (adI B' ^ m) (adI En'.Q ^ m) r1 (adI_pow_le En'.inl m) En'.tb.b r2
  obtain ⟨b', hb'⟩ := r3
  refine isPushout_of_bases (qmap En.inl m) (qmap k m) (qmap k' m) (qmap En'.inl m) ?_ b b' fun α => ?_
  · refine Ideal.Quotient.ringHom_ext (RingHom.ext fun a => ?_)
    exact congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (e1 a)
  · exact (congrArg (qmap k' m) (hb α)).trans ((qmap_mk k' m _).trans
      ((congrArg (Ideal.Quotient.mk (adI En'.Q ^ m)) (env_map_tb_b k' h1 h2 α)).trans (hb' α).symm))

end GlobalTheory.BSP
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPrismGaloisLiftIsPrismHom
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.PrismTwist

variable {l : ℕ} [hl : Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : GlobalTheory.BKReal.PiSys l e)

theorem ev_injective : Function.Injective (ϖ.ev a) := by
  let Q := OCb l ⧸ Ideal.span {ϖ.flat}
  have hn : ¬ IsUnit ϖ.flat := fun h => ϖ.not_isUnit_teich (h.map (WittVector.teichmuller l))
  have : Nontrivial Q := Ideal.Quotient.nontrivial_iff.2 (by rwa [Ne, Ideal.span_singleton_eq_top])
  have : CharP Q l := (CharP.charP_iff_prime_eq_zero hl.out).2 (by
    rw [← map_natCast (Ideal.Quotient.mk _), CharP.cast_eq_zero, map_zero])
  let r : Ainf l →+* WittVector l Q := WittVector.map (Ideal.Quotient.mk _)
  have hr : Function.Injective (r.comp (wA l a).toRingHom) := fun x y h => WittVector.ext fun n =>
    ((Ideal.Quotient.mk (Ideal.span {ϖ.flat})).comp (Fq.val l a)).injective
      (congrArg (WittVector.coeff · n) h)
  have hR : r ϖ.teich = 0 := by
    change WittVector.map (Ideal.Quotient.mk _) (WittVector.teichmuller l ϖ.flat) = 0
    rw [WittVector.map_teichmuller, Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _),
      WittVector.teichmuller_zero]
  have ht : ϖ.teich ≠ 0 := fun h => by
    have := congrArg (fun w : Ainf l => w.coeff 0) h
    simp only [PiSys.teich, WittVector.teichmuller_coeff_zero, WittVector.zero_coeff] at this
    exact ϖ.flat_ne_zero this
  have key : ∀ n (x : (Wq l a)⟦X⟧), ϖ.ev a x = 0 → coeff n x = 0 := by
    have h0 : ∀ x : (Wq l a)⟦X⟧, ϖ.ev a x = 0 → constantCoeff x = 0 := fun x hx => by
      rw [x.eq_X_mul_shift_add_const, map_add (f := _), map_mul, PiSys.ev_X, PiSys.ev_C] at hx
      have h1 := congrArg r hx
      rw [map_add (f := _), map_mul, hR, zero_mul, zero_add, map_zero] at h1
      exact hr (h1.trans (map_zero _).symm)
    intro n
    induction n with
    | zero => exact fun x hx => by simpa using h0 x hx
    | succ n ih =>
      intro x hx
      have h1 := h0 x hx
      rw [x.eq_X_mul_shift_add_const, h1, map_zero, add_zero, map_mul, PiSys.ev_X] at hx
      have h2 := ih _ ((mul_eq_zero.1 hx).resolve_left ht)
      rw [coeff_mk] at h2
      exact h2
  refine (injective_iff_map_eq_zero _).2 fun x hx => PowerSeries.ext fun n => ?_
  rw [key n x hx, map_zero]

theorem σA_frobenius (g : GQ l) (x : Ainf l) :
    Per.σA g (WittVector.frobenius x) = WittVector.frobenius (Per.σA g x) := by
  rw [WittVector.frobenius_eq_map_frobenius]
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.sigA_coeff, WittVector.map_coeff, WittVector.map_coeff, GlobalTheory.RingIface.sigA_coeff,
    frobenius_def, frobenius_def, map_pow]

end GlobalTheory.BKGal.PrismTwist

theorem GlobalTheory.BKGal.PrismTwist.hom_restrict : ∀ {l : ℕ} [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (ϖ : PiSys l e) (g : GQ l) (σ : ↥(OL (ϖ.field a)) →+* ↥(OL (ϖ.field a))), (∀ x, (((σ x : ↥(ϖ.field a).1) : Om l)) = g ((x : ↥(ϖ.field a).1) : Om l)) → ∀ (ψ : (Wq l a)⟦X⟧ →+* (Wq l a)⟦X⟧), (∀ x, ϖ.ev a (ψ x) = Per.σA g (ϖ.ev a x)) → ∃ H : Hom (ϖ.prism a) ((ϖ.prism a).restrict σ), ∀ x, H.f x = ψ x := by
  intro l _ a e _ _ ϖ g σ hσ ψ hψ
  have hfrob : ∀ x, ψ (frobS l a x) = frobS l a (ψ x) := fun x =>
    GlobalTheory.BKGal.PrismTwist.ev_injective a ϖ (by
      rw [hψ, PiSys.ev_frobS, PiSys.ev_frobS, hψ, GlobalTheory.BKGal.PrismTwist.σA_frobenius])
  refine ⟨{ f := ψ
            f_δ := (deltaS l a).map_δ_of_map_φ (deltaS l a)
              (fun x hx => (mul_eq_zero.1 hx).resolve_left (l_ne_zero l a)) ψ hfrob
            f_I := fun (x : (Wq l a)⟦X⟧) hx => ?_
            f_str := fun r (x : (Wq l a)⟦X⟧) h => ?_ }, fun _ => rfl⟩
  · have hx' := Ideal.mem_span_singleton.1 hx
    refine Ideal.mem_span_singleton.2 ((ϖ.theta_ev_eq_zero_iff a (ψ x)).1 ?_)
    rw [hψ, GlobalTheory.RingBasics.θ_σA, (ϖ.theta_ev_eq_zero_iff a x).2 hx', map_zero]
  · apply ϖ.quotToOC_injective a
    change ϖ.quotToOC a (Ideal.Quotient.mk _ (ψ x)) = ϖ.quotToOC a (ϖ.strMap a (σ r))
    have h' : Ideal.Quotient.mk (Ideal.span {eis l a e}) x = ϖ.strMap a r := h
    rw [PiSys.quotToOC_mk, PiSys.quotToOC_strMap, hψ, GlobalTheory.RingBasics.θ_σA, ← PiSys.quotToOC_mk, h',
      PiSys.quotToOC_strMap]
    refine Subtype.ext ?_
    rw [GlobalTheory.RingIface.sigO_coe]
    change Per.σC g (((r : ↥(ϖ.field a).1) : Om l) : ℂ_[l]) = (((σ r : ↥(ϖ.field a).1) : Om l) : ℂ_[l])
    rw [hσ]
    exact GlobalTheory.RingBasics.σC_coe g _
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CompletionLinesOfLatticeAtLevels
section
noncomputable section

namespace GlobalTheory.SenLines.AllRoots

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.AdmLoc GlobalTheory.SenLines TensorProduct

theorem zeta_isPrimitiveRoot {l : ℕ} [Fact l.Prime] (P : LocPrime l) {s : ℕ} (hs : 1 ≤ s) :
    IsPrimitiveRoot (P.ζQ s) (l ^ s) := by
  obtain ⟨m, rfl⟩ : ∃ m, s = m + 1 := ⟨s - 1, by omega⟩
  have hpow : ∀ k, P.ζQ (k + 1) ^ l ^ k = P.ζQ 1 := by
    intro k
    induction k with
    | zero => simp
    | succ j ih => rw [pow_succ', pow_mul, P.ζQ_succ, ih]
  have h1 : ¬ P.ζQ (m + 1) ^ l ^ m = 1 := by rw [hpow]; exact P.ζQ_one
  have h2 : P.ζQ (m + 1) ^ l ^ (m + 1) = 1 := by
    rw [pow_succ, pow_mul, hpow, P.ζQ_succ, P.ζQ_zero]
  rw [← orderOf_eq_prime_pow h1 h2]
  exact IsPrimitiveRoot.orderOf _

theorem exists_isPt {l : ℕ} [Fact l.Prime] {P : LocPrime l} (H : LocHW l P)
    {K : FinExt l} {s : ℕ} {LL : FinExt l} (h : Good K s LL)
    (i : ZMod (Module.finrank ℚ_[l] ↥(K0 K))) (ζ : ↥LL.1) (hζ : IsPrimitiveRoot ζ (l ^ s)) :
    ∃ τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1, H.IsPt h i ζ τ := by
  have hs : 1 ≤ s := h.1
  have hLL := h.2.2.2
  have hprim := zeta_isPrimitiveRoot P hs
  have : NeZero (l ^ s) := ⟨(pow_pos (Fact.out : l.Prime).pos s).ne'⟩
  let Φ : Om l →ₐ[ℚ_[l]] Om l := ((H.W K s LL h).emb i).liftNormal (Om l)
  have hΦ : ∀ x : ↥(K0 K), Φ (x : Om l) = (((H.W K s LL h).emb i x : ↥LL.1) : Om l) := fun x =>
    AlgHom.liftNormal_commutes ((H.W K s LL h).emb i) (Om l) x
  have hζ' : IsPrimitiveRoot (ζ : Om l) (l ^ s) := hζ.map_of_injective (f := LL.1.val) Subtype.val_injective
  obtain ⟨a, -, ha⟩ := (hprim.map_of_injective (f := Φ) Φ.injective).eq_pow_of_pow_eq_one hζ'.pow_eq_one
  rw [← map_pow] at ha
  have hpa : IsPrimitiveRoot (P.ζQ s ^ a) (l ^ s) :=
    IsPrimitiveRoot.of_map_of_injective (f := Φ) (ha ▸ hζ') Φ.injective
  have hconj : IsConjRoot ↥(K0 K) (P.ζQ s ^ a) (P.ζQ s) := by
    unfold IsConjRoot
    rw [GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hprim, GlobalTheory.Cyc.minpoly_unramifiedSubfield_eq_cyclotomic K s hs _ hpa]
  obtain ⟨σ, hσ⟩ := hconj.exists_algEquiv
  let τ₀ : ↥(Ks K s) →ₐ[ℚ_[l]] Om l := (Φ.comp (σ.restrictScalars ℚ_[l]).toAlgHom).comp (Ks K s).val
  let τ : ↥(Ks K s) →ₐ[ℚ_[l]] ↥LL.1 := τ₀.codRestrict LL.1.toSubalgebra (hLL τ₀)
  have hτ : ∀ y : ↥(Ks K s), ((τ y : ↥LL.1) : Om l) = Φ (σ (y : Om l)) := fun _ => rfl
  refine ⟨τ, fun x y hxy => Subtype.ext ?_, fun y hy => Subtype.ext ?_⟩
  · rw [hτ, hxy, show σ (x : Om l) = x from σ.commutes x, hΦ]
  · rw [hτ, hy, hσ, ha]

end GlobalTheory.SenLines.AllRoots
end
end

