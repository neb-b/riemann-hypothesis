module

public import Mathlib
public import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
public import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0054
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0062
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0059
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0066
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0056
public import Development.AbelianVarietyTheory.CrystallinePeriods.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0053
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0067
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0063
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0057
public import Development.AbelianVarietyTheory.CrystallinePeriods.CrisMapsLoc

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FontaineTIsUnitBcrisAndUniformizerBdRPlus
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.MemLoc.TFil

variable {l : ℕ} [Fact l.Prime]

theorem alg_factor (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

theorem j_alg {j : Per.Acris l →+* Per.BdRp l} (hj : IsCrisP j) (a : Per.Ainf l) :
    j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
  rw [alg_factor, hj.on0]
  rfl

theorem mu_eq (e : Per.Fl l) :
    mu e = xi e * (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1) := by
  rw [xi, geom_sum_mul, ← map_pow, mu]
  congr 2
  rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]

theorem isUnit_mu {e : Per.Fl l} (he : IsEps e) :
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (mu e))) := by
  have h1 : e ≠ 1 := by
    rintro rfl
    exact he.2 (by rw [map_one, map_one])
  exact GlobalTheory.CrisLoc.unit_of_root l e he.1 h1

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem isUnit_l {e : Per.Fl l} (he : IsEps e) : IsUnit (l : Per.Bcris l) := by
  obtain ⟨w, hw, -⟩ := _root_.GlobalTheory.MemLoc.exists_mu_pow_div l e he.1
  have h0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) := by
    apply Subtype.ext
    simpa using hw
  have h1 := congrArg (fun x => algebraMap (Per.Acris l) (Per.Bcris l)
    (algebraMap (Per.Acris0 l) (Per.Acris l) x)) h0
  simp only [map_mul, map_natCast, map_pow, ← alg_factor] at h1
  have h2 := (isUnit_mu he).pow (l - 1)
  rw [← h1] at h2
  exact isUnit_of_mul_isUnit_left h2

theorem isUnit_cofactor {e : Per.Fl l} (he : IsEps e) :
    IsUnit (aDp l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm e) - 1)) := by
  obtain ⟨-, -, hu, hθ, -⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  apply hu
  rw [hθ, map_sub, map_one, WittVector.fontaineTheta_teichmuller]
  intro h
  apply he.2
  rw [← sub_eq_zero]
  exact Subtype.ext h

theorem fil_of_eq {e : Per.Fl l} (he : IsEps e) (y v : Per.BdRp l) (hv : IsUnit v)
    (hy : y = aDp l (xi e) * v) : y ∈ Per.FilP l 1 ∧ y ∉ Per.FilP l 2 := by
  obtain ⟨hF, hr, -, -⟩ := _root_.GlobalTheory.MemLoc.filtration_eq_xi_pow l e he
  obtain ⟨-, hk, -, -, -⟩ := _root_.GlobalTheory.MemLoc.thetaD_props l
  refine ⟨(hF 1 y).2 ⟨v, by rw [hy, pow_one]⟩, fun h => ?_⟩
  obtain ⟨c, hc⟩ := (hF 2 y).1 h
  have h1 : v - aDp l (xi e) * c = 0 := by
    apply hr
    rw [mul_sub, ← hy, hc]
    ring
  have h2 : v ∈ Per.FilP l 1 := (hF 1 v).2 ⟨c, by rw [pow_one]; exact sub_eq_zero.1 h1⟩
  exact (hv.map (Per.θD l)).ne_zero ((hk v).2 h2)

end GlobalTheory.MemLoc.TFil

namespace GlobalTheory.MemLoc
open TFil

set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem core_t_unit_fil : ∀ (l : ℕ) [Fact l.Prime], ∀ C : Core l,
    IsUnit (algebraMap (Per.Acris l) (Per.Bcris l) C.t) ∧ C.j C.t ∈ Per.FilP l 1 ∧
      C.j C.t ∉ Per.FilP l 2 ∧ IsUnit (l : Per.Bcris l) := by
  intro l _ C
  have he := _root_.GlobalTheory.MemLoc.core_isEps l C
  obtain ⟨t, u, ht, hu, htu⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l C.ε he.1
  have h1 : t = C.t := (_root_.GlobalTheory.MemLoc.LogFun.log_fun l C.ε C.t he.1 C.t_log).1 t ht
  rw [h1] at htu
  have h2 : C.j C.t = aDp l (xi C.ε) *
      (aDp l (Per.tm ((frobeniusEquiv (Per.Fl l) l).symm C.ε) - 1) * C.j u) := by
    rw [htu, map_mul, j_alg C.j_cris, mu_eq, map_mul, mul_assoc]
  have h3 := fil_of_eq he _ _ ((isUnit_cofactor he).mul (hu.map C.j)) h2
  refine ⟨?_, h3.1, h3.2, isUnit_l he⟩
  rw [htu, map_mul]
  exact (isUnit_mu he).mul (hu.map _)

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyLocalPeriodRingsData
section
namespace GlobalTheory.MemLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

theorem coreEx_alg_tower {l : ℕ} [Fact l.Prime] (a : Per.Ainf l) :
    algebraMap (Per.Ainf l) (Per.Acris l) a =
      algebraMap (Per.Acris0 l) (Per.Acris l) (algebraMap (Per.Ainf l) (Per.Acris0 l) a) :=
  GlobalTheory.RingIface.tower l a

section
set_option allowUnsafeReducibility true in
attribute [local irreducible] Per.Acris Per.Bcris

theorem coreEx_isUnit_l {l : ℕ} [Fact l.Prime] (e : Per.Fl l) (h1 : e.untilt = 1) (h2 : e ≠ 1)
    (w : Per.Acris0 l)
    (hw : (l : Per.AinfP l) * (w : Per.AinfP l) = algebraMap (Per.Ainf l) (Per.AinfP l) (mu e) ^ (l - 1)) :
    IsUnit (l : Per.Bcris l) := by
  have h0 : (l : Per.Acris0 l) * w = algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e) ^ (l - 1) :=
    Subtype.ext (by simpa using hw)
  have hu : IsUnit (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Per.Ainf l) (Per.Acris l) (mu e))) := by
    exact GlobalTheory.CrisLoc.unit_of_root l e h1 h2
  have h3 := congrArg ((algebraMap (Per.Acris l) (Per.Bcris l)).comp
    (algebraMap (Per.Acris0 l) (Per.Acris l))) h0
  rw [map_mul, map_natCast, map_pow] at h3
  have h4 : (algebraMap (Per.Acris l) (Per.Bcris l)).comp (algebraMap (Per.Acris0 l) (Per.Acris l))
      (algebraMap (Per.Ainf l) (Per.Acris0 l) (mu e)) =
      algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Per.Ainf l) (Per.Acris l) (mu e)) := by
    rw [coreEx_alg_tower, RingHom.comp_apply]
  rw [h4] at h3
  exact isUnit_of_mul_isUnit_left (h3 ▸ hu.pow (l - 1))

theorem nonempty_core : ∀ (l : ℕ) [Fact l.Prime], Nonempty (Core l) := by
  intro l _
  obtain ⟨ζ, ε, z0, zs, z1, hr⟩ := GlobalTheory.T.exists_compatible_rootsOfUnity_and_tilt_padic l
  obtain ⟨o, ho⟩ := _root_.GlobalTheory.MemLoc.SecEx.exists_isSec l
  obtain ⟨j, hj⟩ := _root_.GlobalTheory.MemLoc.exists_isCrisP l
  obtain ⟨ι, hι, hinj⟩ := _root_.GlobalTheory.MemLoc.exists_iota_cris_dR l j hj
  have h1 : ε.untilt = 1 := by
    have h := hr 0
    rw [z0, map_one] at h
    exact Subtype.ext h
  have h2 : ε ≠ 1 := by
    intro h
    have h' := hr 1
    rw [h] at h'
    simp only [rootT, Function.iterate_one, map_one] at h'
    apply z1
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← h', map_one]
    rfl
  obtain ⟨w, hw, -⟩ := _root_.GlobalTheory.MemLoc.exists_mu_pow_div l ε h1
  have hA : ∀ a : Per.Ainf l, ι (Per.aB l a) = algebraMap (Per.BdRp l) (Per.BdR l) (aDp l a) := by
    intro a
    have h := hι (algebraMap (Per.Ainf l) (Per.Acris l) a)
    have h' : j (algebraMap (Per.Ainf l) (Per.Acris l) a) = aDp l a := by
      rw [coreEx_alg_tower, hj.on0]; rfl
    rw [h'] at h
    rw [GlobalTheory.RingIface.aB_apply]
    exact h
  obtain ⟨u, hu⟩ := _root_.GlobalTheory.MemLoc.exists_unram_to_cris l o ι ho hinj hA (coreEx_isUnit_l ε h1 h2 w hw)
  obtain ⟨t, -, ht, -⟩ := _root_.GlobalTheory.MemLoc.exists_isLogA l ε h1
  obtain ⟨σ, hσ⟩ := exists_frobenius_Kur l
  obtain ⟨χ, hχ⟩ := exists_cyclotomicChar l
  exact ⟨⟨ζ, z0, zs, z1, ε, hr, o, ho, j, hj, ι, hι, u, hu, t, ht, σ, hσ, χ, hχ⟩⟩

end

end GlobalTheory.MemLoc
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PeriodRingsGaloisActionLawsFrobeniusComm
section
noncomputable section
namespace GlobalTheory.MemLoc.ActLaws
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

section
variable {R S T : Type} [CommRing R] [CommRing S] [CommRing T]

theorem mem_map_of_evalₐ_eq_zero_pt (I : Ideal R) (hI : I.FG) (n : ℕ) (z : AdicCompletion I R)
    (hz : AdicCompletion.evalₐ I n z = 0) : z ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) := by
  have h5 : z ∈ (I ^ n • ⊤ : Submodule R (AdicCompletion I R)) := by
    rw [AdicCompletion.pow_smul_top_eq_ker_eval hI, LinearMap.mem_ker]
    induction z using AdicCompletion.induction_on with
    | _ z =>
      rw [AdicCompletion.evalₐ_mk, Ideal.Quotient.eq_zero_iff_mem] at hz
      change Submodule.Quotient.mk (z.1 n) = 0
      rw [Submodule.Quotient.mk_eq_zero]
      simpa using hz
  rw [Ideal.smul_top_eq_map] at h5
  exact h5

theorem evalₐ_alg_pt (I : Ideal R) (n : ℕ) (y : R) :
    AdicCompletion.evalₐ I n (algebraMap R (AdicCompletion I R) y) = Ideal.Quotient.mk (I ^ n) y :=
  (AdicCompletion.evalₐ I n).commutes y

theorem evalₐ_hom_pt (I : Ideal R) (hI : I.FG) (K : Ideal S) (f : R →+* S) (hf : I ≤ K.comap f)
    (φ : AdicCompletion I R →+* AdicCompletion K S)
    (hφ : ∀ r, φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (n : ℕ) (x : AdicCompletion I R) (y : R) (hy : AdicCompletion.evalₐ I n x = Ideal.Quotient.mk (I ^ n) y) :
    AdicCompletion.evalₐ K n (φ x) = Ideal.Quotient.mk (K ^ n) (f y) := by
  have h1 : x - algebraMap R (AdicCompletion I R) y ∈ (I ^ n).map (algebraMap R (AdicCompletion I R)) :=
    mem_map_of_evalₐ_eq_zero_pt I hI n _ (by rw [map_sub, hy, evalₐ_alg_pt, sub_self])
  have h2 : (I ^ n).map (algebraMap R (AdicCompletion I R)) ≤
      RingHom.ker ((AdicCompletion.evalₐ K n).toRingHom.comp φ) := by
    rw [Ideal.map_le_iff_le_comap]
    intro r hr
    have h3 : f r ∈ K ^ n := Ideal.le_comap_pow f n (Ideal.pow_right_mono hf n hr)
    rw [Ideal.mem_comap, RingHom.mem_ker, RingHom.comp_apply, hφ]
    exact (evalₐ_alg_pt K n (f r)).trans (Ideal.Quotient.eq_zero_iff_mem.2 h3)
  have h4 : AdicCompletion.evalₐ K n (φ (x - algebraMap R (AdicCompletion I R) y)) = 0 := h2 h1
  rw [map_sub, map_sub, hφ, evalₐ_alg_pt, sub_eq_zero] at h4
  exact h4

theorem hom_ext_pt (I : Ideal R) (hI : I.FG) (K : Ideal S) (f : R →+* S) (hf : I ≤ K.comap f)
    (φ ψ : AdicCompletion I R →+* AdicCompletion K S)
    (hφ : ∀ r, φ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (hψ : ∀ r, ψ (algebraMap R (AdicCompletion I R) r) = algebraMap S (AdicCompletion K S) (f r))
    (x : AdicCompletion I R) : φ x = ψ x := by
  refine AdicCompletion.ext_evalₐ fun n => ?_
  obtain ⟨y, hy⟩ := Ideal.Quotient.mk_surjective (AdicCompletion.evalₐ I n x)
  rw [evalₐ_hom_pt I hI K f hf φ hφ n x y hy.symm, evalₐ_hom_pt I hI K f hf ψ hψ n x y hy.symm]

theorem endo_ext_pt {A : Type} [CommRing A] (I : Ideal R) (hI : I.FG) (i : R →+* A) (e : A ≃+* AdicCompletion I R)
    (he : ∀ r, e (i r) = algebraMap R (AdicCompletion I R) r) (f : R →+* R) (hf : I ≤ I.comap f)
    (φ ψ : A →+* A) (hφ : ∀ r, φ (i r) = i (f r)) (hψ : ∀ r, ψ (i r) = i (f r)) (x : A) : φ x = ψ x := by
  have hs : ∀ r, e.symm (algebraMap R (AdicCompletion I R) r) = i r := fun r => by
    rw [← he, RingEquiv.symm_apply_apply]
  have h := hom_ext_pt I hI I f hf (e.toRingHom.comp (φ.comp e.symm.toRingHom))
    (e.toRingHom.comp (ψ.comp e.symm.toRingHom))
    (fun r => by
      change e (φ (e.symm _)) = _
      rw [hs, hφ, he])
    (fun r => by
      change e (ψ (e.symm _)) = _
      rw [hs, hψ, he]) (e x)
  change e (φ (e.symm (e x))) = e (ψ (e.symm (e x))) at h
  rw [RingEquiv.symm_apply_apply] at h
  exact e.injective h

theorem span_le_comap_pt (p : ℕ) (f : R →+* S) : Ideal.span {(p : R)} ≤ (Ideal.span {(p : S)}).comap f := by
  rw [Ideal.span_singleton_le_iff_mem, Ideal.mem_comap, map_natCast]
  exact Ideal.mem_span_singleton_self _

end

variable {l : ℕ} [Fact l.Prime]

theorem awayMap_comp₂ (f g k : Per.Ainf l →+* Per.Ainf l) (e : ∀ x, k x = g (f x)) (x : Per.AinfP l) :
    Per.extP k x = Per.extP g (Per.extP f x) := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := Per.extP k) (k := (Per.extP g).comp (Per.extP f)) (RingHom.ext fun y => ?_)) x
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, e]

theorem awayMap_id₂ (f : Per.Ainf l →+* Per.Ainf l) (e : ∀ x, f x = x) (x : Per.AinfP l) :
    Per.extP f x = x := by
  refine RingHom.congr_fun (IsLocalization.ringHom_ext (Submonoid.powers (l : Per.Ainf l))
    (j := Per.extP f) (k := RingHom.id _) (RingHom.ext fun y => ?_)) x
  simp only [RingHom.comp_apply, GlobalTheory.RingBasics.awayMap_algebraMap₂, e, RingHom.id_apply]

theorem acris_ext_pt (f : Per.Acris0 l →+* Per.Acris0 l) (φ ψ : Per.Acris l →+* Per.Acris l)
    (hφ : ∀ r, φ (algebraMap (Per.Acris0 l) (Per.Acris l) r) = algebraMap (Per.Acris0 l) (Per.Acris l) (f r))
    (hψ : ∀ r, ψ (algebraMap (Per.Acris0 l) (Per.Acris l) r) = algebraMap (Per.Acris0 l) (Per.Acris l) (f r))
    (x : Per.Acris l) : φ x = ψ x := by
  obtain ⟨e, he⟩ := GlobalTheory.AdicMaps.exists_acris_completion l
  exact endo_ext_pt _ (Submodule.fg_span_singleton _) (algebraMap (Per.Acris0 l) (Per.Acris l)) e he f
    (span_le_comap_pt l f) φ ψ hφ hψ x

theorem bdRp_ext_pt (f : Per.AinfP l →+* Per.AinfP l) (hf : Per.kerP l ≤ (Per.kerP l).comap f)
    (φ ψ : Per.BdRp l →+* Per.BdRp l)
    (hφ : ∀ r, φ (algebraMap (Per.AinfP l) (Per.BdRp l) r) = algebraMap (Per.AinfP l) (Per.BdRp l) (f r))
    (hψ : ∀ r, ψ (algebraMap (Per.AinfP l) (Per.BdRp l) r) = algebraMap (Per.AinfP l) (Per.BdRp l) (f r))
    (x : Per.BdRp l) : φ x = ψ x := by
  obtain ⟨e, he, -⟩ := GlobalTheory.RingIface.exists_bdRp_equiv l
  have hfg : (Per.kerP l).FG := by
    obtain ⟨ε, hε⟩ := GlobalTheory.MemLoc.Model.exists_isEps l
    rw [(GlobalTheory.MemLoc.thetaP_facts l).2.2.2.2.2.2 ε hε]
    exact Submodule.fg_span_singleton _
  exact endo_ext_pt _ hfg (algebraMap (Per.AinfP l) (Per.BdRp l)) e he f hf φ ψ hφ hψ x

theorem extends_comp {f g k : Per.Ainf l →+* Per.Ainf l} {F G K : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) (hg : GlobalTheory.CrisMaps.Extends g G) (hk : GlobalTheory.CrisMaps.Extends k K)
    (e : ∀ x, k x = g (f x)) (x : Per.Acris l) : K x = G (F x) :=
  acris_ext_pt ((Per.extP k).restrict _ _ hk.mem) K (G.comp F)
    (fun r => hk.env r)
    (fun r => by
      rw [RingHom.comp_apply, hf.env, hg.env]
      exact congrArg _ (Subtype.ext (awayMap_comp₂ f g k e r).symm)) x

theorem extends_id {f : Per.Ainf l →+* Per.Ainf l} {F : Per.Acris l →+* Per.Acris l}
    (hf : GlobalTheory.CrisMaps.Extends f F) (e : ∀ x, f x = x) (x : Per.Acris l) : F x = x :=
  acris_ext_pt (RingHom.id _) F (RingHom.id _)
    (fun r => (hf.env r).trans (congrArg _ (Subtype.ext (awayMap_id₂ f e r))))
    (fun _ => rfl) x

theorem sigA_mul (g h : Per.Gq l) (x : Per.Acris l) : sigA (g * h) x = sigA g (sigA h x) :=
  extends_comp (GlobalTheory.CrisMaps.sigA_extends h) (GlobalTheory.CrisMaps.sigA_extends g) (GlobalTheory.CrisMaps.sigA_extends (g * h))
    (GlobalTheory.RingBasics.σA_mul g h) x

theorem sigA_one (x : Per.Acris l) : sigA 1 x = x :=
  extends_id (GlobalTheory.CrisMaps.sigA_extends 1) GlobalTheory.RingBasics.σA_one x

theorem σD_alg (g : Per.Gq l) (y : Per.BdRp l) :
    Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y) :=
  GlobalTheory.RingIface.sigD_alg l g y

theorem σDp_mul (g h : Per.Gq l) (x : Per.BdRp l) : Per.σDp (g * h) x = Per.σDp g (Per.σDp h x) :=
  bdRp_ext_pt (Per.extP (Per.σA (g * h))) (GlobalTheory.RingBasics.ker_σ (g * h)) (Per.σDp (g * h)) ((Per.σDp g).comp (Per.σDp h))
    (GlobalTheory.RingIface.sigDp_alg l (g * h))
    (fun r => by
      rw [RingHom.comp_apply, GlobalTheory.RingIface.sigDp_alg, GlobalTheory.RingIface.sigDp_alg,
        awayMap_comp₂ _ _ _ (GlobalTheory.RingBasics.σA_mul g h)]) x

theorem σDp_one (x : Per.BdRp l) : Per.σDp 1 x = x :=
  bdRp_ext_pt (Per.extP (Per.σA (1 : Per.Gq l))) (GlobalTheory.RingBasics.ker_σ 1) (Per.σDp 1) (RingHom.id _)
    (GlobalTheory.RingIface.sigDp_alg l 1)
    (fun r => by rw [RingHom.id_apply, awayMap_id₂ _ GlobalTheory.RingBasics.σA_one]) x

theorem σDp_alg (g : Per.Gq l) (a : Per.AinfP l) :
    Per.σDp g (algebraMap (Per.AinfP l) (Per.BdRp l) a) =
      algebraMap (Per.AinfP l) (Per.BdRp l) (Per.extP (Per.σA g) a) :=
  GlobalTheory.RingIface.sigDp_alg l g a

theorem σDp_aDp (g : Per.Gq l) (a : Per.Ainf l) : Per.σDp g (aDp l a) = aDp l (Per.σA g a) := by
  simp only [aDp, RingHom.comp_apply, σDp_alg, GlobalTheory.RingBasics.awayMap_algebraMap₂]

theorem σD_mul (g h : Per.Gq l) (x : Per.BdR l) : Per.σD (g * h) x = Per.σD g (Per.σD h x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bdR_hom_ext l
    (f := Per.σD (g * h)) (g := (Per.σD g).comp (Per.σD h)) fun y => ?_) x
  simp only [RingHom.comp_apply, σD_alg, σDp_mul]

theorem σD_one (x : Per.BdR l) : Per.σD 1 x = x := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bdR_hom_ext l
    (f := Per.σD 1) (g := RingHom.id _) fun y => ?_) x
  simp only [RingHom.comp_apply, σD_alg, σDp_one, RingHom.id_apply]

theorem endo_zA_pt (F : Per.Ainf l →+* Per.Ainf l) (z : ℤ_[l]) : F (Per.zA l z) = Per.zA l z := by
  rw [← sub_eq_zero]
  refine WittVector.ext fun m => ?_
  obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 (PadicInt.appr_spec (m + 1) z)
  have hz : z = (z.appr (m + 1) : ℤ_[l]) + w * (l : ℤ_[l]) ^ (m + 1) := by rw [hw]; ring
  have h : F (Per.zA l z) - Per.zA l z ∈ Ideal.span {((l : ℕ) : Per.Ainf l) ^ (m + 1)} := by
    refine Ideal.mem_span_singleton'.2 ⟨F (Per.zA l w) - Per.zA l w, ?_⟩
    generalize z.appr (m + 1) = a at hz
    rw [hz]
    simp only [map_add (f := _), map_mul, map_pow, map_natCast]
    ring
  rw [(WittVector.mem_span_p_pow_iff_le_coeff_eq_zero _ _).1 h m (Nat.lt_succ_self m), WittVector.zero_coeff]

theorem φA_σA (g : Per.Gq l) (a : Per.Ainf l) : Per.φA l (Per.σA g a) = Per.σA g (Per.φA l a) := by
  refine WittVector.ext fun n => ?_
  rw [GlobalTheory.RingIface.phiA_coeff, GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.sigA_coeff, GlobalTheory.RingIface.phiA_coeff,
    map_pow]

theorem φB_σB (g : Per.Gq l) (x : Per.Bcris l) : Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := (Per.φB l).comp (Per.σB g)) (g := (Per.σB g).comp (Per.φB l)) fun y => ?_) x
  simp only [RingHom.comp_apply, GlobalTheory.CrisMaps.φB_phiA, GlobalTheory.CrisMaps.σB_sigA, GlobalTheory.CrisMaps.phiA_sigA]

theorem σB_mul (g h : Per.Gq l) (x : Per.Bcris l) : Per.σB (g * h) x = Per.σB g (Per.σB h x) := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := Per.σB (g * h)) (g := (Per.σB g).comp (Per.σB h)) fun y => ?_) x
  simp only [RingHom.comp_apply, GlobalTheory.CrisMaps.σB_sigA, sigA_mul]

theorem σB_one (x : Per.Bcris l) : Per.σB 1 x = x := by
  refine RingHom.congr_fun (GlobalTheory.CrisLoc.bcris_hom_ext l
    (f := Per.σB 1) (g := RingHom.id _) fun y => ?_) x
  simp only [GlobalTheory.CrisMaps.σB_sigA, sigA_one, RingHom.id_apply]

theorem σB_aB (g : Per.Gq l) (a : Per.Ainf l) : Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.CrisMaps.σB_sigA, (GlobalTheory.CrisMaps.sigA_extends g).alg]

theorem φB_aB (a : Per.Ainf l) : Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a) := by
  rw [GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.RingIface.aB_eq_alg, GlobalTheory.CrisMaps.φB_phiA, (GlobalTheory.CrisMaps.phiA_extends l).alg]

theorem act_laws : ∀ (l : ℕ) [Fact l.Prime], (∀ (g h : Per.Gq l) (x : Per.Bcris l), Per.σB (g * h) x = Per.σB g (Per.σB h x)) ∧
    (∀ x : Per.Bcris l, Per.σB 1 x = x) ∧
    (∀ (g h : Per.Gq l) (x : Per.BdR l), Per.σD (g * h) x = Per.σD g (Per.σD h x)) ∧
    (∀ x : Per.BdR l, Per.σD 1 x = x) ∧
    (∀ (g : Per.Gq l) (x : Per.Bcris l), Per.φB l (Per.σB g x) = Per.σB g (Per.φB l x)) ∧
    (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σB g (Per.aB l a) = Per.aB l (Per.σA g a)) ∧
    (∀ a : Per.Ainf l, Per.φB l (Per.aB l a) = Per.aB l (Per.φA l a)) ∧
    (∀ (g : Per.Gq l) (z : ℤ_[l]), Per.σA g (Per.zA l z) = Per.zA l z) ∧
    (∀ z : ℤ_[l], Per.φA l (Per.zA l z) = Per.zA l z) ∧
    (∀ (g : Per.Gq l) (y : Per.BdRp l), Per.σD g (algebraMap (Per.BdRp l) (Per.BdR l) y) = algebraMap (Per.BdRp l) (Per.BdR l) (Per.σDp g y)) ∧
    (∀ (g : Per.Gq l) (a : Per.Ainf l), Per.σDp g (aDp l a) = aDp l (Per.σA g a)) ∧
    (∀ (g : Per.Gq l) (x : Per.Acris l), Per.σB g (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (sigA g x)) ∧
    ∀ x : Per.Acris l, Per.φB l (algebraMap (Per.Acris l) (Per.Bcris l) x) = algebraMap (Per.Acris l) (Per.Bcris l) (phiA l x) :=
  fun l _ => ⟨σB_mul, σB_one, σD_mul, σD_one, φB_σB, σB_aB, φB_aB,
    fun g => endo_zA_pt (Per.σA g), endo_zA_pt (Per.φA l),
    σD_alg, σDp_aDp, GlobalTheory.CrisMaps.σB_sigA, GlobalTheory.CrisMaps.φB_phiA l⟩

end GlobalTheory.MemLoc.ActLaws
end
end

